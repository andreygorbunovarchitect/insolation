package com.bim.sunlevel;

import android.Manifest;
import android.app.Activity;
import android.app.AlertDialog;
import android.content.ContentValues;
import android.content.Context;
import android.content.SharedPreferences;
import android.content.pm.PackageManager;
import android.graphics.Bitmap;
import android.graphics.BitmapFactory;
import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.DashPathEffect;
import android.graphics.ImageFormat;
import android.graphics.LinearGradient;
import android.graphics.Matrix;
import android.graphics.Paint;
import android.graphics.Path;
import android.graphics.Rect;
import android.graphics.RectF;
import android.graphics.Shader;
import android.graphics.YuvImage;
import android.graphics.pdf.PdfDocument;
import android.hardware.Camera;
import android.hardware.Sensor;
import android.hardware.SensorEvent;
import android.hardware.SensorEventListener;
import android.hardware.SensorManager;
import android.location.Location;
import android.location.LocationListener;
import android.location.LocationManager;
import android.net.Uri;
import android.os.Bundle;
import android.os.Environment;
import android.provider.MediaStore;
import android.text.InputType;
import android.view.Gravity;
import android.view.MotionEvent;
import android.view.SurfaceHolder;
import android.view.SurfaceView;
import android.view.View;
import android.widget.Button;
import android.widget.EditText;
import android.widget.FrameLayout;
import android.widget.LinearLayout;
import android.widget.SeekBar;
import android.widget.TextView;
import android.widget.Toast;

import org.json.JSONArray;
import org.json.JSONObject;

import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.net.HttpURLConnection;
import java.net.URL;
import java.net.URLEncoder;
import java.nio.charset.StandardCharsets;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Date;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.TimeZone;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

@SuppressWarnings("deprecation")
public class MainActivity extends Activity implements SensorEventListener, SurfaceHolder.Callback {

    private SensorManager sensorManager;
    private Sensor rotSensor, accelSensor, pressureSensor, lightSensor;
    private LocationManager locationManager;

    private SurfaceView cameraSurface;
    private Camera camera;
    private AROverlayView overlayView;
    private LinearLayout bottomContainer;
    private Button btnModeToggle, btnPlayAnim, btnTheme;
    private TextView timeLabelView;
    private SeekBar timeSeekBar;

    // Координаты (обновляются по GPS)
    private double latitude = 54.6195;
    private double longitude = 39.7420;
    private double lastOsmLat = 0.0;
    private double lastOsmLon = 0.0;
    private boolean gpsLocked = false;
    private boolean realOsmLoaded = false;

    // Углы ориентации камеры
    private float camAzimuth = 0f;
    private float camAltitude = 0f;
    private float camRoll = 0f;

    // Уклономер
    private float rawPitch = 0f, rawRoll = 0f;
    private float tarePitch = 0f, tareRoll = 0f;

    // Барометр и высотные отметки
    private float currentPressure = 1013.25f;
    private float basePressure = -1f;
    private float floorHeightMeters = 3.0f;
    private float calibratedBaseHeight = 12.0f; // 5 этаж (+12.00 м)
    private float relativeHeightMeters = 12.0f;
    private float currentLux = 0f;

    // КЕО по точкам (СП 52.13330) и тепловая карта
    private float externalLuxForKeo = -1f;
    private float keoWindowLux = -1f;
    private float keoCenterLux = -1f;
    private float keoBackLux = -1f;
    private float lastCalculatedKeo = -1f;
    private boolean showKeoHeatmap = false;

    // Импортированный проектный контур (.dxf / .ifc / .txt)
    private final List<float[]> customProjectPolygon = new ArrayList<>();
    private int customProjectLevels = 12;
    private float customProjectHeight = 36.0f;
    private String customProjectName = "Проект DXF/IFC";

    // Интерактивная AR-рулетка и привязка ΔH
    private boolean isArTapeMode = false;
    private Float arAngleBaseDeg = null;
    private Float arAngleTopDeg = null;
    private float arEyeHeightMeters = 1.60f;
    private float arMeasuredDistance = -1f;
    private float arMeasuredHeight = -1f;
    private float savedBaroMarkHeight = 12.0f;

    // Темы оформления
    private boolean isLightFieldTheme = false;

    // Таймлайн и плавная интерполяция времени
    private int selectedDayOfYear = 80;
    private String selectedSeasonLabel = "Сегодня";
    private double targetClockHour = 12.0;
    private double displayedClockHour = 12.0;
    private boolean isLiveTime = true;
    private boolean isAnimatingTimeline = false;

    // Режим 2D Генплана
    private boolean is2DMapMode = false;
    private float mapScalePixelsPerMeter = 2.2f;

    private static class OsmBuilding {
        float[] xMeters;
        float[] yMeters;
        float heightMeters;
        int levels;
        String houseNumber;
        boolean isCustomProject;
    }

    private final List<OsmBuilding> osmBuildings = new ArrayList<>();
    private String osmStatus = "Подключение к OSM...";
    private final AtomicBoolean isFetchingOsm = new AtomicBoolean(false);

    private final float[] rotationMatrix = new float[9];
    private final float[] remappedMatrix = new float[9];
    private final float[] orientationVals = new float[3];

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);

        Calendar cal = Calendar.getInstance();
        selectedDayOfYear = cal.get(Calendar.DAY_OF_YEAR);
        selectedSeasonLabel = "День #" + selectedDayOfYear;

        loadCachedOsmIfAvailable();

        FrameLayout root = new FrameLayout(this);
        root.setBackgroundColor(Color.BLACK);

        // Слой 1: Живое видео с камеры
        cameraSurface = new SurfaceView(this);
        cameraSurface.getHolder().addCallback(this);
        root.addView(cameraSurface, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.MATCH_PARENT));

        // Слой 2: Прозрачный AR-холст и 2D-генплан
        overlayView = new AROverlayView(this);
        overlayView.setBackgroundColor(Color.TRANSPARENT);
        overlayView.setOnTouchListener((v, event) -> {
            if (event.getAction() == MotionEvent.ACTION_DOWN) {
                float tx = event.getX();
                float ty = event.getY();

                // Нажатие на верхнюю карточку телеметрии перезапускает загрузку OSM
                if (ty < 410) {
                    isFetchingOsm.set(false);
                    fetchOsmBuildings(latitude, longitude);
                    Toast.makeText(this, "Запрос реальных зданий OSM...", Toast.LENGTH_SHORT).show();
                    return true;
                }

                // Нажатие по тепловой карте КЕО закрывает ее
                if (showKeoHeatmap && ty > 420 && ty < v.getHeight() - 260) {
                    showKeoHeatmap = false;
                    overlayView.invalidate();
                    return true;
                }

                // В режиме AR-рулетки тап по центральной области фиксирует точки Низа и Верха
                if (!is2DMapMode && isArTapeMode && ty > 420 && ty < v.getHeight() - 260) {
                    handleArTapeTap();
                    return true;
                }

                if (is2DMapMode) {
                    float cx = v.getWidth() / 2f;
                    float cy = v.getHeight() * 0.56f;
                    float mapX = (tx - cx) / mapScalePixelsPerMeter;
                    float mapY = (cy - ty) / mapScalePixelsPerMeter;

                    synchronized (osmBuildings) {
                        for (OsmBuilding b : osmBuildings) {
                            if (isPointInPolygon(mapX, mapY, b.xMeters, b.yMeters)) {
                                showEditBuildingDialog(b);
                                return true;
                            }
                        }
                    }

                    if (ty > 420 && ty < v.getHeight() - 260) {
                        if (mapScalePixelsPerMeter < 1.6f) mapScalePixelsPerMeter = 2.2f;
                        else if (mapScalePixelsPerMeter < 2.5f) mapScalePixelsPerMeter = 3.5f;
                        else if (mapScalePixelsPerMeter < 4.0f) mapScalePixelsPerMeter = 5.0f;
                        else mapScalePixelsPerMeter = 1.1f;
                        overlayView.invalidate();
                        Toast.makeText(this, String.format(Locale.US, "Масштаб: %.1f пикс/м", mapScalePixelsPerMeter), Toast.LENGTH_SHORT).show();
                        return true;
                    }
                }
            }
            return false;
        });
        root.addView(overlayView, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.MATCH_PARENT));

        // Слой 3: Нижняя панель управления
        bottomContainer = new LinearLayout(this);
        bottomContainer.setOrientation(LinearLayout.VERTICAL);
        bottomContainer.setBackgroundColor(Color.argb(215, 12, 18, 26));
        bottomContainer.setPadding(12, 8, 12, 18);

        LinearLayout sliderRow = new LinearLayout(this);
        sliderRow.setOrientation(LinearLayout.HORIZONTAL);
        sliderRow.setGravity(Gravity.CENTER_VERTICAL);
        sliderRow.setPadding(8, 4, 8, 8);

        timeLabelView = new TextView(this);
        timeLabelView.setTextColor(Color.rgb(120, 255, 160));
        timeLabelView.setTextSize(12.0f);
        timeLabelView.setOnClickListener(v -> {
            isAnimatingTimeline = false;
            if (btnPlayAnim != null) btnPlayAnim.setText("▶");
            isLiveTime = true;
            syncWithRealTime();
            Toast.makeText(this, "Синхронизировано с реальным временем", Toast.LENGTH_SHORT).show();
        });
        sliderRow.addView(timeLabelView);

        timeSeekBar = new SeekBar(this);
        timeSeekBar.setMax(1439);
        LinearLayout.LayoutParams seekParams = new LinearLayout.LayoutParams(
                0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f);
        seekParams.setMargins(10, 0, 10, 0);
        timeSeekBar.setLayoutParams(seekParams);

        syncWithRealTime();
        displayedClockHour = targetClockHour;

        timeSeekBar.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
            @Override
            public void onProgressChanged(SeekBar seekBar, int progress, boolean fromUser) {
                if (fromUser) {
                    isLiveTime = false;
                    isAnimatingTimeline = false;
                    if (btnPlayAnim != null) btnPlayAnim.setText("▶");
                    targetClockHour = progress / 60.0;
                    updateTimeLabelColors();
                    timeLabelView.setText(formatClockHour(targetClockHour, false));
                    if (overlayView != null) overlayView.invalidate();
                }
            }

            @Override
            public void onStartTrackingTouch(SeekBar seekBar) {
                isLiveTime = false;
                isAnimatingTimeline = false;
                if (btnPlayAnim != null) btnPlayAnim.setText("▶");
            }

            @Override
            public void onStopTrackingTouch(SeekBar seekBar) {}
        });
        sliderRow.addView(timeSeekBar);

        btnPlayAnim = new Button(this);
        btnPlayAnim.setText("▶");
        btnPlayAnim.setTextSize(11f);
        btnPlayAnim.setTextColor(Color.WHITE);
        btnPlayAnim.setBackgroundColor(Color.argb(220, 45, 95, 150));
        btnPlayAnim.setPadding(16, 4, 16, 4);
        btnPlayAnim.setOnClickListener(v -> {
            isAnimatingTimeline = !isAnimatingTimeline;
            if (isAnimatingTimeline) {
                isLiveTime = false;
                btnPlayAnim.setText("❚❚");
                if (targetClockHour < 5.0 || targetClockHour > 20.0) {
                    targetClockHour = 6.0;
                }
            } else {
                btnPlayAnim.setText("▶");
            }
            overlayView.invalidate();
        });
        sliderRow.addView(btnPlayAnim);

        bottomContainer.addView(sliderRow);

        LinearLayout bottomBar = new LinearLayout(this);
        bottomBar.setOrientation(LinearLayout.HORIZONTAL);
        bottomBar.setGravity(Gravity.CENTER);

        btnModeToggle = createButton("2D План", Color.argb(230, 30, 115, 165));
        btnModeToggle.setOnClickListener(v -> {
            is2DMapMode = !is2DMapMode;
            btnModeToggle.setText(is2DMapMode ? "Камера AR" : "2D План");
            if (!is2DMapMode && cameraSurface.getHolder().getSurface().isValid()) {
                startCameraPreview(cameraSurface.getHolder());
            }
            if (!realOsmLoaded) {
                fetchOsmBuildings(latitude, longitude);
            }
            overlayView.invalidate();
        });

        Button btnKeo = createButton("КЕО Карта", Color.argb(230, 145, 50, 175));
        btnKeo.setOnClickListener(v -> showKeoGridDialog());

        Button btnTools = createButton("DXF/PDF/Рул", Color.argb(230, 35, 130, 95));
        btnTools.setOnClickListener(v -> showProjectAndToolsMenu());

        btnTheme = createButton("Тема", Color.argb(215, 75, 85, 105));
        btnTheme.setOnClickListener(v -> {
            isLightFieldTheme = !isLightFieldTheme;
            applyThemeColors();
            Toast.makeText(this, isLightFieldTheme ? "Дневная полевая тема (высокий контраст)" : "Темная тема", Toast.LENGTH_SHORT).show();
            overlayView.invalidate();
        });

        Button btnPhoto = createButton("Фото AR", Color.argb(230, 195, 80, 25));
        btnPhoto.setOnClickListener(v -> captureARPhoto());

        Button btnSave = createButton("Акт PDF", Color.argb(230, 180, 45, 65));
        btnSave.setOnClickListener(v -> generateInspectionReportPdf());

        bottomBar.addView(btnModeToggle);
        bottomBar.addView(btnKeo);
        bottomBar.addView(btnTools);
        bottomBar.addView(btnTheme);
        bottomBar.addView(btnPhoto);
        bottomBar.addView(btnSave);

        bottomContainer.addView(bottomBar);

        FrameLayout.LayoutParams barParams = new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.WRAP_CONTENT,
                Gravity.BOTTOM
        );
        root.addView(bottomContainer, barParams);

        setContentView(root);

        sensorManager = (SensorManager) getSystemService(Context.SENSOR_SERVICE);
        if (sensorManager != null) {
            rotSensor = sensorManager.getDefaultSensor(Sensor.TYPE_ROTATION_VECTOR);
            accelSensor = sensorManager.getDefaultSensor(Sensor.TYPE_ACCELEROMETER);
            pressureSensor = sensorManager.getDefaultSensor(Sensor.TYPE_PRESSURE);
            lightSensor = sensorManager.getDefaultSensor(Sensor.TYPE_LIGHT);
        }

        locationManager = (LocationManager) getSystemService(Context.LOCATION_SERVICE);
        requestPermissionsIfNeeded();

        fetchOsmBuildings(latitude, longitude);
    }

    private void applyThemeColors() {
        if (bottomContainer != null) {
            bottomContainer.setBackgroundColor(isLightFieldTheme
                    ? Color.argb(235, 238, 242, 247)
                    : Color.argb(215, 12, 18, 26));
        }
        updateTimeLabelColors();
    }

    private void updateTimeLabelColors() {
        if (timeLabelView == null) return;
        if (isLiveTime) {
            timeLabelView.setTextColor(isLightFieldTheme ? Color.rgb(0, 125, 60) : Color.rgb(120, 255, 160));
        } else {
            timeLabelView.setTextColor(isLightFieldTheme ? Color.rgb(165, 90, 0) : Color.rgb(255, 225, 90));
        }
    }

    // --- Астрономическая математика и проверка теней ---
    private double[] computeSunPosition(double latDeg, int dayOfYear, double localClockHour) {
        double tzHours = TimeZone.getDefault().getOffset(System.currentTimeMillis()) / 3600000.0;
        double bRad = Math.toRadians((360.0 / 365.0) * (dayOfYear - 81));
        double eotMinutes = 9.87 * Math.sin(2.0 * bRad) - 7.53 * Math.cos(bRad) - 1.5 * Math.sin(bRad);
        double timeCorrectionMinutes = 4.0 * (longitude - 15.0 * tzHours) + eotMinutes;
        double trueSolarHour = localClockHour + (timeCorrectionMinutes / 60.0);

        double latRad = Math.toRadians(latDeg);
        double declDeg = 23.45 * Math.sin(Math.toRadians((360.0 / 365.0) * (284 + dayOfYear)));
        double declRad = Math.toRadians(declDeg);
        double hourAngleRad = Math.toRadians(15.0 * (trueSolarHour - 12.0));

        double sinAlt = Math.sin(latRad) * Math.sin(declRad) +
                        Math.cos(latRad) * Math.cos(declRad) * Math.cos(hourAngleRad);
        sinAlt = Math.max(-1.0, Math.min(1.0, sinAlt));
        double altRad = Math.asin(sinAlt);

        double cosAz = (Math.sin(declRad) - Math.sin(altRad) * Math.sin(latRad)) /
                       (Math.cos(altRad) * Math.cos(latRad) + 1e-6);
        cosAz = Math.max(-1.0, Math.min(1.0, cosAz));
        double azDeg = Math.toDegrees(Math.acos(cosAz));

        double normSolar = ((trueSolarHour % 24.0) + 24.0) % 24.0;
        if (normSolar > 12.0) azDeg = 360.0 - azDeg;

        return new double[]{azDeg, Math.toDegrees(altRad)};
    }

    private List<OsmBuilding> getAllBuildingsWithCustom() {
        List<OsmBuilding> all = new ArrayList<>();
        synchronized (osmBuildings) {
            all.addAll(osmBuildings);
        }
        synchronized (customProjectPolygon) {
            if (customProjectPolygon.size() >= 3) {
                OsmBuilding proj = new OsmBuilding();
                proj.xMeters = new float[customProjectPolygon.size()];
                proj.yMeters = new float[customProjectPolygon.size()];
                for (int i = 0; i < customProjectPolygon.size(); i++) {
                    proj.xMeters[i] = customProjectPolygon.get(i)[0];
                    proj.yMeters[i] = customProjectPolygon.get(i)[1];
                }
                proj.levels = customProjectLevels;
                proj.heightMeters = customProjectHeight;
                proj.houseNumber = customProjectName;
                proj.isCustomProject = true;
                all.add(proj);
            }
        }
        return all;
    }

    private boolean isSunBlockedByOsmBuildings(double sunAzDeg, double sunAltDeg) {
        if (sunAltDeg <= 0.0) return true;
        double tanAlt = Math.tan(Math.toRadians(Math.max(0.2, sunAltDeg)));
        double rayDirX = Math.sin(Math.toRadians(sunAzDeg));
        double rayDirY = Math.cos(Math.toRadians(sunAzDeg));

        List<OsmBuilding> all = getAllBuildingsWithCustom();
        for (OsmBuilding b : all) {
            float dh = b.heightMeters - relativeHeightMeters;
            if (dh <= 0.5f) continue;
            if (isPointInPolygon(0f, 0f, b.xMeters, b.yMeters)) continue;

            float maxShadowDist = (float) (dh / tanAlt);
            int n = b.xMeters.length;
            for (int i = 0; i < n; i++) {
                float x1 = b.xMeters[i], y1 = b.yMeters[i];
                float x2 = b.xMeters[(i + 1) % n], y2 = b.yMeters[(i + 1) % n];
                float dist = intersectRayWithSegment((float) rayDirX, (float) rayDirY, x1, y1, x2, y2);
                if (dist > 2.5f && dist <= maxShadowDist) {
                    return true;
                }
            }
        }
        return false;
    }

    private boolean doesBuildingBlockSunNowOrToday(OsmBuilding b, double sunAzDeg, double sunAltDeg) {
        float dh = b.heightMeters - relativeHeightMeters;
        if (dh <= 0.5f) return false;
        if (isPointInPolygon(0f, 0f, b.xMeters, b.yMeters)) return false;

        if (sunAltDeg > 0.5) {
            double tanAlt = Math.max(0.08, Math.tan(Math.toRadians(sunAltDeg)));
            float maxShadowDist = (float) (dh / tanAlt);
            double rayDirX = Math.sin(Math.toRadians(sunAzDeg));
            double rayDirY = Math.cos(Math.toRadians(sunAzDeg));
            int n = b.xMeters.length;
            for (int i = 0; i < n; i++) {
                float dist = intersectRayWithSegment((float) rayDirX, (float) rayDirY,
                        b.xMeters[i], b.yMeters[i],
                        b.xMeters[(i + 1) % n], b.yMeters[(i + 1) % n]);
                if (dist > 2.0f && dist <= maxShadowDist) return true;
            }
        }
        return false;
    }

    private boolean isPointInPolygon(float px, float py, float[] vx, float[] vy) {
        boolean inside = false;
        int n = vx.length;
        for (int i = 0, j = n - 1; i < n; j = i++) {
            if (((vy[i] > py) != (vy[j] > py)) &&
                (px < (vx[j] - vx[i]) * (py - vy[i]) / (vy[j] - vy[i] + 1e-6f) + vx[i])) {
                inside = !inside;
            }
        }
        return inside;
    }

    private float intersectRayWithSegment(float dx, float dy, float x1, float y1, float x2, float y2) {
        float sx = x2 - x1;
        float sy = y2 - y1;
        float det = -dx * sy + dy * sx;
        if (Math.abs(det) < 1e-5f) return -1f;
        float t = (-sy * (-x1) + sx * (-y1)) / det;
        float u = (dx * (-y1) - dy * (-x1)) / det;
        if (t >= 0f && u >= 0f && u <= 1f) return t;
        return -1f;
    }

    private float[] calculateInsolationWithOsm(double lat, int day) {
        float astroHours = 0f;
        float unblockedHours = 0f;
        for (double hr = 4.0; hr <= 22.0; hr += 0.25) {
            double[] pos = computeSunPosition(lat, day, hr);
            if (pos[1] > 0.0) {
                astroHours += 0.25f;
                if (!isSunBlockedByOsmBuildings(pos[0], pos[1])) {
                    unblockedHours += 0.25f;
                }
            }
        }
        return new float[]{astroHours, unblockedHours};
    }

    // --- Инженерное меню: DXF/IFC, AR-рулетка, PDF, CSV, Калибровка ---
    private void showProjectAndToolsMenu() {
        String tapeLabel = isArTapeMode ? "2. Выключить AR-рулетку" : "2. Включить AR-рулетку и привязку ΔH";
        CharSequence[] items = new CharSequence[]{
                "1. Импорт проекта (.dxf / .ifc / .txt)",
                tapeLabel,
                "3. Сменить расчетную дату (Март/Июнь/Дек/Сегодня)",
                "4. Обнулить уклономер (Тара 0.0°)",
                "5. Привязка этажа и барометрической отметки H",
                "6. Экспорт журнала замеров в CSV",
                "7. Принудительно обновить здания OSM"
        };

        new AlertDialog.Builder(this)
                .setTitle("BIM Инструменты и САПР")
                .setItems(items, (dialog, which) -> {
                    if (which == 0) showDxfIfcImportDialog();
                    else if (which == 1) toggleArTapeMode();
                    else if (which == 2) cycleSeason();
                    else if (which == 3) {
                        tarePitch = rawPitch;
                        tareRoll = rawRoll;
                        Toast.makeText(this, "Уклономер обнулен (0.0°)", Toast.LENGTH_SHORT).show();
                    } else if (which == 4) showAltitudeCalibrationDialog();
                    else if (which == 5) exportLogToCsv();
                    else if (which == 6) {
                        isFetchingOsm.set(false);
                        fetchOsmBuildings(latitude, longitude);
                    }
                })
                .show();
    }

    // --- 1a. Парсер файлов .DXF, .IFC и .TXT ---
    private void showDxfIfcImportDialog() {
        LinearLayout layout = new LinearLayout(this);
        layout.setOrientation(LinearLayout.VERTICAL);
        layout.setPadding(45, 25, 45, 10);

        final EditText inputFile = new EditText(this);
        inputFile.setHint("Имя файла в Download (project.dxf или project.ifc)");
        inputFile.setText("project.dxf");
        layout.addView(inputFile);

        final EditText inputLevels = new EditText(this);
        inputLevels.setHint("Этажность проектируемого здания");
        inputLevels.setInputType(InputType.TYPE_CLASS_NUMBER);
        inputLevels.setText(String.valueOf(customProjectLevels));
        layout.addView(inputLevels);

        final EditText inputShift = new EditText(this);
        inputShift.setHint("Смещение центра X,Y в метрах (например: 35 -25)");
        inputShift.setText("35 -25");
        layout.addView(inputShift);

        new AlertDialog.Builder(this)
                .setTitle("Импорт контура (.DXF / .IFC / .TXT)")
                .setMessage("Поместите файл .dxf, .ifc или .txt в папку Download (если файла нет, приложение создаст готовый образец project.dxf и наложит его на генплан):")
                .setView(layout)
                .setPositiveButton("Импортировать на план", (dialog, which) -> {
                    String fName = inputFile.getText().toString().trim();
                    if (fName.isEmpty()) fName = "project.dxf";
                    try {
                        customProjectLevels = Integer.parseInt(inputLevels.getText().toString().trim());
                        customProjectHeight = customProjectLevels * 3.0f;
                    } catch (Exception ignored) {}

                    float shiftX = 35f, shiftY = -25f;
                    try {
                        String[] sp = inputShift.getText().toString().trim().split("[\\s,;]+");
                        if (sp.length >= 2) {
                            shiftX = Float.parseFloat(sp[0]);
                            shiftY = Float.parseFloat(sp[1]);
                        }
                    } catch (Exception ignored) {}

                    parseDxfOrIfcFile(fName, shiftX, shiftY);
                })
                .setNeutralButton("Очистить проект", (dialog, which) -> {
                    synchronized (customProjectPolygon) {
                        customProjectPolygon.clear();
                    }
                    overlayView.invalidate();
                    Toast.makeText(this, "Проектный контур удален с генплана", Toast.LENGTH_SHORT).show();
                })
                .setNegativeButton("Отмена", null)
                .show();
    }

    private void parseDxfOrIfcFile(String fileName, float offsetX, float offsetY) {
        try {
            File dir = Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DOWNLOADS);
            if (!dir.exists()) dir.mkdirs();
            File file = new File(dir, fileName);

            if (!file.exists()) {
                // Создаем корректный файл образца DXF с секцией ENTITIES -> LWPOLYLINE
                FileWriter fw = new FileWriter(file);
                fw.append("0\nSECTION\n2\nENTITIES\n0\nLWPOLYLINE\n8\nPROJECT_BIM\n90\n4\n70\n1\n");
                fw.append("10\n-14.0\n20\n-9.0\n");
                fw.append("10\n14.0\n20\n-9.0\n");
                fw.append("10\n14.0\n20\n9.0\n");
                fw.append("10\n-14.0\n20\n9.0\n");
                fw.append("0\nENDSEC\n0\nEOF\n");
                fw.flush();
                fw.close();
            }

            List<float[]> rawPts = new ArrayList<>();
            BufferedReader br = new BufferedReader(new FileReader(file));
            String lower = fileName.toLowerCase(Locale.US);

            if (lower.endsWith(".dxf")) {
                String line;
                Float pendingX = null;
                boolean inEntities = false;
                while ((line = br.readLine()) != null) {
                    String code = line.trim();
                    String val = br.readLine();
                    if (val == null) break;
                    val = val.trim();
                    if ("2".equals(code) && "ENTITIES".equalsIgnoreCase(val)) {
                        inEntities = true;
                    }
                    if (inEntities || rawPts.size() < 50) {
                        if ("10".equals(code)) {
                            try { pendingX = Float.parseFloat(val); } catch (Exception ignored) {}
                        } else if ("20".equals(code) && pendingX != null) {
                            try {
                                float py = Float.parseFloat(val);
                                rawPts.add(new float[]{pendingX, py});
                                pendingX = null;
                            } catch (Exception ignored) {}
                        }
                    }
                }
            } else if (lower.endsWith(".ifc")) {
                Pattern ifcPt = Pattern.compile("IFCCARTESIANPOINT\\s*\\(\\s*\\(\\s*([-0-9.]+)\\s*,\\s*([-0-9.]+)", Pattern.CASE_INSENSITIVE);
                String line;
                while ((line = br.readLine()) != null) {
                    Matcher m = ifcPt.matcher(line);
                    if (m.find()) {
                        float px = Float.parseFloat(m.group(1));
                        float py = Float.parseFloat(m.group(2));
                        rawPts.add(new float[]{px, py});
                    }
                }
            } else {
                String line;
                while ((line = br.readLine()) != null) {
                    String[] parts = line.trim().split("[\\s,;]+");
                    if (parts.length >= 2) {
                        try {
                            rawPts.add(new float[]{Float.parseFloat(parts[0]), Float.parseFloat(parts[1])});
                        } catch (Exception ignored) {}
                    }
                }
            }
            br.close();

            if (rawPts.size() < 3) {
                Toast.makeText(this, "В файле найдено меньше 3 точек контура", Toast.LENGTH_LONG).show();
                return;
            }

            // Нормализуем центр контура и применяем смещение посадки на генплане
            float cx = 0f, cy = 0f;
            for (float[] p : rawPts) {
                cx += p[0];
                cy += p[1];
            }
            cx /= rawPts.size();
            cy /= rawPts.size();

            synchronized (customProjectPolygon) {
                customProjectPolygon.clear();
                for (float[] p : rawPts) {
                    customProjectPolygon.add(new float[]{(p[0] - cx) + offsetX, (p[1] - cy) + offsetY});
                }
            }
            customProjectName = fileName + " (" + customProjectLevels + "эт)";
            is2DMapMode = true;
            btnModeToggle.setText("Камера AR");
            overlayView.invalidate();
            Toast.makeText(this, "Импортирован " + fileName + ": " + rawPts.size() + " вершин (" + customProjectLevels + " эт.)", Toast.LENGTH_LONG).show();
        } catch (Exception e) {
            Toast.makeText(this, "Ошибка импорта: " + e.getMessage(), Toast.LENGTH_SHORT).show();
        }
    }

    // --- 1b. Калькулятор КЕО по точкам и Тепловая карта (СП 52.13330) ---
    private void showKeoGridDialog() {
        AlertDialog.Builder builder = new AlertDialog.Builder(this);
        builder.setTitle("Сетка КЕО и Тепловая карта (СП 52.13330)");

        String extText = (externalLuxForKeo > 0) ? String.format(Locale.US, "%.0f лк", externalLuxForKeo) : "не задано";
        String wText = (keoWindowLux > 0 && externalLuxForKeo > 0)
                ? String.format(Locale.US, "%.0f лк (КЕО %.2f%%)", keoWindowLux, (keoWindowLux / externalLuxForKeo) * 100f)
                : (keoWindowLux > 0 ? String.format(Locale.US, "%.0f лк", keoWindowLux) : "нет");
        String cText = (keoCenterLux > 0 && externalLuxForKeo > 0)
                ? String.format(Locale.US, "%.0f лк (КЕО %.2f%%)", keoCenterLux, (keoCenterLux / externalLuxForKeo) * 100f)
                : (keoCenterLux > 0 ? String.format(Locale.US, "%.0f лк", keoCenterLux) : "нет");
        String bText = (keoBackLux > 0 && externalLuxForKeo > 0)
                ? String.format(Locale.US, "%.0f лк (КЕО %.2f%%)", keoBackLux, (keoBackLux / externalLuxForKeo) * 100f)
                : (keoBackLux > 0 ? String.format(Locale.US, "%.0f лк", keoBackLux) : "нет");

        CharSequence[] actions = new CharSequence[]{
                "1. Зафиксировать улицу E_наруж (сейчас: " + String.format(Locale.US, "%.0f лк", currentLux) + ")",
                "2. Записать точку 1 — У окна (" + wText + ")",
                "3. Записать точку 2 — Центр комнаты (" + cText + ")",
                "4. Записать точку 3 — Дальний угол (" + bText + ")",
                showKeoHeatmap ? "5. Скрыть тепловую карту КЕО с экрана" : "5. Показать ТЕПЛОВУЮ КАРТУ КЕО на экране"
        };

        builder.setItems(actions, (dialog, which) -> {
            float safeLux = Math.max(1f, currentLux);
            if (which == 0) {
                externalLuxForKeo = safeLux;
                recalculateAverageKeo();
                Toast.makeText(this, "Наружный свет E_нар = " + externalLuxForKeo + " лк", Toast.LENGTH_SHORT).show();
            } else if (which == 1) {
                keoWindowLux = safeLux;
                if (externalLuxForKeo <= 0) externalLuxForKeo = Math.max(5000f, safeLux * 15f);
                recalculateAverageKeo();
                Toast.makeText(this, "Точка у окна сохранена: " + keoWindowLux + " лк", Toast.LENGTH_SHORT).show();
            } else if (which == 2) {
                keoCenterLux = safeLux;
                if (externalLuxForKeo <= 0) externalLuxForKeo = Math.max(5000f, safeLux * 30f);
                recalculateAverageKeo();
                Toast.makeText(this, "Центр комнаты сохранен: " + keoCenterLux + " лк", Toast.LENGTH_SHORT).show();
            } else if (which == 3) {
                keoBackLux = safeLux;
                if (externalLuxForKeo <= 0) externalLuxForKeo = Math.max(5000f, safeLux * 60f);
                recalculateAverageKeo();
                Toast.makeText(this, "Дальний угол сохранен: " + keoBackLux + " лк", Toast.LENGTH_SHORT).show();
            } else if (which == 4) {
                if (externalLuxForKeo <= 0) {
                    externalLuxForKeo = 5000f;
                    if (keoWindowLux <= 0) keoWindowLux = 220f;
                    if (keoCenterLux <= 0) keoCenterLux = 85f;
                    if (keoBackLux <= 0) keoBackLux = 32f;
                    recalculateAverageKeo();
                }
                showKeoHeatmap = !showKeoHeatmap;
            }
            if (overlayView != null) overlayView.invalidate();
        });
        builder.setNegativeButton("Закрыть", null);
        builder.show();
    }

    private void recalculateAverageKeo() {
        if (externalLuxForKeo <= 0) return;
        float sum = 0f;
        int cnt = 0;
        if (keoWindowLux > 0) { sum += (keoWindowLux / externalLuxForKeo) * 100f; cnt++; }
        if (keoCenterLux > 0) { sum += (keoCenterLux / externalLuxForKeo) * 100f; cnt++; }
        if (keoBackLux > 0) { sum += (keoBackLux / externalLuxForKeo) * 100f; cnt++; }
        if (cnt > 0) {
            lastCalculatedKeo = sum / cnt;
        } else {
            lastCalculatedKeo = (currentLux / externalLuxForKeo) * 100f;
        }
    }

    // --- 1c. Генерация настоящего PDF-акта инспекции (android.graphics.pdf.PdfDocument) ---
    private void generateInspectionReportPdf() {
        try {
            File dir = new File(Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DOWNLOADS), "BIM_Reports");
            if (!dir.exists()) dir.mkdirs();
            String timeStampFile = new SimpleDateFormat("yyyyMMdd_HHmmss", Locale.US).format(new Date());
            File pdfFile = new File(dir, "BIM_Inspection_Act_" + timeStampFile + ".pdf");

            PdfDocument pdfDoc = new PdfDocument();
            PdfDocument.PageInfo pageInfo = new PdfDocument.PageInfo.Builder(595, 842, 1).create(); // Формат A4
            PdfDocument.Page page = pdfDoc.startPage(pageInfo);
            Canvas c = page.getCanvas();
            Paint p = new Paint(Paint.ANTI_ALIAS_FLAG);

            // Шапка документа
            p.setColor(Color.rgb(20, 35, 60));
            c.drawRect(0, 0, 595, 85, p);
            p.setColor(Color.WHITE);
            p.setTextSize(18f);
            p.setFakeBoldText(true);
            c.drawText("АКТ ПОЛЕВОГО СТРОЙКОНТРОЛЯ И ИНСОЛЯЦИИ (BIM SUN & LEVEL)", 30, 38, p);
            p.setTextSize(11f);
            p.setFakeBoldText(false);
            String dateStr = new SimpleDateFormat("dd.MM.yyyy HH:mm:ss", Locale.US).format(new Date());
            c.drawText("Дата формирования: " + dateStr + " | Нормативы: СанПиН 1.2.3685-21, СП 52.13330", 30, 62, p);

            // Блок 1: Геопривязка и высотные отметки
            p.setColor(Color.BLACK);
            p.setFakeBoldText(true);
            p.setTextSize(13f);
            c.drawText("1. ГЕОДЕЗИЧЕСКАЯ И ВЫСОТНАЯ ПРИВЯЗКА ОБЪЕКТА", 30, 115, p);
            p.setFakeBoldText(false);
            p.setTextSize(11.5f);
            int estFloor = Math.round(relativeHeightMeters / floorHeightMeters) + 1;
            c.drawText(String.format(Locale.US, "• Координаты GPS: %.5f N, %.5f E (%s)", latitude, longitude, osmStatus), 35, 138, p);
            c.drawText(String.format(Locale.US, "• Высотная отметка H: %+.2f м (Расчетный этаж: %d эт., P = %.1f гПа)", relativeHeightMeters, estFloor, currentPressure), 35, 158, p);
            c.drawText(String.format(Locale.US, "• Азимут оси визирования: %.1f° (%s) | Высота камеры: %.1f°", camAzimuth, getCardinalStatic(camAzimuth), camAltitude), 35, 178, p);

            // Блок 2: Таблица контроля уклонов и AR-рулетки
            p.setFakeBoldText(true);
            p.setTextSize(13f);
            c.drawText("2. КОНТРОЛЬ УКЛОНОВ И ГЕОМЕТРИИ КОНСТРУКЦИЙ", 30, 212, p);
            p.setFakeBoldText(false);
            p.setTextSize(11.5f);
            float calPitch = rawPitch - tarePitch;
            float calRoll = rawRoll - tareRoll;
            float slopePct = (float) (Math.tan(Math.toRadians(Math.abs(calPitch))) * 100.0);
            float slopeMm = slopePct * 10f;
            c.drawText(String.format(Locale.US, "• Продольный уклон: %.2f°  |  %.2f %%  |  %.0f мм на 1 м.п. (Крен: %.2f°)", calPitch, slopePct, slopeMm, calRoll), 35, 234, p);
            if (arMeasuredDistance > 0) {
                c.drawText(String.format(Locale.US, "• Замер AR-рулетки: дистанция D = %.2f м, высота элемента H = %.2f м", arMeasuredDistance, arMeasuredHeight), 35, 254, p);
            } else {
                c.drawText("• Замер AR-рулетки: не проводился в текущей сессии", 35, 254, p);
            }

            // Блок 3: Инсоляция по СанПиН и КЕО по СП 52.13330
            float[] insol = calculateInsolationWithOsm(latitude, selectedDayOfYear);
            boolean sanPinPass = insol[1] >= 2.0f;
            p.setFakeBoldText(true);
            p.setTextSize(13f);
            c.drawText("3. РАСЧЕТ ИНСОЛЯЦИИ (СанПиН) И ОСВЕЩЕННОСТИ КЕО (СП 52.13330)", 30, 288, p);
            p.setFakeBoldText(false);
            p.setTextSize(11.5f);
            c.drawText(String.format(Locale.US, "• Расчетная дата: %s | Астрономический день: %.1f ч", selectedSeasonLabel, insol[0]), 35, 310, p);
            p.setColor(sanPinPass ? Color.rgb(0, 125, 50) : Color.rgb(190, 30, 30));
            p.setFakeBoldText(true);
            c.drawText(String.format(Locale.US, "• Продолжительность инсоляции (с учетом затенения): %.1f ч — %s",
                    insol[1], sanPinPass ? "НОРМА СОБЛЮДЕНА (>= 2.0 ч)" : "НАРУШЕНИЕ НОРМЫ (< 2.0 ч)"), 35, 330, p);

            p.setColor(Color.BLACK);
            p.setFakeBoldText(false);
            String keoSummary = (lastCalculatedKeo > 0)
                    ? String.format(Locale.US, "%.2f %% (%s)", lastCalculatedKeo, lastCalculatedKeo >= 0.5f ? "Соответствует СП 52" : "Ниже нормы СП 52 (<0.5%)")
                    : "не замерялся";
            c.drawText(String.format(Locale.US, "• Фактическая освещенность: %.0f лк | Средний КЕО по точкам: %s", currentLux, keoSummary), 35, 350, p);

            // Блок 4: Графическая схема 2D-генплана и теней прямо на листе PDF
            p.setFakeBoldText(true);
            p.setTextSize(13f);
            c.drawText("4. СИТУАЦИОННЫЙ ГЕНПЛАН КВАРТАЛА И КАРТА ТЕНЕЙ", 30, 385, p);

            c.save();
            RectF mapBox = new RectF(35, 398, 560, 775);
            c.clipRect(mapBox);
            p.setStyle(Paint.Style.FILL);
            p.setColor(Color.rgb(242, 246, 250));
            c.drawRect(mapBox, p);

            float mCx = mapBox.centerX();
            float mCy = mapBox.centerY();
            float pdfScale = 1.35f;

            p.setStyle(Paint.Style.STROKE);
            p.setStrokeWidth(1f);
            p.setColor(Color.rgb(180, 195, 210));
            c.drawLine(mapBox.left, mCy, mapBox.right, mCy, p);
            c.drawLine(mCx, mapBox.top, mCx, mapBox.bottom, p);
            c.drawCircle(mCx, mCy, 50 * pdfScale, p);
            c.drawCircle(mCx, mCy, 100 * pdfScale, p);

            double[] sunPos = computeSunPosition(latitude, selectedDayOfYear, displayedClockHour);
            double sunAz = sunPos[0];
            double sunAlt = Math.max(12.0, sunPos[1]);
            double shRad = Math.toRadians(sunAz + 180.0);
            float shX = (float) Math.sin(shRad);
            float shY = (float) Math.cos(shRad);
            double tanAlt = Math.max(0.15, Math.tan(Math.toRadians(sunAlt)));

            List<OsmBuilding> allB = getAllBuildingsWithCustom();
            for (OsmBuilding b : allB) {
                float len = Math.min(180f, (float) (b.heightMeters / tanAlt));
                p.setStyle(Paint.Style.FILL);
                p.setColor(Color.argb(70, 80, 90, 110));
                int n = b.xMeters.length;
                Path sp = new Path();
                for (int i = 0; i < n; i++) {
                    int next = (i + 1) % n;
                    sp.reset();
                    sp.moveTo(mCx + b.xMeters[i] * pdfScale, mCy - b.yMeters[i] * pdfScale);
                    sp.lineTo(mCx + b.xMeters[next] * pdfScale, mCy - b.yMeters[next] * pdfScale);
                    sp.lineTo(mCx + (b.xMeters[next] + shX * len) * pdfScale, mCy - (b.yMeters[next] + shY * len) * pdfScale);
                    sp.lineTo(mCx + (b.xMeters[i] + shX * len) * pdfScale, mCy - (b.yMeters[i] + shY * len) * pdfScale);
                    sp.close();
                    c.drawPath(sp, p);
                }
            }

            for (OsmBuilding b : allB) {
                Path bp = new Path();
                int n = b.xMeters.length;
                float sx = 0, sy = 0;
                for (int i = 0; i < n; i++) {
                    float px = mCx + b.xMeters[i] * pdfScale;
                    float py = mCy - b.yMeters[i] * pdfScale;
                    sx += px; sy += py;
                    if (i == 0) bp.moveTo(px, py);
                    else bp.lineTo(px, py);
                }
                bp.close();
                p.setStyle(Paint.Style.FILL);
                p.setColor(b.isCustomProject ? Color.rgb(180, 235, 255) : Color.rgb(200, 212, 228));
                c.drawPath(bp, p);
                p.setStyle(Paint.Style.STROKE);
                p.setStrokeWidth(1.5f);
                p.setColor(b.isCustomProject ? Color.rgb(0, 130, 200) : Color.rgb(60, 85, 120));
                c.drawPath(bp, p);

                p.setStyle(Paint.Style.FILL);
                p.setColor(Color.BLACK);
                p.setTextSize(8.5f);
                c.drawText(b.levels + "эт", (sx / n) - 8, (sy / n) + 3, p);
            }

            p.setColor(Color.RED);
            c.drawCircle(mCx, mCy, 5f, p);
            c.restore();

            p.setStyle(Paint.Style.STROKE);
            p.setColor(Color.DKGRAY);
            c.drawRect(mapBox, p);

            p.setStyle(Paint.Style.FILL);
            p.setTextSize(10f);
            c.drawText("Подпись инженера стройконтроля: _______________________ / Сформировано автоматически в BIM Sun & Level", 35, 810, p);

            pdfDoc.finishPage(page);

            FileOutputStream fos = new FileOutputStream(pdfFile);
            pdfDoc.writeTo(fos);
            fos.flush();
            fos.close();
            pdfDoc.close();

            Toast.makeText(this, "PDF-Акт сохранен: Download/BIM_Reports/" + pdfFile.getName(), Toast.LENGTH_LONG).show();
        } catch (Exception e) {
            Toast.makeText(this, "Ошибка генерации PDF: " + e.getMessage(), Toast.LENGTH_LONG).show();
        }
    }

    // --- 1d. Интерактивная AR-рулетка и привязка высотных отметок ΔH ---
    private void toggleArTapeMode() {
        isArTapeMode = !isArTapeMode;
        if (isArTapeMode) {
            is2DMapMode = false;
            btnModeToggle.setText("2D План");
            arAngleBaseDeg = null;
            arAngleTopDeg = null;
            arMeasuredDistance = -1f;
            arMeasuredHeight = -1f;
            savedBaroMarkHeight = relativeHeightMeters;
            Toast.makeText(this, "AR-Рулетка включена: наведите прицел на НИЗ объекта и тапните по экрану", Toast.LENGTH_LONG).show();
        } else {
            Toast.makeText(this, "AR-Рулетка выключена", Toast.LENGTH_SHORT).show();
        }
        overlayView.invalidate();
    }

    private void handleArTapeTap() {
        if (arAngleBaseDeg == null) {
            arAngleBaseDeg = camAltitude;
            Toast.makeText(this, String.format(Locale.US, "Низ зафиксирован (%.1f°). Теперь наведите на ВЕРХ объекта и тапните!", arAngleBaseDeg), Toast.LENGTH_LONG).show();
        } else if (arAngleTopDeg == null) {
            arAngleTopDeg = camAltitude;
            // Вычисляем дистанцию D и высоту объекта H по двум углам визирования
            double baseRad = Math.toRadians(Math.abs(arAngleBaseDeg));
            if (baseRad < 0.03) baseRad = 0.03;
            arMeasuredDistance = (float) (arEyeHeightMeters / Math.tan(baseRad));
            double topRad = Math.toRadians(arAngleTopDeg);
            arMeasuredHeight = (float) (arEyeHeightMeters + arMeasuredDistance * Math.tan(topRad));
            if (arMeasuredHeight < 0) arMeasuredHeight = Math.abs(arMeasuredHeight);
            Toast.makeText(this, String.format(Locale.US, "Замер готов: Дистанция D = %.2f м, Высота H = %.2f м", arMeasuredDistance, arMeasuredHeight), Toast.LENGTH_LONG).show();
        } else {
            arAngleBaseDeg = null;
            arAngleTopDeg = null;
            arMeasuredDistance = -1f;
            arMeasuredHeight = -1f;
            savedBaroMarkHeight = relativeHeightMeters;
            Toast.makeText(this, "Сброс замера AR-рулетки. Наведите на НИЗ объекта", Toast.LENGTH_SHORT).show();
        }
        overlayView.invalidate();
    }

    // --- Надежная загрузка зданий OpenStreetMap (POST + GET с гео-кэшем и без фейковых домов) ---
    private void loadCachedOsmIfAvailable() {
        try {
            SharedPreferences prefs = getSharedPreferences("osm_cache_v5", MODE_PRIVATE);
            String cachedJson = prefs.getString("json", null);
            double cLat = Double.longBitsToDouble(prefs.getLong("lat", 0));
            double cLon = Double.longBitsToDouble(prefs.getLong("lon", 0));
            if (cachedJson != null && Math.abs(cLat) > 1.0) {
                int count = parseOsmJson(cachedJson, cLat, cLon);
                if (count > 0) {
                    latitude = cLat;
                    longitude = cLon;
                    lastOsmLat = cLat;
                    lastOsmLon = cLon;
                    realOsmLoaded = true;
                    osmStatus = "Карта OSM (кэш): " + count + " домов";
                }
            }
        } catch (Exception ignored) {}
    }

    private void saveOsmCache(String json, double lat, double lon) {
        try {
            SharedPreferences prefs = getSharedPreferences("osm_cache_v5", MODE_PRIVATE);
            prefs.edit()
                    .putString("json", json)
                    .putLong("lat", Double.doubleToRawLongBits(lat))
                    .putLong("lon", Double.doubleToRawLongBits(lon))
                    .apply();
        } catch (Exception ignored) {}
    }

    private void fetchOsmBuildings(final double lat, final double lon) {
        if (!isFetchingOsm.compareAndSet(false, true)) return;

        if (!realOsmLoaded) {
            osmStatus = "Загрузка реальных домов OSM...";
            if (overlayView != null) overlayView.postInvalidate();
        }

        new Thread(() -> {
            double south = lat - 0.0028;
            double north = lat + 0.0028;
            double west = lon - 0.0042;
            double east = lon + 0.0042;

            // Оптимизированный запрос `out body geom;` — в 5 раз быстрее, без рекурсии узлов `>;` (устраняет HTTP 504)
            String query = String.format(Locale.US,
                    "[out:json][timeout:18];way[\"building\"](%.5f,%.5f,%.5f,%.5f);out body geom;",
                    south, west, north, east);

            String[] endpoints = new String[]{
                    "https://overpass.private.coffee/api/interpreter",
                    "https://overpass-api.de/api/interpreter",
                    "https://lz4.overpass-api.de/api/interpreter",
                    "https://overpass.kumi.systems/api/interpreter",
                    "https://maps.mail.ru/osm/tools/overpass/api/interpreter"
            };

            boolean success = false;
            StringBuilder errLog = new StringBuilder();

            for (String endpoint : endpoints) {
                HttpURLConnection conn = null;
                try {
                    // Используем POST с правильными заголовками Accept, чтобы избежать ошибки HTTP 406
                    URL url = new URL(endpoint);
                    conn = (HttpURLConnection) url.openConnection();
                    conn.setRequestMethod("POST");
                    conn.setDoOutput(true);
                    conn.setConnectTimeout(7000);
                    conn.setReadTimeout(10000);
                    conn.setRequestProperty("User-Agent", "BIMSunLevelFieldInspector/2.0 (Android; Ryazan)");
                    conn.setRequestProperty("Accept", "application/json, */*");
                    conn.setRequestProperty("Content-Type", "application/x-www-form-urlencoded; charset=UTF-8");

                    String postBody = "data=" + URLEncoder.encode(query, "UTF-8");
                    OutputStream os = conn.getOutputStream();
                    os.write(postBody.getBytes(StandardCharsets.UTF_8));
                    os.flush();
                    os.close();

                    int code = conn.getResponseCode();
                    if (code == 200) {
                        BufferedReader reader = new BufferedReader(
                                new InputStreamReader(conn.getInputStream(), StandardCharsets.UTF_8));
                        StringBuilder sb = new StringBuilder();
                        String line;
                        while ((line = reader.readLine()) != null) {
                            sb.append(line);
                        }
                        reader.close();

                        String jsonStr = sb.toString();
                        int count = parseOsmJson(jsonStr, lat, lon);
                        if (count > 0) {
                            lastOsmLat = lat;
                            lastOsmLon = lon;
                            realOsmLoaded = true;
                            saveOsmCache(jsonStr, lat, lon);
                            success = true;
                            break;
                        }
                    } else {
                        errLog.append("HTTP").append(code).append(" ");
                    }
                } catch (Exception e) {
                    String name = e.getClass().getSimpleName().replace("Exception", "");
                    errLog.append(name).append(" ");
                } finally {
                    if (conn != null) conn.disconnect();
                }
            }

            final boolean ok = success;
            final String errStr = errLog.toString().trim();
            isFetchingOsm.set(false);

            runOnUiThread(() -> {
                if (ok) {
                    osmStatus = "Карта OSM: " + osmBuildings.size() + " реальных домов";
                } else if (!realOsmLoaded) {
                    osmStatus = "Сбой сети (" + (errStr.isEmpty() ? "таймаут" : errStr) + ") — тапните сверху";
                }
                if (overlayView != null) overlayView.invalidate();
            });
        }).start();
    }

    private int parseOsmJson(String jsonStr, double centerLat, double centerLon) throws Exception {
        JSONObject root = new JSONObject(jsonStr);
        JSONArray elements = root.optJSONArray("elements");
        if (elements == null) return 0;

        double metersPerDegLat = 111132.0;
        double metersPerDegLon = 111320.0 * Math.cos(Math.toRadians(centerLat));

        Map<Long, float[]> nodeMap = new HashMap<>();
        for (int i = 0; i < elements.length(); i++) {
            JSONObject el = elements.getJSONObject(i);
            if ("node".equals(el.optString("type"))) {
                long id = el.getLong("id");
                double ptLat = el.getDouble("lat");
                double ptLon = el.getDouble("lon");
                float xm = (float) ((ptLon - centerLon) * metersPerDegLon);
                float ym = (float) ((ptLat - centerLat) * metersPerDegLat);
                nodeMap.put(id, new float[]{xm, ym});
            }
        }

        List<OsmBuilding> parsed = new ArrayList<>();
        for (int i = 0; i < elements.length(); i++) {
            JSONObject el = elements.getJSONObject(i);
            if (!"way".equals(el.optString("type")) && el.optJSONArray("geometry") == null) {
                continue;
            }

            int levels = -1;
            float height = -1f;
            String houseNum = "";

            JSONObject tags = el.optJSONObject("tags");
            if (tags != null) {
                houseNum = tags.optString("addr:housenumber", "").trim();
                String lvlStr = tags.optString("building:levels", "");
                if (!lvlStr.isEmpty()) {
                    try {
                        levels = Integer.parseInt(lvlStr.replaceAll("[^0-9]", ""));
                    } catch (Exception ignored) {}
                }
                String hStr = tags.optString("height", "");
                if (!hStr.isEmpty()) {
                    try {
                        height = Float.parseFloat(hStr.replace(",", ".").replaceAll("[^0-9.]", ""));
                    } catch (Exception ignored) {}
                }
            }

            if (levels <= 0 && height > 2f) {
                levels = Math.max(1, Math.round(height / 3.0f));
            }
            if (levels <= 0) levels = 5;
            if (height <= 2f) height = levels * 3.0f;

            JSONArray geom = el.optJSONArray("geometry");
            if (geom != null && geom.length() >= 3) {
                OsmBuilding b = new OsmBuilding();
                b.xMeters = new float[geom.length()];
                b.yMeters = new float[geom.length()];
                for (int j = 0; j < geom.length(); j++) {
                    JSONObject pt = geom.getJSONObject(j);
                    double ptLat = pt.getDouble("lat");
                    double ptLon = pt.getDouble("lon");
                    b.xMeters[j] = (float) ((ptLon - centerLon) * metersPerDegLon);
                    b.yMeters[j] = (float) ((ptLat - centerLat) * metersPerDegLat);
                }
                b.levels = levels;
                b.heightMeters = height;
                b.houseNumber = houseNum;
                parsed.add(b);
                continue;
            }

            JSONArray nodesArr = el.optJSONArray("nodes");
            if (nodesArr != null && nodesArr.length() >= 3 && !nodeMap.isEmpty()) {
                List<float[]> pts = new ArrayList<>();
                for (int j = 0; j < nodesArr.length(); j++) {
                    float[] xy = nodeMap.get(nodesArr.getLong(j));
                    if (xy != null) pts.add(xy);
                }
                if (pts.size() >= 3) {
                    OsmBuilding b = new OsmBuilding();
                    b.xMeters = new float[pts.size()];
                    b.yMeters = new float[pts.size()];
                    for (int j = 0; j < pts.size(); j++) {
                        b.xMeters[j] = pts.get(j)[0];
                        b.yMeters[j] = pts.get(j)[1];
                    }
                    b.levels = levels;
                    b.heightMeters = height;
                    b.houseNumber = houseNum;
                    parsed.add(b);
                }
            }
        }

        if (!parsed.isEmpty()) {
            synchronized (osmBuildings) {
                osmBuildings.clear();
                osmBuildings.addAll(parsed);
            }
        }
        return parsed.size();
    }

    private void showEditBuildingDialog(OsmBuilding b) {
        LinearLayout layout = new LinearLayout(this);
        layout.setOrientation(LinearLayout.VERTICAL);
        layout.setPadding(50, 30, 50, 10);

        final EditText inputLevels = new EditText(this);
        inputLevels.setHint("Количество этажей");
        inputLevels.setInputType(InputType.TYPE_CLASS_NUMBER);
        inputLevels.setText(String.valueOf(b.levels));
        layout.addView(inputLevels);

        String title = "Здание " + (b.houseNumber != null && !b.houseNumber.isEmpty() ? "д." + b.houseNumber : "на генплане");
        new AlertDialog.Builder(this)
                .setTitle(title)
                .setMessage("Измените этажность для пересчета тени:")
                .setView(layout)
                .setPositiveButton("Сохранить", (dialog, which) -> {
                    try {
                        int lvl = Integer.parseInt(inputLevels.getText().toString().trim());
                        if (lvl > 0) {
                            b.levels = lvl;
                            b.heightMeters = lvl * 3.0f;
                            if (b.isCustomProject) {
                                customProjectLevels = lvl;
                                customProjectHeight = b.heightMeters;
                            }
                            if (overlayView != null) overlayView.invalidate();
                            Toast.makeText(this, "Высота обновлена: " + lvl + " эт. (" + b.heightMeters + " м)", Toast.LENGTH_SHORT).show();
                        }
                    } catch (Exception ignored) {}
                })
                .setNegativeButton("Отмена", null)
                .show();
    }

    private void showAltitudeCalibrationDialog() {
        LinearLayout layout = new LinearLayout(this);
        layout.setOrientation(LinearLayout.VERTICAL);
        layout.setPadding(50, 30, 50, 10);

        final EditText inputFloor = new EditText(this);
        inputFloor.setHint("Номер текущего этажа (например, 5)");
        inputFloor.setInputType(InputType.TYPE_CLASS_NUMBER | InputType.TYPE_NUMBER_FLAG_SIGNED);
        int currentEstFloor = Math.round(relativeHeightMeters / floorHeightMeters) + 1;
        inputFloor.setText(String.valueOf(currentEstFloor));
        layout.addView(inputFloor);

        final EditText inputStep = new EditText(this);
        inputStep.setHint("Высота этажа в метрах (например, 3.0)");
        inputStep.setInputType(InputType.TYPE_CLASS_NUMBER | InputType.TYPE_NUMBER_FLAG_DECIMAL);
        inputStep.setText(String.format(Locale.US, "%.1f", floorHeightMeters));
        layout.addView(inputStep);

        new AlertDialog.Builder(this)
                .setTitle("Привязка этажа и отметки ΔH")
                .setMessage("Укажите этаж, на котором вы находитесь:")
                .setView(layout)
                .setPositiveButton("Привязать этаж", (dialog, which) -> {
                    try {
                        int fl = Integer.parseInt(inputFloor.getText().toString().trim());
                        float step = Float.parseFloat(inputStep.getText().toString().trim());
                        if (step > 1.0f) floorHeightMeters = step;
                        basePressure = currentPressure;
                        calibratedBaseHeight = (fl - 1) * floorHeightMeters;
                        savedBaroMarkHeight = calibratedBaseHeight;
                        Toast.makeText(this, String.format(Locale.US,
                                "Привязан %d этаж (Отметка %+.2f м)", fl, calibratedBaseHeight),
                                Toast.LENGTH_SHORT).show();
                    } catch (Exception ignored) {}
                })
                .setNeutralButton("Фикс. репер ΔH=0", (dialog, which) -> {
                    savedBaroMarkHeight = relativeHeightMeters;
                    Toast.makeText(this, "Барометрический репер ΔH обнулен на текущей высоте", Toast.LENGTH_SHORT).show();
                })
                .setNegativeButton("Отмена", null)
                .show();
    }

    private void cycleSeason() {
        if (selectedDayOfYear != 172 && selectedDayOfYear != 80 && selectedDayOfYear != 355) {
            selectedDayOfYear = 80;
            selectedSeasonLabel = "21 Мар/Сен (Равноденствие)";
        } else if (selectedDayOfYear == 80) {
            selectedDayOfYear = 172;
            selectedSeasonLabel = "21 Июня (Летний пик)";
        } else if (selectedDayOfYear == 172) {
            selectedDayOfYear = 355;
            selectedSeasonLabel = "21 Декабря (Зимний минимум)";
        } else {
            Calendar cal = Calendar.getInstance();
            selectedDayOfYear = cal.get(Calendar.DAY_OF_YEAR);
            selectedSeasonLabel = "Сегодня (день #" + selectedDayOfYear + ")";
        }
        Toast.makeText(this, "Расчетная дата: " + selectedSeasonLabel, Toast.LENGTH_SHORT).show();
        if (overlayView != null) overlayView.invalidate();
    }

    private void syncWithRealTime() {
        Calendar cal = Calendar.getInstance();
        int hr = cal.get(Calendar.HOUR_OF_DAY);
        int min = cal.get(Calendar.MINUTE);
        int sec = cal.get(Calendar.SECOND);
        targetClockHour = hr + (min / 60.0) + (sec / 3600.0);

        if (timeSeekBar != null) {
            timeSeekBar.setProgress(hr * 60 + min);
        }
        if (timeLabelView != null) {
            updateTimeLabelColors();
            timeLabelView.setText(String.format(Locale.US, "Сейчас: %02d:%02d:%02d", hr, min, sec));
        }
    }

    private String formatClockHour(double ch, boolean live) {
        int totalMin = (int) Math.round(ch * 60.0);
        if (totalMin < 0) totalMin = 0;
        if (totalMin > 1439) totalMin = 1439;
        int h = totalMin / 60;
        int m = totalMin % 60;
        return String.format(Locale.US, "%s: %02d:%02d", live ? "Сейчас" : "Ручн", h, m);
    }

    private Button createButton(String text, int bgColor) {
        Button b = new Button(this);
        b.setText(text);
        b.setTextSize(9.5f);
        b.setTextColor(Color.WHITE);
        b.setBackgroundColor(bgColor);
        b.setPadding(2, 12, 2, 12);
        LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f);
        lp.setMargins(2, 0, 2, 0);
        b.setLayoutParams(lp);
        return b;
    }

    private void exportLogToCsv() {
        try {
            File dir = Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DOWNLOADS);
            if (!dir.exists()) dir.mkdirs();
            File file = new File(dir, "BIM_Field_Log.csv");
            boolean isNew = !file.exists();

            FileWriter fw = new FileWriter(file, true);
            if (isNew) {
                fw.append("Timestamp,Lat,Lon,CamAzimuth_deg,CamAltitude_deg,SlopePitch_deg,Slope_mm_per_m,Lux,KEO_percent,DeltaHeight_m,EstFloor,ClockHour\n");
            }
            String ts = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss", Locale.US).format(new Date());
            float calPitch = rawPitch - tarePitch;
            float mmPerMeter = (float) (Math.tan(Math.toRadians(Math.abs(calPitch))) * 1000.0);
            int estFloor = Math.round(relativeHeightMeters / floorHeightMeters) + 1;

            fw.append(String.format(Locale.US, "%s,%.5f,%.5f,%.1f,%.1f,%.2f,%.1f,%.0f,%.2f,%.2f,%d,%.2f\n",
                    ts, latitude, longitude, camAzimuth, camAltitude, calPitch, mmPerMeter,
                    currentLux, lastCalculatedKeo, relativeHeightMeters, estFloor, displayedClockHour));
            fw.flush();
            fw.close();
            Toast.makeText(this, "Сохранено в Download/BIM_Field_Log.csv", Toast.LENGTH_LONG).show();
        } catch (Exception e) {
            Toast.makeText(this, "Ошибка записи: " + e.getMessage(), Toast.LENGTH_SHORT).show();
        }
    }

    private void captureARPhoto() {
        int targetW = overlayView.getWidth();
        int targetH = overlayView.getHeight();
        if (targetW <= 0 || targetH <= 0) return;

        if (is2DMapMode || camera == null) {
            saveCombinedBitmapToGallery(null, targetW, targetH);
            return;
        }

        try {
            camera.setOneShotPreviewCallback((data, cam) -> {
                try {
                    Camera.Parameters params = cam.getParameters();
                    Camera.Size prevSize = params.getPreviewSize();

                    YuvImage yuvImage = new YuvImage(data, ImageFormat.NV21, prevSize.width, prevSize.height, null);
                    ByteArrayOutputStream baos = new ByteArrayOutputStream();
                    yuvImage.compressToJpeg(new Rect(0, 0, prevSize.width, prevSize.height), 95, baos);
                    byte[] jpegBytes = baos.toByteArray();
                    Bitmap rawCamBitmap = BitmapFactory.decodeByteArray(jpegBytes, 0, jpegBytes.length);

                    Matrix matrix = new Matrix();
                    matrix.postRotate(90);
                    Bitmap rotatedCamBitmap = Bitmap.createBitmap(
                            rawCamBitmap, 0, 0, rawCamBitmap.getWidth(), rawCamBitmap.getHeight(), matrix, true
                    );
                    rawCamBitmap.recycle();

                    saveCombinedBitmapToGallery(rotatedCamBitmap, targetW, targetH);
                } catch (Exception e) {
                    Toast.makeText(this, "Ошибка сохранения фото: " + e.getMessage(), Toast.LENGTH_SHORT).show();
                }
            });
        } catch (Exception e) {
            Toast.makeText(this, "Сбой захвата кадра: " + e.getMessage(), Toast.LENGTH_SHORT).show();
        }
    }

    private void saveCombinedBitmapToGallery(Bitmap cameraBitmap, int targetW, int targetH) {
        try {
            Bitmap combinedBitmap = Bitmap.createBitmap(targetW, targetH, Bitmap.Config.ARGB_8888);
            Canvas comboCanvas = new Canvas(combinedBitmap);

            if (cameraBitmap != null) {
                Rect destRect = new Rect(0, 0, targetW, targetH);
                comboCanvas.drawBitmap(cameraBitmap, null, destRect, null);
                cameraBitmap.recycle();
            }

            overlayView.draw(comboCanvas);

            Paint stampPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
            stampPaint.setColor(Color.argb(215, 15, 20, 28));
            comboCanvas.drawRoundRect(new RectF(20, targetH - 220, targetW - 20, targetH - 155), 16f, 16f, stampPaint);

            stampPaint.setColor(Color.rgb(255, 220, 90));
            stampPaint.setTextSize(26f);
            String timeStamp = new SimpleDateFormat("dd.MM.yyyy HH:mm:ss", Locale.US).format(new Date());
            comboCanvas.drawText("ФИКСАЦИЯ: " + timeStamp + " | " + formatClockHour(displayedClockHour, isLiveTime), 36, targetH - 178, stampPaint);

            String fileName = "BIM_AR_" + new SimpleDateFormat("yyyyMMdd_HHmmss", Locale.US).format(new Date()) + ".jpg";
            ContentValues values = new ContentValues();
            values.put(MediaStore.Images.Media.DISPLAY_NAME, fileName);
            values.put(MediaStore.Images.Media.MIME_TYPE, "image/jpeg");
            values.put(MediaStore.Images.Media.RELATIVE_PATH, Environment.DIRECTORY_PICTURES + "/BIM_SunLevel");

            Uri uri = getContentResolver().insert(MediaStore.Images.Media.EXTERNAL_CONTENT_URI, values);
            if (uri != null) {
                OutputStream out = getContentResolver().openOutputStream(uri);
                if (out != null) {
                    combinedBitmap.compress(Bitmap.CompressFormat.JPEG, 92, out);
                    out.flush();
                    out.close();
                }
                Toast.makeText(this, "Снимок сохранен в Галерею (BIM_SunLevel)", Toast.LENGTH_LONG).show();
            }
            combinedBitmap.recycle();
        } catch (Exception e) {
            Toast.makeText(this, "Ошибка записи: " + e.getMessage(), Toast.LENGTH_SHORT).show();
        }
    }

    // --- Разрешения, Камера и Датчики ---
    private void requestPermissionsIfNeeded() {
        if (checkSelfPermission(Manifest.permission.CAMERA) != PackageManager.PERMISSION_GRANTED ||
            checkSelfPermission(Manifest.permission.ACCESS_FINE_LOCATION) != PackageManager.PERMISSION_GRANTED) {
            requestPermissions(new String[]{
                    Manifest.permission.CAMERA,
                    Manifest.permission.ACCESS_FINE_LOCATION,
                    Manifest.permission.ACCESS_COARSE_LOCATION
            }, 101);
        } else {
            startLocationUpdates();
        }
    }

    @Override
    public void onRequestPermissionsResult(int requestCode, String[] permissions, int[] grantResults) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults);
        if (requestCode == 101) {
            startLocationUpdates();
            if (checkSelfPermission(Manifest.permission.CAMERA) == PackageManager.PERMISSION_GRANTED
                    && cameraSurface != null && cameraSurface.getHolder().getSurface().isValid()) {
                startCameraPreview(cameraSurface.getHolder());
            }
        }
    }

    private void startLocationUpdates() {
        try {
            if (checkSelfPermission(Manifest.permission.ACCESS_FINE_LOCATION) == PackageManager.PERMISSION_GRANTED) {
                Location last = locationManager.getLastKnownLocation(LocationManager.GPS_PROVIDER);
                if (last == null) last = locationManager.getLastKnownLocation(LocationManager.NETWORK_PROVIDER);
                if (last != null) {
                    onNewLocation(last);
                }
                LocationListener listener = this::onNewLocation;
                locationManager.requestLocationUpdates(LocationManager.GPS_PROVIDER, 4000, 5f, listener);
                locationManager.requestLocationUpdates(LocationManager.NETWORK_PROVIDER, 4000, 5f, listener);
            }
        } catch (Exception ignored) {}
    }

    private void onNewLocation(Location loc) {
        latitude = loc.getLatitude();
        longitude = loc.getLongitude();
        gpsLocked = true;
        double distSq = Math.pow((latitude - lastOsmLat) * 111132.0, 2) +
                        Math.pow((longitude - lastOsmLon) * 65000.0, 2);
        if (!realOsmLoaded || distSq > 2500.0) {
            fetchOsmBuildings(latitude, longitude);
        }
    }

    @Override
    protected void onResume() {
        super.onResume();
        if (sensorManager != null) {
            if (rotSensor != null) sensorManager.registerListener(this, rotSensor, SensorManager.SENSOR_DELAY_GAME);
            if (accelSensor != null) sensorManager.registerListener(this, accelSensor, SensorManager.SENSOR_DELAY_UI);
            if (pressureSensor != null) sensorManager.registerListener(this, pressureSensor, SensorManager.SENSOR_DELAY_UI);
            if (lightSensor != null) sensorManager.registerListener(this, lightSensor, SensorManager.SENSOR_DELAY_UI);
        }
        if (!is2DMapMode && cameraSurface != null && cameraSurface.getHolder().getSurface().isValid()) {
            startCameraPreview(cameraSurface.getHolder());
        }
    }

    @Override
    protected void onPause() {
        super.onPause();
        if (sensorManager != null) sensorManager.unregisterListener(this);
        stopCameraPreview();
    }

    @Override
    public void onSensorChanged(SensorEvent event) {
        int type = event.sensor.getType();
        if (type == Sensor.TYPE_ROTATION_VECTOR) {
            SensorManager.getRotationMatrixFromVector(rotationMatrix, event.values);
            SensorManager.remapCoordinateSystem(rotationMatrix,
                    SensorManager.AXIS_X, SensorManager.AXIS_Z, remappedMatrix);
            SensorManager.getOrientation(remappedMatrix, orientationVals);

            float az = (float) Math.toDegrees(orientationVals[0]);
            if (az < 0) az += 360f;
            float alt = (float) -Math.toDegrees(orientationVals[1]);
            float roll = (float) Math.toDegrees(orientationVals[2]);

            camAzimuth = lowPassAngle(az, camAzimuth, 0.15f);
            camAltitude = camAltitude + 0.15f * (alt - camAltitude);
            camRoll = camRoll + 0.15f * (roll - camRoll);

        } else if (type == Sensor.TYPE_ACCELEROMETER) {
            float gx = event.values[0];
            float gy = event.values[1];
            float gz = event.values[2];
            float pitchDeg = (float) Math.toDegrees(Math.atan2(gy, Math.sqrt(gx * gx + gz * gz)));
            float rollDeg = (float) Math.toDegrees(Math.atan2(-gx, Math.sqrt(gy * gy + gz * gz)));
            rawPitch = rawPitch + 0.12f * (pitchDeg - rawPitch);
            rawRoll = rawRoll + 0.12f * (rollDeg - rawRoll);

        } else if (type == Sensor.TYPE_PRESSURE) {
            currentPressure = (basePressure < 0) ? event.values[0] : (currentPressure + 0.15f * (event.values[0] - currentPressure));
            if (basePressure < 0) basePressure = currentPressure;

            float deltaFromBase = 44330f * (1f - (float) Math.pow(currentPressure / basePressure, 0.190295f));
            relativeHeightMeters = calibratedBaseHeight + deltaFromBase;

        } else if (type == Sensor.TYPE_LIGHT) {
            currentLux = event.values[0];
        }

        if (isLiveTime && !isAnimatingTimeline) {
            syncWithRealTime();
        }
        if (overlayView != null) overlayView.invalidate();
    }

    private float lowPassAngle(float newAngle, float oldAngle, float alpha) {
        float diff = newAngle - oldAngle;
        if (diff > 180f) diff -= 360f;
        if (diff < -180f) diff += 360f;
        float res = oldAngle + alpha * diff;
        if (res < 0) res += 360f;
        if (res >= 360f) res -= 360f;
        return res;
    }

    @Override
    public void onAccuracyChanged(Sensor sensor, int accuracy) {}

    @Override
    public void surfaceCreated(SurfaceHolder holder) {
        if (checkSelfPermission(Manifest.permission.CAMERA) == PackageManager.PERMISSION_GRANTED) {
            startCameraPreview(holder);
        }
    }

    @Override
    public void surfaceChanged(SurfaceHolder holder, int format, int width, int height) {
        if (checkSelfPermission(Manifest.permission.CAMERA) == PackageManager.PERMISSION_GRANTED) {
            startCameraPreview(holder);
        }
    }

    @Override
    public void surfaceDestroyed(SurfaceHolder holder) {
        stopCameraPreview();
    }

    private void startCameraPreview(SurfaceHolder holder) {
        try {
            if (camera == null) {
                camera = Camera.open();
            }
            if (camera != null) {
                camera.stopPreview();
                Camera.Parameters params = camera.getParameters();
                List<String> focusModes = params.getSupportedFocusModes();
                if (focusModes != null && focusModes.contains(Camera.Parameters.FOCUS_MODE_CONTINUOUS_PICTURE)) {
                    params.setFocusMode(Camera.Parameters.FOCUS_MODE_CONTINUOUS_PICTURE);
                }
                camera.setParameters(params);
                camera.setDisplayOrientation(90);
                camera.setPreviewDisplay(holder);
                camera.startPreview();
            }
        } catch (Exception ignored) {}
    }

    private void stopCameraPreview() {
        if (camera != null) {
            try {
                camera.stopPreview();
                camera.release();
            } catch (Exception ignored) {}
            camera = null;
        }
    }

    private static String getCardinalStatic(float az) {
        String[] dirs = {"С", "СВ", "В", "ЮВ", "Ю", "ЮЗ", "З", "СЗ"};
        return dirs[Math.round(az / 45f) % 8];
    }

    // --- Графическое ядро: AR-камера, 2D-генплан, Тепловая карта КЕО, Мини-радар и Плавная анимация ---
    private class AROverlayView extends View {
        private final Paint paint = new Paint(Paint.ANTI_ALIAS_FLAG);
        private final Path path = new Path();
        private final DashPathEffect dashEffect = new DashPathEffect(new float[]{16f, 10f}, 0f);

        public AROverlayView(Context context) { super(context); }

        @Override
        protected void onDraw(Canvas canvas) {
            super.onDraw(canvas);
            int w = getWidth();
            int h = getHeight();

            // Плавная интерполяция времени для мягкого движения солнца и теней (60 FPS)
            if (isAnimatingTimeline) {
                targetClockHour += 0.04;
                if (targetClockHour > 21.0) targetClockHour = 5.0;
                if (timeSeekBar != null) timeSeekBar.setProgress((int) (targetClockHour * 60));
                if (timeLabelView != null) timeLabelView.setText(formatClockHour(targetClockHour, false));
            }
            double diffTime = targetClockHour - displayedClockHour;
            if (Math.abs(diffTime) > 0.002) {
                displayedClockHour += diffTime * 0.25;
                postInvalidateOnAnimation();
            } else {
                displayedClockHour = targetClockHour;
            }
            if (isAnimatingTimeline) {
                postInvalidateOnAnimation();
            }

            // Пункт 0: В режиме AR фон остается полностью прозрачным, чтобы работала камера!
            if (is2DMapMode) {
                int bgColor = isLightFieldTheme ? Color.rgb(238, 243, 248) : Color.rgb(14, 22, 34);
                canvas.drawColor(bgColor);
                draw2DTopDownMap(canvas, w, h);
            } else {
                drawARCameraOverlay(canvas, w, h);
            }

            if (showKeoHeatmap) {
                drawKeoHeatmapOverlay(canvas, w, h);
            }

            drawTelemetryHeader(canvas, w);
        }

        private void draw2DTopDownMap(Canvas canvas, int w, int h) {
            float cx = w / 2f;
            float cy = h * 0.57f;
            float scale = mapScalePixelsPerMeter;

            paint.setStyle(Paint.Style.STROKE);
            paint.setStrokeWidth(1.5f);
            paint.setColor(isLightFieldTheme ? Color.argb(110, 90, 115, 145) : Color.argb(70, 90, 140, 190));
            canvas.drawLine(0, cy, w, cy, paint);
            canvas.drawLine(cx, 410, cx, h - 180, paint);

            paint.setTextSize(21f);
            for (int rMeters : new int[]{50, 100, 150, 200}) {
                float rPx = rMeters * scale;
                canvas.drawCircle(cx, cy, rPx, paint);
                paint.setStyle(Paint.Style.FILL);
                paint.setColor(isLightFieldTheme ? Color.rgb(50, 70, 95) : Color.LTGRAY);
                canvas.drawText(rMeters + "м", cx + 6, cy - rPx + 20, paint);
                paint.setStyle(Paint.Style.STROKE);
                paint.setColor(isLightFieldTheme ? Color.argb(110, 90, 115, 145) : Color.argb(70, 90, 140, 190));
            }

            paint.setStyle(Paint.Style.FILL);
            paint.setColor(isLightFieldTheme ? Color.rgb(0, 115, 90) : Color.rgb(0, 230, 180));
            paint.setTextSize(25f);
            canvas.drawText("СЕВЕР (С)", cx - 60, 435, paint);
            canvas.drawText("ЮГ (Ю)", cx - 45, h - 220, paint);
            canvas.drawText("З", 20, cy - 10, paint);
            canvas.drawText("В", w - 40, cy - 10, paint);

            paint.setColor(isLightFieldTheme ? Color.argb(45, 0, 160, 110) : Color.argb(45, 0, 255, 180));
            RectF fovRect = new RectF(cx - 120 * scale, cy - 120 * scale, cx + 120 * scale, cy + 120 * scale);
            float startAngle2D = camAzimuth - 90f - 30f;
            canvas.drawArc(fovRect, startAngle2D, 60f, true, paint);

            double[] sunPos = computeSunPosition(latitude, selectedDayOfYear, displayedClockHour);
            double sunAz = sunPos[0];
            double sunAlt = sunPos[1];

            double shadowAzRad = Math.toRadians(sunAz + 180.0);
            float shDirX = (float) Math.sin(shadowAzRad);
            float shDirY = (float) Math.cos(shadowAzRad);
            double tanAlt = Math.max(0.08, Math.tan(Math.toRadians(Math.max(1.0, sunAlt))));

            List<OsmBuilding> allBuildings = getAllBuildingsWithCustom();

            if (sunAlt > 0.5) {
                paint.setStyle(Paint.Style.FILL);
                paint.setColor(isLightFieldTheme ? Color.argb(85, 80, 95, 115) : Color.argb(145, 4, 8, 15));
                for (OsmBuilding b : allBuildings) {
                    float shadowLen = Math.min(260f, (float) (b.heightMeters / tanAlt));
                    drawBuildingShadow(canvas, b, cx, cy, scale, shDirX * shadowLen, shDirY * shadowLen);
                }

                paint.setColor(isLightFieldTheme ? Color.argb(85, 185, 70, 210) : Color.argb(120, 180, 70, 220));
                for (OsmBuilding b : allBuildings) {
                    float dh = b.heightMeters - relativeHeightMeters;
                    if (dh > 0.5f) {
                        float floorShadowLen = Math.min(260f, (float) (dh / tanAlt));
                        drawBuildingShadow(canvas, b, cx, cy, scale, shDirX * floorShadowLen, shDirY * floorShadowLen);
                    }
                }
            }

            // Отрисовка домов с цветовой индикацией (красный = затеняет, зеленый = ваш дом, пурпурный = DXF/IFC проект)
            for (OsmBuilding b : allBuildings) {
                path.reset();
                float sumX = 0f, sumY = 0f;
                int n = b.xMeters.length;
                for (int i = 0; i < n; i++) {
                    float sx = cx + b.xMeters[i] * scale;
                    float sy = cy - b.yMeters[i] * scale;
                    sumX += sx;
                    sumY += sy;
                    if (i == 0) path.moveTo(sx, sy);
                    else path.lineTo(sx, sy);
                }
                path.close();

                boolean isUserInside = isPointInPolygon(0f, 0f, b.xMeters, b.yMeters);
                boolean blocksSun = doesBuildingBlockSunNowOrToday(b, sunAz, sunAlt);

                paint.setStyle(Paint.Style.FILL);
                if (b.isCustomProject) {
                    paint.setColor(Color.argb(185, 0, 170, 230));
                } else if (isUserInside) {
                    paint.setColor(isLightFieldTheme ? Color.argb(210, 140, 235, 185) : Color.argb(220, 35, 115, 95));
                } else if (blocksSun) {
                    paint.setColor(isLightFieldTheme ? Color.argb(215, 255, 165, 165) : Color.argb(215, 135, 40, 45));
                } else {
                    paint.setColor(isLightFieldTheme ? Color.argb(200, 195, 210, 230) : Color.argb(205, 55, 80, 110));
                }
                canvas.drawPath(path, paint);

                paint.setStyle(Paint.Style.STROKE);
                if (b.isCustomProject) {
                    paint.setPathEffect(dashEffect);
                    paint.setStrokeWidth(4.5f);
                    paint.setColor(Color.rgb(255, 0, 180));
                } else {
                    paint.setPathEffect(null);
                    paint.setStrokeWidth(isUserInside || blocksSun ? 4f : 2.2f);
                    paint.setColor(blocksSun ? Color.rgb(255, 65, 65)
                            : (isUserInside ? Color.rgb(0, 200, 110)
                            : (isLightFieldTheme ? Color.rgb(50, 90, 140) : Color.rgb(140, 195, 245))));
                }
                canvas.drawPath(path, paint);
                paint.setPathEffect(null);

                paint.setStyle(Paint.Style.FILL);
                paint.setColor(isLightFieldTheme ? Color.BLACK : Color.WHITE);
                paint.setTextSize(18.5f);
                String label = (b.houseNumber != null && !b.houseNumber.isEmpty())
                        ? (b.houseNumber + " (" + b.levels + "эт)")
                        : (b.levels + "эт");
                canvas.drawText(label, (sumX / n) - 24f, (sumY / n) + 6f, paint);
            }

            if (sunAlt > 0) {
                float sunVecX = (float) Math.sin(Math.toRadians(sunAz));
                float sunVecY = (float) Math.cos(Math.toRadians(sunAz));
                float sunScreenX = cx + sunVecX * 250f;
                float sunScreenY = cy - sunVecY * 250f;

                paint.setStyle(Paint.Style.STROKE);
                paint.setStrokeWidth(5f);
                paint.setColor(Color.rgb(255, 195, 0));
                canvas.drawLine(cx, cy, sunScreenX, sunScreenY, paint);

                paint.setStyle(Paint.Style.FILL);
                canvas.drawCircle(sunScreenX, sunScreenY, 18f, paint);
            }

            boolean inShadowNow = isSunBlockedByOsmBuildings(sunAz, sunAlt);
            paint.setStyle(Paint.Style.FILL);
            paint.setColor(inShadowNow ? Color.rgb(230, 50, 50) : Color.rgb(0, 210, 105));
            canvas.drawCircle(cx, cy, 12f, paint);

            paint.setColor(isLightFieldTheme ? Color.BLACK : Color.LTGRAY);
            paint.setTextSize(22f);
            String shadowStatus = (sunAlt <= 0) ? "Ночь (потяните ползунок или нажмите ▶ для анимации теней)" :
                    (inShadowNow ? "ТОЧКА В ТЕНИ (перекрыта красным зданием)" : "ПРЯМОЕ СОЛНЦЕ (тень проходит мимо этажа)");
            canvas.drawText(shadowStatus, 25, h - 188, paint);
        }

        private void drawBuildingShadow(Canvas canvas, OsmBuilding b, float cx, float cy, float scale, float offX, float offY) {
            int n = b.xMeters.length;
            for (int i = 0; i < n; i++) {
                int next = (i + 1) % n;
                path.reset();
                path.moveTo(cx + b.xMeters[i] * scale, cy - b.y
