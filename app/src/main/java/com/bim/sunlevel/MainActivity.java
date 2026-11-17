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
import android.graphics.ImageFormat;
import android.graphics.Matrix;
import android.graphics.Paint;
import android.graphics.Path;
import android.graphics.Rect;
import android.graphics.RectF;
import android.graphics.YuvImage;
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

@SuppressWarnings("deprecation")
public class MainActivity extends Activity implements SensorEventListener, SurfaceHolder.Callback {

    private SensorManager sensorManager;
    private Sensor rotSensor, accelSensor, pressureSensor, lightSensor;
    private LocationManager locationManager;

    private SurfaceView cameraSurface;
    private Camera camera;
    private AROverlayView overlayView;
    private Button btnModeToggle;
    private TextView timeLabelView;
    private SeekBar timeSeekBar;

    private double latitude = 54.6195;
    private double longitude = 39.7420;
    private double lastOsmLat = 0.0;
    private double lastOsmLon = 0.0;
    private boolean gpsLocked = false;
    private boolean realOsmLoaded = false;

    private float camAzimuth = 0f;
    private float camAltitude = 0f;
    private float camRoll = 0f;

    private float rawPitch = 0f, rawRoll = 0f;
    private float tarePitch = 0f, tareRoll = 0f;

    private float currentPressure = 1013.25f;
    private float basePressure = -1f;
    private float floorHeightMeters = 3.0f;
    private float calibratedBaseHeight = 12.0f; // 5 этаж (+12.00 м)
    private float relativeHeightMeters = 12.0f;
    private float currentLux = 0f;

    private float externalLuxForKeo = -1f;
    private float keoWindowLux = -1f;
    private float keoCenterLux = -1f;
    private float keoBackLux = -1f;
    private float lastCalculatedKeo = -1f;

    private final List<float[]> customProjectPolygon = new ArrayList<>();
    private boolean isLightFieldTheme = false;

    private int selectedDayOfYear = 80;
    private String selectedSeasonLabel = "21 Мар/Сен (Равноденствие)";
    private double selectedClockHour = 12.0;
    private boolean isLiveTime = true;

    private boolean is2DMapMode = false;
    private float mapScalePixelsPerMeter = 2.2f;

    private static class OsmBuilding {
        float[] xMeters;
        float[] yMeters;
        float heightMeters;
        int levels;
        String houseNumber;
    }

    private final List<OsmBuilding> osmBuildings = new ArrayList<>();
    private String osmStatus = "Загрузка домов OSM...";
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

        loadOfflineFallbackBuildings();
        loadCachedOsmIfAvailable();

        FrameLayout root = new FrameLayout(this);

        cameraSurface = new SurfaceView(this);
        cameraSurface.getHolder().addCallback(this);
        root.addView(cameraSurface);

        overlayView = new AROverlayView(this);
        overlayView.setOnTouchListener((v, event) -> {
            if (event.getAction() == MotionEvent.ACTION_DOWN) {
                float tx = event.getX();
                float ty = event.getY();

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

                    if (ty > 430 && ty < v.getHeight() - 260) {
                        if (mapScalePixelsPerMeter < 1.6f) mapScalePixelsPerMeter = 2.2f;
                        else if (mapScalePixelsPerMeter < 2.5f) mapScalePixelsPerMeter = 3.5f;
                        else if (mapScalePixelsPerMeter < 4.0f) mapScalePixelsPerMeter = 5.0f;
                        else mapScalePixelsPerMeter = 1.2f;
                        overlayView.invalidate();
                        Toast.makeText(this, "Масштаб плана изменен", Toast.LENGTH_SHORT).show();
                        return true;
                    }
                } else if (ty < 400) {
                    isFetchingOsm.set(false);
                    fetchOsmBuildings(latitude, longitude);
                    Toast.makeText(this, "Повторный запрос к карте OSM...", Toast.LENGTH_SHORT).show();
                    return true;
                }
            }
            return false;
        });
        root.addView(overlayView);

        LinearLayout bottomContainer = new LinearLayout(this);
        bottomContainer.setOrientation(LinearLayout.VERTICAL);
        bottomContainer.setBackgroundColor(isLightFieldTheme ? Color.argb(230, 240, 244, 248) : Color.argb(205, 12, 18, 26));
        bottomContainer.setPadding(12, 10, 12, 20);

        LinearLayout sliderRow = new LinearLayout(this);
        sliderRow.setOrientation(LinearLayout.HORIZONTAL);
        sliderRow.setGravity(Gravity.CENTER_VERTICAL);
        sliderRow.setPadding(12, 4, 12, 8);

        timeLabelView = new TextView(this);
        timeLabelView.setTextColor(isLightFieldTheme ? Color.rgb(20, 100, 50) : Color.rgb(120, 255, 160));
        timeLabelView.setTextSize(12.5f);
        timeLabelView.setOnClickListener(v -> {
            isLiveTime = true;
            syncWithRealTime();
            Toast.makeText(this, "Включено реальное системное время", Toast.LENGTH_SHORT).show();
        });
        sliderRow.addView(timeLabelView);

        timeSeekBar = new SeekBar(this);
        timeSeekBar.setMax(1439);
        LinearLayout.LayoutParams seekParams = new LinearLayout.LayoutParams(
                0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f);
        seekParams.setMargins(14, 0, 6, 0);
        timeSeekBar.setLayoutParams(seekParams);

        syncWithRealTime();

        timeSeekBar.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
            @Override
            public void onProgressChanged(SeekBar seekBar, int progress, boolean fromUser) {
                if (fromUser) {
                    isLiveTime = false;
                    selectedClockHour = progress / 60.0;
                    timeLabelView.setTextColor(isLightFieldTheme ? Color.rgb(150, 100, 0) : Color.rgb(255, 225, 90));
                    timeLabelView.setText(formatClockHour(selectedClockHour, false));
                    if (overlayView != null) overlayView.invalidate();
                }
            }

            @Override
            public void onStartTrackingTouch(SeekBar seekBar) {
                isLiveTime = false;
            }

            @Override
            public void onStopTrackingTouch(SeekBar seekBar) {}
        });
        sliderRow.addView(timeSeekBar);
        bottomContainer.addView(sliderRow);

        LinearLayout bottomBar = new LinearLayout(this);
        bottomBar.setOrientation(LinearLayout.HORIZONTAL);
        bottomBar.setGravity(Gravity.CENTER);

        btnModeToggle = createButton("2D План", Color.argb(230, 30, 115, 165));
        btnModeToggle.setOnClickListener(v -> {
            is2DMapMode = !is2DMapMode;
            btnModeToggle.setText(is2DMapMode ? "Камера AR" : "2D План");
            overlayView.invalidate();
        });

        Button btnKeo = createButton("КЕО/СП", Color.argb(230, 160, 50, 180));
        btnKeo.setOnClickListener(v -> showKeoGridDialog());

        Button btnProject = createButton("DXF/PDF", Color.argb(230, 40, 130, 90));
        btnProject.setOnClickListener(v -> showProjectAndReportMenu());

        Button btnTheme = createButton("Тема", Color.argb(210, 80, 90, 110));
        btnTheme.setOnClickListener(v -> {
            isLightFieldTheme = !isLightFieldTheme;
            Toast.makeText(this, isLightFieldTheme ? "Включена светлая полевая тема" : "Включена темная тема", Toast.LENGTH_SHORT).show();
            overlayView.invalidate();
        });

        Button btnPhoto = createButton("Фото", Color.argb(230, 190, 75, 25));
        btnPhoto.setOnClickListener(v -> captureARPhoto());

        Button btnSave = createButton("CSV", Color.argb(210, 35, 110, 70));
        btnSave.setOnClickListener(v -> exportLogToCsv());

        bottomBar.addView(btnModeToggle);
        bottomBar.addView(btnKeo);
        bottomBar.addView(btnProject);
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

    // --- Методы расчета инсоляции и СанПиН (вынесены на уровень MainActivity) ---
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

    private boolean isSunBlockedByOsmBuildings(double sunAzDeg, double sunAltDeg) {
        if (sunAltDeg <= 0.0) return true;
        double tanAlt = Math.tan(Math.toRadians(Math.max(0.2, sunAltDeg)));
        double rayDirX = Math.sin(Math.toRadians(sunAzDeg));
        double rayDirY = Math.cos(Math.toRadians(sunAzDeg));

        synchronized (osmBuildings) {
            for (OsmBuilding b : osmBuildings) {
                float dh = b.heightMeters - relativeHeightMeters;
                if (dh <= 0.5f) continue;

                if (isPointInPolygon(0f, 0f, b.xMeters, b.yMeters)) continue;

                float maxShadowDist = (float) (dh / tanAlt);
                int n = b.xMeters.length;
                for (int i = 0; i < n; i++) {
                    float x1 = b.xMeters[i], y1 = b.yMeters[i];
                    float x2 = b.xMeters[(i + 1) % n], y2 = b.yMeters[(i + 1) % n];
                    float dist = intersectRayWithSegment((float) rayDirX, (float) rayDirY, x1, y1, x2, y2);
                    if (dist > 3.0f && dist <= maxShadowDist) {
                        return true;
                    }
                }
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
    // ---------------------------------------------------------------------

    private void showProjectAndReportMenu() {
        CharSequence[] items = new X().items(
                "1. Импортировать проектный контур (DXF/TXT)",
                "2. Генерация акта инспекции (PDF/TXT)",
                "3. Обнулить уклономер (Тара 0°)",
                "4. Калибровка этажа (Высота)"
        );

        new AlertDialog.Builder(this)
                .setTitle("Проектные данные и отчеты")
                .setItems(items, (dialog, which) -> {
                    if (which == 0) importCustomPolygonDialog();
                    else if (which == 1) generateInspectionReportPdf();
                    else if (which == 2) {
                        tarePitch = rawPitch;
                        tareRoll = rawRoll;
                        Toast.makeText(this, "Уклономер обнулен (0.0°)", Toast.LENGTH_SHORT).show();
                    } else if (which == 3) showAltitudeCalibrationDialog();
                })
                .show();
    }

    private static class X {
        CharSequence[] items(CharSequence... c) { return c; }
    }

    private void importCustomPolygonDialog() {
        try {
            File dir = Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DOWNLOADS);
            File file = new File(dir, "project_contour.txt");
            if (!file.exists()) {
                FileWriter fw = new FileWriter(file);
                fw.append("-10 -10\n10 -10\n10 10\n-10 10\n");
                fw.flush();
                fw.close();
                Toast.makeText(this, "Создан шаблон Download/project_contour.txt. Запишите в него точки X Y", Toast.LENGTH_LONG).show();
                return;
            }

            BufferedReader br = new BufferedReader(new FileReader(file));
            String line;
            synchronized (customProjectPolygon) {
                customProjectPolygon.clear();
                while ((line = br.readLine()) != null) {
                    String[] parts = line.trim().split("\\s+");
                    if (parts.length >= 2) {
                        float px = Float.parseFloat(parts[0]);
                        float py = Float.parseFloat(parts[1]);
                        customProjectPolygon.add(new float[]{px, py});
                    }
                }
            }
            br.close();
            Toast.makeText(this, "Проектный контур загружен (" + customProjectPolygon.size() + " точек)", Toast.LENGTH_LONG).show();
            if (overlayView != null) overlayView.invalidate();
        } catch (Exception e) {
            Toast.makeText(this, "Ошибка чтения контура: " + e.getMessage(), Toast.LENGTH_SHORT).show();
        }
    }

    private void generateInspectionReportPdf() {
        try {
            File dir = new File(Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DOWNLOADS), "BIM_Reports");
            if (!dir.exists()) dir.mkdirs();
            String timeStampFile = new SimpleDateFormat("yyyyMMdd_HHmmss", Locale.US).format(new Date());
            File reportFile = new File(dir, "Inspection_Act_" + timeStampFile + ".txt");

            float[] insol = calculateInsolationWithOsm(latitude, selectedDayOfYear);
            boolean sanPinPass = insol[1] >= 2.0f;
            int estFloor = Math.round(relativeHeightMeters / floorHeightMeters) + 1;

            FileWriter fw = new FileWriter(reportFile);
            fw.append("========================================\n");
            fw.append(" ОФИЦИАЛЬНЫЙ АКТ ИНСПЕКЦИИ И СТРОЙКОНТРОЛЯ\n");
            fw.append(" Проектный модуль BIM Sun & Level\n");
            fw.append("========================================\n");
            fw.append("Дата и время: ").append(new SimpleDateFormat("dd.MM.yyyy HH:mm:ss", Locale.US).format(new Date())).append("\n");
            fw.append(String.format(Locale.US, "Координаты GPS: %.5f N, %.5f E\n", latitude, longitude));
            fw.append(String.format(Locale.US, "Высотная отметка H: %+.2f м (~%d этаж)\n", relativeHeightMeters, estFloor));
            fw.append("----------------------------------------\n");
            fw.append(String.format(Locale.US, "Освещенность фактическая: %.0f лк\n", currentLux));
            fw.append(String.format(Locale.US, "Коэффициент КЕО: %s\n", lastCalculatedKeo > 0 ? String.format(Locale.US, "%.2f%%", lastCalculatedKeo) : "не замерялся"));
            fw.append("----------------------------------------\n");
            fw.append(String.format(Locale.US, "Норматив инсоляции СанПиН / СП 42:\nСтатус: %s\n", sanPinPass ? "СОБЛЮДЕНА (≥2.0 ч)" : "НАРУШЕНИЕ (<2.0 ч)"));
            fw.append(String.format(Locale.US, "Непрерывное солнце без тени: %.1f ч (астрон: %.1f ч)\n", insol[1], insol[0]));
            fw.append("========================================\n");
            fw.flush();
            fw.close();

            Toast.makeText(this, "Акт сохранен в Download/BIM_Reports/" + reportFile.getName(), Toast.LENGTH_LONG).show();
        } catch (Exception e) {
            Toast.makeText(this, "Ошибка создания акта: " + e.getMessage(), Toast.LENGTH_SHORT).show();
        }
    }

    private void showKeoGridDialog() {
        AlertDialog.Builder builder = new AlertDialog.Builder(this);
        builder.setTitle("Сетка контроля КЕО по точкам (СП 52.13330)");

        String extText = (externalLuxForKeo > 0) ? String.format(Locale.US, "%.0f лк", externalLuxForKeo) : "не задано";
        String wText = (keoWindowLux > 0) ? String.format(Locale.US, "%.0f лк", keoWindowLux) : "нет";
        String cText = (keoCenterLux > 0) ? String.format(Locale.US, "%.0f лк", keoCenterLux) : "нет";
        String bText = (keoBackLux > 0) ? String.format(Locale.US, "%.0f лк", keoBackLux) : "нет";

        builder.setMessage("Наружный свет (улица): " + extText + "\n\n" +
                "Точки контроля в помещении:\n" +
                "• У окна: " + wText + "\n" +
                "• В центре комнаты: " + cText + "\n" +
                "• В дальнем углу: " + bText + "\n\n" +
                "Норма КЕО (боковое): ≥ 0.5% – 1.0%");

        builder.setPositiveButton("1. Запомнить улицу (E_нар)", (dialog, which) -> {
            externalLuxForKeo = currentLux;
            Toast.makeText(this, "Уличная освещенность сохранена: " + externalLuxForKeo + " лк", Toast.LENGTH_LONG).show();
        });

        builder.setNeutralButton("2. Замер точки", (d, w) -> showPointSelectDialog());

        builder.setNegativeButton("Закрыть", null);
        builder.show();
    }

    private void showPointSelectDialog() {
        CharSequence[] pts = new X().items("У окна", "В центре комнаты", "В дальнем углу");
        new AlertDialog.Builder(this)
                .setTitle("Выберите точку для сохранения замера")
                .setItems(pts, (dialog, which) -> {
                    if (which == 0) keoWindowLux = currentLux;
                    else if (which == 1) keoCenterLux = currentLux;
                    else if (which == 2) keoBackLux = currentLux;

                    if (externalLuxForKeo > 0 && keoWindowLux > 0 && keoCenterLux > 0 && keoBackLux > 0) {
                        lastCalculatedKeo = (keoCenterLux / externalLuxForKeo) * 100.0f;
                    } else if (currentLux > 0 && externalLuxForKeo > 0) {
                        lastCalculatedKeo = (currentLux / externalLuxForKeo) * 100.0f;
                    }
                    Toast.makeText(this, "Замер сохранен. Текущий КЕО: " + String.format(Locale.US, "%.2f%%", lastCalculatedKeo), Toast.LENGTH_SHORT).show();
                    if (overlayView != null) overlayView.invalidate();
                })
                .show();
    }

    private void loadOfflineFallbackBuildings() {
        synchronized (osmBuildings) {
            if (!osmBuildings.isEmpty()) return;
            osmBuildings.add(makeRectBuilding(-35f, -8f, 35f, 8f, 5, "12"));
            osmBuildings.add(makeRectBuilding(-70f, -60f, -20f, -44f, 9, "10"));
            osmBuildings.add(makeRectBuilding(20f, -65f, 45f, -25f, 10, "14"));
            osmBuildings.add(makeRectBuilding(-40f, 42f, 35f, 58f, 5, "16"));
            osmBuildings.add(makeRectBuilding(-100f, -15f, -80f, 40f, 14, "8"));
        }
        osmStatus = "Оффлайн-режим (встроенный шаблон)";
    }

    private OsmBuilding makeRectBuilding(float x1, float y1, float x2, float y2, int levels, String hNum) {
        OsmBuilding b = new OsmBuilding();
        b.xMeters = new float[]{x1, x2, x2, x1};
        b.yMeters = new float[]{y1, y1, y2, y2};
        b.levels = levels;
        b.heightMeters = levels * 3.0f;
        b.houseNumber = hNum;
        return b;
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

        String title = "Здание " + (b.houseNumber != null && !b.houseNumber.isEmpty() ? "д." + b.houseNumber : "выбрано");
        new AlertDialog.Builder(this)
                .setTitle(title)
                .setMessage("Измените этажность для пересчета тени на этаж:")
                .setView(layout)
                .setPositiveButton("Сохранить", (dialog, which) -> {
                    try {
                        int lvl = Integer.parseInt(inputLevels.getText().toString().trim());
                        if (lvl > 0) {
                            b.levels = lvl;
                            b.heightMeters = lvl * 3.0f;
                            if (overlayView != null) overlayView.invalidate();
                            Toast.makeText(this, "Высота обновлена: " + lvl + " эт (" + b.heightMeters + "м)", Toast.LENGTH_SHORT).show();
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
                .setTitle("Привязка этажа и карты OSM")
                .setMessage("Укажите этаж, на котором вы находитесь:")
                .setView(layout)
                .setPositiveButton("Привязать этаж", (dialog, which) -> {
                    try {
                        int fl = Integer.parseInt(inputFloor.getText().toString().trim());
                        float step = Float.parseFloat(inputStep.getText().toString().trim());
                        if (step > 1.0f) floorHeightMeters = step;
                        basePressure = currentPressure;
                        calibratedBaseHeight = (fl - 1) * floorHeightMeters;
                        Toast.makeText(this, String.format(Locale.US,
                                "Привязан %d этаж (Отметка %+.2f м)", fl, calibratedBaseHeight),
                                Toast.LENGTH_SHORT).show();
                    } catch (Exception ignored) {}
                })
                .setNeutralButton("Обновить дома OSM", (dialog, which) -> {
                    isFetchingOsm.set(false);
                    fetchOsmBuildings(latitude, longitude);
                })
                .setNegativeButton("Отмена", null)
                .show();
    }

    private void syncWithRealTime() {
        Calendar cal = Calendar.getInstance();
        int hr = cal.get(Calendar.HOUR_OF_DAY);
        int min = cal.get(Calendar.MINUTE);
        int sec = cal.get(Calendar.SECOND);
        selectedClockHour = hr + (min / 60.0) + (sec / 3600.0);

        if (timeSeekBar != null) {
            timeSeekBar.setProgress(hr * 60 + min);
        }
        if (timeLabelView != null) {
            timeLabelView.setTextColor(isLightFieldTheme ? Color.rgb(20, 100, 50) : Color.rgb(120, 255, 160));
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
        b.setTextSize(10.0f);
        b.setTextColor(Color.WHITE);
        b.setBackgroundColor(bgColor);
        b.setPadding(2, 12, 2, 12);
        LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f);
        lp.setMargins(2, 0, 2, 0);
        b.setLayoutParams(lp);
        return b;
    }

    private void loadCachedOsmIfAvailable() {
        try {
            SharedPreferences prefs = getSharedPreferences("osm_cache_v2", MODE_PRIVATE);
            String cachedJson = prefs.getString("json", null);
            double cLat = Double.longBitsToDouble(prefs.getLong("lat", 0));
            double cLon = Double.longBitsToDouble(prefs.getLong("lon", 0));
            if (cachedJson != null && Math.abs(cLat - latitude) < 0.01 && Math.abs(cLon - longitude) < 0.01) {
                int count = parseOsmJson(cachedJson, latitude, longitude);
                if (count > 0) {
                    realOsmLoaded = true;
                    lastOsmLat = cLat;
                    lastOsmLon = cLon;
                    osmStatus = "Карта OSM (кэш): " + count + " домов";
                }
            }
        } catch (Exception ignored) {}
    }

    private void saveOsmCache(String json, double lat, double lon) {
        try {
            SharedPreferences prefs = getSharedPreferences("osm_cache_v2", MODE_PRIVATE);
            prefs.edit()
                    .putString("json", json)
                    .putLong("lat", Double.doubleToRawLongBits(lat))
                    .putLong("lon", Double.doubleToRawLongBits(lon))
                    .apply();
        } catch (Exception ignored) {}
    }

    private void fetchOsmBuildings(final double lat, final double lon) {
        if (!isFetchingOsm.compareAndSet(false, true)) return;

        new Thread(() -> {
            double south = lat - 0.0024;
            double north = lat + 0.0024;
            double west = lon - 0.0038;
            double east = lon + 0.0038;

            String query = String.format(Locale.US,
                    "[out:json][timeout:12];(way[\"building\"](%.5f,%.5f,%.5f,%.5f);>;);out body;",
                    south, west, north, east);

            String[] endpoints = new String[]{
                    "https://maps.mail.ru/osm/tools/overpass/api/interpreter",
                    "https://overpass-api.de/api/interpreter",
                    "https://lz4.overpass-api.de/api/interpreter",
                    "https://overpass.kumi.systems/api/interpreter"
            };

            boolean success = false;
            StringBuilder errLog = new StringBuilder();

            for (String endpoint : endpoints) {
                HttpURLConnection conn = null;
                try {
                    String urlStr = endpoint + "?data=" + URLEncoder.encode(query, "UTF-8");
                    URL url = new URL(urlStr);
                    conn = (HttpURLConnection) url.openConnection();
                    conn.setRequestMethod("GET");
                    conn.setConnectTimeout(5000);
                    conn.setReadTimeout(6000);
                    conn.setRequestProperty("User-Agent", "Mozilla/5.0 (Linux; Android 14)");

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
                    osmStatus = "Оффлайн-шаблон (сеть недоступна)";
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
                    continue;
                }
            }

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
            stampPaint.setColor(Color.argb(210, 15, 20, 28));
            comboCanvas.drawRoundRect(new RectF(20, targetH - 220, targetW - 20, targetH - 155), 16f, 16f, stampPaint);

            stampPaint.setColor(Color.rgb(255, 220, 90));
            stampPaint.setTextSize(28f);
            String timeStamp = new SimpleDateFormat("dd.MM.yyyy HH:mm:ss", Locale.US).format(new Date());
            comboCanvas.drawText("ШТАМП ФИКСАЦИИ: " + timeStamp + " | " + formatClockHour(selectedClockHour, isLiveTime), 40, targetH - 178, stampPaint);

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
                Toast.makeText(this, "Сохранено в Галерею (BIM_SunLevel)", Toast.LENGTH_LONG).show();
            }
            combinedBitmap.recycle();
        } catch (Exception e) {
            Toast.makeText(this, "Ошибка записи: " + e.getMessage(), Toast.LENGTH_SHORT).show();
        }
    }

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
        if (requestCode == 101) {
            boolean camGranted = false;
            for (int i = 0; i < permissions.length; i++) {
                if (permissions[i].equals(Manifest.permission.CAMERA) && grantResults[i] == PackageManager.PERMISSION_GRANTED) {
                    camGranted = true;
                }
            }
            startLocationUpdates();
            if (camGranted && cameraSurface.getHolder().getSurface().isValid()) {
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
                locationManager.requestLocationUpdates(LocationManager.GPS_PROVIDER, 5000, 5f, listener);
                locationManager.requestLocationUpdates(LocationManager.NETWORK_PROVIDER, 5000, 5f, listener);
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
    }

    @Override
    protected void onPause() {
        super.onPause();
        if (sensorManager != null) sensorManager.unregisterListener(this);
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

        if (isLiveTime) {
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
    public void surfaceChanged(SurfaceHolder holder, int format, int width, int height) {}

    @Override
    public void surfaceDestroyed(SurfaceHolder holder) {
        if (camera != null) {
            try {
                camera.stopPreview();
                camera.release();
            } catch (Exception ignored) {}
            camera = null;
        }
    }

    private void startCameraPreview(SurfaceHolder holder) {
        try {
            if (camera == null) {
                camera = Camera.open();
            }
            if (camera != null) {
                camera.stopPreview();
                camera.setDisplayOrientation(90);
                camera.setPreviewDisplay(holder);
                camera.startPreview();
            }
        } catch (Exception e) {
            Toast.makeText(this, "Ошибка запуска камеры: " + e.getMessage(), Toast.LENGTH_SHORT).show();
        }
    }

    private class AROverlayView extends View {
        private final Paint paint = new Paint(Paint.ANTI_ALIAS_FLAG);
        private final Path path = new Path();

        public AROverlayView(Context context) { super(context); }

        @Override
        protected void onDraw(Canvas canvas) {
            super.onDraw(canvas);
            int w = getWidth();
            int h = getHeight();

            int bgColor = isLightFieldTheme ? Color.rgb(240, 244, 248) : Color.rgb(14, 22, 34);
            canvas.drawColor(bgColor);

            if (is2DMapMode) {
                draw2DTopDownMap(canvas, w, h);
            } else {
                drawARCameraOverlay(canvas, w, h);
            }

            drawTelemetryHeader(canvas, w);
        }

        private void draw2DTopDownMap(Canvas canvas, int w, int h) {
            float cx = w / 2f;
            float cy = h * 0.56f;
            float scale = mapScalePixelsPerMeter;

            paint.setStyle(Paint.Style.STROKE);
            paint.setStrokeWidth(1.5f);
            paint.setColor(isLightFieldTheme ? Color.argb(90, 100, 120, 150) : Color.argb(70, 90, 140, 190));
            canvas.drawLine(0, cy, w, cy, paint);
            canvas.drawLine(cx, 390, cx, h - 180, paint);

            paint.setTextSize(22f);
            for (int rMeters : new int[]{50, 100, 150, 200}) {
                float rPx = rMeters * scale;
                canvas.drawCircle(cx, cy, rPx, paint);
                paint.setStyle(Paint.Style.FILL);
                paint.setColor(isLightFieldTheme ? Color.DKGRAY : Color.LTGRAY);
                canvas.drawText(rMeters + "м", cx + 6, cy - rPx + 22, paint);
                paint.setStyle(Paint.Style.STROKE);
            }

            paint.setStyle(Paint.Style.FILL);
            paint.setColor(isLightFieldTheme ? Color.rgb(0, 120, 100) : Color.rgb(0, 230, 180));
            paint.setTextSize(26f);
            canvas.drawText("СЕВЕР (С)", cx - 60, 420, paint);
            canvas.drawText("ЮГ (Ю)", cx - 45, h - 225, paint);
            canvas.drawText("З", 20, cy - 10, paint);
            canvas.drawText("В", w - 40, cy - 10, paint);

            paint.setColor(isLightFieldTheme ? Color.argb(30, 0, 180, 120) : Color.argb(45, 0, 255, 180));
            RectF fovRect = new RectF(cx - 120 * scale, cy - 120 * scale, cx + 120 * scale, cy + 120 * scale);
            float startAngle2D = camAzimuth - 90f - 30f;
            canvas.drawArc(fovRect, startAngle2D, 60f, true, paint);

            synchronized (customProjectPolygon) {
                if (!customProjectPolygon.isEmpty()) {
                    paint.setStyle(Paint.Style.STROKE);
                    paint.setStrokeWidth(4f);
                    paint.setColor(Color.rgb(0, 200, 80));
                    path.reset();
                    for (int i = 0; i < customProjectPolygon.size(); i++) {
                        float[] pt = customProjectPolygon.get(i);
                        float sx = cx + pt[0] * scale;
                        float sy = cy - pt[1] * scale;
                        if (i == 0) path.moveTo(sx, sy);
                        else path.lineTo(sx, sy);
                    }
                    path.close();
                    canvas.drawPath(path, paint);
                }
            }

            double[] sunPos = computeSunPosition(latitude, selectedDayOfYear, selectedClockHour);
            double sunAz = sunPos[0];
            double sunAlt = sunPos[1];

            double shadowAzRad = Math.toRadians(sunAz + 180.0);
            float shDirX = (float) Math.sin(shadowAzRad);
            float shDirY = (float) Math.cos(shadowAzRad);
            double tanAlt = Math.max(0.08, Math.tan(Math.toRadians(Math.max(1.0, sunAlt))));

            synchronized (osmBuildings) {
                if (sunAlt > 0.5) {
                    paint.setStyle(Paint.Style.FILL);
                    paint.setColor(isLightFieldTheme ? Color.argb(80, 120, 130, 150) : Color.argb(145, 4, 8, 15));
                    for (OsmBuilding b : osmBuildings) {
                        float shadowLen = Math.min(260f, (float) (b.heightMeters / tanAlt));
                        drawBuildingShadow(canvas, b, cx, cy, scale, shDirX * shadowLen, shDirY * shadowLen);
                    }

                    paint.setColor(isLightFieldTheme ? Color.argb(70, 180, 100, 220) : Color.argb(120, 180, 70, 220));
                    for (OsmBuilding b : osmBuildings) {
                        float dh = b.heightMeters - relativeHeightMeters;
                        if (dh > 0.5f) {
                            float floorShadowLen = Math.min(260f, (float) (dh / tanAlt));
                            drawBuildingShadow(canvas, b, cx, cy, scale, shDirX * floorShadowLen, shDirY * floorShadowLen);
                        }
                    }
                }

                for (OsmBuilding b : osmBuildings) {
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

                    paint.setStyle(Paint.Style.FILL);
                    if (isUserInside) {
                        paint.setColor(isLightFieldTheme ? Color.argb(200, 160, 230, 200) : Color.argb(220, 35, 115, 95));
                    } else if (b.heightMeters > relativeHeightMeters + 1.0f) {
                        paint.setColor(isLightFieldTheme ? Color.argb(200, 200, 210, 225) : Color.argb(215, 75, 100, 135));
                    } else {
                        paint.setColor(isLightFieldTheme ? Color.argb(180, 220, 225, 235) : Color.argb(195, 45, 65, 90));
                    }
                    canvas.drawPath(path, paint);

                    paint.setStyle(Paint.Style.STROKE);
                    paint.setStrokeWidth(isUserInside ? 4f : 2.2f);
                    paint.setColor(isUserInside ? Color.rgb(0, 180, 100) : (isLightFieldTheme ? Color.rgb(70, 110, 160) : Color.rgb(140, 195, 245)));
                    canvas.drawPath(path, paint);

                    paint.setStyle(Paint.Style.FILL);
                    paint.setColor(isLightFieldTheme ? Color.BLACK : Color.WHITE);
                    paint.setTextSize(19f);
                    String label = (b.houseNumber != null && !b.houseNumber.isEmpty())
                            ? (b.houseNumber + " (" + b.levels + "эт)")
                            : (b.levels + "эт");
                    canvas.drawText(label, (sumX / n) - 24f, (sumY / n) + 6f, paint);
                }
            }

            if (sunAlt > 0) {
                float sunVecX = (float) Math.sin(Math.toRadians(sunAz));
                float sunVecY = (float) Math.cos(Math.toRadians(sunAz));
                float sunScreenX = cx + sunVecX * 260f;
                float sunScreenY = cy - sunVecY * 260f;

                paint.setStyle(Paint.Style.STROKE);
                paint.setStrokeWidth(5f);
                paint.setColor(Color.rgb(255, 200, 0));
                canvas.drawLine(cx, cy, sunScreenX, sunScreenY, paint);

                paint.setStyle(Paint.Style.FILL);
                canvas.drawCircle(sunScreenX, sunScreenY, 18f, paint);
            }

            boolean inShadowNow = isSunBlockedByOsmBuildings(sunAz, sunAlt);
            paint.setStyle(Paint.Style.FILL);
            paint.setColor(inShadowNow ? Color.rgb(220, 50, 50) : Color.rgb(0, 200, 100));
            canvas.drawCircle(cx, cy, 12f, paint);

            paint.setColor(isLightFieldTheme ? Color.DKGRAY : Color.LTGRAY);
            paint.setTextSize(23f);
            String shadowStatus = (sunAlt <= 0) ? "Ночь (Солнце за горизонтом)" :
                    (inShadowNow ? "В ТЕНИ соседнего дома (на отм. этажа)" : "ПРЯМОЕ СОЛНЦЕ (тень мимо этажа)");
            canvas.drawText(shadowStatus, 25, h - 190, paint);
        }

        private void drawBuildingShadow(Canvas canvas, OsmBuilding b, float cx, float cy, float scale, float offX, float offY) {
            int n = b.xMeters.length;
            for (int i = 0; i < n; i++) {
                int next = (i + 1) % n;
                path.reset();
                path.moveTo(cx + b.xMeters[i] * scale, cy - b.yMeters[i] * scale);
                path.lineTo(cx + b.xMeters[next] * scale, cy - b.yMeters[next] * scale);
                path.lineTo(cx + (b.xMeters[next] + offX) * scale, cy - (b.yMeters[next] + offY) * scale);
                path.lineTo(cx + (b.xMeters[i] + offX) * scale, cy - (b.yMeters[i] + offY) * scale);
                path.close();
                canvas.drawPath(path, paint);
            }
        }

        private void drawARCameraOverlay(Canvas canvas, int w, int h) {
            float cx = w / 2f;
            float cy = h / 2f;
            float fovH = 60f;
            float fovV = 75f;

            drawOsmBuildingsInAR(canvas, w, h, fovH, fovV);

            float horizonY = cy + (camAltitude / fovV) * h;
            paint.setStyle(Paint.Style.STROKE);
            paint.setColor(isLightFieldTheme ? Color.rgb(0, 150, 120) : Color.argb(160, 0, 255, 180));
            paint.setStrokeWidth(3f);
            canvas.drawLine(0, horizonY, w, horizonY, paint);

            String[] dirs = {"С (0°)", "СВ", "В (90°)", "ЮВ", "Ю (180°)", "ЮЗ", "З (270°)", "СЗ"};
            paint.setStyle(Paint.Style.FILL);
            paint.setTextSize(30f);
            for (int i = 0; i < 8; i++) {
                float dirAz = i * 45f;
                float x = azimuthToScreenX(dirAz, w, fovH);
                if (x >= -50 && x <= w + 50) {
                    canvas.drawCircle(x, horizonY, 8f, paint);
                    canvas.drawText(dirs[i], x - 40f, horizonY - 16f, paint);
                }
            }

            drawSunArc(canvas, w, h, fovH, fovV, 355, Color.argb(140, 100, 180, 255), false);
            drawSunArc(canvas, w, h, fovH, fovV, 172, Color.argb(140, 255, 120, 80), false);
            drawSunArc(canvas, w, h, fovH, fovV, selectedDayOfYear, Color.rgb(255, 230, 0), true);

            double[] curSun = computeSunPosition(latitude, selectedDayOfYear, selectedClockHour);
            if (curSun[1] > -5.0) {
                float sunX = azimuthToScreenX((float) curSun[0], w, fovH);
                float sunY = cy - (((float) curSun[1] - camAltitude) / fovV) * h;
                boolean blocked = isSunBlockedByOsmBuildings(curSun[0], curSun[1]);

                paint.setStyle(Paint.Style.FILL);
                paint.setColor(blocked ? Color.argb(220, 255, 80, 80) : Color.rgb(255, 240, 60));
                canvas.drawCircle(sunX, sunY, 24f, paint);

                paint.setStyle(Paint.Style.STROKE);
                paint.setStrokeWidth(4f);
                paint.setColor(Color.WHITE);
                canvas.drawCircle(sunX, sunY, 28f, paint);
            }

            float calPitch = rawPitch - tarePitch;
            float calRoll = rawRoll - tareRoll;
            float levelRadius = 105f;
            paint.setStyle(Paint.Style.STROKE);
            paint.setStrokeWidth(4f);
            boolean isLevel = Math.abs(calPitch) < 0.5f && Math.abs(calRoll) < 0.5f;
            paint.setColor(isLevel ? Color.GREEN : (isLightFieldTheme ? Color.BLACK : Color.WHITE));
            canvas.drawCircle(cx, cy, levelRadius, paint);
            canvas.drawLine(cx - levelRadius - 20, cy, cx + levelRadius + 20, cy, paint);
            canvas.drawLine(cx, cy - levelRadius - 20, cx, cy + levelRadius + 20, cy, paint);

            float bx = cx + Math.max(-levelRadius, Math.min(levelRadius, (calRoll / 15f) * levelRadius));
            float by = cy + Math.max(-levelRadius, Math.min(levelRadius, (calPitch / 15f) * levelRadius));
            paint.setStyle(Paint.Style.FILL);
            paint.setColor(isLevel ? Color.argb(210, 0, 255, 100) : Color.argb(210, 255, 180, 0));
            canvas.drawCircle(bx, by, 20f, paint);
        }

        private void drawOsmBuildingsInAR(Canvas canvas, int w, int h, float fovH, float fovV) {
            float cy = h / 2f;
            paint.setStyle(Paint.Style.STROKE);
            paint.setStrokeWidth(2.5f);
            paint.setColor(isLightFieldTheme ? Color.rgb(40, 100, 160) : Color.argb(130, 100, 200, 255));

            synchronized (osmBuildings) {
                for (OsmBuilding b : osmBuildings) {
                    if (isPointInPolygon(0f, 0f, b.xMeters, b.yMeters)) continue;
                    int n = b.xMeters.length;
                    for (int i = 0; i < n; i++) {
                        float x = b.xMeters[i];
                        float y = b.yMeters[i];
                        float dist = (float) Math.hypot(x, y);
                        if (dist < 5f || dist > 180f) continue;

                        float az = (float) Math.toDegrees(Math.atan2(x, y));
                        if (az < 0) az += 360f;
                        float roofAlt = (float) Math.toDegrees(Math.atan2(b.heightMeters - relativeHeightMeters, dist));
                        float baseAlt = (float) Math.toDegrees(Math.atan2(-relativeHeightMeters, dist));

                        float sx = azimuthToScreenX(az, w, fovH);
                        if (sx >= 0 && sx <= w) {
                            float syRoof = cy - ((roofAlt - camAltitude) / fovV) * h;
                            float syBase = cy - ((baseAlt - camAltitude) / fovV) * h;
                            canvas.drawLine(sx, syRoof, sx, syBase, paint);
                        }
                    }
                }
            }
        }

        private void drawTelemetryHeader(Canvas canvas, int w) {
            paint.setStyle(Paint.Style.FILL);
            paint.setColor(isLightFieldTheme ? Color.argb(230, 255, 255, 255) : Color.argb(195, 15, 20, 28));
            canvas.drawRoundRect(new RectF(18, 25, w - 18, 400), 22f, 22f, paint);

            double[] curSun = computeSunPosition(latitude, selectedDayOfYear, selectedClockHour);
            paint.setColor(isLightFieldTheme ? Color.BLACK : Color.WHITE);
            paint.setTextSize(30f);
            canvas.drawText(String.format(Locale.US, "Азимут: %.1f° (%s) | Солнце: Аз %.0f° Выс %.0f°",
                    camAzimuth, getCardinal(camAzimuth), curSun[0], curSun[1]), 38, 68, paint);

            float calPitch = rawPitch - tarePitch;
            float calRoll = rawRoll - tareRoll;
            boolean isLevel = Math.abs(calPitch) < 0.5f && Math.abs(calRoll) < 0.5f;
            float slopePercent = (float) (Math.tan(Math.toRadians(Math.abs(calPitch))) * 100.0);
            float slopeMmM = slopePercent * 10f;
            paint.setColor(isLevel ? Color.rgb(0, 150, 0) : Color.rgb(180, 130, 0));
            canvas.drawText(String.format(Locale.US, "Уклон: %.1f° | %.1f%% | %.0f мм/м (Крен: %.1f°)",
                    calPitch, slopePercent, slopeMmM, calRoll), 38, 118, paint);

            int estFloor = Math.round(relativeHeightMeters / floorHeightMeters) + 1;
            paint.setColor(isLightFieldTheme ? Color.rgb(0, 100, 160) : Color.rgb(130, 220, 255));
            canvas.drawText(String.format(Locale.US, "Отметка H: %+.2f м (~%d эт.) | %.1f гПа",
                    relativeHeightMeters, estFloor, currentPressure), 38, 168, paint);

            paint.setColor(isLightFieldTheme ? Color.rgb(0, 120, 50) : Color.rgb(200, 255, 160));
            canvas.drawText(String.format(Locale.US, "Свет: %.0f лк (%s) | КЕО: %s",
                    currentLux, evaluateLuxNorm(currentLux), lastCalculatedKeo > 0 ? String.format(Locale.US, "%.2f%%", lastCalculatedKeo) : "не замер."), 38, 218, paint);

            float[] insolHours = calculateInsolationWithOsm(latitude, selectedDayOfYear);
            boolean sanPinPassed = insolHours[1] >= 2.0f;
            paint.setColor(sanPinPassed ? Color.rgb(0, 150, 80) : Color.rgb(200, 50, 50));
            canvas.drawText(String.format(Locale.US, "СанПиН: %s (%.1f ч без тени)",
                    sanPinPassed ? "СОБЛЮДЕНА (≥2ч)" : "НАРУШЕНИЕ (<2ч)", insolHours[1]), 38, 268, paint);

            paint.setColor(isLightFieldTheme ? Color.rgb(100, 80, 0) : Color.rgb(255, 230, 100));
            paint.setTextSize(27f);
            canvas.drawText(String.format(Locale.US, "%s | Астрон. свет: %.1f ч", selectedSeasonLabel, insolHours[0]), 38, 312, paint);

            paint.setTextSize(24f);
            paint.setColor(realOsmLoaded ? Color.rgb(0, 130, 60) : Color.rgb(180, 100, 0));
            String gpsText = gpsLocked ? "GPS" : "Старт";
            canvas.drawText(String.format(Locale.US, "%.4f N, %.4f E [%s] | %s",
                    latitude, longitude, gpsText, osmStatus), 38, 352, paint);

            paint.setColor(isLightFieldTheme ? Color.rgb(50, 90, 140) : Color.rgb(140, 200, 255));
            canvas.drawText("DXF/PDF в меню | Тап по зданию = правка этажей", 38, 388, paint);
        }

        private void drawSunArc(Canvas canvas, int w, int h, float fovH, float fovV, int day, int color, boolean drawHours) {
            paint.setColor(color);
            paint.setStyle(Paint.Style.STROKE);
            paint.setStrokeWidth(drawHours ? 6f : 3f);
            path.reset();
            boolean started = false;

            for (double hr = 4.0; hr <= 22.0; hr += 0.5) {
                double[] pos = computeSunPosition(latitude, day, hr);
                if (pos[1] < -5.0) continue;

                float sx = azimuthToScreenX((float) pos[0], w, fovH);
                float sy = (h / 2f) - (((float) pos[1] - camAltitude) / fovV) * h;

                if (sx >= -w && sx <= 2 * w) {
                    if (!started) {
                        path.moveTo(sx, sy);
                        started = true;
                    } else {
                        path.lineTo(sx, sy);
                    }
                } else {
                    started = false;
                }

                if (drawHours && Math.abs(hr - Math.round(hr)) < 0.01 && sx >= 0 && sx <= w && sy >= 0 && sy <= h) {
                    boolean blocked = isSunBlockedByOsmBuildings(pos[0], pos[1]);
                    paint.setStyle(Paint.Style.FILL);
                    paint.setColor(blocked ? Color.rgb(255, 80, 80) : color);
                    canvas.drawCircle(sx, sy, 11f, paint);
                    paint.setTextSize(26f);
                    canvas.drawText(((int) hr) + ":00", sx - 25f, sy - 16f, paint);
                    paint.setStyle(Paint.Style.STROKE);
                    paint.setColor(color);
                }
            }
            canvas.drawPath(path, paint);
        }

        private float azimuthToScreenX(float targetAz, int screenW, float fovH) {
            float diff = targetAz - camAzimuth;
            if (diff > 180f) diff -= 360f;
            if (diff < -180f) diff += 360f;
            return (screenW / 2f) + (diff / fovH) * screenW;
        }

        private String getCardinal(float az) {
            String[] dirs = {"С", "СВ", "В", "ЮВ", "Ю", "ЮЗ", "З", "СЗ"};
            return dirs[Math.round(az / 45f) % 8];
        }

        private String evaluateLuxNorm(float lux) {
            if (lux < 50) return "Сумерки / Коридор";
            if (lux < 150) return "Жилая комната (>=150 лк)";
            if (lux < 300) return "Офис / Кухня (>=200-300 лк)";
            if (lux < 500) return "Рабочий кабинет (300-500 лк)";
            return "Черчение / Улица (>=500 лк)";
        }
    }
}
