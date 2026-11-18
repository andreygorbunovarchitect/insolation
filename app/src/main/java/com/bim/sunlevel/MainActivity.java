package com.bim.sunlevel;

import android.Manifest;
import android.app.Activity;
import android.app.AlertDialog;
import android.content.ContentValues;
import android.content.Context;
import android.content.Intent;
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
import android.os.Build;
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
import java.io.InputStream;
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

    private static final int REQ_PERMISSIONS = 101;
    private static final int REQ_PICK_CAD_FILE = 202;

    private SensorManager sensorManager;
    private Sensor rotSensor, accelSensor, magSensor, pressureSensor, lightSensor;
    private boolean hasRotationVector = false, hasBarometer = false;
    private final float[] lastAccel = new float[]{0f, 0f, 9.81f};
    private final float[] lastMag = new float[]{0f, 1f, 0f};
    private boolean hasAccelData = false, hasMagData = false;

    private LocationManager locationManager;
    private final LocationListener universalLocationListener = new LocationListener() {
        @Override public void onLocationChanged(Location loc) { onNewLocation(loc); }
        @Override public void onStatusChanged(String provider, int status, Bundle extras) {}
        @Override public void onProviderEnabled(String provider) {}
        @Override public void onProviderDisabled(String provider) {}
    };

    private SurfaceView cameraSurface;
    private Camera camera;
    private AROverlayView overlayView;
    private Button btnModeToggle;
    private TextView timeLabelView;
    private SeekBar timeSeekBar;

    private double latitude = 54.6195, longitude = 39.7420;
    private float gpsAccuracyMeters = 0f, lastGpsAltitudeASL = 0f;
    private double lastOsmLat = 0.0, lastOsmLon = 0.0;
    private boolean gpsLocked = false, realOsmLoaded = false;
    private volatile boolean pendingOsmReload = false;

    private float camAzimuth = 0f, camAltitude = 0f, camRoll = 0f;
    private float rawPitch = 0f, rawRoll = 0f, tarePitch = 0f, tareRoll = 0f;

    // Автоматический и ручной высотомер / определение этажа
    private float currentPressure = 1013.25f;
    private float autoGroundPressure = -1f; // Давление на уровне земли в точке GPS (гПа)
    private float autoGroundElevationASL = -1f; // Высота рельефа земли над уровнем моря (м)
    private float manualRefPressure = -1f;
    private float manualRefHeight = 0f;
    private boolean isManualHeightMode = false;
    private float floorHeightMeters = 3.0f;
    private float relativeHeightMeters = 0.0f;
    private final AtomicBoolean isFetchingGroundMeteo = new AtomicBoolean(false);

    private float currentLux = 0f;
    private float externalLuxForKeo = -1f, keoWindowLux = -1f, keoCenterLux = -1f, keoBackLux = -1f, lastCalculatedKeo = -1f;
    private boolean showKeoHeatmap = false;

    // 3D AR-рулетка (0 = Выкл, 1 = Стена/Окно на дист. D, 2 = От пола Вверх, 3 = По полу 3D)
    private int tapeMode = 0;
    private Float tapeAz1 = null, tapeAlt1 = null;
    private Float tapeAz2 = null, tapeAlt2 = null;
    private float tapeWallDist = 2.50f; // Дистанция до стены/окна по умолчанию (м)
    private float tapeEyeHeight = 1.60f; // Высота камеры от пола (м)

    private final List<float[]> customProjectPolygon = new ArrayList<>();
    private float customProjectHeight = 24.0f;

    private boolean isLightFieldTheme = false;
    private int selectedDayOfYear = 80;
    private String selectedSeasonLabel = "Сегодня";
    private double targetClockHour = 12.0, displayedClockHour = 12.0;
    private boolean isLiveTime = true, is2DMapMode = false;
    private float mapScalePixelsPerMeter = 2.2f;

    private static class OsmBuilding {
        float[] xMeters, yMeters;
        float heightMeters;
        int levels;
        String houseNumber;
        boolean isCustomProject;
    }

    private final List<OsmBuilding> osmBuildings = new ArrayList<>();
    private String rawOsmJsonCache = null;
    private String osmStatus = "Ожидание GPS...";
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

        loadSavedLocationAndCache();

        FrameLayout root = new FrameLayout(this);
        cameraSurface = new SurfaceView(this);
        cameraSurface.getHolder().addCallback(this);
        root.addView(cameraSurface);

        overlayView = new AROverlayView(this);
        overlayView.setOnTouchListener((v, event) -> {
            if (event.getAction() == MotionEvent.ACTION_DOWN) {
                float tx = event.getX(), ty = event.getY();
                float ui = v.getWidth() / 1080f;

                // Тап по строке "Отметка H / Этаж" в шапке (Y: 125..195) открывает быструю корректировку этажа
                if (ty >= 120 * ui && ty <= 195 * ui) {
                    showAltitudeCalibrationDialog();
                    return true;
                }

                // Тап по остальной части верхней шапки обновляет GPS и дома OSM
                if (ty < 385 * ui) {
                    startLocationUpdates();
                    isFetchingOsm.set(false);
                    fetchOsmBuildings(latitude, longitude);
                    fetchAutoGroundElevationAndPressure(latitude, longitude);
                    Toast.makeText(this, "Обновление GPS, высоты рельефа и OSM...", Toast.LENGTH_SHORT).show();
                    return true;
                }

                // Управление AR-рулеткой через нижнюю интерактивную панель рулетки
                if (tapeMode > 0 && !is2DMapMode && ty >= v.getHeight() - 360 * ui && ty <= v.getHeight() - 190 * ui) {
                    if (tx < v.getWidth() * 0.55f) {
                        handleArTapePointTrigger();
                    } else if (tx < v.getWidth() * 0.80f) {
                        showTapeSettingsDialog();
                    } else {
                        tapeMode = 0;
                        tapeAz1 = tapeAlt1 = tapeAz2 = tapeAlt2 = null;
                        Toast.makeText(this, "AR-рулетка закрыта", Toast.LENGTH_SHORT).show();
                    }
                    overlayView.invalidate();
                    return true;
                }

                if (is2DMapMode) {
                    float cx = v.getWidth() / 2f, cy = v.getHeight() * 0.56f, sc = mapScalePixelsPerMeter * ui;
                    float mapX = (tx - cx) / sc, mapY = (cy - ty) / sc;
                    synchronized (osmBuildings) {
                        for (OsmBuilding b : osmBuildings) {
                            if (isPointInPolygon(mapX, mapY, b.xMeters, b.yMeters)) {
                                showEditBuildingDialog(b);
                                return true;
                            }
                        }
                    }
                    if (ty > 385 * ui && ty < v.getHeight() - 220 * ui) {
                        if (mapScalePixelsPerMeter < 1.6f) mapScalePixelsPerMeter = 2.2f;
                        else if (mapScalePixelsPerMeter < 2.6f) mapScalePixelsPerMeter = 3.6f;
                        else if (mapScalePixelsPerMeter < 4.2f) mapScalePixelsPerMeter = 5.0f;
                        else mapScalePixelsPerMeter = 1.2f;
                        overlayView.invalidate();
                        return true;
                    }
                }
            }
            return false;
        });
        root.addView(overlayView);

        LinearLayout bottomContainer = new LinearLayout(this);
        bottomContainer.setOrientation(LinearLayout.VERTICAL);
        bottomContainer.setBackgroundColor(Color.argb(215, 12, 18, 26));
        bottomContainer.setPadding(10, 8, 10, 16);

        LinearLayout sliderRow = new LinearLayout(this);
        sliderRow.setOrientation(LinearLayout.HORIZONTAL);
        sliderRow.setGravity(Gravity.CENTER_VERTICAL);
        sliderRow.setPadding(10, 2, 10, 6);

        timeLabelView = new TextView(this);
        timeLabelView.setTextColor(Color.rgb(120, 255, 160));
        timeLabelView.setTextSize(12f);
        timeLabelView.setOnClickListener(v -> {
            isLiveTime = true;
            syncWithRealTime();
            Toast.makeText(this, "Реальное системное время", Toast.LENGTH_SHORT).show();
        });
        sliderRow.addView(timeLabelView);

        timeSeekBar = new SeekBar(this);
        timeSeekBar.setMax(1439);
        LinearLayout.LayoutParams seekParams = new LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f);
        seekParams.setMargins(12, 0, 6, 0);
        timeSeekBar.setLayoutParams(seekParams);
        syncWithRealTime();
        displayedClockHour = targetClockHour;

        timeSeekBar.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
            @Override
            public void onProgressChanged(SeekBar seekBar, int progress, boolean fromUser) {
                if (fromUser) {
                    isLiveTime = false;
                    targetClockHour = progress / 60.0;
                    timeLabelView.setTextColor(Color.rgb(255, 225, 90));
                    timeLabelView.setText(formatClockHour(targetClockHour, false));
                    if (overlayView != null) overlayView.invalidate();
                }
            }
            @Override public void onStartTrackingTouch(SeekBar seekBar) { isLiveTime = false; }
            @Override public void onStopTrackingTouch(SeekBar seekBar) {}
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
            if (!is2DMapMode && cameraSurface.getHolder().getSurface().isValid()) {
                startCameraPreview(cameraSurface.getHolder());
            }
            if (!realOsmLoaded) fetchOsmBuildings(latitude, longitude);
            overlayView.invalidate();
        });

        Button btnTape = createButton("Рулетка", Color.argb(230, 0, 140, 130));
        btnTape.setOnClickListener(v -> {
            is2DMapMode = false;
            btnModeToggle.setText("2D План");
            if (tapeMode == 0) {
                tapeMode = 1;
                tapeAz1 = tapeAlt1 = tapeAz2 = tapeAlt2 = null;
                autoDetectWallDistanceFromOsm();
                Toast.makeText(this, "AR-Рулетка включена: наведите прицел и нажмите [+ Точка А]", Toast.LENGTH_SHORT).show();
            } else {
                showTapeSettingsDialog();
            }
            overlayView.invalidate();
        });

        Button btnFloor = createButton("Этаж/H", Color.argb(230, 65, 105, 175));
        btnFloor.setOnClickListener(v -> showAltitudeCalibrationDialog());

        Button btnKeo = createButton("КЕО", Color.argb(230, 155, 50, 175));
        btnKeo.setOnClickListener(v -> showKeoGridDialog());

        Button btnTools = createButton("Меню BIM", Color.argb(230, 40, 130, 95));
        btnTools.setOnClickListener(v -> showProjectAndToolsMenu());

        Button btnPdf = createButton("Акт PDF", Color.argb(230, 185, 55, 45));
        btnPdf.setOnClickListener(v -> generatePdfReport());

        bottomBar.addView(btnModeToggle);
        bottomBar.addView(btnTape);
        bottomBar.addView(btnFloor);
        bottomBar.addView(btnKeo);
        bottomBar.addView(btnTools);
        bottomBar.addView(btnPdf);
        bottomContainer.addView(bottomBar);

        root.addView(bottomContainer, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.WRAP_CONTENT, Gravity.BOTTOM));
        setContentView(root);

        sensorManager = (SensorManager) getSystemService(Context.SENSOR_SERVICE);
        if (sensorManager != null) {
            rotSensor = sensorManager.getDefaultSensor(Sensor.TYPE_ROTATION_VECTOR);
            if (rotSensor == null) rotSensor = sensorManager.getDefaultSensor(Sensor.TYPE_GEOMAGNETIC_ROTATION_VECTOR);
            hasRotationVector = (rotSensor != null);
            accelSensor = sensorManager.getDefaultSensor(Sensor.TYPE_ACCELEROMETER);
            magSensor = sensorManager.getDefaultSensor(Sensor.TYPE_MAGNETIC_FIELD);
            pressureSensor = sensorManager.getDefaultSensor(Sensor.TYPE_PRESSURE);
            hasBarometer = (pressureSensor != null);
            lightSensor = sensorManager.getDefaultSensor(Sensor.TYPE_LIGHT);
        }

        locationManager = (LocationManager) getSystemService(Context.LOCATION_SERVICE);
        requestPermissionsIfNeeded();
        fetchAutoGroundElevationAndPressure(latitude, longitude);
    }

    private Button createButton(String text, int bgColor) {
        Button b = new Button(this);
        b.setText(text);
        b.setTextSize(9.5f);
        b.setTextColor(Color.WHITE);
        b.setBackgroundColor(bgColor);
        b.setPadding(2, 10, 2, 10);
        LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f);
        lp.setMargins(2, 0, 2, 0);
        b.setLayoutParams(lp);
        return b;
    }

    // --- Автоматическое получение давления на уровне земли и рельефа для авто-определения этажа ---
    private void fetchAutoGroundElevationAndPressure(final double lat, final double lon) {
        if (!isFetchingGroundMeteo.compareAndSet(false, true)) return;
        new Thread(() -> {
            HttpURLConnection conn = null;
            try {
                String urlStr = String.format(Locale.US,
                        "https://api.open-meteo.com/v1/forecast?latitude=%.5f&longitude=%.5f&current=surface_pressure,pressure_msl",
                        lat, lon);
                conn = (HttpURLConnection) new URL(urlStr).openConnection();
                conn.setConnectTimeout(6000);
                conn.setReadTimeout(6000);
                conn.setRequestProperty("User-Agent", "BIMSunLevel/3.1");
                if (conn.getResponseCode() == 200) {
                    BufferedReader br = new BufferedReader(new InputStreamReader(conn.getInputStream(), StandardCharsets.UTF_8));
                    StringBuilder sb = new StringBuilder();
                    String line;
                    while ((line = br.readLine()) != null) sb.append(line);
                    br.close();

                    JSONObject root = new JSONObject(sb.toString());
                    if (root.has("elevation")) {
                        autoGroundElevationASL = (float) root.getDouble("elevation");
                    }
                    JSONObject cur = root.optJSONObject("current");
                    if (cur != null && cur.has("surface_pressure")) {
                        autoGroundPressure = (float) cur.getDouble("surface_pressure");
                    }
                    recalculateCurrentElevationAndFloor();
                    if (overlayView != null) overlayView.postInvalidate();
                }
            } catch (Exception ignored) {
            } finally {
                if (conn != null) conn.disconnect();
                isFetchingGroundMeteo.set(false);
            }
        }).start();
    }

    private void recalculateCurrentElevationAndFloor() {
        if (isManualHeightMode) {
            if (hasBarometer && manualRefPressure > 0 && currentPressure > 0) {
                float delta = 44330f * (1f - (float) Math.pow(currentPressure / manualRefPressure, 0.190295f));
                relativeHeightMeters = manualRefHeight + delta;
            } else {
                relativeHeightMeters = manualRefHeight;
            }
        } else {
            // Автоматический режим определения отметки H и этажа
            if (hasBarometer && autoGroundPressure > 0 && currentPressure > 0) {
                float h = 44330f * (1f - (float) Math.pow(currentPressure / autoGroundPressure, 0.190295f));
                relativeHeightMeters = Math.max(0f, h);
            } else if (lastGpsAltitudeASL != 0f && autoGroundElevationASL > 0f) {
                relativeHeightMeters = Math.max(0f, lastGpsAltitudeASL - autoGroundElevationASL);
            } else if (hasBarometer && manualRefPressure > 0) {
                float delta = 44330f * (1f - (float) Math.pow(currentPressure / manualRefPressure, 0.190295f));
                relativeHeightMeters = Math.max(0f, delta);
            }
        }
    }

    // Диалог быстрой корректировки этажа, отметки H и шага этажа (+ возврат в Авто)
    private void showAltitudeCalibrationDialog() {
        LinearLayout layout = new LinearLayout(this);
        layout.setOrientation(LinearLayout.VERTICAL);
        layout.setPadding(45, 20, 45, 10);

        int currentEstFloor = Math.max(1, Math.round(relativeHeightMeters / floorHeightMeters) + 1);

        // Ряд быстрых кнопок: [-1 этаж] [1 эт (0м)] [+1 этаж]
        LinearLayout quickRow = new LinearLayout(this);
        quickRow.setOrientation(LinearLayout.HORIZONTAL);

        final EditText inputFloor = new EditText(this);
        inputFloor.setHint("Номер этажа (напр. 5)");
        inputFloor.setInputType(InputType.TYPE_CLASS_NUMBER | InputType.TYPE_NUMBER_FLAG_SIGNED);
        inputFloor.setText(String.valueOf(currentEstFloor));

        final EditText inputStep = new EditText(this);
        inputStep.setHint("Высота этажа, м (напр. 3.0)");
        inputStep.setInputType(InputType.TYPE_CLASS_NUMBER | InputType.TYPE_NUMBER_FLAG_DECIMAL);
        inputStep.setText(String.format(Locale.US, "%.1f", floorHeightMeters));

        Button btnMinus = new Button(this);
        btnMinus.setText("-1 эт");
        btnMinus.setOnClickListener(v -> {
            try {
                int f = Integer.parseInt(inputFloor.getText().toString().trim()) - 1;
                inputFloor.setText(String.valueOf(Math.max(1, f)));
            } catch (Exception ignored) {}
        });

        Button btnGround = new Button(this);
        btnGround.setText("1 эт (0м)");
        btnGround.setOnClickListener(v -> inputFloor.setText("1"));

        Button btnPlus = new Button(this);
        btnPlus.setText("+1 эт");
        btnPlus.setOnClickListener(v -> {
            try {
                int f = Integer.parseInt(inputFloor.getText().toString().trim()) + 1;
                inputFloor.setText(String.valueOf(f));
            } catch (Exception ignored) {}
        });

        LinearLayout.LayoutParams qp = new LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f);
        quickRow.addView(btnMinus, qp);
        quickRow.addView(btnGround, qp);
        quickRow.addView(btnPlus, qp);
        layout.addView(quickRow);

        TextView lblF = new TextView(this);
        lblF.setText("Текущий этаж:");
        lblF.setPadding(0, 16, 0, 2);
        layout.addView(lblF);
        layout.addView(inputFloor);

        TextView lblS = new TextView(this);
        lblS.setText("Высота одного этажа (м):");
        lblS.setPadding(0, 12, 0, 2);
        layout.addView(lblS);
        layout.addView(inputStep);

        String modeInfo = isManualHeightMode ? "Режим: РУЧНАЯ ПРИВЯЗКА" : "Режим: АВТОМАТИЧЕСКИЙ (барометр + рельеф GPS)";
        new AlertDialog.Builder(this)
                .setTitle("Отметка H и Этаж")
                .setMessage(modeInfo + String.format(Locale.US, "\nТекущая отметка: %+.2f м (~%d этаж)", relativeHeightMeters, currentEstFloor))
                .setView(layout)
                .setPositiveButton("Скорректировать", (d, w) -> {
                    try {
                        int fl = Integer.parseInt(inputFloor.getText().toString().trim());
                        float step = Float.parseFloat(inputStep.getText().toString().trim().replace(",", "."));
                        if (step >= 1.5f && step <= 10f) floorHeightMeters = step;
                        isManualHeightMode = true;
                        manualRefPressure = currentPressure;
                        manualRefHeight = (fl - 1) * floorHeightMeters;
                        // Также уточняем давление на уровне земли для текущей локации
                        if (hasBarometer && currentPressure > 0) {
                            autoGroundPressure = (float) (currentPressure / Math.pow(1.0 - (manualRefHeight / 44330.0), 5.255));
                        }
                        recalculateCurrentElevationAndFloor();
                        overlayView.invalidate();
                        Toast.makeText(this, String.format(Locale.US, "Установлен %d этаж (%+.2f м)", fl, relativeHeightMeters), Toast.LENGTH_SHORT).show();
                    } catch (Exception ignored) {}
                })
                .setNeutralButton("Включить АВТО", (d, w) -> {
                    isManualHeightMode = false;
                    fetchAutoGroundElevationAndPressure(latitude, longitude);
                    recalculateCurrentElevationAndFloor();
                    overlayView.invalidate();
                    Toast.makeText(this, "Включено авто-определение этажа", Toast.LENGTH_SHORT).show();
                })
                .setNegativeButton("Отмена", null).show();
    }

    // --- Новая 3D AR-Рулетка: фиксация точек, авто-луч до стены OSM и 3 режима замера ---
    private void handleArTapePointTrigger() {
        if (tapeAz1 == null || (tapeAz1 != null && tapeAz2 != null)) {
            tapeAz1 = camAzimuth;
            tapeAlt1 = camAltitude;
            tapeAz2 = null;
            tapeAlt2 = null;
            if (tapeMode == 1) autoDetectWallDistanceFromOsm();
            Toast.makeText(this, "Точка А зафиксирована! Наведите прицел на Точку Б", Toast.LENGTH_SHORT).show();
        } else {
            tapeAz2 = camAzimuth;
            tapeAlt2 = camAltitude;
            Toast.makeText(this, "Точка Б зафиксирована! Нажмите снова для нового замера", Toast.LENGTH_SHORT).show();
        }
    }

    private void autoDetectWallDistanceFromOsm() {
        float rayX = (float) Math.sin(Math.toRadians(camAzimuth));
        float rayY = (float) Math.cos(Math.toRadians(camAzimuth));
        float bestDist = -1f;
        synchronized (osmBuildings) {
            for (OsmBuilding b : osmBuildings) {
                int n = b.xMeters.length;
                for (int i = 0; i < n; i++) {
                    float d = intersectRayWithSegment(rayX, rayY, b.xMeters[i], b.yMeters[i], b.xMeters[(i + 1) % n], b.yMeters[(i + 1) % n]);
                    if (d > 1.0f && d < 120f && (bestDist < 0 || d < bestDist)) {
                        bestDist = d;
                    }
                }
            }
        }
        if (bestDist > 1.2f && bestDist < 50f) {
            tapeWallDist = bestDist;
        }
    }

    // Расчет 3D-размеров между (az1, alt1) и (az2, alt2): возвращает [L_total, dH, dW, D_ref, Area]
    private float[] computeArTapeMetrics(float az1, float alt1, float az2, float alt2) {
        float dAzDeg = Math.abs(az2 - az1);
        if (dAzDeg > 180f) dAzDeg = 360f - dAzDeg;
        double dAzRad = Math.toRadians(dAzDeg);
        double alt1Rad = Math.toRadians(alt1);
        double alt2Rad = Math.toRadians(alt2);

        if (tapeMode == 2) {
            // Режим 2: От пола (Точка А на полу -> авто-дистанция, Точка Б на стене/вверху)
            double lookDownRad = Math.max(Math.toRadians(2.0), Math.abs(alt1Rad));
            float distToWall = (float) (tapeEyeHeight / Math.tan(lookDownRad));
            float dH = (float) Math.abs(distToWall * (Math.tan(alt2Rad) - Math.tan(alt1Rad)));
            float dW = (float) (2.0 * distToWall * Math.tan(dAzRad / 2.0));
            float totalL = (float) Math.hypot(dH, dW);
            return new float[]{totalL, dH, dW, distToWall, dH * dW};
        } else if (tapeMode == 3) {
            // Режим 3: По полу 3D (Обе точки А и Б на полу)
            double down1 = Math.max(Math.toRadians(2.0), Math.abs(alt1Rad));
            double down2 = Math.max(Math.toRadians(2.0), Math.abs(alt2Rad));
            float d1 = (float) (tapeEyeHeight / Math.tan(down1));
            float d2 = (float) (tapeEyeHeight / Math.tan(down2));
            float floorLen = (float) Math.sqrt(Math.max(0.0, d1 * d1 + d2 * d2 - 2.0 * d1 * d2 * Math.cos(dAzRad)));
            return new float[]{floorLen, 0f, floorLen, d1, 0f};
        } else {
            // Режим 1: Стена / Окно / Фасад на дистанции tapeWallDist (работает под любым углом, даже вверх)
            float d = Math.max(0.3f, tapeWallDist);
            float dW = (float) (2.0 * d * Math.tan(dAzRad / 2.0));
            float dH = (float) Math.abs(d * (Math.tan(alt2Rad) - Math.tan(alt1Rad)));
            float totalL = (float) Math.hypot(dW, dH);
            return new float[]{totalL, dH, dW, d, dW * dH};
        }
    }

    private void showTapeSettingsDialog() {
        LinearLayout layout = new LinearLayout(this);
        layout.setOrientation(LinearLayout.VERTICAL);
        layout.setPadding(45, 20, 45, 10);

        final EditText inDist = new EditText(this);
        inDist.setHint("Дистанция до стены/окна D (м)");
        inDist.setInputType(InputType.TYPE_CLASS_NUMBER | InputType.TYPE_NUMBER_FLAG_DECIMAL);
        inDist.setText(String.format(Locale.US, "%.2f", tapeWallDist));

        final EditText inEye = new EditText(this);
        inEye.setHint("Высота камеры от пола h_глаз (м)");
        inEye.setInputType(InputType.TYPE_CLASS_NUMBER | InputType.TYPE_NUMBER_FLAG_DECIMAL);
        inEye.setText(String.format(Locale.US, "%.2f", tapeEyeHeight));

        TextView t1 = new TextView(this);
        t1.setText("Дистанция до стены/окна D (м) [для Режима 1]:");
        layout.addView(t1);
        layout.addView(inDist);

        TextView t2 = new TextView(this);
        t2.setText("Высота телефона от пола (м) [для Режимов 2 и 3]:");
        t2.setPadding(0, 14, 0, 0);
        layout.addView(t2);
        layout.addView(inEye);

        String[] modeNames = new String[]{
                "1. Стена / Окно (на дистанции D)",
                "2. От пола вверх (Авто-дистанция + Высота)",
                "3. По полу 3D (Длина между 2 точками пола)"
        };

        new AlertDialog.Builder(this)
                .setTitle("Настройка 3D AR-Рулетки")
                .setView(layout)
                .setSingleChoiceItems(modeNames, Math.max(0, tapeMode - 1), (d, which) -> tapeMode = which + 1)
                .setPositiveButton("Применить", (d, w) -> {
                    try { tapeWallDist = Float.parseFloat(inDist.getText().toString().trim().replace(",", ".")); } catch (Exception ignored) {}
                    try { tapeEyeHeight = Float.parseFloat(inEye.getText().toString().trim().replace(",", ".")); } catch (Exception ignored) {}
                    if (tapeMode == 0) tapeMode = 1;
                    overlayView.invalidate();
                })
                .setNeutralButton("Авто-луч D из OSM", (d, w) -> {
                    autoDetectWallDistanceFromOsm();
                    Toast.makeText(this, String.format(Locale.US, "Дистанция до фасада: %.2f м", tapeWallDist), Toast.LENGTH_SHORT).show();
                    overlayView.invalidate();
                })
                .setNegativeButton("Выкл рулетку", (d, w) -> {
                    tapeMode = 0;
                    tapeAz1 = tapeAlt1 = tapeAz2 = tapeAlt2 = null;
                    overlayView.invalidate();
                }).show();
    }

    private void syncWithRealTime() {
        Calendar cal = Calendar.getInstance();
        int hr = cal.get(Calendar.HOUR_OF_DAY), min = cal.get(Calendar.MINUTE), sec = cal.get(Calendar.SECOND);
        targetClockHour = hr + (min / 60.0) + (sec / 3600.0);
        if (timeSeekBar != null) timeSeekBar.setProgress(hr * 60 + min);
        if (timeLabelView != null) {
            timeLabelView.setTextColor(isLightFieldTheme ? Color.rgb(0, 120, 60) : Color.rgb(120, 255, 160));
            timeLabelView.setText(String.format(Locale.US, "Сейчас: %02d:%02d:%02d", hr, min, sec));
        }
    }

    private String formatClockHour(double ch, boolean live) {
        int tm = Math.max(0, Math.min(1439, (int) Math.round(ch * 60.0)));
        return String.format(Locale.US, "%s: %02d:%02d", live ? "Сейчас" : "Ручн", tm / 60, tm % 60);
    }

    private OutputStream openUniversalDownloadStream(String fileName, String mimeType, String subFolder) throws Exception {
        if (Build.VERSION.SDK_INT >= 29) {
            ContentValues cv = new ContentValues();
            cv.put(MediaStore.Downloads.DISPLAY_NAME, fileName);
            cv.put(MediaStore.Downloads.MIME_TYPE, mimeType);
            cv.put(MediaStore.Downloads.RELATIVE_PATH, Environment.DIRECTORY_DOWNLOADS + "/" + subFolder);
            Uri uri = getContentResolver().insert(MediaStore.Downloads.EXTERNAL_CONTENT_URI, cv);
            if (uri != null) {
                OutputStream os = getContentResolver().openOutputStream(uri);
                if (os != null) return os;
            }
        }
        File dir = new File(Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DOWNLOADS), subFolder);
        if (!dir.exists() && !dir.mkdirs()) {
            dir = new File(getExternalFilesDir(Environment.DIRECTORY_DOWNLOADS), subFolder);
            if (!dir.exists()) dir.mkdirs();
        }
        return new FileOutputStream(new File(dir, fileName));
    }

    private void loadSavedLocationAndCache() {
        try {
            SharedPreferences prefs = getSharedPreferences("osm_cache_v7", MODE_PRIVATE);
            if (prefs.contains("last_gps_lat") && prefs.contains("last_gps_lon")) {
                latitude = Double.longBitsToDouble(prefs.getLong("last_gps_lat", Double.doubleToRawLongBits(latitude)));
                longitude = Double.longBitsToDouble(prefs.getLong("last_gps_lon", Double.doubleToRawLongBits(longitude)));
            }
            String json = prefs.getString("json", null);
            double cLat = Double.longBitsToDouble(prefs.getLong("lat", 0));
            double cLon = Double.longBitsToDouble(prefs.getLong("lon", 0));
            if (json != null && Math.abs(cLat - latitude) < 0.005 && Math.abs(cLon - longitude) < 0.008) {
                rawOsmJsonCache = json;
                int count = parseOsmJson(json, latitude, longitude);
                if (count > 0) {
                    realOsmLoaded = true;
                    lastOsmLat = cLat;
                    lastOsmLon = cLon;
                    osmStatus = "OSM (кэш): " + count + " домов";
                }
            }
        } catch (Exception ignored) {}
    }

    private void saveOsmCache(String json, double lat, double lon) {
        try {
            rawOsmJsonCache = json;
            getSharedPreferences("osm_cache_v7", MODE_PRIVATE).edit()
                    .putString("json", json)
                    .putLong("lat", Double.doubleToRawLongBits(lat))
                    .putLong("lon", Double.doubleToRawLongBits(lon)).apply();
        } catch (Exception ignored) {}
    }

    private void fetchOsmBuildings(final double lat, final double lon) {
        if (!isFetchingOsm.compareAndSet(false, true)) {
            pendingOsmReload = true;
            return;
        }
        pendingOsmReload = false;
        osmStatus = "Загрузка домов OSM...";
        if (overlayView != null) overlayView.postInvalidate();

        new Thread(() -> {
            double s = lat - 0.0028, n = lat + 0.0028, w = lon - 0.0045, e = lon + 0.0045;
            String query = String.format(Locale.US,
                    "[out:json][timeout:18];(way[\"building\"](%.5f,%.5f,%.5f,%.5f);relation[\"building\"](%.5f,%.5f,%.5f,%.5f););out geom;",
                    s, w, n, e, s, w, n, e);

            String[] endpoints = new String[]{
                    "https://overpass.private.coffee/api/interpreter",
                    "https://maps.mail.ru/osm/tools/overpass/api/interpreter",
                    "https://overpass-api.de/api/interpreter",
                    "https://lz4.overpass-api.de/api/interpreter"
            };

            boolean success = false;
            int loadedCount = 0;
            StringBuilder errLog = new StringBuilder();

            for (String ep : endpoints) {
                HttpURLConnection conn = null;
                try {
                    URL url = new URL(ep + "?data=" + URLEncoder.encode(query, "UTF-8"));
                    conn = (HttpURLConnection) url.openConnection();
                    conn.setRequestMethod("GET");
                    conn.setConnectTimeout(7000);
                    conn.setReadTimeout(11000);
                    conn.setRequestProperty("User-Agent", "BIMSunLevel/3.1 (Android; Universal)");
                    conn.setRequestProperty("Accept", "*/*");

                    int code = conn.getResponseCode();
                    if (code == 200) {
                        BufferedReader br = new BufferedReader(new InputStreamReader(conn.getInputStream(), StandardCharsets.UTF_8));
                        StringBuilder sb = new StringBuilder();
                        String line;
                        while ((line = br.readLine()) != null) sb.append(line);
                        br.close();

                        loadedCount = parseOsmJson(sb.toString(), latitude, longitude);
                        lastOsmLat = lat;
                        lastOsmLon = lon;
                        realOsmLoaded = true;
                        if (loadedCount > 0) saveOsmCache(sb.toString(), lat, lon);
                        success = true;
                        break;
                    } else {
                        errLog.append("HTTP").append(code).append(" ");
                    }
                } catch (Exception ex) {
                    errLog.append(ex.getClass().getSimpleName().replace("Exception", "")).append(" ");
                } finally {
                    if (conn != null) conn.disconnect();
                }
            }

            final boolean ok = success;
            final int total = loadedCount;
            final String err = errLog.toString().trim();
            isFetchingOsm.set(false);

            double driftSq = Math.pow((latitude - lat) * 111132.0, 2) + Math.pow((longitude - lon) * 65000.0, 2);
            if (pendingOsmReload || driftSq > 900.0) {
                fetchOsmBuildings(latitude, longitude);
                return;
            }

            runOnUiThread(() -> {
                if (ok) osmStatus = "Карта OSM: " + total + " домов";
                else if (!realOsmLoaded) osmStatus = "Сеть OSM (" + err + ") — тапните сверху";
                if (overlayView != null) overlayView.invalidate();
            });
        }).start();
    }

    private int parseOsmJson(String jsonStr, double centerLat, double centerLon) throws Exception {
        JSONObject root = new JSONObject(jsonStr);
        JSONArray elements = root.optJSONArray("elements");
        if (elements == null) return 0;

        double mLat = 111132.0, mLon = 111320.0 * Math.cos(Math.toRadians(centerLat));
        Map<Long, float[]> nodeMap = new HashMap<>();
        for (int i = 0; i < elements.length(); i++) {
            JSONObject el = elements.getJSONObject(i);
            if ("node".equals(el.optString("type"))) {
                nodeMap.put(el.getLong("id"), new float[]{
                        (float) ((el.getDouble("lon") - centerLon) * mLon),
                        (float) ((el.getDouble("lat") - centerLat) * mLat)
                });
            }
        }

        List<OsmBuilding> parsed = new ArrayList<>();
        for (int i = 0; i < elements.length(); i++) {
            JSONObject el = elements.getJSONObject(i);
            int levels = -1;
            float height = -1f;
            String houseNum = "";
            JSONObject tags = el.optJSONObject("tags");
            if (tags != null) {
                houseNum = tags.optString("addr:housenumber", "").trim();
                String lvlStr = tags.optString("building:levels", "").replaceAll("[^0-9]", "");
                if (!lvlStr.isEmpty()) try { levels = Integer.parseInt(lvlStr); } catch (Exception ignored) {}
                String hStr = tags.optString("height", "").replace(",", ".").replaceAll("[^0-9.]", "");
                if (!hStr.isEmpty()) try { height = Float.parseFloat(hStr); } catch (Exception ignored) {}
            }
            if (levels <= 0 && height > 2f) levels = Math.max(1, Math.round(height / 3.0f));
            if (levels <= 0) levels = 5;
            if (height <= 2f) height = levels * 3.0f;

            JSONArray geom = el.optJSONArray("geometry");
            if (geom != null && geom.length() >= 3) {
                OsmBuilding b = buildFromGeomArray(geom, centerLat, centerLon, mLat, mLon, levels, height, houseNum);
                if (b != null) parsed.add(b);
                continue;
            }

            JSONArray members = el.optJSONArray("members");
            if (members != null) {
                for (int m = 0; m < members.length(); m++) {
                    JSONObject mem = members.getJSONObject(m);
                    if ("outer".equals(mem.optString("role", "outer"))) {
                        JSONArray mGeom = mem.optJSONArray("geometry");
                        if (mGeom != null && mGeom.length() >= 3) {
                            OsmBuilding b = buildFromGeomArray(mGeom, centerLat, centerLon, mLat, mLon, levels, height, houseNum);
                            if (b != null) parsed.add(b);
                        }
                    }
                }
                continue;
            }

            JSONArray nodes = el.optJSONArray("nodes");
            if (nodes != null && nodes.length() >= 3 && !nodeMap.isEmpty()) {
                List<float[]> pts = new ArrayList<>();
                for (int j = 0; j < nodes.length(); j++) {
                    float[] xy = nodeMap.get(nodes.getLong(j));
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

        synchronized (osmBuildings) {
            osmBuildings.clear();
            osmBuildings.addAll(parsed);
            appendCustomProjectBuildingLocked();
        }
        return parsed.size();
    }

    private OsmBuilding buildFromGeomArray(JSONArray geom, double cLat, double cLon, double mLat, double mLon,
                                           int levels, float height, String houseNum) throws Exception {
        OsmBuilding b = new OsmBuilding();
        b.xMeters = new float[geom.length()];
        b.yMeters = new float[geom.length()];
        for (int j = 0; j < geom.length(); j++) {
            JSONObject pt = geom.getJSONObject(j);
            b.xMeters[j] = (float) ((pt.getDouble("lon") - cLon) * mLon);
            b.yMeters[j] = (float) ((pt.getDouble("lat") - cLat) * mLat);
        }
        b.levels = levels;
        b.heightMeters = height;
        b.houseNumber = houseNum;
        return b;
    }

    private void appendCustomProjectBuildingLocked() {
        if (customProjectPolygon.size() >= 3) {
            OsmBuilding proj = new OsmBuilding();
            proj.xMeters = new float[customProjectPolygon.size()];
            proj.yMeters = new float[customProjectPolygon.size()];
            for (int i = 0; i < customProjectPolygon.size(); i++) {
                proj.xMeters[i] = customProjectPolygon.get(i)[0];
                proj.yMeters[i] = customProjectPolygon.get(i)[1];
            }
            proj.heightMeters = customProjectHeight;
            proj.levels = Math.max(1, Math.round(customProjectHeight / 3.0f));
            proj.houseNumber = "ПРОЕКТ";
            proj.isCustomProject = true;
            osmBuildings.add(proj);
        }
    }

    private void showProjectAndToolsMenu() {
        CharSequence[] items = new CharSequence[]{
                "1. Геолокация: Поиск адреса или ввод координат",
                "2. Импорт проекта (.dxf / .ifc / .txt через проводник)",
                "3. Обнулить уклономер (Тара 0°)",
                "4. Переключить тему (Темная / Полевая дневная)",
                "5. Смена сезона (Сегодня / Равноденствие / Лето / Зима)",
                "6. Сделать Фото AR в Галерею",
                "7. Экспорт журнала замеров в CSV"
        };
        new AlertDialog.Builder(this)
                .setTitle("BIM Инструменты и Настройки")
                .setItems(items, (d, w) -> {
                    if (w == 0) showLocationSearchDialog();
                    else if (w == 1) openCadFilePicker();
                    else if (w == 2) {
                        tarePitch = rawPitch;
                        tareRoll = rawRoll;
                        Toast.makeText(this, "Уклономер обнулен (0.0°)", Toast.LENGTH_SHORT).show();
                    } else if (w == 3) {
                        isLightFieldTheme = !isLightFieldTheme;
                        overlayView.invalidate();
                    } else if (w == 4) cycleSeason();
                    else if (w == 5) captureARPhoto();
                    else if (w == 6) exportLogToCsv();
                }).show();
    }

    private void showLocationSearchDialog() {
