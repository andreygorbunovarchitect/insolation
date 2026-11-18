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
    private double lastOsmLat = 0.0, lastOsmLon = 0.0;
    private boolean gpsLocked = false, realOsmLoaded = false;

    private float camAzimuth = 0f, camAltitude = 0f, camRoll = 0f;
    private float rawPitch = 0f, rawRoll = 0f, tarePitch = 0f, tareRoll = 0f;

    private float currentPressure = 1013.25f, basePressure = -1f;
    private float floorHeightMeters = 3.0f, calibratedBaseHeight = 12.0f, relativeHeightMeters = 12.0f;
    private float currentLux = 0f;

    // КЕО сетка и тепловая карта (СП 52.13330)
    private float externalLuxForKeo = -1f;
    private float keoWindowLux = -1f, keoCenterLux = -1f, keoBackLux = -1f;
    private float lastCalculatedKeo = -1f;
    private boolean showKeoHeatmap = false;

    // AR-рулетка (замер по 2 углам визирования)
    private boolean isTapeMode = false;
    private Float tapeBasePitch = null;
    private float tapeEyeHeight = 1.6f;
    private String tapeResultText = "";

    // Проектный контур (.dxf / .ifc / .txt)
    private final List<float[]> customProjectPolygon = new ArrayList<>();
    private float customProjectHeight = 24.0f;

    // UX: Светлая полевая тема, плавная интерполяция времени
    private boolean isLightFieldTheme = false;
    private int selectedDayOfYear = 80;
    private String selectedSeasonLabel = "Сегодня";
    private double targetClockHour = 12.0;
    private double displayedClockHour = 12.0;
    private boolean isLiveTime = true;
    private boolean is2DMapMode = false;
    private float mapScalePixelsPerMeter = 2.2f;

    private static class OsmBuilding {
        float[] xMeters, yMeters;
        float heightMeters;
        int levels;
        String houseNumber;
        boolean isCustomProject;
    }

    private final List<OsmBuilding> osmBuildings = new ArrayList<>();
    private String osmStatus = "Загрузка карты OSM...";
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
        cameraSurface = new SurfaceView(this);
        cameraSurface.getHolder().addCallback(this);
        root.addView(cameraSurface);

        overlayView = new AROverlayView(this);
        overlayView.setOnTouchListener((v, event) -> {
            if (event.getAction() == MotionEvent.ACTION_DOWN) {
                float tx = event.getX(), ty = event.getY();

                if (ty < 390) {
                    isFetchingOsm.set(false);
                    fetchOsmBuildings(latitude, longitude);
                    Toast.makeText(this, "Запрос реальных домов OSM...", Toast.LENGTH_SHORT).show();
                    return true;
                }

                if (isTapeMode && !is2DMapMode && ty >= 390 && ty < v.getHeight() - 240) {
                    handleArTapeClick();
                    return true;
                }

                if (is2DMapMode) {
                    float cx = v.getWidth() / 2f, cy = v.getHeight() * 0.56f;
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
                    if (ty > 420 && ty < v.getHeight() - 250) {
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
            Toast.makeText(this, "Синхронизировано с реальным временем", Toast.LENGTH_SHORT).show();
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
            if (!realOsmLoaded) fetchOsmBuildings(latitude, longitude);
            overlayView.invalidate();
        });

        Button btnKeo = createButton("КЕО Карта", Color.argb(230, 155, 50, 175));
        btnKeo.setOnClickListener(v -> showKeoGridDialog());

        Button btnTools = createButton("Меню BIM", Color.argb(230, 40, 130, 95));
        btnTools.setOnClickListener(v -> showProjectAndToolsMenu());

        Button btnTheme = createButton("Тема", Color.argb(210, 75, 90, 115));
        btnTheme.setOnClickListener(v -> {
            isLightFieldTheme = !isLightFieldTheme;
            bottomContainer.setBackgroundColor(isLightFieldTheme ? Color.argb(235, 235, 240, 245) : Color.argb(215, 12, 18, 26));
            Toast.makeText(this, isLightFieldTheme ? "Полевая (дневная) тема" : "Темная тема", Toast.LENGTH_SHORT).show();
            overlayView.invalidate();
        });

        Button btnPhoto = createButton("Фото AR", Color.argb(230, 195, 80, 25));
        btnPhoto.setOnClickListener(v -> captureARPhoto());

        Button btnPdf = createButton("Акт PDF", Color.argb(230, 180, 45, 55));
        btnPdf.setOnClickListener(v -> generatePdfReport());

        bottomBar.addView(btnModeToggle);
        bottomBar.addView(btnKeo);
        bottomBar.addView(btnTools);
        bottomBar.addView(btnTheme);
        bottomBar.addView(btnPhoto);
        bottomBar.addView(btnPdf);
        bottomContainer.addView(bottomBar);

        root.addView(bottomContainer, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.WRAP_CONTENT, Gravity.BOTTOM));
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

    // --- Быстрая загрузка реальных домов OSM (без HTTP 504 и HTTP 406) ---
    private void loadCachedOsmIfAvailable() {
        try {
            SharedPreferences prefs = getSharedPreferences("osm_cache_v5", MODE_PRIVATE);
            String json = prefs.getString("json", null);
            double cLat = Double.longBitsToDouble(prefs.getLong("lat", 0));
            double cLon = Double.longBitsToDouble(prefs.getLong("lon", 0));
            if (json != null && Math.abs(cLat - latitude) < 0.02 && Math.abs(cLon - longitude) < 0.02) {
                int count = parseOsmJson(json, cLat, cLon);
                if (count > 0) {
                    realOsmLoaded = true;
                    lastOsmLat = cLat;
                    lastOsmLon = cLon;
                    osmStatus = "OSM (кэш): " + count + " реальных домов";
                }
            }
        } catch (Exception ignored) {}
    }

    private void saveOsmCache(String json, double lat, double lon) {
        try {
            getSharedPreferences("osm_cache_v5", MODE_PRIVATE).edit()
                    .putString("json", json)
                    .putLong("lat", Double.doubleToRawLongBits(lat))
                    .putLong("lon", Double.doubleToRawLongBits(lon)).apply();
        } catch (Exception ignored) {}
    }

    private void fetchOsmBuildings(final double lat, final double lon) {
        if (!isFetchingOsm.compareAndSet(false, true)) return;
        osmStatus = "Загрузка домов OSM...";
        if (overlayView != null) overlayView.postInvalidate();

        new Thread(() -> {
            double s = lat - 0.0025, n = lat + 0.0025, w = lon - 0.0040, e = lon + 0.0040;
            // out geom; работает в 10 раз быстрее и не вызывает HTTP 504 Gateway Timeout
            String query = String.format(Locale.US,
                    "[out:json][timeout:18];way[\"building\"](%.5f,%.5f,%.5f,%.5f);out geom;", s, w, n, e);

            String[] endpoints = new String[]{
                    "https://overpass.private.coffee/api/interpreter",
                    "https://maps.mail.ru/osm/tools/overpass/api/interpreter",
                    "https://overpass-api.de/api/interpreter",
                    "https://lz4.overpass-api.de/api/interpreter"
            };

            boolean success = false;
            StringBuilder errLog = new StringBuilder();

            for (String ep : endpoints) {
                HttpURLConnection conn = null;
                try {
                    URL url = new URL(ep + "?data=" + URLEncoder.encode(query, "UTF-8"));
                    conn = (HttpURLConnection) url.openConnection();
                    conn.setRequestMethod("GET");
                    conn.setConnectTimeout(7000);
                    conn.setReadTimeout(10000);
                    conn.setRequestProperty("User-Agent", "BIMSunLevel/2.0 (Android; FieldEngineer)");
                    conn.setRequestProperty("Accept", "*/*");

                    int code = conn.getResponseCode();
                    if (code == 200) {
                        BufferedReader br = new BufferedReader(new InputStreamReader(conn.getInputStream(), StandardCharsets.UTF_8));
                        StringBuilder sb = new StringBuilder();
                        String line;
                        while ((line = br.readLine()) != null) sb.append(line);
                        br.close();

                        int count = parseOsmJson(sb.toString(), lat, lon);
                        if (count > 0) {
                            lastOsmLat = lat;
                            lastOsmLon = lon;
                            realOsmLoaded = true;
                            saveOsmCache(sb.toString(), lat, lon);
                            success = true;
                            break;
                        }
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
            final String err = errLog.toString().trim();
            isFetchingOsm.set(false);
            runOnUiThread(() -> {
                if (ok) osmStatus = "Карта OSM: " + osmBuildings.size() + " домов";
                else if (!realOsmLoaded) osmStatus = "Сеть OSM (" + err + ") — тапните сюда";
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
                OsmBuilding b = new OsmBuilding();
                b.xMeters = new float[geom.length()];
                b.yMeters = new float[geom.length()];
                for (int j = 0; j < geom.length(); j++) {
                    JSONObject pt = geom.getJSONObject(j);
                    b.xMeters[j] = (float) ((pt.getDouble("lon") - centerLon) * mLon);
                    b.yMeters[j] = (float) ((pt.getDouble("lat") - centerLat) * mLat);
                }
                b.levels = levels;
                b.heightMeters = height;
                b.houseNumber = houseNum;
                parsed.add(b);
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

        if (!parsed.isEmpty()) {
            synchronized (osmBuildings) {
                osmBuildings.clear();
                osmBuildings.addAll(parsed);
                appendCustomProjectBuildingLocked();
            }
        }
        return parsed.size();
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

    // --- Меню инструментов: DXF/IFC парсер, AR-рулетка, калибровка, CSV ---
    private void showProjectAndToolsMenu() {
        CharSequence[] items = new CharSequence[]{
                "1. Импорт проекта (.dxf / .ifc / .txt из Download)",
                "2. AR-рулетка (Замер дистанции и высоты ΔH в 2 тапа)",
                "3. Калибровка этажа и барометра (Отметка H)",
                "4. Обнулить уклономер (Тара 0°)",
                "5. Смена сезона (Сегодня / Равноденствие / Лето / Зима)",
                "6. Экспорт телеметрии в CSV"
        };
        new AlertDialog.Builder(this)
                .setTitle("BIM Инструменты и САПР")
                .setItems(items, (d, w) -> {
                    if (w == 0) importDxfOrIfcFile();
                    else if (w == 1) {
                        isTapeMode = !isTapeMode;
                        tapeBasePitch = null;
                        is2DMapMode = false;
                        btnModeToggle.setText("2D План");
                        tapeResultText = isTapeMode ? "AR-Рулетка: тапните по экрану на НИЗ объекта" : "";
                        Toast.makeText(this, isTapeMode ? "Режим AR-рулетки включен" : "AR-рулетка выключена", Toast.LENGTH_SHORT).show();
                        overlayView.invalidate();
                    } else if (w == 2) showAltitudeCalibrationDialog();
                    else if (w == 3) {
                        tarePitch = rawPitch;
                        tareRoll = rawRoll;
                        Toast.makeText(this, "Уклономер обнулен (0.0°)", Toast.LENGTH_SHORT).show();
                    } else if (w == 4) cycleSeason();
                    else if (w == 5) exportLogToCsv();
                }).show();
    }

    private void handleArTapeClick() {
        float pitchRad = (float) Math.toRadians(camAltitude);
        if (tapeBasePitch == null) {
            tapeBasePitch = pitchRad;
            tapeResultText = "Нижняя точка зафиксирована! Наведите на ВЕРХ и тапните";
        } else {
            float topPitch = pitchRad;
            float baseAbs = Math.max(0.03f, Math.abs(tapeBasePitch));
            float dist = (float) (tapeEyeHeight / Math.tan(baseAbs));
            float height = (float) (dist * (Math.tan(topPitch) - Math.tan(tapeBasePitch)));
            tapeResultText = String.format(Locale.US, "Рулетка: Дист = %.2f м | Высота ΔH = %.2f м", dist, Math.abs(height));
            tapeBasePitch = null;
        }
        overlayView.invalidate();
    }

    // Парсер реальных файлов .dxf (коды 10/20), .ifc (IFCCARTESIANPOINT) и .txt
    private void importDxfOrIfcFile() {
        try {
            File dir = Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DOWNLOADS);
            File dxfFile = new File(dir, "project.dxf");
            File ifcFile = new File(dir, "project.ifc");
            File txtFile = new File(dir, "project_contour.txt");

            List<float[]> pts = new ArrayList<>();
            String sourceName = "";

            if (dxfFile.exists()) {
                sourceName = "project.dxf";
                BufferedReader br = new BufferedReader(new FileReader(dxfFile));
                String line;
                Float lastX = null;
                while ((line = br.readLine()) != null) {
                    String code = line.trim();
                    if ("10".equals(code)) {
                        String val = br.readLine();
                        if (val != null) lastX = Float.parseFloat(val.trim());
                    } else if ("20".equals(code) && lastX != null) {
                        String val = br.readLine();
                        if (val != null) {
                            pts.add(new float[]{lastX, Float.parseFloat(val.trim())});
                            lastX = null;
                        }
                    }
                }
                br.close();
            } else if (ifcFile.exists()) {
                sourceName = "project.ifc";
                BufferedReader br = new BufferedReader(new FileReader(ifcFile));
                String line;
                while ((line = br.readLine()) != null) {
                    String up = line.toUpperCase(Locale.US);
                    if (up.contains("IFCCARTESIANPOINT((")) {
                        int s = up.indexOf("((") + 2, e = up.indexOf("))");
                        if (s > 1 && e > s) {
                            String[] coords = up.substring(s, e).split(",");
                            if (coords.length >= 2) {
                                pts.add(new float[]{Float.parseFloat(coords[0].trim()), Float.parseFloat(coords[1].trim())});
                            }
                        }
                    }
                }
                br.close();
            } else {
                if (!txtFile.exists()) {
                    FileWriter fw = new FileWriter(txtFile);
                    fw.append("15 15\n45 15\n45 35\n15 35\n");
                    fw.flush();
                    fw.close();
                }
                sourceName = "project_contour.txt";
                BufferedReader br = new BufferedReader(new FileReader(txtFile));
                String line;
                while ((line = br.readLine()) != null) {
                    String[] p = line.trim().split("\\s+");
                    if (p.length >= 2) pts.add(new float[]{Float.parseFloat(p[0]), Float.parseFloat(p[1])});
                }
                br.close();
            }

            if (pts.size() >= 3) {
                synchronized (osmBuildings) {
                    customProjectPolygon.clear();
                    customProjectPolygon.addAll(pts);
                    osmBuildings.removeIf(b -> b.isCustomProject);
                    appendCustomProjectBuildingLocked();
                }
                Toast.makeText(this, "Импортирован " + sourceName + " (" + pts.size() + " тчк)", Toast.LENGTH_LONG).show();
                overlayView.invalidate();
            }
        } catch (Exception e) {
            Toast.makeText(this, "Ошибка импорта DXF/IFC: " + e.getMessage(), Toast.LENGTH_SHORT).show();
        }
    }

    // Сетка КЕО + тепловая карта освещенности помещения (СП 52.13330)
    private void showKeoGridDialog() {
        String ext = externalLuxForKeo > 0 ? String.format(Locale.US, "%.0f лк", externalLuxForKeo) : "не задано";
        String wL = keoWindowLux > 0 ? String.format(Locale.US, "%.0f лк (КЕО %.2f%%)", keoWindowLux, externalLuxForKeo > 0 ? keoWindowLux * 100f / externalLuxForKeo : 0f) : "нет";
        String cL = keoCenterLux > 0 ? String.format(Locale.US, "%.0f лк (КЕО %.2f%%)", keoCenterLux, externalLuxForKeo > 0 ? keoCenterLux * 100f / externalLuxForKeo : 0f) : "нет";
        String bL = keoBackLux > 0 ? String.format(Locale.US, "%.0f лк (КЕО %.2f%%)", keoBackLux, externalLuxForKeo > 0 ? keoBackLux * 100f / externalLuxForKeo : 0f) : "нет";

        CharSequence[] actions = new CharSequence[]{
                "1. Зафиксировать уличный свет E_нар (" + Math.round(currentLux) + " лк)",
                "2. Записать точку: У ОКНА (" + wL + ")",
                "3. Записать точку: ЦЕНТР КОМНАТЫ (" + cL + ")",
                "4. Записать точку: ДАЛЬНИЙ УГОЛ (" + bL + ")",
                showKeoHeatmap ? "5. Скрыть тепловую карту КЕО с экрана" : "5. Показать тепловую карту КЕО на экране"
        };

        new AlertDialog.Builder(this)
                .setTitle("Сетка КЕО (СП 52.13330) | E_нар: " + ext)
                .setItems(actions, (d, which) -> {
                    if (which == 0) externalLuxForKeo = Math.max(1f, currentLux);
                    else if (which == 1) keoWindowLux = currentLux;
                    else if (which == 2) keoCenterLux = currentLux;
                    else if (which == 3) keoBackLux = currentLux;
                    else if (which == 4) showKeoHeatmap = !showKeoHeatmap;

                    if (externalLuxForKeo > 0) {
                        float ref = keoCenterLux > 0 ? keoCenterLux : currentLux;
                        lastCalculatedKeo = (ref / externalLuxForKeo) * 100.0f;
                    }
                    overlayView.invalidate();
                }).show();
    }

    // Генерация настоящего PDF-документа строительного акта инспекции
    private void generatePdfReport() {
        try {
            File dir = new File(Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DOWNLOADS), "BIM_Reports");
            if (!dir.exists()) dir.mkdirs();
            String tsFile = new SimpleDateFormat("yyyyMMdd_HHmmss", Locale.US).format(new Date());
            File pdfFile = new File(dir, "BIM_Inspection_Act_" + tsFile + ".pdf");

            PdfDocument pdf = new PdfDocument();
            PdfDocument.PageInfo pageInfo = new PdfDocument.PageInfo.Builder(595, 842, 1).create();
            PdfDocument.Page page = pdf.startPage(pageInfo);
            Canvas c = page.getCanvas();
            Paint p = new Paint(Paint.ANTI_ALIAS_FLAG);

            p.setColor(Color.rgb(20, 40, 70));
            p.setTextSize(16f);
            c.drawText("АКТ ПОЛЕВОЙ ИНСПЕКЦИИ И СТРОЙКОНТРОЛЯ (BIM Sun & Level)", 40, 45, p);

            p.setColor(Color.BLACK);
            p.setTextSize(11f);
            float[] insol = calculateInsolationWithOsm(latitude, selectedDayOfYear);
            int estFloor = Math.round(relativeHeightMeters / floorHeightMeters) + 1;
            float calPitch = rawPitch - tarePitch;
            float slopeMm = (float) (Math.tan(Math.toRadians(Math.abs(calPitch))) * 1000.0);

            c.drawText("Дата и время замера: " + new SimpleDateFormat("dd.MM.yyyy HH:mm:ss", Locale.US).format(new Date()), 40, 75, p);
            c.drawText(String.format(Locale.US, "Координаты GPS: %.5f N, %.5f E | Барометр: %.1f гПа", latitude, longitude, currentPressure), 40, 95, p);
            c.drawText(String.format(Locale.US, "Высотная отметка: %+.2f м (~%d этаж) | Азимут взгляда: %.1f°", relativeHeightMeters, estFloor, camAzimuth), 40, 115, p);
            c.drawText(String.format(Locale.US, "Нивелир / Уклон: %.2f° (%.0f мм/м) | Крен: %.2f°", calPitch, slopeMm, rawRoll - tareRoll), 40, 135, p);
            c.drawText(String.format(Locale.US, "Освещенность: %.0f лк | КЕО (СП 52.13330): %s", currentLux,
                    lastCalculatedKeo > 0 ? String.format(Locale.US, "%.2f%% (Окно %.0f / Центр %.0f / Угол %.0f лк)", lastCalculatedKeo, keoWindowLux, keoCenterLux, keoBackLux) : "не замерялся"), 40, 155, p);
            p.setColor(insol[1] >= 2.0f ? Color.rgb(0, 130, 60) : Color.rgb(200, 30, 30));
            c.drawText(String.format(Locale.US, "Заключение СанПиН (инсоляция): %s — %.1f ч без тени (астрон. %.1f ч)",
                    insol[1] >= 2.0f ? "НОРМА СОБЛЮДЕНА (>=2.0ч)" : "НАРУШЕНИЕ (<2.0ч)", insol[1], insol[0]), 40, 180, p);

            // Встраиваем графический снимок генплана/AR прямо в лист PDF
            Bitmap snap = Bitmap.createBitmap(overlayView.getWidth(), overlayView.getHeight(), Bitmap.Config.ARGB_8888);
            Canvas snapCanvas = new Canvas(snap);
            snapCanvas.drawColor(Color.rgb(18, 26, 38));
            overlayView.draw(snapCanvas);
            Rect dest = new Rect(40, 200, 555, 800);
            c.drawBitmap(snap, null, dest, null);
            snap.recycle();

            pdf.finishPage(page);
            FileOutputStream fos = new FileOutputStream(pdfFile);
            pdf.writeTo(fos);
            fos.close();
            pdf.close();

            Toast.makeText(this, "PDF сохранен: Download/BIM_Reports/" + pdfFile.getName(), Toast.LENGTH_LONG).show();
        } catch (Exception e) {
            Toast.makeText(this, "Ошибка PDF: " + e.getMessage(), Toast.LENGTH_SHORT).show();
        }
    }

    private void showEditBuildingDialog(OsmBuilding b) {
        final EditText input = new EditText(this);
        input.setInputType(InputType.TYPE_CLASS_NUMBER);
        input.setText(String.valueOf(b.levels));
        new AlertDialog.Builder(this)
                .setTitle("Этажность дома " + (b.houseNumber.isEmpty() ? "" : b.houseNumber))
                .setView(input)
                .setPositiveButton("Применить", (d, w) -> {
                    try {
                        int lvl = Integer.parseInt(input.getText().toString().trim());
                        if (lvl > 0) {
                            b.levels = lvl;
                            b.heightMeters = lvl * 3.0f;
                            if (b.isCustomProject) customProjectHeight = b.heightMeters;
                            overlayView.invalidate();
                        }
                    } catch (Exception ignored) {}
                }).setNegativeButton("Отмена", null).show();
    }

    private void showAltitudeCalibrationDialog() {
        final EditText inputFloor = new EditText(this);
        inputFloor.setInputType(InputType.TYPE_CLASS_NUMBER | InputType.TYPE_NUMBER_FLAG_SIGNED);
        inputFloor.setText(String.valueOf(Math.round(relativeHeightMeters / floorHeightMeters) + 1));
        new AlertDialog.Builder(this)
                .setTitle("Укажите ваш текущий этаж")
                .setView(inputFloor)
                .setPositiveButton("Привязать", (d, w) -> {
                    try {
                        int fl = Integer.parseInt(inputFloor.getText().toString().trim());
                        basePressure = currentPressure;
                        calibratedBaseHeight = (fl - 1) * floorHeightMeters;
                        overlayView.invalidate();
                    } catch (Exception ignored) {}
                }).setNegativeButton("Отмена", null).show();
    }

    private void cycleSeason() {
        if (selectedDayOfYear != 80 && selectedDayOfYear != 172 && selectedDayOfYear != 355) {
            selectedDayOfYear = 80;
            selectedSeasonLabel = "21 Мар/Сен (Равноденствие)";
        } else if (selectedDayOfYear == 80) {
            selectedDayOfYear = 172;
            selectedSeasonLabel = "21 Июня (Лето)";
        } else if (selectedDayOfYear == 172) {
            selectedDayOfYear = 355;
            selectedSeasonLabel = "21 Декабря (Зима)";
        } else {
            selectedDayOfYear = Calendar.getInstance().get(Calendar.DAY_OF_YEAR);
            selectedSeasonLabel = "Сегодня (#" + selectedDayOfYear + ")";
        }
        overlayView.invalidate();
    }

    // --- Астрономия и геометрия теней ---
    private double[] computeSunPosition(double latDeg, int dayOfYear, double localClockHour) {
        double tzHours = TimeZone.getDefault().getOffset(System.currentTimeMillis()) / 3600000.0;
        double bRad = Math.toRadians((360.0 / 365.0) * (dayOfYear - 81));
        double eotMin = 9.87 * Math.sin(2.0 * bRad) - 7.53 * Math.cos(bRad) - 1.5 * Math.sin(bRad);
        double trueSolarHour = localClockHour + (4.0 * (longitude - 15.0 * tzHours) + eotMin) / 60.0;

        double latRad = Math.toRadians(latDeg);
        double declRad = Math.toRadians(23.45 * Math.sin(Math.toRadians((360.0 / 365.0) * (284 + dayOfYear))));
        double haRad = Math.toRadians(15.0 * (trueSolarHour - 12.0));

        double sinAlt = Math.max(-1.0, Math.min(1.0, Math.sin(latRad) * Math.sin(declRad) + Math.cos(latRad) * Math.cos(declRad) * Math.cos(haRad)));
        double altRad = Math.asin(sinAlt);
        double cosAz = Math.max(-1.0, Math.min(1.0, (Math.sin(declRad) - Math.sin(altRad) * Math.sin(latRad)) / (Math.cos(altRad) * Math.cos(latRad) + 1e-6)));
        double azDeg = Math.toDegrees(Math.acos(cosAz));
        if (((trueSolarHour % 24.0) + 24.0) % 24.0 > 12.0) azDeg = 360.0 - azDeg;
        return new double[]{azDeg, Math.toDegrees(altRad)};
    }

    private boolean isSunBlockedByOsmBuildings(double sunAzDeg, double sunAltDeg) {
        if (sunAltDeg <= 0.0) return true;
        synchronized (osmBuildings) {
            for (OsmBuilding b : osmBuildings) {
                if (doesBuildingBlockSun(b, sunAzDeg, sunAltDeg)) return true;
            }
        }
        return false;
    }

    private boolean doesBuildingBlockSun(OsmBuilding b, double sunAzDeg, double sunAltDeg) {
        if (sunAltDeg <= 0.5) return false;
        float dh = b.heightMeters - relativeHeightMeters;
        if (dh <= 0.5f || isPointInPolygon(0f, 0f, b.xMeters, b.yMeters)) return false;
        float maxShadowDist = (float) (dh / Math.tan(Math.toRadians(Math.max(0.5, sunAltDeg))));
        float dx = (float) Math.sin(Math.toRadians(sunAzDeg)), dy = (float) Math.cos(Math.toRadians(sunAzDeg));
        int n = b.xMeters.length;
        for (int i = 0; i < n; i++) {
            float dist = intersectRayWithSegment(dx, dy, b.xMeters[i], b.yMeters[i], b.xMeters[(i + 1) % n], b.yMeters[(i + 1) % n]);
            if (dist > 2.0f && dist <= maxShadowDist) return true;
        }
        return false;
    }

    private boolean isPointInPolygon(float px, float py, float[] vx, float[] vy) {
        boolean inside = false;
        for (int i = 0, j = vx.length - 1; i < vx.length; j = i++) {
            if (((vy[i] > py) != (vy[j] > py)) && (px < (vx[j] - vx[i]) * (py - vy[i]) / (vy[j] - vy[i] + 1e-6f) + vx[i])) {
                inside = !inside;
            }
        }
        return inside;
    }

    private float intersectRayWithSegment(float dx, float dy, float x1, float y1, float x2, float y2) {
        float sx = x2 - x1, sy = y2 - y1;
        float det = -dx * sy + dy * sx;
        if (Math.abs(det) < 1e-5f) return -1f;
        float t = (-sy * (-x1) + sx * (-y1)) / det;
        float u = (dx * (-y1) - dy * (-x1)) / det;
        return (t >= 0f && u >= 0f && u <= 1f) ? t : -1f;
    }

    private float[] calculateInsolationWithOsm(double lat, int day) {
        float astro = 0f, unblocked = 0f;
        for (double hr = 4.0; hr <= 22.0; hr += 0.25) {
            double[] pos = computeSunPosition(lat, day, hr);
            if (pos[1] > 0.0) {
                astro += 0.25f;
                if (!isSunBlockedByOsmBuildings(pos[0], pos[1])) unblocked += 0.25f;
            }
        }
        return new float[]{astro, unblocked};
    }

    private void exportLogToCsv() {
        try {
            File dir = Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DOWNLOADS);
            if (!dir.exists()) dir.mkdirs();
            File file = new File(dir, "BIM_Field_Log.csv");
            boolean isNew = !file.exists();
            FileWriter fw = new FileWriter(file, true);
            if (isNew) fw.append("Timestamp,Lat,Lon,Azimuth,Altitude,Slope_deg,Slope_mm_m,Lux,KEO_pct,Height_m,ClockHour\n");
            String ts = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss", Locale.US).format(new Date());
            float calP = rawPitch - tarePitch;
            float mmM = (float) (Math.tan(Math.toRadians(Math.abs(calP))) * 1000.0);
            fw.append(String.format(Locale.US, "%s,%.5f,%.5f,%.1f,%.1f,%.2f,%.0f,%.0f,%.2f,%.2f,%.2f\n",
                    ts, latitude, longitude, camAzimuth, camAltitude, calP, mmM, currentLux, lastCalculatedKeo, relativeHeightMeters, displayedClockHour));
            fw.flush();
            fw.close();
            Toast.makeText(this, "Сохранено в Download/BIM_Field_Log.csv", Toast.LENGTH_LONG).show();
        } catch (Exception e) {
            Toast.makeText(this, "Ошибка CSV: " + e.getMessage(), Toast.LENGTH_SHORT).show();
        }
    }

    private void captureARPhoto() {
        int w = overlayView.getWidth(), h = overlayView.getHeight();
        if (w <= 0 || h <= 0) return;
        if (is2DMapMode || camera == null) {
            saveCombinedBitmapToGallery(null, w, h);
            return;
        }
        try {
            camera.setOneShotPreviewCallback((data, cam) -> {
                try {
                    Camera.Size s = cam.getParameters().getPreviewSize();
                    YuvImage yuv = new YuvImage(data, ImageFormat.NV21, s.width, s.height, null);
                    ByteArrayOutputStream baos = new ByteArrayOutputStream();
                    yuv.compressToJpeg(new Rect(0, 0, s.width, s.height), 92, baos);
                    Bitmap raw = BitmapFactory.decodeByteArray(baos.toByteArray(), 0, baos.size());
                    Matrix m = new Matrix();
                    m.postRotate(90);
                    Bitmap rot = Bitmap.createBitmap(raw, 0, 0, raw.getWidth(), raw.getHeight(), m, true);
                    raw.recycle();
                    saveCombinedBitmapToGallery(rot, w, h);
                } catch (Exception e) {
                    Toast.makeText(this, "Ошибка фото: " + e.getMessage(), Toast.LENGTH_SHORT).show();
                }
            });
        } catch (Exception ignored) {}
    }

    private void saveCombinedBitmapToGallery(Bitmap camBmp, int w, int h) {
        try {
            Bitmap combo = Bitmap.createBitmap(w, h, Bitmap.Config.ARGB_8888);
            Canvas c = new Canvas(combo);
            if (camBmp != null) {
                c.drawBitmap(camBmp, null, new Rect(0, 0, w, h), null);
                camBmp.recycle();
            }
            overlayView.draw(c);
            ContentValues cv = new ContentValues();
            cv.put(MediaStore.Images.Media.DISPLAY_NAME, "BIM_AR_" + System.currentTimeMillis() + ".jpg");
            cv.put(MediaStore.Images.Media.MIME_TYPE, "image/jpeg");
            cv.put(MediaStore.Images.Media.RELATIVE_PATH, Environment.DIRECTORY_PICTURES + "/BIM_SunLevel");
            Uri uri = getContentResolver().insert(MediaStore.Images.Media.EXTERNAL_CONTENT_URI, cv);
            if (uri != null) {
                OutputStream os = getContentResolver().openOutputStream(uri);
                if (os != null) {
                    combo.compress(Bitmap.CompressFormat.JPEG, 92, os);
                    os.close();
                }
                Toast.makeText(this, "Фото сохранено в Галерею", Toast.LENGTH_SHORT).show();
            }
            combo.recycle();
        } catch (Exception ignored) {}
    }

    private void requestPermissionsIfNeeded() {
        if (checkSelfPermission(Manifest.permission.CAMERA) != PackageManager.PERMISSION_GRANTED ||
            checkSelfPermission(Manifest.permission.ACCESS_FINE_LOCATION) != PackageManager.PERMISSION_GRANTED) {
            requestPermissions(new String[]{Manifest.permission.CAMERA, Manifest.permission.ACCESS_FINE_LOCATION, Manifest.permission.ACCESS_COARSE_LOCATION}, 101);
        } else {
            startLocationUpdates();
        }
    }

    @Override
    public void onRequestPermissionsResult(int requestCode, String[] permissions, int[] grantResults) {
        startLocationUpdates();
        if (cameraSurface.getHolder().getSurface().isValid()) startCameraPreview(cameraSurface.getHolder());
    }

    private void startLocationUpdates() {
        try {
            if (checkSelfPermission(Manifest.permission.ACCESS_FINE_LOCATION) == PackageManager.PERMISSION_GRANTED) {
                Location last = locationManager.getLastKnownLocation(LocationManager.GPS_PROVIDER);
                if (last == null) last = locationManager.getLastKnownLocation(LocationManager.NETWORK_PROVIDER);
                if (last != null) onNewLocation(last);
                LocationListener ll = this::onNewLocation;
                locationManager.requestLocationUpdates(LocationManager.GPS_PROVIDER, 4000, 5f, ll);
                locationManager.requestLocationUpdates(LocationManager.NETWORK_PROVIDER, 4000, 5f, ll);
            }
        } catch (Exception ignored) {}
    }

    private void onNewLocation(Location loc) {
        latitude = loc.getLatitude();
        longitude = loc.getLongitude();
        gpsLocked = true;
        double distSq = Math.pow((latitude - lastOsmLat) * 111132.0, 2) + Math.pow((longitude - lastOsmLon) * 65000.0, 2);
        if (!realOsmLoaded || distSq > 2500.0) fetchOsmBuildings(latitude, longitude);
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
            SensorManager.remapCoordinateSystem(rotationMatrix, SensorManager.AXIS_X, SensorManager.AXIS_Z, remappedMatrix);
            SensorManager.getOrientation(remappedMatrix, orientationVals);
            float az = (float) Math.toDegrees(orientationVals[0]);
            if (az < 0) az += 360f;
            camAzimuth = lowPassAngle(az, camAzimuth, 0.16f);
            camAltitude += 0.16f * ((float) -Math.toDegrees(orientationVals[1]) - camAltitude);
            camRoll += 0.16f * ((float) Math.toDegrees(orientationVals[2]) - camRoll);
        } else if (type == Sensor.TYPE_ACCELEROMETER) {
            float gx = event.values[0], gy = event.values[1], gz = event.values[2];
            rawPitch += 0.12f * ((float) Math.toDegrees(Math.atan2(gy, Math.sqrt(gx * gx + gz * gz))) - rawPitch);
            rawRoll += 0.12f * ((float) Math.toDegrees(Math.atan2(-gx, Math.sqrt(gy * gy + gz * gz))) - rawRoll);
        } else if (type == Sensor.TYPE_PRESSURE) {
            currentPressure = (basePressure < 0) ? event.values[0] : (currentPressure + 0.15f * (event.values[0] - currentPressure));
            if (basePressure < 0) basePressure = currentPressure;
            relativeHeightMeters = calibratedBaseHeight + 44330f * (1f - (float) Math.pow(currentPressure / basePressure, 0.190295f));
        } else if (type == Sensor.TYPE_LIGHT) {
            currentLux = event.values[0];
        }

        if (isLiveTime) syncWithRealTime();
        // Плавная интерполяция времени для гладкой анимации теней и солнца
        displayedClockHour += 0.22 * (targetClockHour - displayedClockHour);
        if (overlayView != null) overlayView.invalidate();
    }

    private float lowPassAngle(float n, float o, float a) {
        float d = n - o;
        if (d > 180f) d -= 360f;
        if (d < -180f) d += 360f;
        return (o + a * d + 360f) % 360f;
    }

    @Override public void onAccuracyChanged(Sensor sensor, int accuracy) {}

    @Override
    public void surfaceCreated(SurfaceHolder holder) {
        if (checkSelfPermission(Manifest.permission.CAMERA) == PackageManager.PERMISSION_GRANTED) startCameraPreview(holder);
    }
    @Override public void surfaceChanged(SurfaceHolder h, int f, int w, int he) {}
    @Override
    public void surfaceDestroyed(SurfaceHolder holder) {
        if (camera != null) {
            try { camera.stopPreview(); camera.release(); } catch (Exception ignored) {}
            camera = null;
        }
    }

    private void startCameraPreview(SurfaceHolder holder) {
        try {
            if (camera == null) camera = Camera.open();
            if (camera != null) {
                camera.stopPreview();
                camera.setDisplayOrientation(90);
                camera.setPreviewDisplay(holder);
                camera.startPreview();
            }
        } catch (Exception ignored) {}
    }

    // --- Отрисовка AR-камеры (прозрачной), 2D-генплана, мини-радара и тепловой карты КЕО ---
    private class AROverlayView extends View {
        private final Paint paint = new Paint(Paint.ANTI_ALIAS_FLAG);
        private final Path path = new Path();

        public AROverlayView(Context context) { super(context); }

        @Override
        protected void onDraw(Canvas canvas) {
            super.onDraw(canvas);
            int w = getWidth(), h = getHeight();

            if (is2DMapMode) {
                canvas.drawColor(isLightFieldTheme ? Color.rgb(238, 242, 247) : Color.rgb(14, 22, 34));
                draw2DTopDownMap(canvas, w, h);
            } else {
                // В режиме AR НЕ закрашиваем холст, чтобы видеопоток с камеры был 100% прозрачным и видимым
                drawARCameraOverlay(canvas, w, h);
            }

            if (showKeoHeatmap) drawKeoHeatmapWidget(canvas, w, h);
            drawTelemetryHeader(canvas, w);
        }

        private void draw2DTopDownMap(Canvas canvas, int w, int h) {
            float cx = w / 2f, cy = h * 0.56f, sc = mapScalePixelsPerMeter;
            paint.setStyle(Paint.Style.STROKE);
            paint.setStrokeWidth(1.5f);
            paint.setColor(isLightFieldTheme ? Color.argb(100, 90, 110, 140) : Color.argb(75, 90, 140, 190));
            canvas.drawLine(0, cy, w, cy, paint);
            canvas.drawLine(cx, 390, cx, h - 180, paint);

            paint.setTextSize(21f);
            for (int r : new int[]{50, 100, 150, 200}) {
                canvas.drawCircle(cx, cy, r * sc, paint);
                paint.setStyle(Paint.Style.FILL);
                canvas.drawText(r + "м", cx + 6, cy - r * sc + 20, paint);
                paint.setStyle(Paint.Style.STROKE);
            }

            paint.setStyle(Paint.Style.FILL);
            paint.setColor(isLightFieldTheme ? Color.argb(40, 0, 160, 110) : Color.argb(45, 0, 255, 180));
            canvas.drawArc(new RectF(cx - 120 * sc, cy - 120 * sc, cx + 120 * sc, cy + 120 * sc), camAzimuth - 120f, 60f, true, paint);

            double[] sunPos = computeSunPosition(latitude, selectedDayOfYear, displayedClockHour);
            double sunAz = sunPos[0], sunAlt = sunPos[1];
            float shX = (float) Math.sin(Math.toRadians(sunAz + 180.0)), shY = (float) Math.cos(Math.toRadians(sunAz + 180.0));
            double tanAlt = Math.max(0.08, Math.tan(Math.toRadians(Math.max(1.0, sunAlt))));

            synchronized (osmBuildings) {
                if (sunAlt > 0.5) {
                    paint.setColor(isLightFieldTheme ? Color.argb(85, 100, 115, 135) : Color.argb(145, 4, 8, 15));
                    for (OsmBuilding b : osmBuildings) {
                        float len = Math.min(260f, (float) (b.heightMeters / tanAlt));
                        drawBuildingShadow(canvas, b, cx, cy, sc, shX * len, shY * len);
                    }
                    paint.setColor(isLightFieldTheme ? Color.argb(95, 170, 60, 200) : Color.argb(120, 180, 70, 220));
                    for (OsmBuilding b : osmBuildings) {
                        float dh = b.heightMeters - relativeHeightMeters;
                        if (dh > 0.5f) {
                            float len = Math.min(260f, (float) (dh / tanAlt));
                            drawBuildingShadow(canvas, b, cx, cy, sc, shX * len, shY * len);
                        }
                    }
                }

                for (OsmBuilding b : osmBuildings) {
                    path.reset();
                    float sumX = 0f, sumY = 0f;
                    int n = b.xMeters.length;
                    for (int i = 0; i < n; i++) {
                        float sx = cx + b.xMeters[i] * sc, sy = cy - b.yMeters[i] * sc;
                        sumX += sx;
                        sumY += sy;
                        if (i == 0) path.moveTo(sx, sy);
                        else path.lineTo(sx, sy);
                    }
                    path.close();

                    boolean inside = isPointInPolygon(0f, 0f, b.xMeters, b.yMeters);
                    boolean blocks = doesBuildingBlockSun(b, sunAz, sunAlt);

                    paint.setStyle(Paint.Style.FILL);
                    if (b.isCustomProject) paint.setColor(Color.argb(190, 0, 180, 215));
                    else if (inside) paint.setColor(Color.argb(210, 30, 140, 100));
                    else if (blocks) paint.setColor(Color.argb(210, 175, 45, 55));
                    else paint.setColor(isLightFieldTheme ? Color.argb(200, 195, 208, 225) : Color.argb(200, 55, 80, 110));
                    canvas.drawPath(path, paint);

                    paint.setStyle(Paint.Style.STROKE);
                    paint.setStrokeWidth(blocks || inside || b.isCustomProject ? 3.5f : 2f);
                    paint.setColor(b.isCustomProject ? Color.CYAN : (blocks ? Color.rgb(255, 70, 70) : (inside ? Color.GREEN : Color.rgb(120, 175, 230))));
                    canvas.drawPath(path, paint);

                    paint.setStyle(Paint.Style.FILL);
                    paint.setColor(isLightFieldTheme ? Color.BLACK : Color.WHITE);
                    paint.setTextSize(18f);
                    String lbl = b.houseNumber.isEmpty() ? (b.levels + "эт") : (b.houseNumber + "(" + b.levels + "э)");
                    canvas.drawText(lbl, sumX / n - 24f, sumY / n + 6f, paint);
                }
            }

            if (sunAlt > 0) {
                float sx = cx + (float) Math.sin(Math.toRadians(sunAz)) * 250f;
                float sy = cy - (float) Math.cos(Math.toRadians(sunAz)) * 250f;
                paint.setStyle(Paint.Style.STROKE);
                paint.setStrokeWidth(5f);
                paint.setColor(Color.rgb(255, 205, 0));
                canvas.drawLine(cx, cy, sx, sy, paint);
                paint.setStyle(Paint.Style.FILL);
                canvas.drawCircle(sx, sy, 16f, paint);
            }
            paint.setStyle(Paint.Style.FILL);
            paint.setColor(Color.rgb(0, 230, 130));
            canvas.drawCircle(cx, cy, 10f, paint);
        }

        private void drawBuildingShadow(Canvas c, OsmBuilding b, float cx, float cy, float sc, float ox, float oy) {
            int n = b.xMeters.length;
            for (int i = 0; i < n; i++) {
                int nx = (i + 1) % n;
                path.reset();
                path.moveTo(cx + b.xMeters[i] * sc, cy - b.yMeters[i] * sc);
                path.lineTo(cx + b.xMeters[nx] * sc, cy - b.yMeters[nx] * sc);
                path.lineTo(cx + (b.xMeters[nx] + ox) * sc, cy - (b.yMeters[nx] + oy) * sc);
                path.lineTo(cx + (b.xMeters[i] + ox) * sc, cy - (b.yMeters[i] + oy) * sc);
                path.close();
                c.drawPath(path, paint);
            }
        }

        private void drawARCameraOverlay(Canvas canvas, int w, int h) {
            float cx = w / 2f, cy = h / 2f, fovH = 60f, fovV = 75f;

            // Контуры реальных домов OSM в AR
            paint.setStyle(Paint.Style.STROKE);
            paint.setStrokeWidth(2.5f);
            double[] curSun = computeSunPosition(latitude, selectedDayOfYear, displayedClockHour);
            synchronized (osmBuildings) {
                for (OsmBuilding b : osmBuildings) {
                    if (isPointInPolygon(0f, 0f, b.xMeters, b.yMeters)) continue;
                    boolean blocks = doesBuildingBlockSun(b, curSun[0], curSun[1]);
                    paint.setColor(blocks ? Color.argb(180, 255, 80, 80) : Color.argb(140, 90, 200, 255));
                    for (int i = 0; i < b.xMeters.length; i++) {
                        float x = b.xMeters[i], y = b.yMeters[i];
                        float dist = (float) Math.hypot(x, y);
                        if (dist < 4f || dist > 190f) continue;
                        float az = ((float) Math.toDegrees(Math.atan2(x, y)) + 360f) % 360f;
                        float sx = azimuthToScreenX(az, w, fovH);
                        if (sx >= 0 && sx <= w) {
                            float syRoof = cy - (((float) Math.toDegrees(Math.atan2(b.heightMeters - relativeHeightMeters, dist)) - camAltitude) / fovV) * h;
                            float syBase = cy - (((float) Math.toDegrees(Math.atan2(-relativeHeightMeters, dist)) - camAltitude) / fovV) * h;
                            canvas.drawLine(sx, syRoof, sx, syBase, paint);
                        }
                    }
                }
            }

            float horizonY = cy + (camAltitude / fovV) * h;
            paint.setColor(Color.argb(180, 0, 255, 180));
            paint.setStrokeWidth(3f);
            canvas.drawLine(0, horizonY, w, horizonY, paint);

            drawSunArc(canvas, w, h, fovH, fovV, 355, Color.argb(140, 100, 180, 255), false);
            drawSunArc(canvas, w, h, fovH, fovV, 172, Color.argb(140, 255, 120, 80), false);
            drawSunArc(canvas, w, h, fovH, fovV, selectedDayOfYear, Color.rgb(255, 230, 0), true);

            if (curSun[1] > -6.0) {
                float sunX = azimuthToScreenX((float) curSun[0], w, fovH);
                float sunY = cy - (((float) curSun[1] - camAltitude) / fovV) * h;
                boolean blocked = isSunBlockedByOsmBuildings(curSun[0], curSun[1]);
                paint.setStyle(Paint.Style.FILL);
                paint.setColor(blocked ? Color.rgb(255, 75, 75) : Color.rgb(255, 235, 50));
                canvas.drawCircle(sunX, sunY, 24f, paint);
            }

            drawSmartMiniRadar(canvas, w, curSun[0]);

            float calP = rawPitch - tarePitch, calR = rawRoll - tareRoll, r = 95f;
            boolean ok = Math.abs(calP) < 0.5f && Math.abs(calR) < 0.5f;
            paint.setStyle(Paint.Style.STROKE);
            paint.setStrokeWidth(4f);
            paint.setColor(ok ? Color.GREEN : Color.WHITE);
            canvas.drawCircle(cx, cy, r, paint);
            canvas.drawLine(cx - r - 20, cy, cx + r + 20, cy, paint);
            canvas.drawLine(cx, cy - r - 20, cx, cy + r + 20, paint);

            paint.setStyle(Paint.Style.FILL);
            paint.setColor(ok ? Color.argb(210, 0, 255, 100) : Color.argb(210, 255, 180, 0));
            canvas.drawCircle(cx + Math.max(-r, Math.min(r, (calR / 15f) * r)),
                              cy + Math.max(-r, Math.min(r, (calP / 15f) * r)), 18f, paint);

            if (!tapeResultText.isEmpty()) {
                paint.setColor(Color.argb(210, 15, 25, 35));
                canvas.drawRoundRect(new RectF(30, h - 255, w - 30, h - 195), 14f, 14f, paint);
                paint.setColor(Color.CYAN);
                paint.setTextSize(25f);
                canvas.drawText(tapeResultText, 50, h - 216, paint);
            }
        }

        private void drawSmartMiniRadar(Canvas c, int w, double sunAz) {
            float rx = w - 95f, ry = 465f, rad = 68f;
            paint.setStyle(Paint.Style.FILL);
            paint.setColor(Color.argb(185, 14, 22, 34));
            c.drawCircle(rx, ry, rad, paint);
            paint.setStyle(Paint.Style.STROKE);
            paint.setStrokeWidth(2.5f);
            paint.setColor(Color.rgb(0, 230, 180));
            c.drawCircle(rx, ry, rad, paint);

            // Дома вокруг на мини-радаре
            paint.setStyle(Paint.Style.FILL);
            paint.setColor(Color.argb(170, 120, 190, 255));
            double rotRad = Math.toRadians(-camAzimuth);
            synchronized (osmBuildings) {
                for (OsmBuilding b : osmBuildings) {
                    if (b.xMeters.length > 0) {
                        float bx = b.xMeters[0] * 0.45f, by = b.yMeters[0] * 0.45f;
                        float rxPt = (float) (bx * Math.cos(rotRad) - by * Math.sin(rotRad));
                        float ryPt = (float) (bx * Math.sin(rotRad) + by * Math.cos(rotRad));
                        if (Math.hypot(rxPt, ryPt) < rad - 10f) c.drawCircle(rx + rxPt, ry - ryPt, 3.5f, paint);
                    }
                }
            }

            double nRad = Math.toRadians(-camAzimuth - 90.0);
            paint.setColor(Color.RED);
            paint.setTextSize(18f);
            c.drawText("N", rx + (float) Math.cos(nRad) * (rad - 14f) - 6f, ry + (float) Math.sin(nRad) * (rad - 14f) + 6f, paint);

            double sRad = Math.toRadians(sunAz - camAzimuth - 90.0);
            paint.setColor(Color.YELLOW);
            c.drawCircle(rx + (float) Math.cos(sRad) * (rad - 14f), ry + (float) Math.sin(sRad) * (rad - 14f), 8f, paint);
        }

        private void drawKeoHeatmapWidget(Canvas c, int w, int h) {
            RectF box = new RectF(30, 410, 350, 560);
            paint.setStyle(Paint.Style.FILL);
            paint.setColor(Color.argb(215, 16, 22, 32));
            c.drawRoundRect(box, 16f, 16f, paint);

            float eExt = Math.max(1f, externalLuxForKeo > 0 ? externalLuxForKeo : 5000f);
            float k1 = (keoWindowLux > 0 ? keoWindowLux : currentLux) * 100f / eExt;
            float k2 = (keoCenterLux > 0 ? keoCenterLux : currentLux * 0.5f) * 100f / eExt;
            float k3 = (keoBackLux > 0 ? keoBackLux : currentLux * 0.2f) * 100f / eExt;

            float[] vals = new float[]{k1, k2, k3};
            String[] names = new String[]{"Окно", "Центр", "Угол"};
            for (int i = 0; i < 3; i++) {
                paint.setColor(vals[i] >= 1.0f ? Color.rgb(40, 190, 90) : (vals[i] >= 0.5f ? Color.rgb(230, 175, 30) : Color.rgb(215, 55, 55)));
                c.drawRoundRect(new RectF(45 + i * 98, 445, 133 + i * 98, 545), 10f, 10f, paint);
                paint.setColor(Color.WHITE);
                paint.setTextSize(19f);
                c.drawText(names[i], 55 + i * 98, 480, paint);
                c.drawText(String.format(Locale.US, "%.1f%%", vals[i]), 55 + i * 98, 520, paint);
            }
        }

        private void drawTelemetryHeader(Canvas c, int w) {
            paint.setStyle(Paint.Style.FILL);
            paint.setColor(isLightFieldTheme ? Color.argb(235, 250, 252, 255) : Color.argb(200, 14, 20, 28));
            c.drawRoundRect(new RectF(16, 22, w - 16, 385), 20f, 20f, paint);

            double[] curSun = computeSunPosition(latitude, selectedDayOfYear, displayedClockHour);
            int txtMain = isLightFieldTheme ? Color.BLACK : Color.WHITE;
            paint.setColor(txtMain);
            paint.setTextSize(28f);
            c.drawText(String.format(Locale.US, "Азимут: %.1f° (%s) | Солнце: Аз %.0f° Выс %.0f°",
                    camAzimuth, getCardinal(camAzimuth), curSun[0], curSun[1]), 34, 64, paint);

            float calP = rawPitch - tarePitch, calR = rawRoll - tareRoll;
            float slopePct = (float) (Math.tan(Math.toRadians(Math.abs(calP))) * 100.0);
            paint.setColor(Math.abs(calP) < 0.5f ? Color.rgb(0, 170, 70) : (isLightFieldTheme ? Color.rgb(175, 100, 0) : Color.rgb(255, 215, 80)));
            c.drawText(String.format(Locale.US, "Уклон: %.1f° | %.1f%% | %.0f мм/м (Крен %.1f°)", calP, slopePct, slopePct * 10f, calR), 34, 112, paint);

            int estFl = Math.round(relativeHeightMeters / floorHeightMeters) + 1;
            paint.setColor(isLightFieldTheme ? Color.rgb(0, 95, 165) : Color.rgb(130, 220, 255));
            c.drawText(String.format(Locale.US, "Отметка H: %+.2f м (~%d эт.) | %.1f гПа", relativeHeightMeters, estFl, currentPressure), 34, 160, paint);

            paint.setColor(isLightFieldTheme ? Color.rgb(20, 125, 50) : Color.rgb(190, 255, 160));
            c.drawText(String.format(Locale.US, "Свет: %.0f лк | КЕО: %s", currentLux,
                    lastCalculatedKeo > 0 ? String.format(Locale.US, "%.2f%%", lastCalculatedKeo) : "не замер."), 34, 208, paint);

            float[] ins = calculateInsolationWithOsm(latitude, selectedDayOfYear);
            paint.setColor(ins[1] >= 2.0f ? Color.rgb(0, 175, 85) : Color.rgb(225, 55, 55));
            c.drawText(String.format(Locale.US, "СанПиН: %s (%.1f ч без тени / %.1f ч)",
                    ins[1] >= 2.0f ? "СОБЛЮДЕНА (≥2ч)" : "НАРУШЕНИЕ (<2ч)", ins[1], ins[0]), 34, 256, paint);

            paint.setTextSize(23f);
            paint.setColor(realOsmLoaded ? Color.rgb(0, 160, 80) : Color.rgb(220, 130, 20));
            c.drawText(String.format(Locale.US, "%.4f N, %.4f E [%s] | %s",
                    latitude, longitude, gpsLocked ? "GPS" : "Старт", osmStatus), 34, 302, paint);

            paint.setColor(isLightFieldTheme ? Color.DKGRAY : Color.rgb(150, 205, 255));
            c.drawText(selectedSeasonLabel + " | Тап сверху = обновить карту OSM", 34, 342, paint);
            c.drawText("Тап по дому на 2D-плане = этажи | Красный = затеняет", 34, 374, paint);
        }

        private void drawSunArc(Canvas c, int w, int h, float fovH, float fovV, int day, int color, boolean drawHrs) {
            paint.setColor(color);
            paint.setStyle(Paint.Style.STROKE);
            paint.setStrokeWidth(drawHrs ? 5.5f : 3f);
            path.reset();
            boolean started = false;
            for (double hr = 4.0; hr <= 22.0; hr += 0.5) {
                double[] pos = computeSunPosition(latitude, day, hr);
                if (pos[1] < -5.0) continue;
                float sx = azimuthToScreenX((float) pos[0], w, fovH);
                float sy = (h / 2f) - (((float) pos[1] - camAltitude) / fovV) * h;
                if (sx >= -w && sx <= 2 * w) {
                    if (!started) { path.moveTo(sx, sy); started = true; }
                    else path.lineTo(sx, sy);
                } else started = false;

                if (drawHrs && Math.abs(hr - Math.round(hr)) < 0.01 && sx >= 0 && sx <= w && sy >= 0 && sy <= h) {
                    boolean blk = isSunBlockedByOsmBuildings(pos[0], pos[1]);
                    paint.setStyle(Paint.Style.FILL);
                    paint.setColor(blk ? Color.rgb(255, 80, 80) : color);
                    c.drawCircle(sx, sy, 10f, paint);
                    paint.setTextSize(24f);
                    c.drawText(((int) hr) + ":00", sx - 24f, sy - 14f, paint);
                    paint.setStyle(Paint.Style.STROKE);
                    paint.setColor(color);
                }
            }
            c.drawPath(path, paint);
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
    }
}
