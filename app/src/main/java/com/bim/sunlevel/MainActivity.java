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
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.net.HttpURLConnection;
import java.net.URL;
import java.net.URLEncoder;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.List;
import java.util.Locale;
import java.util.TimeZone;
import java.util.concurrent.atomic.AtomicBoolean;

@SuppressWarnings("deprecation")
public class MainActivity extends Activity implements SensorEventListener, SurfaceHolder.Callback {

    private SensorManager sensorManager;
    private Sensor rotSensor, accelSensor, magSensor, pressureSensor, lightSensor;
    private boolean hasRotVec = false, hasBaro = false, hasAcc = false, hasMag = false;
    private final float[] lastAcc = {0f, 0f, 9.81f}, lastMag = {0f, 1f, 0f};
    private final float[] rotMat = new float[9], remapMat = new float[9], orient = new float[3];

    private LocationManager locationManager;
    private final LocationListener locListener = new LocationListener() {
        @Override public void onLocationChanged(Location l) { onNewLocation(l); }
        @Override public void onStatusChanged(String p, int s, Bundle e) {}
        @Override public void onProviderEnabled(String p) {}
        @Override public void onProviderDisabled(String p) {}
    };

    private SurfaceView cameraSurface;
    private Camera camera;
    private AROverlayView overlayView;
    private Button btnModeToggle;
    private TextView timeLabelView;
    private SeekBar timeSeekBar;

    private double latitude = 54.6195, longitude = 39.7420, lastOsmLat = 0.0, lastOsmLon = 0.0;
    private float gpsAcc = 0f, lastGpsAltASL = 0f;
    private boolean gpsLocked = false, realOsmLoaded = false;
    private volatile boolean pendingOsmReload = false;

    private float camAzimuth = 0f, camAltitude = 0f, camRoll = 0f;
    private float rawPitch = 0f, rawRoll = 0f, tarePitch = 0f, tareRoll = 0f;

    private float currentPressure = 1013.25f, autoGroundPressure = -1f, autoGroundElevationASL = -1f;
    private float manualRefPressure = -1f, manualRefHeight = 0f, floorHeightMeters = 3.0f, relativeHeightMeters = 0f;
    private boolean isManualHeightMode = false;
    private final AtomicBoolean isFetchingMeteo = new AtomicBoolean(false);

    private float currentLux = 0f, externalLuxForKeo = -1f, keoWin = -1f, keoCen = -1f, keoBack = -1f, lastKeo = -1f;
    private boolean showKeoHeatmap = false;

    private int tapeMode = 0;
    private Float tapeAz1 = null, tapeAlt1 = null, tapeAz2 = null, tapeAlt2 = null;
    private float tapeWallDist = 2.50f, tapeEyeHeight = 1.60f;

    private final List<float[]> customPoly = new ArrayList<>();
    private float customProjHeight = 24.0f;
    private boolean isLightTheme = false, isLiveTime = true, is2DMapMode = false;
    private int selectedDay = 80;
    private String seasonLabel = "Сегодня";
    private double targetHour = 12.0, dispHour = 12.0;
    private float mapScale = 2.2f;

    private static class OsmBuilding {
        float[] xMeters, yMeters;
        float heightMeters;
        int levels;
        String houseNumber;
        boolean isCustom;
    }

    private final List<OsmBuilding> osmBuildings = new ArrayList<>();
    private String rawOsmCache = null, osmStatus = "Ожидание GPS...";
    private final AtomicBoolean isFetchingOsm = new AtomicBoolean(false);

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        selectedDay = Calendar.getInstance().get(Calendar.DAY_OF_YEAR);
        seasonLabel = "День #" + selectedDay;
        loadSavedState();

        FrameLayout root = new FrameLayout(this);
        cameraSurface = new SurfaceView(this);
        cameraSurface.getHolder().addCallback(this);
        root.addView(cameraSurface);

        overlayView = new AROverlayView(this);
        overlayView.setOnTouchListener((v, ev) -> {
            if (ev.getAction() != MotionEvent.ACTION_DOWN) return false;
            float tx = ev.getX(), ty = ev.getY(), ui = v.getWidth() / 1080f;
            if (ty >= 120 * ui && ty <= 195 * ui) { showAltitudeDialog(); return true; }
            if (ty < 385 * ui) {
                startLocationUpdates();
                isFetchingOsm.set(false);
                fetchOsmBuildings(latitude, longitude);
                fetchAutoGroundMeteo(latitude, longitude);
                Toast.makeText(this, "Обновление GPS, рельефа и OSM...", Toast.LENGTH_SHORT).show();
                return true;
            }
            if (tapeMode > 0 && !is2DMapMode && ty >= v.getHeight() - 360 * ui && ty <= v.getHeight() - 190 * ui) {
                if (tx < v.getWidth() * 0.54f) triggerTapePoint();
                else if (tx < v.getWidth() * 0.81f) showTapeDialog();
                else { tapeMode = 0; tapeAz1 = tapeAlt1 = tapeAz2 = tapeAlt2 = null; }
                overlayView.invalidate();
                return true;
            }
            if (is2DMapMode) {
                float cx = v.getWidth() / 2f, cy = v.getHeight() * 0.56f, sc = mapScale * ui;
                float mx = (tx - cx) / sc, my = (cy - ty) / sc;
                synchronized (osmBuildings) {
                    for (OsmBuilding b : osmBuildings) {
                        if (isPointInPoly(mx, my, b.xMeters, b.yMeters)) { showEditBuildingDialog(b); return true; }
                    }
                }
                if (ty > 385 * ui && ty < v.getHeight() - 220 * ui) {
                    mapScale = (mapScale < 1.6f) ? 2.2f : (mapScale < 2.6f ? 3.6f : (mapScale < 4.2f ? 5.0f : 1.2f));
                    overlayView.invalidate();
                    return true;
                }
            }
            return false;
        });
        root.addView(overlayView);

        LinearLayout bottom = new LinearLayout(this);
        bottom.setOrientation(LinearLayout.VERTICAL);
        bottom.setBackgroundColor(Color.argb(215, 12, 18, 26));
        bottom.setPadding(10, 8, 10, 16);

        LinearLayout sRow = new LinearLayout(this);
        sRow.setGravity(Gravity.CENTER_VERTICAL);
        sRow.setPadding(10, 2, 10, 6);
        timeLabelView = new TextView(this);
        timeLabelView.setTextColor(Color.rgb(120, 255, 160));
        timeLabelView.setTextSize(12f);
        timeLabelView.setOnClickListener(v -> { isLiveTime = true; syncRealTime(); });
        sRow.addView(timeLabelView);

        timeSeekBar = new SeekBar(this);
        timeSeekBar.setMax(1439);
        LinearLayout.LayoutParams sp = new LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f);
        sp.setMargins(12, 0, 6, 0);
        timeSeekBar.setLayoutParams(sp);
        syncRealTime();
        dispHour = targetHour;
        timeSeekBar.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
            @Override public void onProgressChanged(SeekBar s, int p, boolean u) {
                if (u) {
                    isLiveTime = false;
                    targetHour = p / 60.0;
                    timeLabelView.setTextColor(Color.rgb(255, 225, 90));
                    timeLabelView.setText(String.format(Locale.US, "Ручн: %02d:%02d", p / 60, p % 60));
                    overlayView.invalidate();
                }
            }
            @Override public void onStartTrackingTouch(SeekBar s) { isLiveTime = false; }
            @Override public void onStopTrackingTouch(SeekBar s) {}
        });
        sRow.addView(timeSeekBar);
        bottom.addView(sRow);

        LinearLayout bar = new LinearLayout(this);
        bar.setGravity(Gravity.CENTER);
        btnModeToggle = mkBtn("2D План", Color.argb(230, 30, 115, 165), v -> {
            is2DMapMode = !is2DMapMode;
            btnModeToggle.setText(is2DMapMode ? "Камера AR" : "2D План");
            if (!is2DMapMode && cameraSurface.getHolder().getSurface().isValid()) startCameraPreview(cameraSurface.getHolder());
            if (!realOsmLoaded) fetchOsmBuildings(latitude, longitude);
            overlayView.invalidate();
        });
        bar.addView(btnModeToggle);
        bar.addView(mkBtn("Рулетка", Color.argb(230, 0, 140, 130), v -> {
            is2DMapMode = false;
            btnModeToggle.setText("2D План");
            if (tapeMode == 0) { tapeMode = 1; tapeAz1 = tapeAlt1 = tapeAz2 = tapeAlt2 = null; autoDetectWallDist(); }
            else showTapeDialog();
            overlayView.invalidate();
        }));
        bar.addView(mkBtn("Этаж/H", Color.argb(230, 65, 105, 175), v -> showAltitudeDialog()));
        bar.addView(mkBtn("КЕО", Color.argb(230, 155, 50, 175), v -> showKeoDialog()));
        bar.addView(mkBtn("Меню BIM", Color.argb(230, 40, 130, 95), v -> showToolsMenu()));
        bar.addView(mkBtn("Акт PDF", Color.argb(230, 185, 55, 45), v -> generatePdfReport()));
        bottom.addView(bar);

        root.addView(bottom, new FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.WRAP_CONTENT, Gravity.BOTTOM));
        setContentView(root);

        sensorManager = (SensorManager) getSystemService(Context.SENSOR_SERVICE);
        if (sensorManager != null) {
            rotSensor = sensorManager.getDefaultSensor(Sensor.TYPE_ROTATION_VECTOR);
            if (rotSensor == null) rotSensor = sensorManager.getDefaultSensor(Sensor.TYPE_GEOMAGNETIC_ROTATION_VECTOR);
            hasRotVec = (rotSensor != null);
            accelSensor = sensorManager.getDefaultSensor(Sensor.TYPE_ACCELEROMETER);
            magSensor = sensorManager.getDefaultSensor(Sensor.TYPE_MAGNETIC_FIELD);
            pressureSensor = sensorManager.getDefaultSensor(Sensor.TYPE_PRESSURE);
            hasBaro = (pressureSensor != null);
            lightSensor = sensorManager.getDefaultSensor(Sensor.TYPE_LIGHT);
        }
        locationManager = (LocationManager) getSystemService(Context.LOCATION_SERVICE);
        requestPerms();
        fetchAutoGroundMeteo(latitude, longitude);
    }

    private Button mkBtn(String txt, int col, View.OnClickListener l) {
        Button b = new Button(this);
        b.setText(txt); b.setTextSize(9.5f); b.setTextColor(Color.WHITE); b.setBackgroundColor(col);
        b.setPadding(2, 10, 2, 10); b.setOnClickListener(l);
        LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f);
        lp.setMargins(2, 0, 2, 0); b.setLayoutParams(lp);
        return b;
    }

    private void syncRealTime() {
        Calendar c = Calendar.getInstance();
        int h = c.get(Calendar.HOUR_OF_DAY), m = c.get(Calendar.MINUTE), s = c.get(Calendar.SECOND);
        targetHour = h + m / 60.0 + s / 3600.0;
        if (timeSeekBar != null) timeSeekBar.setProgress(h * 60 + m);
        if (timeLabelView != null) {
            timeLabelView.setTextColor(isLightTheme ? Color.rgb(0, 120, 60) : Color.rgb(120, 255, 160));
            timeLabelView.setText(String.format(Locale.US, "Сейчас: %02d:%02d:%02d", h, m, s));
        }
    }

    private void fetchAutoGroundMeteo(final double lat, final double lon) {
        if (!isFetchingMeteo.compareAndSet(false, true)) return;
        new Thread(() -> {
            HttpURLConnection c = null;
            try {
                URL u = new URL(String.format(Locale.US, "https://api.open-meteo.com/v1/forecast?latitude=%.5f&longitude=%.5f&current=surface_pressure", lat, lon));
                c = (HttpURLConnection) u.openConnection();
                c.setConnectTimeout(6000); c.setReadTimeout(6000);
                if (c.getResponseCode() == 200) {
                    BufferedReader br = new BufferedReader(new InputStreamReader(c.getInputStream(), StandardCharsets.UTF_8));
                    StringBuilder sb = new StringBuilder(); String l;
                    while ((l = br.readLine()) != null) sb.append(l);
                    br.close();
                    JSONObject r = new JSONObject(sb.toString());
                    if (r.has("elevation")) autoGroundElevationASL = (float) r.getDouble("elevation");
                    JSONObject cur = r.optJSONObject("current");
                    if (cur != null && cur.has("surface_pressure")) autoGroundPressure = (float) cur.getDouble("surface_pressure");
                    recalcHeight();
                    if (overlayView != null) overlayView.postInvalidate();
                }
            } catch (Exception ignored) {} finally {
                if (c != null) c.disconnect();
                isFetchingMeteo.set(false);
            }
        }).start();
    }

    private void recalcHeight() {
        if (isManualHeightMode) {
            relativeHeightMeters = (hasBaro && manualRefPressure > 0)
                    ? manualRefHeight + 44330f * (1f - (float) Math.pow(currentPressure / manualRefPressure, 0.190295f))
                    : manualRefHeight;
        } else if (hasBaro && autoGroundPressure > 0) {
            relativeHeightMeters = Math.max(0f, 44330f * (1f - (float) Math.pow(currentPressure / autoGroundPressure, 0.190295f)));
        } else if (lastGpsAltASL != 0f && autoGroundElevationASL > 0f) {
            relativeHeightMeters = Math.max(0f, lastGpsAltASL - autoGroundElevationASL);
        } else if (hasBaro && manualRefPressure > 0) {
            relativeHeightMeters = Math.max(0f, 44330f * (1f - (float) Math.pow(currentPressure / manualRefPressure, 0.190295f)));
        }
    }

    private void showAltitudeDialog() {
        LinearLayout lay = new LinearLayout(this);
        lay.setOrientation(LinearLayout.VERTICAL); lay.setPadding(45, 20, 45, 10);
        int curFl = Math.max(1, Math.round(relativeHeightMeters / floorHeightMeters) + 1);
        final EditText inFl = new EditText(this);
        inFl.setInputType(InputType.TYPE_CLASS_NUMBER | InputType.TYPE_NUMBER_FLAG_SIGNED);
        inFl.setText(String.valueOf(curFl));
        final EditText inSt = new EditText(this);
        inSt.setInputType(InputType.TYPE_CLASS_NUMBER | InputType.TYPE_NUMBER_FLAG_DECIMAL);
        inSt.setText(String.format(Locale.US, "%.1f", floorHeightMeters));

        LinearLayout qRow = new LinearLayout(this);
        LinearLayout.LayoutParams qp = new LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f);
        Button bM = new Button(this); bM.setText("-1 эт");
        bM.setOnClickListener(v -> { try { inFl.setText(String.valueOf(Math.max(1, Integer.parseInt(inFl.getText().toString().trim()) - 1))); } catch (Exception ignored) {} });
        Button b0 = new Button(this); b0.setText("1 эт (0м)"); b0.setOnClickListener(v -> inFl.setText("1"));
        Button bP = new Button(this); bP.setText("+1 эт");
        bP.setOnClickListener(v -> { try { inFl.setText(String.valueOf(Integer.parseInt(inFl.getText().toString().trim()) + 1)); } catch (Exception ignored) {} });
        qRow.addView(bM, qp); qRow.addView(b0, qp); qRow.addView(bP, qp);
        lay.addView(qRow);
        TextView t1 = new TextView(this); t1.setText("Текущий этаж:"); lay.addView(t1); lay.addView(inFl);
        TextView t2 = new TextView(this); t2.setText("Высота этажа (м):"); lay.addView(t2); lay.addView(inSt);

        new AlertDialog.Builder(this)
                .setTitle("Отметка H и Этаж (" + (isManualHeightMode ? "РУЧН" : "АВТО") + ")")
                .setView(lay)
                .setPositiveButton("Применить", (d, w) -> {
                    try {
                        int fl = Integer.parseInt(inFl.getText().toString().trim());
                        float st = Float.parseFloat(inSt.getText().toString().trim().replace(",", "."));
                        if (st >= 1.5f && st <= 10f) floorHeightMeters = st;
                        isManualHeightMode = true; manualRefPressure = currentPressure; manualRefHeight = (fl - 1) * floorHeightMeters;
                        recalcHeight(); overlayView.invalidate();
                    } catch (Exception ignored) {}
                })
                .setNeutralButton("Режим АВТО", (d, w) -> {
                    isManualHeightMode = false; fetchAutoGroundMeteo(latitude, longitude); recalcHeight(); overlayView.invalidate();
                })
                .setNegativeButton("Отмена", null).show();
    }

    private void triggerTapePoint() {
        if (tapeAz1 == null || tapeAz2 != null) {
            tapeAz1 = camAzimuth; tapeAlt1 = camAltitude; tapeAz2 = tapeAlt2 = null;
            if (tapeMode == 1) autoDetectWallDist();
        } else {
            tapeAz2 = camAzimuth; tapeAlt2 = camAltitude;
        }
    }

    private void autoDetectWallDist() {
        float rx = (float) Math.sin(Math.toRadians(camAzimuth)), ry = (float) Math.cos(Math.toRadians(camAzimuth)), best = -1f;
        synchronized (osmBuildings) {
            for (OsmBuilding b : osmBuildings) {
                for (int i = 0; i < b.xMeters.length; i++) {
                    float d = intersectRay(rx, ry, b.xMeters[i], b.yMeters[i], b.xMeters[(i + 1) % b.xMeters.length], b.yMeters[(i + 1) % b.xMeters.length]);
                    if (d > 1.0f && d < 100f && (best < 0 || d < best)) best = d;
                }
            }
        }
        if (best > 1.2f && best < 50f) tapeWallDist = best;
    }

    private float[] calcTape(float az1, float alt1, float az2, float alt2) {
        float dAz = Math.abs(az2 - az1); if (dAz > 180f) dAz = 360f - dAz;
        double dAzR = Math.toRadians(dAz), a1R = Math.toRadians(alt1), a2R = Math.toRadians(alt2);
        if (tapeMode == 2) {
            float d = (float) (tapeEyeHeight / Math.tan(Math.max(Math.toRadians(2.0), Math.abs(a1R))));
            float dH = (float) Math.abs(d * (Math.tan(a2R) - Math.tan(a1R))), dW = (float) (2.0 * d * Math.tan(dAzR / 2.0));
            return new float[]{(float) Math.hypot(dH, dW), dH, dW, d, dH * dW};
        } else if (tapeMode == 3) {
            float d1 = (float) (tapeEyeHeight / Math.tan(Math.max(Math.toRadians(2.0), Math.abs(a1R))));
            float d2 = (float) (tapeEyeHeight / Math.tan(Math.max(Math.toRadians(2.0), Math.abs(a2R))));
            float len = (float) Math.sqrt(Math.max(0.0, d1 * d1 + d2 * d2 - 2.0 * d1 * d2 * Math.cos(dAzR)));
            return new float[]{len, 0f, len, d1, 0f};
        } else {
            float d = Math.max(0.3f, tapeWallDist);
            float dW = (float) (2.0 * d * Math.tan(dAzR / 2.0)), dH = (float) Math.abs(d * (Math.tan(a2R) - Math.tan(a1R)));
            return new float[]{(float) Math.hypot(dW, dH), dH, dW, d, dW * dH};
        }
    }

    private void showTapeDialog() {
        LinearLayout lay = new LinearLayout(this);
        lay.setOrientation(LinearLayout.VERTICAL); lay.setPadding(45, 15, 45, 10);
        final EditText inD = new EditText(this);
        inD.setInputType(InputType.TYPE_CLASS_NUMBER | InputType.TYPE_NUMBER_FLAG_DECIMAL);
        inD.setText(String.format(Locale.US, "%.2f", tapeWallDist));
        TextView t = new TextView(this); t.setText("Дистанция до стены/окна D (м):");
        lay.addView(t); lay.addView(inD);
        String[] modes = {"1. Стена/Окно (на дист. D)", "2. От пола вверх (Авто-D)", "3. По полу 3D (Горизонт)"};
        new AlertDialog.Builder(this).setTitle("3D AR-Рулетка").setView(lay)
                .setSingleChoiceItems(modes, Math.max(0, tapeMode - 1), (d, w) -> tapeMode = w + 1)
                .setPositiveButton("ОК", (d, w) -> {
                    try { tapeWallDist = Float.parseFloat(inD.getText().toString().trim().replace(",", ".")); } catch (Exception ignored) {}
                    if (tapeMode == 0) tapeMode = 1;
                    overlayView.invalidate();
                })
                .setNeutralButton("Авто-луч OSM", (d, w) -> { autoDetectWallDist(); overlayView.invalidate(); })
                .setNegativeButton("Выкл", (d, w) -> { tapeMode = 0; overlayView.invalidate(); }).show();
    }

    private void loadSavedState() {
        try {
            SharedPreferences p = getSharedPreferences("osm_cache_v8", MODE_PRIVATE);
            if (p.contains("lat")) {
                latitude = Double.longBitsToDouble(p.getLong("lat", Double.doubleToRawLongBits(latitude)));
                longitude = Double.longBitsToDouble(p.getLong("lon", Double.doubleToRawLongBits(longitude)));
            }
            String j = p.getString("json", null);
            if (j != null) {
                rawOsmCache = j;
                int c = parseOsmJson(j, latitude, longitude);
                if (c > 0) { realOsmLoaded = true; lastOsmLat = latitude; lastOsmLon = longitude; osmStatus = "OSM (кэш): " + c + " домов"; }
            }
        } catch (Exception ignored) {}
    }

    private void fetchOsmBuildings(final double lat, final double lon) {
        if (!isFetchingOsm.compareAndSet(false, true)) { pendingOsmReload = true; return; }
        pendingOsmReload = false; osmStatus = "Загрузка OSM...";
        if (overlayView != null) overlayView.postInvalidate();

        new Thread(() -> {
            double s = lat - 0.0028, n = lat + 0.0028, w = lon - 0.0045, e = lon + 0.0045;
            String q = String.format(Locale.US, "[out:json][timeout:18];(way[\"building\"](%.5f,%.5f,%.5f,%.5f);relation[\"building\"](%.5f,%.5f,%.5f,%.5f););out geom;", s, w, n, e, s, w, n, e);
            String[] eps = {"https://overpass.private.coffee/api/interpreter", "https://maps.mail.ru/osm/tools/overpass/api/interpreter", "https://overpass-api.de/api/interpreter"};
            boolean ok = false; int cnt = 0;
            for (String ep : eps) {
                HttpURLConnection c = null;
                try {
                    c = (HttpURLConnection) new URL(ep + "?data=" + URLEncoder.encode(q, "UTF-8")).openConnection();
                    c.setConnectTimeout(7000); c.setReadTimeout(10000);
                    c.setRequestProperty("User-Agent", "BIMSunLevel/3.2"); c.setRequestProperty("Accept", "*/*");
                    if (c.getResponseCode() == 200) {
                        BufferedReader br = new BufferedReader(new InputStreamReader(c.getInputStream(), StandardCharsets.UTF_8));
                        StringBuilder sb = new StringBuilder(); String l;
                        while ((l = br.readLine()) != null) sb.append(l);
                        br.close();
                        rawOsmCache = sb.toString();
                        cnt = parseOsmJson(rawOsmCache, latitude, longitude);
                        lastOsmLat = lat; lastOsmLon = lon; realOsmLoaded = true; ok = true;
                        getSharedPreferences("osm_cache_v8", MODE_PRIVATE).edit().putString("json", rawOsmCache)
                                .putLong("lat", Double.doubleToRawLongBits(lat)).putLong("lon", Double.doubleToRawLongBits(lon)).apply();
                        break;
                    }
                } catch (Exception ignored) {} finally { if (c != null) c.disconnect(); }
            }
            isFetchingOsm.set(false);
            if (pendingOsmReload) { fetchOsmBuildings(latitude, longitude); return; }
            final boolean fOk = ok; final int fCnt = cnt;
            runOnUiThread(() -> {
                osmStatus = fOk ? ("Карта OSM: " + fCnt + " домов") : "Сеть OSM — тапните сверху";
                if (overlayView != null) overlayView.invalidate();
            });
        }).start();
    }

    private int parseOsmJson(String json, double cLat, double cLon) throws Exception {
        JSONArray els = new JSONObject(json).optJSONArray("elements");
        if (els == null) return 0;
        double mLat = 111132.0, mLon = 111320.0 * Math.cos(Math.toRadians(cLat));
        List<OsmBuilding> list = new ArrayList<>();
        for (int i = 0; i < els.length(); i++) {
            JSONObject el = els.getJSONObject(i);
            int lv = 5; float h = -1f; String num = "";
            JSONObject t = el.optJSONObject("tags");
            if (t != null) {
                num = t.optString("addr:housenumber", "").trim();
                String ls = t.optString("building:levels", "").replaceAll("[^0-9]", "");
                if (!ls.isEmpty()) try { lv = Integer.parseInt(ls); } catch (Exception ignored) {}
                String hs = t.optString("height", "").replace(",", ".").replaceAll("[^0-9.]", "");
                if (!hs.isEmpty()) try { h = Float.parseFloat(hs); } catch (Exception ignored) {}
            }
            if (h <= 2f) h = lv * 3.0f;
            JSONArray g = el.optJSONArray("geometry");
            if (g != null && g.length() >= 3) list.add(mkGeomBld(g, cLat, cLon, mLat, mLon, lv, h, num));
            JSONArray mem = el.optJSONArray("members");
            if (mem != null) {
                for (int m = 0; m < mem.length(); m++) {
                    JSONObject mo = mem.getJSONObject(m);
                    JSONArray mg = mo.optJSONArray("geometry");
                    if ("outer".equals(mo.optString("role", "outer")) && mg != null && mg.length() >= 3)
                        list.add(mkGeomBld(mg, cLat, cLon, mLat, mLon, lv, h, num));
                }
            }
        }
        synchronized (osmBuildings) {
            osmBuildings.clear(); osmBuildings.addAll(list);
            if (customPoly.size() >= 3) {
                OsmBuilding p = new OsmBuilding();
                p.xMeters = new float[customPoly.size()]; p.yMeters = new float[customPoly.size()];
                for (int i = 0; i < customPoly.size(); i++) { p.xMeters[i] = customPoly.get(i)[0]; p.yMeters[i] = customPoly.get(i)[1]; }
                p.heightMeters = customProjHeight; p.levels = Math.round(customProjHeight / 3f); p.houseNumber = "ПРОЕКТ"; p.isCustom = true;
                osmBuildings.add(p);
            }
        }
        return list.size();
    }

    private OsmBuilding mkGeomBld(JSONArray g, double cLat, double cLon, double mLat, double mLon, int lv, float h, String num) throws Exception {
        OsmBuilding b = new OsmBuilding();
        b.xMeters = new float[g.length()]; b.yMeters = new float[g.length()];
        for (int j = 0; j < g.length(); j++) {
            JSONObject pt = g.getJSONObject(j);
            b.xMeters[j] = (float) ((pt.getDouble("lon") - cLon) * mLon);
            b.yMeters[j] = (float) ((pt.getDouble("lat") - cLat) * mLat);
        }
        b.levels = lv; b.heightMeters = h; b.houseNumber = num;
        return b;
    }

    private void showToolsMenu() {
        CharSequence[] items = {"1. Поиск адреса или ввод координат", "2. Импорт контура (.dxf / .ifc / .txt)",
                "3. Тара уклономера (0.0°)", "4. Смена темы (Темная / Дневная)", "5. Смена сезона", "6. Фото AR в Галерею", "7. Экспорт в CSV"};
        new AlertDialog.Builder(this).setTitle("BIM Инструменты").setItems(items, (d, w) -> {
            if (w == 0) showLocDialog();
            else if (w == 1) {
                Intent i = new Intent(Intent.ACTION_GET_CONTENT); i.setType("*/*"); i.addCategory(Intent.CATEGORY_OPENABLE);
                startActivityForResult(Intent.createChooser(i, "Файл DXF/IFC/TXT"), 202);
            } else if (w == 2) { tarePitch = rawPitch; tareRoll = rawRoll; }
            else if (w == 3) { isLightTheme = !isLightTheme; overlayView.invalidate(); }
            else if (w == 4) {
                selectedDay = (selectedDay == 80) ? 172 : (selectedDay == 172 ? 355 : (selectedDay == 355 ? Calendar.getInstance().get(Calendar.DAY_OF_YEAR) : 80));
                seasonLabel = (selectedDay == 80) ? "21 Мар/Сен" : (selectedDay == 172 ? "21 Июня" : (selectedDay == 355 ? "21 Декабря" : "Сегодня"));
                overlayView.invalidate();
            } else if (w == 5) captureARPhoto();
            else if (w == 6) exportCsv();
        }).show();
    }

    private void showLocDialog() {
        final EditText in = new EditText(this);
        in.setHint("Город, улица, дом ИЛИ широта, долгота");
        new AlertDialog.Builder(this).setTitle("Поиск адреса / Координаты").setView(in)
                .setPositiveButton("Найти", (d, w) -> {
                    final String q = in.getText().toString().trim();
                    if (q.matches(".*[0-9]+\\.[0-9]+.*[,;\\s]+.*[0-9]+\\.[0-9]+.*")) {
                        String[] p = q.split("[,;\\s]+");
                        Location l = new Location("manual"); l.setLatitude(Double.parseDouble(p[0])); l.setLongitude(Double.parseDouble(p[1]));
                        onNewLocation(l);
                    } else {
                        new Thread(() -> {
                            try {
                                HttpURLConnection c = (HttpURLConnection) new URL("https://nominatim.openstreetmap.org/search?format=json&limit=1&q=" + URLEncoder.encode(q, "UTF-8")).openConnection();
                                c.setRequestProperty("User-Agent", "BIMSunLevel/3.2");
                                BufferedReader br = new BufferedReader(new InputStreamReader(c.getInputStream()));
                                JSONArray a = new JSONArray(br.readLine()); br.close();
                                if (a.length() > 0) {
                                    JSONObject o = a.getJSONObject(0);
                                    Location l = new Location("nom"); l.setLatitude(o.getDouble("lat")); l.setLongitude(o.getDouble("lon"));
                                    runOnUiThread(() -> onNewLocation(l));
                                }
                            } catch (Exception ignored) {}
                        }).start();
                    }
                }).setNegativeButton("Авто-GPS", (d, w) -> startLocationUpdates()).show();
    }

    @Override
    protected void onActivityResult(int req, int res, Intent data) {
        if (req == 202 && res == RESULT_OK && data != null && data.getData() != null) {
            try {
                BufferedReader br = new BufferedReader(new InputStreamReader(getContentResolver().openInputStream(data.getData())));
                List<String> lines = new ArrayList<>(); String l;
                while ((l = br.readLine()) != null) lines.add(l.trim());
                br.close();
                List<float[]> pts = new ArrayList<>();
                Float lx = null;
                for (int i = 0; i < lines.size(); i++) {
                    String s = lines.get(i).toUpperCase(Locale.US);
                    if (s.contains("IFCCARTESIANPOINT((")) {
                        String[] c = s.substring(s.indexOf("((") + 2, s.indexOf("))")).split(",");
                        if (c.length >= 2) pts.add(new float[]{Float.parseFloat(c[0].trim()), Float.parseFloat(c[1].trim())});
                    } else if ("10".equals(s) && i + 1 < lines.size()) {
                        try { lx = Float.parseFloat(lines.get(++i)); } catch (Exception ignored) {}
                    } else if ("20".equals(s) && lx != null && i + 1 < lines.size()) {
                        try { pts.add(new float[]{lx, Float.parseFloat(lines.get(++i))}); lx = null; } catch (Exception ignored) {}
                    }
                }
                if (pts.size() >= 3) {
                    customPoly.clear(); customPoly.addAll(pts);
                    if (rawOsmCache != null) parseOsmJson(rawOsmCache, latitude, longitude);
                    is2DMapMode = true; btnModeToggle.setText("Камера AR"); overlayView.invalidate();
                }
            } catch (Exception ignored) {}
        }
    }

    private void showKeoDialog() {
        CharSequence[] a = {"1. Запомнить улицу E_нар (" + Math.round(currentLux) + " лк)", "2. Точка: У ОКНА",
                "3. Точка: ЦЕНТР", "4. Точка: УГОЛ", showKeoHeatmap ? "5. Скрыть карту КЕО" : "5. Показать тепловую карту КЕО"};
        new AlertDialog.Builder(this).setTitle("КЕО СП 52.13330").setItems(a, (d, w) -> {
            if (w == 0) externalLuxForKeo = Math.max(1f, currentLux);
            else if (w == 1) keoWin = Math.max(1f, currentLux);
            else if (w == 2) keoCen = Math.max(1f, currentLux);
            else if (w == 3) keoBack = Math.max(1f, currentLux);
            else if (w == 4) showKeoHeatmap = !showKeoHeatmap;
            if (externalLuxForKeo > 0) lastKeo = ((keoCen > 0 ? keoCen : currentLux) / externalLuxForKeo) * 100f;
            overlayView.invalidate();
        }).show();
    }

    private OutputStream openDownloadStream(String name, String mime) throws Exception {
        if (Build.VERSION.SDK_INT >= 29) {
            ContentValues cv = new ContentValues();
            cv.put(MediaStore.Downloads.DISPLAY_NAME, name); cv.put(MediaStore.Downloads.MIME_TYPE, mime);
            cv.put(MediaStore.Downloads.RELATIVE_PATH, Environment.DIRECTORY_DOWNLOADS + "/BIM_Reports");
            Uri u = getContentResolver().insert(MediaStore.Downloads.EXTERNAL_CONTENT_URI, cv);
            if (u != null) return getContentResolver().openOutputStream(u);
        }
        File dir = new File(Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DOWNLOADS), "BIM_Reports");
        if (!dir.exists()) dir.mkdirs();
        return new FileOutputStream(new File(dir, name));
    }

    private void generatePdfReport() {
        try {
            String name = "BIM_Act_" + System.currentTimeMillis() + ".pdf";
            PdfDocument pdf = new PdfDocument();
            PdfDocument.Page page = pdf.startPage(new PdfDocument.PageInfo.Builder(595, 842, 1).create());
            Canvas c = page.getCanvas(); Paint p = new Paint(Paint.ANTI_ALIAS_FLAG);
            p.setTextSize(15f); c.drawText("АКТ СТРОЙКОНТРОЛЯ И ИНСОЛЯЦИИ (BIM Sun & Level)", 40, 45, p);
            p.setTextSize(11f);
            float[] ins = calcInsolation(latitude, selectedDay);
            int fl = Math.max(1, Math.round(relativeHeightMeters / floorHeightMeters) + 1);
            c.drawText(String.format(Locale.US, "GPS: %.5f N, %.5f E | Отметка H: %+.2f м (~%d эт.)", latitude, longitude, relativeHeightMeters, fl), 40, 75, p);
            c.drawText(String.format(Locale.US, "Уклон: %.2f° | Свет: %.0f лк | КЕО: %.2f%% | СанПиН: %.1f ч (%s)",
                    rawPitch - tarePitch, currentLux, Math.max(0f, lastKeo), ins[1], ins[1] >= 2f ? "НОРМА" : "НАРУШЕНИЕ"), 40, 98, p);
            Bitmap bmp = Bitmap.createBitmap(overlayView.getWidth(), overlayView.getHeight(), Bitmap.Config.ARGB_8888);
            Canvas sc = new Canvas(bmp); sc.drawColor(Color.rgb(16, 24, 36)); overlayView.draw(sc);
            c.drawBitmap(bmp, null, new Rect(40, 120, 555, 800), null); bmp.recycle();
            pdf.finishPage(page);
            OutputStream os = openDownloadStream(name, "application/pdf");
            pdf.writeTo(os); os.close(); pdf.close();
            Toast.makeText(this, "PDF сохранен: Download/BIM_Reports/" + name, Toast.LENGTH_LONG).show();
        } catch (Exception e) { Toast.makeText(this, "Ошибка PDF: " + e.getMessage(), Toast.LENGTH_SHORT).show(); }
    }

    private void exportCsv() {
        try {
            String name = "BIM_Log_" + System.currentTimeMillis() + ".csv";
            OutputStream os = openDownloadStream(name, "text/csv");
            int fl = Math.max(1, Math.round(relativeHeightMeters / floorHeightMeters) + 1);
            String row = String.format(Locale.US, "Lat,Lon,Azimuth,Slope_deg,Lux,KEO,Height_m,Floor\n%.5f,%.5f,%.1f,%.2f,%.0f,%.2f,%.2f,%d\n",
                    latitude, longitude, camAzimuth, rawPitch - tarePitch, currentLux, lastKeo, relativeHeightMeters, fl);
            os.write(row.getBytes(StandardCharsets.UTF_8)); os.close();
            Toast.makeText(this, "CSV сохранен: " + name, Toast.LENGTH_LONG).show();
        } catch (Exception ignored) {}
    }

    private void showEditBuildingDialog(OsmBuilding b) {
        final EditText in = new EditText(this); in.setInputType(InputType.TYPE_CLASS_NUMBER); in.setText(String.valueOf(b.levels));
        new AlertDialog.Builder(this).setTitle("Этажность дома " + b.houseNumber).setView(in)
                .setPositiveButton("ОК", (d, w) -> {
                    try { b.levels = Integer.parseInt(in.getText().toString().trim()); b.heightMeters = b.levels * 3f; overlayView.invalidate(); } catch (Exception ignored) {}
                }).show();
    }

    private double[] computeSun(double lat, int day, double hr) {
        double tz = TimeZone.getDefault().getOffset(System.currentTimeMillis()) / 3600000.0;
        double b = Math.toRadians((360.0 / 365.0) * (day - 81));
        double eot = 9.87 * Math.sin(2 * b) - 7.53 * Math.cos(b) - 1.5 * Math.sin(b);
        double sh = hr + (4.0 * (longitude - 15.0 * tz) + eot) / 60.0;
        double lR = Math.toRadians(lat), dR = Math.toRadians(23.45 * Math.sin(Math.toRadians((360.0 / 365.0) * (284 + day))));
        double hR = Math.toRadians(15.0 * (sh - 12.0));
        double aR = Math.asin(Math.max(-1.0, Math.min(1.0, Math.sin(lR) * Math.sin(dR) + Math.cos(lR) * Math.cos(dR) * Math.cos(hR))));
        double cAz = Math.max(-1.0, Math.min(1.0, (Math.sin(dR) - Math.sin(aR) * Math.sin(lR)) / (Math.cos(aR) * Math.cos(lR) + 1e-6)));
        double az = Math.toDegrees(Math.acos(cAz));
        if (((sh % 24.0) + 24.0) % 24.0 > 12.0) az = 360.0 - az;
        return new double[]{az, Math.toDegrees(aR)};
    }

    private boolean doesBlock(OsmBuilding b, double az, double alt) {
        if (alt <= 0.5) return false;
        float dh = b.heightMeters - relativeHeightMeters;
        if (dh <= 0.5f || isPointInPoly(0f, 0f, b.xMeters, b.yMeters)) return false;
        float maxD = (float) (dh / Math.tan(Math.toRadians(Math.max(0.5, alt))));
        float dx = (float) Math.sin(Math.toRadians(az)), dy = (float) Math.cos(Math.toRadians(az));
        for (int i = 0; i < b.xMeters.length; i++) {
            float d = intersectRay(dx, dy, b.xMeters[i], b.yMeters[i], b.xMeters[(i + 1) % b.xMeters.length], b.yMeters[(i + 1) % b.xMeters.length]);
            if (d > 2.0f && d <= maxD) return true;
        }
        return false;
    }

    private boolean isSunBlocked(double az, double alt) {
        if (alt <= 0) return true;
        synchronized (osmBuildings) { for (OsmBuilding b : osmBuildings) if (doesBlock(b, az, alt)) return true; }
        return false;
    }

    private float[] calcInsolation(double lat, int day) {
        float a = 0f, u = 0f;
        for (double h = 4.0; h <= 22.0; h += 0.25) {
            double[] p = computeSun(lat, day, h);
            if (p[1] > 0) { a += 0.25f; if (!isSunBlocked(p[0], p[1])) u += 0.25f; }
        }
        return new float[]{a, u};
    }

    private boolean isPointInPoly(float px, float py, float[] vx, float[] vy) {
        boolean in = false;
        for (int i = 0, j = vx.length - 1; i < vx.length; j = i++)
            if (((vy[i] > py) != (vy[j] > py)) && (px < (vx[j] - vx[i]) * (py - vy[i]) / (vy[j] - vy[i] + 1e-6f) + vx[i])) in = !in;
        return in;
    }

    private float intersectRay(float dx, float dy, float x1, float y1, float x2, float y2) {
        float sx = x2 - x1, sy = y2 - y1, det = -dx * sy + dy * sx;
        if (Math.abs(det) < 1e-5f) return -1f;
        float t = (-sy * (-x1) + sx * (-y1)) / det, u = (dx * (-y1) - dy * (-x1)) / det;
        return (t >= 0f && u >= 0f && u <= 1f) ? t : -1f;
    }

    private void captureARPhoto() {
        int w = overlayView.getWidth(), h = overlayView.getHeight();
        if (w <= 0 || h <= 0) return;
        if (!is2DMapMode && camera != null) {
            try {
                camera.setOneShotPreviewCallback((data, cam) -> {
                    try {
                        Camera.Size s = cam.getParameters().getPreviewSize();
                        YuvImage yuv = new YuvImage(data, ImageFormat.NV21, s.width, s.height, null);
                        ByteArrayOutputStream baos = new ByteArrayOutputStream();
                        yuv.compressToJpeg(new Rect(0, 0, s.width, s.height), 92, baos);
                        Bitmap raw = BitmapFactory.decodeByteArray(baos.toByteArray(), 0, baos.size());
                        Matrix m = new Matrix(); m.postRotate(90);
                        Bitmap rot = Bitmap.createBitmap(raw, 0, 0, raw.getWidth(), raw.getHeight(), m, true);
                        raw.recycle();
                        savePhotoBmp(rot, w, h);
                    } catch (Exception e) { savePhotoBmp(null, w, h); }
                });
                return;
            } catch (Exception ignored) {}
        }
        savePhotoBmp(null, w, h);
    }

    private void savePhotoBmp(Bitmap camBmp, int w, int h) {
        Bitmap b = Bitmap.createBitmap(w, h, Bitmap.Config.ARGB_8888);
        Canvas c = new Canvas(b);
        if (camBmp != null) { c.drawBitmap(camBmp, null, new Rect(0, 0, w, h), null); camBmp.recycle(); }
        else c.drawColor(Color.rgb(16, 24, 36));
        overlayView.draw(c);
        try {
            ContentValues cv = new ContentValues();
            cv.put(MediaStore.Images.Media.DISPLAY_NAME, "BIM_" + System.currentTimeMillis() + ".jpg");
            cv.put(MediaStore.Images.Media.MIME_TYPE, "image/jpeg");
            Uri u = getContentResolver().insert(MediaStore.Images.Media.EXTERNAL_CONTENT_URI, cv);
            if (u != null) { OutputStream os = getContentResolver().openOutputStream(u); b.compress(Bitmap.CompressFormat.JPEG, 92, os); os.close(); }
            Toast.makeText(this, "Сохранено в Галерею", Toast.LENGTH_SHORT).show();
        } catch (Exception ignored) {}
        b.recycle();
    }

    private void requestPerms() {
        if (checkSelfPermission(Manifest.permission.CAMERA) != PackageManager.PERMISSION_GRANTED ||
            checkSelfPermission(Manifest.permission.ACCESS_FINE_LOCATION) != PackageManager.PERMISSION_GRANTED) {
            requestPermissions(new String[]{Manifest.permission.CAMERA, Manifest.permission.ACCESS_FINE_LOCATION, Manifest.permission.ACCESS_COARSE_LOCATION}, 101);
        } else startLocationUpdates();
    }

    @Override public void onRequestPermissionsResult(int r, String[] p, int[] g) {
        startLocationUpdates();
        if (cameraSurface.getHolder().getSurface().isValid()) startCameraPreview(cameraSurface.getHolder());
    }

    private void startLocationUpdates() {
        if (locationManager == null) return;
        if (checkSelfPermission(Manifest.permission.ACCESS_FINE_LOCATION) != PackageManager.PERMISSION_GRANTED &&
            checkSelfPermission(Manifest.permission.ACCESS_COARSE_LOCATION) != PackageManager.PERMISSION_GRANTED) return;
        Location best = null;
        for (String p : new String[]{"fused", LocationManager.GPS_PROVIDER, LocationManager.NETWORK_PROVIDER, LocationManager.PASSIVE_PROVIDER}) {
            try {
                locationManager.requestLocationUpdates(p, 1500L, 0f, locListener);
                Location l = locationManager.getLastKnownLocation(p);
                if (l != null && (best == null || l.getTime() > best.getTime())) best = l;
            } catch (Exception ignored) {}
        }
        if (best != null) onNewLocation(best);
        else if (!realOsmLoaded) fetchOsmBuildings(latitude, longitude);
    }

    private void onNewLocation(Location l) {
        if (l == null || (Math.abs(l.getLatitude()) < 0.001 && Math.abs(l.getLongitude()) < 0.001)) return;
        double mvSq = Math.pow((l.getLatitude() - latitude) * 111132.0, 2) + Math.pow((l.getLongitude() - longitude) * 65000.0, 2);
        latitude = l.getLatitude(); longitude = l.getLongitude(); gpsAcc = l.getAccuracy();
        if (l.hasAltitude()) lastGpsAltASL = (float) l.getAltitude();
        gpsLocked = true;
        if (autoGroundPressure < 0 || mvSq > 2500.0) fetchAutoGroundMeteo(latitude, longitude);
        recalcHeight();
        double osmSq = Math.pow((latitude - lastOsmLat) * 111132.0, 2) + Math.pow((longitude - lastOsmLon) * 65000.0, 2);
        if (!realOsmLoaded || osmSq > 1600.0 || mvSq > 1600.0) fetchOsmBuildings(latitude, longitude);
        if (overlayView != null) overlayView.postInvalidate();
    }

    @Override protected void onResume() {
        super.onResume();
        if (sensorManager != null) {
            if (rotSensor != null) sensorManager.registerListener(this, rotSensor, SensorManager.SENSOR_DELAY_GAME);
            if (accelSensor != null) sensorManager.registerListener(this, accelSensor, SensorManager.SENSOR_DELAY_GAME);
            if (magSensor != null) sensorManager.registerListener(this, magSensor, SensorManager.SENSOR_DELAY_GAME);
            if (pressureSensor != null) sensorManager.registerListener(this, pressureSensor, SensorManager.SENSOR_DELAY_UI);
            if (lightSensor != null) sensorManager.registerListener(this, lightSensor, SensorManager.SENSOR_DELAY_UI);
        }
        startLocationUpdates();
    }

    @Override protected void onPause() {
        super.onPause();
        if (sensorManager != null) sensorManager.unregisterListener(this);
        if (locationManager != null) try { locationManager.removeUpdates(locListener); } catch (Exception ignored) {}
    }

    @Override public void onSensorChanged(SensorEvent e) {
        int t = e.sensor.getType();
        if (t == Sensor.TYPE_ROTATION_VECTOR || t == Sensor.TYPE_GEOMAGNETIC_ROTATION_VECTOR) {
            SensorManager.getRotationMatrixFromVector(rotMat, e.values); applyRot();
        } else if (t == Sensor.TYPE_ACCELEROMETER) {
            System.arraycopy(e.values, 0, lastAcc, 0, 3); hasAcc = true;
            rawPitch += 0.12f * ((float) Math.toDegrees(Math.atan2(e.values[1], Math.sqrt(e.values[0] * e.values[0] + e.values[2] * e.values[2]))) - rawPitch);
            rawRoll += 0.12f * ((float) Math.toDegrees(Math.atan2(-e.values[0], Math.sqrt(e.values[1] * e.values[1] + e.values[2] * e.values[2]))) - rawRoll);
            if (!hasRotVec && hasMag && SensorManager.getRotationMatrix(rotMat, null, lastAcc, lastMag)) applyRot();
        } else if (t == Sensor.TYPE_MAGNETIC_FIELD) {
            System.arraycopy(e.values, 0, lastMag, 0, 3); hasMag = true;
            if (!hasRotVec && hasAcc && SensorManager.getRotationMatrix(rotMat, null, lastAcc, lastMag)) applyRot();
        } else if (t == Sensor.TYPE_PRESSURE) {
            currentPressure = (manualRefPressure < 0) ? e.values[0] : (currentPressure + 0.15f * (e.values[0] - currentPressure));
            if (manualRefPressure < 0) manualRefPressure = currentPressure;
            recalcHeight();
        } else if (t == Sensor.TYPE_LIGHT) currentLux = e.values[0];
        if (isLiveTime) syncRealTime();
        dispHour += 0.22 * (targetHour - dispHour);
        if (overlayView != null) overlayView.invalidate();
    }

    private void applyRot() {
        SensorManager.remapCoordinateSystem(rotMat, SensorManager.AXIS_X, SensorManager.AXIS_Z, remapMat);
        SensorManager.getOrientation(remapMat, orient);
        float az = ((float) Math.toDegrees(orient[0]) + 360f) % 360f;
        float d = az - camAzimuth; if (d > 180f) d -= 360f; if (d < -180f) d += 360f;
        camAzimuth = (camAzimuth + 0.16f * d + 360f) % 360f;
        camAltitude += 0.16f * ((float) -Math.toDegrees(orient[1]) - camAltitude);
        camRoll += 0.16f * ((float) Math.toDegrees(orient[2]) - camRoll);
    }

    @Override public void onAccuracyChanged(Sensor s, int a) {}
    @Override public void surfaceCreated(SurfaceHolder h) { if (checkSelfPermission(Manifest.permission.CAMERA) == PackageManager.PERMISSION_GRANTED) startCameraPreview(h); }
    @Override public void surfaceChanged(SurfaceHolder h, int f, int w, int he) {}
    @Override public void surfaceDestroyed(SurfaceHolder h) { if (camera != null) { try { camera.stopPreview(); camera.release(); } catch (Exception ignored) {} camera = null; } }

    private void startCameraPreview(SurfaceHolder h) {
        try {
            if (camera == null) camera = Camera.open();
            if (camera != null) { camera.stopPreview(); camera.setDisplayOrientation(90); camera.setPreviewDisplay(h); camera.startPreview(); }
        } catch (Exception ignored) {}
    }

    private class AROverlayView extends View {
        private final Paint paint = new Paint(Paint.ANTI_ALIAS_FLAG);
        private final Path path = new Path();
        public AROverlayView(Context c) { super(c); }

        @Override protected void onDraw(Canvas c) {
            super.onDraw(c);
            int w = getWidth(), h = getHeight(); if (w <= 0 || h <= 0) return;
            float ui = w / 1080f;
            double[] sun = computeSun(latitude, selectedDay, dispHour);
            if (is2DMapMode) {
                c.drawColor(isLightTheme ? Color.rgb(238, 242, 247) : Color.rgb(14, 22, 34));
                draw2D(c, w, h, ui, sun);
            } else drawAR(c, w, h, ui, sun);
            if (showKeoHeatmap) drawKeoMap(c, ui);
            drawHeader(c, w, ui, sun);
        }

        private void draw2D(Canvas c, int w, int h, float ui, double[] sun) {
            float cx = w / 2f, cy = h * 0.56f, sc = mapScale * ui;
            paint.setStyle(Paint.Style.STROKE); paint.setStrokeWidth(1.5f * ui); paint.setColor(Color.argb(80, 100, 140, 180));
            c.drawLine(0, cy, w, cy, paint); c.drawLine(cx, 390 * ui, cx, h - 180 * ui, paint);
            for (int r : new int[]{50, 100, 150, 200}) c.drawCircle(cx, cy, r * sc, paint);
            paint.setStyle(Paint.Style.FILL); paint.setColor(Color.argb(45, 0, 255, 180));
            c.drawArc(new RectF(cx - 120 * sc, cy - 120 * sc, cx + 120 * sc, cy + 120 * sc), camAzimuth - 120f, 60f, true, paint);

            float shX = (float) Math.sin(Math.toRadians(sun[0] + 180.0)), shY = (float) Math.cos(Math.toRadians(sun[0] + 180.0));
            double tanA = Math.max(0.08, Math.tan(Math.toRadians(Math.max(1.0, sun[1]))));
            synchronized (osmBuildings) {
                if (sun[1] > 0.5) {
                    paint.setColor(Color.argb(135, 8, 12, 20));
                    for (OsmBuilding b : osmBuildings) {
                        float len = Math.min(250f, (float) (b.heightMeters / tanA));
                        for (int i = 0; i < b.xMeters.length; i++) {
                            int nx = (i + 1) % b.xMeters.length; path.reset();
                            path.moveTo(cx + b.xMeters[i] * sc, cy - b.yMeters[i] * sc);
                            path.lineTo(cx + b.xMeters[nx] * sc, cy - b.yMeters[nx] * sc);
                            path.lineTo(cx + (b.xMeters[nx] + shX * len) * sc, cy - (b.yMeters[nx] + shY * len) * sc);
                            path.lineTo(cx + (b.xMeters[i] + shX * len) * sc, cy - (b.yMeters[i] + shY * len) * sc);
                            path.close(); c.drawPath(path, paint);
                        }
                    }
                }
                for (OsmBuilding b : osmBuildings) {
                    path.reset(); float sx = 0, sy = 0; int n = b.xMeters.length;
                    for (int i = 0; i < n; i++) {
                        float px = cx + b.xMeters[i] * sc, py = cy - b.yMeters[i] * sc;
                        sx += px; sy += py; if (i == 0) path.moveTo(px, py); else path.lineTo(px, py);
                    }
                    path.close();
                    boolean blk = doesBlock(b, sun[0], sun[1]);
                    paint.setStyle(Paint.Style.FILL);
                    paint.setColor(b.isCustom ? Color.argb(190, 0, 180, 215) : (blk ? Color.argb(210, 175, 45, 55) : Color.argb(200, 55, 80, 110)));
                    c.drawPath(path, paint);
                    paint.setStyle(Paint.Style.STROKE); paint.setStrokeWidth(2.5f * ui);
                    paint.setColor(blk ? Color.RED : Color.rgb(130, 190, 245)); c.drawPath(path, paint);
                    paint.setStyle(Paint.Style.FILL); paint.setColor(Color.WHITE); paint.setTextSize(18f * ui);
                    c.drawText(b.houseNumber + "(" + b.levels + "э)", sx / n - 22 * ui, sy / n + 6 * ui, paint);
                }
            }
            paint.setColor(Color.GREEN); c.drawCircle(cx, cy, 10f * ui, paint);
        }

        private void drawAR(Canvas c, int w, int h, float ui, double[] sun) {
            float cx = w / 2f, cy = h / 2f, fH = 60f, fV = 75f;
            paint.setStyle(Paint.Style.STROKE); paint.setStrokeWidth(2.5f * ui);
            synchronized (osmBuildings) {
                for (OsmBuilding b : osmBuildings) {
                    paint.setColor(doesBlock(b, sun[0], sun[1]) ? Color.argb(180, 255, 80, 80) : Color.argb(140, 90, 200, 255));
                    for (int i = 0; i < b.xMeters.length; i++) {
                        float d = (float) Math.hypot(b.xMeters[i], b.yMeters[i]);
                        if (d < 4f || d > 190f) continue;
                        float sx = azToX(((float) Math.toDegrees(Math.atan2(b.xMeters[i], b.yMeters[i])) + 360f) % 360f, w, fH);
                        if (sx >= 0 && sx <= w) {
                            float yR = cy - (((float) Math.toDegrees(Math.atan2(b.heightMeters - relativeHeightMeters, d)) - camAltitude) / fV) * h;
                            float yB = cy - (((float) Math.toDegrees(Math.atan2(-relativeHeightMeters, d)) - camAltitude) / fV) * h;
                            c.drawLine(sx, yR, sx, yB, paint);
                        }
                    }
                }
            }
            float hy = cy + (camAltitude / fV) * h;
            paint.setColor(Color.argb(180, 0, 255, 180)); c.drawLine(0, hy, w, hy, paint);

            path.reset(); boolean st = false; paint.setColor(Color.YELLOW); paint.setStrokeWidth(5f * ui);
            for (double hr = 5.0; hr <= 21.0; hr += 0.5) {
                double[] p = computeSun(latitude, selectedDay, hr); if (p[1] < -5) continue;
                float sx = azToX((float) p[0], w, fH), sy = cy - (((float) p[1] - camAltitude) / fV) * h;
                if (sx >= -w && sx <= 2 * w) { if (!st) { path.moveTo(sx, sy); st = true; } else path.lineTo(sx, sy); } else st = false;
            }
            c.drawPath(path, paint);

            float r = 85f * ui, calP = rawPitch - tarePitch;
            paint.setColor(Math.abs(calP) < 0.5f ? Color.GREEN : Color.WHITE);
            c.drawCircle(cx, cy, r, paint); c.drawLine(cx - r - 20 * ui, cy, cx + r + 20 * ui, cy, paint); c.drawLine(cx, cy - r - 20 * ui, cx, cy + r + 20 * ui, paint);

            if (tapeMode > 0) {
                float eAz = tapeAz2 != null ? tapeAz2 : camAzimuth, eAlt = tapeAlt2 != null ? tapeAlt2 : camAltitude;
                if (tapeAz1 != null) {
                    float x1 = azToX(tapeAz1, w, fH), y1 = cy - ((tapeAlt1 - camAltitude) / fV) * h;
                    float x2 = azToX(eAz, w, fH), y2 = cy - ((eAlt - camAltitude) / fV) * h;
                    paint.setColor(Color.CYAN); paint.setStrokeWidth(5f * ui); c.drawLine(x1, y1, x2, y2, paint);
                    paint.setStyle(Paint.Style.FILL); c.drawCircle(x1, y1, 13 * ui, paint); c.drawCircle(x2, y2, 13 * ui, paint);
                }
                paint.setStyle(Paint.Style.FILL); paint.setColor(Color.argb(230, 14, 22, 34));
                c.drawRoundRect(new RectF(20 * ui, h - 355 * ui, w - 20 * ui, h - 195 * ui), 16 * ui, 16 * ui, paint);
                paint.setColor(Color.WHITE); paint.setTextSize(23f * ui);
                if (tapeAz1 == null) c.drawText(String.format(Locale.US, "Рулетка (Реж.%d D=%.2fм): наведите на Точку А", tapeMode, tapeWallDist), 36 * ui, h - 295 * ui, paint);
                else {
                    float[] m = calcTape(tapeAz1, tapeAlt1, eAz, eAlt);
                    c.drawText(String.format(Locale.US, "L: %.2fм | ΔH: %.2fм | ΔW: %.2fм | S: %.2fм²", m[0], m[1], m[2], m[4]), 36 * ui, h - 295 * ui, paint);
                }
                paint.setColor(Color.rgb(0, 165, 95)); c.drawRoundRect(new RectF(35 * ui, h - 262 * ui, w * 0.53f, h - 207 * ui), 12 * ui, 12 * ui, paint);
                paint.setColor(Color.rgb(55, 90, 140)); c.drawRoundRect(new RectF(w * 0.55f, h - 262 * ui, w * 0.81f, h - 207 * ui), 12 * ui, 12 * ui, paint);
                paint.setColor(Color.rgb(170, 50, 55)); c.drawRoundRect(new RectF(w * 0.83f, h - 262 * ui, w - 35 * ui, h - 207 * ui), 12 * ui, 12 * ui, paint);
                paint.setColor(Color.WHITE);
                c.drawText((tapeAz1 == null || tapeAz2 != null) ? "+ Точка А" : "+ Точка Б", 70 * ui, h - 226 * ui, paint);
                c.drawText("Режим/D", w * 0.58f, h - 226 * ui, paint); c.drawText("Выкл", w * 0.86f, h - 226 * ui, paint);
            }
        }

        private void drawKeoMap(Canvas c, float ui) {
            paint.setStyle(Paint.Style.FILL); paint.setColor(Color.argb(215, 16, 22, 32));
            c.drawRoundRect(new RectF(24 * ui, 400 * ui, 345 * ui, 540 * ui), 14 * ui, 14 * ui, paint);
            float ext = Math.max(1f, externalLuxForKeo > 0 ? externalLuxForKeo : 5000f);
            float[] v = {(keoWin > 0 ? keoWin : currentLux) * 100f / ext, (keoCen > 0 ? keoCen : currentLux * 0.5f) * 100f / ext, (keoBack > 0 ? keoBack : currentLux * 0.2f) * 100f / ext};
            String[] nm = {"Окно", "Центр", "Угол"};
            for (int i = 0; i < 3; i++) {
                paint.setColor(v[i] >= 1f ? Color.rgb(40, 185, 85) : (v[i] >= 0.5f ? Color.rgb(225, 170, 30) : Color.rgb(210, 55, 55)));
                c.drawRoundRect(new RectF((38 + i * 98) * ui, 420 * ui, (126 + i * 98) * ui, 525 * ui), 10 * ui, 10 * ui, paint);
                paint.setColor(Color.WHITE); paint.setTextSize(19f * ui);
                c.drawText(nm[i], (48 + i * 98) * ui, 460 * ui, paint); c.drawText(String.format(Locale.US, "%.1f%%", v[i]), (48 + i * 98) * ui, 500 * ui, paint);
            }
        }

        private void drawHeader(Canvas c, int w, float ui, double[] sun) {
            paint.setStyle(Paint.Style.FILL);
            paint.setColor(isLightTheme ? Color.argb(235, 250, 252, 255) : Color.argb(205, 14, 20, 28));
            c.drawRoundRect(new RectF(16 * ui, 20 * ui, w - 16 * ui, 385 * ui), 20 * ui, 20 * ui, paint);
            paint.setColor(isLightTheme ? Color.BLACK : Color.WHITE); paint.setTextSize(26.5f * ui);
            c.drawText(String.format(Locale.US, "Азимут: %.1f° | Солнце: Аз %.0f° Выс %.0f°", camAzimuth, sun[0], sun[1]), 34 * ui, 62 * ui, paint);

            float calP = rawPitch - tarePitch, pct = (float) (Math.tan(Math.toRadians(Math.abs(calP))) * 100.0);
            paint.setColor(Math.abs(calP) < 0.5f ? Color.rgb(0, 170, 70) : Color.rgb(255, 210, 70));
            c.drawText(String.format(Locale.US, "Уклон: %.1f° | %.1f%% | %.0f мм/м (Крен %.1f°)", calP, pct, pct * 10f, rawRoll - tareRoll), 34 * ui, 110 * ui, paint);

            int fl = Math.max(1, Math.round(relativeHeightMeters / floorHeightMeters) + 1);
            paint.setColor(isLightTheme ? Color.rgb(0, 95, 165) : Color.rgb(110, 225, 255));
            c.drawText(String.format(Locale.US, "Отметка H: %+.2f м (~%d эт. %s) [Тап = Изм]", relativeHeightMeters, fl, isManualHeightMode ? "РУЧН" : "АВТО"), 34 * ui, 158 * ui, paint);

            paint.setColor(isLightTheme ? Color.rgb(20, 125, 50) : Color.rgb(190, 255, 160));
            c.drawText(String.format(Locale.US, "Свет: %.0f лк | КЕО: %s", currentLux, lastKeo > 0 ? String.format(Locale.US, "%.2f%%", lastKeo) : "не замер."), 34 * ui, 206 * ui, paint);

            float[] ins = calcInsolation(latitude, selectedDay);
            paint.setColor(ins[1] >= 2f ? Color.rgb(0, 175, 85) : Color.rgb(225, 55, 55));
            c.drawText(String.format(Locale.US, "СанПиН: %s (%.1f ч без тени / %.1f ч)", ins[1] >= 2f ? "СОБЛЮДЕНА (≥2ч)" : "НАРУШЕНИЕ (<2ч)", ins[1], ins[0]), 34 * ui, 254 * ui, paint);

            paint.setTextSize(22.5f * ui); paint.setColor(gpsLocked ? Color.rgb(0, 160, 80) : Color.rgb(220, 130, 20));
            c.drawText(String.format(Locale.US, "%.4f N, %.4f E [%s] | %s", latitude, longitude, gpsLocked ? "GPS ОК" : "Поиск GPS", osmStatus), 34 * ui, 300 * ui, paint);
            paint.setColor(isLightTheme ? Color.DKGRAY : Color.rgb(150, 205, 255));
            c.drawText(seasonLabel + " | Тап по Отметке H = коррекция этажа", 34 * ui, 340 * ui, paint);
            c.drawText("Рулетка = 3D замер | Меню BIM = поиск адреса и DXF", 34 * ui, 372 * ui, paint);
        }

        private float azToX(float az, int w, float fH) {
            float d = az - camAzimuth; if (d > 180f) d -= 360f; if (d < -180f) d += 360f;
            return (w / 2f) + (d / fH) * w;
        }
    }
}
// === КОНЕЦ ФАЙЛА ===
