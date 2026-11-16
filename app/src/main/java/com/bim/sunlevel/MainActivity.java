package com.bim.sunlevel;

import android.Manifest;
import android.app.Activity;
import android.app.AlertDialog;
import android.content.ContentValues;
import android.content.Context;
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
import java.io.FileWriter;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.net.HttpURLConnection;
import java.net.URL;
import java.net.URLEncoder;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Date;
import java.util.List;
import java.util.Locale;

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

    // Стартовые координаты (по умолчанию 54.619 N, 39.742 E до уточнения GPS)
    private double latitude = 54.6190;
    private double longitude = 39.7420;
    private double lastOsmLat = 0.0;
    private double lastOsmLon = 0.0;
    private boolean gpsLocked = false;

    // Ориентация камеры (в градусах)
    private float camAzimuth = 0f;
    private float camAltitude = 0f;
    private float camRoll = 0f;

    // Данные цифрового нивелира
    private float rawPitch = 0f, rawRoll = 0f;
    private float tarePitch = 0f, tareRoll = 0f;

    // Барометр, калибровка этажа и люксметр
    private float currentPressure = 1013.25f;
    private float basePressure = -1f;
    private float floorHeightMeters = 3.0f;
    private float calibratedBaseHeight = 12.0f; // 5 этаж (+12.00 м)
    private float relativeHeightMeters = 12.0f;
    private float currentLux = 0f;

    // Дата и выбранное ползунком время суток
    private int selectedDayOfYear = 80;
    private String selectedSeasonLabel = "21 Мар/Сен (СанПиН)";
    private double selectedSolarHour = 12.5; // Ползунок времени (5.0 .. 21.0)

    // Режим отображения: false = AR Камера, true = 2D Генплан с тенями
    private boolean is2DMapMode = false;
    private float mapScalePixelsPerMeter = 2.2f;

    // Список зданий из OpenStreetMap
    private static class OsmBuilding {
        float[] xMeters; // Восток (+X), Запад (-X) относительно пользователя
        float[] yMeters; // Север (+Y), Юг (-Y) относительно пользователя
        float heightMeters;
        int levels;
    }

    private final List<OsmBuilding> osmBuildings = new ArrayList<>();
    private String osmStatus = "Загрузка домов OSM...";
    private boolean isFetchingOsm = false;

    private final float[] rotationMatrix = new float[9];
    private final float[] remappedMatrix = new float[9];
    private final float[] orientationVals = new float[3];

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);

        Calendar cal = Calendar.getInstance();
        selectedDayOfYear = cal.get(Calendar.DAY_OF_YEAR);
        selectedSeasonLabel = "Сегодня (день #" + selectedDayOfYear + ")";
        int hr = cal.get(Calendar.HOUR_OF_DAY);
        int min = cal.get(Calendar.MINUTE);
        selectedSolarHour = Math.max(5.0, Math.min(21.0, hr + min / 60.0));

        FrameLayout root = new FrameLayout(this);

        cameraSurface = new SurfaceView(this);
        cameraSurface.getHolder().addCallback(this);
        root.addView(cameraSurface);

        overlayView = new AROverlayView(this);
        // Масштабирование 2D-карты нажатием в режиме плана
        overlayView.setOnTouchListener((v, event) -> {
            if (is2DMapMode && event.getAction() == MotionEvent.ACTION_DOWN) {
                if (event.getY() > 420 && event.getY() < v.getHeight() - 260) {
                    if (mapScalePixelsPerMeter < 2.0f) mapScalePixelsPerMeter = 2.6f;
                    else if (mapScalePixelsPerMeter < 3.2f) mapScalePixelsPerMeter = 4.0f;
                    else mapScalePixelsPerMeter = 1.4f;
                    overlayView.invalidate();
                    Toast.makeText(this, "Масштаб 2D-плана изменен", Toast.LENGTH_SHORT).show();
                }
            }
            return false;
        });
        root.addView(overlayView);

        // Нижний блок управления (ползунок времени + панель кнопок)
        LinearLayout bottomContainer = new LinearLayout(this);
        bottomContainer.setOrientation(LinearLayout.VERTICAL);
        bottomContainer.setBackgroundColor(Color.argb(205, 12, 18, 26));
        bottomContainer.setPadding(12, 10, 12, 20);

        // Строка ползунка времени суток
        LinearLayout sliderRow = new LinearLayout(this);
        sliderRow.setOrientation(LinearLayout.HORIZONTAL);
        sliderRow.setGravity(Gravity.CENTER_VERTICAL);
        sliderRow.setPadding(12, 4, 12, 8);

        timeLabelView = new TextView(this);
        timeLabelView.setTextColor(Color.rgb(255, 225, 90));
        timeLabelView.setTextSize(13f);
        timeLabelView.setText(formatSolarHour(selectedSolarHour));
        sliderRow.addView(timeLabelView);

        SeekBar timeSeekBar = new SeekBar(this);
        timeSeekBar.setMax(160); // от 5.0 до 21.0 часов с шагом 0.1 ч (6 минут)
        timeSeekBar.setProgress((int) Math.round((selectedSolarHour - 5.0) * 10.0));
        LinearLayout.LayoutParams seekParams = new LinearLayout.LayoutParams(
                0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f);
        seekParams.setMargins(16, 0, 8, 0);
        timeSeekBar.setLayoutParams(seekParams);
        timeSeekBar.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
            @Override
            public void onProgressChanged(SeekBar seekBar, int progress, boolean fromUser) {
                selectedSolarHour = 5.0 + progress / 10.0;
                timeLabelView.setText(formatSolarHour(selectedSolarHour));
                if (overlayView != null) overlayView.invalidate();
            }

            @Override
            public void onStartTrackingTouch(SeekBar seekBar) {}

            @Override
            public void onStopTrackingTouch(SeekBar seekBar) {}
        });
        sliderRow.addView(timeSeekBar);
        bottomContainer.addView(sliderRow);

        // Ряд кнопок управления
        LinearLayout bottomBar = new LinearLayout(this);
        bottomBar.setOrientation(LinearLayout.HORIZONTAL);
        bottomBar.setGravity(Gravity.CENTER);

        btnModeToggle = createButton("2D План", Color.argb(230, 30, 115, 165));
        btnModeToggle.setOnClickListener(v -> {
            is2DMapMode = !is2DMapMode;
            btnModeToggle.setText(is2DMapMode ? "Камера AR" : "2D План");
            overlayView.invalidate();
        });

        Button btnSeason = createButton("Дата", Color.argb(210, 45, 65, 95));
        btnSeason.setOnClickListener(v -> cycleSeason());

        Button btnTare = createButton("Тара 0°", Color.argb(210, 45, 65, 95));
        btnTare.setOnClickListener(v -> {
            tarePitch = rawPitch;
            tareRoll = rawRoll;
            Toast.makeText(this, "Уклономер обнулен (0.0°)", Toast.LENGTH_SHORT).show();
        });

        Button btnZeroAlt = createButton("Этаж/0м", Color.argb(210, 45, 65, 95));
        btnZeroAlt.setOnClickListener(v -> showAltitudeCalibrationDialog());

        Button btnPhoto = createButton("Фото AR", Color.argb(230, 190, 75, 25));
        btnPhoto.setOnClickListener(v -> captureARPhoto());

        Button btnSave = createButton("В CSV", Color.argb(210, 35, 110, 70));
        btnSave.setOnClickListener(v -> exportLogToCsv());

        bottomBar.addView(btnModeToggle);
        bottomBar.addView(btnSeason);
        bottomBar.addView(btnTare);
        bottomBar.addView(btnZeroAlt);
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

        // Сразу запускаем загрузку домов OSM для текущих координат
        fetchOsmBuildings(latitude, longitude);
    }

    private String formatSolarHour(double sh) {
        int h = (int) sh;
        int m = (int) Math.round((sh - h) * 60.0);
        if (m == 60) { h++; m = 0; }
        return String.format(Locale.US, "Время: %02d:%02d", h, m);
    }

    private Button createButton(String text, int bgColor) {
        Button b = new Button(this);
        b.setText(text);
        b.setTextSize(10.5f);
        b.setTextColor(Color.WHITE);
        b.setBackgroundColor(bgColor);
        b.setPadding(4, 12, 4, 12);
        LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f);
        lp.setMargins(3, 0, 3, 0);
        b.setLayoutParams(lp);
        return b;
    }

    // Загрузка реальных зданий из OpenStreetMap (Overpass API) в радиусе 220 метров
    private void fetchOsmBuildings(final double lat, final double lon) {
        if (isFetchingOsm) return;
        isFetchingOsm = true;
        osmStatus = "Загрузка домов OSM...";
        if (overlayView != null) overlayView.postInvalidate();

        new Thread(() -> {
            String[] endpoints = new String[]{
                    "https://overpass-api.de/api/interpreter",
                    "https://lz4.overpass-api.de/api/interpreter",
                    "https://overpass.kumi.systems/api/interpreter"
            };
            String query = String.format(Locale.US,
                    "[out:json][timeout:15];(way[\"building\"](around:220,%.5f,%.5f););out body geom;",
                    lat, lon);

            boolean success = false;
            for (String endpoint : endpoints) {
                HttpURLConnection conn = null;
                try {
                    String urlStr = endpoint + "?data=" + URLEncoder.encode(query, "UTF-8");
                    URL url = new URL(urlStr);
                    conn = (HttpURLConnection) url.openConnection();
                    conn.setConnectTimeout(8000);
                    conn.setReadTimeout(12000);
                    conn.setRequestProperty("User-Agent", "SunLevelBIM-Android/1.0");

                    if (conn.getResponseCode() == 200) {
                        BufferedReader reader = new BufferedReader(new InputStreamReader(conn.getInputStream()));
                        StringBuilder sb = new StringBuilder();
                        String line;
                        while ((line = reader.readLine()) != null) {
                            sb.append(line);
                        }
                        reader.close();

                        parseOsmJson(sb.toString(), lat, lon);
                        lastOsmLat = lat;
                        lastOsmLon = lon;
                        success = true;
                        break;
                    }
                } catch (Exception ignored) {
                } finally {
                    if (conn != null) conn.disconnect();
                }
            }

            final boolean ok = success;
            runOnUiThread(() -> {
                isFetchingOsm = false;
                if (ok) {
                    osmStatus = "Дома OSM: " + osmBuildings.size() + " шт.";
                } else {
                    osmStatus = "OSM нет связи (нажмите Этаж/0м для повтора)";
                }
                if (overlayView != null) overlayView.invalidate();
            });
        }).start();
    }

    private void parseOsmJson(String jsonStr, double centerLat, double centerLon) throws Exception {
        JSONObject root = new JSONObject(jsonStr);
        JSONArray elements = root.optJSONArray("elements");
        if (elements == null) return;

        List<OsmBuilding> parsed = new ArrayList<>();
        double metersPerDegLat = 111132.0;
        double metersPerDegLon = 111320.0 * Math.cos(Math.toRadians(centerLat));

        for (int i = 0; i < elements.length(); i++) {
            JSONObject el = elements.getJSONObject(i);
            JSONArray geom = el.optJSONArray("geometry");
            if (geom == null || geom.length() < 3) continue;

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

            // Определение этажности и высоты здания из тегов OSM
            int levels = 5;
            float height = -1f;
            JSONObject tags = el.optJSONObject("tags");
            if (tags != null) {
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
            if (levels <= 0) levels = 5;
            if (height <= 2f) height = levels * 3.0f;

            b.levels = levels;
            b.heightMeters = height;
            parsed.add(b);
        }

        synchronized (osmBuildings) {
            osmBuildings.clear();
            osmBuildings.addAll(parsed);
        }
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
                .setNeutralButton("Обновить дома OSM", (dialog, which) -> fetchOsmBuildings(latitude, longitude))
                .setNegativeButton("Отмена", null)
                .show();
    }

    private void captureARPhoto() {
        int targetW = overlayView.getWidth();
        int targetH = overlayView.getHeight();
        if (targetW <= 0 || targetH <= 0) return;

        // Если включен 2D-генплан, сохраняем чертеж с тенями напрямую
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
            comboCanvas.drawText("ШТАМП ФИКСАЦИИ: " + timeStamp + " | " + formatSolarHour(selectedSolarHour), 40, targetH - 178, stampPaint);

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

    private void cycleSeason() {
        if (selectedDayOfYear != 172 && selectedDayOfYear != 80 && selectedDayOfYear != 355) {
            selectedDayOfYear = 80;
            selectedSeasonLabel = "21 Мар/Сен (Равноденствие)";
        } else if (selectedDayOfYear == 80) {
            selectedDayOfYear = 172;
            selectedSeasonLabel = "21 Июня (Летний максимум)";
        } else if (selectedDayOfYear == 172) {
            selectedDayOfYear = 355;
            selectedSeasonLabel = "21 Декабря (Зимний минимум)";
        } else {
            Calendar cal = Calendar.getInstance();
            selectedDayOfYear = cal.get(Calendar.DAY_OF_YEAR);
            selectedSeasonLabel = "Сегодня (день #" + selectedDayOfYear + ")";
        }
        if (overlayView != null) overlayView.invalidate();
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
        // Если сместились более чем на 60 метров от точки прошлой выгрузки OSM — обновляем карту
        double distSq = Math.pow((latitude - lastOsmLat) * 111132.0, 2) +
                        Math.pow((longitude - lastOsmLon) * 65000.0, 2);
        if (distSq > 3600.0) {
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

    // Астрономический расчет Солнца: возвращает {Азимут 0..360, Высота над горизонтом -90..90}
    private double[] computeSunPosition(double latDeg, int dayOfYear, double solarHour) {
        double latRad = Math.toRadians(latDeg);
        double declDeg = 23.45 * Math.sin(Math.toRadians((360.0 / 365.0) * (284 + dayOfYear)));
        double declRad = Math.toRadians(declDeg);
        double hourAngleRad = Math.toRadians(15.0 * (solarHour - 12.0));

        double sinAlt = Math.sin(latRad) * Math.sin(declRad) +
                        Math.cos(latRad) * Math.cos(declRad) * Math.cos(hourAngleRad);
        sinAlt = Math.max(-1.0, Math.min(1.0, sinAlt));
        double altRad = Math.asin(sinAlt);

        double cosAz = (Math.sin(declRad) - Math.sin(altRad) * Math.sin(latRad)) /
                       (Math.cos(altRad) * Math.cos(latRad) + 1e-6);
        cosAz = Math.max(-1.0, Math.min(1.0, cosAz));
        double azDeg = Math.toDegrees(Math.acos(cosAz));
        if (solarHour > 12.0) azDeg = 360.0 - azDeg;

        return new double[]{azDeg, Math.toDegrees(altRad)};
    }

    // Проверка, закрыто ли Солнце соседними зданиями OSM на высоте текущего этажа
    private boolean isSunBlockedByOsmBuildings(double sunAzDeg, double sunAltDeg) {
        if (sunAltDeg <= 0.5) return true;
        double tanAlt = Math.tan(Math.toRadians(sunAltDeg));
        double rayDirX = Math.sin(Math.toRadians(sunAzDeg));
        double rayDirY = Math.cos(Math.toRadians(sunAzDeg));

        synchronized (osmBuildings) {
            for (OsmBuilding b : osmBuildings) {
                float dh = b.heightMeters - relativeHeightMeters;
                if (dh <= 0.5f) continue; // Здание ниже нашего этажа не дает тень на окно

                // Если точка (0,0) внутри самого контура нашего дома — пропускаем его
                if (isPointInPolygon(0f, 0f, b.xMeters, b.yMeters)) continue;

                float maxShadowDist = (float) (dh / tanAlt);
                int n = b.xMeters.length;
                for (int i = 0; i < n; i++) {
                    float x1 = b.xMeters[i], y1 = b.yMeters[i];
                    float x2 = b.xMeters[(i + 1) % n], y2 = b.yMeters[(i + 1) % n];
                    float dist = intersectRayWithSegment((float) rayDirX, (float) rayDirY, x1, y1, x2, y2);
                    if (dist > 2.0f && dist <= maxShadowDist) {
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

    // Пересечение луча из (0,0) в направлении (dx, dy) с отрезком стены (x1,y1)-(x2,y2)
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

    private void exportLogToCsv() {
        try {
            File dir = Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DOWNLOADS);
            if (!dir.exists()) dir.mkdirs();
            File file = new File(dir, "BIM_Field_Log.csv");
            boolean isNew = !file.exists();

            FileWriter fw = new FileWriter(file, true);
            if (isNew) {
                fw.append("Timestamp,Lat,Lon,CamAzimuth_deg,CamAltitude_deg,SlopePitch_deg,Slope_mm_per_m,Lux,DeltaHeight_m,EstFloor,SolarHour\n");
            }
            String ts = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss", Locale.US).format(new Date());
            float calPitch = rawPitch - tarePitch;
            float mmPerMeter = (float) (Math.tan(Math.toRadians(Math.abs(calPitch))) * 1000.0);
            int estFloor = Math.round(relativeHeightMeters / floorHeightMeters) + 1;

            fw.append(String.format(Locale.US, "%s,%.5f,%.5f,%.1f,%.1f,%.2f,%.1f,%.0f,%.2f,%d,%.1f\n",
                    ts, latitude, longitude, camAzimuth, camAltitude, calPitch, mmPerMeter,
                    currentLux, relativeHeightMeters, estFloor, selectedSolarHour));
            fw.flush();
            fw.close();
            Toast.makeText(this, "Сохранено в Download/BIM_Field_Log.csv", Toast.LENGTH_LONG).show();
        } catch (Exception e) {
            Toast.makeText(this, "Ошибка записи: " + e.getMessage(), Toast.LENGTH_SHORT).show();
        }
    }

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

            if (is2DMapMode) {
                draw2DTopDownMap(canvas, w, h);
            } else {
                drawARCameraOverlay(canvas, w, h);
            }

            // Верхняя инженерная панель телеметрии (общая для AR и 2D-генплана)
            drawTelemetryHeader(canvas, w);
        }

        // РЕЖИМ 1: 2D ГЕНПЛАН С ДОМАМИ OPENSTREETMAP И ТЕНЯМИ
        private void draw2DTopDownMap(Canvas canvas, int w, int h) {
            // Темный чертежный фон генплана
            canvas.drawColor(Color.rgb(14, 22, 34));

            float cx = w / 2f;
            float cy = h * 0.56f;
            float scale = mapScalePixelsPerMeter;

            // Координатная сетка и радиусы 50м / 100м / 150м
            paint.setStyle(Paint.Style.STROKE);
            paint.setStrokeWidth(1.5f);
            paint.setColor(Color.argb(70, 90, 140, 190));
            canvas.drawLine(0, cy, w, cy, paint);
            canvas.drawLine(cx, 380, cx, h - 180, paint);

            paint.setTextSize(22f);
            for (int rMeters : new int[]{50, 100, 150}) {
                float rPx = rMeters * scale;
                canvas.drawCircle(cx, cy, rPx, paint);
                paint.setStyle(Paint.Style.FILL);
                canvas.drawText(rMeters + "м", cx + 6, cy - rPx + 22, paint);
                paint.setStyle(Paint.Style.STROKE);
            }

            // Сектор обзора камеры (куда сейчас направлен телефон)
            paint.setStyle(Paint.Style.FILL);
            paint.setColor(Color.argb(45, 0, 255, 180));
            RectF fovRect = new RectF(cx - 120 * scale, cy - 120 * scale, cx + 120 * scale, cy + 120 * scale);
            float startAngle2D = camAzimuth - 90f - 30f;
            canvas.drawArc(fovRect, startAngle2D, 60f, true, paint);

            // Положение Солнца для выбранного на ползунке времени
            double[] sunPos = computeSunPosition(latitude, selectedDayOfYear, selectedSolarHour);
            double sunAz = sunPos[0];
            double sunAlt = sunPos[1];

            // Вектор падения тени (противоположен азимуту Солнца)
            double shadowAzRad = Math.toRadians(sunAz + 180.0);
            float shDirX = (float) Math.sin(shadowAzRad); // Восток (+X)
            float shDirY = (float) Math.cos(shadowAzRad); // Север (+Y)
            double tanAlt = Math.max(0.08, Math.tan(Math.toRadians(Math.max(1.0, sunAlt))));

            synchronized (osmBuildings) {
                // Слой 1: Тени зданий на уровне земли (темно-синие/черные)
                if (sunAlt > 0.5) {
                    paint.setStyle(Paint.Style.FILL);
                    paint.setColor(Color.argb(135, 4, 8, 15));
                    for (OsmBuilding b : osmBuildings) {
                        float shadowLen = Math.min(260f, (float) (b.heightMeters / tanAlt));
                        drawBuildingShadow(canvas, b, cx, cy, scale, shDirX * shadowLen, shDirY * shadowLen);
                    }

                    // Слой 2: Тени зданий на высоте вашего этажа (фиолетово-синий контур)
                    paint.setColor(Color.argb(115, 180, 70, 220));
                    for (OsmBuilding b : osmBuildings) {
                        float dh = b.heightMeters - relativeHeightMeters;
                        if (dh > 0.5f) {
                            float floorShadowLen = Math.min(260f, (float) (dh / tanAlt));
                            drawBuildingShadow(canvas, b, cx, cy, scale, shDirX * floorShadowLen, shDirY * floorShadowLen);
                        }
                    }
                }

                // Слой 3: Контуры самих домов и подписи этажности
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

                    // Дома выше нашего этажа выделяем более теплым оттенком
                    paint.setStyle(Paint.Style.FILL);
                    if (b.heightMeters > relativeHeightMeters + 1.0f) {
                        paint.setColor(Color.argb(210, 75, 95, 125));
                    } else {
                        paint.setColor(Color.argb(190, 45, 65, 85));
                    }
                    canvas.drawPath(path, paint);

                    paint.setStyle(Paint.Style.STROKE);
                    paint.setStrokeWidth(2.5f);
                    paint.setColor(Color.rgb(140, 195, 245));
                    canvas.drawPath(path, paint);

                    // Подпись этажности в центре дома
                    paint.setStyle(Paint.Style.FILL);
                    paint.setColor(Color.WHITE);
                    paint.setTextSize(20f);
                    canvas.drawText(b.levels + "эт", (sumX / n) - 18f, (sumY / n) + 7f, paint);
                }
            }

            // Луч направления на Солнце на 2D-карте
            if (sunAlt > 0) {
                float sunVecX = (float) Math.sin(Math.toRadians(sunAz));
                float sunVecY = (float) Math.cos(Math.toRadians(sunAz));
                float sunScreenX = cx + sunVecX * 260f;
                float sunScreenY = cy - sunVecY * 260f;

                paint.setStyle(Paint.Style.STROKE);
                paint.setStrokeWidth(5f);
                paint.setColor(Color.rgb(255, 220, 40));
                canvas.drawLine(cx, cy, sunScreenX, sunScreenY, paint);

                paint.setStyle(Paint.Style.FILL);
                canvas.drawCircle(sunScreenX, sunScreenY, 18f, paint);
            }

            // Точка местоположения пользователя в центре
            boolean inShadowNow = isSunBlockedByOsmBuildings(sunAz, sunAlt);
            paint.setStyle(Paint.Style.FILL);
            paint.setColor(inShadowNow ? Color.rgb(255, 90, 90) : Color.rgb(0, 255, 140));
            canvas.drawCircle(cx, cy, 12f, paint);

            // Подсказка внизу 2D-карты
            paint.setColor(Color.LTGRAY);
            paint.setTextSize(25f);
            String shadowStatus = (sunAlt <= 0) ? "Ночь (Солнце за горизонтом)" :
                    (inShadowNow ? "В ТЕНИ соседнего здания (на отм. этажа)" : "ПРЯМОЕ СОЛНЦЕ (тень не перекрывает этаж)");
            canvas.drawText(shadowStatus + " | " + osmStatus, 30, h - 195, paint);
        }

        // Отрисовка падающей тени от каждой стены здания
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

        // РЕЖИМ 2: AR-КАМЕРА С ДУГАМИ СОЛНЦА, ДОМАМИ И 2D-НИВЕЛИРОМ
        private void drawARCameraOverlay(Canvas canvas, int w, int h) {
            float cx = w / 2f;
            float cy = h / 2f;
            float fovH = 60f;
            float fovV = 75f;

            // 1. Отрисовка 3D-силуэтов соседних домов из OpenStreetMap поверх камеры
            drawOsmBuildingsInAR(canvas, w, h, fovH, fovV);

            // 2. Линия горизонта
            float horizonY = cy + (camAltitude / fovV) * h;
            paint.setStyle(Paint.Style.STROKE);
            paint.setColor(Color.argb(160, 0, 255, 180));
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

            // 3. Дуги Солнца (Зима, Лето, Выбранная дата)
            drawSunArc(canvas, w, h, fovH, fovV, 355, Color.argb(140, 100, 180, 255), false);
            drawSunArc(canvas, w, h, fovH, fovV, 172, Color.argb(140, 255, 120, 80), false);
            drawSunArc(canvas, w, h, fovH, fovV, selectedDayOfYear, Color.rgb(255, 230, 0), true);

            // 4. Яркий маркер Солнца для выбранного на ползунке времени
            double[] curSun = computeSunPosition(latitude, selectedDayOfYear, selectedSolarHour);
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

            // 5. Цифровой 2D-нивелир в центре
            float calPitch = rawPitch - tarePitch;
            float calRoll = rawRoll - tareRoll;
            float levelRadius = 105f;
            paint.setStyle(Paint.Style.STROKE);
            paint.setStrokeWidth(4f);
            boolean isLevel = Math.abs(calPitch) < 0.5f && Math.abs(calRoll) < 0.5f;
            paint.setColor(isLevel ? Color.GREEN : Color.WHITE);
            canvas.drawCircle(cx, cy, levelRadius, paint);
            canvas.drawLine(cx - levelRadius - 20, cy, cx + levelRadius + 20, cy, paint);
            canvas.drawLine(cx, cy - levelRadius - 20, cx, cy + levelRadius + 20, paint);

            float bx = cx + Math.max(-levelRadius, Math.min(levelRadius, (calRoll / 15f) * levelRadius));
            float by = cy + Math.max(-levelRadius, Math.min(levelRadius, (calPitch / 15f) * levelRadius));
            paint.setStyle(Paint.Style.FILL);
            paint.setColor(isLevel ? Color.argb(210, 0, 255, 100) : Color.argb(210, 255, 180, 0));
            canvas.drawCircle(bx, by, 20f, paint);
        }

        // Проекция контуров крыш соседних зданий OSM в AR-видоискатель
        private void drawOsmBuildingsInAR(Canvas canvas, int w, int h, float fovH, float fovV) {
            float cy = h / 2f;
            paint.setStyle(Paint.Style.STROKE);
            paint.setStrokeWidth(2.5f);
            paint.setColor(Color.argb(130, 100, 200, 255));

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
            paint.setColor(Color.argb(195, 15, 20, 28));
            canvas.drawRoundRect(new RectF(18, 25, w - 18, 385), 22f, 22f, paint);

            double[] curSun = computeSunPosition(latitude, selectedDayOfYear, selectedSolarHour);
            paint.setColor(Color.WHITE);
            paint.setTextSize(31f);
            canvas.drawText(String.format(Locale.US, "Азимут: %.1f° (%s) | Солнце: Аз %.0f° Выс %.0f°",
                    camAzimuth, getCardinal(camAzimuth), curSun[0], curSun[1]), 38, 72, paint);

            float calPitch = rawPitch - tarePitch;
            float calRoll = rawRoll - tareRoll;
            boolean isLevel = Math.abs(calPitch) < 0.5f && Math.abs(calRoll) < 0.5f;
            float slopePercent = (float) (Math.tan(Math.toRadians(Math.abs(calPitch))) * 100.0);
            float slopeMmM = slopePercent * 10f;
            paint.setColor(isLevel ? Color.GREEN : Color.rgb(255, 215, 80));
            canvas.drawText(String.format(Locale.US, "Уклон: %.1f° | %.1f%% | %.0f мм/м (Крен: %.1f°)",
                    calPitch, slopePercent, slopeMmM, calRoll), 38, 124, paint);

            int estFloor = Math.round(relativeHeightMeters / floorHeightMeters) + 1;
            paint.setColor(Color.rgb(130, 220, 255));
            canvas.drawText(String.format(Locale.US, "Отметка H: %+.2f м (~%d эт.) | %.1f гПа",
                    relativeHeightMeters, estFloor, currentPressure), 38, 176, paint);

            paint.setColor(Color.rgb(200, 255, 160));
            canvas.drawText(String.format(Locale.US, "Свет: %.0f лк (%s)",
                    currentLux, evaluateLuxNorm(currentLux)), 38, 228, paint);

            float[] insolHours = calculateInsolationWithOsm(latitude, selectedDayOfYear);
            paint.setColor(Color.rgb(255, 230, 100));
            canvas.drawText(String.format(Locale.US, "%s: %.1f ч (без тени домов: %.1f ч)",
                    selectedSeasonLabel, insolHours[0], insolHours[1]), 38, 280, paint);

            paint.setTextSize(26f);
            paint.setColor(Color.LTGRAY);
            String gpsText = gpsLocked ? "GPS точный" : "GPS старт";
            canvas.drawText(String.format(Locale.US, "%.4f N, %.4f E [%s] | %s",
                    latitude, longitude, gpsText, osmStatus), 38, 332, paint);

            paint.setColor(Color.rgb(140, 200, 255));
            canvas.drawText(is2DMapMode ? "Режим: 2D Генплан теней (нажмите на карту для зума)" :
                    "Режим: Камера AR (красный кружок на дуге = тень от дома)", 38, 368, paint);
        }

        private void drawSunArc(Canvas canvas, int w, int h, float fovH, float fovV, int day, int color, boolean drawHours) {
            paint.setColor(color);
            paint.setStyle(Paint.Style.STROKE);
            paint.setStrokeWidth(drawHours ? 6f : 3f);
            path.reset();
            boolean started = false;

            for (double hr = 5.0; hr <= 21.0; hr += 0.5) {
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

        // Возвращает {Астрономические часы света, Реальные часы света без тени соседних зданий}
        private float[] calculateInsolationWithOsm(double lat, int day) {
            float astroHours = 0f;
            float unblockedHours = 0f;
            for (double hr = 4.5; hr <= 21.5; hr += 0.25) {
                double[] pos = computeSunPosition(lat, day, hr);
                if (pos[1] > 0) {
                    astroHours += 0.25f;
                    if (!isSunBlockedByOsmBuildings(pos[0], pos[1])) {
                        unblockedHours += 0.25f;
                    }
                }
            }
            return new float[]{astroHours, unblockedHours};
        }
    }
}
