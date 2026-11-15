package com.bim.sunlevel;

import android.Manifest;
import android.app.Activity;
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
import android.view.Gravity;
import android.view.SurfaceHolder;
import android.view.SurfaceView;
import android.view.View;
import android.widget.Button;
import android.widget.FrameLayout;
import android.widget.LinearLayout;
import android.widget.Toast;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileWriter;
import java.io.OutputStream;
import java.text.SimpleDateFormat;
import java.util.Calendar;
import java.util.Date;
import java.util.Locale;

@SuppressWarnings("deprecation")
public class MainActivity extends Activity implements SensorEventListener, SurfaceHolder.Callback {

    private SensorManager sensorManager;
    private Sensor rotSensor, accelSensor, pressureSensor, lightSensor;
    private LocationManager locationManager;

    private SurfaceView cameraSurface;
    private Camera camera;
    private AROverlayView overlayView;

    // Геокоординаты (по умолчанию 54.62 N, 39.74 E до получения GPS)
    private double latitude = 54.6269;
    private double longitude = 39.7456;
    private boolean gpsLocked = false;

    // Ориентация камеры для AR (в градусах)
    private float camAzimuth = 0f;   // 0..360 (0=С, 90=В, 180=Ю, 270=З)
    private float camAltitude = 0f;  // -90..+90 (0=горизонт, +90=зенит)
    private float camRoll = 0f;

    // Данные для цифрового нивелира (с учетом калибровки "Тара")
    private float rawPitch = 0f, rawRoll = 0f;
    private float tarePitch = 0f, tareRoll = 0f;

    // Барометр и люксметр
    private float currentPressure = 1013.25f;
    private float basePressure = -1f;
    private float relativeHeightMeters = 0f;
    private float currentLux = 0f;

    // Режимы отображения даты солнца
    private int selectedDayOfYear = 80;
    private String selectedSeasonLabel = "21 Мар/Сен (Норма СанПиН)";

    private final float[] rotationMatrix = new float[9];
    private final float[] remappedMatrix = new float[9];
    private final float[] orientationVals = new float[3];

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);

        Calendar cal = Calendar.getInstance();
        selectedDayOfYear = cal.get(Calendar.DAY_OF_YEAR);
        selectedSeasonLabel = "Сегодня (день #" + selectedDayOfYear + ")";

        FrameLayout root = new FrameLayout(this);

        cameraSurface = new SurfaceView(this);
        cameraSurface.getHolder().addCallback(this);
        root.addView(cameraSurface);

        overlayView = new AROverlayView(this);
        root.addView(overlayView);

        // Нижняя панель кнопок управления (5 кнопок)
        LinearLayout bottomBar = new LinearLayout(this);
        bottomBar.setOrientation(LinearLayout.HORIZONTAL);
        bottomBar.setGravity(Gravity.CENTER);
        bottomBar.setBackgroundColor(Color.argb(190, 15, 20, 28));
        bottomBar.setPadding(10, 14, 10, 22);

        Button btnSeason = createButton("Дата", Color.argb(210, 45, 65, 95));
        btnSeason.setOnClickListener(v -> cycleSeason());

        Button btnTare = createButton("Тара 0°", Color.argb(210, 45, 65, 95));
        btnTare.setOnClickListener(v -> {
            tarePitch = rawPitch;
            tareRoll = rawRoll;
            Toast.makeText(this, "Уклономер обнулен (0.0°)", Toast.LENGTH_SHORT).show();
        });

        Button btnZeroAlt = createButton("Отм 0м", Color.argb(210, 45, 65, 95));
        btnZeroAlt.setOnClickListener(v -> {
            basePressure = currentPressure;
            Toast.makeText(this, "Базовая отметка 0.00 м зафиксирована", Toast.LENGTH_SHORT).show();
        });

        Button btnPhoto = createButton("Фото AR", Color.argb(230, 190, 75, 25));
        btnPhoto.setOnClickListener(v -> captureARPhoto());

        Button btnSave = createButton("В CSV", Color.argb(210, 35, 110, 70));
        btnSave.setOnClickListener(v -> exportLogToCsv());

        bottomBar.addView(btnSeason);
        bottomBar.addView(btnTare);
        bottomBar.addView(btnZeroAlt);
        bottomBar.addView(btnPhoto);
        bottomBar.addView(btnSave);

        FrameLayout.LayoutParams barParams = new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.WRAP_CONTENT,
                Gravity.BOTTOM
        );
        root.addView(bottomBar, barParams);

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
    }

    private Button createButton(String text, int bgColor) {
        Button b = new Button(this);
        b.setText(text);
        b.setTextSize(11f);
        b.setTextColor(Color.WHITE);
        b.setBackgroundColor(bgColor);
        LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f);
        lp.setMargins(5, 0, 5, 0);
        b.setLayoutParams(lp);
        return b;
    }

    // Захват кадра с камеры, наложение AR-слоя со штампом и сохранение в Галерею
    private void captureARPhoto() {
        if (camera == null) {
            Toast.makeText(this, "Камера не активна", Toast.LENGTH_SHORT).show();
            return;
        }
        try {
            camera.setOneShotPreviewCallback((data, cam) -> {
                try {
                    Camera.Parameters params = cam.getParameters();
                    Camera.Size prevSize = params.getPreviewSize();

                    // Конвертация буфера камеры NV21 в JPEG
                    YuvImage yuvImage = new YuvImage(data, ImageFormat.NV21, prevSize.width, prevSize.height, null);
                    ByteArrayOutputStream baos = new ByteArrayOutputStream();
                    yuvImage.compressToJpeg(new Rect(0, 0, prevSize.width, prevSize.height), 95, baos);
                    byte[] jpegBytes = baos.toByteArray();
                    Bitmap rawCamBitmap = BitmapFactory.decodeByteArray(jpegBytes, 0, jpegBytes.length);

                    // Поворот кадра на 90 градусов для портретного режима
                    Matrix matrix = new Matrix();
                    matrix.postRotate(90);
                    Bitmap rotatedCamBitmap = Bitmap.createBitmap(
                            rawCamBitmap, 0, 0, rawCamBitmap.getWidth(), rawCamBitmap.getHeight(), matrix, true
                    );
                    rawCamBitmap.recycle();

                    int targetW = overlayView.getWidth();
                    int targetH = overlayView.getHeight();
                    Bitmap combinedBitmap = Bitmap.createBitmap(targetW, targetH, Bitmap.Config.ARGB_8888);
                    Canvas comboCanvas = new Canvas(combinedBitmap);

                    // 1. Отрисовка кадра с камеры на весь холст
                    Rect destRect = new Rect(0, 0, targetW, targetH);
                    comboCanvas.drawBitmap(rotatedCamBitmap, null, destRect, null);
                    rotatedCamBitmap.recycle();

                    // 2. Отрисовка AR-слоя (дуги солнца, нивелир, панель телеметрии)
                    overlayView.draw(comboCanvas);

                    // 3. Добавление нижнего штампа времени фотофиксации
                    Paint stampPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
                    stampPaint.setColor(Color.argb(200, 15, 20, 28));
                    comboCanvas.drawRoundRect(new RectF(20, targetH - 180, targetW - 20, targetH - 110), 16f, 16f, stampPaint);

                    stampPaint.setColor(Color.rgb(255, 220, 90));
                    stampPaint.setTextSize(30f);
                    String timeStamp = new SimpleDateFormat("dd.MM.yyyy HH:mm:ss", Locale.US).format(new Date());
                    comboCanvas.drawText("ШТАМП ФИКСАЦИИ: " + timeStamp, 45, targetH - 135, stampPaint);

                    // 4. Запись в системную Галерею (Pictures/BIM_SunLevel)
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
                        Toast.makeText(this, "Фото сохранено в Галерею (BIM_SunLevel)", Toast.LENGTH_LONG).show();
                    }
                    combinedBitmap.recycle();
                } catch (Exception e) {
                    Toast.makeText(this, "Ошибка сохранения фото: " + e.getMessage(), Toast.LENGTH_SHORT).show();
                }
            });
        } catch (Exception e) {
            Toast.makeText(this, "Сбой захвата кадра: " + e.getMessage(), Toast.LENGTH_SHORT).show();
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
        startLocationUpdates();
        startCameraPreview();
    }

    private void startLocationUpdates() {
        try {
            if (checkSelfPermission(Manifest.permission.ACCESS_FINE_LOCATION) == PackageManager.PERMISSION_GRANTED) {
                Location last = locationManager.getLastKnownLocation(LocationManager.GPS_PROVIDER);
                if (last == null) last = locationManager.getLastKnownLocation(LocationManager.NETWORK_PROVIDER);
                if (last != null) {
                    latitude = last.getLatitude();
                    longitude = last.getLongitude();
                    gpsLocked = true;
                }
                LocationListener listener = (Location loc) -> {
                    latitude = loc.getLatitude();
                    longitude = loc.getLongitude();
                    gpsLocked = true;
                };
                locationManager.requestLocationUpdates(LocationManager.GPS_PROVIDER, 5000, 5f, listener);
                locationManager.requestLocationUpdates(LocationManager.NETWORK_PROVIDER, 5000, 5f, listener);
            }
        } catch (Exception ignored) {}
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
            currentPressure = event.values[0];
            if (basePressure < 0) basePressure = currentPressure;
            relativeHeightMeters = 44330f * (1f - (float) Math.pow(currentPressure / basePressure, 0.190295f));

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

    private void exportLogToCsv() {
        try {
            File dir = Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DOWNLOADS);
            if (!dir.exists()) dir.mkdirs();
            File file = new File(dir, "BIM_Field_Log.csv");
            boolean isNew = !file.exists();

            FileWriter fw = new FileWriter(file, true);
            if (isNew) {
                fw.append("Timestamp,Lat,Lon,CamAzimuth_deg,CamAltitude_deg,SlopePitch_deg,Slope_mm_per_m,Lux,DeltaHeight_m,EstFloor\n");
            }
            String ts = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss", Locale.US).format(new Date());
            float calPitch = rawPitch - tarePitch;
            float mmPerMeter = (float) (Math.tan(Math.toRadians(Math.abs(calPitch))) * 1000.0);
            int estFloor = Math.round(relativeHeightMeters / 3.0f) + 1;

            fw.append(String.format(Locale.US, "%s,%.5f,%.5f,%.1f,%.1f,%.2f,%.1f,%.0f,%.2f,%d\n",
                    ts, latitude, longitude, camAzimuth, camAltitude, calPitch, mmPerMeter,
                    currentLux, relativeHeightMeters, estFloor));
            fw.flush();
            fw.close();
            Toast.makeText(this, "Сохранено в Download/BIM_Field_Log.csv", Toast.LENGTH_LONG).show();
        } catch (Exception e) {
            Toast.makeText(this, "Ошибка записи: " + e.getMessage(), Toast.LENGTH_SHORT).show();
        }
    }

    @Override
    public void surfaceCreated(SurfaceHolder holder) { startCameraPreview(); }

    @Override
    public void surfaceChanged(SurfaceHolder holder, int format, int width, int height) {}

    @Override
    public void surfaceDestroyed(SurfaceHolder holder) {
        if (camera != null) {
            camera.stopPreview();
            camera.release();
            camera = null;
        }
    }

    private void startCameraPreview() {
        try {
            if (checkSelfPermission(Manifest.permission.CAMERA) != PackageManager.PERMISSION_GRANTED) return;
            if (camera == null) camera = Camera.open();
            if (camera != null) {
                camera.setDisplayOrientation(90);
                camera.setPreviewDisplay(cameraSurface.getHolder());
                camera.startPreview();
            }
        } catch (Exception ignored) {}
    }

    // Кастомный слой AR-графики и цифрового нивелира
    private class AROverlayView extends View {
        private final Paint paint = new Paint(Paint.ANTI_ALIAS_FLAG);
        private final Path path = new Path();

        public AROverlayView(Context context) { super(context); }

        @Override
        protected void onDraw(Canvas canvas) {
            super.onDraw(canvas);
            int w = getWidth();
            int h = getHeight();
            float cx = w / 2f;
            float cy = h / 2f;

            float fovH = 60f;
            float fovV = 75f;

            // 1. Линия горизонта в AR
            float horizonY = cy + (camAltitude / fovV) * h;
            paint.setColor(Color.argb(150, 0, 255, 180));
            paint.setStrokeWidth(3f);
            canvas.drawLine(0, horizonY, w, horizonY, paint);

            String[] dirs = {"С (0°)", "СВ", "В (90°)", "ЮВ", "Ю (180°)", "ЮЗ", "З (270°)", "СЗ"};
            paint.setTextSize(32f);
            for (int i = 0; i < 8; i++) {
                float dirAz = i * 45f;
                float x = azimuthToScreenX(dirAz, w, fovH);
                if (x >= -50 && x <= w + 50) {
                    canvas.drawCircle(x, horizonY, 8f, paint);
                    canvas.drawText(dirs[i], x - 40f, horizonY - 16f, paint);
                }
            }

            // 2. Дуги Солнца (Зима, Лето и выбранная дата)
            drawSunArc(canvas, w, h, fovH, fovV, 355, Color.argb(140, 100, 180, 255), false);
            drawSunArc(canvas, w, h, fovH, fovV, 172, Color.argb(140, 255, 120, 80), false);
            drawSunArc(canvas, w, h, fovH, fovV, selectedDayOfYear, Color.rgb(255, 230, 0), true);

            // 3. Цифровой 2D-нивелир (мишень в центре)
            float calPitch = rawPitch - tarePitch;
            float calRoll = rawRoll - tareRoll;
            float levelRadius = 110f;
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
            canvas.drawCircle(bx, by, 22f, paint);

            // 4. Верхняя приборная панель
            paint.setColor(Color.argb(190, 15, 20, 28));
            canvas.drawRoundRect(new RectF(20, 30, w - 20, 390), 24f, 24f, paint);

            paint.setColor(Color.WHITE);
            paint.setTextSize(34f);
            canvas.drawText(String.format(Locale.US, "Азимут: %.1f° (%s) | Луч: %.1f°",
                    camAzimuth, getCardinal(camAzimuth), camAltitude), 45, 80, paint);

            float slopePercent = (float) (Math.tan(Math.toRadians(Math.abs(calPitch))) * 100.0);
            float slopeMmM = slopePercent * 10f;
            paint.setColor(isLevel ? Color.GREEN : Color.rgb(255, 215, 80));
            canvas.drawText(String.format(Locale.US, "Уклон: %.1f° | %.1f%% | %.0f мм/м (Крен: %.1f°)",
                    calPitch, slopePercent, slopeMmM, calRoll), 45, 135, paint);

            int estFloor = Math.round(relativeHeightMeters / 3.0f) + 1;
            paint.setColor(Color.rgb(130, 220, 255));
            canvas.drawText(String.format(Locale.US, "Отметка ΔH: %+.2f м (~%d эт.) | %.1f гПа",
                    relativeHeightMeters, estFloor, currentPressure), 45, 190, paint);

            paint.setColor(Color.rgb(200, 255, 160));
            canvas.drawText(String.format(Locale.US, "Свет: %.0f лк (%s)",
                    currentLux, evaluateLuxNorm(currentLux)), 45, 245, paint);

            int sunHours = calculateDaylightHours(latitude, selectedDayOfYear);
            paint.setColor(Color.rgb(255, 230, 100));
            canvas.drawText("Инсоляция: " + selectedSeasonLabel + " (~" + sunHours + " ч света)", 45, 300, paint);

            paint.setTextSize(28f);
            paint.setColor(Color.LTGRAY);
            String gpsText = gpsLocked ? "GPS точный" : "GPS по умолчанию (Рязань/ЦФО)";
            canvas.drawText(String.format(Locale.US, "Коорд: %.3f N, %.3f E [%s]", latitude, longitude, gpsText), 45, 355, paint);
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
                    paint.setStyle(Paint.Style.FILL);
                    canvas.drawCircle(sx, sy, 12f, paint);
                    paint.setTextSize(28f);
                    canvas.drawText(((int) hr) + ":00", sx - 25f, sy - 18f, paint);
                    paint.setStyle(Paint.Style.STROKE);
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

        private int calculateDaylightHours(double lat, int day) {
            int count = 0;
            for (int hr = 4; hr <= 22; hr++) {
                if (computeSunPosition(lat, day, hr)[1] > 0) count++;
            }
            return count;
        }
    }
}
