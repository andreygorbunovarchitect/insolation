    @Override
    public void onRequestPermissionsResult(int requestCode, String[] permissions, int[] grantResults) {
        if (requestCode == 101) {
            boolean camGranted = false;
            for (int i = 0; i < permissions.length; i++) {
                if (permissions[i].equals(Manifest.permission.CAMERA) && grantResults[i] == PackageManager.PERMISSION_GRANTED) {
                    camGranted = true;
                }
            }
            if (camGranted) {
                startLocationUpdates();
                if (cameraSurface.getHolder().getSurface().isValid()) {
                    startCameraPreview(cameraSurface.getHolder());
                }
            } else {
                Toast.makeText(this, "Требуется разрешение на камеру для AR!", Toast.LENGTH_LONG).show();
            }
        }
    }

    @Override
    public void surfaceCreated(SurfaceHolder holder) {
        if (checkSelfPermission(Manifest.permission.CAMERA) == PackageManager.PERMISSION_GRANTED) {
            startCameraPreview(holder);
        }
    }

    @Override
    public void surfaceChanged(SurfaceHolder holder, int format, int width, int height) {
        // Контроль изменения размеров поверхности
    }

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
                
                // Автоматическое включение вспышки (фонарика) для подсветки в темноте
                Camera.Parameters params = camera.getParameters();
                if (params.getSupportedFlashModes() != null && 
                    params.getSupportedFlashModes().contains(Camera.Parameters.FLASH_MODE_TORCH)) {
                    params.setFlashMode(Camera.Parameters.FLASH_MODE_TORCH);
                }
                camera.setParameters(params);
                
                camera.startPreview();
            }
        } catch (Exception e) {
            Toast.makeText(this, "Ошибка запуска камеры: " + e.getMessage(), Toast.LENGTH_SHORT).show();
        }
    }
