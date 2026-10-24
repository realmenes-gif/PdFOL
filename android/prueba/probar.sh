#!/bin/bash
# Prueba en el emulador: instala, abre PdFOL, abre un PDF con «Abrir con» y saca capturas.
set -x
APK="$1"; OUT="$2"; mkdir -p "$OUT"
adb wait-for-device
adb shell settings put global window_animation_scale 0
adb shell settings put global transition_animation_scale 0
adb shell settings put global animator_duration_scale 0
adb install -r "$APK" || exit 1
adb shell am start -W -n com.meneses999.pdfol/.MainActivity
sleep 12
adb exec-out screencap -p > "$OUT/1_inicio.png"
adb push android/prueba/prueba.pdf /sdcard/Download/prueba.pdf
adb shell content call --uri content://media --method scan_volume --arg external_primary || true
sleep 3
ID=$(adb shell content query --uri content://media/external/file --projection _id --where "_display_name=\'prueba.pdf\'" | grep -oE "_id=[0-9]+" | head -1 | cut -d= -f2)
echo "ID=$ID"
adb shell am start -W -a android.intent.action.VIEW -d "content://media/external/file/$ID" -t application/pdf --grant-read-uri-permission -n com.meneses999.pdfol/.MainActivity
sleep 14
adb exec-out screencap -p > "$OUT/2_documento.png"
# buscar con el teclado: toca la lupa (arriba a la derecha) no es fiable por coordenadas: se usa la tecla de busqueda
# pagina escaneada: reconocer texto (OCR)
adb push android/prueba/escaneado.pdf /sdcard/Download/escaneado.pdf
adb shell content call --uri content://media --method scan_volume --arg external_primary || true
sleep 3
ID2=$(adb shell content query --uri content://media/external/file --projection _id --where "_display_name=\'escaneado.pdf\'" | grep -oE "_id=[0-9]+" | head -1 | cut -d= -f2)
adb shell am start -W -a android.intent.action.VIEW -d "content://media/external/file/$ID2" -t application/pdf --grant-read-uri-permission -n com.meneses999.pdfol/.MainActivity
sleep 30
adb exec-out screencap -p > "$OUT/2b_escaneado.png"
sleep 30
adb exec-out screencap -p > "$OUT/2c_escaneado.png"
adb logcat -d | grep -E "PdFOL OCR" | tail -5
adb shell input keyevent KEYCODE_BACK
sleep 2
adb shell input keyevent KEYCODE_BACK
sleep 3
adb exec-out screencap -p > "$OUT/3_atras.png"
adb shell input keyevent KEYCODE_HOME
adb shell cmd uimode night yes
sleep 2
adb shell am start -W -a android.intent.action.VIEW -d "content://media/external/file/$ID" -t application/pdf --grant-read-uri-permission -n com.meneses999.pdfol/.MainActivity
sleep 12
adb exec-out screencap -p > "$OUT/4_oscuro.png"
adb shell wm size 1600x2560; adb shell wm density 320
sleep 6
adb exec-out screencap -p > "$OUT/5_tablet.png"
adb logcat -d | grep -iE "pdfol|AndroidRuntime|FATAL|mlkit|vision|TextRecognizer|DynamiteModule|ModuleInstall" | tail -400 > "$OUT/log.txt"
ls -la "$OUT"
