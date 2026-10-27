@echo off
if not "%~1"=="_abierto" (
    cmd /k ""%~f0" _abierto"
    exit /b
)
chcp 65001 >nul
setlocal
cd /d "%~dp0"
title Creando PdFOL v2.5 portable

echo.
echo  ==========================================================
echo    Creando la version PORTABLE de PdFOL v2.5
echo    (solo se hace una vez; tarda unos minutos)
echo  ==========================================================
echo.

where python >nul 2>nul
if errorlevel 1 (
    echo  No se encontro Python. Instalalo desde https://www.python.org/downloads/
    echo  y marca la casilla "Add python.exe to PATH" durante la instalacion.
    echo.
    goto :fin
)

python -c "import sys; sys.exit(0 if sys.maxsize > 2**32 else 1)"
if errorlevel 1 (
    echo  Tu Python es de 32 bits. Instala Python de 64 bits desde python.org.
    goto :fin
)

python -c "import tkinter" 2>nul
if errorlevel 1 (
    echo  A tu Python le falta "tcl/tk". Reinstala Python desde python.org
    echo  dejando marcada la opcion "tcl/tk and IDLE".
    goto :fin
)

if not exist "PdFOL_v2.5.py" (
    echo  No encuentro PdFOL_v2.5.py en esta carpeta.
    echo  Descomprimi el .zip completo y ejecuta este .bat desde esa carpeta.
    goto :fin
)
if not exist "PdFOL.iss" (
    echo  No encuentro PdFOL.iss junto a este .bat.
    echo  Descomprimi el .zip completo y ejecuta este .bat desde esa carpeta.
    goto :fin
)
if not exist "PdFOL.ico" (
    echo  No encuentro el icono PdFOL.ico junto a este .bat.
    echo  Descomprimi el .zip completo y ejecuta este .bat desde esa carpeta.
    goto :fin
)
if not exist "fuentes\SpecialElite-Regular.ttf" (
    echo  No encuentro la carpeta "fuentes" junto a este .bat.
    echo  Descomprimi el .zip completo, que incluye la carpeta fuentes.
    goto :fin
)

echo [1/4] Instalando herramientas (PyMuPDF, pikepdf, Pillow, CustomTkinter, PyInstaller)...
rem Versiones fijas: las probadas con PdFOL (PyMuPDF 2 y CustomTkinter 6 cambian demasiado)
python -m pip install --upgrade --quiet --disable-pip-version-check "pymupdf>=1.24,<2" pikepdf pillow "customtkinter>=5.2,<6" tkinterdnd2 pyinstaller
if errorlevel 1 (
    echo  Error instalando las librerias. Revisa tu conexion a internet.
    goto :fin
)

echo [2/4] Armando el programa (puede tardar 2 a 5 minutos)...
python -m PyInstaller --noconfirm --clean --windowed --onedir ^
    --name PdFOL ^
    --icon "%~dp0PdFOL.ico" ^
    --collect-all pymupdf ^
    --collect-all pikepdf ^
    --collect-all customtkinter ^
    --collect-all tkinterdnd2 ^
    --hidden-import PIL._tkinter_finder ^
    --hidden-import PIL.ImageTk ^
    --hidden-import PIL.JpegImagePlugin ^
    --hidden-import PIL.PngImagePlugin ^
    --hidden-import PIL.IcoImagePlugin ^
    --hidden-import PIL.BmpImagePlugin ^
    --add-data "%~dp0fuentes;fuentes" ^
    --distpath "%~dp0_dist" --workpath "%~dp0_build" --specpath "%~dp0_build" ^
    PdFOL_v2.5.py
if errorlevel 1 (
    echo.
    echo  Hubo un error armando el programa. Copia el texto de arriba y envialo.
    goto :fin
)

echo [3/4] Ordenando la carpeta portable...
rem Desde la v2.0 el programa se llama PdFOL.exe (sin numero): asi se puede actualizar solo.
set "DESTINO=%~dp0PdFOL_portable"
set "PERFILES="
if exist "%DESTINO%\PdFOL_perfiles.json" (
    copy /y "%DESTINO%\PdFOL_perfiles.json" "%TEMP%\PdFOL_perfiles_respaldo.json" >nul
    set "PERFILES=1"
)
rem Si no hay perfiles todavia, se traen los de la v1.1 (si su carpeta esta al lado)
if not defined PERFILES if exist "%~dp0PdFOL_v1.1_portable\PdFOL_perfiles.json" (
    copy /y "%~dp0PdFOL_v1.1_portable\PdFOL_perfiles.json" "%TEMP%\PdFOL_perfiles_respaldo.json" >nul
    set "PERFILES=1"
)
if not defined PERFILES if exist "%~dp0..\PdFOL_v1.1\PdFOL_v1.1_portable\PdFOL_perfiles.json" (
    copy /y "%~dp0..\PdFOL_v1.1\PdFOL_v1.1_portable\PdFOL_perfiles.json" "%TEMP%\PdFOL_perfiles_respaldo.json" >nul
    set "PERFILES=1"
)
if exist "%DESTINO%" rmdir /s /q "%DESTINO%"
move "%~dp0_dist\PdFOL" "%DESTINO%" >nul
copy /y "%~dp0PdFOL_documento.ico" "%DESTINO%\PdFOL_documento.ico" >nul
if defined PERFILES copy /y "%TEMP%\PdFOL_perfiles_respaldo.json" "%DESTINO%\PdFOL_perfiles.json" >nul
rmdir /s /q "%~dp0_dist" 2>nul
rmdir /s /q "%~dp0_build" 2>nul

echo [4/4] Creando el instalador (Inno Setup, gratis)...
set "ISCC="
call :buscar_iscc
if defined ISCC goto :armar_instalador
echo  Inno Setup no esta instalado: se descarga e instala solo para tu usuario (una sola vez)...
powershell -NoProfile -ExecutionPolicy Bypass -Command "try { [Net.ServicePointManager]::SecurityProtocol = 'Tls12'; Invoke-WebRequest -UseBasicParsing 'https://jrsoftware.org/download.php/is.exe' -OutFile ($env:TEMP + '\innosetup_instalador.exe'); exit 0 } catch { exit 1 }"
if errorlevel 1 goto :sin_inno_descarga
"%TEMP%\innosetup_instalador.exe" /VERYSILENT /SUPPRESSMSGBOXES /NORESTART /SP- /CURRENTUSER
call :buscar_iscc
if defined ISCC goto :armar_instalador
winget install --id JRSoftware.InnoSetup -e --scope user --silent --accept-package-agreements --accept-source-agreements >nul 2>nul
call :buscar_iscc
if defined ISCC goto :armar_instalador
goto :sin_inno

:armar_instalador
"%ISCC%" /Q "%~dp0PdFOL.iss"
if errorlevel 1 goto :sin_instalador
set "INSTALADOR=PdFOL_v2.5_instalador.exe"
goto :listo

:sin_inno_descarga
echo  No se pudo descargar Inno Setup (revisa internet).
:sin_inno
echo  No se pudo preparar Inno Setup. El portable SI quedo listo.
echo  Para el instalador: instala Inno Setup desde https://jrsoftware.org/isdl.php
echo  y vuelve a ejecutar este .bat.
set "INSTALADOR="
goto :listo

:sin_instalador
echo  Hubo un error armando el instalador. El portable SI quedo listo.
set "INSTALADOR="
goto :listo

:listo
echo.
echo  ==========================================================
echo    LISTO
echo.
echo    PORTABLE:     carpeta PdFOL_portable  (PdFOL.exe, doble clic)
echo                  Podes copiar esa carpeta COMPLETA a una USB o
echo                  a otra PC con Windows 10/11. No necesita nada.
if defined INSTALADOR echo    INSTALADOR:   %INSTALADOR%
if defined INSTALADOR echo                  Se instala solo para el usuario (sin administrador),
if defined INSTALADOR echo                  con acceso en el menu Inicio y desinstalador.
echo  ==========================================================
echo.
explorer "%~dp0"
echo  Ya podes cerrar esta ventana.
goto :eof

:buscar_iscc
if exist "%LOCALAPPDATA%\Programs\Inno Setup 6\ISCC.exe" set "ISCC=%LOCALAPPDATA%\Programs\Inno Setup 6\ISCC.exe"
if exist "%ProgramFiles%\Inno Setup 6\ISCC.exe" set "ISCC=%ProgramFiles%\Inno Setup 6\ISCC.exe"
if exist "%ProgramFiles(x86)%\Inno Setup 6\ISCC.exe" set "ISCC=%ProgramFiles(x86)%\Inno Setup 6\ISCC.exe"
goto :eof

:fin
echo.
echo  El proceso se detuvo. Revisa el mensaje de arriba.
