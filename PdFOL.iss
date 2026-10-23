; Instalador de PdFOL (Inno Setup 6). Lo arma crear_portable.bat (paso 4) a partir de la carpeta PdFOL_portable.
; Se instala SOLO para el usuario (no pide administrador), en %LOCALAPPDATA%\Programs\PdFOL,
; con acceso en el menu Inicio, desinstalador y PdFOL en «Abrir con» para los PDF.
#ifndef MiVersion
  #define MiVersion "2.4"
#endif

[Setup]
AppId={{6C2E8B3A-41D7-4F5C-9A6E-3D0F5C1B2A20}
AppName=PdFOL
AppVersion={#MiVersion}
AppVerName=PdFOL v{#MiVersion}
AppPublisher=PdFOL
DefaultDirName={localappdata}\Programs\PdFOL
DefaultGroupName=PdFOL
DisableProgramGroupPage=yes
DisableDirPage=auto
PrivilegesRequired=lowest
OutputDir=.
OutputBaseFilename=PdFOL_v{#MiVersion}_instalador
SetupIconFile=PdFOL.ico
UninstallDisplayIcon={app}\PdFOL.exe
UninstallDisplayName=PdFOL
Compression=lzma2/max
SolidCompression=yes
WizardStyle=modern
ChangesAssociations=yes
CloseApplications=yes
RestartApplications=no

[Languages]
Name: "es"; MessagesFile: "compiler:Languages\Spanish.isl"

[Tasks]
Name: "escritorio"; Description: "Crear un acceso directo en el escritorio"; GroupDescription: "Accesos:"
Name: "pdf"; Description: "Ofrecer PdFOL para abrir los PDF (aparece en «Abrir con»)"; GroupDescription: "Archivos PDF:"

[Files]
; los perfiles del usuario nunca se pisan
Source: "PdFOL_portable\*"; DestDir: "{app}"; Excludes: "PdFOL_perfiles.json"; Flags: recursesubdirs createallsubdirs ignoreversion

[Icons]
Name: "{autoprograms}\PdFOL"; Filename: "{app}\PdFOL.exe"
Name: "{autodesktop}\PdFOL"; Filename: "{app}\PdFOL.exe"; Tasks: escritorio

[Registry]
; tipo de archivo de PdFOL para los PDF
Root: HKCU; Subkey: "Software\Classes\PdFOL.PDF"; ValueType: string; ValueData: "Documento PDF"; Flags: uninsdeletekey; Tasks: pdf
Root: HKCU; Subkey: "Software\Classes\PdFOL.PDF\DefaultIcon"; ValueType: string; ValueData: "{app}\PdFOL_documento.ico"; Tasks: pdf
Root: HKCU; Subkey: "Software\Classes\PdFOL.PDF\shell\open\command"; ValueType: string; ValueData: """{app}\PdFOL.exe"" ""%1"""; Tasks: pdf
Root: HKCU; Subkey: "Software\Classes\.pdf\OpenWithProgids"; ValueType: string; ValueName: "PdFOL.PDF"; ValueData: ""; Flags: uninsdeletevalue; Tasks: pdf
Root: HKCU; Subkey: "Software\Classes\Applications\PdFOL.exe"; ValueType: string; ValueName: "FriendlyAppName"; ValueData: "PdFOL"; Flags: uninsdeletekey; Tasks: pdf
Root: HKCU; Subkey: "Software\Classes\Applications\PdFOL.exe\shell\open\command"; ValueType: string; ValueData: """{app}\PdFOL.exe"" ""%1"""; Tasks: pdf
Root: HKCU; Subkey: "Software\Classes\Applications\PdFOL.exe\SupportedTypes"; ValueType: string; ValueName: ".pdf"; ValueData: ""; Tasks: pdf
; registro como aplicacion (asi aparece en «Aplicaciones predeterminadas» de Windows)
Root: HKCU; Subkey: "Software\PdFOL\Capabilities"; ValueType: string; ValueName: "ApplicationName"; ValueData: "PdFOL"; Flags: uninsdeletekey; Tasks: pdf
Root: HKCU; Subkey: "Software\PdFOL\Capabilities"; ValueType: string; ValueName: "ApplicationDescription"; ValueData: "Visor de PDF que aplana, folia y comprime"; Tasks: pdf
Root: HKCU; Subkey: "Software\PdFOL\Capabilities"; ValueType: string; ValueName: "ApplicationIcon"; ValueData: "{app}\PdFOL.exe,0"; Tasks: pdf
Root: HKCU; Subkey: "Software\PdFOL\Capabilities\FileAssociations"; ValueType: string; ValueName: ".pdf"; ValueData: "PdFOL.PDF"; Tasks: pdf
Root: HKCU; Subkey: "Software\RegisteredApplications"; ValueType: string; ValueName: "PdFOL"; ValueData: "Software\PdFOL\Capabilities"; Flags: uninsdeletevalue; Tasks: pdf

[Run]
Filename: "{app}\PdFOL.exe"; Description: "Abrir PdFOL"; Flags: nowait postinstall skipifsilent
