@echo off
setlocal
cd /d "%~dp0"
:: Auto-elevate (so the build can stop a running elevated ClientManager.exe)
>nul 2>&1 "%SYSTEMROOT%\system32\cacls.exe" "%SYSTEMROOT%\system32\config\system"
if '%errorlevel%' NEQ '0' goto UACPrompt
goto GotAdmin

:UACPrompt
echo Set UAC = CreateObject("Shell.Application") > "%temp%\getadmin.vbs"
echo UAC.ShellExecute "%~s0", "", "", "runas", 1 >> "%temp%\getadmin.vbs"
"%temp%\getadmin.vbs"
del "%temp%\getadmin.vbs"
exit /B

:GotAdmin
cd /d "%~dp0"

taskkill /f /im ClientManager.exe >nul 2>&1
timeout /t 1 /nobreak >nul

:: Clean PATH so a stray link.exe (e.g. from Git) cannot hijack the MSVC linker
set "PATH=%SystemRoot%\system32;%SystemRoot%;%SystemRoot%\System32\Wbem;%SystemRoot%\System32\WindowsPowerShell\v1.0\"

set "VSDEV="
for %%E in (Community Professional Enterprise BuildTools Preview) do if not defined VSDEV if exist "%ProgramFiles%\Microsoft Visual Studio\2022\%%E\Common7\Tools\VsDevCmd.bat" set "VSDEV=%ProgramFiles%\Microsoft Visual Studio\2022\%%E\Common7\Tools\VsDevCmd.bat"
if defined VSDEV goto :havevs
set "VSW=%ProgramFiles(x86)%\Microsoft Visual Studio\Installer\vswhere.exe"
if exist "%VSW%" for /f "usebackq delims=" %%I in (`"%VSW%" -latest -products * -requires Microsoft.VisualStudio.Component.VC.Tools.x86.x64 -property installationPath`) do set "VSDEV=%%I\Common7\Tools\VsDevCmd.bat"
:havevs
if not defined VSDEV goto :novs
if not exist "%VSDEV%" goto :novs

echo Loading Visual Studio x64 C++ environment...
call "%VSDEV%" -arch=x64 -host_arch=x64 >nul

set "RESFILE="
if exist ClientManager.rc (
    rc.exe /nologo ClientManager.rc
    if exist ClientManager.res set "RESFILE=ClientManager.res"
)

echo Compiling ClientManager.cpp (x64, static runtime, UAC manifest) ...
cl.exe /nologo /O2 /MT /EHsc /utf-8 /W3 ClientManager.cpp %RESFILE% user32.lib gdi32.lib shell32.lib advapi32.lib winmm.lib /link /OUT:ClientManager.exe /SUBSYSTEM:WINDOWS /MACHINE:X64 /MANIFEST:EMBED /MANIFESTUAC:"level='requireAdministrator' uiAccess='false'"
set "BUILDRC=%ERRORLEVEL%"
del ClientManager.obj ClientManager.res >nul 2>&1
if not "%BUILDRC%"=="0" goto :failed

echo [Success] ClientManager.exe build complete.
:: Un-freeze the game in case the old tool was killed in the middle of a CPU-limit cycle
ClientManager.exe /resume
pause
exit /b 0

:novs
echo [Error] Visual Studio 2022 C++ build tools (Desktop development with C++) not found!
pause
exit /b 1

:failed
echo [Error] Build failed! Please send the error lines above.
pause
exit /b 1
