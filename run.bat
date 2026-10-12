@echo off
chcp 65001 >nul
cd /d "%~dp0"
echo.
where py >nul 2>nul
if %errorlevel%==0 goto RUNPY
where python >nul 2>nul
if %errorlevel%==0 goto RUNPYTHON
echo Python not found. Install it first:
echo     winget install -e --id Python.Python.3.12
echo.
pause
exit /b 1
:RUNPY
py pmk.py %*
if errorlevel 1 pause
exit /b
:RUNPYTHON
python pmk.py %*
if errorlevel 1 pause
