@echo off
chcp 65001 >nul
title Quality Dental V8.5
cd /d "%~dp0"
echo ============================================
echo       Quality Dental V8.5 - Starting
echo ============================================
where py >nul 2>nul
if %errorlevel%==0 (
  py -m pip install -r requirements.txt
  py run.py
) else (
  where python >nul 2>nul
  if %errorlevel%==0 (
    python -m pip install -r requirements.txt
    python run.py
  ) else (
    echo Python is not installed or not in PATH.
    echo Install Python from python.org and enable Add Python to PATH.
    pause
  )
)
pause
