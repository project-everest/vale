@echo off
rem Run this from a 32-bit VS command window

setlocal
set ROOT=%~dp0..\..\..\..
set TEST=%ROOT%\tools\Vale\obj
rem set OPENSSL_ROOT=c:\OpenSSL-Win32
set OPENSSL_ROOT=c:\Users\barrybo\Downloads\openssl\openssl-1.1.0

cd /d %TEST%

rem compile this __cdecl so it can call OpenSSL code
cl.exe /nologo /c /Ox /Zi /Gd /LD %ROOT%\src\Libraries\Crypto\hashing\EverestSha256.c /I %ROOT%\tools\Kremlin\kremlib /I %TEST% /I %OPENSSL_ROOT%\include

rem compile these __stdcall so they can call Vale crypto code
cl.exe /nologo /c /Ox /Zi /Gz /LD sha256_main_i.c %ROOT%\src\Libraries\Crypto\hashing\EverestSHA256Glue.c /I %ROOT%\tools\Kremlin\kremlib /I %TEST% /I %OPENSSL_ROOT%\include /I %ROOT%\src\Libraries\Util

rem link it all together
cl.exe /nologo /Ox /Zi /Gd /LD EverestSha256.obj EverestSha256Glue.obj sha256_main_i.obj sha256.obj cbc.obj %OPENSSL_ROOT%\libcrypto.lib
if errorlevel 1 echo cl.exe failed! && goto :EOF

echo Built %TEST%\EverestSha256.dll successfully.
echo.
echo From an OpenSSL prompt, enter:
echo engine %TEST%\EverestSha256.dll
echo speed -engine Everest -evp sha256
echo speed -engine Everest -evp aes-128-cbc
echo dgst -engine Everest %~f0