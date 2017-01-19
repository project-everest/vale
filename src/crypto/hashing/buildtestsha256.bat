@echo off
setlocal
set ROOT=%~dp0..\..\..\..
set TEST=%ROOT%\tools\Vale\obj\test
set VALE=%ROOT%\tools\Vale\bin\Vale.exe
set KREMLIN=%ROOT%\Kremlin\kremlin.native
set DAFNY=%ROOT%\tools\Dafny\Dafny.exe

cd /d %TEST%

rem build the Dafny parts
if exist %ROOT%\src\Libraries\Util\types.s.old del %ROOT%\src\Libraries\Util\types.s.old
copy /y %ROOT%\src\Libraries\Util\types.s.dfy %ROOT%\src\Libraries\Util\types.s.old
copy /y %ROOT%\src\Libraries\Util\types.s.dfy.kremlin %ROOT%\src\Libraries\Util\types.s.dfy
%DAFNY% /nologo /kremlin /noVerify /compile:2 /spillTargetCode 1 %ROOT%\src\Libraries\Crypto\hashing\sha256_main.i.dfy /out:%TEST%\sha256_main.i.json
rem if errorlevel 1 echo Dafny failed! && goto :EOF
copy /y %ROOT%\src\Libraries\Util\types.s.old %ROOT%\src\Libraries\Util\types.s.dfy
del %ROOT%\src\Libraries\Util\types.s.old

%KREMLIN% %TEST%\sha256_main.i.json -warn-error +1..4 -skip-compilation
if errorlevel 1 echo Kremlin failed! && goto :EOF
rem we now have %TEST%\sha256_main_i.c and %TEST%\sha256_main_i.h

rem build the Vale parts
cd %ROOT%\tools\Vale
nmake refine
if errorlevel 1 echo Make Refine failed && goto :EOF
cd %TEST%
sha256-refined.exe > sha256-refined.asm
ml.exe /nologo /c /Zi sha256-refined.asm /Fosha256-refined.obj
if errorlevel 1 echo sha256-refined failed! && goto :EOF

rem build the test exe
cl.exe /nologo /Ox /Zi /Gz %ROOT%\src\Libraries\Crypto\hashing\testsha256.c sha256_main_i.c sha256-refined.obj /I %ROOT%\Kremlin\kremlib /I %TEST%
if errorlevel 1 echo cl.exe failed! && goto :EOF

echo Built %TEST%\testsha256.exe successfully.  Running it:
%TEST%\testsha256.exe