SCONS=$(cygpath -d "$(dirname `which scons.bat`)/scons.py")
PYTHON=$(cygpath -d "$(dirname `which scons.bat`)/python.exe")
"${PYTHON}" "${SCONS}" $*
