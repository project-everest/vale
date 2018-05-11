SCONS=$(cygpath -d "$(dirname `which python`)/Scripts/scons.py")
python "${SCONS}" $*
