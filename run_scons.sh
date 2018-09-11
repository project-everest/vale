#!/bin/bash

# Platform-independent invocation of SCons
# Inspired from the Everest script

set -e

SCONS_PYTHON_MAJOR_MINOR=3.6

# Windows-only: print out the directory of the Python associated to SCons
windows_scons_python_dir () {
    PYDIR=$(regtool -q get "/HKLM/Software/Python/PythonCore/$SCONS_PYTHON_MAJOR_MINOR/InstallPath/" || true)
    if ! [[ -d $PYDIR ]] ; then
      PYDIR=$(regtool -q get "/HKCU/Software/Python/PythonCore/$SCONS_PYTHON_MAJOR_MINOR/InstallPath/" || true)
    fi
    if ! [[ -d $PYDIR ]] ; then
      echo "ERROR: Python $SCONS_PYTHON_MAJOR_MINOR was not installed properly" >&2
      exit 1
    fi
    echo "$PYDIR"
}

windows_setup_environment () {
    # Determine the command line to set up the Visual Studio environment (VS_ENV_CMD)
    # Starting from Visual Studio 2017, version 15.2 or later,
    # we can determine the location of a VS install
    # using vswhere.exe, see:
    # https://docs.microsoft.com/en-us/visualstudio/extensibility/locating-visual-studio
    if
        VSWHERE_WINDOWS="$(cmd.exe /C 'echo %ProgramFiles(x86)%\Microsoft Visual Studio\Installer\vswhere.exe' | sed 's!\r!!g')" &&
            VSWHERE=$(cygpath -u "$VSWHERE_WINDOWS") &&
            VS_HOME=$("$VSWHERE" -requires Microsoft.VisualStudio.Component.FSharp -format value -property InstallationPath | sed 's!\r!!g') &&
            [[ -n "$VS_HOME" ]]
    then
        # Visual Studio 2017 (15.2) or later
        # vcvarsall.bat has been superseded by vsdevcmd.bat, see:
        # https://docs.microsoft.com/en-us/dotnet/csharp/language-reference/compiler-options/how-to-set-environment-variables-for-the-visual-studio-command-line
        VSDEVCMD_PATH=$(cygpath -u "$VS_HOME")/Common7/Tools
        VSDEVCMD=$(cygpath -w "$VSDEVCMD_PATH/VsDevCmd.bat")
        # Here we assume that BOTH the target platform
        # and the host platform are amd64.
        VS_ENV_CMD='"'"$VSDEVCMD"'" -arch=amd64 -host_arch=amd64'
    else
        # Older versions are based on vcvarsall.bat
        if [[ -v VS140COMNTOOLS ]]; then
            # Visual Studio 2015 (14.x)
            VS_TOOLS_PATH="$VS140COMNTOOLS"
        elif [[ -v VS120COMNTOOLS ]]; then
            # Visual Studio 2012 (12.x)
            VS_TOOLS_PATH="$VS120COMNTOOLS"
        elif [[ -v VS110COMNTOOLS ]]; then
            # Visual Studio 2010 (10.x)
            VS_TOOLS_PATH="$VS110COMNTOOLS"
        else
            # Not found
            echo Could not find Visual Studio >&2
            exit 1
        fi
        VCVARSALL_PATH="$VS_TOOLS_PATH"/../../VC
        VCVARSALL=$(cygpath -d "$VCVARSALL_PATH/vcvarsall.bat")
        # Here we assume that BOTH the target platform
        # and the host platform are amd64.
        VS_ENV_CMD="$VCVARSALL amd64"
    fi
    echo "$VS_ENV_CMD"
}

is_windows () {
  [[ $OS == "Windows_NT" ]]
}

if is_windows ; then
    VS_ENV_CMD=$(windows_setup_environment)
    pydir=$(windows_scons_python_dir)

    # Instead of invoking cmd.exe /c, which would force us to
    # rely on its flaky semantics for double quotes,
    # we go through a batch file.
    THIS_PID=$$
    # Find an unambiguous file name for our .bat file
    SCONS_EXECS=0
    while
      SCONS_INVOKE_FILE="vale$THIS_PID""scons$SCONS_EXECS"".bat" &&
      [[ -e "$SCONS_INVOKE_FILE" ]]
    do
      SCONS_EXECS=$(($SCONS_EXECS + 1))
    done
    # Then create, run and remove the .bat file
    cat > "$SCONS_INVOKE_FILE" <<EOF
call $VS_ENV_CMD
EOF
    if command -v scons.bat > /dev/null 2>&1 ; then
      echo "call scons.bat $cmd $parallel_opt" >> "$SCONS_INVOKE_FILE"
    else
      PYDIR=$(cygpath -d $(windows_scons_python_dir))
      echo "$PYDIR/python.exe $PYDIR/Scripts/scons.py $*" >> "$SCONS_INVOKE_FILE"
    fi
    chmod +x "$SCONS_INVOKE_FILE"
    "./$SCONS_INVOKE_FILE"
    SCONS_RETCODE=$?
    rm -f "$SCONS_INVOKE_FILE"
    return $SCONS_RETCODE
else
    python$SCONS_PYTHON_MAJOR_MINOR $(which scons) "$@"
fi
