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
    PYDIR=$(cygpath -u "$PYDIR")
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
    pydir_w=$(cygpath -d "$pydir")

    # Instead of invoking cmd.exe /c, which would force us to
    # rely on its flaky semantics for double quotes,
    # we go through a batch file.

    # The problem is that, if we run scons directly from within the
    # .bat file (or, even worse, call scons.bat), then it will not
    # capture UNIX signals (CTRL+C, etc.) So we need to go "back to
    # Cygwin": create a .sh file, and have the .bat file call bash
    # with the .sh file, and have the .sh file call python with scons.py
    # instead of calling scons.bat.

    # This detour through a .bat file is necessary because of
    # vcvarsall.bat, which is called to change the caller's
    # environment, which only works from a .bat file, and not from a
    # bash script or python script.

    THIS_PID=$$
    # Find an unambiguous file name for our .bat file
    SCONS_EXECS=0
    while
      SCONS_INVOKE_FILE_BASENAME="vale$THIS_PID""scons$SCONS_EXECS" && {
      [[ -e "$SCONS_INVOKE_FILE_BASENAME.bat" ]] ||
      [[ -e "$SCONS_INVOKE_FILE_BASENAME.err" ]] ||
      [[ -e "$SCONS_INVOKE_FILE_BASENAME.sh" ]]
    }
    do
      SCONS_EXECS=$(($SCONS_EXECS + 1))
    done
    # Then create, run and remove the .bat file
    cat > "$SCONS_INVOKE_FILE_BASENAME.bat" <<EOF
call $VS_ENV_CMD
C:\cygwin64\bin\bash.exe $SCONS_INVOKE_FILE_BASENAME.sh
EOF
    # TODO: convert arguments to scons to windows paths.
    echo "$pydir/python.exe '$pydir_w\\Scripts\\scons.py' $*" > "$SCONS_INVOKE_FILE_BASENAME.sh"
    echo "echo "'$'"? > $SCONS_INVOKE_FILE_BASENAME.err" >> "$SCONS_INVOKE_FILE_BASENAME.sh"
    chmod +x "$SCONS_INVOKE_FILE_BASENAME.bat"
    "./$SCONS_INVOKE_FILE_BASENAME.bat"
    SCONS_RETCODE=$(cat "$SCONS_INVOKE_FILE_BASENAME.err")
    echo "Return code is: $SCONS_RETCODE"
    rm -f "$SCONS_INVOKE_FILE_BASENAME.bat" "$SCONS_INVOKE_FILE_BASENAME.sh" "$SCONS_INVOKE_FILE_BASENAME.err"
    exit $SCONS_RETCODE
else
    python$SCONS_PYTHON_MAJOR_MINOR $(which scons) "$@"
fi
