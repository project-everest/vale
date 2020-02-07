# Using the Vale binary release (recommended)

The [Vale binary release](https://github.com/project-everest/vale/releases) relies on the following tools:

* .NET (included in Windows) or mono (Unix)
  * On an Ubuntu system, including Windows Subsystem for Linux, you can install mono with:
    ```sudo apt install mono-devel```
  * On Mac OS X (tested with El Capitan, 10.11.6), you can install mono with:
    ```brew install mono```
* Z3, used by F* and Dafny
  * See https://github.com/FStarLang/binaries/tree/master/z3-tested

To install the binary release, unzip the latest vale-release-*.zip file from [here](https://github.com/project-everest/vale/releases).
Then either add the z3 binary to your path or to the unzipped Vale bin directory.

## Testing the Vale binary release

To test the binary release, download [this test file](https://raw.githubusercontent.com/project-everest/vale/master/tools/Vale/test/refined3.vad),
then run:

* On Windows:
  * ```bin/vale.exe -in refined3.vad -out refined3.dfy```
  * ```bin/Dafny.exe /trace refined3.dfy```
* On Unix:
  * ```mono bin/vale.exe -in refined3.vad -out refined3.dfy```
  * ```mono bin/Dafny.exe /trace refined3.dfy```

If you have [F*](https://github.com/FStarLang/FStar) installed,
you can also download [this test file](https://raw.githubusercontent.com/project-everest/vale/master/tools/Vale/test/common.vaf),
then run:

* On Windows:
  * ```bin/vale.exe -fstarText -in common.vaf -out common.fst -outi common.fsti```
  * ```fstar.exe --query_stats common.fst```
* On Unix:
  * ```mono bin/vale.exe -fstarText -in common.vaf -out common.fst -outi common.fsti```
  * ```fstar.exe --query_stats common.fst```

# Building Vale from source

Vale sources rely on the following tools, which must be installed before building Vale:

* Python (version >= 3.6), used by SCons
  * See https://www.python.org/
* SCons (version >= 3.00), the Python-based build system used by Vale
  * See http://scons.org/
* F\# (version >= 4.0), including [FsLexYacc](http://fsprojects.github.io/FsLexYacc/).  Vale is written in F\#.
  * See http://fsharp.org/ for complete information, including free versions for Windows, Mac, and Linux.
  * FsLexYacc is installed via nuget.exe; see [nuget](https://www.nuget.org/), under "latest nuget.exe"
    * In the Vale root directory, run the command `nuget.exe restore ./tools/Vale/src/packages.config -PackagesDirectory tools/FsLexYacc`
    * This will create a directory tools/FsLexYacc that contains the FsLexYacc binaries; the build will expect to find these binaries in tools/FsLexYacc
* C\#, used by [Dafny](https://github.com/Microsoft/dafny/blob/master/INSTALL)
  * See https://www.visualstudio.com/vs/community/ or http://www.mono-project.com/
* Z3, used by F* and Dafny
  * See https://github.com/FStarLang/binaries/tree/master/z3-tested

On an Ubuntu system, including Windows Subsystem for Linux, you can install the dependencies with:
     ```sudo apt install scons fsharp nuget mono-devel```.

On Mac OS X (tested with El Capitan, 10.11.6), you can install the dependencies with:
    ```brew install scons nuget mono```.
Note that the mono package includes F\#.

Once these tools are installed, running SCons in the top-level directory will build the Vale tool:

```python.exe scons.py```

To verify all Dafny sources in the [src](./src) directory, run:

```python.exe scons.py --DAFNY```

To verify all F* sources in the [src](./src) directory (this requires an installation of [F*](https://github.com/FStarLang/FStar)), run:

```python.exe scons.py --FSTAR```

NOTE: You can override tools/Kremlin by setting the KREMLIN_HOME
environment variable to point to the directory where KreMLin is
installed.
