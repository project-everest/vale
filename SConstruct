# This file requires Python version >= 3.6
# This file requires SCons version >= 3.00

##################################################################################################
#
# Here are some background notes on SCons for anyone interested in reading or editing this file.
# See https://scons.org/documentation.html for more information.
#
# SCons is a build tool, like Make. Similar to Make, it builds a graph of dependencies and
# commands that should be run when files change.  However, unlike Make, SCons does not have a
# specialized language to describe the graph.  Instead, SCons runs a user-supplied Python script
# named "SConstruct" to construct the graph.  After the script completes, the SCons engine
# uses the constructed graph to analyze dependencies and run commands.  (Note that unlike Make,
# SCons's default dependency analysis uses file hashes rather than timestamps.)
#
# For example, consider the following Makefile:
#
#   b.txt : a1.txt sub/a2.txt
#       cmd1 a1.txt sub\\a2.txt > b.txt
#   c.txt : b.txt
#       cmd2 b.txt > c.txt
#
# The most direct SCons equivalent of this is the following Python code:
#
#   Command('b.txt', ['a1.txt', 'sub/a2.txt'], 'cmd1 a1.txt sub\\a2.txt > b.txt')
#   Command('c.txt', 'b.txt', 'cmd2 b.txt > c.txt')
#
# However, SCons encourages a more platform-neutral style, based on two concepts: nodes and
# environments.  For example, the code above contains a string that is hard-wired to use
# Windows-style backslashes rather than Unix-style forward slashes.  Instead of writing strings,
# SCons allows scripts to construct abstract "nodes" that can represent graph nodes such as files.
# SCons can then convert those nodes into paths with forward or backward slashes depending on
# the platform:
#
#   # First construct File nodes for each file name (using forward slashes, even on Windows):
#   a1 = File('a1.txt')
#   a2 = File('sub/a2.txt')
#   b = File('b.txt')
#   c = File('c.txt')
#   # Then let SCons convert the File nodes into strings:
#   Command(b, [a1, a2], f'cmd1 {a1} {a2} > {b}')
#   Command(c, b, f'cmd2 {b} > {c}')
#
# Scripts can say str(a1), a1.path, a1.abspath, etc. to convert a node to a string.  The code
# above uses Python's f-strings (formatted string literals) to convert nodes to strings and embed
# them into larger strings ( https://docs.python.org/3/whatsnew/3.6.html#pep-498-formatted-string-literals ).
#
# SCons encourages scripts to write functions that accept and pass nodes rather than strings
# For example, the built-in SCons object-file generator will generate an object file node, whose
# actual string representation may be "foo.o" using Unix tools or "foo.obj" using Windows tools:
#
#   foo_c = File('foo.c')
#   foo_obj = Object(foo_c)  # compile foo.c to foo.o or foo.obj
#
# (Note that "foo_obj = Object('foo.c')" is also ok, because most built-in SCons functions
# convert string names to nodes automatically.)
#
# In addition to encouraging platform independence, SCons tries to encourage independence from
# users' configurations.  In particular, by default, it executes commands in a minimal
# environment with a minimal PATH, such as ['/usr/local/bin', '/bin', '/usr/bin'] on Unix.
# The Environment function creates a new minimal environment:
#
#   env = Environment()
#
# Scripts can then customize various environments to change the PATH, change the default
# C/C++/Assembly tools, change the flags passed to various tools, etc:
#
#   env.Append(CCFLAGS=['-O3', '-flto', '-g', '-DKRML_NOUINT128', '-std=c++11'])
#   env.PrependENVPath('PATH', os.path.dirname(str(gmp_dll)))
#
# Built in top-level functions like "Command(...)" and "Object(...)" execute in a default
# environment.  To run them in a custom environment, simply call them as methods of an
# environment object:
#
#   env.Command(b, [a1, a2], f'cmd1 {a1} {a2} > {b}')
#   env.Command(c, b, f'cmd2 {b} > {c}')
#   foo_obj = env.Object(foo_c)
#
# SCons has many other features, but for simplicity, the code in this file uses SCons features
# sparingly, preferring Python features (such as f-strings) to SCons features (such as
# SCons's own string substitution for special variables like $SOURCES) when possible.
# Our hope is that this Python-centric style will be more approachable to newcomers.
#
##################################################################################################

import re
import sys
import os, os.path
import subprocess
import traceback
import pdb
import SCons.Util
import atexit
import platform
import fnmatch
import pathlib
import shutil
import json

if sys.version_info < (3, 6):
  print(f'Requires Python version >= 3.6, found version {sys.version_info}')  # If the syntax of this line is invalid, the version of Python is probably older than 3.6
  exit(1)

##################################################################################################
#
#   Command-line options
#
##################################################################################################

if 'Z3_HOME' in os.environ:
  z3_default_path = os.environ['Z3_HOME']
else:
  z3_default_path = 'tools/Z3'

if 'KREMLIN_HOME' in os.environ:
  kremlin_default_path = os.environ['KREMLIN_HOME']
else:
  kremlin_default_path = 'tools/Kremlin'

if 'FSTAR_HOME' in os.environ:
  fstar_default_path = os.environ['FSTAR_HOME']
else:
  fstar_default_path = 'tools/FStar'

def AddOptYesNo(name, dest, default, help):
  AddOption('--' + name, dest = dest, default = default, action = 'store_true', help = f'{help} (default {default})')
  AddOption('--NO-' + name, dest = dest, default = default, action = 'store_false')

# Retrieve tool-specific command overrides passed in by the user
AddOptYesNo('DAFNY', dest = 'do_dafny', default = False,
  help='Verify Dafny files')
AddOptYesNo('FSTAR', dest = 'do_fstar', default = False,
  help='Verify F* files')
AddOptYesNo('DAFNY-USE-MY-Z3', dest = 'dafny_use_my_z3', default = False,
  help='With Dafny on Windows, use the Z3 in the PATH or specified by --Z3-PATH, not the one provided in tools/Dafny')
AddOption('--DAFNY-PATH', dest = 'dafny_path', type = 'string', default = 'tools/Dafny', action = 'store',
  help='Specify the path to Dafny tool binaries')
AddOption('--Z3-PATH', dest = 'z3_path', type = 'string', default = z3_default_path, action = 'store',
  help = 'Specify the path to directory containing Z3 executable')
AddOption('--KREMLIN-PATH', dest = 'kremlin_path', type = 'string', default = kremlin_default_path, action = 'store',
  help = 'Specify the path to kreMLin')
AddOption('--FSTAR-PATH', dest = 'fstar_path', type = 'string', default = fstar_default_path, action = 'store',
  help = 'Specify the path to F* tool')
AddOptYesNo('FSTAR-MY-VERSION', dest = 'fstar_my_version', default = False,
  help = 'Use version of F* that does not necessarily match .docker/build/config.json[recommended_fstar_version]')
AddOptYesNo('Z3-MY-VERSION', dest = 'z3_my_version', default = False,
  help = 'Use version of Z3 that does not necessarily match .docker/build/config.json[recommended_z3_version]')
AddOption('--DARGS', dest = 'dafny_user_args', type = 'string', default=[], action = 'append',
  help='Supply temporary additional arguments to the Dafny compiler')
AddOption('--FARGS', dest = 'fstar_user_args', type = 'string', default = [], action = 'append',
  help = 'Supply temporary additional arguments to the F* compiler')
AddOption('--VARGS', dest = 'vale_user_args', type = 'string', default = [], action = 'append',
  help = 'Supply temporary additional arguments to the Vale compiler')
AddOption('--KARGS', dest = 'kremlin_user_args', type = 'string', default = [], action = 'append',
  help = 'Supply temporary additional arguments to the Kremlin compiler')
AddOption('--CACHE-DIR', dest = 'cache_dir', type = 'string', default = None, action = 'store',
  help = 'Specify the SCons Shared Cache Directory')
AddOptYesNo('COLOR', dest = 'do_color', default = True,
  help="Add color to build output")
AddOptYesNo('DUMP-ARGS', dest = 'dump_args', default = False,
  help = "Print arguments that will be passed to the verification tools")
AddOptYesNo('PROFILE', dest = 'profile', default = False,
  help = "Turn on profile options to measure verification performance (note: --NO-USE-HINTS is recommended when profiling)")

do_help = GetOption('help')
do_clean = GetOption('clean')
do_build = not (do_help or do_clean)
do_dafny = GetOption('do_dafny')
do_fstar = GetOption('do_fstar')
dafny_use_my_z3 = GetOption('dafny_use_my_z3')
dafny_path = Dir(GetOption('dafny_path')).abspath
z3_path = Dir(GetOption('z3_path')).abspath
kremlin_path = Dir(GetOption('kremlin_path')).abspath
fstar_path = Dir(GetOption('fstar_path')).abspath
dafny_user_args = GetOption('dafny_user_args')
fstar_user_args = GetOption('fstar_user_args')
vale_user_args = GetOption('vale_user_args')
kremlin_user_args = GetOption('kremlin_user_args')
fstar_my_version = GetOption('fstar_my_version')
z3_my_version = GetOption('z3_my_version')
do_color = GetOption('do_color')
dump_args = GetOption('dump_args')
profile = GetOption('profile')

verify = do_dafny or do_fstar

##################################################################################################
#
#   Environment settings
#
##################################################################################################

common_env = Environment()
win32 = sys.platform == 'win32'

mono = ''
if do_build:
  if win32:
    import importlib.util
    if 'SHELL' in os.environ and importlib.util.find_spec('win32job') != None and importlib.util.find_spec('win32api'):
      # Special job handling for cygwin so that child processes exit when the parent process exits
      import win32job
      import win32api
      hdl = win32job.CreateJobObject(None, "")
      win32job.AssignProcessToJobObject(hdl, win32api.GetCurrentProcess())
      extended_info = win32job.QueryInformationJobObject(None, win32job.JobObjectExtendedLimitInformation)
      extended_info['BasicLimitInformation']['LimitFlags'] = win32job.JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE
      win32job.SetInformationJobObject(hdl, win32job.JobObjectExtendedLimitInformation, extended_info)
  else:
    mono = 'mono'
  if do_fstar and win32:
    # fstar.exe relies on libgmp-10.dll
    gmp_dll = FindFile('libgmp-10.dll', os.environ['PATH'].split(';'))
    if gmp_dll != None:
      common_env.PrependENVPath('PATH', os.path.dirname(str(gmp_dll)))

# Helper class to specify per-file command-line options for verification.
class BuildOptions:
  # First argument is mandatory (verification options); all others are optional named arguments
  def __init__(self, args, vale_includes = None):
    self.env = common_env.Clone()
    self.verifier_flags = args
    self.vale_includes = vale_includes

##################################################################################################
#
#   Configuration settings
#
##################################################################################################

dafny_default_args_nlarith = ('/ironDafny /allocated:1 /induction:1 /compile:0'
  + ' /timeLimit:30 /errorLimit:1 /errorTrace:0 /trace'
  )
dafny_default_args_larith = dafny_default_args_nlarith + ' /noNLarith'

fstar_default_args_nosmtencoding = ('--max_fuel 1 --max_ifuel 1'
  + (' --initial_ifuel 0')
  # The main purpose of --z3cliopt smt.QI.EAGER_THRESHOLD=100 is to make sure that matching loops get caught
  # Don't remove unless you're sure you've used the axiom profiler to make sure you have no matching loops
  + ' --z3cliopt smt.arith.nl=false --z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3'
  + ' --hint_info'
  + ' --cache_checked_modules'
  + ' --cache_dir obj/cache_checked'
  )
fstar_default_args = (fstar_default_args_nosmtencoding
  + ' --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped'
  )

vale_scons_args = ''
vale_includes = f'-include {File("fstar/code/lib/util/operator.vaf")}'

verify_paths = [
  'dafny',
  'fstar',
  'tools/Vale/test',
]

manual_dependencies = {
}

ulib_cache = f'{fstar_path}/ulib/.cache'
external_paths = [ulib_cache]

#
# Table of special-case sources which requires non-default arguments
#
verify_options = [
  ('fstar/code/lib/util/operator.vaf', BuildOptions(fstar_default_args, vale_includes = '')),
  ('tools/Vale/test/types.vaf', BuildOptions(None)), # type-check only, no verification
  ('tools/Vale/test/FTypeVale.vaf', BuildOptions(None)), # type-check only, no verification

  ('fstar/*/*.fst', BuildOptions(fstar_default_args)),
  ('fstar/*/*.fsti', BuildOptions(fstar_default_args)),
  ('tools/Vale/test/*/*.fst', BuildOptions(fstar_default_args)),
  ('tools/Vale/test/*/*.fsti', BuildOptions(fstar_default_args)),

  ('tools/Vale/test/docs_helper.dfy',  BuildOptions(dafny_default_args_nlarith)),

  # .dfy files default to this set of options
  ('.dfy', BuildOptions(dafny_default_args_larith)),

  # .fst/.fsti files default to this set of options
  ('.fst', BuildOptions(fstar_default_args)),
  ('.fsti', BuildOptions(fstar_default_args)),

  # .vad/.vaf files default to this set of options when compiling .dfy/.fst/.fsti
  ('.vad', BuildOptions(dafny_default_args_larith)),
  ('.vaf', BuildOptions(fstar_default_args)),
]

verify_options_dict = { k:v for (k, v) in verify_options }

# Find Z3
found_z3 = False
if verify and do_build:
  z3_exe = File(z3_path + '/z3' + ('.exe' if win32 else ''))
  if os.path.isfile(str(z3_exe)):
    found_z3 = True
  else:
    if win32:
      find_z3 = FindFile('z3.exe', os.environ['PATH'].split(';'))
    else:
      find_z3 = FindFile('z3', os.environ['PATH'].split(':'))
    if find_z3 != None:
      found_z3 = True
      z3_exe = find_z3
  fstar_z3_path = f'--smt {z3_exe}'
else:
  fstar_z3_path = ''

if verify and do_dafny:
  if sys.platform == 'win32' and not dafny_use_my_z3:
    dafny_z3_path = '' # use the default Boogie search rule, which uses Z3 from the tools/Dafny directory
  else:
    dafny_z3_path = f'/z3exe:{z3_exe}'

vale_exe = File('bin/vale.exe')
import_fstar_types_exe = File('bin/importFStarTypes.exe')
dafny_exe = File(f'{dafny_path}/Dafny.exe')
fstar_exe = File(f'{fstar_path}/bin/fstar.exe')

##################################################################################################
#
#   Global variables
#
##################################################################################################

all_modules = []  # string names of modules
src_include_paths = []  # string paths in sources where .fst, .fsti are found
obj_include_paths = []  # string paths in obj/, but omitting the 'obj/' prefix
fsti_map = {}  # map module names to .fsti File nodes (or .fst File nodes if no .fsti exists)
dump_deps = {}  # map F* type .dump file names x.dump to sets of .dump file names that x.dump depends on
vaf_dump_deps = {} # map .vaf file names x.vaf to sets of .dump file names that x.vaf depends on
vaf_vaf_deps = {} # map .vaf file names x.vaf to sets of y.vaf file names that x.vaf depends on

dafny_include_re = re.compile(r'^\s*include\s+"(\S+)"', re.M)
# match 'include {:attr1} ... {:attrn} "filename"'
# where attr may be 'verbatim' or 'from BASE'
vale_include_re = re.compile(r'include((?:\s*\{\:(?:\w|[ ])*\})*)\s*"(\S+)"', re.M)
vale_fstar_re = re.compile(r'\{\:\s*fstar\s*\}')
vale_verbatim_re = re.compile(r'\{\:\s*verbatim\s*\}')
vale_from_base_re = re.compile(r'\{\:\s*from\s*BASE\s*\}')
vale_open_re = re.compile(r'open\s+([a-zA-Z0-9_.]+)')
vale_friend_re = re.compile(r'friend\s+([a-zA-Z0-9_.]+)')
vale_import_re = re.compile(r'module\s+[a-zA-Z0-9_]+\s*[=]\s*([a-zA-Z0-9_.]+)')

if (not sys.stdout.isatty()) or not do_color:
  # No color if the output is not a terminal or user opts out
  yellow = ''
  red = ''
  uncolor = ''
else:
  yellow = '\033[93m'
  red = '\033[91;40;38;5;217m'
  uncolor = '\033[0m'

##################################################################################################
#
#   Utility functions
#
##################################################################################################

def print_error(s):
  print(f'{red}{s}{uncolor}')

def print_error_exit(s):
  print_error(s)
  Exit(1)

# Given a File node for dir/dir/.../m.extension, return m
def file_module_name(file):
  name = file.name
  name = name[:1].upper() + name[1:] # capitalize first letter, as expected for F* module names
  return os.path.splitext(name)[0]

# Return '.vaf', '.fst', etc.
def file_extension(file):
  return os.path.splitext(file.path)[1]

# Drop the '.vaf', '.fst', etc.
def file_drop_extension(file):
  return os.path.splitext(file.path)[0]

# Given source File node, return File node in object directory
def to_obj_dir(file):
  if str(file).startswith('obj'):
    return file
  else:
    return File(f'obj/{file}')

def to_hint_file(file):
  return File(f'hints/{file.name}.hints')

# Is the file from our own sources, rather than an external file (e.g., like an F* library file)?
def is_our_file(file):
  path = file.path
  return True in [path.startswith(str(Dir(p))) for p in ['obj'] + verify_paths]

def compute_include_paths(src_include_paths, obj_include_paths, obj_prefix):
  return src_include_paths + [str(Dir(f'{obj_prefix}/{x}')) for x in obj_include_paths]

def compute_includes(src_include_paths, obj_include_paths, obj_prefix):
  fstar_include_paths = compute_include_paths(src_include_paths, obj_include_paths, obj_prefix)
  return " ".join(["--include " + x for x in fstar_include_paths])

def CopyFile(target, source):
  Command(target, source, Copy(target, source))
  return target

##################################################################################################
#
#   Configuration and environment functions
#
##################################################################################################

# Helper to look up a BuildOptions matching a srcpath File node, from the
# verify_options[] list, falling back on a default if no specific override is present.
def get_build_options(srcnode):
  srcpath = srcnode.path
  srcpath = srcpath.replace('\\', '/')  # switch to posix path separators
  if srcpath in verify_options_dict:    # Exact match
    return verify_options_dict[srcpath]
  else:
    for key, options in verify_options: # Fuzzy match
      if fnmatch.fnmatch (srcpath, key):
        return options
    ext = os.path.splitext(srcpath)[1]
    if ext in verify_options_dict:      # Exact extension match
      return verify_options_dict[ext]
    else:
      return None

def check_fstar_version(config):
  import subprocess
  version = config['ValeProject']['recommended_fstar_version']
  cmd = [str(fstar_exe), '--version']
  o = subprocess.check_output(cmd, stderr = subprocess.STDOUT).decode('ascii')
  lines = o.splitlines()
  for line in lines:
    if '=' in line:
      key, v = line.split('=', 1)
      if key == 'commit' and v == version:
        return
  print_error(f'Expected F* version commit={version}, but fstar --version returned the following:')
  for line in lines:
    print_error('  ' + line)
  print_error_exit(
    f'Get F* version {version} from https://github.com/FStarLang/FStar,' +
    f' modify .docker/build/config.json[recommended_fstar_version], or use the --FSTAR-MY-VERSION option to override.' +
    f' (We try to update the F* version frequently; feel free to change .docker/build/config.json[recommended_fstar_version]' +
    f' to a more recent F* version as long as the build still succeeds with the new version.' +
    f' We try to maintain the invariant that the build succeeds with the F* version in .docker/build/config.json[recommended_fstar_version].)')

def check_z3_version(config, z3_exe):
  import subprocess
  version = config['ValeProject']['recommended_z3_version']
  cmd = [str(z3_exe), '--version']
  o = subprocess.check_output(cmd, stderr = subprocess.STDOUT).decode('ascii')
  lines = o.splitlines()
  line = lines[0]
  for word in line.split(' '):
    if '.' in word:
      if word == version:
        return
      break
  print_error(f'Expected Z3 version {version}, but z3 --version returned the following:')
  for line in lines:
    print_error('  ' + line)
  print_error_exit(
    'Get a recent Z3 executable from https://github.com/FStarLang/binaries/tree/master/z3-tested,' +
    ' modify .docker/build/config.json[recommended_z3_version], or use the --Z3-MY-VERSION option to override.' +
    ' (We rarely change the Z3 version; we strongly recommend using the expected version of Z3.)')

def add_fslexyacc(env):
  # probe for fslexyacc to ensure it is installed ahead of trying to use it to build
  build_dir = Dir('#tools/FsLexYacc/FsLexYacc.6.1.0/build')    # the '#' character makes this relative to the SConstruct file in the root of the repo
  fslex_exe = File(f'{build_dir}/fslex.exe')
  if not os.path.isfile(str(fslex_exe)):
    packages_config = File('#tools/Vale/src/packages.config')
    packages_dir = Dir('#tools/FsLexYacc')
    nuget_env = Environment()
    nuget_env['ENV']['PATH'] = os.environ['PATH']
    if nuget_env.Execute(f'nuget{".exe" if win32 else ""} restore {packages_config} -PackagesDirectory {packages_dir}'):
      print("Unable to run nuget in order to restore FsLexYacc.  See INSTALL.md for more details.")
      Exit(1)

def print_dump_args():
  print('Currently using the following F* args:')
  fstar_includes = compute_includes(src_include_paths, obj_include_paths, 'obj')
  for option in [fstar_z3_path, fstar_includes, fstar_user_args, fstar_default_args]:
    if len(option) > 0:
      print(f'{option} ', end='')
  print()
  Exit(1)

# extract a string filename out of a build failure
def bf_to_filename(bf):
  import SCons.Errors
  if bf is None: # unknown targets product None in list
    return '(unknown tgt)'
  elif isinstance(bf, SCons.Errors.StopError):
    return str(bf)
  elif bf.node:
    return str(bf.node)
  elif bf.filename:
    return bf.filename
  return '(unknown failure)'

def report_verification_failures():
  import time
  from SCons.Script import GetBuildFailures
  bf = GetBuildFailures()
  if bf:
    # bf is normally a list of build failures; if an element is None,
    # it's because of a target that scons doesn't know anything about.
    for x in bf:
      if x is not None:
        filename = bf_to_filename(x)
        if filename.endswith('.tmp') and os.path.isfile(filename):
          error_filename = filename[:-len('.tmp')] + '.error'
          stderr_filename = filename[:-len('.tmp')] + '.stderr'
          if os.path.isfile(error_filename):
            os.remove(error_filename)
          report_filename = stderr_filename if os.path.isfile(stderr_filename) else filename
          print()
          print(f'##### {red}Verification error{uncolor}')
          print('Printing contents of ' + report_filename + ' #####')
          with open (report_filename, 'r') as myfile:
            lines = myfile.read().splitlines()
            valeErrors = [line for line in lines if ("*****" in line)]
            for line in lines:
              if 'error was reported' in line or '(Error)' in line or ' failed' in line:
                line = f'{red}{line}{uncolor}'
              print(line)
          print()
          time.sleep(1)
          os.rename(filename, error_filename)

##################################################################################################
#
#   File and module processing functions
#
##################################################################################################

def find_external_fstar_file(module):
  for d in external_paths:
    for suffix in ('.fsti', '.fst', '.fsti.checked', '.fst.checked'):
      if os.path.isfile(os.path.join(d, module + suffix)):
        return File(os.path.join(d, module + suffix.replace('.checked', '')))
  return None

def add_module_for_file(file):
  global all_modules
  m = file_module_name(file)
  if m in all_modules:
    print(f'error: found more than one instance of module {m} (all module names must be unique for include paths to work correctly)')
    Exit(1)
  all_modules.append(m)

def add_include_dir_for_file(include_paths, file):
  d = str(file.dir)
  if not (d in include_paths):
    include_paths.append(d)
    pathlib.Path(str(to_obj_dir(file).dir)).mkdir(parents = True, exist_ok = True)

def include_fstar_file(env, file):
  options = get_build_options(file)
  add_include_dir_for_file(src_include_paths, file)
  if options != None:
    if (file_extension(file) == ".fst"):
      add_module_for_file(file)
    fsti_map[file_module_name(file)] = file

def include_vaf_file(env, file):
  options = get_build_options(file)
  add_include_dir_for_file(obj_include_paths, file)
  dummy_dir = File(f'obj/dummies/{file_drop_extension(file)}').dir
  pathlib.Path(str(dummy_dir)).mkdir(parents = True, exist_ok = True)
  if options != None:
    add_module_for_file(file)
    module_name = file_module_name(file)
    fsti_map[module_name] = f'{file_drop_extension(to_obj_dir(file))}.fsti'
    for extension in ['.fst', '.fsti']:
      # The F* dependency analysis runs before .vaf files are converted to .fst/.fsti files,
      # so generate a dummy .fst/.fsti file pair for each .vaf file for the F* dependency analysis.
      dummy_file = File(f'obj/dummies/{file_drop_extension(file)}{extension}')
      pathlib.Path(str(dummy_file.dir)).mkdir(parents = True, exist_ok = True)
      with open(str(dummy_file), 'w') as myfile:
        myfile.write(f'module {module_name}' + '\n')

# Verify a .dfy file
def verify_dafny_file(options, targetfile, sourcefile):
  env = options.env
  temptargetfile = File(f'{targetfile}.tmp')
  env.Command(temptargetfile, sourcefile,
    f'{mono} {dafny_exe} {options.verifier_flags} {dafny_z3_path}' +
    f' {sourcefile} {" ".join(dafny_user_args)}' +
    f' 1> {temptargetfile} 2>&1')
  CopyFile(targetfile, temptargetfile)

# Verify a .fst or .fsti file
def verify_fstar_file(options, targetfile, sourcefile, fstar_includes):
  env = options.env
  stderrfile = File(f'{targetfile}.stderr')
  temptargetfile = File(f'{targetfile}.tmp')
  dumptargetfile = File(re.sub('\.verified$', '.dump', str(targetfile)))
  env.Command(temptargetfile, sourcefile,
    f'{fstar_exe} {sourcefile} {options.verifier_flags} {fstar_z3_path}' +
    f' {fstar_includes} {" ".join(fstar_user_args)}' +
    (f' --debug {file_module_name(File(sourcefile))} --debug_level print_normalized_terms' if profile else '') +
    f' 1> {temptargetfile} 2> {stderrfile}')
  CopyFile(targetfile, temptargetfile)
  dump_module_flag = '--dump_module ' + file_module_name(sourcefile)
  dump_flags = ('--print_implicits --print_universes --print_effect_args --print_full_names' +
    ' --print_bound_var_types --ugly ' + dump_module_flag)
  env.Command(dumptargetfile, sourcefile,
    f'{fstar_exe} {sourcefile} {options.verifier_flags} {fstar_z3_path} --admit_smt_queries true' +
    f' {fstar_includes} {" ".join(fstar_user_args)}' +
    f' {dump_flags} 1>{dumptargetfile} 2> {dumptargetfile}.stderr')
  Depends(dumptargetfile, targetfile)

# Scan a .dfy file to discover its dependencies, and add .dfy.verified targets for each.
def dafny_dependency_scan(env, file):
  contents = file.get_text_contents()
  dirname = os.path.dirname(str(file))
  includes = dafny_include_re.findall(contents)
  obj_tmp = [f'{to_obj_dir(file)}.verified.tmp']
  for i in includes:
    srcpath = File(os.path.join(dirname, i))
    # TODO : this should convert the .dfy filename back to a dafny\code\...\.vad filename, and look up its options
    options = get_build_options(srcpath)
    if options != None:
      f_base = to_obj_dir(File(os.path.join(dirname, i)))
      f_dfy = File(f'{f_base}.verified')
      Depends(obj_tmp, f_dfy)
      process_dafny_file(env, srcpath)

# Process a .dfy file
def process_dafny_file(env, file):
  options = get_build_options(file)
  if verify and options != None:
    dafny_dependency_scan(env, file)
    target = File(f'{to_obj_dir(file)}.verified')
    verify_dafny_file(options, target, file)

# Process a .fst or .fsti file
def process_fstar_file(env, file, fstar_includes):
  options = get_build_options(file)
  if verify and options != None:
    target = File(f'{to_obj_dir(file)}.verified')
    verify_fstar_file(options, target, file, fstar_includes)

def vad_dependency_scan(env, file):
  contents = file.get_text_contents()
  dirname = os.path.dirname(str(file))
  includes = vale_include_re.findall(contents)
  obj_file_base = file_drop_extension(to_obj_dir(file))
  obj_tmps = [f'{obj_file_base}.dfy.verified.tmp']
  for (attrs, inc) in includes:
    f = os.path.join('dafny' if vale_from_base_re.search(attrs) else dirname, inc)
    if vale_verbatim_re.search(attrs):
      f_base = file_drop_extension(to_obj_dir(File(f)))
      f_dfy = File(f_base + '.dfy.verified')
      Depends(obj_tmps, f_dfy)
    else:
      f_base = file_drop_extension(to_obj_dir(File(f)))
      f_dfy = File(f_base + '.dfy.verified')
      Depends(obj_tmps, f_dfy)

def vaf_dependency_scan(env, file):
  contents = file.get_text_contents()
  dirname = os.path.dirname(str(file))
  vaf_includes = vale_include_re.findall(contents)
  fst_includes = vale_open_re.findall(contents) + vale_import_re.findall(contents)
  fst_friends = vale_friend_re.findall(contents)
  obj_file_base = file_drop_extension(to_obj_dir(file))
  #dumptargetfile = f'{obj_file_base}.fsti.dump'
  #dump_deps[dumptargetfile] = set()
  vaf_dump_deps[str(file)] = set()
  vaf_vaf_deps[str(file)] = set()
  fst_fsti = [f'{obj_file_base}.fst', f'{obj_file_base}.fsti']
  obj_tmp = [f'{obj_file_base}.fst.verified.tmp']
  obj_tmps = [f'{obj_file_base}.fst.verified.tmp', f'{obj_file_base}.fsti.verified.tmp']
  typesfile = File(f'{obj_file_base}.types.vaf')
  for (attrs, inc) in vaf_includes:
    if vale_fstar_re.search(attrs):
      if inc in fsti_map:
        dumpsourcebase = to_obj_dir(File(f'{fsti_map[inc]}'))
      else:
        dumpsourcebase = find_external_fstar_file(inc)
        if dumpsourcebase == None:
          print_error_exit(f'could not find external F* module {inc} included by {file} in paths {external_paths}')
      dumpsourcefile = File(f'{dumpsourcebase}.dump')
      if is_our_file(dumpsourcebase):
        vaf_dump_deps[str(file)].add(str(dumpsourcefile))
    else:
      f = os.path.join('fstar' if vale_from_base_re.search(attrs) else dirname, inc)
      # if A.vaf includes B.vaf, then manually establish these dependencies:
      #   A.fst.verified.tmp  depends on B.fsti.verified
      #   A.fsti.verified.tmp depends on B.fsti.verified
      vaf_vaf_deps[str(file)].add(str(File(f)))
      f_base = file_drop_extension(to_obj_dir(File(f)))
      f_fsti = File(f_base + '.fsti.verified')
      Depends(obj_tmps, f_fsti)
  Depends(fst_fsti, typesfile)
  for inc in fst_includes:
    if inc in fsti_map:
      Depends(obj_tmps, to_obj_dir(File(f'{fsti_map[inc]}.verified')))
  for inc in fst_friends:
    if inc in fsti_map:
      Depends(obj_tmp, re.sub('\.fsti$', '.fst.verified', str(to_obj_dir(fsti_map[inc]))))

# Translate Vale .vad to .dfy file
# Takes a source .vad File node
# Returns .dfy File node
def translate_vad_file(options, source_vad):
  env = options.env
  target = file_drop_extension(to_obj_dir(source_vad))
  target_dfy = File(target + '.dfy')
  env.Command(target_dfy, [source_vad, vale_exe],
    f'{mono} {vale_exe} -includeSuffix .vad .dfy -dafnyText' +
    f' -sourceFrom BASE dafny -destFrom BASE obj/dafny'
    f' -in {source_vad} -out {target_dfy}' +
    f' {" ".join(vale_user_args)}')
  return target_dfy

# Translate Vale .vaf to F* .fst/fsti pair
# Takes a source .vaf File node
# Returns list of File nodes representing the resulting .fst and .fsti files
def translate_vaf_file(options, source_vaf):
  env = options.env
  target = file_drop_extension(to_obj_dir(source_vaf))
  target_fst = File(target + '.fst')
  target_fsti = File(target + '.fsti')
  targets = [target_fst, target_fsti]
  opt_vale_includes = vale_includes if options.vale_includes == None else options.vale_includes
  types_include = ''
  types_include = f'-include {target}.types.vaf'
  env.Command(targets, [source_vaf, vale_exe],
    f'{mono} {vale_exe} -fstarText {types_include} {opt_vale_includes}' +
    f' -in {source_vaf} -out {target_fst} -outi {target_fsti}' +
    f' {vale_scons_args} {" ".join(vale_user_args)}')
  return targets

# Process a .vad file
def process_vad_file(env, file):
  options = get_build_options(file)
  if options != None:
    vad_dependency_scan(env, file)
    dfy = translate_vad_file(options, file)
    if verify:
      dfy_options = get_build_options(dfy)
      target = file_drop_extension(to_obj_dir(file))
      target_dfy = f'{target}.dfy.verified'
      verify_dafny_file(dfy_options, target_dfy, dfy)

# Process a .vaf file
def process_vaf_file(env, file, fstar_includes):
  options = get_build_options(file)
  if options != None:
    vaf_dependency_scan(env, file)
    fsts = translate_vaf_file(options, file)
    fst = fsts[0]
    fsti = fsts[1]
    if verify and options.verifier_flags != None:
      fst_options = get_build_options(fst)
      fsti_options = get_build_options(fsti)
      target = file_drop_extension(to_obj_dir(file))
      target_fst = f'{target}.fst.verified'
      target_fsti = f'{target}.fsti.verified'
      Depends(f'{target_fst}.tmp', target_fsti)
      verify_fstar_file(fst_options, target_fst, fst, fstar_includes)
      verify_fstar_file(fsti_options, target_fsti, fsti, fstar_includes)

def compute_module_types(env, source_vaf):
  source_base = file_drop_extension(to_obj_dir(File(source_vaf)))
  types_vaf = f'{source_base}.types.vaf'
  done = set()
  dumps = []
  def collect_dumps_in_order(x):
    if not (x in done):
      done.add(x)
      for y in sorted(dump_deps[x]):
        # if x depends on y, y must appear first
        collect_dumps_in_order(y)
      x_vaf = re.sub('\.dump$', '.types.vaf', x)
      Depends(types_vaf, x)
      dumps.append(x)
  for vaf in sorted(vaf_vaf_deps[source_vaf] | {source_vaf}):
    for x in sorted(vaf_dump_deps[vaf]):
      collect_dumps_in_order(x)
  dumps_string = " ".join(['-in ' + str(x) for x in dumps])
  Depends(types_vaf, import_fstar_types_exe)
  Command(types_vaf, dumps, f'{mono} {import_fstar_types_exe} {dumps_string} -out {types_vaf}')

def recursive_glob(env, pattern, strings = False):
  matches = []
  split = os.path.split(pattern) # [0] is the directory, [1] is the actual pattern
  platform_directory = split[0] #os.path.normpath(split[0])
  for d in os.listdir(platform_directory):
    if os.path.isdir(os.path.join(platform_directory, d)):
      newpattern = os.path.join(split[0], d, split[1])
      matches.append(recursive_glob(env, newpattern, strings))
  files = env.Glob(pattern, strings=strings)
  matches.append(files)
  return Flatten([File(x) for x in matches])

# Verify *.dfy, *.fst, *.fsti, *.vad, *.vaf files in a list of directories.
# This enumerates all files in those trees, and creates verification targets for each,
# which in turn causes a dependency scan to verify all of their dependencies.
def process_files_in(env, directories):
  if do_dafny:
    dfys = []
    vads = []
    for d in directories:
      dfys.extend(recursive_glob(env, d + '/*.dfy', strings = True))
      vads.extend(recursive_glob(env, d + '/*.vad', strings = True))
    # Process and verify files:
    for file in dfys:
      process_dafny_file(env, file)
    for file in vads:
      process_vad_file(env, file)
  if do_fstar:
    fsts = []
    fstis = []
    vafs = []
    for d in directories:
      fsts.extend(recursive_glob(env, d + '/*.fst', strings = True))
      fstis.extend(recursive_glob(env, d + '/*.fsti', strings = True))
      vafs.extend(recursive_glob(env, d + '/*.vaf', strings = True))
    # Compute include directories:
    for file in fsts:
      include_fstar_file(env, file)
    for file in fstis:
      include_fstar_file(env, file)
    for file in vafs:
      include_vaf_file(env, file)
    # Process and verify files:
    fstar_include_paths = compute_include_paths(src_include_paths, obj_include_paths, 'obj')
    fstar_includes = compute_includes(src_include_paths, obj_include_paths, 'obj')
    for file in fsts:
      process_fstar_file(env, file, fstar_includes)
    for file in fstis:
      process_fstar_file(env, file, fstar_includes)
    for file in vafs:
      process_vaf_file(env, file, fstar_includes)
    for target in manual_dependencies:
      Depends(target, manual_dependencies[target])

##################################################################################################
#
#   FStar dependency analysis
#
##################################################################################################

def compute_fstar_deps(env, src_directories, fstar_includes):
  import subprocess
  # find all .fst, .fsti files in src_directories
  fst_files = []
  for d in src_directories:
    fst_files.extend(recursive_glob(env, d+'/*.fst', strings = True))
    fst_files.extend(recursive_glob(env, d+'/*.fsti', strings = True))
  # use fst_files to choose .fst and .fsti files that need dependency analysis
  files = []
  for f in fst_files:
    options = get_build_options(f)
    if options != None:
      files.append(f)
  # call fstar --dep make
  includes = []
  for include in fstar_includes:
    includes += ["--include", include]
  lines = []
  depsBackupFile = 'obj/fstarDepsBackup.d'
  args = ["--dep", "make", "--already_cached", "Prims FStar"] + includes + files
  cmd = [fstar_exe] + args
  cmd = [str(x) for x in cmd]
  #print(" ".join(cmd)) # note: this won't work without '' around Prims FStar
  try:
    print('F* dependency analysis starting')
    o = subprocess.check_output(cmd, stderr = subprocess.STDOUT).decode('ascii')
    print('F* dependency analysis finished')
  except (subprocess.CalledProcessError) as e:
    print(f'F* dependency analysis: error: {e.output}')
    Exit(1)
  fstar_deps_ok = True
  lines = o.splitlines()
  for line in lines:
    if 'Warning:' in line:
      print(line)
      fstar_deps_ok = False
    if len(line) == 0:
      pass
    elif '(Warning ' in line:
      # example: "(Warning 307) logic qualifier is deprecated"
      pass
    else:
      # lines are of the form:
      #   a1.fst a2.fst ... : b1.fst b2.fst ...
      # we change this to:
      #   obj\...\a1.fst.verified obj\...\a2.fst.verified ... : b1.fst.verified b2.fst.verified ...
      # we ignore targets that we will not verify (e.g. F* standard libraries)
      targets, sources = line.split(': ', 1) # ': ', not ':', because of Windows drive letters
      sources = sources.split()
      targets = targets.split()
      obj_name = str(Dir('obj'))
      dummies_name = str(Dir('obj/dummies'))
      sources = [str(File(x)).replace(dummies_name, obj_name) for x in sources]
      targets = [str(File(x)).replace(dummies_name, obj_name) for x in targets]
#      for source in sources:
#        for target in targets:
#          if target.startswith('specs') and (source.startswith('obj') or source.startswith('code')):
#            print(f'{yellow}Warning: file {target} in specs directory depends on file {source} outside specs directory{uncolor}')
      sources_ver = [to_obj_dir(File(re.sub('\.fst$', '.fst.verified', re.sub('\.fsti$', '.fsti.verified', x)))) for x in sources if is_our_file(File(x))]
      targets_ver = [to_obj_dir(File(re.sub('\.fst$', '.fst.verified.tmp', re.sub('\.fsti$', '.fsti.verified.tmp', x)))) for x in targets if is_our_file(File(x))]
      Depends(targets_ver, sources_ver)
      # Computing types from F* files
      # Dump F* types for for each of a1.fst a2.fst ... into a1.fst.dump, a2.fst.dump, ...
      # Targets that we don't verify go in obj/external
      for t in targets:
        if is_our_file(File(t)):
          dumptargetfile = str(to_obj_dir(t + '.dump'))
        else:
          # Compute types of an external module, assuming it was compiled with default arguments
          dumptargetfile = 'obj/external/' + os.path.split(t)[1] + '.dump'
          dump_module_flag = '--dump_module ' + file_module_name(File(t))
          dump_flags = ('--print_implicits --print_universes --print_effect_args --print_full_names' +
            ' --print_bound_var_types --ugly ' + dump_module_flag)
          env.Command(dumptargetfile, t,
            f'{fstar_exe} {t} {fstar_z3_path} --admit_smt_queries true' +
            f' {dump_flags} 1>{dumptargetfile} 2> {dumptargetfile}.stderr')
        if not (dumptargetfile in dump_deps):
          dump_deps[dumptargetfile] = set()
        for s in sources:
          if is_our_file(File(s)):
            dump_deps[dumptargetfile].add(str(to_obj_dir(s + '.dump')))
          else:
            dump_deps[dumptargetfile].add('obj/external/' + os.path.split(s)[1] + '.dump')
  if fstar_deps_ok:
    # Save results in depsBackupFile
    with open(depsBackupFile, 'w') as myfile:
      for line in lines:
        myfile.write(line + '\n')
  else:
    print('F* dependency analysis failed')
    Exit(1)

##################################################################################################
#
#   Top-level commands
#
##################################################################################################

if do_build:
  atexit.register(report_verification_failures)
  env = common_env

# Create obj directory and any subdirectories needed during dependency analysis
  # (SCons will create other subdirectories during build)
  pathlib.Path('bin').mkdir(parents = True, exist_ok = True)
  pathlib.Path('obj').mkdir(parents = True, exist_ok = True)
  pathlib.Path('obj/cache_checked').mkdir(parents = True, exist_ok = True)

  config_filename = '.docker/build/config.json'
  with open(config_filename) as myfile:
    config = json.load(myfile)
  vale_version = config['ValeProject']['binary_release_vale_version']
  def write_vale_version(target, source, env):
    with open('bin/.vale_version', 'w', newline = '\n') as myfile:
      myfile.write(f'{vale_version}\n')
  env.Command('bin/.vale_version', config_filename, write_vale_version)

  Export('env')
  Export('win32')
  Export('do_build')
  Export('mono')
  Export('dafny_path')
  add_fslexyacc(env)
  SConscript('tools/Vale/SConscript')
  SConscript('tools/ImportFStarTypes/SConscript')

  # Check F* and Z3 versions
  if do_fstar and not fstar_my_version:
    check_fstar_version(config)
  if verify and not z3_my_version:
    if not found_z3:
      print_error_exit('Could not find z3 executable.  Either put z3 in your path, or put it in the directory tools/Z3/, or use the --FSTARZ3=<z3-executable> option.')
    check_z3_version(config, z3_exe)

  print('Processing source files')
  process_files_in(env, verify_paths)
  if do_fstar:
    compute_fstar_deps(env, verify_paths, compute_include_paths(src_include_paths, obj_include_paths, 'obj/dummies'))
    for x in vaf_dump_deps:
      compute_module_types(env, x)

  if dump_args:
    print_dump_args()
