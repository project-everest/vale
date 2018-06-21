# for python2 to use the print() function, removing the print keyword
from __future__ import print_function

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

# TODO:
#  - switch over to Dafny/Vale tools for dependency generation, rather than regex

Import("*")

target_arch='x86'
target_x='86'
sha_arch_dir=''
aes_arch_dir=''
if (sys.platform == 'win32' and os.getenv('PLATFORM')=='X64') or platform.machine() == 'x86_64' :
  target_arch='amd64'
  target_x='64'
  sha_arch_dir='sha-x64'
  aes_arch_dir='x64'
  
envDict = {'TARGET_ARCH':target_arch,
           'X':target_x,
           'ARCH':'src/arch/x$X',
           'SHA_ARCH_DIR':sha_arch_dir,
           'AES_ARCH_DIR':aes_arch_dir}

env = Environment(**envDict)
if sys.platform == 'win32':
  import win32job
  import win32api
  env.Replace(CCPDBFLAGS='/Zi /Fd${TARGET.base}.pdb')
  # Use kremlib.h without primitive support for uint128_t.
  env.Append(CCFLAGS=['/Ox', '/Gz', '/DKRML_NOUINT128'])
  env.Append(LINKFLAGS=['/DEBUG'])
  env['NUGET'] = 'nuget.exe'
  hdl = win32job.CreateJobObject(None, "")
  win32job.AssignProcessToJobObject(hdl, win32api.GetCurrentProcess())
  extended_info = win32job.QueryInformationJobObject(None, win32job.JobObjectExtendedLimitInformation)
  extended_info['BasicLimitInformation']['LimitFlags'] = win32job.JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE
  win32job.SetInformationJobObject(hdl, win32job.JobObjectExtendedLimitInformation, extended_info)
  if os.getenv('PLATFORM')=='X64':
    env['AS'] = 'ml64'
else:
  env.Append(CCFLAGS=['-O3', '-flto', '-g', '-DKRML_NOUINT128', '-std=c++11'])
  env['MONO'] = 'mono'
  env['NUGET'] = 'nuget'

# Convert NUMBER_OF_PROCESSORS into '-j n'.
#num_cpu = int(os.environ.get('NUMBER_OF_PROCESSORS', 1)) 
#SetOption('num_jobs', num_cpu) 

if 'FSTAR_HOME' in os.environ:
  fstar_default_path = os.environ['FSTAR_HOME']
else:
  fstar_default_path = '#tools/FStar'

# Retrieve tool-specific command overrides passed in by the user
AddOption('--STAGE1',
  dest='stage1',
  default=False,
  action='store_true',
  help='F* stage 1 (of 2)')
AddOption('--STAGE2',
  dest='stage2',
  default=False,
  action='store_true',
  help='F* stage 2 (of 2)')
AddOption('--DAFNY',
  dest='do_dafny',
  default=False,
  action='store_true',
  help='Verify Dafny files')
AddOption('--NODAFNY',
  dest='do_dafny',
  default=False,
  action='store_false',
  help='Do not verify Dafny files')
AddOption('--DAFNYPATH',
  dest='dafny_path',
  type='string',
  default='#tools/Dafny',
  action='store',
  help='Specify the path to Dafny tool binaries')
AddOption('--FSTAR',
  dest='do_fstar',
  default=True,
  action='store_true',
  help='Verify F* files')
AddOption('--NOFSTAR',
  dest='do_fstar',
  default=True,
  action='store_false',
  help='Do not verify F* files')
AddOption('--FSTARPATH',
  dest='fstar_path',
  type='string',
  default=fstar_default_path,
  action='store',
  help='Specify the path to F* tool')
AddOption('--FSTARZ3',
  dest='fstar_z3',
  type='string',
  default='',
  action='store',
  help='Specify the path to z3 or z3.exe for F*')
AddOption('--FSTAR-MY-VERSION',
  dest='fstar_my_version',
  default=False,
  action='store_true',
  help='Use version of F* that does not necessarily match .fstar_version')
AddOption('--FSTAR-Z3-MY-VERSION',
  dest='fstar_z3_my_version',
  default=False,
  action='store_true',
  help='Use version of Z3 that does not necessarily match .fstar_z3_version')
AddOption('--GEN-HINTS',
  dest='gen_hints',
  default=False,
  action='store_true',
  help='Generate new F* .hints files and copy them into the hints directory')
AddOption('--DARGS',
  dest='dafny_user_args',
  type='string',
  default=[],
  action='append',
  help='Supply temporary additional arguments to the Dafny compiler')
AddOption('--FARGS',
  dest='fstar_user_args',
  type='string',
  default=[],
  action='append',
  help='Supply temporary additional arguments to the F* compiler')
AddOption('--VARGS',
  dest='vale_user_args',
  type='string',
  default=[],
  action='append',
  help='Supply temporary additional arguments to the Vale compiler')
AddOption('--KARGS',
  dest='kremlin_user_args',
  type='string',
  default=[],
  action='append',
  help='Supply temporary additional arguments to the Kremlin compiler')
AddOption('--CARGS',
  dest='c_user_args',
  type='string',
  default=[],
  action='append',
  help='Supply temporary additional arguments to the C compiler')
AddOption('--OPENSSL',
  dest='openssl_path',
  type='string',
  default=None,
  action='store',
  help='Specify the path to the root of an OpenSSL source tree')
AddOption('--CACHEDIR',
  dest='cache_dir',
  type='string',
  default=None,
  action='store',
  help='Specify the SCSons Shared Cache Directory')
AddOption('--NOVERIFY',
  dest='noverify',
  default=False,
  action='store_true',
  help='Verify and compile, or compile only')
AddOption('--ONE',
  dest='single_vaf',
  type='string',
  default=None,
  action='store',
  help='Only verify one specified .vaf file, and in that file, only verify procedures or verbatim blocks marked as {:verify}.')
AddOption('--NOCOLOR',
  dest='nocolor',
  default=False,
  action='store_true',
  help="Don't add color to build output")
AddOption('--DUMPARGS',
  dest='dump_args',
  default=False,
  action='store_true',
  help="Print arguments that will be passed to the verification tools")
AddOption('--FSTAR-EXTRACT',
  dest='fstar_extract',
  default=False,
  action='store_true',
  help="Extract .ml files from F* files")
AddOption('--NO-LEMMAS',
  dest='no_lemmas',
  default=False,
  action='store_true',
  help="Generate Vale code but no lemmas")
AddOption('--MIN_TEST',
  dest='min_test',
  default=False,
  action='store_true',
  help="Only run on a minimal set of test files")

env['DAFNY_PATH'] = Dir(GetOption('dafny_path')).abspath
env['FSTAR_PATH'] = Dir(GetOption('fstar_path')).abspath
env['DAFNY_USER_ARGS'] = GetOption('dafny_user_args')
env['FSTAR_USER_ARGS'] = GetOption('fstar_user_args')
env['VALE_USER_ARGS'] = GetOption('vale_user_args')
env['KREMLIN_USER_ARGS'] = GetOption('kremlin_user_args')
env.Append(CCFLAGS=GetOption('c_user_args'))
env['OPENSSL_PATH'] = GetOption('openssl_path')

do_dafny = GetOption('do_dafny')
do_fstar = GetOption('do_fstar')
stage1 = GetOption('stage1')
stage2 = GetOption('stage2')
fstar_my_version = GetOption('fstar_my_version')
fstar_z3_my_version = GetOption('fstar_z3_my_version')
fstar_extract = GetOption('fstar_extract')
no_lemmas = GetOption('no_lemmas')
gen_hints = GetOption('gen_hints')
single_vaf = GetOption('single_vaf')
is_single_vaf = not (single_vaf is None)
min_test = GetOption('min_test')
env['VALE_SCONS_ARGS'] = '-disableVerify -omitUnverified' if is_single_vaf else '-noLemmas' if no_lemmas else ''

####################################################################
#
#   Add support for color in the output
#
####################################################################

colors = {}
colors['cyan']   = '\033[96m'
colors['purple'] = '\033[95m'
colors['blue']   = '\033[94m'
colors['green']  = '\033[92m'
colors['yellow'] = '\033[93m'
colors['red']    = '\033[91;40;38;5;217m'
colors['end']    = '\033[0m'

# If the output is not a terminal or user opts out, remove the colors
if (not sys.stdout.isatty()) or GetOption('nocolor'):
   for key, value in colors.items():
      colors[key] = ''

####################################################################
#
#   Set up stages and environment
#
####################################################################

if do_fstar and not stage1 and not stage2:
  #
  # Stage1 builds the Vale tool and compiles vaf files to F* files.
  # Stage2 runs F*'s dependency analysis on the F* files and verifies F* files.
  # (F* dependency analysis cannot run until stage1 completes, which is
  # why we have two stages.)
  #
  # Here, we try to run "scons --stage1 ..." and then proceed to stage2.
  # Unfortunately, this requires running scons recursively, which is
  # not something that scons is designed for.  If this doesn't work,
  # the user can always run "scons --STAGE1" and "scons --STAGE2" explicitly.
  #
  print("%s*** Running scons --STAGE1 ***%s" % (colors['yellow'], colors['end']))
  args_stage1 = [x for x in sys.argv if not x.endswith('.verified') and not x.endswith('.hints') and not x.endswith('.ml') and not x.endswith('.exe') and not x.endswith('.asm') and not x.endswith('.S') and not x.endswith('.obj')]
  subprocess.check_call(['python'] + args_stage1 + ['--STAGE1'])
  print("%s*** Running scons --STAGE2 ***%s" % (colors['yellow'], colors['end']))
  stage2 = True

# --NOVERIFY is intended for CI scenarios, where the Win32/x86 build is verified, so
# the other build flavors do not redundently re-verify the same results.
env['DAFNY_NO_VERIFY'] = ''
env['FSTAR_NO_VERIFY'] = ''
verify=(GetOption('noverify') == False)
if not verify:
  print('***\n*** WARNING:  NOT VERIFYING ANY CODE\n***')
  env['DAFNY_NO_VERIFY'] = '/noVerify'
  env['FSTAR_NO_VERIFY'] = '--lax'

cache_dir=GetOption('cache_dir')
if cache_dir != None:
  print('Using Shared Cache Directory %s'%cache_dir)
  CacheDir(cache_dir)

env['DAFNY'] = Dir(env['DAFNY_PATH']).File('Dafny.exe')
env['FSTAR'] = Dir(env['FSTAR_PATH']).Dir('bin').File('fstar.exe')

if 'KREMLIN_HOME' in os.environ:
  kremlin_path = os.environ['KREMLIN_HOME']
  env['KREMLIN'] = File(kremlin_path + '/_build/src/Kremlin.native')
  kremlib_path = kremlin_path + '/kremlib'

env['VALE'] = File('bin/vale.exe')
env['VALE_INCLUDE'] = '-include ' + str(File('src/lib/util/operator.vaf'))

# Useful Dafny command lines
dafny_default_args_nlarith =   '/ironDafny /allocated:1 /induction:1 /compile:0 /timeLimit:30 /errorLimit:1 /errorTrace:0 /trace'
dafny_default_args_larith = dafny_default_args_nlarith + ' /noNLarith'

fstar_default_args_nosmtencoding = '--max_fuel 1 --max_ifuel 1' \
  + (' --initial_ifuel 1' if is_single_vaf else ' --initial_ifuel 0') \
  + ' --z3cliopt smt.arith.nl=false --z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3' \
  + ' --hint_info' \
  + ('' if is_single_vaf else ' --use_hints') \
  + (' --record_hints' if gen_hints else ' --cache_checked_modules') \
  + (' --use_extracted_interfaces true')
fstar_default_args = fstar_default_args_nosmtencoding \
  + ' --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped'

####################################################################
#
#   Add support for color in the output
#
####################################################################

colors = {}
colors['cyan']   = '\033[96m'
colors['purple'] = '\033[95m'
colors['blue']   = '\033[94m'
colors['green']  = '\033[92m'
colors['yellow'] = '\033[93m'
colors['red']    = '\033[91m'
colors['end']    = '\033[0m'

# If the output is not a terminal or user opts out, remove the colors
if (not sys.stdout.isatty()) or GetOption('nocolor'):
   for key, value in colors.items():
      colors[key] = ''

####################################################################
#
#   General-purpose utility commands
#
####################################################################

def formatExceptionInfo(maxTBlevel=5):
   cla, exc, trbk = sys.exc_info()
   excName = cla.__name__
   try:
       excArgs = exc.__dict__["args"]
   except KeyError:
       excArgs = "<no args>"
   excTb = traceback.format_tb(trbk, maxTBlevel)
   return (excName, excArgs, excTb)

def docmd(env, cmd):
  try:
    #print('cmd ' + cmd)
    pipe = SCons.Action._subproc(env, cmd,
                                 stdin = 'devnull',
                                 stderr = 'devnull',
                                 stdout = subprocess.PIPE)  
    #print('back from cmd')
  except:
    e = sys.exc_info()[0]
    print ("%sError invoking: %s%s" % (colors['red'], cmd, colors['end']))
    print (formatExceptionInfo())
    #print ("Exception: %s" % e)
    Exit(1)
  result = []
  line = pipe.stdout.readline()
  while line:
    result.append(line)
    line = pipe.stdout.readline()
  return result

def make_cygwin_path(path):
  cygwin_path = docmd("cygpath", path.rstrip()) 
  return cygwin_path[0]

def replace_extension(path, new_ext):
  return "%s.%s" % (os.path.splitext(path)[0], new_ext)

####################################################################
#
#   General utilities
#
####################################################################

# The obj directory structure is based on the src and tools directory structures:
#   src/... --> obj/...
#   tools/... --> obj/...
def to_obj_dir(path):
  path = os.path.relpath(path)
  path = path.replace('\\', '/')
  if path.startswith('obj/'):
    return path
  if path.startswith('src/'):
    return path.replace('src/', 'obj/', 1)
  if path.startswith('tools/'):
    return path.replace('tools/', 'obj/', 1)
  raise Exception('expected src/... or tools/..., found ' + path)

# obj/... -> hints/...
def to_hints_dir(path):
  path = os.path.relpath(path)
  path = path.replace('\\', '/')
  if path.startswith('obj/'):
    return path.replace('obj/', 'hints/', 1)
  raise Exception('expected obj/..., found ' + path)

def has_obj_dir(path):
  path = os.path.relpath(path)
  path = path.replace('\\', '/')
  return path.startswith('obj/') or path.startswith('src/') or path.startswith('tools/')

####################################################################
#
#   Define a Vale transformation Builder
#
####################################################################

# add vale.exe and its dependent DLLs to the source list, so a change
# in any one of them causes the target to rebuild.
def vale_tool_dependency_Emitter(target, source, env):
  source.append(vale_deps)
  return (target, source)
  
# add env.Vale*(), to invoke Vale to compile a .vad to a .gen.dfy or a .vaf to a .fst
def add_vale_builders(env):
  vale_dafny_builder = Builder(action = "$MONO $VALE -includeSuffix .vad .gen.dfy -sourceFrom BASE src -destFrom BASE obj -in $SOURCE -out $TARGET $VALE_USER_ARGS",
                            suffix = '.gen.dfy',
                            src_suffix = '.vad',
                            emitter = vale_tool_dependency_Emitter)
  vale_fstar_builder = Builder(action = "$MONO $VALE -fstarText $VALE_INCLUDE -in $SOURCE -out $TARGET -outi ${TARGET}i $VALE_SCONS_ARGS $VALE_USER_ARGS",
                            src_suffix = '.vaf',
                            emitter = vale_tool_dependency_Emitter)
  env.Append(BUILDERS = {'ValeDafny' : vale_dafny_builder})
  env.Append(BUILDERS = {'ValeFStar' : vale_fstar_builder})

# match 'include {:attr1} ... {:attrn} "filename"'
# where attr may be 'verbatim' or 'from BASE'
vale_include_re = re.compile(r'include((?:\s*\{\:(?:\w|[ ])*\})*)\s*"(\S+)"', re.M)
vale_verbatim_re = re.compile(r'\{\:\s*verbatim\s*\}')
vale_from_base_re = re.compile(r'\{\:\s*from\s*BASE\s*\}')

def vale_dafny_file_scan(node, env, path):
  contents = node.get_text_contents()
  dirname =  os.path.dirname(str(node))

  includes = vale_include_re.findall(contents)

  v_dfy_includes = []
  v_vad_includes = []
  for (attrs, inc) in includes:
    f = os.path.join('src' if vale_from_base_re.search(attrs) else dirname, inc)
    if vale_verbatim_re.search(attrs):
      v_dfy_includes.append(f)
      #v = os.path.join(dirname.replace('src', 'obj'), os.path.splitext(inc)[0] + '.vdfy')
    else:
      #v = os.path.join(dirname, os.path.splitext(i)[0] + '.vdfy').replace('src', 'obj')
      v_vad_includes.append(f)

  files = env.File(v_dfy_includes + v_vad_includes) 
  return files

def vale_fstar_file_scan(node, env, path):
  contents = node.get_text_contents()
  dirname =  os.path.dirname(str(node))

  includes = vale_include_re.findall(contents)

  v_vaf_includes = []
  for (attrs, inc) in includes:
    f = os.path.join('src' if vale_from_base_re.search(attrs) else dirname, inc)
    if not vale_verbatim_re.search(attrs):
      v_vaf_includes.append(f)
      # if A.vaf includes B.vaf, then manually establish these dependencies:
      #   A.fst.verified  depends on B.fsti
      #   A.fsti.verified depends on B.fsti
      # note that A.fst.verified and A.fsti.verified may also have other dependencies; we rely on F*'s dependency analysis for these
      f_fsti = os.path.splitext(to_obj_dir(os.path.normpath(f)))[0] + '.fsti.verified'
      node_o = to_obj_dir(str(node))
      node_o_base = os.path.splitext(node_o)[0]
      Depends([node_o_base + '.fst.verified.tmp', node_o_base + '.fsti.verified.tmp'], f_fsti)

  files = env.File(v_vaf_includes) 
  return files

vale_dafny_scan = Scanner(function = vale_dafny_file_scan,
                     skeys = ['.vad'])
vale_fstar_scan = Scanner(function = vale_fstar_file_scan,
                     skeys = ['.vaf'])
if do_dafny:
  env.Append(SCANNERS = vale_dafny_scan)
if do_fstar and not is_single_vaf:
  env.Append(SCANNERS = vale_fstar_scan)


####################################################################
#
#   Dafny-specific utilities
#
####################################################################

### Could try adding this to the scanner below...
### From: http://stackoverflow.com/questions/241327/python-snippet-to-remove-c-and-c-comments
##def comment_remover(text):
##    def replacer(match):
##        s = match.group(0)
##        if s.startswith('/'):
##            return " " # note: a space and not an empty string
##        else:
##            return s
##    pattern = re.compile(
##        r'//.*?$|/\*.*?\*/|\'(?:\\.|[^\\\'])*\'|"(?:\\.|[^\\"])*"',
##        re.DOTALL | re.MULTILINE
##    )
##    return re.sub(pattern, replacer, text)
##
## This picks up on any include statement, even those commented out by /* on earlier lines :(
## (It does work for //, though)
dafny_include_re = re.compile(r'^\s*include\s+"(\S+)"', re.M)

# helper to look up a Dafny BuildOptions matching a srcpath, from the 
# verify_options[] list, dealing with POSIX and Windows pathnames, and 
# falling back on a default if no specific override is present.
def get_build_options(srcpath):
  srcpath = os.path.normpath(srcpath)  # normalize the path, which, on Windows, switches to \\ separators
  srcpath = srcpath.replace('\\', '/') # switch to posix path separators

  if srcpath in verify_options:
    return verify_options[srcpath]
  else:
    for key in verify_options:
      if fnmatch.fnmatch (srcpath, key):
        return verify_options[key]
    ext = os.path.splitext(srcpath)[1]
    if ext in verify_options:
      return verify_options[ext]
    else:
      return None

# Scan a .dfy file to discover its dependencies, and add .vdfy targets for each.
# Returns a list of File representing the discovered .dfy dependencies.      
def dafny_file_scan(node, env, path):
    #print("Scanning " + str(node))
    contents = node.get_text_contents()
    dirname =  os.path.dirname(str(node))
    #output = docmd(env, '$DAFNY /nologo /ironDafny /noVerify /printIncludes:Transitive /deprecation:0 /noNLarith ' + str(node))
    #for o in output:
    #  print("Output " + o)
    
    includes = dafny_include_re.findall(contents)
    v_includes = []
    for i in includes:
      srcpath = os.path.join(dirname, i)
      # TODO : this should convert the .gen.dfy filename back to a src\...\.vad filename, and look up its options
      options = get_build_options(srcpath)
      if options != None:
        f = to_obj_dir(os.path.join(dirname, os.path.splitext(i)[0] + '.vdfy'))
        v_includes.append(f)
        options.env.Dafny(f, srcpath)
    return env.File(v_includes)

# Add env.dafny_scan(), to automatically scan .dfy files for dependencies
dafny_scan = Scanner(function = dafny_file_scan,
                     skeys = ['.dfy'])
if do_dafny:
  env.Append(SCANNERS = dafny_scan)

####################################################################
#
#   Define some transformation Builders
#
####################################################################

# Pseudo-builder that takes Dafny code verifies it
# Arguments:
#  targetfile - the target .vdfy to generate, as a string
#  sourcefile - the .dfy file to verify, as a string or File()
# Return:
#  File representing the verification result
def verify_dafny(env, targetfile, sourcefile):
  temptargetfile = os.path.splitext(targetfile)[0] + '.tmp'
  temptarget = env.Command(temptargetfile, sourcefile, "$MONO $DAFNY $VERIFIER_FLAGS $DAFNY_Z3_PATH $SOURCE $DAFNY_NO_VERIFY $DAFNY_USER_ARGS >$TARGET")
  return env.CopyAs(source=temptarget, target=targetfile)

# Add env.Dafny(), to verify a .dfy file into a .vdfy
def add_dafny_verifier(env):
  env.AddMethod(verify_dafny, "Dafny")

def on_black_list(f, list):
  for entry in list:
    if str(f).replace('\\','/').startswith(entry):
      return True
  return False

def verify_fstar(env, targetfile, sourcefile):
  temptargetfiles = [targetfile + '.tmp']
  hintsfile = str(sourcefile) + '.hints'
  hhintsfile = to_hints_dir(hintsfile)
  outs = []
  if min_test and on_black_list(sourcefile, min_test_suite_blacklist):
    print("Skipping %s because it is on the min_test_suite_blacklist defined in SConscript" % sourcefile)
    return outs
  # else:
  #   print("File %s is not on the blacklist" % str(sourcefile))

  if gen_hints:
    temptargetfiles.append(hintsfile)
  temptargets = env.Command(temptargetfiles, sourcefile, "$FSTAR $SOURCE $VERIFIER_FLAGS $FSTAR_Z3_PATH $FSTAR_NO_VERIFY $FSTAR_INCLUDES $FSTAR_USER_ARGS 1>$TARGET 2>&1")
  temptarget = temptargets[0]
  outs.append(env.CopyAs(source = temptarget, target = targetfile))
  if gen_hints:
    outs.append(env.CopyAs(source = temptargets[1], target = hhintsfile))
  elif os.path.isfile(hhintsfile):
    Depends(temptargets, env.CopyAs(source = hhintsfile, target = hintsfile))
  return outs

def ml_out_name(sourcefile, suffix):
  base_name = os.path.splitext(str(sourcefile))[0]
  module_name = os.path.split(base_name)[1]
  return 'obj/ml_out/' + module_name.replace('.', '_') + suffix

def extract_fstar(env, sourcefile):
  base_name = os.path.splitext(str(sourcefile))[0]
  module_name = os.path.split(base_name)[1]
  mlfile = ml_out_name(sourcefile, '.ml')
  Depends(mlfile, base_name + '.fst.verified')
  env = env.Clone(VERIFIER_FLAGS = env['VERIFIER_FLAGS'].replace("--use_extracted_interfaces true", ""))
  cmd_line = "$FSTAR $SOURCE $VERIFIER_FLAGS $FSTAR_Z3_PATH $FSTAR_NO_VERIFY $FSTAR_INCLUDES $FSTAR_USER_ARGS"
  cmd_line += " --odir obj/ml_out --codegen OCaml --admit_smt_queries true --extract_module " + module_name
  return env.Command(mlfile, sourcefile, cmd_line)

# Add env.FStar(), to verify a .fst or .fsti file into a .fst.verified or .fsti.verified
def add_fstar_verifier(env):
  env.AddMethod(verify_fstar, "FStar")

# Add env.FStar(), to verify a .fst or .fsti file into a .fst.verified or .fsti.verified
def add_fstar_extract(env):
  env.AddMethod(extract_fstar, "FStarExtract")

# Add env.DafnyCompile(), to compile without verification, a .dfy file into a .exe
def add_dafny_compiler(env):
  env['DAFNY_COMPILER_FLAGS'] = '/nologo /noVerify /compile:2'
  dafny_compiler = Builder(action='$MONO $DAFNY $DAFNY_COMPILER_FLAGS $SOURCE /out:$TARGET $DAFNY_USER_ARGS',
                           suffix = '.exe',
                           src_suffix = '.dfy')

  env.Append(BUILDERS = {'DafnyCompile' : dafny_compiler})

# Add env.DafnyKremlin(), to compile without verification, a .dfy file into a Kremlin .json.  
def add_dafny_kremlin(env):
  env['DAFNY_KREMLIN_FLAGS'] = dafny_default_args_larith + ' /nologo /kremlin /noVerify /compile:2 /spillTargetCode:1'
  dafny_kremlin = Builder(action='$MONO $DAFNY $DAFNY_KREMLIN_FLAGS $SOURCE /out:$TARGET $DAFNY_USER_ARGS',
                           suffix = '.json',
                           src_suffix = '.dfy')

  env.Append(BUILDERS = {'DafnyKremlin' : dafny_kremlin})

# Custom emitter for Kremlin .json->.c that also notes the generation of the matching .h file  
def kremlin_emitter(target, source, env):
  c_name = str(target[0])
  h_name = os.path.splitext(c_name)[0]+'.h'
  target.append(h_name)
  return target, source

# Add env.Kremlin(), to extract .c/.h from .json.  The builder returns
# two targets, the .c file first, followed by the .h file.
def add_kremlin(env):
  # In order to succeed, the Kremlin builder needs an extra directory in the
  # PATH on Windows so that the DLL can be properly found.
  if sys.platform == 'win32':
    gmp_dll = FindFile('libgmp-10.dll', os.environ['PATH'].split(';'))
    if gmp_dll != None:
      env.PrependENVPath('PATH', os.path.dirname(str(gmp_dll)))
  env['KREMLIN_FLAGS'] = '-fnouint128 -warn-error +1..4 -warn-error @4 -skip-compilation -add-include \\"DafnyLib.h\\" -cc msvc -drop FStar'
  kremlin = Builder(action='cd ${TARGET.dir} && ${KREMLIN.abspath} $KREMLIN_FLAGS ${SOURCE.file} $KREMLIN_USER_ARGS',
                           suffix = '.c',
                           src_suffix = '.json',
                           emitter = kremlin_emitter)
  # Copy pre-generated FStar.h; could be regenerared using
  # krml -fnouint128 -I ../kremlin/kremlib -skip-compilation ulib/FStar.UInt128.fst
  env.CopyAs(source='src/crypto/hashing/FStar.h', target='obj/crypto/hashing/FStar.h')
  env.Append(BUILDERS = {'Kremlin' : kremlin})

# Pseudo-builder that takes Dafny code and extracts it via Kremlin
# Arguments:
#  kremlin_dfys - a list of .dfy files to extract to C
# Return:
#  A set of targets, two per dfy, the first for the .c file and the second for the .h file
def extract_dafny_code(env, kremlin_dfys):
  kremlin_outputs = []
  for k in kremlin_dfys:
    # generate .json from .dfy
    json_file = os.path.splitext(to_obj_dir(k))[0]+'.json' # dest is in obj\ dir and has .json extension instead of .dfy
    json = env.DafnyKremlin(source=k, target=json_file)
    # generate .c from .json
    json_split = os.path.split(json_file) # [0] is the pathname, [1] is the filename
    target_path = json_split[0]
    json_file = json_split[1]
    target_file_base = os.path.join(target_path, os.path.splitext(json_file)[0].replace('.', '_'))
    target_file_c = target_file_base+'.c'
    target_file_h = target_file_base+'.h'
    if 'KREMLIN_HOME' in os.environ:
      outputs = env.Kremlin(source=json, target=target_file_c)
      kremlin_outputs.append(outputs)
  return kremlin_outputs

# Compile Vale .vad to Dafny .gen.dfy
# Takes a source .vad file as a string
# Returns a File() representing the resulting .gen.dfy file
def compile_vale_dafny(env, source_vad):
  target_s = os.path.splitext(to_obj_dir(source_vad))[0]+'.gen.dfy'
  target_dfy = env.ValeDafny(source=source_vad, target=target_s)
  return target_dfy

# Compile Vale .vaf to FStar .fst/fsti pair
# Takes a source .vaf file as a string
# Returns list of File() representing the resulting .fst and .fsti files
def compile_vale_fstar(env, source_vaf):
  s = os.path.splitext(to_obj_dir(source_vaf))[0]
  target_s = s + '.fst'
  target_si = s + '.fsti'
  targets = env.ValeFStar(source=source_vaf, target=[target_s, target_si])
  return targets

ml_out_deps = {}

def extract_vale_ocaml(env, output_base_name, main_name, alg_name, cmdline_name):
  # OCaml depends on many libraries and executables; we have to assume they are in the user's PATH:
  ocaml_env = Environment(ENV = {'PATH' : os.environ['PATH'], 'OCAMLPATH' : env['FSTAR_PATH'] + '/bin'})
  main_ml = ml_out_name(main_name, '.ml')
  main_cmx = ml_out_name(main_name, '.cmx')
  main_exe = ml_out_name(main_name, '.exe')
  alg_ml = ml_out_name(alg_name, '.ml')
  alg_cmx = ml_out_name(alg_name, '.cmx')
  cmdline_ml = ml_out_name(cmdline_name, '.ml')
  cmdline_cmx = ml_out_name(cmdline_name, '.cmx')
  pointer_src = 'src/lib/util/FStar_Pointer_Base.ml'
  pointer_ml = ml_out_name(pointer_src, '.ml')
  pointer_cmx = ml_out_name(pointer_src, '.cmx')
  env.Command(pointer_ml, pointer_src, Copy("$TARGET", "$SOURCE"))
  env.Command(cmdline_ml, cmdline_name, Copy("$TARGET", "$SOURCE"))
  env.Command(main_ml, main_name, Copy("$TARGET", "$SOURCE"))
  Depends(cmdline_cmx, alg_cmx)
  Depends(cmdline_cmx, cmdline_ml)
  Depends(main_cmx, alg_cmx)
  Depends(main_cmx, cmdline_cmx)
  Depends(main_cmx, main_ml)
  done = set()
  cmxs = []
  def add_cmx(x_ml):
    x_cmx = ml_out_name(x_ml, '.cmx')
    if x_ml != pointer_ml:
      Depends(x_cmx, pointer_cmx)
    cmx = ocaml_env.Command(x_cmx, x_ml, "ocamlfind ocamlopt -c -package fstarlib -o $TARGET $SOURCE -I obj/ml_out")
    cmxs.append(cmx[0])
    Depends(main_exe, cmx[0])
  def collect_cmxs_in_order(x_ml):
    if not (x_ml in done):
      done.add(x_ml)
      for y_ml in ml_out_deps[x_ml]:
        # if x depends on y, y must appear first in ocaml link step
        Depends(ml_out_name(x_ml, '.cmx'), ml_out_name(y_ml, '.cmx'))
        collect_cmxs_in_order(y_ml)
      Depends(x_ml, pointer_ml)
      add_cmx(x_ml)
  add_cmx(pointer_ml)
  collect_cmxs_in_order(alg_ml)
  add_cmx(cmdline_ml)
  add_cmx(main_ml)
  cmxs_string = " ".join([str(cmx) for cmx in cmxs])
  exe = ocaml_env.Command(main_exe, cmxs, "ocamlfind ocamlopt -linkpkg -package fstarlib " + cmxs_string + " -o $TARGET")

  output_target_base = 'obj/' + output_base_name
  masm_win = env.Command(output_target_base + '.asm', exe, '$SOURCE MASM Win > $TARGET')
  gcc_win = env.Command(output_target_base + '-gcc.S', exe, '$SOURCE GCC Win > $TARGET')
  gcc_linux = env.Command(output_target_base + '-linux.S', exe, '$SOURCE GCC Linux > $TARGET')
  gcc_macos = env.Command(output_target_base + '-macos.S', exe, '$SOURCE GCC MacOS > $TARGET')
  
  if sys.platform.startswith('linux'):
    return [gcc_linux, masm_win, gcc_win, gcc_macos]
  elif sys.platform == 'win32':
    return [masm_win, gcc_win, gcc_linux, gcc_macos]
  elif sys.platform == 'cygwin':
    return [gcc_win, masm_win, gcc_linux, gcc_macos]
  elif sys.platform == 'darwin':
    return [gcc_macos, gcc_win, masm_win, gcc_linux]
  else:
    print('Unsupported sys.platform value: ' + sys.platform)

# Pseudo-builder that takes Vale code, a main .dfy, and generates a Vale EXE which then emits .asm files
# Arguments:
#  vads - a list of vad files to extract
#  vad_main_dfy - the main .dfy used to drive extraction
#  output_base_name - the base name to use for the EXE and ASM files, such as "sha256" to generate "obj\sha256.asm/.s"
# Return:
#  Multiple targets, which are the assembly source files for all platforms.  The first one is the correct file for 
#  the current OS platform (ie. the .s file when running on a POSIX OS, or the .asm on Windows).  The subsequent
#  ones are for other OS platforms, in no particular order.
def extract_vale_code(env, vads, vad_main_dfy, output_base_name):
  # generate decls.gen.dfy from decls.vad
  vale_outputs = []
  for s in vads:
    outputs = compile_vale_dafny(env, s)
    vale_outputs.append(File(env.subst(s)))
  output_target_base = 'obj/'+output_base_name
  ionative = os.path.normpath('src/lib/util/IoNative.cs')
  exe_name = output_target_base+'.exe'
  exe = env.Clone(DAFNY_COMPILER_FLAGS=dafny_default_args_larith + ' /nologo /noVerify /compile:2 '+ionative).DafnyCompile(
    source=vad_main_dfy, target=exe_name)
  Depends(exe, ionative)
  Depends(exe, vale_outputs) # todo: this should be implicitly generated by scanning the vad_main_dfy file.  Is it?
  
  masm_win = env.Command(output_target_base+'.asm', exe, '$MONO $SOURCE MASM Win > $TARGET')
  gcc_win = env.Command(output_target_base+'-gcc.S', exe, '$MONO $SOURCE GCC Win > $TARGET')
  gcc_linux = env.Command(output_target_base+'-linux.S', exe, '$MONO $SOURCE GCC Linux > $TARGET')
  gcc_macos = env.Command(output_target_base+'-macos.S', exe, '$MONO $SOURCE GCC MacOS > $TARGET')
  
  if sys.platform.startswith('linux'):
    return [gcc_linux, masm_win, gcc_win, gcc_macos]
  elif sys.platform == 'win32':
    return [masm_win, gcc_win, gcc_linux, gcc_macos]
  elif sys.platform == 'cygwin':
    return [gcc_win, masm_win, gcc_linux, gcc_macos]
  elif sys.platform == 'darwin':
    return [gcc_macos, gcc_win, masm_win, gcc_linux]
  else:
    print('Unsupported sys.platform value: ' + sys.platform)
  
# build and execute a test app
# inputs - set of files to build into the resulting exe
# include_dir - an extra include directory - usually the path to the kremlin-generated headers
# output_base_name - base filename (no path, no extension) to build into the obj\ directory
# returns the exe target and the stdout after executing the exe test target
def build_test(env, inputs, include_dir, output_base_name):
  testenv = env.Clone()
  if 'KREMLIN_HOME' in os.environ:
    testenv.Append(CPPPATH=[kremlib_path, 'src/lib/util', include_dir])
  else:
    # We need gcc_compat.h from kremlib:
    testenv.Append(CPPPATH=['#tools/Kremlin/kremlib', 'src/lib/util', include_dir])
  inputs_obj = []
  for inp in inputs:
    inps = str(inp)
    if inps.startswith('src/'):
      inp = env.CopyAs(source=inp, target=to_obj_dir(inps))
    inputs_obj.append(inp)
  if sys.platform == 'win32':
    built = testenv.Program(source=inputs_obj, target=['obj/'+output_base_name+'.exe', 'obj/'+output_base_name+'.pdb'])
    exe = built[0]
  else:
    built = testenv.Program(source=inputs_obj, target='obj/'+output_base_name+'.exe')
    exe = built
  testoutput = 'obj/'+output_base_name+'.txt'
  env.Command(target=testoutput,
              source=exe,
              action = [exe, 'echo ABC > ' + testoutput])
  a = env.Alias('runtest', '', built)
  #AlwaysBuild(a)
  return a

# Add pseudobuilders to env.  
def add_extract_code(env):
  env.AddMethod(extract_vale_ocaml, "ExtractValeOCaml")
  env.AddMethod(extract_vale_code, "ExtractValeCode")
  env.AddMethod(extract_dafny_code, "ExtractDafnyCode")
  env.AddMethod(build_test, "BuildTest")

# Helper class used by the src/SConscript file, to specify per-file
# command-line options for verification.
class BuildOptions:
  # First argument is mandatory (verification options); all others are optional named arguments
  def __init__(self, args, valeIncludes = None):
    self.env = env.Clone(VERIFIER_FLAGS=args)
    if valeIncludes != None:
      self.env = self.env.Clone(VALE_INCLUDE=valeIncludes)

# Verify a set of Dafny files by creating verification targets for each,
# which in turn causes a dependency scan to verify all of their dependencies.
def verify_dafny_files(env, files):
  for f in files:
    options = get_build_options(f)
    if options != None and verify == True:
      target = os.path.splitext(to_obj_dir(f))[0] + '.vdfy'
      options.env.Dafny(target, f)

# Verify .fst and/or .fsti files
def verify_fstar_files(env, files):
  for f in files:
    options = get_build_options(f)
    if options != None and verify:
      o = to_obj_dir(f)
      env.Command(o, f, Copy("$TARGET", "$SOURCE"))
      if stage2:
        target = o + '.verified'
        options.env.FStar(target, o)
        if fstar_extract:
          if os.path.splitext(o)[1] == '.fst':
            options.env.FStarExtract(o)

# Verify a set of Vale files by creating verification targets for each,
# which in turn causes a dependency scan to verify all of their dependencies.
def verify_vale_dafny_files(env, files):
  for f in files:
    options = get_build_options(f)
    if options != None:
      dfy = compile_vale_dafny(env, f)
      if verify == True:
        dfy_str = str(dfy[0]).replace('\\', '/')  # switch from Windows to Unix path ahead of calling get_build_options()
        dafny_gen_options = get_build_options(dfy_str)
        target = os.path.splitext(to_obj_dir(f))[0] + '.gen.vdfy'
        dafny_gen_options.env.Dafny(target, dfy)

def verify_vale_fstar_files(env, files):
  for f in files:
    options = get_build_options(f)
    if options != None:
      fsts = compile_vale_fstar(options.env, f)
      if verify == True and stage2:
        fst_str = str(fsts[0]).replace('\\', '/')
        fsti_str = str(fsts[1]).replace('\\', '/')
        fstar_gen_options = get_build_options(fst_str)
        fstari_gen_options = get_build_options(fsti_str)
        s = os.path.splitext(to_obj_dir(f))[0]
        target = s + '.fst.verified'
        targeti = s + '.fsti.verified'
        fstar_gen_options.env.FStar(target, fsts[0])
        fstari_gen_options.env.FStar(targeti, fsts[1])
        if fstar_extract:
          fstar_gen_options.env.FStarExtract(fsts[0])

def recursive_glob(env, pattern, strings=False):
  matches = []
  split = os.path.split(pattern) # [0] is the directory, [1] is the actual pattern
  platform_directory =  split[0] #os.path.normpath(split[0])
  for d in os.listdir(platform_directory):
    if os.path.isdir(os.path.join(platform_directory, d)):
      newpattern = os.path.join(split[0], d, split[1])
      matches.append(recursive_glob(env, newpattern, strings))
  
  files = env.Glob(pattern, strings=strings)
  matches.append(files)
  return Flatten(matches)

# Verify *.dfy, *.vad, *.fst, *.vaf files in a list of directories.  This enumerates
# all files in those trees, and creates verification targets for each,
# which in turn causes a dependency scan to verify all of their dependencies.
def verify_files_in(env, directories):
  for d in directories:
    if do_dafny:
      files = recursive_glob(env, d+'/*.dfy', strings=True)
      verify_dafny_files(env, files)
      files = recursive_glob(env, d+'/*.vad', strings=True)
      verify_vale_dafny_files(env, files)
    if do_fstar:
      if is_single_vaf:
        files = [single_vaf]
        verify_vale_fstar_files(env, files)
      else:
        files = recursive_glob(env, d+'/*.fst', strings=True)
        verify_fstar_files(env, files)
        files = recursive_glob(env, d+'/*.fsti', strings=True)
        verify_fstar_files(env, files)
        files = recursive_glob(env, d+'/*.vaf', strings=True)
        verify_vale_fstar_files(env, files)
    
def check_fstar_z3_version(fstar_z3):
  import subprocess
  z3_version_file = ".fstar_z3_version"
  if os.path.isfile(z3_version_file):
    with open(z3_version_file, 'r') as myfile:
      lines = myfile.read().splitlines()
    version = lines[0]
    versions = version.split('.')
    cmd = [fstar_z3, '--version']
    o = subprocess.check_output(cmd, stderr = subprocess.STDOUT).decode('ascii')
    lines = o.splitlines()
    line = lines[0]
    for word in line.split(' '):
      if '.' in word:
        nums = word.split('.')
        higher = False
        lower = False
        for i in range(min(len(nums), len(versions))):
          if nums[i] < versions[i]:
            lower = True
            break
          if nums[i] > versions[i]:
            higher = True
            break
        if higher or (not lower and len(nums) >= len(versions)):
          return
        break
    print('%sExpected Z3 version >= %s%s%s, but z3 --version returned the following:%s' % (colors['red'], colors['yellow'], version, colors['red'], colors['end']))
    for line in lines:
      print('  ' + line)
    print('%sGet a recent Z3 executable from https://github.com/FStarLang/binaries/tree/master/z3-tested, modify .fstar_z3_version, or use the --FSTAR-Z3-MY-VERSION option to override%s' % (colors['cyan'], colors['end']))
    Exit(1)

def check_fstar_version():
  import subprocess
  fstar_version_file = ".fstar_version"
  if os.path.isfile(fstar_version_file):
    with open(fstar_version_file, 'r') as myfile:
      lines = myfile.read().splitlines()
    version = lines[0]
    fstar = str(env['FSTAR'])
    cmd = [fstar, '--version']
    o = subprocess.check_output(cmd, stderr = subprocess.STDOUT).decode('ascii')
    lines = o.splitlines()
    for line in lines:
      if '=' in line:
        key, v = line.split('=', 1)
        if key == 'commit' and v == version:
          return
    print('%sExpected F* version %scommit=%s%s, but fstar --version returned the following:%s' % (colors['red'], colors['yellow'], version, colors['red'], colors['end']))
    for line in lines:
      print('  ' + line)
    print('%sGet F* version %s from https://github.com/FStarLang/FStar, modify .fstar_version, or use the --FSTAR-MY-VERSION option to override%s' % (colors['cyan'], version, colors['end']))
    Exit(1)

####################################################################
#
#   FStar dependency analysis
#
####################################################################

def predict_fstar_deps(env, verify_options, src_directories, fstar_include_paths):
  import subprocess
  # find all .fst, .fsti, and .vaf files in src_directories
  fst_files = []
  vaf_files = []
  for d in src_directories:
    fst_files.extend(recursive_glob(env, d+'/*.fst', strings=True))
    fst_files.extend(recursive_glob(env, d+'/*.fsti', strings=True))
    vaf_files.extend(recursive_glob(env, d+'/*.vaf', strings=True))
  # use fst_files and vaf_files to choose .fst and .fsti files that need dependency analysis
  # (including .fst and .fsti in obj directory generated from source .vaf files)
  files = []
  for f in fst_files:
    options = get_build_options(f)
    if options != None:
      files.append(to_obj_dir(f))
  for f in vaf_files:
    options = get_build_options(f)
    if options != None:
      s = os.path.splitext(to_obj_dir(f))[0]
      for t in [s + '.fst', s + '.fsti']:
        if os.path.isfile(t):
          files.append(t)
  # call fstar --dep make
  includes = []
  for include in fstar_include_paths:
    includes += ["--include", include]
  fstar = str(env['FSTAR'])
  lines = []
  depsBackupFile = 'obj/fstarDepsBackup.d'
  print('%sF* dependency analysis: starting%s' % (colors['cyan'], colors['end']))
  args = ["--dep", "make"] + includes + files
  cmd = [fstar] + args
  print(" ".join(cmd))
  try:
    o = subprocess.check_output(cmd, stderr = subprocess.STDOUT).decode('ascii')
  except (subprocess.CalledProcessError) as e:
    print('%sF* dependency analysis: error: %s %s' % (colors['red'], e.output, colors['end']))
    raise e
  print('%sF* dependency analysis: done%s' % (colors['cyan'], colors['end']))
  fstar_deps_ok = True
  lines = o.splitlines()
  for line in lines:
    if 'Warning:' in line:
      print(line)
      fstar_deps_ok = False
    if len(line) == 0:
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
      sources_ver = [to_obj_dir(re.sub('\.fst$', '.fst.verified', re.sub('\.fsti$', '.fsti.verified', x))) for x in sources if has_obj_dir(x)]
      targets_ver = [to_obj_dir(re.sub('\.fst$', '.fst.verified.tmp', re.sub('\.fsti$', '.fsti.verified.tmp', x))) for x in targets if has_obj_dir(x)]
      Depends(targets_ver, sources_ver)
      if fstar_extract:
        sources_ml = [ml_out_name(x, '.ml') for x in sources if has_obj_dir(x)]
        targets_ml = [ml_out_name(x, '.ml') for x in targets if has_obj_dir(x)]
        sources_ml = [x for x in sources_ml if not (x in targets_ml)]
        Depends(targets_ml, sources_ml)
        for t in targets_ml:
          if not (t in ml_out_deps):
            ml_out_deps[t] = set()
          for s in sources_ml:
            ml_out_deps[t].add(s)
  if fstar_deps_ok:
    # Save results in depsBackupFile
    with open(depsBackupFile, 'w') as myfile:
      for line in lines:
        myfile.write(line + '\n')
  else:
    raise Exception('%sF* dependency analysis failed%s' % (colors['red'], colors['end']))

####################################################################
#
#   Put it all together
#
####################################################################
add_dafny_verifier(env)
add_fstar_verifier(env)
add_fstar_extract(env)
add_dafny_compiler(env)
add_dafny_kremlin(env)
add_vale_builders(env)
if do_fstar or 'KREMLIN_HOME' in os.environ:
  add_kremlin(env)
add_extract_code(env)
env.AddMethod(verify_files_in, "VerifyFilesIn")
env.AddMethod(verify_vale_dafny_files, "VerifyValeDafnyFiles")
env.AddMethod(verify_dafny_files, "VerifyDafnyFiles")
env.AddMethod(verify_vale_fstar_files, "VerifyValeFStarFiles")
env.AddMethod(verify_fstar_files, "VerifyFStarFiles")

#
# Pull in the SConscript files which define actual build targets:
#

# Export identifiers to make them visible inside SConscript files
Export('env', 'BuildOptions', 'dafny_default_args_nlarith', 'dafny_default_args_larith', 'fstar_default_args', 'fstar_default_args_nosmtencoding', 'do_dafny', 'do_fstar', 'stage2', 'fstar_extract')

# Include the SConscript files themselves
vale_tool_results = SConscript('tools/Vale/SConscript')
vale_deps = vale_tool_results.dependencies;
env['Z3'] = vale_tool_results.z3
if sys.platform == 'win32':
  env['DAFNY_Z3_PATH'] = '' # use the default Boogie search rule, which uses Z3 from the tools/Dafny directory
else:
  env['DAFNY_Z3_PATH'] = '/z3exe:$Z3'

# Check F* version
if do_fstar and not fstar_my_version:
  check_fstar_version()

# Find Z3 for F*
if do_fstar and verify:
  fstar_z3 = GetOption('fstar_z3')
  if fstar_z3 == '':
    fstar_z3 = 'tools\\Z3\\z3.exe' if sys.platform == 'win32' else 'tools/Z3/z3'
    if not os.path.isfile(fstar_z3):
      if sys.platform == 'win32':
        find_z3 = FindFile('z3.exe', os.environ['PATH'].split(';'))
      else:
        find_z3 = FindFile('z3', os.environ['PATH'].split(':'))
      if find_z3 == None:
        print('%sCould not find z3 executable.  Either put z3 in your path, or put it in the directory tools/Z3/, or use the --FSTARZ3=<z3-executable> option.%s' % (colors['red'], colors['end']))
        Exit(1)
      else:
        fstar_z3 = str(find_z3)
  if not fstar_z3_my_version:
    check_fstar_z3_version(fstar_z3)
  env['FSTAR_Z3_PATH'] = '--smt ' + fstar_z3
else:
  env['FSTAR_Z3_PATH'] = ''

SConscript('./SConscript')

# Import identifiers defined inside SConscript files, which the SConstruct consumes
Import(['manual_dependencies', 'verify_options', 'verify_paths', 'fstar_include_paths', 'min_test_suite_blacklist'])

env['FSTAR_INCLUDES'] = " ".join(["--include " + x for x in fstar_include_paths])

# F* dependencies
if do_fstar and stage2 and not is_single_vaf:
  import distutils.dir_util
  # create obj directory
  distutils.dir_util.mkpath('obj')
  for d in fstar_include_paths:
    if d.startswith('obj/'):
      distutils.dir_util.mkpath(d)
  for target in manual_dependencies:
    source = manual_dependencies[target]
    Depends(target, source)
  predict_fstar_deps(env, verify_options, verify_paths, fstar_include_paths)

# Verification
env.VerifyFilesIn(verify_paths)

#
# build aesgcm
#
if fstar_extract and stage2:
  aesgcm_asm = env.ExtractValeOCaml('aesgcm', 'src/crypto/aes/x64/Main.ml', 'src/crypto/aes/x64/X64.GCMdecrypt.vaf', 'src/lib/util/CmdLineParser.ml')
  if env['TARGET_ARCH'] == 'amd64': 
    aesgcmasm_obj = env.Object('obj/aesgcmasm_openssl', aesgcm_asm[0])
    aesgcmtest_src = 'src/crypto/aes/x64/TestAesGcm.cpp'
    aesgcmtest_cpp = to_obj_dir(aesgcmtest_src)
    env.Command(aesgcmtest_cpp, aesgcmtest_src, Copy("$TARGET", "$SOURCE"))
    aesgcmtest_exe = env.Program(source = [aesgcmasm_obj, aesgcmtest_cpp], target = 'obj/TestAesGcm.exe')

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
              errorfilename = filename[:-len('.tmp')] + '.error'
              if os.path.isfile(errorfilename):
                os.remove(errorfilename)
              print('##### %sVerification error%s. ' % (colors['red'], colors['end']))
              print('Printing contents of ' + filename + ' #####')
              with open (filename, 'r') as myfile:
                lines = myfile.read().splitlines()
                valeErrors = [line for line in lines if ("*****" in line)]
                lastValeErrors = valeErrors[-1:]
                for line in lines:
                  if "(Error)" in line or "failed" in line or line in lastValeErrors:
                    line = "%s%s%s" % (colors['red'], line, colors['end'])
                  print(line)
              time.sleep(1)
              os.rename(filename, errorfilename)

def display_build_status():
  report_verification_failures()

def print_env_options(options):
  for option in options:
    if option in env and len(env[option]) > 0:
      print("%s " % env[option], end='')

if GetOption('dump_args'):
  print("Currently using the following F* args:")
  print_env_options(['VERIFIER_FLAGS', 'FSTAR_Z3_PATH', 'FSTAR_NO_VERIFY', 'FSTAR_INCLUDES', 'FSTAR_USER_ARGS'])
  print(fstar_default_args)
  sys.exit(1)

atexit.register(display_build_status)
