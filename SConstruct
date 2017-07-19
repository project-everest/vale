import re
import sys
import os, os.path
import subprocess
import traceback
import pdb
import SCons.Util
import atexit
import platform

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
  aes_arch_dir='aes-x64'
envDict = {'TARGET_ARCH':target_arch,
           'X':target_x,
           'ARCH':'src/arch/x$X',
           'SHA_ARCH_DIR':sha_arch_dir,
           'AES_ARCH_DIR':aes_arch_dir}

env = Environment(**envDict)
if sys.platform == 'win32':
  env.Replace(CCPDBFLAGS='/Zi /Fd${TARGET.base}.pdb')
  # Use kremlib.h without primitive support for uint128_t.
  env.Append(CCFLAGS=['/Ox', '/Gz', '/DKRML_NOUINT128'])
  env.Append(LINKFLAGS=['/DEBUG'])
  if os.getenv('PLATFORM')=='X64':
    env['AS'] = 'ml64'
else:
  env.Append(CCFLAGS=['-O3', '-flto', '-g', '-DKRML_NOUINT128'])
  env['MONO'] = 'mono'

# Convert NUMBER_OF_PROCESSORS into '-j n'.
#num_cpu = int(os.environ.get('NUMBER_OF_PROCESSORS', 1)) 
#SetOption('num_jobs', num_cpu) 

if 'FSTAR_HOME' in os.environ:
  fstar_default_path = os.environ['FSTAR_HOME']
else:
  fstar_default_path = '#tools/FStar'

# Retrieve tool-specific command overrides passed in by the user
AddOption('--DAFNY',
  dest='do_dafny',
  default=True,
  action='store_true',
  help='Verify Dafny files')
AddOption('--NODAFNY',
  dest='do_dafny',
  default=True,
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
  default=False,
  action='store_true',
  help='Verify F* files')
AddOption('--NOFSTAR',
  dest='do_fstar',
  default=False,
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
AddOption('--NOCOLOR',
  dest='nocolor',
  default=False,
  action='store_true',
  help="Don't add color to build output")

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
else:
  kremlin_path = '#tools/Kremlin'
  env['KREMLIN'] = File(kremlin_path + '/Kremlin.native')

env['VALE'] = File('bin/vale.exe')

kremlib_path = kremlin_path + '/kremlib'

# Useful Dafny command lines
dafny_default_args_nlarith =   '/ironDafny /allocated:1 /induction:1 /compile:0 /timeLimit:30 /errorLimit:1 /errorTrace:0 /trace'
dafny_default_args_larith = dafny_default_args_nlarith + ' /noNLarith'

fstar_default_args = '--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3'\
  + ' --z3cliopt smt.arith.nl=false --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped'\
  + ' --max_fuel 0 --max_ifuel 1 --initial_ifuel 0 --hint_info --record_hints --use_hints'

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
   for key, value in colors.iteritems():
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
    print formatExceptionInfo()
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
  vale_dafny_builder = Builder(action = "$MONO $VALE -includeSuffix .vad .gen.dfy -in $SOURCE -out $TARGET $VALE_USER_ARGS",
                            suffix = '.gen.dfy',
                            src_suffix = '.vad',
                            emitter = vale_tool_dependency_Emitter)
  vale_fstar_builder = Builder(action = "$MONO $VALE -fstarText -in $SOURCE -out $TARGET -outi ${TARGET}i $VALE_USER_ARGS",
                            src_suffix = '.vaf',
                            emitter = vale_tool_dependency_Emitter)
  env.Append(BUILDERS = {'ValeDafny' : vale_dafny_builder})
  env.Append(BUILDERS = {'ValeFStar' : vale_fstar_builder})

vale_verbatim_include_re = re.compile(r'^\s*include verbatim\s+"(\S+)"', re.M)
vale_vale_include_re = re.compile(r'^\s*include\s+"(\S+)"', re.M)

def vale_dafny_file_scan(node, env, path):
  contents = node.get_text_contents()
  dirname =  os.path.dirname(str(node))

  dfy_includes = vale_verbatim_include_re.findall(contents)
  vad_includes = vale_vale_include_re.findall(contents)

  v_dfy_includes = []
  v_vad_includes = []
  for i in dfy_includes:
    f = os.path.join(dirname, i)
    v_dfy_includes.append(f)
    v = os.path.join(to_obj_dir(dirname), os.path.splitext(i)[0] + '.vdfy')
    env.Dafny(v, f)
  for i in vad_includes:
    #v = to_obj_dir(os.path.join(dirname, os.path.splitext(i)[0] + '.vdfy'))
    f = os.path.join(dirname, i)
    v_vad_includes.append(f)

  files = env.File(v_dfy_includes + v_vad_includes) 
  return files

def vale_fstar_file_scan(node, env, path):
  contents = node.get_text_contents()
  dirname =  os.path.dirname(str(node))

  vaf_includes = vale_vale_include_re.findall(contents)

  v_vaf_includes = []
  for i in vaf_includes:
    f = os.path.join(dirname, i)
    v_vaf_includes.append(f)
    # if A.vaf includes B.vaf, then manually establish these dependencies:
    #   A.vfst  depends on B.fsti
    #   A.vfsti depends on B.fsti
    # note that A.vfst and A.vfsti may also have other dependencies; we rely on F*'s dependency analysis for these
    f_fsti = os.path.splitext(to_obj_dir(os.path.normpath(f)))[0] + '.vfsti'
    node_o = to_obj_dir(str(node))
    node_o_base = os.path.splitext(node_o)[0]
    Depends([node_o_base + '.vfst.tmp', node_o_base + '.vfsti.tmp'], f_fsti)

  files = env.File(v_vaf_includes) 
  return files

vale_dafny_scan = Scanner(function = vale_dafny_file_scan,
                     skeys = ['.vad'])
vale_fstar_scan = Scanner(function = vale_fstar_file_scan,
                     skeys = ['.vaf'])
if do_dafny:
  env.Append(SCANNERS = vale_dafny_scan)
if do_fstar:
  env.Append(SCANNERS = vale_fstar_scan)


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

def has_obj_dir(path):
  path = os.path.relpath(path)
  path = path.replace('\\', '/')
  return path.startswith('obj/') or path.startswith('src/') or path.startswith('tools/')

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

def verify_fstar(env, targetfile, sourcefile):
  temptargetfile = targetfile + '.tmp'
  temptarget = env.Command(temptargetfile, sourcefile, "$FSTAR $VERIFIER_FLAGS $FSTAR_Z3_PATH $SOURCE $FSTAR_NO_VERIFY $FSTAR_INCLUDES $FSTAR_USER_ARGS 1>$TARGET 2>&1")
  return env.CopyAs(source=temptarget, target=targetfile)

# Add env.FStar(), to verify a .fst or .fsti file into a .vfst or .vfsti
def add_fstar_verifier(env):
  env.AddMethod(verify_fstar, "FStar")

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
  testenv.Append(CPPPATH=[kremlib_path, 'src/lib/util', include_dir])
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
  env.AddMethod(extract_vale_code, "ExtractValeCode")
  env.AddMethod(extract_dafny_code, "ExtractDafnyCode")
  env.AddMethod(build_test, "BuildTest")

# Helper class used by the src/SConscript file, to specify per-file
# Dafny command-line options for verification.  
class BuildOptions:
  def __init__(self, args):
    self.env = env.Clone(VERIFIER_FLAGS=args)

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
      s = os.path.splitext(to_obj_dir(f))
      target = s[0] + '.v' + s[1].replace('.', '')
      options.env.FStar(target, f)

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
      fsts = compile_vale_fstar(env, f)
      if verify == True:
        fst_str = str(fsts[0]).replace('\\', '/')
        fsti_str = str(fsts[1]).replace('\\', '/')
        fstar_gen_options = get_build_options(fst_str)
        fstari_gen_options = get_build_options(fsti_str)
        s = os.path.splitext(to_obj_dir(f))[0]
        target = s + '.vfst'
        targeti = s + '.vfsti'
        fstar_gen_options.env.FStar(target, fsts[0])
        fstari_gen_options.env.FStar(targeti, fsts[1])

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
      files = recursive_glob(env, d+'/*.fst', strings=True)
      verify_fstar_files(env, files)
      files = recursive_glob(env, d+'/*.fsti', strings=True)
      verify_fstar_files(env, files)
      files = recursive_glob(env, d+'/*.vaf', strings=True)
      verify_vale_fstar_files(env, files)
    
####################################################################
#
#   FStar dependency analysis
#
####################################################################

fstar_deps_ok = False

# Use F*'s dependency analysis to determine dependencies for .fst/.fsti files,
# and predict dependencies for .fst/.fsti files generated from .vaf files.
# Unfortunately, whenever a .vaf file changes its dependencies, we end up
# verifying twice: once because the .vaf file changed, and again (in the
# next invocation of scons) because the dependencies changed.  This also
# happens for the very first build.
# We could remove this redundancy if we ran scons in two stages: first,
# to generate the tools and compile the .vaf files, and second to run
# F*'s dependency analysis and verify the .fst/.fsti files.
def predict_fstar_deps(env, verify_options, src_directories, fstar_include_paths):
  import subprocess
  global fstar_deps_ok
  import distutils.dir_util
  # create obj directory
  distutils.dir_util.mkpath('obj')
  for d in fstar_include_paths:
    if d.startswith('obj/'):
      distutils.dir_util.mkpath(d)
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
      files.append(f)
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
  try:
    print('%sF* dependency analysis: starting%s' % (colors['blue'], colors['end']))
    args = ["--dep", "make"] + includes + files
    cmd = [fstar] + args
    print(" ".join(cmd))
    o = subprocess.check_output(cmd, stderr = subprocess.STDOUT)
    print('%sF* dependency analysis: done%s' % (colors['blue'], colors['end']))
    fstar_deps_ok = True
    lines = o.splitlines()
  except subprocess.CalledProcessError as e:
    print(e)
    print(e.output)
    print('%sF* dependency analysis: done, but with errors%s' % (colors['red'], colors['end']))
    if os.path.isfile(depsBackupFile):
      print('  loading dependencies from ' + depsBackupFile)
      with open(depsBackupFile, 'r') as myfile:
        lines = myfile.read().splitlines()
  for line in lines:
    if 'Warning:' in line:
      print(line)
      fstar_deps_ok = False
    else:
      # lines are of the form:
      #   a1.fst a2.fst ... : b1.fst b2.fst ...
      # we change this to:
      #   obj\...\a1.vfst obj\...\a2.vfst ... : b1.fst b2.fst ...
      # we ignore targets that we will not verify (e.g. F* standard libraries)
      targets, sources = line.split(': ', 1) # ': ', not ':', because of Windows drive letters
      sources = sources.split()
      targets = targets.split()
      targets = [to_obj_dir(re.sub('\.fst$', '.vfst.tmp', re.sub('\.fsti$', '.vfsti.tmp', x))) for x in targets if has_obj_dir(x)]
      if not fstar_deps_ok:
        # If dependency analysis failed, remove non-existent sources so that scons can make progress
        # Otherwise, scons won't recompile the .vaf files, so the dependencies will never get fixed
        sources = [x for x in sources if os.path.isfile(x)]
      Depends(targets, sources)
  if fstar_deps_ok:
    # Save results in depsBackupFile
    # This can be used in case of errors in future invocations of scons
    with open(depsBackupFile, 'w') as myfile:
      for line in lines:
        myfile.write(line + '\n')

####################################################################
#
#   Put it all together
#
####################################################################
add_dafny_verifier(env)
add_fstar_verifier(env)
add_dafny_compiler(env)
add_dafny_kremlin(env)
add_vale_builders(env)
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
Export('env', 'BuildOptions', 'dafny_default_args_nlarith', 'dafny_default_args_larith', 'fstar_default_args', 'do_dafny', 'do_fstar')

# Include the SConscript files themselves
vale_tool_results = SConscript('tools/Vale/SConscript')
vale_deps = vale_tool_results.dependencies;
env['Z3'] = vale_tool_results.z3
if sys.platform == 'win32':
  env['DAFNY_Z3_PATH'] = '' # use the default Boogie search rule, which uses Z3 from the tools/Dafny directory
else:
  env['DAFNY_Z3_PATH'] = '/z3exe:$Z3'

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
        print('Could not find z3 executable.  Either put z3 in your path, or put it in the directory tools/Z3/, or use the --FSTARZ3=<z3-executable> option.')
        Exit(1)
      else:
        fstar_z3 = str(find_z3)
  env['FSTAR_Z3_PATH'] = '--smt ' + fstar_z3
else:
  env['FSTAR_Z3_PATH'] = ''

SConscript('./SConscript')

# Import identifiers defined inside SConscript files, which the SConstruct consumes
Import(['verify_options', 'verify_paths', 'fstar_include_paths'])

env['FSTAR_INCLUDES'] = " ".join(["--include " + x for x in fstar_include_paths])

# F* dependencies
if do_fstar:
  predict_fstar_deps(env, verify_options, verify_paths, fstar_include_paths)

# Verification
env.VerifyFilesIn(verify_paths)

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
    from SCons.Script import GetBuildFailures
    bf = GetBuildFailures()
    if bf:
        # bf is normally a list of build failures; if an element is None,
        # it's because of a target that scons doesn't know anything about.
        for x in bf:
          if x is not None:
            filename = bf_to_filename(x)
            if filename.endswith('.tmp') and os.path.isfile(filename):
              print '##### %sVerification error%s. ' % (colors['red'], colors['end']),
              print 'Printing contents of ' + filename + ' #####' 
              with open (filename, 'r') as myfile:
                lines = myfile.read().splitlines()
                for line in lines:
                  if "(Error)" in line:
                    line = "%s%s%s" % (colors['red'], line, colors['end'])
                  print line

def display_build_status():
  report_verification_failures()
  if do_fstar and not fstar_deps_ok:
    raise Exception('%sInitial F* dependency analysis failed; you might need to run scons again.%s' % (colors['red'], colors['end']))

atexit.register(display_build_status)
