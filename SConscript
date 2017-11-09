#
# Main file for building Vale source code, under the src\tree
#

# Python imports
import os, os.path
import sys

# Imported identifiers defined in the SConstruct file
Import('env', 'BuildOptions', 'dafny_default_args_nlarith', 'dafny_default_args_larith', 'fstar_default_args', 'fstar_default_args_nosmtencoding', 'do_dafny', 'do_fstar')

#
# Verify *.vad and *.dfy under src/test/ and tools/vale/test/
#
verify_paths = [
  'src/',
  'tools/Vale/test',
]
Export('verify_paths')

# A few .fst/.fsti files depend on .fsti files generated from .vaf files.
# Without manually writing the dependencies for these, the dependency
# analysis will miss them the first time scons runs.
manual_dependencies = {
  'obj/arch/x64/X64.Vale.StrongPost_i.vfsti.tmp': 'obj/arch/x64/X64.Vale.Decls.fsti',
  'obj/arch/x64/X64.Vale.StrongPost_i.vfst.tmp': 'obj/arch/x64/X64.Vale.Decls.fsti',
  'obj/Vale/test/StateUpdateTest.vfst.tmp': 'obj/arch/x64/X64.Vale.Decls.fsti',
}
Export('manual_dependencies')

#
# All include paths for FStar should be in this list.
# All files should use exactly the include paths in this list.
# All .fst files and .fsti files in the include paths should have distinct names.
# Otherwise, the dependency analysis will not be able to find all the
# dependencies for all the files using just one invocation of FStar.exe --dep.
#
# For .vaf files, the generated .fst and .fsti files live under the obj directory,
# so the include path should contain obj/... for any .vaf files.
#
fstar_include_paths = [
  'tools/Vale/test',
  'obj/Vale/test',
  'src/test',
  'obj/test',
  'src/arch/x64/',
  'obj/arch/x64/',
  'src/lib/collections/',
  'src/lib/util',
  'src/crypto/poly1305/',
  'src/crypto/poly1305/x64/',
  'obj/thirdPartyPorts/OpenSSL/poly1305/x64/',
]
Export('fstar_include_paths')
env['FSTAR_INCLUDES'] = " ".join(["--include " + x for x in fstar_include_paths])

#
# Table of special-case Dafny source which requires non-default arguments
#
verify_options = {
  'src/arch/arm/nlarith.s.dfy': BuildOptions(dafny_default_args_nlarith),
  'src/arch/arm/bitvectors.i.dfy': BuildOptions(dafny_default_args_larith + ' /proverOpt:OPTIMIZE_FOR_BV=true'),
  'src/crypto/aes/aes-x64/aes_main.i.dfy': BuildOptions(dafny_default_args_larith),
  'src/lib/math/mul_nonlinear.i.dfy': BuildOptions(dafny_default_args_nlarith),
  'src/lib/math/div_nonlinear.i.dfy': BuildOptions(dafny_default_args_nlarith),
  'src/crypto/hashing/sha-arm/bit-vector-lemmas.i.dfy': BuildOptions(dafny_default_args_larith + ' /proverOpt:OPTIMIZE_FOR_BV=true'),
  'src/crypto/hashing/sha-x64/sha256_vale_main.i.dfy': BuildOptions(dafny_default_args_larith),
  'src/lib/math/div.i.dfy': BuildOptions(dafny_default_args_larith + ' /timeLimit:60'),
  'src/lib/util/operations.i.dfy': BuildOptions(dafny_default_args_larith + ' /proverOpt:OPTIMIZE_FOR_BV=true'),
  'obj/crypto/aes/cbc.gen.dfy': BuildOptions(dafny_default_args_larith + ' /timeLimit:120'),
  'obj/crypto/aes/aes-x64/cbc.gen.dfy': BuildOptions(dafny_default_args_larith + ' /timeLimit:120'),

  # .dfy files default to this set of options
  '.dfy': BuildOptions(dafny_default_args_larith),

  # Special treatment for the taint analysis
  'src/arch/x64/X64.Leakage_Ins_i.fst': BuildOptions(fstar_default_args_nosmtencoding),

  # .fst/.fsti files default to this set of options
  '.fst': BuildOptions(fstar_default_args),
  '.fsti': BuildOptions(fstar_default_args),

  'tools/Vale/test/vale-debug.vad': None,
  'tools/Vale/test/tactics1.vaf': None,

  # .vad/.vaf files default to this set of options when compiling .gen.dfy/.fst/.fsti
  '.vad': BuildOptions(dafny_default_args_larith),
  '.vaf': BuildOptions(fstar_default_args),

  # Disable verification by adding 'filename': None
}
if env['TARGET_ARCH']!='x86':
 verify_options['src/test/memcpy.vad'] = None
 verify_options['src/test/stack-test.vad'] = None
 
Export('verify_options')

#
# Table of files we export to F*'s test suite
#
fstar_test_suite = [
  'src/arch/x64/',
  'src/crypto/poly1305/x64/',
  'src/lib/util/',
  'src/lib/collections/',
  'obj/thirdPartyPorts/OpenSSL/poly1305/',
  'obj/thirdPartyPorts/OpenSSL/poly1305/x64/',
  'obj/arch/x64/X64.Vale.Decls.fst',
  'obj/arch/x64/X64.Vale.Decls.fsti'
]

Export('fstar_test_suite')

#
# build sha256-exe
#
if do_dafny:
  sha_asm = env.ExtractValeCode(
    ['src/crypto/hashing/$SHA_ARCH_DIR/sha256.vad'],           # Vale source
    'src/crypto/hashing/$SHA_ARCH_DIR/sha256_vale_main.i.dfy', # Dafny main
    'sha256'                                                   # Base name for the ASM files and EXE
    )
  if 'KREMLIN_HOME' in os.environ:
    sha_c_h = env.ExtractDafnyCode(['src/crypto/hashing/sha256_main.i.dfy'])
    sha_include_dir = os.path.split(str(sha_c_h[0][1]))[0]
    env.BuildTest(['src/crypto/hashing/testsha256.c', sha_asm[0], sha_c_h[0][0]], sha_include_dir, 'testsha256')

#
# build cbc-exe
#
if do_dafny and (env['TARGET_ARCH']=='x86' or env['TARGET_ARCH']=='amd64'):   # x86 and x64 only
  cbc_asm = env.ExtractValeCode(
    ['src/crypto/aes/$AES_ARCH_DIR/aes.vad', 'src/crypto/aes/$AES_ARCH_DIR/cbc.vad'], # Vale source
    'src/crypto/aes/$AES_ARCH_DIR/cbc_main.i.dfy',              # Dafny main
    'cbc'                                                       # Base name for the ASM files and EXE
    )
  env.BuildTest(['src/crypto/aes/testcbc.c', cbc_asm[0]], '', 'testcbc')
else:
  print('Not building AES-CBC for this target architecture')

#
# build aes-exe
#
if do_dafny and (env['TARGET_ARCH']=='x86' or env['TARGET_ARCH']=='amd64'):   # x86 and x64 only
  aes_asm = env.ExtractValeCode(
    ['src/crypto/aes/$AES_ARCH_DIR/aes.vad'],        # Vale source
    'src/crypto/aes/$AES_ARCH_DIR/aes_main.i.dfy',   # Dafny main
    'aes'                                            # Base name for the ASM files and EXE
    )
  env.BuildTest(['src/crypto/aes/testaes.c', aes_asm[0]], 'src/crypto/aes', 'testaes')
else:
  print('Not building AES for this target architecture')

#
# build poly1305
#
if do_dafny and env['TARGET_ARCH']=='amd64' and sys.platform == "win32":     # x64-only; not yet tested on Linux
  poly1305_asm = env.ExtractValeCode(
    ['src/thirdPartyPorts/OpenSSL/poly1305/x64/poly1305.vad'],  # Vale source
    'src/crypto/poly1305/x64/poly1305_main.i.dfy',              # Dafny main
    'poly1305'                                                  # Base name for the ASM files and EXE
    )
  env.BuildTest(['src/crypto/poly1305/testpoly1305.c', poly1305_asm[0]], 'src/crypto/poly1305', 'testpoly1305')
else:
  print('Not building Poly1305 for this target architecture')

if 'KREMLIN_HOME' in os.environ:
  kremlin_path = os.environ['KREMLIN_HOME']
  kremlib_path = kremlin_path + '/kremlib'

#
# Build the OpenSSL engine
#
if do_dafny and env['OPENSSL_PATH'] != None and 'KREMLIN_HOME' in os.environ:
  engineenv = env.Clone()
  engineenv.Append(CPPPATH=[kremlib_path, '#obj/crypto/hashing', '$OPENSSL_PATH/include', '#src/lib/util'])
  cdeclenv = engineenv.Clone(CCFLAGS='/Ox /Zi /Gd /LD') # compile __cdecl so it can call OpenSSL code
  stdcallenv=engineenv.Clone(CCFLAGS='/Ox /Zi /Gz /LD') # compile __stdcall so it can call the Vale crypto code
  everest_sha256 = cdeclenv.Object('src/Crypto/hashing/EverestSha256.c')
  everest_glue = stdcallenv.Object('src/Crypto/hashing/EverestSHA256Glue.c')
  if env['TARGET_ARCH']=='x86':
    sha256_obj = engineenv.Object('obj/sha256_openssl', sha_c_h[0][0])
    cbc_obj = engineenv.Object('obj/cbc_openssl', cbc_asm[0])
    aes_obj = engineenv.Object('obj/aes_openssl', sha_asm[0])
    engine = engineenv.SharedLibrary(target='obj/EverestSha256.dll',
      source=[everest_sha256, everest_glue, sha256_obj, cbc_obj, aes_obj, '$OPENSSL_PATH/libcrypto.lib'])
  if env['TARGET_ARCH']=='amd64' and sys.platform == "win32":
    sha256_obj = engineenv.Object('obj/sha256_openssl', sha_c_h[0][0])
    sha256asm_obj = engineenv.Object('obj/sha256asm_openssl', sha_asm[0])
    poly1305_obj = engineenv.Object('obj/poly1305_openssl', poly1305_asm[0])
    engine = engineenv.SharedLibrary(target='obj/EverestSha256.dll',
      source=[everest_sha256, everest_glue, sha256_obj, sha256asm_obj, poly1305_obj, '$OPENSSL_PATH/libcrypto.lib'])

