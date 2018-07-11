#
# Main file for building Vale source code, under the src\tree
#

# Python imports
import os, os.path
import sys

# Imported identifiers defined in the SConstruct file
Import('env', 'BuildOptions', 'fstar_default_args', 'fstar_default_args_nosmtencoding', 'do_fstar', 'stage1', 'stage2', 'fstar_extract')

#
# Verify *.vaf and *.fst{i} under src/test/ and tools/vale/test/
#
verify_paths = [
  'src/',
  'tools/Vale/test',
]
Export('verify_paths')

external_files = [
  'obj/external/CanonCommSwaps.fst',
  'obj/external/CanonCommMonoid.fst',
  'obj/external/CanonCommSemiring.fst',
]
Export('external_files')

no_extraction_files = [
  'obj/ml_out/CanonCommMonoid.ml',
  'obj/ml_out/CanonCommSemiring.ml',
  'obj/ml_out/X64_Poly1305_Math_i.ml',
  'obj/ml_out/Vale_Tactics.ml',
]
Export('no_extraction_files')

manual_dependencies = {
  'obj/arch/x64/X64.Vale.InsBasic.fst.verified.tmp': 'obj/arch/x64/X64.Vale.Decls_i.fst',
  'obj/arch/x64/X64.Vale.InsMem.fst.verified.tmp': 'obj/arch/x64/X64.Vale.Decls_i.fst',
  'obj/arch/x64/X64.Vale.InsVector.fst.verified.tmp': 'obj/arch/x64/X64.Vale.Decls_i.fst',
  'obj/arch/x64/X64.Vale.InsAes.fst.verified.tmp': 'obj/arch/x64/X64.Vale.Decls_i.fst',

  'obj/arch/x64/X64.Vale.InsMem.fst.tmp': 'obj/arch/x64/X64.Memory_i.fst',
  'obj/arch/x64/X64.Vale.InsVector.fst.tmp': 'obj/arch/x64/X64.Memory_i.fst',
  'obj/arch/x64/X64.Vale.StateLemmas_i.fsti.tmp': 'obj/arch/x64/X64.Memory_i.fst',
  'obj/arch/x64/X64.Vale.StateLemmas_i.fst.tmp': 'obj/arch/x64/X64.Memory_i.fst',
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
  'obj/Vale/test',
  'obj/test',
  'obj/arch',
  'obj/arch/x64/',
  'obj/arch/x64/interop',
  'obj/lib/collections/',
  'obj/lib/math',
  'obj/lib/util',
  'obj/crypto/aes/',
  'obj/crypto/aes/x64',
  'obj/crypto/poly1305/',
  'obj/crypto/poly1305/x64/',
  'obj/thirdPartyPorts/OpenSSL/poly1305/x64/',
  'obj/external/'
]
Export('fstar_include_paths')
env['FSTAR_INCLUDES'] = " ".join(["--include " + x for x in fstar_include_paths])

#
# Table of special-case source which requires non-default arguments
#
verify_options = {
  'src/lib/util/operator.vaf': BuildOptions(fstar_default_args, valeIncludes = ''),

  # Any use of expose_interfaces       - [ ] `crypto/poly1305/x64/X64.Poly1305.Util_i.fsti`: `lemma_poly1305_heap_hash_blocks_alt` requires adding to manual_dependencies
  'obj/arch/x64/X64.Vale.InsBasic.fst': BuildOptions(fstar_default_args + ' --expose_interfaces obj/arch/x64/X64.Vale.Decls_i.fst' + ' --expose_interfaces obj/arch/x64/X64.Memory_i.fst'),
  'obj/arch/x64/X64.Vale.InsMem.fst': BuildOptions(fstar_default_args + ' --expose_interfaces obj/arch/x64/X64.Vale.Decls_i.fst' + ' --expose_interfaces obj/arch/x64/X64.Memory_i.fst'),
  'obj/arch/x64/X64.Vale.InsVector.fst': BuildOptions(fstar_default_args + ' --expose_interfaces obj/arch/x64/X64.Vale.Decls_i.fst' + ' --expose_interfaces obj/arch/x64/X64.Memory_i.fst'),
  'obj/arch/x64/X64.Vale.InsAes.fst': BuildOptions(fstar_default_args + ' --expose_interfaces obj/arch/x64/X64.Vale.Decls_i.fst' + ' --expose_interfaces obj/arch/x64/X64.Memory_i.fst'),
  'src/arch/x64/X64.Vale.StateLemmas_i.fsti': BuildOptions(fstar_default_args + ' --expose_interfaces obj/arch/x64/X64.Memory_i.fst'),
  'src/arch/x64/X64.Vale.StateLemmas_i.fst': BuildOptions(fstar_default_args + ' --expose_interfaces obj/arch/x64/X64.Memory_i.fst'),
  'src/arch/x64/X64.Vale.Lemmas_i.fsti': BuildOptions(fstar_default_args + ' --expose_interfaces obj/arch/x64/X64.Memory_i.fst'),
  'src/arch/x64/X64.Vale.Lemmas_i.fst': BuildOptions(fstar_default_args + ' --expose_interfaces obj/arch/x64/X64.Memory_i.fst'),
  'src/arch/x64/X64.Vale.Decls_i.fst': BuildOptions(fstar_default_args + ' --expose_interfaces obj/arch/x64/X64.Memory_i.fst'),

  # Special treatment for sensitive modules
  'src/arch/x64/X64.Leakage_Ins_i.fst': BuildOptions(fstar_default_args_nosmtencoding),

  # Disable verification by adding 'filename': None
  'tools/Vale/test/vale-debug.vad': None,
  'tools/Vale/test/tactics1.vaf': None,
  'src/crypto/aes/x64/Low.GCMencrypt.fst': None,
#  'src/arch/x64/interop/*.fst': None,
#  'src/arch/x64/interop/*.fsti': None,

  
  #'src/thirdPartyPorts/OpenSSL/poly1305/x64/X64.Poly1305.vaf': None,

  'src/*/*.fst': BuildOptions(fstar_default_args),
  'src/*/*.fsti': BuildOptions(fstar_default_args),

  'src/arch/x64/interop/Interop_assumptions.fst': BuildOptions(fstar_default_args),
  'src/arch/x64/interop/Interop_Printer.fst': BuildOptions(fstar_default_args),
  'src/arch/x64/interop/*.fst': BuildOptions(fstar_default_args_nosmtencoding.replace('--z3cliopt smt.QI.EAGER_THRESHOLD=100', '').replace('--use_extracted_interfaces true', '').replace('--z3cliopt smt.arith.nl=false', '') + '--smtencoding.elim_box true ' + ' --expose_interfaces SecretByte.fst --expose_interfaces X64.Memory_i_s.fst --expose_interfaces X64.Memory_i.fst'),

  # .fst/.fsti files default to this set of options
  '.fst': BuildOptions(fstar_default_args + ' --use_two_phase_tc false'),
  '.fsti': BuildOptions(fstar_default_args + ' --use_two_phase_tc false'),

  'obj/lib/collections/Collections.Lists_i.fst': BuildOptions(fstar_default_args.replace('--z3cliopt smt.QI.EAGER_THRESHOLD=100','')),
  'src/crypto/poly1305/x64/X64.Poly1305.Util_i.fst': BuildOptions(fstar_default_args_nosmtencoding),
  'src/crypto/poly1305/x64/X64.Poly1305.Util_i.fsti': BuildOptions(fstar_default_args_nosmtencoding),
  'src/arch/x64/X64.Bytes_Semantics_i.fst': BuildOptions(fstar_default_args.replace('--smtencoding.nl_arith_repr wrapped', '--smtencoding.nl_arith_repr native')),
  'src/arch/x64/X64.Memory_i_s.fst': BuildOptions(fstar_default_args_nosmtencoding.replace('--z3cliopt smt.QI.EAGER_THRESHOLD=100', '').replace('--use_extracted_interfaces true', '').replace('--z3cliopt smt.arith.nl=false', '') + '--smtencoding.elim_box true ' + ' --expose_interfaces obj/arch/SecretByte.fst'),
  'src/arch/x64/Interop.fst': BuildOptions(fstar_default_args_nosmtencoding.replace('--use_extracted_interfaces true', '') + '--smtencoding.elim_box true '),
  'src/arch/Memory_s.fst': BuildOptions(fstar_default_args.replace('--use_extracted_interfaces true', '')),
  'src/lib/util/BufferViewHelpers.fst' : BuildOptions(fstar_default_args_nosmtencoding.replace('--z3cliopt smt.arith.nl=false', '')),

  # We copy these files from F*'s library because we need to generate a .checked file for them,
  # but we don't need to reverify them:
  'obj/external/*.fst': BuildOptions('--cache_checked_modules --admit_smt_queries true'),

  # .vaf files default to this set of options when compiling .fst/.fsti
  '.vaf': BuildOptions(fstar_default_args  + ' --use_two_phase_tc false'),
}
if env['TARGET_ARCH'] != 'x86':
  verify_options['src/test/memcpy.vad'] = None
  verify_options['src/test/stack-test.vad'] = None

if do_fstar and stage1:
  for x in ['CanonCommSwaps.fst', 'CanonCommMonoid.fst', 'CanonCommSemiring.fst']:
    env.Command('obj/external/' + x, env['FSTAR_PATH'] + '/examples/tactics/' + x, Copy("$TARGET", "$SOURCE"))
  if 'KREMLIN_HOME' in os.environ:
    for x in ['C.Loops.fst']:
      env.Command('obj/external/' + x, env['KREMLIN_HOME'] + '/kremlib/' + x, Copy("$TARGET", "$SOURCE"))
 

Export('verify_options')
