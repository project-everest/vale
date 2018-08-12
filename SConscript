#
# Main file for building Vale source code, under the src\tree
#

# Python imports
import os, os.path
import sys

# Imported identifiers defined in the SConstruct file
Import('env', 'BuildOptions', 'dafny_default_args_nlarith', 'dafny_default_args_larith', 'fstar_default_args', 'fstar_default_args_nosmtencoding', 'do_dafny', 'do_fstar', 'stage1', 'stage2', 'fstar_extract')

#
# Verify *.vad and *.dfy under src/test/ and tools/vale/test/
#
verify_paths = [
  'src/',
  'tools/Vale/test',
]
Export('verify_paths')

external_files = [
]
Export('external_files')

no_extraction_files = [
]
Export('no_extraction_files')

manual_dependencies = {
  'obj/arch/x64/X64.Vale.InsBasic.fst.verified.tmp': 'obj/arch/x64/X64.Vale.Decls_i.fst',
  'obj/arch/x64/X64.Vale.InsMem.fst.verified.tmp': 'obj/arch/x64/X64.Vale.Decls_i.fst',
  'obj/arch/x64/X64.Vale.InsVector.fst.verified.tmp': 'obj/arch/x64/X64.Vale.Decls_i.fst',
  'obj/arch/x64/X64.Vale.InsAes.fst.verified.tmp': 'obj/arch/x64/X64.Vale.Decls_i.fst',
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
  'obj/lib/collections/',
  'obj/lib/math',
  'obj/lib/util',
  'obj/external/'
]
Export('fstar_include_paths')
env['FSTAR_INCLUDES'] = " ".join(["--include " + x for x in fstar_include_paths])

#
# Table of special-case Dafny source which requires non-default arguments
#
verify_options = {
  'src/arch/arm/nlarith.s.dfy': BuildOptions(dafny_default_args_nlarith),
  'src/arch/arm/bitvectors.i.dfy': BuildOptions(dafny_default_args_larith + ' /proverOpt:OPTIMIZE_FOR_BV=true'),
  'src/lib/math/mul_nonlinear.i.dfy': BuildOptions(dafny_default_args_nlarith),
  'src/lib/math/div_nonlinear.i.dfy': BuildOptions(dafny_default_args_nlarith),
  'src/lib/math/div.i.dfy': BuildOptions(dafny_default_args_larith + ' /timeLimit:60'),
  'src/lib/util/operations.i.dfy': BuildOptions(dafny_default_args_larith + ' /proverOpt:OPTIMIZE_FOR_BV=true'),
  'src/lib/util/operator.vaf': BuildOptions(fstar_default_args, valeIncludes = ''),

  # Any use of expose_interfaces requires adding to manual_dependencies
  'obj/arch/x64/X64.Vale.InsBasic.fst': BuildOptions(fstar_default_args + ' --expose_interfaces obj/arch/x64/X64.Vale.Decls_i.fst'),
  'obj/arch/x64/X64.Vale.InsMem.fst': BuildOptions(fstar_default_args + ' --expose_interfaces obj/arch/x64/X64.Vale.Decls_i.fst'),
  'obj/arch/x64/X64.Vale.InsVector.fst': BuildOptions(fstar_default_args + ' --expose_interfaces obj/arch/x64/X64.Vale.Decls_i.fst'),

  # .dfy files default to this set of options
  '.dfy': BuildOptions(dafny_default_args_larith),

  # Special treatment for sensitive modules
  'src/arch/x64/X64.Leakage_Ins_i.fst': BuildOptions(fstar_default_args_nosmtencoding),

  # Disable verification by adding 'filename': None
  'src/test/Test.FastBlock.vaf': None,
  'src/arch/x64/X64.Taint_Semantics_s.fst': None,
  'src/arch/x64/X64.Leakage_s.fst': None,
  'src/arch/x64/X64.Leakage_Ins_i.fst': None,
  'src/arch/x64/X64.Leakage_i.fst': None,
  'src/arch/x64/X64.Leakage_Helpers_i.fst': None,
#  'src/arch/x64/X64.Bytes_Semantics_i.fst': None,
  'tools/Vale/test/vale-debug.vad': None,
  'tools/Vale/test/tactics1.vaf': None,

  #'src/thirdPartyPorts/OpenSSL/poly1305/x64/X64.Poly1305.vaf': None,

  'src/*/*.fst': BuildOptions(fstar_default_args),
  'src/*/*.fsti': BuildOptions(fstar_default_args),

  # .fst/.fsti files default to this set of options
  '.fst': BuildOptions(fstar_default_args + ' --use_two_phase_tc false'),
  '.fsti': BuildOptions(fstar_default_args + ' --use_two_phase_tc false'),

  'src/arch/x64/X64.Bytes_Semantics_i.fst': BuildOptions(fstar_default_args.replace('--smtencoding.nl_arith_repr wrapped', '--smtencoding.nl_arith_repr native')),
  'src/arch/x64/Interop.fst': BuildOptions(fstar_default_args_nosmtencoding.replace('--use_extracted_interfaces true', '') + '--smtencoding.elim_box true '),
  'src/arch/x64/X64.Memory_i_s.fst': BuildOptions(fstar_default_args_nosmtencoding.replace('--use_extracted_interfaces true', '').replace('--z3cliopt smt.arith.nl=false', '') + '--smtencoding.elim_box true '),
  'src/arch/Memory_s.fst': BuildOptions(fstar_default_args.replace('--use_extracted_interfaces true', '')),

  # We copy these files from F*'s library because we need to generate a .checked file for them,
  # but we don't need to reverify them:
  'obj/external/*.fst': BuildOptions('--cache_checked_modules --admit_smt_queries true'),

  # .vad/.vaf files default to this set of options when compiling .gen.dfy/.fst/.fsti
  '.vad': BuildOptions(dafny_default_args_larith),
  '.vaf': BuildOptions(fstar_default_args  + ' --use_two_phase_tc false'),
}
if env['TARGET_ARCH'] != 'x86':
  verify_options['src/test/memcpy.vad'] = None
  verify_options['src/test/stack-test.vad'] = None

Export('verify_options')

#
# Table of files we exclude from the minimal test suite
# (typically for performance reasons)
# Note that the entries below are prefixes of blacklisted files
#
min_test_suite_blacklist = [
]

Export('min_test_suite_blacklist')

