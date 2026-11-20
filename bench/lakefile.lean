import Lake
open Lake DSL System

package «distillery-bench»

require distillery from ".."
require «distillery-demo» from "../demo"

/-- The instruction counter of the driver, a C function over `perf_event_open`. -/
target instructions.o pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "ffi" / "instructions.c")
  let oFile := pkg.buildDir / "ffi" / "instructions.o"
  let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC", "-O2"]
  buildO oFile src flags #[] "cc"

extern_lib libbenchffi pkg := do
  let name := nameToStaticLib "benchffi"
  buildStaticLib (pkg.staticLibDir / name) #[← instructions.o.fetch]

/-- The driver runs compiled, so that it can call the instruction counter. -/
lean_lib Driver where
  srcDir := "lib"
  precompileModules := true

lean_lib Cases where
  srcDir := "cases"
  globs := #[.submodules `Cases]

lean_lib CasesX64 where
  srcDir := "casesx64"
  globs := #[.submodules `CasesX64]

@[default_target]
lean_lib Bench where
  roots := #[`distill_adc_chain, `distill_dite_split, `distill_match_split, `distill_let_binding, `distill_ifs_jp, `distill_matches_jp, `distill_wide_jp, `distill_add_sub_cancel, `distill_add_sub_cancel_deep, `distill_add_sub_cancel_simp, `distill_backtrack, `distill_catch, `distill_entries, `distill_get_throw_set, `distill_holes, `distill_loop, `distill_match_iota, `distill_pure_precond, `distill_reader_state, `distill_reg_file, `distill_table, `distill_word_abs, `distill_word_abs_val]

@[default_target]
lean_lib BenchX64 where
  roots := #[`x64_array, `x64_calls, `x64_frame, `x64_straight]
