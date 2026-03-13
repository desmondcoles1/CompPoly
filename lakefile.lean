import Lake

open System Lake DSL

package CompPoly where
  version := v!"0.1.0"
  testDriver := "CompPolyTests"

require "leanprover-community" / mathlib @ git "v4.28.0"

require ExtTreeMapLemmas from git "https://github.com/Verified-zkEVM/ExtTreeMapLemmas"@"v4.28.0"

@[default_target]
lean_lib CompPoly

lean_lib CompPolyTests where
  srcDir := "tests"

/-- Compile clmul64.c into a static library for FFI linking. -/
extern_lib compoly_clmul (pkg) := do
  let oFile := pkg.buildDir / "c" / "clmul64.o"
  let srcJob ← inputTextFile <| pkg.dir / "CompPoly" / "Fields" / "Binary" / "clmul64.c"
  let flags := #["-I", (← getLeanIncludeDir).toString, "-O2"]
  let oJob ← buildO oFile srcJob flags
  let libName := nameToStaticLib "compoly_clmul"
  buildStaticLib (pkg.buildDir / "lib" / libName) #[oJob]

/-- Benchmark: compare reference clMul against C-backed and pure-Lean Karatsuba. -/
lean_exe benchFastMul where
  root := `CompPoly.Fields.Binary.BenchForFastMul
  supportInterpreter := false

