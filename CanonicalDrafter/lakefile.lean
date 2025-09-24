import Lake
open Lake DSL

package canonicaldrafter where
  name := `CanonicalDrafter
  defaultTargets := #["canonicaldrafter-wrapper"]
  supportInterpreter := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.22.0"

require Canonical from git
  "https://github.com/chasenorman/CanonicalLean" @ "v4.22.0"

require REPL from git "https://github.com/leanprover-community/repl" @ "v4.22.0"

lean_lib CanonicalDrafter where
  -- Your library code here if needed

lean_lib Test where

lean_exe test {
  root := `Test
}

lean_exe extract_data {
  root := `ExtractData
}
