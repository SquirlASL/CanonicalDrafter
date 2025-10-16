import Lake
open Lake DSL

package canonicaldrafter where
  name := `CanonicalDrafter
  defaultTargets := #["canonicaldrafter-wrapper"]
  supportInterpreter := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.23.0"

require Canonical from git
  "https://github.com/chasenorman/CanonicalLean" @ "v4.23.0"

require REPL from git "https://github.com/leanprover-community/repl" @ "2f8073af0a5e3a141fee075652790a2c19132516"

require llmlean from git
  "https://github.com/FrederickPu/llmlean.git"  @ "unify-generation"

lean_lib CanonicalDrafter where
  -- Your library code here if needed

lean_lib Test where

lean_exe test {
  root := `Test
}

lean_exe extract_data {
  root := `ExtractData
}
