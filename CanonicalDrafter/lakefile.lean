import Lake
open Lake DSL

package canonicaldrafter where
  name := `CanonicalDrafter
  defaultTargets := #["canonicaldrafter-wrapper"]
  supportInterpreter := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.21.0"

require "chasenorman" / "Canonical"

require REPL from git "https://github.com/leanprover-community/repl" @ "v4.21.0"

lean_lib CanonicalDrafter where
  -- Your library code here if needed

lean_lib Test where

lean_exe test {
  root := `Test
}
