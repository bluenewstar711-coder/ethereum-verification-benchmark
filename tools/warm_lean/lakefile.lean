import Lake
open Lake DSL

package «warm-lean» where

@[default_target]
lean_exe «warm-lean» where
  root := `WarmLean
  supportInterpreter := true
