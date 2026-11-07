module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.SimpRw
public import Mathlib.Tactic.SplitIfs
public import Lean.Elab.Tactic.Omega
public import Lean.Elab.Tactic.NormCast
public import Lean.Elab.Tactic.Ext

@[expose] public section

/-! Only the proof tactics used by these modules. This avoids importing
the complete tactic collection into every algebraic and analytic file. -/
