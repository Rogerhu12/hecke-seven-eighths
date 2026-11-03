import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Ext

/-! Only the proof tactics used by these modules. This avoids importing
the complete tactic collection into every algebraic and analytic file. -/
