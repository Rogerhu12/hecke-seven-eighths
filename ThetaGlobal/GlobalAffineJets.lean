import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Module.Multilinear.Topology

/-! A local smooth chart may be restricted to an affine linear family
without requiring a globally smooth extension of that chart. -/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalAffineJets

open Set
open scoped ContDiff

variable {E G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem iteratedFDeriv_comp_affine
    (L : E →L[ℝ] G) (a : G) (f : G → H) (s : Set G)
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s)
    (x : E) (hx : a + L x ∈ s) (n : ℕ) :
    iteratedFDeriv ℝ n (fun y => f (a + L y)) x =
      (iteratedFDeriv ℝ n f (a + L x)).compContinuousLinearMap (fun _ => L) := by
  let t : Set G := (fun y : G => a + y) ⁻¹' s
  have ht : IsOpen t := hs.preimage (continuous_const.add continuous_id)
  have hg : ContDiffOn ℝ ∞ (fun y : G => f (a + y)) t :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ h => h)
  have htx : L x ∈ t := hx
  have h := L.iteratedFDerivWithin_comp_right hg ht.uniqueDiffOn
    (ht.preimage L.continuous).uniqueDiffOn htx (i := n) (by simp)
  rw [iteratedFDerivWithin_of_isOpen n (ht.preimage L.continuous) htx,
    iteratedFDerivWithin_of_isOpen n ht htx,
    iteratedFDeriv_comp_add_left] at h
  exact h

end ThetaGlobal.GlobalAffineJets
