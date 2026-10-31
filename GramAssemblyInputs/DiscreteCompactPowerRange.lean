import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Order

/-!
UNCOMPILED / native 0. A power image is closed in a topological monoid
isomorphic to a discrete monoid times a compact Hausdorff monoid.
Only continuity of multiplication on the compact factor is needed.
This is a general topological lemma, with no local-field or class-field input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HeckeGeneral.Analysis.DiscreteCompactPowerRangeDraft

open Set

variable {G D C : Type*} [Monoid G] [Monoid D] [Monoid C]
variable [TopologicalSpace G] [TopologicalSpace D] [TopologicalSpace C]
variable [DiscreteTopology D] [CompactSpace C] [T2Space C] [ContinuousMul C]

/-- A power image is closed after an actual multiplicative homeomorphism
with a discrete factor and a compact Hausdorff factor. No positivity or
nonvanishing condition on the natural-number exponent is necessary. -/
theorem isClosed_range_pow_of_discrete_compact (e : G ≃ₜ* D × C) (n : ℕ) :
    IsClosed (Set.range (fun g : G => g ^ n)) := by
  have hD : IsClosed (Set.range (fun d : D => d ^ n)) := isClosed_discrete _
  have hC : IsClosed (Set.range (fun c : C => c ^ n)) :=
    (isCompact_range (continuous_pow n)).isClosed
  have heq : Set.range (fun g : G => g ^ n) =
      e.toHomeomorph ⁻¹' (Set.range (fun d : D => d ^ n) ×ˢ
        Set.range (fun c : C => c ^ n)) := by
    ext g
    change (∃ x : G, x ^ n = g) ↔
      (∃ d : D, d ^ n = (e g).1) ∧ (∃ c : C, c ^ n = (e g).2)
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨⟨(e x).1, ?_⟩, ⟨(e x).2, ?_⟩⟩
      · exact congrArg Prod.fst (map_pow e x n).symm
      · exact congrArg Prod.snd (map_pow e x n).symm
    · rintro ⟨⟨d, hd⟩, ⟨c, hc⟩⟩
      refine ⟨e.symm (d, c), e.injective ?_⟩
      rw [map_pow, e.apply_symm_apply]
      exact Prod.ext hd hc
  rw [heq]
  exact e.toHomeomorph.isClosed_preimage.mpr (hD.prod hC)

end HeckeGeneral.Analysis.DiscreteCompactPowerRangeDraft
