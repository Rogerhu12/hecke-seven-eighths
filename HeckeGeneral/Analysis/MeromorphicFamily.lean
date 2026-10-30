import HeckeGeneral.Analysis.EndpointClosure
import HeckeGeneral.Analysis.MeromorphicDescent

/-!
# Connecting the family closure to meromorphic functions

Zeros are defined by positive meromorphic order, so poles cannot become
spurious zeros through a convention for the value of a total function.
The seed and strict improvement remain explicit analytic hypotheses.
-/

namespace HeckeGeneral.Analysis

noncomputable section

/-- Real parts of genuine zeros of a meromorphic germ. -/
def zeroRealParts (f : ℂ → ℂ) : Set ℝ :=
  {r | ∃ z : ℂ, z.re = r ∧ 0 < meromorphicOrderAt f z}

/-- Vertical translation in the ideal-value norm-twist convention. -/
def verticalShift (f : ℂ → ℂ) (t : ℝ) : ℂ → ℂ :=
  fun s => f (s - (t : ℂ) * Complex.I)

theorem zeroRealParts_verticalShift (f : ℂ → ℂ) (t : ℝ) :
    zeroRealParts (verticalShift f t) = zeroRealParts f := by
  ext r
  constructor
  · rintro ⟨z, hz, ho⟩
    refine ⟨z - (t : ℂ) * Complex.I, ?_, ?_⟩
    · simpa using hz
    · change 0 < meromorphicOrderAt (fun s => f (s - (t : ℂ) * Complex.I)) z at ho
      rwa [meromorphicOrderAt_fun_comp_sub_const_eq_meromorphicOrderAt] at ho
  · rintro ⟨z, hz, ho⟩
    refine ⟨z + (t : ℂ) * Complex.I, ?_, ?_⟩
    · simpa using hz
    · change 0 < meromorphicOrderAt (fun s => f (s - (t : ℂ) * Complex.I))
        (z + (t : ℂ) * Complex.I)
      rw [meromorphicOrderAt_fun_comp_sub_const_eq_meromorphicOrderAt, add_sub_cancel_right]
      exact ho

/-- Uniform family closure, stated for actual meromorphic functions. This
is conditional on the two remaining analytic inputs; it is not a theorem
that supplies those inputs for general Hecke characters. -/
theorem meromorphic_family_sevenEighths_of_seed_improvement {ι : Type*}
    (f : ι → ℂ → ℂ)
    (hmero : ∀ i, MeromorphicOn (f i) {s : ℂ | 7 / 8 < s.re})
    (hseed : SeedBound (fun i => zeroRealParts (f i)))
    (himprove : SupremumStrictImprovement (fun i => zeroRealParts (f i)))
    (i : ι) : MeromorphicZeroFreeOn (f i) {s : ℂ | 7 / 8 < s.re} := by
  refine ⟨hmero i, ?_⟩
  intro z hz
  apply le_of_not_gt
  intro hzero
  exact family_zeroFree_sevenEighths (fun i => zeroRealParts (f i))
    hseed himprove i hz ⟨z, rfl, hzero⟩

end

end HeckeGeneral.Analysis
