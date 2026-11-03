import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Reindexing with retained zero coefficients

The paper's full index deliberately retains local zero coefficients.
Only the nonzero support must be injective.  This theorem restores all
zero terms after the arithmetic frequency correspondence is proved,
without silently requiring injectivity on the larger raw index.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalSupportReindex

open Function

variable {I J : Type*}

theorem hasSum_iff_of_supported_coordinates (f : I → ℂ) (g : J → ℂ) (ν : J → I)
    (hinj : Set.InjOn ν (support g))
    (hcover : ∀ i, f i ≠ 0 → ∃ j, g j ≠ 0 ∧ ν j = i)
    (hterm : ∀ j, g j ≠ 0 → f (ν j) = g j) (z : ℂ) :
    HasSum f z ↔ HasSum g z := by
  apply hasSum_iff_hasSum_of_ne_zero_bij (fun j : support g => ν j.val)
  · intro j k h
    exact Subtype.ext (hinj j.property k.property h)
  · intro i hi
    obtain ⟨j, hj, he⟩ := hcover i hi
    exact ⟨⟨j, hj⟩, he⟩
  · intro j
    exact hterm j.val j.property

theorem summable_iff_of_supported_coordinates (f : I → ℂ) (g : J → ℂ) (ν : J → I)
    (hinj : Set.InjOn ν (support g))
    (hcover : ∀ i, f i ≠ 0 → ∃ j, g j ≠ 0 ∧ ν j = i)
    (hterm : ∀ j, g j ≠ 0 → f (ν j) = g j) :
    Summable f ↔ Summable g :=
  exists_congr (hasSum_iff_of_supported_coordinates f g ν hinj hcover hterm)

/-- The hypotheses are the pointwise coefficient dictionary and the
arithmetic correspondence on its support, not an equality of sums. -/
theorem tsum_eq_of_supported_coordinates (f : I → ℂ) (g : J → ℂ) (ν : J → I)
    (hinj : Set.InjOn ν (support g))
    (hcover : ∀ i, f i ≠ 0 → ∃ j, g j ≠ 0 ∧ ν j = i)
    (hterm : ∀ j, g j ≠ 0 → f (ν j) = g j) :
    (∑' i, f i) = ∑' j, g j := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun j : support g => ν j.val)
  · intro j k h
    apply Subtype.ext
    exact hinj j.property k.property h
  · intro i hi
    obtain ⟨j, hj, he⟩ := hcover i hi
    exact ⟨⟨j, hj⟩, he⟩
  · intro j
    exact hterm j.val j.property

theorem tsum_norm_eq_of_supported_coordinates (f : I → ℂ) (g : J → ℂ) (ν : J → I)
    (hinj : Set.InjOn ν (support g))
    (hcover : ∀ i, f i ≠ 0 → ∃ j, g j ≠ 0 ∧ ν j = i)
    (hterm : ∀ j, g j ≠ 0 → f (ν j) = g j) :
    (∑' i, ‖f i‖) = ∑' j, ‖g j‖ := by
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun j : support (fun j => ‖g j‖) => ν j.val)
  · intro j k h
    apply Subtype.ext
    exact hinj (by simpa only [mem_support, norm_ne_zero_iff] using j.property)
      (by simpa only [mem_support, norm_ne_zero_iff] using k.property) h
  · intro i hi
    obtain ⟨j, hj, he⟩ := hcover i (by simpa only [mem_support, norm_ne_zero_iff] using hi)
    exact ⟨⟨j, by simpa only [mem_support, norm_ne_zero_iff] using hj⟩, he⟩
  · intro j
    rw [hterm j.val (by simpa only [mem_support, norm_ne_zero_iff] using j.property)]

end ThetaGlobal.GlobalSupportReindex

#print axioms ThetaGlobal.GlobalSupportReindex.tsum_eq_of_supported_coordinates
#print axioms ThetaGlobal.GlobalSupportReindex.tsum_norm_eq_of_supported_coordinates
#print axioms ThetaGlobal.GlobalSupportReindex.summable_iff_of_supported_coordinates
