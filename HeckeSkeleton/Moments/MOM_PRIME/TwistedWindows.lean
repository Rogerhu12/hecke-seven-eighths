import HeckeGeneral.Analysis.TInputSeparatedProfiles
import HeckeGeneral.Analysis.ActualPrimeGeometryAbsoluteBound
import HeckeGeneral.Analysis.MomentSlotScaleChange

/-!
# Uniform bounds for the actual frozen prime windows

`PrimeWindow.freezeTwist` changes a profile, even though it preserves its
length and support.  On the original annulus `1 < y < 2`, a common upper
bound on the real part of the complex exponent controls the new sup norm.
The imaginary part, the frozen time and the later interface time are
unrestricted.  These are absolute profile bounds and require no zero-free
region or derivative estimate.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField Set HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

/-- On positive arguments the norm of the actual total profile power
depends only on the real part of its exponent. -/
theorem norm_profilePower_eq_rpow (power : ℂ) (y : ℝ) (hy : 0 < y) :
    ‖profilePower power y‖ = y ^ power.re := by
  rw [profilePower_eq_cpow power hy, Complex.norm_cpow_eq_rpow_re_of_pos hy]

/-- A one-sided real-part bound suffices on the closed positive annulus.
No lower bound on the real part or bound on the imaginary part is needed. -/
theorem norm_profilePower_le_annular (power : ℂ) (L y : ℝ)
    (hpower : power.re ≤ L) (hy₁ : 1 ≤ y) (hy₂ : y ≤ 2) :
    ‖profilePower power y‖ ≤ (2 : ℝ) ^ (max L 0) := by
  rw [norm_profilePower_eq_rpow power y (zero_lt_one.trans_le hy₁)]
  exact (Real.rpow_le_rpow_of_exponent_le hy₁
    (hpower.trans (le_max_left L 0))).trans
      (Real.rpow_le_rpow (zero_le_one.trans hy₁) hy₂ (le_max_right L 0))

variable {K : Type} [Field K] [NumberField K]

/-- The total power is everywhere nonzero, so support is preserved exactly,
including at nonpositive arguments. -/
theorem primeWindow_freezeTwist_support (W : PrimeWindow K)
    (time : ℝ) (power : ℂ) (τ : ℝ) :
    Function.support ((W.freezeTwist time power).profile τ) =
      Function.support (W.profile time) := by
  ext y
  change W.profile time y * profilePower power y ≠ 0 ↔ W.profile time y ≠ 0
  exact ⟨left_ne_zero_of_mul, fun h => mul_ne_zero h (profilePower_ne_zero power y)⟩

theorem primeWindow_freezeTwist_annular (W : PrimeWindow K)
    (time : ℝ) (power : ℂ)
    (hs : Function.support (W.profile time) ⊆ Ioo (1 : ℝ) 2) (τ : ℝ) :
    Function.support ((W.freezeTwist time power).profile τ) ⊆ Ioo (1 : ℝ) 2 := by
  rw [primeWindow_freezeTwist_support]
  exact hs

/-- The actual frozen profile has a uniform sup bound. Outside the annulus
the original profile vanishes, so the extension of `profilePower` there
does not introduce any extra hypothesis. -/
theorem primeWindow_freezeTwist_norm_le (W : PrimeWindow K)
    (time : ℝ) (power : ℂ) (B L : ℝ) (hB : 0 ≤ B)
    (hs : Function.support (W.profile time) ⊆ Ioo (1 : ℝ) 2)
    (hbound : ∀ y, ‖W.profile time y‖ ≤ B) (hpower : power.re ≤ L)
    (τ y : ℝ) :
    ‖(W.freezeTwist time power).profile τ y‖ ≤ B * (2 : ℝ) ^ (max L 0) := by
  change ‖W.profile time y * profilePower power y‖ ≤ _
  by_cases hw : W.profile time y = 0
  · rw [hw, zero_mul, norm_zero]
    exact mul_nonneg hB (Real.rpow_nonneg (by norm_num) _)
  · have hy := hs hw
    rw [norm_mul]
    exact mul_le_mul (hbound y)
      (norm_profilePower_le_annular power L y hpower hy.1.le hy.2.le)
      (norm_nonneg _) hB

/-- Pointwise transfer of annular support to every slot of the actual
`freezeTwists` operation. -/
theorem freezeTwists_annular (g : SlotGeometry K)
    (time : Fin g.slotCount → ℝ) (power : Fin g.slotCount → ℂ)
    (hs : ∀ i, Function.support ((g.slots i).profile (time i)) ⊆ Ioo (1 : ℝ) 2)
    (i : Fin g.slotCount) (τ : ℝ) :
    Function.support (((g.freezeTwists time power).slots i).profile τ) ⊆
      Ioo (1 : ℝ) 2 :=
  primeWindow_freezeTwist_annular (g.slots i) (time i) (power i) (hs i) τ

/-- A single bound controls every slot, with independent frozen times and
independent complex powers whose real parts have a common upper bound. -/
theorem freezeTwists_norm_le (g : SlotGeometry K)
    (time : Fin g.slotCount → ℝ) (power : Fin g.slotCount → ℂ)
    (B L : ℝ) (hB : 0 ≤ B)
    (hs : ∀ i, Function.support ((g.slots i).profile (time i)) ⊆ Ioo (1 : ℝ) 2)
    (hbound : ∀ i y, ‖(g.slots i).profile (time i) y‖ ≤ B)
    (hpower : ∀ i, (power i).re ≤ L) (i : Fin g.slotCount) (τ y : ℝ) :
    ‖((g.freezeTwists time power).slots i).profile τ y‖ ≤
      B * (2 : ℝ) ^ (max L 0) :=
  primeWindow_freezeTwist_norm_le (g.slots i) (time i) (power i) B L hB
    (hs i) (hbound i) (hpower i) τ y

variable (K)

/-- The fixed physical windows supply a positive constant before all
frozen times, complex powers, later heights and profile arguments. -/
theorem exists_actualFrozenPrimeGeometry_profile_bound (g : PrimeWindowGeometry) (L : ℝ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (time : Fin g.slots → ℝ) (power : Fin g.slots → ℂ),
        (∀ i, (power i).re ≤ L) → ∀ (i : Fin g.slots) (τ y : ℝ),
          ‖(((momentPrimeGeometry K g).freezeTwists time power).slots i).profile τ y‖ ≤ B := by
  obtain ⟨B, hB, hprofile⟩ := exists_actualMomentPrimeGeometry_profile_bound K g
  refine ⟨B * (2 : ℝ) ^ (max L 0),
    mul_pos hB (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro time power hpower i τ y
  exact freezeTwists_norm_le (momentPrimeGeometry K g) time power B L hB.le
    (fun j => g.support_annular j) (fun j => hprofile j (time j)) hpower i τ y

/-- The same pretarget constant works after any positive base change and
any subset of slots. This covers the actual geometry used by separated
profiles without requiring equality with the untwisted windows. -/
theorem exists_actualSelectedFrozenPrimeGeometry_profile_bounds
    (g : PrimeWindowGeometry) (L : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (shell : ℝ) (hshell : 0 < shell) (I : Finset (Fin g.slots)),
      let G := ((momentPrimeGeometry K g).changeBase shell hshell).restrictSlots I
      ∀ (time : Fin G.slotCount → ℝ) (power : Fin G.slotCount → ℂ),
        (∀ i, (power i).re ≤ L) →
        (∀ (i : Fin G.slotCount) (τ : ℝ),
          Function.support (((G.freezeTwists time power).slots i).profile τ) ⊆
            Ioo (1 : ℝ) 2) ∧
        (∀ (i : Fin G.slotCount) (τ y : ℝ),
          ‖((G.freezeTwists time power).slots i).profile τ y‖ ≤ B) := by
  obtain ⟨B, hB, hprofile⟩ := exists_actualMomentPrimeGeometry_profile_bound K g
  refine ⟨B * (2 : ℝ) ^ (max L 0),
    mul_pos hB (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro shell hshell I G time power hpower
  have hann (i : Fin G.slotCount) :
      Function.support ((G.slots i).profile (time i)) ⊆ Ioo (1 : ℝ) 2 :=
    g.support_annular (selectedSlotIndex I i)
  have hbound (i : Fin G.slotCount) (y : ℝ) :
      ‖(G.slots i).profile (time i) y‖ ≤ B :=
    hprofile (selectedSlotIndex I i) (time i) y
  exact ⟨fun i τ => freezeTwists_annular G time power hann i τ,
    fun i τ y => freezeTwists_norm_le G time power B L hB.le hann hbound hpower i τ y⟩

end HeckeSkeleton.Moments.MOM_PRIME
