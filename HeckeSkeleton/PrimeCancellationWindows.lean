import HeckeGeneral.Analysis.MomentPrimeWindows
import PrimeCancellationUniformProfiles

/-!
# Schwartz control for the existing pretarget prime windows

These are the literal windows in `analyticMomentPrimeWindow`. Their fixed
finite family supplies the new profile contract with height exponent zero.
Constructing and calibrating the full source moment models remains separate.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.PrimeCancellationWindows

open NumberField HeckeGeneral.ThetaSkeleton.Physical
open PrimeCancellation.UniformProfiles
open scoped Classical BigOperators

def actualPrimeWindowSchwartz (g : PrimeWindowGeometry) (j : Fin g.slots) :
    SchwartzMap ℝ ℂ :=
  (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (g.weight j).support).toSchwartzMap
    (g.weight j).smooth

theorem actualPrimeWindowSchwartz_profile
    (K : Type) [Field K] [NumberField K] (g : PrimeWindowGeometry) (j : Fin g.slots) :
    (actualPrimeWindowSchwartz g j : ℝ → ℂ) =
      (analyticMomentPrimeWindow K g j).profile 0 := rfl

theorem actualPrimeWindowSchwartz_support (g : PrimeWindowGeometry) (j : Fin g.slots) :
    Function.support (actualPrimeWindowSchwartz g j : ℝ → ℂ) ⊆ Set.Icc (1 : ℝ) 2 :=
  (g.support_annular j).trans Set.Ioo_subset_Icc_self

/-- The constant is chosen before every slot and height, for each requested
finite family of Schwartz seminorms. -/
theorem actualPrimeWindowSchwartz_uniform_seminorm (g : PrimeWindowGeometry)
    (seminorms : Finset (ℕ × ℕ)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (T : ℝ) (j : Fin g.slots),
      sourceSeminorm seminorms (actualPrimeWindowSchwartz g j) ≤ C * (1 + T) ^ (0 : ℝ) := by
  let B : ℝ := ∑ j : Fin g.slots, sourceSeminorm seminorms (actualPrimeWindowSchwartz g j)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => sourceSeminorm_nonneg seminorms _)
  refine ⟨1 + B, by linarith, ?_⟩
  intro T j
  rw [Real.rpow_zero, mul_one]
  have hj : sourceSeminorm seminorms (actualPrimeWindowSchwartz g j) ≤ B :=
    Finset.single_le_sum (fun k _ => sourceSeminorm_nonneg seminorms _)
      (Finset.mem_univ j)
  linarith

#print axioms actualPrimeWindowSchwartz_uniform_seminorm

end HeckeSkeleton.PrimeCancellationWindows
