import HeckeSkeleton.PrimeCancellationWindows
import HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE.MellinWindows
import HeckeSkeleton.ExpansionModels.SourceData
import Expansion.PhysicalRecipeSchedule

/-!
# Schwartz control of the original physical prime windows

The Mellin test used here has a fixed cutoff equal to one throughout the
prime annulus.  Multiplication by the original prime weight therefore
recovers the literal frozen profile, including its real power -33/50 and
its physical imaginary parameter.  Its finite Schwartz seminorms have a
polynomial height bound chosen before every source index and selected slot.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.PrimeCancellationWindows
open PrimeCancellation.UniformProfiles
open scoped Classical BigOperators ContDiff SchwartzMap ComplexConjugate

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

local notation "Source" => recipeMomentSourceData K c (expansionRecipeRaw K c)
local notation "Models" => recipeMomentModels K c (expansionRecipeRaw K c)

def actualPrimeWindow (Z T : ℝ) (i : SourceMomentIndexFor K c Source Z T)
    (s : SixthUnitClasses K (places K c))
    (j : Fin (pairedModelFor Models i s).geometry.slotCount) : SchwartzMap ℝ ℂ :=
  MellinWindow.frozen (actualPrimeWindowSchwartz c.geometry (selectedSlotIndex i.selected j))
    ((Models).heights Z T i 2)

theorem actualPrimeWindow_eq (Z T : ℝ) (i : SourceMomentIndexFor K c Source Z T)
    (s : SixthUnitClasses K (places K c))
    (j : Fin (pairedModelFor Models i s).geometry.slotCount) :
    (actualPrimeWindow K c Z T i s j : ℝ → ℂ) =
      ((pairedModelFor Models i s).geometry.slots j).profile 0 := by
  funext y
  rw [actualPrimeWindow, MellinWindow.frozen_apply _
    (c.geometry.support_annular (selectedSlotIndex i.selected j))]
  rfl

theorem actualPrimeWindow_support (Z T : ℝ) (i : SourceMomentIndexFor K c Source Z T)
    (s : SixthUnitClasses K (places K c))
    (j : Fin (pairedModelFor Models i s).geometry.slotCount) :
    Function.support (actualPrimeWindow K c Z T i s j : ℝ → ℂ) ⊆ Set.Icc (1 : ℝ) 2 :=
  MellinWindow.frozen_support _ (c.geometry.support_annular (selectedSlotIndex i.selected j)) _

theorem actualPrimeWindow_uniform_seminorm (seminorms : Finset (ℕ × ℕ)) :
    ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ Z T (i : SourceMomentIndexFor K c Source Z T) s j, 1 ≤ Z → 1 ≤ T →
        sourceSeminorm seminorms (actualPrimeWindow K c Z T i s j) ≤ C * (1 + T) ^ A := by
  obtain ⟨m, C, hC, hb⟩ := MellinWindow.frozen_uniform_seminorm_bound
    (actualPrimeWindowSchwartz c.geometry) seminorms
  refine ⟨C, m, hC, Nat.cast_nonneg _, ?_⟩
  intro Z T i s j _hZ _hT
  have hheight := ((recipeMomentModels_geometry K c (expansionRecipeRaw K c)
    (expansionRecipeRaw_geometry K c)).2 Z T i).1
  have ht : |(Models).heights Z T i 2| ≤ T := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm ((Models).heights Z T i) 2).trans hheight
  rw [Real.rpow_natCast]
  exact (hb _ _).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (add_le_add_left ht 1) m) (zero_le_one.trans hC))

end HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE

#print axioms HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE.actualPrimeWindow_uniform_seminorm
