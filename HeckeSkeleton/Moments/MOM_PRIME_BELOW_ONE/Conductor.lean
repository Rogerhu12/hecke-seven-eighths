import HeckeSkeleton.ExpansionModels.ActualRowEligibility
import HeckeSkeleton.ExpansionModels.SmallRowNumerator
import HeckeSkeleton.HeckeConductorNorm
import HeckeSkeleton.PrimeCancellationPolynomials

/-!
# Conductor control on every actual paired row

The complete ideal indexing a paired row can contain a sixth-power factor.
Its character is the character of its sixth-power-free part. The arithmetic
conductor bound for that part is therefore bounded by the norm of the complete
ideal, uniformly over all selected slots and physical parameters.

This covers the full paired-row sum, including rows not represented by an
individual physical witness. The original complete-ideal mask is unchanged.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open scoped Classical

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

local notation "Source" => recipeMomentSourceData K c (expansionRecipeRaw K c)
local notation "Models" => recipeMomentModels K c (expansionRecipeRaw K c)

variable {Z T : ℝ}

/-- The actual selected slot coefficients are identically one. -/
theorem actual_prime_slotCoefficient_eq_one
    (i : SourceMomentIndexFor K c Source Z T)
    (s : SixthUnitClasses K (places K c))
    (j : Fin (pairedModelFor Models i s).geometry.slotCount) :
    (pairedModelFor Models i s).slotCoefficient j = 1 := rfl

/-- The inverse of each actual slot coefficient belongs to the existing
canonical exceptional family. -/
theorem actual_prime_slot_inverse_mem
    (i : SourceMomentIndexFor K c Source Z T)
    (s : SixthUnitClasses K (places K c))
    (j : Fin (pairedModelFor Models i s).geometry.slotCount) :
    ((pairedModelFor Models i s).slotCoefficient j)⁻¹ ∈
      (pairedModelFor Models i s).theta := by
  rw [actual_prime_slotCoefficient_eq_one, inv_one, actualRecipeMoment_theta]
  exact Expansion.Project.one_mem_canonicalDetectorTheta K (targetCharacter K c)

/-- Filtering paired rows preserves the original exterior-ideal condition. -/
theorem actual_paired_row_exterior
    (i : SourceMomentIndexFor K c Source Z T)
    (s : SixthUnitClasses K (places K c)) (u : NonzeroIdeal K)
    (hu : u ∈ pairedRows (pairedModelFor Models i s)
      (pairedParametersFor i) (momentBaseFor i)) :
    completeIdealIsExterior K (places K c) u := by
  exact (((pairedModelFor Models i s).rows_spec _ u).mp
    (PrimeCancellationMoment.mem_rows_of_mem_pairedRows _ _ _ u hu)).1

/-- Removing sixth powers can only decrease the norm of an integral ideal. -/
theorem sixthPowerFreePart_norm_le (u : NonzeroIdeal K) :
    idealNorm K (sixthPowerFreePart u) ≤ idealNorm K u := by
  have hd := map_dvd Ideal.absNorm (sixthPowerFreePart_dvd u)
  have hn := Nat.le_of_dvd (Ideal.absNorm_pos_of_nonZeroDivisors u) hd
  change ((sixthPowerFreePart u).val.absNorm : ℝ) ≤ (u.val.absNorm : ℝ)
  exact_mod_cast hn

/-- A fixed linear conductor constant works for every complete paired row.
It is chosen before scales, physical heights, sectors and selected slots. -/
theorem actual_prime_conductor_norm_bound :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧
      ∀ (Z T : ℝ) (i : SourceMomentIndexFor K c Source Z T)
        (s : SixthUnitClasses K (places K c)) (u : NonzeroIdeal K),
        u ∈ pairedRows (pairedModelFor Models i s)
          (pairedParametersFor i) (momentBaseFor i) →
        ∀ j, heckeConductorScale K
          ((pairedModelFor Models i s).rowCharacter u *
            (pairedModelFor Models i s).slotCoefficient j) ≤ C₀ * idealNorm K u := by
  obtain ⟨A, hA, hbound⟩ := Expansion.SmallRows.exists_row_conductorScale_bound
    K (places K c)
  refine ⟨max 1 A, le_max_left _ _, ?_⟩
  intro Z T i s u hu j
  have hext := actual_paired_row_exterior K c i s u hu
  let v : ExteriorIdeal K (places K c) := ⟨u, hext⟩
  rw [actual_prime_slotCoefficient_eq_one, mul_one]
  change heckeConductorScale K
    (completeIdealRowCharacter K (places K c) (probeData K c)
      (momentRowCharacters K c) s v.val) ≤ max 1 A * idealNorm K u
  rw [completeIdealRowCharacter_exterior]
  have h := hbound (probeData K c) (momentRowCharacters K c)
    (decomposedFrequencyRow K (places K c) v s)
  change heckeConductorScale K
    ((momentRowCharacters K c).character (decomposedFrequencyRow K (places K c) v s)) ≤
      A * idealNorm K (sixthPowerFreePart u) at h
  exact h.trans ((mul_le_mul_of_nonneg_left (sixthPowerFreePart_norm_le K u) hA.le).trans
    (mul_le_mul_of_nonneg_right (le_max_right 1 A) (idealNorm_pos K u).le))

end HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE
