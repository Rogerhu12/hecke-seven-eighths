import HeckeSkeleton.ExpansionModels.SourceData

/-!
# One external threshold and the full original sector sum

The original recipe has shell at least 1/16. Thus a single threshold
for its internal base becomes a single threshold for the external scale,
before any source index or height parameter is selected. The actual
finite sector cardinal is the only cost of restoring the full marked
model energy. This is a quantifier transport lemma; its pointwise premise
is discharged by the original marked-source proof in the final closure.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedUniform

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)
variable (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
  c.geometry (expansionShellAllowance K c))

local notation "Sector" => SixthUnitClasses K (places K c)
local notation "E" => recipeMomentSourceData K c R
local notation "M" => recipeMomentModels K c R

local instance sectorFintype : Fintype Sector := Fintype.ofFinite _

/-- The internal base threshold is reached uniformly for the actual
recipe indices, using their original lower shell and no rowwise choice. -/
theorem base_threshold (U₀ Z T : ℝ) (hU₀ : 1 ≤ U₀)
    (hZ : max 1 (U₀ ^ (16 : ℝ)) ≤ Z)
    (i : SourceMomentIndexFor K c E Z T) : U₀ ≤ momentBaseFor i := by
  have hZ1 : 1 ≤ Z := (le_max_left _ _).trans hZ
  have hU : U₀ ^ (16 : ℝ) ≤ Z := (le_max_right _ _).trans hZ
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg (zero_le_one.trans hU₀) _) hU
    (by norm_num : (0 : ℝ) ≤ 1 / 16)
  have he : (U₀ ^ (16 : ℝ)) ^ (1 / 16 : ℝ) = U₀ := by
    rw [← Real.rpow_mul (zero_le_one.trans hU₀)]
    norm_num
  rw [he] at hp
  exact hp.trans (Real.rpow_le_rpow_of_exponent_le hZ1 (recipeMoment_shell_lower i))

/-- The whole marked model inherits one uniform bound from its
literal sector energies. Height order and ceiling precede tau, and the
threshold precedes every original source index and every sector. -/
theorem of_sector_bound (A C U₀ loss : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hU₀ : 2 ≤ U₀) (hloss : loss ≤ c.family.lamA)
    (hbound : ∀ Z T : ℝ, ∀ i : SourceMomentIndexFor K c E Z T, ∀ s : Sector,
      1 ≤ Z → 1 ≤ T → U₀ ≤ momentBaseFor i →
      51 / 100 < (momentBlockFor i).bin → inverseCapacityFor i →
      inverseEnergy (inverseModelFor M i s) (inverseParametersFor i) (momentBaseFor i) 0 ≤
        C * (momentBaseFor i) ^ (rowWidthFor i + loss) * (1 + T) ^ A) :
    UniformMomentBoundFor
      (fun _ _ i => markedModelEnergyFor M i)
      (fun _ _ i => rowWidthFor i)
      (fun _ _ i => inverseCapacityFor i) := by
  let k := (Fintype.card Sector : ℝ) * C
  have hk : 0 ≤ k := mul_nonneg (Nat.cast_nonneg _) hC
  refine ⟨A, 1, hA, zero_lt_one, ?_⟩
  intro tau htau htauCeiling
  refine ⟨max 1 (U₀ ^ (16 : ℝ)), k, le_max_left _ _, hk, ?_⟩
  intro Z hZ i hbin hcap
  have hZ1 : 1 ≤ Z := (le_max_left _ _).trans hZ
  have hT : 1 ≤ Z ^ tau := Real.one_le_rpow hZ1 htau.le
  have hbase := base_threshold K c R U₀ Z (Z ^ tau) (by linarith) hZ i
  have hbase1 : 1 ≤ momentBaseFor i := by linarith
  have hh : 0 ≤ (1 + Z ^ tau) ^ A := Real.rpow_nonneg (by positivity) _
  have hsector (s : Sector) :
      inverseEnergy (inverseModelFor M i s) (inverseParametersFor i) (momentBaseFor i) 0 ≤
        C * (momentBaseFor i) ^ (rowWidthFor i + c.family.lamA) * (1 + Z ^ tau) ^ A := by
    apply (hbound Z (Z ^ tau) i s hZ1 hT hbase hbin hcap).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hbase1 (add_le_add_left hloss _)) hC) hh
  unfold markedModelEnergyFor
  calc
    _ ≤ ∑ _s : Sector, C * (momentBaseFor i) ^ (rowWidthFor i + c.family.lamA) *
        (1 + Z ^ tau) ^ A := Finset.sum_le_sum (fun s _ => hsector s)
    _ = k * (momentBaseFor i) ^ (rowWidthFor i + c.family.lamA) * (1 + Z ^ tau) ^ A := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, k]
      ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedUniform

end
