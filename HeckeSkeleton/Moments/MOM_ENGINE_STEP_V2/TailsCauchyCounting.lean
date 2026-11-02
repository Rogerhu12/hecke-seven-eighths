import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsCauchyGeometry

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Counting every literal first Cauchy label

The common-pair pool is an image of the original Cartesian square.
A mask has at most its norm many Boolean divisors, and the residual
divisor is one actual nonzero ideal of bounded norm. The finite phase
group is trivial and the side contributes exactly two labels.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckePort.CenteredMomentCounting
open HeckePort.Moments HeckePort.Moments.MobiusRegroup
open DedekindZetaZeroFree.LargeSieve

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

local instance firstCauchyCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

theorem firstCauchyCharacter_card :
    Fintype.card ((PUnit.{1} × PUnit.{1}) →* Circle) = 1 := by
  letI : Unique ((PUnit.{1} × PUnit.{1}) →* Circle) where
    default := 1
    uniq f := by
      ext x
      rw [Subsingleton.elim x 1]
      simp
  exact Fintype.card_unique

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem first_common_card (F : FirstPresentation call p) :
    (Fintype.card F.source.CommonLabel : ℝ) ≤ (F.source.columns.card : ℝ) ^ 2 := by
  change (Fintype.card ↥(commonSupportPool F.source.columns F.source.columns
    (fun i => (F.source.ideal i).val) (fun j => (F.source.ideal j).val)) : ℝ) ≤ _
  rw [Fintype.card_coe]
  have hn := Finset.card_image_le (s := F.source.columns ×ˢ F.source.columns)
    (f := fun ij => commonSupportLabel (F.source.ideal ij.1).val (F.source.ideal ij.2).val)
  rw [Finset.card_product] at hn
  simpa only [commonSupportPool, pow_two, Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr hn

theorem first_full_mask_powerset_card
    (F : FirstPresentation call p) (hF : F.Realizes)
    (input : ProfileInput call) (hlarge : originalThreshold c call.frame ≤ call.base)
    (v : F.source.CommonLabel) :
    (((F.source.block v).mask F.source.mask).powerset.card : ℝ) ≤
      call.base ^ carrierColumnExponent c := by
  have hnorm :
      (sIntegerElementNorm K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
          ((F.source.block v).mask F.source.mask))).val ≤
        call.base ^ carrierColumnExponent c := by
    rw [hF.mask]
    exact (PhysicalBlock.tailsV2_principal_mask_norm_le_common
      (F.source.block v) (Arithmetic.context c)).trans
        (first_common_norms_le F hF input hlarge v).1
  exact (mask_powerset_card_le_generator_norm (K := K) (S := (Arithmetic.data c).Sf)
    ((F.source.block v).mask F.source.mask)).trans hnorm

theorem first_residualPool_card
    (F : FirstPresentation call p) (hF : F.Realizes)
    (input : ProfileInput call) (hlarge : originalThreshold c call.frame ≤ call.base)
    (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) :
    ((divisorPool (F.source.pieces v D).rightData.columns
      (fun j => ((F.source.pieces v D).rightData.ideal j).val)).card : ℝ) ≤
        idealCountConstant K * call.base ^ carrierColumnExponent c := by
  apply card_le_idealCountConstant K _ (call.base ^ carrierColumnExponent c)
    (Real.one_le_rpow call.domain.scale.le (carrierColumnExponent_nonneg c))
  intro I hI
  obtain ⟨j, hj, hdivisor⟩ := Finset.mem_biUnion.mp hI
  have hd := (mem_idealDivisors
    ((F.source.pieces v D).rightData.ideal j).property.1).mp hdivisor
  have hI0 : I ≠ 0 := by
    intro hz
    rw [hz, zero_dvd_iff] at hd
    exact ((F.source.pieces v D).rightData.ideal j).property.1 hd
  rw [(F.source.pieces v D).right_columns] at hj
  rw [(F.source.pieces v D).right_ideal] at hd
  have hfull : I ∣ (F.source.ideal j).val := by
    apply hd.trans
    rw [(F.source.block v).right_reconstruct F.source.columns j hj]
    exact dvd_mul_left _ _
  exact ⟨hI0,
    (tailsV2_physical_ideal_norm_le_of_dvd I (F.source.ideal j).val
      (F.source.ideal j).property.1 hfull).trans
        (first_ideal_norm_le_all F hF input hlarge j (Finset.mem_filter.mp hj).1)⟩

def firstFamilyCountConstant (c : TargetContext K) : ℝ :=
  2 * idealCountConstant K ^ (2 * (c.geometry.slots + 2) + 1)

def firstFamilyCountDegree (c : TargetContext K) : ℝ :=
  ((2 * (c.geometry.slots + 2) + 2 : ℕ) : ℝ) * carrierColumnExponent c

theorem firstFamilyCountConstant_nonneg (c : TargetContext K) :
    0 ≤ firstFamilyCountConstant c := by
  have hc := zero_le_one.trans (one_le_idealCountConstant K)
  dsimp [firstFamilyCountConstant]
  positivity

theorem firstFamilyCountDegree_nonneg (c : TargetContext K) :
    0 ≤ firstFamilyCountDegree c :=
  mul_nonneg (Nat.cast_nonneg _) (carrierColumnExponent_nonneg c)

theorem first_family_count_eq (F : FirstPresentation call p)
    (family : FirstCauchyFamily F) :
    (family.count : ℝ) =
      ∑ v : F.source.CommonLabel, ∑ D : ((F.source.block v).mask F.source.mask).powerset,
        ((divisorPool (F.source.pieces v D).rightData.columns
          (fun j => ((F.source.pieces v D).rightData.ideal j).val)).card : ℝ) * 2 := by
  have he : family.count = Fintype.card (FirstCauchyKey F) := by
    simpa only [Fintype.card_fin] using Fintype.card_congr family.index
  rw [he]
  simp only [FirstCauchyKey, Fintype.card_sigma, Fintype.card_prod,
    firstCauchyCharacter_card, Fintype.card_bool, Fintype.card_coe,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat, one_mul]

theorem first_family_count_le
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F)
    (input : ProfileInput call) (hlarge : originalThreshold c call.frame ≤ call.base) :
    (family.count : ℝ) ≤
      firstFamilyCountConstant c * call.base ^ firstFamilyCountDegree c := by
  let G := carrierColumnExponent c
  let H := idealCountConstant K * call.base ^ G
  have hH : 0 ≤ H := mul_nonneg
    (zero_le_one.trans (one_le_idealCountConstant K)) (Real.rpow_nonneg call.base_pos.le G)
  have hmask (v : F.source.CommonLabel) :
      (∑ D : ((F.source.block v).mask F.source.mask).powerset,
        ((divisorPool (F.source.pieces v D).rightData.columns
          (fun j => ((F.source.pieces v D).rightData.ideal j).val)).card : ℝ) * 2) ≤
        call.base ^ G * H * 2 := by
    calc
      _ ≤ ∑ _D : ((F.source.block v).mask F.source.mask).powerset, H * 2 :=
        Finset.sum_le_sum fun D _ => mul_le_mul_of_nonneg_right
          (first_residualPool_card F hF input hlarge v D) (by norm_num)
      _ = (((F.source.block v).mask F.source.mask).powerset.card : ℝ) * (H * 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      _ ≤ call.base ^ G * (H * 2) :=
        mul_le_mul_of_nonneg_right (first_full_mask_powerset_card F hF input hlarge v)
          (mul_nonneg hH (by norm_num))
      _ = _ := by ring
  have hcommon : (Fintype.card F.source.CommonLabel : ℝ) ≤
      (H ^ (c.geometry.slots + 2)) ^ 2 :=
    (first_common_card F).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (first_columns_card F hF input hlarge) 2)
  rw [first_family_count_eq]
  calc
    _ ≤ ∑ _v : F.source.CommonLabel, call.base ^ G * H * 2 :=
      Finset.sum_le_sum fun v _ => hmask v
    _ = (Fintype.card F.source.CommonLabel : ℝ) * (call.base ^ G * H * 2) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (H ^ (c.geometry.slots + 2)) ^ 2 * (call.base ^ G * H * 2) :=
      mul_le_mul_of_nonneg_right hcommon
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg call.base_pos.le G) hH) (by norm_num))
    _ = firstFamilyCountConstant c * call.base ^ firstFamilyCountDegree c := by
      have hpoly (x : ℝ) (k : ℕ) :
          ((idealCountConstant K * x) ^ k) ^ 2 * (x * (idealCountConstant K * x) * 2) =
            (2 * idealCountConstant K ^ (2 * k + 1)) * x ^ (2 * k + 2) := by
        rw [show 2 * k + 1 = k * 2 + 1 by omega,
          show 2 * k + 2 = k * 2 + 2 by omega,
          pow_add, pow_add, pow_one, pow_mul, pow_mul, mul_pow]
        ring
      dsimp only [H]
      rw [hpoly]
      have hp : (call.base ^ G) ^ (2 * (c.geometry.slots + 2) + 2) =
          call.base ^ (((2 * (c.geometry.slots + 2) + 2 : ℕ) : ℝ) * G) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul call.base_pos.le]
        congr 1
        ring
      rw [hp]
      rfl

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.first_family_count_le

