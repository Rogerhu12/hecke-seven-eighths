module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsOriginalBounds

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# A polynomial bound for the actual first tail mass

The common-label identity counts each original pair once. Zero
coefficients contribute zero seminorm, so only the proved active
original carrier is counted. Every remaining mask and modulus is
bounded by divisibility in its actual original ideal pair.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentCounting HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

def originalKernelSeminorm (c : TargetContext K) (orders : Finset (ℕ × ℕ)) : ℝ :=
  orders.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (CanonicalRowBall.archTest K (Arithmetic.data c).Sf 1)

theorem originalKernelSeminorm_nonneg (c : TargetContext K) (orders : Finset (ℕ × ℕ)) :
    0 ≤ originalKernelSeminorm c orders := apply_nonneg _ _

def firstMassDegree (c : TargetContext K) : ℝ :=
  ((2 * (c.geometry.slots + 2) : ℕ) : ℝ) * originalColumnExponent c +
    3 * originalColumnExponent c

def firstMassCoefficient (c : TargetContext K) (orders : Finset (ℕ × ℕ)) : ℝ :=
  8 * firstTailFieldConstant K * idealCountConstant K ^ (2 * (c.geometry.slots + 2)) *
    originalKernelSeminorm c orders

theorem firstMassCoefficient_nonneg (c : TargetContext K) (orders : Finset (ℕ × ℕ)) :
    0 ≤ firstMassCoefficient c orders := by
  have hf := firstTailFieldConstant_nonneg (K := K)
  have hc := zero_le_one.trans (one_le_idealCountConstant K)
  have hs := originalKernelSeminorm_nonneg c orders
  dsimp [firstMassCoefficient]
  positivity

theorem firstMassDegree_nonneg (c : TargetContext K) : 0 ≤ firstMassDegree c := by
  exact add_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (originalColumnExponent_nonneg c))
    (mul_nonneg (by norm_num) (originalColumnExponent_nonneg c))

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable (F : FirstPresentation call p) (hF : F.Realizes)

def firstActiveColumns : Finset F.source.Column :=
  F.source.columns.filter (fun i => F.coefficient i ≠ 0)

def firstActivePairs :
    Finset (F.source.CommonLabel × (F.source.Column × F.source.Column)) :=
  (firstZeroPairs F.source.columns F.source.columns F.source.ideal F.source.ideal).filter
    (fun v => F.coefficient v.2.1 ≠ 0 ∧ F.coefficient v.2.2 ≠ 0)

include hF in
theorem firstActiveColumns_card (input : ProfileInput call)
    (hlarge : originalThreshold c call.frame ≤ call.base) :
    ((firstActiveColumns F).card : ℝ) ≤
      (idealCountConstant K * call.base ^ originalColumnExponent c) ^
        (c.geometry.slots + 2) := by
  have hsub : (firstActiveColumns F).map F.index.toEmbedding ⊆ activeOriginalColumns call := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    have hjm := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨first_index_mem F hF j hjm.1, hjm.2⟩
  have hn : (firstActiveColumns F).card ≤ (activeOriginalColumns call).card := by
    simpa only [Finset.card_map] using Finset.card_le_card hsub
  exact (Nat.cast_le.mpr hn).trans (activeOriginalColumns_card call input hlarge)

theorem firstActivePairs_card :
    ((firstActivePairs F).card : ℝ) ≤ ((firstActiveColumns F).card : ℝ) ^ 2 := by
  have hsub : (firstActivePairs F).image Prod.snd ⊆
      firstActiveColumns F ×ˢ firstActiveColumns F := by
    intro ij hij
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hij
    have hvm := Finset.mem_filter.mp hv
    have hm := (mem_firstZeroPairs F.source.columns F.source.columns
      F.source.ideal F.source.ideal v).mp hvm.1
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨hm.1, hvm.2.1⟩,
        Finset.mem_filter.mpr ⟨hm.2.1, hvm.2.2⟩⟩
  have hinj : Set.InjOn Prod.snd (firstActivePairs F : Set
      (F.source.CommonLabel × (F.source.Column × F.source.Column))) := by
    intro v hv w hw h
    exact firstZeroPairs_projection_injective F.source.columns F.source.columns
      F.source.ideal F.source.ideal (Finset.mem_filter.mp hv).1
      (Finset.mem_filter.mp hw).1 h
  have hn := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_product] at hn
  simpa only [pow_two, Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr hn

include hF in
theorem first_gram_seminorm_le (input : ProfileInput call)
    (horders : originalOrders ⊆ input.orders) (orders : Finset (ℕ × ℕ))
    (i : F.source.Column) (hi : i ∈ F.source.columns)
    (j : F.source.Column) (hj : j ∈ F.source.columns) :
    orders.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
        (F.source.profiles i j) ≤
      (2 * input.amplitude ^ (c.geometry.slots + 2)) ^ 2 *
        originalKernelSeminorm c orders := by
  rw [hF.profile, FirstPresentation.originalProfile, map_smul_eq_mul, norm_mul, norm_star]
  apply mul_le_mul_of_nonneg_right _ (originalKernelSeminorm_nonneg c orders)
  simpa only [pow_two] using
    mul_le_mul (first_coefficient_norm_le F hF input horders i hi)
      (first_coefficient_norm_le F hF input horders j hj) (norm_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (pow_nonneg (zero_le_one.trans input.amplitude_one_le) _))

include hF in
theorem first_pair_truncationMass_le (input : ProfileInput call)
    (hlarge : originalThreshold c call.frame ≤ call.base)
    (v : F.source.CommonLabel) (i : F.source.Column)
    (hi : i ∈ (F.source.source v).leftColumns) (j : F.source.Column)
    (hj : j ∈ (F.source.source v).rightColumns)
    (hci : F.coefficient i ≠ 0) (hcj : F.coefficient j ≠ 0) :
    ((F.source.source v).pairs i j).truncationMass
        (F.source.source v).mask F.source.radius ≤
      (2 * firstTailFieldConstant K) * call.base ^ (3 * originalColumnExponent c) := by
  have hmask := first_mask_norm_le F hF input hlarge v i hi hci
  have hmod := first_modulus_norm_le F hF input hlarge v i hi j hj hci hcj
  have hexp : (2 : ℝ) ≤ 2 * originalColumnExponent c := by
    have hs := (recipeInduction_budget (c := c)).1
    dsimp [originalColumnExponent]
    linarith
  have hinv := (first_inverse_radius_le F hF).trans
    (Real.rpow_le_rpow_of_exponent_le call.domain.scale.le hexp)
  have hadd : F.source.radius.val⁻¹ +
      (sIntegerElementNorm K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
        ⟨((F.source.source v).pairs i j).modulus,
          ((F.source.source v).pairs i j).modulus_ne_zero⟩).val ≤
      2 * call.base ^ (2 * originalColumnExponent c) := by linarith
  have hm := ((F.source.source v).pairs i j).truncationMass_le_mask_norm
    ((F.source.block v).residue_norm_le_one (Arithmetic.units_are_sixth c)
      (Arithmetic.context c) F.source.profiles i j)
    (F.source.source v).mask F.source.radius
  calc
    _ ≤ firstTailFieldConstant K *
        (sIntegerElementNorm K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
          (sIntegerMaskGenerator K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
            (F.source.source v).mask)).val *
        (F.source.radius.val⁻¹ +
          (sIntegerElementNorm K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
            ⟨((F.source.source v).pairs i j).modulus,
              ((F.source.source v).pairs i j).modulus_ne_zero⟩).val) := hm
    _ ≤ firstTailFieldConstant K * call.base ^ originalColumnExponent c *
        (2 * call.base ^ (2 * originalColumnExponent c)) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left hmask firstTailFieldConstant_nonneg) hadd
        (add_nonneg (inv_nonneg.mpr F.source.radius.property.le)
          (sIntegerElementNorm K _
            ⟨((F.source.source v).pairs i j).modulus,
              ((F.source.source v).pairs i j).modulus_ne_zero⟩).property.le)
        (mul_nonneg firstTailFieldConstant_nonneg (Real.rpow_nonneg call.base_pos.le _))
    _ = _ := by
      rw [show (3 : ℝ) * originalColumnExponent c =
        originalColumnExponent c + 2 * originalColumnExponent c by ring,
        Real.rpow_add call.base_pos]
      ring

include hF in
/-- The exact finite first tail mass has a fixed polynomial degree.
The estimate uses no cardinality assumption on its public carrier. -/
theorem first_tailCost_bound (input : ProfileInput call)
    (horders : originalOrders ⊆ input.orders)
    (hlarge : originalThreshold c call.frame ≤ call.base)
    (orders : Finset (ℕ × ℕ)) :
    F.source.tailCost orders ≤
      firstMassCoefficient c orders * input.amplitude ^ (2 * (c.geometry.slots + 2)) *
        call.base ^ firstMassDegree c := by
  let P := firstZeroPairs F.source.columns F.source.columns F.source.ideal F.source.ideal
  let term := fun v : F.source.CommonLabel × (F.source.Column × F.source.Column) =>
    orders.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
        (F.source.profiles v.2.1 v.2.2) *
      ((F.source.block v.1).pair (Arithmetic.units_are_sixth c) (Arithmetic.context c)
        F.source.profiles v.2.1 v.2.2).truncationMass
        ((F.source.block v.1).mask F.source.mask) F.source.radius
  have hsum : (∑ v ∈ P, term v) = ∑ v ∈ firstActivePairs F, term v := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro v hv hvnot
    have hz : F.coefficient v.2.1 = 0 ∨ F.coefficient v.2.2 = 0 := by
      by_cases hi : F.coefficient v.2.1 = 0
      · exact Or.inl hi
      · right
        by_contra hj
        exact hvnot (Finset.mem_filter.mpr ⟨hv, hi, hj⟩)
    have hprofile : F.source.profiles v.2.1 v.2.2 = 0 := by
      rw [hF.profile]
      rcases hz with hi | hj
      · simp only [FirstPresentation.originalProfile, hi, zero_mul, zero_smul]
      · simp only [FirstPresentation.originalProfile, hj, star_zero, mul_zero, zero_smul]
    dsimp only [term]
    rw [hprofile, map_zero, zero_mul]
  let Amp := (2 * input.amplitude ^ (c.geometry.slots + 2)) ^ 2 *
    originalKernelSeminorm c orders
  let Mass := (2 * firstTailFieldConstant K) *
    call.base ^ (3 * originalColumnExponent c)
  have hAmp : 0 ≤ Amp := mul_nonneg (sq_nonneg _) (originalKernelSeminorm_nonneg c orders)
  have hMass : 0 ≤ Mass := mul_nonneg
    (mul_nonneg (by norm_num) firstTailFieldConstant_nonneg)
    (Real.rpow_nonneg call.base_pos.le _)
  have hpoint (v) (hv : v ∈ firstActivePairs F) : term v ≤ Amp * Mass := by
    have hvm := Finset.mem_filter.mp hv
    have hm := (mem_firstZeroPairs F.source.columns F.source.columns
      F.source.ideal F.source.ideal v).mp hvm.1
    have hb := ((F.source.block v.1).mem_iff_label F.source.columns F.source.columns
      (commonSupportPool_support_eq F.source.columns F.source.columns
        (fun i => (F.source.ideal i).val) (fun j => (F.source.ideal j).val)
        v.1.val v.1.property) _ _).mpr hm
    have hmass := first_pair_truncationMass_le F hF input hlarge v.1
      v.2.1 hb.1 v.2.2 hb.2.1 hvm.2.1 hvm.2.2
    have hprofile := first_gram_seminorm_le F hF input horders orders v.2.1 hm.1 v.2.2 hm.2.1
    exact (mul_le_mul_of_nonneg_left hmass (apply_nonneg _ _)).trans
      (mul_le_mul_of_nonneg_right hprofile hMass)
  have hcount : ((firstActivePairs F).card : ℝ) ≤
      ((idealCountConstant K * call.base ^ originalColumnExponent c) ^
        (c.geometry.slots + 2)) ^ 2 :=
    (firstActivePairs_card F).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (firstActiveColumns_card F hF input hlarge) 2)
  have hscale : (call.base ^ originalColumnExponent c) ^ (2 * (c.geometry.slots + 2)) =
      call.base ^ (((2 * (c.geometry.slots + 2) : ℕ) : ℝ) * originalColumnExponent c) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul call.base_pos.le]
    congr 1
    ring
  have hcountpow :
      ((idealCountConstant K * call.base ^ originalColumnExponent c) ^
        (c.geometry.slots + 2)) ^ 2 =
      idealCountConstant K ^ (2 * (c.geometry.slots + 2)) *
        call.base ^ (((2 * (c.geometry.slots + 2) : ℕ) : ℝ) * originalColumnExponent c) := by
    rw [← pow_mul, Nat.mul_comm (c.geometry.slots + 2) 2, mul_pow, hscale]
  have hprofilepow : Amp =
      4 * originalKernelSeminorm c orders *
        input.amplitude ^ (2 * (c.geometry.slots + 2)) := by
    dsimp only [Amp]
    rw [mul_pow, ← pow_mul, Nat.mul_comm (c.geometry.slots + 2) 2]
    ring
  change firstBlockTailMass (Arithmetic.units_are_sixth c) (Arithmetic.context c)
    F.source.columns F.source.columns F.source.ideal F.source.ideal F.source.block
    orders F.source.profiles F.source.radius F.source.mask ≤ _
  rw [firstBlockTailMass_eq_original_pairs]
  change (∑ v ∈ P, term v) ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ _v ∈ firstActivePairs F, Amp * Mass := Finset.sum_le_sum hpoint
    _ = ((firstActivePairs F).card : ℝ) * (Amp * Mass) := by simp
    _ ≤ ((idealCountConstant K * call.base ^ originalColumnExponent c) ^
        (c.geometry.slots + 2)) ^ 2 * (Amp * Mass) :=
      mul_le_mul_of_nonneg_right hcount (mul_nonneg hAmp hMass)
    _ = _ := by
      rw [hcountpow, hprofilepow]
      dsimp only [Mass, firstMassCoefficient, firstMassDegree]
      rw [Real.rpow_add call.base_pos]
      ring

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.first_tailCost_bound

