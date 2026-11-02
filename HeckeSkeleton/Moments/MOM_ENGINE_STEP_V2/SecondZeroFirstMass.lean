import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstSourceCarrierBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstZeroMaskBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstPhysicalMaskBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondZeroNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstLogBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstTerminalIndexMass

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The first Cauchy weights of the second zero term

The Fourier measure is the original fixed logarithmic measure. The
chosen side allowance cancels its own Cauchy denominator, while both
allowance square roots and the actual active Gauss norm remain in the
common-support weight. The residual divisor is retained with its one
inverse norm. Constants are selected before the moving first source.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open HeckePort.IdealMobiusDivisorSum UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar

local instance firstMassCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

/-- This total mass depends only on the fixed source parameters. -/
def firstFourierMass (c : TargetContext K) (p : SourceParameters c) : ℝ :=
  (actualFourierMeasure (secondKernel c p)).real Set.univ

theorem firstFourierMass_nonneg : 0 ≤ firstFourierMass c p := measureReal_nonneg

private theorem chart_projections_of_heq (F : FirstPresentation call p)
    (v : F.source.CommonLabel) (D : ((F.source.block v).mask F.source.mask).powerset)
    {φ ψ : F.source.Column → F.source.Column →
      SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
    (e : φ = ψ)
    (x : FirstBlockProfileChart (E := ℝ) (Arithmetic.units_are_sixth c)
      (Arithmetic.localMeasures (K := K)) (F.source.block v)
      (Arithmetic.context c) F.source.columns F.source.columns φ
      (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) F.source.radius D.val)
    (y : FirstBlockProfileChart (E := ℝ) (Arithmetic.units_are_sixth c)
      (Arithmetic.localMeasures (K := K)) (F.source.block v)
      (Arithmetic.context c) F.source.columns F.source.columns ψ
      (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) F.source.radius D.val)
    (h : HEq x y) : x.kernel = y.kernel ∧ x.weight = y.weight := by
  cases e
  have he : x = y := eq_of_heq h
  exact ⟨congrArg FirstBlockProfileChart.kernel he,
    congrArg FirstBlockProfileChart.weight he⟩

theorem first_chart_kernel (F : FirstPresentation call p) (hF : F.Realizes)
    (v : F.source.CommonLabel) (D : ((F.source.block v).mask F.source.mask).powerset) :
    (F.source.charts v D).kernel = secondKernel c p := by
  exact (chart_projections_of_heq F v D hF.profile
    (F.source.charts v D) (F.canonicalChart v D) (hF.chart v D)).1

theorem first_family_fourier_mass {F : FirstPresentation call p}
    (hF : F.Realizes) (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (i : Fin family.count) :
    (actualFourierMeasure (family.source i).firstKernel).real Set.univ =
      firstFourierMass c p := by
  rw [hfamily.kernel i, first_chart_kernel F hF]
  rfl

private theorem first_active_radical_comm (F : FirstPresentation call p)
    (v : F.source.CommonLabel) :
    firstActiveRadical v.val.2 v.val.1 = firstActiveRadical v.val.1 v.val.2 := by
  unfold firstActiveRadical
  rw [← (F.source.block v).common_support_eq]
  congr 1
  apply Finset.filter_congr
  intro q _
  exact ne_comm

def firstSideAllowance {F : FirstPresentation call p} (key : FirstCauchyKey F)
    (N : F.source.Normalization) : ℝ :=
  if FirstCauchyKey.side key then
    N.right key.1 key.2.1 (FirstCauchyKey.residual key) (FirstCauchyKey.character key)
  else N.left key.1 key.2.1 (FirstCauchyKey.residual key) (FirstCauchyKey.character key)

theorem firstSideAllowance_pos {F : FirstPresentation call p} (key : FirstCauchyKey F)
    (N : F.source.Normalization) : 0 < firstSideAllowance key N := by
  unfold firstSideAllowance
  split_ifs
  · exact N.right_pos _ _ _ _
  · exact N.left_pos _ _ _ _

theorem first_family_side_allowance {F : FirstPresentation call p}
    (family : FirstCauchyFamily F) (hfamily : family.Realizes) (i : Fin family.count) :
    sourceSideAllowance (family.source i) =
      firstSideAllowance (family.index i) family.normalization := by
  unfold sourceSideAllowance firstSideAllowance
  rw [hfamily.selected i, hfamily.opposite i, hfamily.complementary i]
  cases hside : FirstCauchyKey.side (family.index i)
  · simp only [Bool.false_eq_true, if_false]
    rw [hfamily.leftAllowance]
    rfl
  · simp only [if_true]
    rw [hfamily.rightAllowance, first_active_radical_comm F (family.index i).1]
    rfl

/-- Only the selected allowance cancels; the two original square
roots are untouched. This includes the actual phase coefficient. -/
theorem first_key_outer_mul_allowance {F : FirstPresentation call p}
    (key : FirstCauchyKey F) (N : F.source.Normalization) :
    FirstCauchyKey.outer key N * firstSideAllowance key N =
      (F.source.fiber : ℝ) * ‖(moebius (FirstCauchyKey.residual key).val : ℂ)‖ *
        ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) (FirstCauchyKey.character key)‖ *
        ((FirstCauchyKey.piece key).rowBound *
          Real.sqrt (N.left key.1 key.2.1 (FirstCauchyKey.residual key)
            (FirstCauchyKey.character key)) *
          Real.sqrt (N.right key.1 key.2.1 (FirstCauchyKey.residual key)
            (FirstCauchyKey.character key)) / 2) := by
  change _ / firstSideAllowance key N * firstSideAllowance key N = _
  exact div_mul_cancel₀ _ (firstSideAllowance_pos key N).ne'

def firstTotal (F : FirstPresentation call p) (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) : ℝ :=
  call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z +
    call.workingParameters.q + idealLogLength call.base (firstActiveRadical v.val.1 v.val.2) +
    idealLogLength call.base (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val).val

def canonicalFirstWeightBound (F : FirstPresentation call p) (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) : ℝ :=
  CanonicalFirstLog.rowWeightBound
    (actualActiveColumn (Arithmetic.units_are_sixth c) (Arithmetic.context c)
      (F.source.block v).primes (F.source.block v).primes_injective
      (F.source.block v).leftMultiplicity (F.source.block v).rightMultiplicity)
    F.source.radius D.val p.tilt

theorem canonicalFirstWeightBound_nonneg (F : FirstPresentation call p)
    (v : F.source.CommonLabel) (D : ((F.source.block v).mask F.source.mask).powerset) :
    0 ≤ canonicalFirstWeightBound F v D :=
  CanonicalFirstLog.rowWeightBound_nonneg _ _ _ _

theorem first_weightBound_le (F : FirstPresentation call p) (hF : F.Realizes)
    (v : F.source.CommonLabel) (D : ((F.source.block v).mask F.source.mask).powerset) :
    (F.source.pieces v D).weightBound ≤ canonicalFirstWeightBound F v D := by
  let qbound : NNReal := ⟨canonicalFirstWeightBound F v D,
    canonicalFirstWeightBound_nonneg F v D⟩
  rw [hF.weight v D]
  change ((Finset.sup _ _ : NNReal) : ℝ) ≤ (qbound : ℝ)
  exact_mod_cast (show ((F.source.source v).divisorRows D.val).sup
      (fun q => ‖(F.source.charts v D).weight q‖₊) ≤ qbound from by
    apply Finset.sup_le
    intro q _
    change ‖(F.source.charts v D).weight q‖ ≤ canonicalFirstWeightBound F v D
    rw [(chart_projections_of_heq F v D hF.profile
      (F.source.charts v D) (F.canonicalChart v D) (hF.chart v D)).2]
    exact CanonicalFirstLog.norm_poissonTiltWeight_le _ _ _ p.tilt p.tilt_pos.le q)

/-- The standard first allowance identity also applies to the actual
direct piece. No pool or aggregate source bound is used here. -/
theorem first_row_allowance_le (F : FirstPresentation call p)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (v : F.source.CommonLabel) (D : ((F.source.block v).mask F.source.mask).powerset)
    (S : divisorPool (F.source.pieces v D).rightData.columns
      (fun i => ((F.source.pieces v D).rightData.ideal i).val))
    (chi : (PUnit.{1} × PUnit.{1}) →* Circle) (amplitude : ℝ)
    (hweight : (F.source.pieces v D).weightBound ≤
      amplitude * call.base ^
        (call.node.parameters.m + call.node.parameters.q - firstTotal F v D)) :
    (F.source.pieces v D).rowBound * Real.sqrt (family.normalization.left v D S chi) *
        Real.sqrt (family.normalization.right v D S chi) / call.parentNormalizer ≤
      amplitude * firstCommonWeight call.base v.val.1 v.val.2 := by
  rw [hfamily.leftAllowance, hfamily.rightAllowance]
  change (F.source.pieces v D).rowBound *
    Real.sqrt (firstLeftAllowance call.base (firstTotal F v D) v.val.1 v.val.2) *
    Real.sqrt (firstRightAllowance call.base (firstTotal F v D) v.val.1 v.val.2) /
    call.base ^ (call.node.parameters.m + call.node.parameters.q) ≤ _
  unfold FirstBlockDirectData.rowBound
  rw [(F.source.block v).activeNorm_eq]
  calc
    _ ≤ (amplitude * call.base ^
        (call.node.parameters.m + call.node.parameters.q - firstTotal F v D)) *
      Real.sqrt (Ideal.absNorm (firstActiveRadical v.val.1 v.val.2) : ℝ) *
      Real.sqrt (firstLeftAllowance call.base (firstTotal F v D) v.val.1 v.val.2) *
      Real.sqrt (firstRightAllowance call.base (firstTotal F v D) v.val.1 v.val.2) /
      call.base ^ (call.node.parameters.m + call.node.parameters.q) := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg call.base_pos.le _)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hweight (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    _ = amplitude * (call.base ^
        (call.node.parameters.m + call.node.parameters.q - firstTotal F v D) *
      Real.sqrt (Ideal.absNorm (firstActiveRadical v.val.1 v.val.2) : ℝ) *
      Real.sqrt (firstLeftAllowance call.base (firstTotal F v D) v.val.1 v.val.2) *
      Real.sqrt (firstRightAllowance call.base (firstTotal F v D) v.val.1 v.val.2) /
      call.base ^ (call.node.parameters.m + call.node.parameters.q)) := by ring
    _ = _ := by rw [first_allowance_scalar_identity _ _ _ call.domain.scale]

/-- Each common label inherits a norm bound from the actual complete
column dictionary, including columns with zero coefficient. -/
theorem first_common_norm_box (F : FirstPresentation call p) (Y : ℝ)
    (hN : ∀ i ∈ F.source.columns, (Arithmetic.data c).exteriorNorm (F.source.ideal i) ≤ Y)
    (v : F.source.CommonLabel) :
    (Ideal.absNorm v.val.1 : ℝ) ≤ Y ∧ (Ideal.absNorm v.val.2 : ℝ) ≤ Y := by
  obtain ⟨ij, hij, he⟩ := Finset.mem_image.mp v.property
  have hn := actual_common_label_norm_le (F.source.ideal ij.1).val
    (F.source.ideal ij.2).val (F.source.ideal ij.1).property.1
      (F.source.ideal ij.2).property.1
  rw [he] at hn
  exact ⟨hn.1.trans (hN ij.1 (Finset.mem_product.mp hij).1),
    hn.2.trans (hN ij.2 (Finset.mem_product.mp hij).2)⟩

theorem first_residual_divisor_box (F : FirstPresentation call p) (Y : ℝ)
    (hN : ∀ i ∈ F.source.columns, (Arithmetic.data c).exteriorNorm (F.source.ideal i) ≤ Y)
    (v : F.source.CommonLabel) (D : ((F.source.block v).mask F.source.mask).powerset)
    (S : divisorPool (F.source.pieces v D).rightData.columns
      (fun i => ((F.source.pieces v D).rightData.ideal i).val)) :
    S.val ≠ 0 ∧ (Ideal.absNorm S.val : ℝ) ≤ Y := by
  obtain ⟨j, hj, hS⟩ := Finset.mem_biUnion.mp S.property
  have hd := (mem_idealDivisors ((F.source.pieces v D).rightData.ideal j).property.1).mp hS
  have hj' : j ∈ F.source.columns := by
    rw [(F.source.pieces v D).right_columns] at hj
    exact (Finset.mem_filter.mp hj).1
  have hres : ((F.source.pieces v D).rightData.ideal j).val ∣ (F.source.ideal j).val := by
    rw [(F.source.pieces v D).right_ideal, (F.source.block v).right_residual]
    refine ⟨supportExtract (F.source.ideal j).val (primeSupport v.val.1), ?_⟩
    exact (support_reconstruct (F.source.ideal j).val (F.source.ideal j).property.1
      (primeSupport v.val.1)).symm.trans (mul_comm _ _)
  refine ⟨ne_zero_of_dvd_ne_zero ((F.source.pieces v D).rightData.ideal j).property.1 hd, ?_⟩
  exact (ideal_norm_le_of_dvd (F.source.ideal j).property.1 (hd.trans hres)).trans (hN j hj')

/-- The tiny Mellin factor is paid by the two literal original ideal
norms. The inverse physical and active norms remain in the scalar. -/
theorem first_weightBound_normalized (F : FirstPresentation call p) (hF : F.Realizes)
    (B : ℝ)
    (hN : ∀ i ∈ F.source.columns,
      (Arithmetic.data c).exteriorNorm (F.source.ideal i) ≤ call.base ^ B)
    (v : F.source.CommonLabel) (D : ((F.source.block v).mask F.source.mask).powerset) :
    (F.source.pieces v D).weightBound ≤
      (orbitalFieldFactor K * call.base ^
        (call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z +
          2 * B * p.tilt)) *
      call.base ^ (call.node.parameters.m + call.node.parameters.q - firstTotal F v D) := by
  let b := F.source.block v
  let r := actualActiveColumn (Arithmetic.units_are_sixth c) (Arithmetic.context c)
    b.primes b.primes_injective b.leftMultiplicity b.rightMultiplicity
  let mask := sIntegerMaskGenerator K (Arithmetic.data c).Sf D.val
  have hactive := generates_sIntegerElementNorm
    (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity)
    (firstActiveGenerator (Arithmetic.context c) b.primes b.leftMultiplicity b.rightMultiplicity)
    (firstActiveGenerator_generates (Arithmetic.context c) b.primes
      b.leftMultiplicity b.rightMultiplicity)
  change (sIntegerElementNorm K (Arithmetic.data c).Sf ⟨r.modulus, r.nonzero⟩).val =
    (Arithmetic.data c).exteriorNorm
      (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity) at hactive
  rw [b.activeNorm_eq] at hactive
  have hphysical := generates_sIntegerElementNorm
    (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val) mask.val
    (originalFrequencyIdeal_generates (A := Arithmetic.data c) mask.val mask.property)
  change (sIntegerElementNorm K (Arithmetic.data c).Sf mask).val =
    (Arithmetic.data c).exteriorNorm
      (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val) at hphysical
  have hcommon := (first_common_norm_box F _ hN v).1
  have hphys := (FirstZeroProof.first_physical_divisor_norm_le F hF v D).trans hcommon
  have hact := (FirstZeroProof.first_active_norm_le F v).trans hcommon
  have hradius : F.source.radius.val ≤ 1 := by
    rw [hF.radius]
    exact Real.rpow_le_one_of_one_le_of_nonpos call.domain.scale.le
      (neg_nonpos.mpr (FirstZeroProof.working_m_nonneg call hF.active))
  have hwindow :
      (sIntegerMaskDilationRadius K (Arithmetic.data c).Sf F.source.radius mask).val *
        (sIntegerElementNorm K (Arithmetic.data c).Sf ⟨r.modulus, r.nonzero⟩).val ≤
      call.base ^ (2 * B) := by
    change (F.source.radius.val * (sIntegerElementNorm K (Arithmetic.data c).Sf mask).val) *
      (sIntegerElementNorm K (Arithmetic.data c).Sf ⟨r.modulus, r.nonzero⟩).val ≤ _
    rw [hphysical, hactive]
    have hleft : F.source.radius.val * (Arithmetic.data c).exteriorNorm
        (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val) ≤ call.base ^ B := by
      exact (mul_le_mul_of_nonneg_right hradius
        ((Arithmetic.data c).exteriorNorm_pos _).le).trans (by simpa only [one_mul] using hphys)
    calc
      _ ≤ call.base ^ B * call.base ^ B := mul_le_mul hleft hact
        (Nat.cast_nonneg _) (Real.rpow_nonneg call.base_pos.le _)
      _ = _ := by rw [← Real.rpow_add call.base_pos]; congr 1; ring
  have ht := CanonicalFirstLog.rowWeightBound_le_of_norm_window r F.source.radius D.val
    p.tilt_pos.le call.base_pos hwindow
  rw [CanonicalFirstLog.norm_maskPoissonFactor] at ht
  change canonicalFirstWeightBound F v D ≤
    (orbitalFieldFactor K *
      (F.source.radius.val * (sIntegerElementNorm K (Arithmetic.data c).Sf mask).val)⁻¹ *
      (sIntegerElementNorm K (Arithmetic.data c).Sf ⟨r.modulus, r.nonzero⟩).val⁻¹) *
      call.base ^ ((2 * B) * p.tilt) at ht
  rw [hphysical, hactive, hF.radius] at ht
  apply (first_weightBound_le F hF v D).trans (ht.trans_eq ?_)
  rw [← rpow_idealLogLength call.base call.domain.scale
      (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val).val
      (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val).property.1,
    ← rpow_idealLogLength call.base call.domain.scale
      (firstActiveRadical v.val.1 v.val.2) (firstActiveRadical_ne_zero _ _)]
  change (orbitalFieldFactor K *
      (call.base ^ (-call.workingParameters.m) * call.base ^
        idealLogLength call.base (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val).val)⁻¹ *
      (call.base ^ idealLogLength call.base (firstActiveRadical v.val.1 v.val.2))⁻¹) *
      call.base ^ ((2 * B) * p.tilt) = _
  simp only [← Real.rpow_add call.base_pos, ← Real.rpow_neg call.base_pos.le]
  unfold firstTotal
  simp only [mul_assoc, ← Real.rpow_add call.base_pos]
  congr 2
  have hw := FirstZeroProof.working_width call
  linarith

/-- The arithmetic weight retains the true residual divisor. The
fixed finite phase and two Cauchy sides are counted separately. -/
def firstKeyWeight {F : FirstPresentation call p} (key : FirstCauchyKey F) : ℝ :=
  firstCommonWeight call.base key.1.val.1 key.1.val.2 *
    ‖(moebius (FirstCauchyKey.residual key).val : ℂ)‖ /
      (Ideal.absNorm (FirstCauchyKey.residual key).val : ℝ)

theorem firstKeyWeight_nonneg {F : FirstPresentation call p} (key : FirstCauchyKey F) :
    0 ≤ firstKeyWeight key :=
  div_nonneg (mul_nonneg (Real.rpow_nonneg call.base_pos.le _) (norm_nonneg _))
    (Nat.cast_nonneg _)

/-- Pointwise reduction of the actual first outer scalar. The factor
one half and the fixed phase are bounded only in this proof. -/
theorem first_key_outer_mass_le (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (B : ℝ)
    (hN : ∀ i ∈ F.source.columns,
      (Arithmetic.data c).exteriorNorm (F.source.ideal i) ≤ call.base ^ B)
    (key : FirstCauchyKey F) :
    FirstCauchyKey.outer key family.normalization * firstFourierMass c p *
        firstSideAllowance key family.normalization /
        (Ideal.absNorm (FirstCauchyKey.residual key).val : ℝ) / call.parentNormalizer ≤
      firstFourierMass c p * orbitalFieldFactor K *
        call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z + 2 * B * p.tilt) * firstKeyWeight key := by
  let N := family.normalization
  let w := (FirstCauchyKey.piece key).rowBound *
    Real.sqrt (N.left key.1 key.2.1 (FirstCauchyKey.residual key) (FirstCauchyKey.character key)) *
    Real.sqrt (N.right key.1 key.2.1 (FirstCauchyKey.residual key) (FirstCauchyKey.character key)) /
    call.parentNormalizer
  have hw0 : 0 ≤ w := by
    exact div_nonneg (mul_nonneg (mul_nonneg (FirstBlockDirectData.rowBound_nonneg _)
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) call.parentNormalizer_pos.le
  have hrow := first_row_allowance_le F family hfamily key.1 key.2.1
    (FirstCauchyKey.residual key) (FirstCauchyKey.character key)
    (orbitalFieldFactor K * call.base ^ (call.workingParameters.n₁ +
      call.workingParameters.n₂ + call.workingParameters.z + 2 * B * p.tilt))
    (first_weightBound_normalized F hF B hN key.1 key.2.1)
  have hphase : ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle))
      (FirstCauchyKey.character key)‖ / 2 ≤ (1 : ℝ) := by
    have h := fixed_phase_coefficient_norm PUnit (fun _ => (1 : Circle))
      (FirstCauchyKey.character key)
    linarith
  have hfactor : 0 ≤ firstFourierMass c p *
      (‖(moebius (FirstCauchyKey.residual key).val : ℂ)‖ /
        (Ideal.absNorm (FirstCauchyKey.residual key).val : ℝ)) :=
    mul_nonneg firstFourierMass_nonneg (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
  calc
    _ = (firstFourierMass c p *
        (‖(moebius (FirstCauchyKey.residual key).val : ℂ)‖ /
          (Ideal.absNorm (FirstCauchyKey.residual key).val : ℝ))) *
        (‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle))
          (FirstCauchyKey.character key)‖ / 2 * w) := by
      rw [show FirstCauchyKey.outer key family.normalization * firstFourierMass c p *
          firstSideAllowance key family.normalization = firstFourierMass c p *
          (FirstCauchyKey.outer key family.normalization * firstSideAllowance key family.normalization)
        by ring, first_key_outer_mul_allowance, hF.fiber]
      simp only [Nat.cast_one, one_mul]
      dsimp only [w, N]
      ring
    _ ≤ (firstFourierMass c p *
        (‖(moebius (FirstCauchyKey.residual key).val : ℂ)‖ /
          (Ideal.absNorm (FirstCauchyKey.residual key).val : ℝ))) * w :=
      mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_right hphase hw0).trans_eq (one_mul _)) hfactor
    _ ≤ (firstFourierMass c p *
        (‖(moebius (FirstCauchyKey.residual key).val : ℂ)‖ /
          (Ideal.absNorm (FirstCauchyKey.residual key).val : ℝ))) *
        ((orbitalFieldFactor K * call.base ^ (call.workingParameters.n₁ +
          call.workingParameters.n₂ + call.workingParameters.z + 2 * B * p.tilt)) *
          firstCommonWeight call.base key.1.val.1 key.1.val.2) :=
      mul_le_mul_of_nonneg_left hrow hfactor
    _ = _ := by unfold firstKeyWeight; ring

private theorem first_common_mass_uniform (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {call : Call c} {p : SourceParameters c}
      (F : FirstPresentation call p),
      (∀ i ∈ F.source.columns,
        (Arithmetic.data c).exteriorNorm (F.source.ideal i) ≤ call.base ^ B) →
      (∑ v : F.source.CommonLabel, firstCommonWeight call.base v.val.1 v.val.2) ≤
        C * call.base ^ δ := by
  obtain ⟨C, hC, hm⟩ := actual_first_common_mass (K := K) B δ hB hδ
  refine ⟨C, hC, ?_⟩
  intro call p F hN
  let pairs := commonSupportPool F.source.columns F.source.columns
    (fun i => (F.source.ideal i).val) (fun i => (F.source.ideal i).val)
  let decorate : (Ideal (𝓞 K) × Ideal (𝓞 K)) → CommonSupportMass.Label K :=
    fun DE => (DE, ∅)
  let labels := pairs.image decorate
  have hvalid : ∀ w ∈ labels, CommonSupportMass.Valid (1 : Ideal (𝓞 K)) w := by
    intro w hw
    obtain ⟨DE, hDE, rfl⟩ := Finset.mem_image.mp hw
    let v : F.source.CommonLabel := ⟨DE, hDE⟩
    have hleft : DE.1 ≠ 0 := by
      rw [← (F.source.block v).common_left]
      exact (primePowerProduct (F.source.block v).primes (F.source.block v).leftMultiplicity).property.1
    have hright : DE.2 ≠ 0 := by
      rw [← (F.source.block v).common_right]
      exact (primePowerProduct (F.source.block v).primes (F.source.block v).rightMultiplicity).property.1
    exact ⟨hleft, hright, (F.source.block v).common_support_eq,
      one_dvd _, one_dvd _, Finset.empty_subset _⟩
  have hnorm : ∀ w ∈ labels,
      (Ideal.absNorm w.1.1 : ℝ) ≤ call.base ^ B ∧
        (Ideal.absNorm w.1.2 : ℝ) ≤ call.base ^ B := by
    intro w hw
    obtain ⟨DE, hDE, rfl⟩ := Finset.mem_image.mp hw
    exact first_common_norm_box F _ hN ⟨DE, hDE⟩
  have hs := hm call.base call.domain.scale 1 (by simp) (by simp) labels hvalid hnorm
  have he : (∑ w ∈ labels, firstCommonWeight call.base w.1.1 w.1.2) =
      ∑ v : F.source.CommonLabel, firstCommonWeight call.base v.val.1 v.val.2 := by
    rw [Finset.sum_image (fun x _ y _ h => congrArg Prod.fst h)]
    exact (Finset.sum_coe_sort pairs
      (fun DE => firstCommonWeight call.base DE.1 DE.2)).symm
  rw [he] at hs
  simpa only [map_one, Nat.cast_one, div_one] using hs

private theorem sum_firstKeyWeight (F : FirstPresentation call p) :
    (∑ key : FirstCauchyKey F, firstKeyWeight key) =
      (2 * (Fintype.card ((PUnit.{1} × PUnit.{1}) →* Circle) : ℝ)) *
        ∑ v : F.source.CommonLabel, firstCommonWeight call.base v.val.1 v.val.2 *
          ∑ D : ((F.source.block v).mask F.source.mask).powerset,
            ∑ S : divisorPool (F.source.pieces v D).rightData.columns
              (fun i => ((F.source.pieces v D).rightData.ideal i).val),
              ‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ) := by
  simp only [FirstCauchyKey, Fintype.sum_sigma, Fintype.sum_prod_type,
    firstKeyWeight, FirstCauchyKey.residual, Finset.sum_const, Finset.card_univ,
    Fintype.card_bool, nsmul_eq_mul, Nat.cast_ofNat]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro D _
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- Constants precede the complete moving carrier. The physical-mask
cardinality, common-support mass and one residual divisor density each
consume an arbitrarily small exponent. No old-mask divisibility is
added to the original column contract. -/
theorem first_key_mass_uniform (c : TargetContext K) (B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {call : Call c} {p : SourceParameters c}
      (F : FirstPresentation call p), F.Realizes →
      (∀ i ∈ F.source.columns,
        (Arithmetic.data c).exteriorNorm (F.source.ideal i) ≤ call.base ^ B) →
      (∑ key : FirstCauchyKey F, firstKeyWeight key) ≤ C * call.base ^ ε := by
  let δ := ε / 3
  have hδ : 0 < δ := div_pos hε (by norm_num)
  obtain ⟨Ccommon, hCcommon, hcommon⟩ := first_common_mass_uniform (c := c) B δ hB hδ
  obtain ⟨Cmask, hCmask, hmask⟩ := FirstZeroProof.first_empty_mask_card_uniform (K := K) B δ hB hδ
  obtain ⟨Cdivisor, hCdivisor, hdivisor⟩ :=
    CommonSupportMass.ideal_inverse_norm_subpower (K := K) B δ hB hδ
  let nphase : ℝ := Fintype.card ((PUnit.{1} × PUnit.{1}) →* Circle)
  have hnphase : 0 ≤ nphase := Nat.cast_nonneg _
  refine ⟨(2 * (nphase + 1)) * Ccommon * Cmask * Cdivisor, by positivity, ?_⟩
  intro call p F hF hN
  have hdiv (v : F.source.CommonLabel)
      (D : ((F.source.block v).mask F.source.mask).powerset) :
      (∑ S : divisorPool (F.source.pieces v D).rightData.columns
        (fun i => ((F.source.pieces v D).rightData.ideal i).val),
          ‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) ≤
      Cdivisor * call.base ^ δ := by
    rw [Finset.sum_coe_sort]
    calc
      _ ≤ ∑ S ∈ divisorPool (F.source.pieces v D).rightData.columns
          (fun i => ((F.source.pieces v D).rightData.ideal i).val),
          1 / (Ideal.absNorm S : ℝ) := by
        apply Finset.sum_le_sum
        intro S _
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        unfold UniqueFactorizationMonoid.moebius
        split_ifs <;> simp
      _ ≤ _ := hdivisor call.base call.domain.scale.le _
        (fun S hS => (first_residual_divisor_box F _ hN v D ⟨S, hS⟩).1)
        (fun S hS => (first_residual_divisor_box F _ hN v D ⟨S, hS⟩).2)
  have hinner (v : F.source.CommonLabel) :
      (∑ D : ((F.source.block v).mask F.source.mask).powerset,
        ∑ S : divisorPool (F.source.pieces v D).rightData.columns
          (fun i => ((F.source.pieces v D).rightData.ideal i).val),
          ‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) ≤
      (Cmask * call.base ^ δ) * (Cdivisor * call.base ^ δ) := by
    have hc : (((F.source.block v).mask F.source.mask).powerset.card : ℝ) ≤
        Cmask * call.base ^ δ := by
      rw [hF.mask]
      exact hmask call.base call.domain.scale.le (F.source.block v)
        (first_common_norm_box F _ hN v).1
    calc
      _ ≤ ∑ _D : ((F.source.block v).mask F.source.mask).powerset,
          Cdivisor * call.base ^ δ := Finset.sum_le_sum fun D _ => hdiv v D
      _ = (((F.source.block v).mask F.source.mask).powerset.card : ℝ) *
          (Cdivisor * call.base ^ δ) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc
        (mul_nonneg hCdivisor.le (Real.rpow_nonneg call.base_pos.le _))
  have hbase : (∑ v : F.source.CommonLabel, firstCommonWeight call.base v.val.1 v.val.2 *
      ∑ D : ((F.source.block v).mask F.source.mask).powerset,
        ∑ S : divisorPool (F.source.pieces v D).rightData.columns
          (fun i => ((F.source.pieces v D).rightData.ideal i).val),
          ‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) ≤
      (Ccommon * Cmask * Cdivisor) * call.base ^ ε := by
    calc
      _ ≤ ∑ v : F.source.CommonLabel, firstCommonWeight call.base v.val.1 v.val.2 *
          ((Cmask * call.base ^ δ) * (Cdivisor * call.base ^ δ)) :=
        Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hinner v)
          (Real.rpow_nonneg call.base_pos.le _)
      _ = (∑ v : F.source.CommonLabel, firstCommonWeight call.base v.val.1 v.val.2) *
          ((Cmask * call.base ^ δ) * (Cdivisor * call.base ^ δ)) := by rw [Finset.sum_mul]
      _ ≤ (Ccommon * call.base ^ δ) *
          ((Cmask * call.base ^ δ) * (Cdivisor * call.base ^ δ)) :=
        mul_le_mul_of_nonneg_right (hcommon F hN) (by positivity)
      _ = _ := by
        rw [show ε = δ + δ + δ by dsimp only [δ]; ring,
          Real.rpow_add call.base_pos, Real.rpow_add call.base_pos]
        ring
  rw [sum_firstKeyWeight]
  calc
    _ ≤ (2 * nphase) * ((Ccommon * Cmask * Cdivisor) * call.base ^ ε) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ ≤ (2 * (nphase + 1)) * ((Ccommon * Cmask * Cdivisor) * call.base ^ ε) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

/-- The complete first Cauchy family carries its one actual Fourier
measure and one residual divisor density. The bound is uniform before
the moving call, the source, or either index bijection is selected. -/
theorem first_family_mass_uniform (c : TargetContext K) (p : SourceParameters c)
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {call : Call c}
      (F : FirstPresentation call p), F.Realizes →
      ∀ family : FirstCauchyFamily F, family.Realizes →
      (∀ i ∈ F.source.columns,
        (Arithmetic.data c).exteriorNorm (F.source.ideal i) ≤ call.base ^ B) →
      (∑ i, (family.source i).outerWeight *
        (actualFourierMeasure (family.source i).firstKernel).real Set.univ *
        sourceSideAllowance (family.source i) /
        (Ideal.absNorm (family.source i).first.residualDivisor.val : ℝ) /
        call.parentNormalizer) ≤
      C * call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
        call.workingParameters.z + 2 * B * p.tilt + ε) := by
  obtain ⟨Cindex, hCindex, hindex⟩ := first_key_mass_uniform c B ε hB hε
  have hmass := firstFourierMass_nonneg (c := c) (p := p)
  have horbital := orbitalFieldFactor_nonneg K
  refine ⟨1 + firstFourierMass c p * orbitalFieldFactor K * Cindex, by positivity, ?_⟩
  intro call F hF family hfamily hN
  let prefactor := firstFourierMass c p * orbitalFieldFactor K *
    call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
      call.workingParameters.z + 2 * B * p.tilt)
  have hprefactor : 0 ≤ prefactor := by dsimp only [prefactor]; positivity
  have hsum : (∑ i, (family.source i).outerWeight *
      (actualFourierMeasure (family.source i).firstKernel).real Set.univ *
      sourceSideAllowance (family.source i) /
      (Ideal.absNorm (family.source i).first.residualDivisor.val : ℝ) /
      call.parentNormalizer) ≤
      prefactor * ∑ key : FirstCauchyKey F, firstKeyWeight key := by
    calc
      _ ≤ ∑ i, prefactor * firstKeyWeight (family.index i) := by
        apply Finset.sum_le_sum
        intro i _
        rw [hfamily.outer i, first_family_fourier_mass hF family hfamily i,
          first_family_side_allowance family hfamily i, hfamily.residual i]
        exact first_key_outer_mass_le F hF family hfamily B hN (family.index i)
      _ = prefactor * ∑ i, firstKeyWeight (family.index i) := by rw [Finset.mul_sum]
      _ = _ := by
        congr 1
        exact Fintype.sum_equiv family.index _ _ (fun i => rfl)
  calc
    _ ≤ prefactor * (Cindex * call.base ^ ε) :=
      hsum.trans (mul_le_mul_of_nonneg_left (hindex F hF hN) hprefactor)
    _ = (firstFourierMass c p * orbitalFieldFactor K * Cindex) *
        call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z + 2 * B * p.tilt + ε) := by
      dsimp only [prefactor]
      rw [Real.rpow_add call.base_pos]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg call.base_pos.le _)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof
