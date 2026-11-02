import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstZeroFactorization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstZeroMaskBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstZeroNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstZeroSignedBound

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T1: fixed original-profile witnesses for the actual first zero

The finite orders, scalar coefficient and annulus threshold are chosen
before any moving call. All subsequent premises are exactly the input
readiness and actual first-source realization from the public contract.
The powerful tuple count uses the original ordered factors, and both
parts of the signed zero are paid before the original parent division.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineStep HeckeSkeleton.Moments.EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

/-- The original zero-frequency estimate, with the public order of
quantifiers. No transformed bound is inserted into eligibility. -/
theorem uniform_first_zero_certificate (c : TargetContext K)
    (p : SourceParameters c) (frame : SourceFrame) :
    Nonempty (FirstZeroCertificate c frame p) := by
  obtain ⟨eta, Czero, hCzero, hzero⟩ :=
    Tasks.first_signed_zero_diagonal_supported
      (A := Arithmetic.data c) (Γ := Arithmetic.unitSubgroup c)
      (σ := Arithmetic.embedding c) (η := (Arithmetic.choice c).η)
      (hS := (Arithmetic.choice c).hS)
      (hΓ := Arithmetic.units_are_sixth c) (μv := Arithmetic.localMeasures (K := K))
      (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)
      (2 * (c.geometry.slots + 2)) (firstCountingExponent c p)
      (firstCountingExponent_pos p)
  obtain ⟨Cmask, hCmask, hmask⟩ := first_source_mask_sum_uniform c
    (firstColumnExponent c p) p.loss (firstColumnExponent_pos p).le p.loss_pos
  obtain ⟨Z₀, hZ₀, hannulus⟩ := original_annulus_power_threshold
    c.geometry.slots (uniformAnnulus c frame) p.loss p.loss_pos
  let Cprofile := 4 * originalArchSeminorm c eta
  have hCprofile : 0 ≤ Cprofile :=
    mul_nonneg (by norm_num) (originalArchSeminorm_nonneg c eta)
  let coefficient := Czero * ((1 + Cmask) * Cprofile)
  have hcoefficient : 0 ≤ coefficient :=
    mul_nonneg hCzero.le (mul_nonneg (by linarith) hCprofile)
  let cost : UniformCost := {
    orders := {(0, 0)}
    coefficient := coefficient
    coefficient_nonneg := hcoefficient
    profileDegree := 2 * (c.geometry.slots + 2)
    heightDegree := 0
    heightDegree_nonneg := le_rfl
    threshold := Z₀
    threshold_one_le := hZ₀.le }
  refine ⟨{ cost := cost, bound := ?_ }⟩
  intro call input hframe hready F hF
  have horders : {(0, 0)} ⊆ input.orders := hready.orders
  have hannulusZ : uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤
      call.base ^ p.loss := hannulus call.base hready.large
  let L := call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z
  let P := Cprofile * input.amplitude ^ (2 * (c.geometry.slots + 2))
  let N := call.base ^ (2 * (L + p.loss))
  let Amp := ((1 + Cmask) * P) *
    call.base ^ (call.workingParameters.m + 2 * p.loss)
  have hP : 0 ≤ P := mul_nonneg hCprofile
    (pow_nonneg (zero_le_one.trans input.amplitude_one_le) _)
  have hAmp : 0 ≤ Amp := mul_nonneg (mul_nonneg (by linarith) hP)
    (Real.rpow_nonneg call.base_pos.le _)
  have hN : 1 ≤ N := Real.one_le_rpow call.domain.scale.le
    (mul_nonneg (by norm_num) (add_nonneg (original_total_nonneg call) p.loss_pos.le))
  have hnormalization
      (v : FirstZeroLabel F.source.columns F.source.columns F.source.ideal F.source.ideal ×
        (F.source.Column × F.source.Column))
      (hv : v ∈ firstZeroPairs F.source.columns F.source.columns
        F.source.ideal F.source.ideal) :
      eta.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
          (F.source.profiles v.2.1 v.2.2) *
        (∑ D ∈ ((F.source.block v.1).mask F.source.mask).powerset,
          firstZeroDivisorWeight F.source.radius D) ≤ Amp / Real.sqrt N ∧
      eta.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
          (F.source.profiles v.2.1 v.2.2) ≤ Amp / Real.sqrt N := by
    by_cases hφ : F.source.profiles v.2.1 v.2.2 = 0
    · simp only [hφ, map_zero, zero_mul]
      exact ⟨div_nonneg hAmp (Real.sqrt_nonneg N),
        div_nonneg hAmp (Real.sqrt_nonneg N)⟩
    · have hmem := (mem_firstZeroPairs F.source.columns F.source.columns
        F.source.ideal F.source.ideal v).mp hv
      have hcoefficient : F.coefficient v.2.1 ≠ 0 := by
        intro hz
        apply hφ
        rw [hF.profile, FirstPresentation.originalProfile, hz, zero_mul, zero_smul]
      have hleft := first_active_column_norm_le frame input hframe p.loss hannulusZ F hF
        v.2.1 hmem.1 hcoefficient
      have hleftfixed : (Arithmetic.data c).exteriorNorm (F.source.ideal v.2.1) ≤
          call.base ^ firstColumnExponent c p := by
        apply hleft.trans
        apply Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
        dsimp only [firstColumnExponent]
        have htotal := working_total_le call
        linarith
      have hweight := hmask F hF v hv hleftfixed
      have hprofile :
          eta.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
            (F.source.profiles v.2.1 v.2.2) ≤ P * call.base ^ (-L) :=
        first_source_profile_seminorm_le input horders F hF eta
          v.2.1 v.2.2 hmem.1 hmem.2.1
      exact first_profile_normalization call.base P Cmask L call.workingParameters.m p.loss
        _ _ call.domain.scale.le hP hCmask.le (working_m_nonneg call hF.active) p.loss_pos.le
        hprofile (apply_nonneg _ _) hweight
        (Finset.sum_nonneg (fun D _ => firstZeroDivisorWeight_nonneg F.source.radius D))
  have hnorm : ∀ ij ∈ F.source.columns ×ˢ F.source.columns,
      F.source.profiles ij.1 ij.2 ≠ 0 →
      (Ideal.absNorm ((F.source.ideal ij.1).val * (F.source.ideal ij.2).val) : ℝ) ≤ N := by
    intro ij hij hφ
    exact first_active_pair_norm_le frame input hframe p.loss hannulusZ F hF ij hij hφ
  have hz := hzero (Arithmetic.context c) F.source.columns F.source.columns
    F.source.ideal F.source.ideal F.source.block F.source.profiles
    (Arithmetic.different c) F.source.radius F.source.mask
    (p.firstCutoff call) (p.firstCutoff_one call)
    (firstPairFactors F) (firstPairFactors_injective F).injOn
    (firstPairFactors_product F hF) N Amp hN hAmp hnorm
    (fun v hv => (hnormalization v hv).1) (fun v hv => (hnormalization v hv).2)
  change F.source.zeroCost (Arithmetic.different c) ≤
    Czero * Amp * N ^ firstCountingExponent c p at hz
  have hparent := first_parent_normalization p call Czero ((1 + Cmask) * P)
    hCzero.le (mul_nonneg (by linarith) hP)
  calc
    F.normalizedZero = F.source.zeroCost (Arithmetic.different c) / call.parentNormalizer := by
      simp only [FirstPresentation.normalizedZero, Call.normalizedScalar,
        FirstPresentation.zero, hF.fiber, Nat.cast_one, one_mul]
    _ ≤ (Czero * Amp * N ^ firstCountingExponent c p) / call.parentNormalizer :=
      div_le_div_of_nonneg_right hz call.parentNormalizer_pos.le
    _ ≤ Czero * ((1 + Cmask) * P) * call.base ^ recipeInductionTerminalLoss c := hparent
    _ = cost.value input.amplitude call.request.height *
        call.base ^ recipeInductionTerminalLoss c := by
      simp only [cost, UniformCost.value, Real.rpow_zero, mul_one]
      dsimp only [coefficient, P]
      ring

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof
