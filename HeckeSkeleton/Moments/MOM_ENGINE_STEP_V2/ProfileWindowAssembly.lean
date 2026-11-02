import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ProfileWindowContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ProfileAssembly
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ClippedAnnulusSchedule
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActiveChildAnnulus

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Actual raw and clipped windows from the global formula task

N5a is used once on a fixed maximal original annulus. The actual raw
window is recovered from its global formula. Clipping is constructed
for all labels with the exact cost of the original two scales. The
same polynomial radius controls raw and clipped profiles; only the
active source needs the uniform cost bound used in the mass estimate.
No unfinished task is imported by this pure assembly.
-/

noncomputable section
open scoped Classical SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction EngineInduction.Source Blueprint

variable {K : Type} [Field K] [NumberField K]

/-- A nonzero value of the transformed formula comes from a nonzero
value of the same original profile at the actual dilated argument. -/
private theorem formula_support (f : ProfileFormula) (lower upper : ℝ)
    (hsupport : Function.support f.original ⊆ Set.Icc lower upper)
    (ξ : EngineParameter) :
    Function.support (f.value ξ) ⊆ f.window lower upper := by
  intro x hx
  have hxvalue : f.value ξ x ≠ 0 := hx
  have hxpos : 0 < x := by
    by_contra h
    simp only [ProfileFormula.value, if_neg h] at hxvalue
    exact hxvalue rfl
  have horiginal : f.original (f.dilation * x) ≠ 0 := by
    intro h
    simp [ProfileFormula.value, hxpos, h] at hxvalue
  have hmem := hsupport horiginal
  change lower / f.dilation ≤ x ∧ x ≤ upper / f.dilation
  exact ⟨(div_le_iff₀ f.dilation_pos).2 (by simpa only [mul_comm] using hmem.1),
    (le_div_iff₀ f.dilation_pos).2 (by simpa only [mul_comm] using hmem.2)⟩

/-- Restrict the original support window without changing any uniform
order, degree or coefficient, or any of the chosen representatives. -/
private def restrictFormulaCertificate {shape : ProfileShape}
    {largeLower largeUpper : ℝ} {orders : Finset (ℕ × ℕ)}
    (certificate : ProfileFormulaCertificate shape largeLower largeUpper orders)
    (lower upper : ℝ)
    (hwindow : Set.Icc lower upper ⊆ Set.Icc largeLower largeUpper) :
    ProfileFormulaCertificate shape lower upper orders where
  inputOrders := certificate.inputOrders
  degree := certificate.degree
  coefficient := certificate.coefficient
  coefficient_pos := certificate.coefficient_pos
  control f bounded hsupport amplitude scalarBound hamplitude hscalar hnorm hfactor := by
    let original := Classical.choice (certificate.control f bounded
      (hsupport.trans hwindow) amplitude scalarBound hamplitude hscalar hnorm hfactor)
    refine ⟨{
      representative := original.representative
      value_eq := original.value_eq
      support := ?_
      bound := original.bound }⟩
    intro ξ x hx
    apply formula_support f lower upper hsupport ξ
    change f.value ξ x ≠ 0
    rw [← original.value_eq ξ x]
    exact hx

private def uniformRankBound (c : TargetContext K) : ℕ :=
  6 * (widthBand (recipeInductionSigma c) 2 + 1)

private def uniformLower (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  (frame.lower / clippedAnnulusStep frame.upper (uniformRankBound c) ^
    uniformRankBound c) / 2

private def uniformUpper (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  2 * (frame.upper * (2 : ℝ) ^ uniformRankBound c)

private theorem uniformLower_pos (c : TargetContext K) (frame : SourceFrame) :
    0 < uniformLower c frame := by
  exact div_pos (div_pos frame.lower_pos
    (pow_pos (clippedAnnulusStep_pos frame.upper (uniformRankBound c)) _))
    (by norm_num)

private theorem uniformInterval (c : TargetContext K) (frame : SourceFrame) :
    uniformLower c frame ≤ uniformUpper c frame := by
  have hleft : frame.lower /
      clippedAnnulusStep frame.upper (uniformRankBound c) ^ uniformRankBound c ≤
      frame.lower := by
    simpa only [clippedAnnulusLower, Nat.sub_zero] using
      clippedAnnulusLower_le frame.lower_pos.le (uniformRankBound c) 0
  have hupper : 0 ≤ frame.upper := (frame.lower_pos.trans frame.interval).le
  have hright : frame.upper ≤ frame.upper * (2 : ℝ) ^ uniformRankBound c :=
    le_mul_of_one_le_right hupper (one_le_pow₀ (by norm_num))
  have hsmall : 0 < frame.lower /
      clippedAnnulusStep frame.upper (uniformRankBound c) ^ uniformRankBound c :=
    div_pos frame.lower_pos
      (pow_pos (clippedAnnulusStep_pos frame.upper (uniformRankBound c)) _)
  dsimp only [uniformLower, uniformUpper]
  linarith [frame.interval]

private theorem enlarged_window_subset {lower upper : ℝ}
    (hlower : 0 ≤ lower) (hupper : 0 ≤ upper) (N rank : ℕ) :
    Set.Icc (clippedAnnulusLower lower upper N rank / 2)
        (2 * rankedAnnulusUpper upper N rank) ⊆
      Set.Icc ((lower / clippedAnnulusStep upper N ^ N) / 2)
        (2 * (upper * (2 : ℝ) ^ N)) := by
  have hlo : lower / clippedAnnulusStep upper N ^ N ≤
      clippedAnnulusLower lower upper N rank :=
    div_le_div_of_nonneg_left hlower
      (pow_pos (clippedAnnulusStep_pos upper N) _)
      (pow_le_pow_right₀ (clippedAnnulusStep_one_le upper N) (Nat.sub_le N rank))
  have hhi : rankedAnnulusUpper upper N rank ≤ upper * (2 : ℝ) ^ N :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le N rank)) hupper
  intro x hx
  exact ⟨(div_le_div_of_nonneg_right hlo (by norm_num)).trans hx.1,
    hx.2.trans (mul_le_mul_of_nonneg_left hhi (by norm_num))⟩

private theorem parentWindow_subset {c : TargetContext K}
    (frame : SourceFrame) (call : Call c) (input : ProfileInput call)
    (hframe : call.frame = frame) :
    call.window ⊆ Set.Icc (uniformLower c frame) (uniformUpper c frame) := by
  have h := enlarged_window_subset frame.lower_pos.le
    (frame.lower_pos.trans frame.interval).le (uniformRankBound c) call.rank
  simpa only [Call.window, input.regular.lower, input.regular.upper,
    hframe, Call.rankBound, uniformRankBound, uniformLower, uniformUpper] using h

private theorem uniformUpper_one_le (c : TargetContext K) (frame : SourceFrame) :
    1 ≤ uniformUpper c frame := by
  have hupper : 0 ≤ frame.upper := (frame.lower_pos.trans frame.interval).le
  have hmul : frame.upper ≤ frame.upper * (2 : ℝ) ^ uniformRankBound c :=
    le_mul_of_one_le_right hupper (one_le_pow₀ (by norm_num))
  dsimp only [uniformUpper]
  linarith [frame.upper_large]

private theorem callUpper_one_le {c : TargetContext K} {call : Call c}
    (input : ProfileInput call) : 1 ≤ 2 * call.prepared.upper := by
  rw [input.regular.upper]
  have hupper : 0 ≤ call.frame.upper :=
    (call.frame.lower_pos.trans call.frame.interval).le
  have hmul : call.frame.upper ≤ rankedAnnulusUpper call.frame.upper call.rankBound call.rank :=
    le_mul_of_one_le_right hupper (one_le_pow₀ (by norm_num))
  linarith [call.frame.upper_large]

private theorem callUpper_le_uniform {c : TargetContext K}
    (frame : SourceFrame) (call : Call c) (input : ProfileInput call)
    (hframe : call.frame = frame) :
    2 * call.prepared.upper ≤ uniformUpper c frame := by
  rw [input.regular.upper]
  change 2 * (call.frame.upper * (2 : ℝ) ^ (uniformRankBound c - call.rank)) ≤
    2 * (frame.upper * (2 : ℝ) ^ uniformRankBound c)
  rw [hframe]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (Nat.sub_le (uniformRankBound c) call.rank))
      (frame.lower_pos.trans frame.interval).le) (by norm_num)

/-- The raw dictionary is N3's actual global formula. The clipped
window is constructed here, with its computed scale coefficient. -/
theorem profile_windows_of_formula (c : TargetContext K)
    (formula_control : ProfileFormulaTask) : ProfileWindowTask c := by
  intro frame shape orders
  let certificate := Classical.choice (formula_control shape
    (uniformLower c frame) (uniformUpper c frame)
    (uniformLower_pos c frame) (uniformInterval c frame) orders)
  let uniformClip := CanonicalLogProfiles.clippingCoefficient (uniformUpper c frame) orders
  have hclipOne : 1 ≤ uniformClip :=
    CanonicalLogProfiles.clippingCoefficient_one_le _ (uniformUpper_one_le c frame) orders
  let cost := uniformClip * (1 + certificate.coefficient)
  have hcost : 0 < cost := by
    exact mul_pos (zero_lt_one.trans_le hclipOne) (by linarith [certificate.coefficient_pos])
  refine ⟨{
    inputOrders := certificate.inputOrders
    degree := certificate.degree
    coefficient := certificate.coefficient
    coefficient_pos := certificate.coefficient_pos
    costCoefficient := cost
    costCoefficient_pos := hcost
    windows := ?_ }⟩
  intro call input hframe horders H k s D scalarBound hscalar dictionary
  let actual := restrictFormulaCertificate certificate
    (call.prepared.lower / 2) (2 * call.prepared.upper)
    (parentWindow_subset frame call input hframe)
  let raw := fun ξ => profileWindow_of_dictionary dictionary actual horders hscalar ξ
  let Braw := certificate.coefficient * input.amplitude * scalarBound
  let R := ProfileWindowProof.actualClippingCoefficient s.base D.calibration.parameters orders
  have hamp : 0 ≤ input.amplitude := zero_le_one.trans input.amplitude_one_le
  have hBraw : 0 ≤ Braw := mul_nonneg
    (mul_nonneg certificate.coefficient_pos.le hamp) hscalar
  have hRone : 1 ≤ R :=
    ProfileWindowProof.actualClippingCoefficient_one_le _ _ _ s.base_gt_one.le
  have hR : 0 ≤ R := zero_le_one.trans hRone
  have ha : 0 < call.prepared.lower / 2 := div_pos call.prepared.lower_pos (by norm_num)
  have hB := callUpper_one_le input
  refine ⟨{
    coefficient_nonneg := CanonicalFullKappaPrime.enlargedCoefficient_nonneg hBraw hR
    original := ?_
    clipped := ?_
    active_cost := ?_ }⟩
  · intro ξ
    exact (raw ξ).mono (CanonicalFullKappaPrime.radius_le_enlarged Braw R hBraw hRone
      certificate.degree certificate.degree (WithLp.ofLp ξ))
  · intro ξ
    let clipped := ProfileWindowProof.clipRawWindow_broad
      (D.calibration.data ξ) D.calibration.parameters s.base s.base_gt_one.le
      (call.prepared.lower / 2) (2 * call.prepared.upper) ha hB orders
      (polynomialProfileRadius_pos Braw hBraw certificate.degree certificate.degree
        (WithLp.ofLp ξ)).le (raw ξ)
    apply clipped.mono
    exact (mul_comm R _).trans_le
      (CanonicalFullKappaPrime.radius_mul_le_enlarged Braw R hR
        certificate.degree certificate.degree (WithLp.ofLp ξ))
  · intro hactive
    have hclipping := ActiveChildAnnulus.active_clipping_factors (cal := D.calibration)
      hB raw (fun _ _ _ => Set.mem_univ _) (fun _ => Set.mem_univ _) hactive
    have hupper := callUpper_le_uniform frame call input hframe
    have hRbound : R ≤ uniformClip :=
      ProfileWindowProof.actualClippingCoefficient_le _ _ _ s.base_gt_one.le
        (uniformUpper c frame) (hclipping.1.trans hupper) (hclipping.2.trans hupper)
    have hins : 1 + Braw ≤
        (1 + certificate.coefficient) * input.amplitude * (1 + scalarBound) := by
      dsimp only [Braw]
      nlinarith [input.amplitude_one_le,
        mul_nonneg certificate.coefficient_pos.le hamp, mul_nonneg hamp hscalar]
    calc
      _ = R * (1 + Braw) := rfl
      _ ≤ uniformClip * (1 + Braw) :=
        mul_le_mul_of_nonneg_right hRbound (by linarith)
      _ ≤ uniformClip * ((1 + certificate.coefficient) * input.amplitude *
          (1 + scalarBound)) := mul_le_mul_of_nonneg_left hins (zero_le_one.trans hclipOne)
      _ = cost * input.amplitude * (1 + scalarBound) := by dsimp only [cost]; ring

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.profile_windows_of_formula
