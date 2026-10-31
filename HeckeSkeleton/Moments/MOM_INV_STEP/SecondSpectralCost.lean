import HeckeSkeleton.Moments.MOM_INV_STEP.SecondProductionIntegral
import HeckeSkeleton.Moments.MOM_INV_STEP.IteratedFrequencyBudget
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstSpectralAggregation

/-!
# Paying the actual second spectral cost

The finite seminorm required by the canonical child induction is bounded
by one explicit continuous polynomial in the two actual frequencies.
The second Fourier exponent is chosen to equal that polynomial degree.
Its integral uses the literal second Mellin density and the literal
Cauchy mass, and reduces exactly to the already controlled two-pass
Mellin cost. All constants and seminorms are chosen before any arithmetic
source, row, mask, or frequency.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondSpectralCost

open MeasureTheory CommonKernel FirstCommonEnvelope NestedMellinBudget
  IteratedFrequencyBudget FirstCenteredErrorIntegrals FirstSpectralAggregation
open scoped Classical BigOperators

/-- A continuous majorant, used as the actual `Cchild` in the second
source integral. No measurability of a supremum of seminorms is assumed. -/
def polynomialCost (k : ℕ) (B : ℝ) (L : LogPlane →L[ℝ] ℝ)
    (p : LogPlane × ℝ) : ℝ :=
  B * (1 + |p.2|) ^ k * (1 + |L p.1|) ^ k

theorem polynomialCost_nonneg (k : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (L : LogPlane →L[ℝ] ℝ) (p : LogPlane × ℝ) :
    0 ≤ polynomialCost k B L p := by
  unfold polynomialCost
  positivity

theorem polynomialCost_continuous (k : ℕ) (B : ℝ) (L : LogPlane →L[ℝ] ℝ) :
    Continuous (polynomialCost k B L) := by
  unfold polynomialCost
  fun_prop

/-- The fixed finite child seminorm chooses the second decay exponent
and the coefficient before both frequencies and the coordinate map. -/
theorem exists_seminorm_majorant (q : Finset (ℕ × ℕ)) :
    ∃ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ (L : LogPlane →L[ℝ] ℝ) (p : LogPlane × ℝ),
        (q.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (FinalMellinTests.weightedTest 0 (p.2 + L p.1))) ^ 2 ≤
            polynomialCost k B L p := by
  obtain ⟨m, A, hA, hb⟩ := FinalMellinTests.combined_frequency_seminorm_bound 0 q
  refine ⟨2 * m, A ^ 2, sq_nonneg A, fun L p => ?_⟩
  have hh := pow_le_pow_left₀ (apply_nonneg _ _) (hb p.2 (L p.1)) 2
  simpa only [polynomialCost, mul_pow, ← pow_mul, Nat.mul_comm] using hh

/-- The production density is exactly the density in the Mellin
moment ledger, including its negative half-power test. -/
theorem actual_mellinDensity_eq (s : ℝ) :
    SecondMellinEnergy.mellinDensity (SecondProductionIntegral.mellinTest s)
      (SecondProductionIntegral.mellinTest_support s) =
        secondDensity (-(1 / 2 : ℝ)) s := by
  simp only [SecondMellinEnergy.mellinDensity, SecondProductionIntegral.mellinTest,
    secondDensity, secondTest, neg_div]

theorem jointDensity_eq (s : ℝ) (k : ℕ) (p : LogPlane × ℝ) :
    SecondProductionIntegral.jointDensity s k p =
      frequencyEnvelope k p.1 * ‖secondDensity (-(1 / 2 : ℝ)) s p.2‖ := by
  simp only [SecondProductionIntegral.jointDensity, actual_mellinDensity_eq]

theorem joint_polynomial_integrable (s : ℝ) (k : ℕ) (B : ℝ)
    (L : LogPlane →L[ℝ] ℝ) :
    Integrable (fun p : LogPlane × ℝ =>
      SecondProductionIntegral.jointDensity s k p * polynomialCost k B L p)
      ((volume : Measure LogPlane).prod (volume : Measure ℝ)) := by
  have hi := ((weighted_coordinate_integrable L k).mul_prod
    (moment_integrable (-(1 / 2 : ℝ)) s k)).const_mul B
  convert hi using 1
  funext p
  rw [jointDensity_eq]
  unfold polynomialCost
  ring

/-- This fixed Fourier moment depends only on the chosen decay degree
and the coordinate, and never on the source or Mellin frequency. -/
def coordinateMoment (k : ℕ) (L : LogPlane →L[ℝ] ℝ) : ℝ :=
  ∫ ξ : LogPlane, frequencyEnvelope k ξ * (1 + |L ξ|) ^ k

theorem coordinateMoment_nonneg (k : ℕ) (L : LogPlane →L[ℝ] ℝ) :
    0 ≤ coordinateMoment k L :=
  integral_nonneg fun ξ => mul_nonneg (frequencyEnvelope_nonneg k ξ) (by positivity)

theorem coordinateMoment_bound (k : ℕ) (L : LogPlane →L[ℝ] ℝ) :
    coordinateMoment k L ≤ max 1 ‖L‖ ^ k * ∫ ξ : LogPlane, fourierEnvelope ξ := by
  have hb := polynomial_integral_bound L k 1 (by norm_num)
    (fun ξ => (1 + |L ξ|) ^ k) (fun ξ => by positivity) (fun ξ => by simp)
  simpa only [coordinateMoment, mul_one] using hb

/-- The actual product integral factors into the chosen Fourier
moment and the genuine second Mellin moment. -/
theorem joint_polynomial_integral_eq (s : ℝ) (k : ℕ) (B : ℝ)
    (L : LogPlane →L[ℝ] ℝ) :
    (∫ p : LogPlane × ℝ,
      SecondProductionIntegral.jointDensity s k p * polynomialCost k B L p
      ∂((volume : Measure LogPlane).prod (volume : Measure ℝ))) =
      B * coordinateMoment k L * moment (-(1 / 2 : ℝ)) s k := by
  calc
    _ = ∫ p : LogPlane × ℝ, B *
        ((frequencyEnvelope k p.1 * (1 + |L p.1|) ^ k) *
          ((1 + |p.2|) ^ k * ‖secondDensity (-(1 / 2 : ℝ)) s p.2‖))
          ∂((volume : Measure LogPlane).prod (volume : Measure ℝ)) := by
      apply integral_congr_ae
      filter_upwards [] with p
      rw [jointDensity_eq]
      unfold polynomialCost
      ring
    _ = _ := by
      rw [integral_const_mul, integral_prod_mul]
      unfold coordinateMoment moment
      ring

theorem mass_joint_polynomial_eq (s : ℝ) (k : ℕ) (B : ℝ)
    (L : LogPlane →L[ℝ] ℝ) :
    moment (-(1 / 2 : ℝ)) s 0 *
      (∫ p : LogPlane × ℝ,
        SecondProductionIntegral.jointDensity s k p * polynomialCost k B L p
        ∂((volume : Measure LogPlane).prod (volume : Measure ℝ))) =
      (B * coordinateMoment k L) * cauchyCost (-(1 / 2 : ℝ)) s k := by
  rw [joint_polynomial_integral_eq]
  unfold cauchyCost
  ring

theorem mass_joint_polynomial_bound (s : ℝ) (k : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (L : LogPlane →L[ℝ] ℝ) :
    moment (-(1 / 2 : ℝ)) s 0 *
      (∫ p : LogPlane × ℝ,
        SecondProductionIntegral.jointDensity s k p * polynomialCost k B L p
        ∂((volume : Measure LogPlane).prod (volume : Measure ℝ))) ≤
      (B * (max 1 ‖L‖ ^ k * ∫ ξ : LogPlane, fourierEnvelope ξ)) *
        cauchyCost (-(1 / 2 : ℝ)) s k := by
  rw [mass_joint_polynomial_eq]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (coordinateMoment_bound k L) hB)
    (cauchyCost_nonneg _ _ _)

/-- This also bounds the literal finite-seminorm integral. The source
proof uses the continuous majorant above, whose integrability is proved. -/
theorem actual_seminorm_integral_le (q : Finset (ℕ × ℕ))
    (s : ℝ) (k : ℕ) (B : ℝ) (L : LogPlane →L[ℝ] ℝ)
    (hb : ∀ p : LogPlane × ℝ,
      (q.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (FinalMellinTests.weightedTest 0 (p.2 + L p.1))) ^ 2 ≤
          polynomialCost k B L p) :
    (∫ p : LogPlane × ℝ, SecondProductionIntegral.jointDensity s k p *
      (q.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (FinalMellinTests.weightedTest 0 (p.2 + L p.1))) ^ 2
        ∂((volume : Measure LogPlane).prod (volume : Measure ℝ))) ≤
      B * coordinateMoment k L * moment (-(1 / 2 : ℝ)) s k := by
  rw [← joint_polynomial_integral_eq]
  apply integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun p =>
      mul_nonneg (SecondProductionIntegral.jointDensity_nonneg s k p) (sq_nonneg _))
    (joint_polynomial_integrable s k B L)
  exact Filter.Eventually.of_forall fun p => mul_le_mul_of_nonneg_left (hb p)
    (SecondProductionIntegral.jointDensity_nonneg s k p)

/-- The first Fourier coordinate has the sign dictated by the actual
conjugated source column. -/
def firstCoordinate (side : Bool) : LogPlane →L[ℝ] ℝ :=
  -(SecondParentProduction.coordinate side)

@[simp] theorem firstCoordinate_apply (side : Bool) (ξ : LogPlane) :
    firstCoordinate side ξ = FirstPositiveSource.signedCoordinate side ξ := by
  cases side <;> simp [firstCoordinate, FirstPositiveSource.signedCoordinate]

/-- Both first branches use one decay exponent and one finite original
test seminorm. The two actual signed coordinates enter only the fixed
constant, so neither branch chooses its constants after the source. -/
theorem exists_signed_nested_cost_bound (k : ℕ) :
    ∃ m : ℕ, ∃ q : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ (side : Bool) (W : SchwartzMap ℝ ℂ)
        (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2),
        (∫ t : ℝ, ‖MellinSeparation.density W hW t‖) *
          spectralAverage (MellinSeparation.density W hW) m
            (FirstPositiveSource.signedCoordinate side)
            (fun s => cauchyCost (-(1 / 2 : ℝ)) s k) ≤
          A * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 := by
  obtain ⟨m, q, C, hC, hb⟩ := two_pass_cauchyCost_bound (-(1 / 2 : ℝ)) k
  let Q : ℝ := (max 1 ‖firstCoordinate false‖ ^ m +
    max 1 ‖firstCoordinate true‖ ^ m) * ∫ ξ : LogPlane, fourierEnvelope ξ
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    exact mul_nonneg (by positivity) (integral_nonneg fourierEnvelope_nonneg)
  refine ⟨m, q, Q * C, mul_nonneg hQ hC, fun side W hW => ?_⟩
  have hside : max 1 ‖firstCoordinate side‖ ^ m *
      (∫ ξ : LogPlane, fourierEnvelope ξ) ≤ Q := by
    dsimp only [Q]
    apply mul_le_mul_of_nonneg_right _ (integral_nonneg fourierEnvelope_nonneg)
    cases side
    · exact le_add_of_nonneg_right (by positivity)
    · exact le_add_of_nonneg_left (by positivity)
  have hp := polynomial_integral_bound (firstCoordinate side) m
    (C * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2) (by positivity)
    (fun ξ => (∫ t : ℝ, ‖MellinSeparation.density W hW t‖) *
      (∫ t : ℝ, ‖MellinSeparation.density W hW t‖ *
        cauchyCost (-(1 / 2 : ℝ)) (t + firstCoordinate side ξ) k))
    (fun ξ => mul_nonneg (integral_nonneg fun _ => norm_nonneg _)
      (integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (cauchyCost_nonneg _ _ _)))
    (fun ξ => hb W hW (firstCoordinate side ξ))
  have he : (∫ t : ℝ, ‖MellinSeparation.density W hW t‖) *
      spectralAverage (MellinSeparation.density W hW) m
        (FirstPositiveSource.signedCoordinate side)
        (fun s => cauchyCost (-(1 / 2 : ℝ)) s k) =
      ∫ ξ : LogPlane, frequencyEnvelope m ξ *
        ((∫ t : ℝ, ‖MellinSeparation.density W hW t‖) *
          (∫ t : ℝ, ‖MellinSeparation.density W hW t‖ *
            cauchyCost (-(1 / 2 : ℝ)) (t + firstCoordinate side ξ) k)) := by
    unfold spectralAverage
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ξ
    simp only [firstCoordinate_apply]
    ring
  rw [he]
  exact hp.trans ((mul_le_mul_of_nonneg_right hside (by positivity)).trans_eq (by ring))

/-- A continuous majorant for the remaining first Mellin frequency. -/
def firstPolynomial (m : ℕ) (B s : ℝ) : ℝ := B * (1 + |s|) ^ m

theorem firstPolynomial_nonneg (m : ℕ) (B : ℝ) (hB : 0 ≤ B) (s : ℝ) :
    0 ≤ firstPolynomial m B s := mul_nonneg hB (by positivity)

theorem firstPolynomial_continuous (m : ℕ) (B : ℝ) :
    Continuous (firstPolynomial m B) := by unfold firstPolynomial; fun_prop

theorem firstPolynomial_add_le (m : ℕ) (B : ℝ) (hB : 0 ≤ B) (t v : ℝ) :
    firstPolynomial m B (t + v) ≤ B * (1 + |t|) ^ m * (1 + |v|) ^ m := by
  have hp : 1 + |t + v| ≤ (1 + |t|) * (1 + |v|) := by
    have ha := abs_add_le t v
    nlinarith [abs_nonneg t, abs_nonneg v, mul_nonneg (abs_nonneg t) (abs_nonneg v)]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hp m) hB).trans_eq
    (by rw [mul_pow]; ring)

/-- This specialization is measurable without requiring any parameter
regularity statement about the second Mellin density. -/
theorem exists_cauchy_polynomial_majorant (k : ℕ) :
    ∃ m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℝ,
      cauchyCost (-(1 / 2 : ℝ)) s k ≤ firstPolynomial m B s := by
  obtain ⟨m, B, hB, hb⟩ := cauchyCost_bound (-(1 / 2 : ℝ)) k
  refine ⟨m, B, hB, fun s => ?_⟩
  simpa only [firstPolynomial, add_zero, abs_zero, one_pow, mul_one]
    using hb s 0

theorem firstPolynomial_inner_integrable (ρ : SchwartzMap ℝ ℂ)
    (m : ℕ) (B : ℝ) (hB : 0 ≤ B) (v : ℝ) :
    Integrable (fun t : ℝ => ‖ρ t‖ * firstPolynomial m B (t + v)) := by
  apply ((MellinSeparation.moment_integrable ρ m).const_mul
    (B * (1 + |v|) ^ m)).mono_nonneg
  · exact (ρ.continuous.norm.mul
      ((firstPolynomial_continuous m B).comp (continuous_id.add continuous_const))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t =>
      mul_nonneg (norm_nonneg _) (firstPolynomial_nonneg m B hB _)
  · exact Filter.Eventually.of_forall fun t =>
      (mul_le_mul_of_nonneg_left (firstPolynomial_add_le m B hB t v)
        (norm_nonneg _)).trans_eq (by ring)

theorem firstPolynomial_inner_bound (ρ : SchwartzMap ℝ ℂ)
    (m : ℕ) (B : ℝ) (hB : 0 ≤ B) (v : ℝ) :
    (∫ t : ℝ, ‖ρ t‖ * firstPolynomial m B (t + v)) ≤
      (B * (∫ t : ℝ, (1 + |t|) ^ m * ‖ρ t‖)) * (1 + |v|) ^ m := by
  calc
    _ ≤ ∫ t : ℝ, (B * (1 + |v|) ^ m) * ((1 + |t|) ^ m * ‖ρ t‖) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun t =>
          mul_nonneg (norm_nonneg _) (firstPolynomial_nonneg m B hB _))
        ((MellinSeparation.moment_integrable ρ m).const_mul _)
      exact Filter.Eventually.of_forall fun t =>
        (mul_le_mul_of_nonneg_left (firstPolynomial_add_le m B hB t v)
          (norm_nonneg _)).trans_eq (by ring)
    _ = _ := by rw [integral_const_mul]; ring

theorem firstPolynomial_joint_integrable (ρ : SchwartzMap ℝ ℂ)
    (m : ℕ) (B : ℝ) (hB : 0 ≤ B) (L : LogPlane →L[ℝ] ℝ) :
    Integrable (fun p : LogPlane × ℝ =>
      frequencyEnvelope m p.1 * (‖ρ p.2‖ * firstPolynomial m B (p.2 + L p.1)))
      ((volume : Measure LogPlane).prod (volume : Measure ℝ)) := by
  have hi := ((weighted_coordinate_integrable L m).mul_prod
    (MellinSeparation.moment_integrable ρ m)).const_mul B
  apply hi.mono_nonneg
  · have hc : Continuous (fun p : LogPlane × ℝ =>
        frequencyEnvelope m p.1 * (‖ρ p.2‖ * firstPolynomial m B (p.2 + L p.1))) :=
      ((frequencyEnvelope_continuous m).comp continuous_fst).mul
        ((ρ.continuous.comp continuous_snd).norm.mul
          ((firstPolynomial_continuous m B).comp
            (continuous_snd.add (L.continuous.comp continuous_fst))))
    exact hc.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p =>
      mul_nonneg (frequencyEnvelope_nonneg m p.1)
        (mul_nonneg (norm_nonneg _) (firstPolynomial_nonneg m B hB _))
  · exact Filter.Eventually.of_forall fun p =>
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (firstPolynomial_add_le m B hB p.2 (L p.1))
          (norm_nonneg _)) (frequencyEnvelope_nonneg m p.1)).trans_eq (by ring)

/-- The two certificates used by `spectralAverage_le_add`: the
dominating production term has an integrable inner and outer integral. -/
theorem firstPolynomial_outer_integrable (ρ : SchwartzMap ℝ ℂ)
    (m : ℕ) (B : ℝ) (hB : 0 ≤ B) (L : LogPlane →L[ℝ] ℝ) :
    Integrable (fun ξ : LogPlane => frequencyEnvelope m ξ *
      ∫ t : ℝ, ‖ρ t‖ * firstPolynomial m B (t + L ξ)) := by
  have hi := (firstPolynomial_joint_integrable ρ m B hB L).integral_prod_left
  simpa only [integral_const_mul] using hi

theorem firstPolynomial_average_bound (ρ : SchwartzMap ℝ ℂ)
    (m : ℕ) (B : ℝ) (hB : 0 ≤ B) (L : LogPlane →L[ℝ] ℝ) :
    spectralAverage ρ m L (firstPolynomial m B) ≤
      B * coordinateMoment m L * (∫ t : ℝ, (1 + |t|) ^ m * ‖ρ t‖) := by
  unfold spectralAverage
  calc
    _ ≤ ∫ ξ : LogPlane,
        (B * (∫ t : ℝ, (1 + |t|) ^ m * ‖ρ t‖)) *
          (frequencyEnvelope m ξ * (1 + |L ξ|) ^ m) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun ξ =>
          mul_nonneg (frequencyEnvelope_nonneg m ξ)
            (integral_nonneg fun t => mul_nonneg (norm_nonneg _)
              (firstPolynomial_nonneg m B hB _)))
        ((weighted_coordinate_integrable L m).const_mul _)
      exact Filter.Eventually.of_forall fun ξ =>
        (mul_le_mul_of_nonneg_left (firstPolynomial_inner_bound ρ m B hB (L ξ))
          (frequencyEnvelope_nonneg m ξ)).trans_eq (by ring)
    _ = _ := by rw [integral_const_mul]; unfold coordinateMoment; ring

/-- After the original Cauchy mass, any chosen continuous first
polynomial has a fixed quadratic seminorm bound on the original test. -/
theorem exists_firstPolynomial_budget (m : ℕ) :
    ∃ q : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
        (B : ℝ) (hB : 0 ≤ B) (L : LogPlane →L[ℝ] ℝ),
        (∫ t : ℝ, ‖MellinSeparation.density W hW t‖) *
          spectralAverage (MellinSeparation.density W hW) m L (firstPolynomial m B) ≤
            A * B * coordinateMoment m L *
              (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 := by
  obtain ⟨q₀, A₀, hA₀, hb₀⟩ := MellinSeparation.density_moment_bound 0
  obtain ⟨q₁, A₁, hA₁, hb₁⟩ := MellinSeparation.density_moment_bound m
  refine ⟨q₀ ∪ q₁, A₀ * A₁, mul_nonneg hA₀ hA₁, fun W hW B hB L => ?_⟩
  let Q := (q₀ ∪ q₁).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have h₀ : (∫ t : ℝ, ‖MellinSeparation.density W hW t‖) ≤ A₀ * Q := by
    have hh : (∫ t : ℝ, ‖MellinSeparation.density W hW t‖) ≤
        A₀ * q₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by simpa using hb₀ W hW
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) W) hA₀)
  have h₁ : (∫ t : ℝ, (1 + |t|) ^ m * ‖MellinSeparation.density W hW t‖) ≤
      A₁ * Q := (hb₁ W hW).trans (mul_le_mul_of_nonneg_left
        (Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) W) hA₁)
  have hp := firstPolynomial_average_bound (MellinSeparation.density W hW) m B hB L
  have hn : 0 ≤ spectralAverage (MellinSeparation.density W hW) m L
      (firstPolynomial m B) := integral_nonneg fun ξ =>
    mul_nonneg (frequencyEnvelope_nonneg m ξ) (integral_nonneg fun t =>
      mul_nonneg (norm_nonneg _) (firstPolynomial_nonneg m B hB _))
  have hp' := hp.trans (mul_le_mul_of_nonneg_left h₁
    (mul_nonneg hB (coordinateMoment_nonneg m L)))
  exact (mul_le_mul h₀ hp' hn (mul_nonneg hA₀ (apply_nonneg _ _))).trans_eq (by
    dsimp only [Q]
    ring)

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeSkeleton.Moments.MOMInvStep

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {σ : Type*} [DecidableEq σ]

theorem cauchyMass_eq (T : FirstParentEnergy.Data K S (σ := σ))
    (J : Finset σ) (s : ℝ) :
    SecondProductionIntegral.cauchyMass K S T J s =
      (((T.columns.slots \ J).powerset.card : ℝ) * moment (-(1 / 2 : ℝ)) s 0) := by
  simp only [SecondProductionIntegral.cauchyMass, SecondMellinEnergy.mellinMass,
    actual_mellinDensity_eq, moment, pow_zero, one_mul]

theorem actual_cauchy_polynomial_eq (T : FirstParentEnergy.Data K S (σ := σ))
    (J : Finset σ) (s : ℝ) (k : ℕ) (B : ℝ) (L : LogPlane →L[ℝ] ℝ) :
    SecondProductionIntegral.cauchyMass K S T J s *
      (∫ p : LogPlane × ℝ,
        SecondProductionIntegral.jointDensity s k p * polynomialCost k B L p
        ∂((volume : Measure LogPlane).prod (volume : Measure ℝ))) =
      (((T.columns.slots \ J).powerset.card : ℝ) * B * coordinateMoment k L) *
        cauchyCost (-(1 / 2 : ℝ)) s k := by
  rw [cauchyMass_eq, joint_polynomial_integral_eq]
  unfold cauchyCost
  ring

/-- The remaining mask count is charged once, by the original slot
cap, independently of the source restriction and the original mask. -/
theorem remaining_masks_bound (T : FirstParentEnergy.Data K S (σ := σ))
    (slotCap : ℕ) (hcap : T.columns.slots.card ≤ slotCap) (J : Finset σ) :
    ((T.columns.slots \ J).powerset.card : ℝ) ≤ (2 : ℝ) ^ slotCap := by
  rw [Finset.card_powerset]
  norm_cast
  exact Nat.pow_le_pow_right (by omega)
    ((Finset.card_le_card Finset.sdiff_subset).trans hcap)

theorem actual_cauchy_polynomial_bound (T : FirstParentEnergy.Data K S (σ := σ))
    (slotCap : ℕ) (hcap : T.columns.slots.card ≤ slotCap) (J : Finset σ)
    (s : ℝ) (k : ℕ) (B : ℝ) (hB : 0 ≤ B) (L : LogPlane →L[ℝ] ℝ) :
    SecondProductionIntegral.cauchyMass K S T J s *
      (∫ p : LogPlane × ℝ,
        SecondProductionIntegral.jointDensity s k p * polynomialCost k B L p
        ∂((volume : Measure LogPlane).prod (volume : Measure ℝ))) ≤
      ((2 : ℝ) ^ slotCap * B * coordinateMoment k L) *
        cauchyCost (-(1 / 2 : ℝ)) s k := by
  rw [actual_cauchy_polynomial_eq]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (remaining_masks_bound K S T slotCap hcap J) hB)
      (coordinateMoment_nonneg k L)) (cauchyCost_nonneg _ _ _)

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondSpectralCost

end
