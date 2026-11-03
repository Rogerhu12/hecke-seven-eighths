import ExpansionDetector.IdealTail
import ExpansionDetector.DetectorPower

/-! A zero of an ordinary entire ideal Dirichlet L-function creates an
actual finite terminal source. The hypotheses are initial Dirichlet series,
absolute convergence and an ordinary polynomial strip bound, and the
conclusion is a finite sum with explicitly defined coefficients. No
detector, product spike, or witness is assumed. -/
noncomputable section
namespace ExpansionDetector.IdealCutoff
open scoped NumberField Classical BigOperators nonZeroDivisors
variable {K : Type*} [Field K] [NumberField K]

lemma finite_ideal_zeta_two_le (S : Finset (Ideal (𝓞 K)))
    (hzeta : Summable (fun I : NonzeroIntegralIdeal (K := K) => nonzeroIdealNorm I ^ (-2 : ℝ))) :
    (∑ I ∈ S, (Ideal.absNorm I : ℝ) ^ (-2 : ℝ)) ≤
      ∑' I : NonzeroIntegralIdeal (K := K), nonzeroIdealNorm I ^ (-2 : ℝ) := by
  let f : Ideal (𝓞 K) → ℝ := fun I => (Ideal.absNorm I : ℝ) ^ (-2 : ℝ)
  have hsup : Function.support f ⊆ (Ideal (𝓞 K))⁰ := by
    intro I hI
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro heq
    subst I
    exact hI (by simp [f])
  have hsum : Summable f :=
    ((hasSum_subtype_iff_of_support_subset hsup).mp hzeta.hasSum).summable
  calc
    _ ≤ ∑' I : Ideal (𝓞 K), f I :=
      hsum.sum_le_tsum S (fun I _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := (tsum_subtype_eq_of_support_subset hsup).symm

lemma inverseIdealSet_norm (D : ℝ) (I : Ideal (𝓞 K)) (hI : I ∈ inverseIdealSet D) :
    1 ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ 2 * D := by
  have hm := (mem_inverseIdealSet D I).mp hI
  refine ⟨?_, hm.2⟩
  exact_mod_cast Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hm.1))

lemma inverseIdealCoefficient_norm_le_one
    (w : Ideal (𝓞 K) →*₀ ℂ) (hw : ∀ I, ‖w I‖ ≤ 1)
    (V : ℝ → ℂ) (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) (D : ℝ) (I : Ideal (𝓞 K)) :
    ‖inverseIdealCoefficient w V D I‖ ≤ 1 := by
  simp only [inverseIdealCoefficient, norm_mul]
  calc
    ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖ * ‖w I‖ *
        ‖V ((Ideal.absNorm I : ℝ) / D)‖ ≤ (1 * 1) * 1 := by
      apply mul_le_mul _ (hV _) (norm_nonneg _) (by norm_num)
      exact mul_le_mul (norm_ideal_moebius_le_one I) (hw I) (norm_nonneg _) zero_le_one
    _ = 1 := by ring

lemma terminal_scale_ratio (U : ℝ) (hU : 0 < U) :
    (U ^ (20 : ℕ)) ^ (70 : ℕ) / (U ^ (21 : ℕ)) ^ (67 : ℕ) = U ^ (-7 : ℝ) := by
  rw [← pow_mul, ← pow_mul]
  norm_num only [Nat.mul] 
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_sub hU]
  norm_num

lemma unit_smoothing_lower (U : ℝ) (hU : 2 ≤ U) (s : ℂ) :
    (1 / 2 : ℝ) ≤ ‖(1 : ℂ) ^ (-s) * (Real.exp (-(1 : ℝ) / U ^ 20) : ℂ)‖ := by
  have hU1 : 1 ≤ U := by linarith
  have hUp : 0 < U := by linarith
  have h20 : 2 ≤ U ^ (20 : ℕ) := by
    have hp := pow_le_pow_right₀ hU1 (by norm_num : (1 : ℕ) ≤ 20)
    rw [pow_one] at hp
    exact hU.trans hp
  have hi : 1 / U ^ (20 : ℕ) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (pow_pos hUp 20)).mpr
    linarith
  have he := Real.add_one_le_exp (-(1 : ℝ) / U ^ 20)
  rw [neg_div] at he
  simp only [Complex.one_cpow, one_mul, Complex.norm_of_nonneg (Real.exp_nonneg _)]
  rw [neg_div]
  linarith

/-- Uniform zero-to-finite-source theorem. The zero's real part need only
lie in [0.51,1], and the complete height budget must satisfy A*theta<=1.
The finite smoothing scales are Y=U^20 and H=U^21. -/
theorem actualIdeal_terminal_lower_of_zero
    (A θ α CL CZ : ℝ) (hA : 0 ≤ A) (hθ : 0 ≤ θ) (hα : α ≤ 2)
    (hCL : 0 ≤ CL) (hCZ : 0 ≤ CZ) (hbudget : A * θ ≤ 1)
    (hzeta₃ : Summable (fun I : NonzeroIntegralIdeal (K := K) => nonzeroIdealNorm I ^ (-3 / 2 : ℝ)))
    (hzeta₂ : Summable (fun I : NonzeroIntegralIdeal (K := K) => nonzeroIdealNorm I ^ (-2 : ℝ)))
    (hCZsum : (∑' I : NonzeroIntegralIdeal (K := K), nonzeroIdealNorm I ^ (-2 : ℝ)) ≤ CZ) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
      ∀ (w : Ideal (𝓞 K) →*₀ ℂ) (V T : ℝ → ℂ) (D : ℝ) (L : ℂ → ℂ) (ρ : ℂ),
      (∀ I, ‖w I‖ ≤ 1) →
      (∀ x : ℝ, ‖V x‖ ≤ 1) →
      (∀ x : ℝ, 0 ≤ x → ‖1 - V x‖ ≤ 1) →
      (∀ x : ℝ, 0 ≤ x → ‖1 - T x‖ ≤ 1) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1) →
      (∀ x : ℝ, 2 ≤ x → V x = 0) →
      (∀ x : ℝ, 2 ≤ x → T x = 0) →
      2 ≤ D → D ≤ U ^ (3 / 2 : ℝ) → Differentiable ℂ L →
      (∀ s : ℂ, 1 < s.re → L s = ∑' I : Ideal (𝓞 K), idealDirichletWeight w s I) →
      (∀ s : ℂ, 1 < s.re → Summable (fun I : Ideal (𝓞 K) => ‖idealDirichletWeight w s I‖)) →
      (∀ s : ℂ, 1 / 100 ≤ s.re → s.re ≤ 3 →
        ‖L s‖ ≤ CL * U ^ α * (2 + |s.im|) ^ A) →
      L ρ = 0 → 51 / 100 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ U ^ θ →
      (1 / 4 : ℝ) ≤ ‖∑ I ∈ terminalIdealSet (U ^ 21),
        terminalTerm w V T D (U ^ 21)
          (fun n => (n : ℂ) ^ (-ρ) * (Real.exp (-(n : ℝ) / U ^ 20) : ℂ)) I‖ := by
  obtain ⟨G, hG, hdet⟩ := ExpansionDetector.Analytic.gammaDetector_power_bound A hA
  obtain ⟨U₁, hU₁, hsmall₁⟩ := ExpansionDetector.Analytic.detector_uniform_small_power
    ((4 * G * CL * CZ) * 3 ^ A) 4 (1 / 8) (by norm_num) (by norm_num)
  obtain ⟨U₂, hU₂, hsmall₂⟩ := ExpansionDetector.Analytic.detector_uniform_small_power
    (((70 : ℕ).factorial : ℝ) * CZ) 4 (1 / 8) (by norm_num) (by norm_num)
  refine ⟨max U₁ U₂, hU₁.trans (le_max_left _ _), ?_⟩
  intro U hU w V T D L ρ hw hV hVc hTc hVsmall hTsmall hVzero hTzero hD hDU hL hseries habs hstrip hz hβ hβ1 hγ
  have hUlo : 2 ≤ U := hU₁.trans ((le_max_left _ _).trans hU)
  have hUone : 1 ≤ U := by linarith
  have hUp : 0 < U := by linarith
  have hDp : 0 < D := by linarith
  have hY : 0 < U ^ (20 : ℕ) := pow_pos hUp _
  have hH : 0 < U ^ (21 : ℕ) := pow_pos hUp _
  let kernel : ℕ → ℂ := fun n => (n : ℂ) ^ (-ρ) * (Real.exp (-(n : ℝ) / U ^ 20) : ℂ)
  obtain ⟨hsm, hmellin⟩ := actualIdeal_gamma_mellin_identity w hw V hV hVzero
    D (U ^ 20) hDp hY L hseries habs ρ (by linarith) hzeta₃
  obtain ⟨hrem, htail⟩ := actualIdeal_terminal_remainder_bound w hw V T hV hVc hTc hTsmall
    D (U ^ 20) (U ^ 21) hDp hY hH ρ (by linarith) 67 hzeta₂
  have htail' : ‖∑' I : Ideal (𝓞 K), terminalRemainder w V T D (U ^ 21) kernel I‖ ≤ (1 / 8 : ℝ) := by
    apply htail.trans
    calc
      _ = (((70 : ℕ).factorial : ℝ) * U ^ (-7 : ℝ)) *
          ∑' I : NonzeroIntegralIdeal (K := K), nonzeroIdealNorm I ^ (-2 : ℝ) := by
        change (((70 : ℕ).factorial : ℝ) * (U ^ (20 : ℕ)) ^ 70 / (U ^ (21 : ℕ)) ^ 67) * _ = _
        rw [mul_div_assoc, terminal_scale_ratio U hUp]
      _ ≤ (((70 : ℕ).factorial : ℝ) * U ^ (-7 : ℝ)) * CZ :=
        mul_le_mul_of_nonneg_left hCZsum (by positivity)
      _ ≤ (((70 : ℕ).factorial : ℝ) * CZ) * U ^ (-4 : ℝ) := by
        have hp := Real.rpow_le_rpow_of_exponent_le hUone (by norm_num : (-7 : ℝ) ≤ -4)
        have h := mul_le_mul_of_nonneg_left hp (show 0 ≤ ((70 : ℕ).factorial : ℝ) * CZ by positivity)
        nlinarith
      _ ≤ (1 / 8 : ℝ) := (hsmall₂ U ((le_max_right _ _).trans hU)).le
  have hdet' := hdet (inverseIdealSet D) (inverseIdealCoefficient w V D)
    (fun I => (Ideal.absNorm I : ℝ)) L ρ U D CL CZ α
    hUlo hDp.le hDU hCL hCZ hL hz hβ hβ1
    (fun I hI => inverseIdealSet_norm D I hI)
    (fun I _ => inverseIdealCoefficient_norm_le_one w hw V hV D I)
    ((finite_ideal_zeta_two_le (inverseIdealSet D) hzeta₂).trans hCZsum) hstrip
  have hsm' : ‖∑' I : Ideal (𝓞 K), smoothedTerm w V D kernel I‖ ≤ (1 / 8 : ℝ) := by
    rw [← hmellin]
    apply hdet'.trans
    apply (ExpansionDetector.Analytic.detector_height_power_four hUone hA hθ
      (by positivity : 0 ≤ 4 * G * CL * CZ) hγ hα hbudget).trans
    exact (hsmall₁ U ((le_max_left _ _).trans hU)).le
  apply finite_terminal_lower_of_summable w V T D (U ^ 21) hD hH hVsmall hVzero hTzero
    kernel hsm hrem (1 / 8) (1 / 8) (1 / 4) _ hsm' htail'
  have hu := unit_smoothing_lower U hUlo ρ
  simpa only [kernel, Nat.cast_one, show (1 / 4 : ℝ) + 1 / 8 + 1 / 8 = 1 / 2 by norm_num] using hu

end ExpansionDetector.IdealCutoff
