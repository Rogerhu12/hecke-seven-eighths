import HeckeGeneral.Analysis.PhysicalProbeData
import HeckeGeneral.Analysis.IdealSummability
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
Absolute convergence of the literal completed ideal theta series with its
logarithmic Gaussian profile. A cardinality bound for the actual finite Gauss
sum suffices; no calibration, reflection, KP realization or moment input is
used. The whole-index mask is retained, and the estimate is uniform in its
marks and the S-integer argument.

UNCOMPILED static candidate, 2026-10-12; native_runs=0, verified_increment=0.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualThetaAbsoluteDraft

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem exteriorNorm_pos (I : ExteriorIdeal K S) : 0 < exteriorNorm K S I :=
  idealNorm_pos K I.val

theorem one_le_exteriorNorm (I : ExteriorIdeal K S) : 1 ≤ exteriorNorm K S I :=
  one_le_idealNorm K I.val

theorem exteriorNorm_completedIdeal (c n : ExteriorIdeal K S) :
    exteriorNorm K S (completedIdeal K S c n) =
      exteriorNorm K S c * exteriorNorm K S n ^ 3 := by
  change ((c.val.val * (n.val.val * (n.val.val * n.val.val))).absNorm : ℝ) = _
  simp only [map_mul, Nat.cast_mul, exteriorNorm]
  ring

theorem norm_idealSymbol_le_one (I : ExteriorIdeal K S) (m : S.integer K) :
    ‖idealSymbol K S D I m‖ ≤ 1 :=
  norm_sIntegerSexticIdealEvaluation_le_one K S D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) m

/-- The finite quotient cardinality, rather than a Gauss norm identity,
controls the sum. This also covers the one-element quotient. -/
theorem norm_thetaGamma_two_le_sqrt (I : ExteriorIdeal K S) :
    ‖thetaGamma K S D I 2‖ ≤ Real.sqrt (exteriorNorm K S I) := by
  letI : Finite (ThetaQuotient K S I) :=
    finite_sIntegerSexticIdealQuotient K S I.val.val
      (nonZeroDivisors.coe_ne_zero I.val) I.property
  letI : Fintype (ThetaQuotient K S I) := Fintype.ofFinite _
  let χ : ThetaQuotient K S I → ℂ :=
    sIntegerSexticIdealQuotientFunction K S D.root6 D.primitive6 D.embedding
      I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
      (fun p hp => D.away_six p (I.property p hp))
  have hχ (x : ThetaQuotient K S I) : ‖χ x‖ ≤ 1 := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change ‖sIntegerSexticIdealQuotientFunction K S D.root6 D.primitive6 D.embedding
      I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
      (fun p hp => D.away_six p (I.property p hp)) (Ideal.Quotient.mk _ a)‖ ≤ 1
    rw [sIntegerSexticIdealQuotientFunction_mk]
    exact norm_sIntegerSexticIdealEvaluation_le_one K S D.root6 D.primitive6 D.embedding
      I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
      (fun p hp => D.away_six p (I.property p hp)) a
  have hcard : Fintype.card (ThetaQuotient K S I) = I.val.val.absNorm := by
    simpa only [Nat.card_eq_fintype_card] using
      natCard_sIntegerResidue K S I.val.val (sexticIdeal_coprime_S K S I.val.val I.property)
  have hsum : ‖∑ x : ThetaQuotient K S I,
      χ x ^ 2 * thetaPrincipalAddCharacter K S D I x‖ ≤ exteriorNorm K S I := by
    calc
      _ ≤ ∑ x : ThetaQuotient K S I,
          ‖χ x ^ 2 * thetaPrincipalAddCharacter K S D I x‖ := norm_sum_le _ _
      _ ≤ ∑ _x : ThetaQuotient K S I, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x _hx
        rw [norm_mul, norm_pow, AddChar.norm_apply, mul_one]
        exact pow_le_one₀ (norm_nonneg _) (hχ x)
      _ = exteriorNorm K S I := by simp [hcard, exteriorNorm]
  have hN := exteriorNorm_pos K S I
  have hs := Real.sqrt_pos.mpr hN
  change ‖(Real.sqrt (exteriorNorm K S I) : ℂ)⁻¹ *
      ∑ x : ThetaQuotient K S I, χ x ^ 2 * thetaPrincipalAddCharacter K S D I x‖ ≤ _
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ = ‖∑ x : ThetaQuotient K S I,
        χ x ^ 2 * thetaPrincipalAddCharacter K S D I x‖ /
          Real.sqrt (exteriorNorm K S I) := by ring
    _ ≤ Real.sqrt (exteriorNorm K S I) := by
      apply (div_le_iff₀ hs).mpr
      nlinarith [Real.sq_sqrt hN.le]

theorem norm_completedCoefficient_le_one (θ : HeckeCharacter K)
    (m : S.integer K) (c n : ExteriorIdeal K S) :
    ‖thetaGamma K S D c 2 /
        ((Real.sqrt (exteriorNorm K S c) : ℂ) * (exteriorNorm K S n : ℂ)) *
      heckeIdealCoefficient K θ (completedIdeal K S c n).val *
      idealSymbol K S D (completedIdeal K S c n) m‖ ≤ 1 := by
  have hc := exteriorNorm_pos K S c
  have hn := exteriorNorm_pos K S n
  have hn1 := one_le_exteriorNorm K S n
  have hs := Real.sqrt_pos.mpr hc
  have hden : ‖(Real.sqrt (exteriorNorm K S c) : ℂ) *
      (exteriorNorm K S n : ℂ)‖ =
      Real.sqrt (exteriorNorm K S c) * exteriorNorm K S n := by
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (Real.sqrt_nonneg _), Real.norm_of_nonneg hn.le]
  have hg : ‖thetaGamma K S D c 2 /
      ((Real.sqrt (exteriorNorm K S c) : ℂ) * (exteriorNorm K S n : ℂ))‖ ≤ 1 := by
    rw [norm_div, hden]
    apply (div_le_one (mul_pos hs hn)).mpr
    have hgamma := norm_thetaGamma_two_le_sqrt K S D c
    nlinarith
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (1 : ℝ) * 1 * 1 :=
      mul_le_mul (mul_le_mul hg (norm_heckeIdealCoefficient_le_one K θ _)
        (norm_nonneg _) zero_le_one)
        (norm_idealSymbol_le_one K S D _ m) (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

def gaussianTailConstant : ℝ := ‖logGaussianNormalization‖ * Real.exp 4

theorem gaussianTailConstant_nonneg : 0 ≤ gaussianTailConstant := by
  exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

/-- Complete the square in the logarithm; the constant is explicit. -/
theorem norm_logGaussianProfile_le_inv_sq {x : ℝ} (hx : 0 < x) :
    ‖logGaussianProfile x‖ ≤ gaussianTailConstant / x ^ 2 := by
  have hcast : -(Real.log x : ℂ) ^ 2 / 4 =
      ((-(Real.log x) ^ 2 / 4 : ℝ) : ℂ) := by push_cast; rfl
  have hnorm : ‖logGaussianProfile x‖ =
      ‖logGaussianNormalization‖ * Real.exp (-(Real.log x) ^ 2 / 4) := by
    simp only [logGaussianProfile, logarithmicGaussian, norm_mul, hcast,
      Complex.norm_exp, Complex.ofReal_re]
  have hexp : Real.exp (4 - 2 * Real.log x) = Real.exp 4 / x ^ 2 := by
    rw [Real.exp_sub, show 2 * Real.log x = (2 : ℕ) * Real.log x by norm_num,
      Real.exp_nat_mul, Real.exp_log hx]
  calc
    _ = ‖logGaussianNormalization‖ * Real.exp (-(Real.log x) ^ 2 / 4) := hnorm
    _ ≤ ‖logGaussianNormalization‖ * Real.exp (4 - 2 * Real.log x) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (Real.log x - 4)]
    _ = gaussianTailConstant / x ^ 2 := by rw [hexp]; unfold gaussianTailConstant; ring

theorem norm_logGaussianProfile_product_le (a b Z : ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hZ : 0 < Z) :
    ‖logGaussianProfile (a * b ^ 3 / Z)‖ ≤
      (gaussianTailConstant * Z ^ 2) * (a ^ 2)⁻¹ * (b ^ 2)⁻¹ := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hab : 0 < a * b := mul_pos ha0 hb0
  have hA : 0 < a * b ^ 3 := mul_pos ha0 (pow_pos hb0 _)
  have hbsq : 1 ≤ b ^ 2 := by nlinarith [sq_nonneg (b - 1)]
  have hb3 : b ≤ b ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbsq) hb0.le]
  have hle : a * b ≤ a * b ^ 3 := mul_le_mul_of_nonneg_left hb3 ha0.le
  have hsq : (a * b) ^ 2 ≤ (a * b ^ 3) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hab.le hA.le)]
  calc
    _ ≤ gaussianTailConstant / (a * b ^ 3 / Z) ^ 2 :=
      norm_logGaussianProfile_le_inv_sq (div_pos hA hZ)
    _ = (gaussianTailConstant * Z ^ 2) / (a * b ^ 3) ^ 2 := by
      rw [div_pow, div_div_eq_mul_div]
    _ ≤ (gaussianTailConstant * Z ^ 2) / (a * b) ^ 2 :=
      div_le_div_of_nonneg_left (mul_nonneg gaussianTailConstant_nonneg (sq_nonneg Z))
        (sq_pos_of_pos hab) hsq
    _ = (gaussianTailConstant * Z ^ 2) * (a ^ 2)⁻¹ * (b ^ 2)⁻¹ := by
      rw [mul_pow, div_eq_mul_inv, mul_inv]
      ring

theorem summable_exteriorNorm_inv_sq :
    Summable (fun I : ExteriorIdeal K S => (exteriorNorm K S I ^ 2)⁻¹) := by
  have h := (summable_nonzeroIdeal_norm_rpow K (σ := 2) (by norm_num)).subtype
    (fun I => ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → p ∉ S)
  have heq (I : ExteriorIdeal K S) :
      (I.val.val.absNorm : ℝ) ^ (-2 : ℝ) = (exteriorNorm K S I ^ 2)⁻¹ := by
    rw [Real.rpow_neg (Nat.cast_nonneg _) 2, Real.rpow_two]
    rfl
  simpa only [Function.comp_def, heq] using h

theorem norm_completedTerm_le_product (θ : HeckeCharacter K) (m : S.integer K)
    (r : ExteriorIdeal K S) (Q : Finset (ExteriorPrime K S))
    {Z : ℝ} (hZ : 0 < Z) (cn : ExteriorIdeal K S × ExteriorIdeal K S) :
    ‖completedTerm K S D θ m r Q logGaussianProfile Z cn‖ ≤
      (gaussianTailConstant * Z ^ 2) *
        (exteriorNorm K S cn.1 ^ 2)⁻¹ * (exteriorNorm K S cn.2 ^ 2)⁻¹ := by
  unfold completedTerm
  dsimp only
  split_ifs with hmask
  · rw [norm_mul]
    calc
      _ ≤ 1 * ‖logGaussianProfile
          (exteriorNorm K S (completedIdeal K S cn.1 cn.2) / Z)‖ :=
        mul_le_mul_of_nonneg_right (norm_completedCoefficient_le_one K S D θ m cn.1 cn.2)
          (norm_nonneg _)
      _ ≤ _ := by
        rw [one_mul, exteriorNorm_completedIdeal]
        exact norm_logGaussianProfile_product_le _ _ _
          (one_le_exteriorNorm K S cn.1) (one_le_exteriorNorm K S cn.2) hZ
  · rw [norm_zero]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg gaussianTailConstant_nonneg (sq_nonneg Z))
      (inv_nonneg.mpr (sq_nonneg _))) (inv_nonneg.mpr (sq_nonneg _))

/-- Absolute convergence for every actual argument, target and whole-index
mask. The majorant is the product of two convergent ideal Dirichlet series. -/
theorem absolutelySummable_completedTerm (θ : HeckeCharacter K) (m : S.integer K)
    (r : ExteriorIdeal K S) (Q : Finset (ExteriorPrime K S))
    {Z : ℝ} (hZ : 0 < Z) :
    Summable (fun cn => ‖completedTerm K S D θ m r Q logGaussianProfile Z cn‖) := by
  have h := summable_exteriorNorm_inv_sq K S
  have hp := h.mul_of_nonneg h (fun I => inv_nonneg.mpr (sq_nonneg _))
    (fun I => inv_nonneg.mpr (sq_nonneg _))
  have hmajor := hp.mul_left (gaussianTailConstant * Z ^ 2)
  apply Summable.of_nonneg_of_le (fun cn => norm_nonneg _)
    (norm_completedTerm_le_product K S D θ m r Q hZ)
  simpa only [mul_assoc] using hmajor

/-- The exact original ProbeIntegralInput.theta_absolute field, with no
convergence premise and no additional restriction on m or Q. -/
theorem actual_probeTheta_absolute (P : ProbeData K S) (ψ : HeckeCharacter K) :
    ∀ (m : S.integer K) (Q : Finset (ExteriorPrime K S)) (Z : ℝ),
      0 < Z → Summable (completedTerm K S P.arithmetic (thetaPeriod K S P ψ) m
        (primeSetIdeal K S ∅) Q logGaussianProfile Z) := by
  intro m Q Z hZ
  exact (absolutelySummable_completedTerm K S P.arithmetic (thetaPeriod K S P ψ)
    m (primeSetIdeal K S ∅) Q hZ).of_norm

end HeckeGeneral.ThetaSkeleton.Physical.ActualThetaAbsoluteDraft
