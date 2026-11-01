import HeckeSkeleton.Moments.MOM_PRIME.ExceptionalAnnularBounds
import HeckeSkeleton.Moments.MOM_PRIME.ExceptionalMomentBridge

/-!
# Actual masked exceptional asymptotics and equal-product cancellation

The all-scale annular asymptotic is produced by the actual Hecke
continuation.  Finite inclusion-exclusion preserves the common mask and
the exact norm phase.  Its residue is the actual pole coefficient times
the original divisor density.

The uniform error and the absolute ideal count also bound the residue
coefficient itself.  This avoids a second divisor loss: the final
equal-product estimate has one factor `Z ^ epsilon` and the same height
order as the unmasked analytic remainder.  All constants precede the two
annular tests, their supremum bounds, the common mask and all four scales.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField IsDedekindDomain Set
open UniqueFactorizationMonoid DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Analysis HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMoment HeckePort.CenteredMomentMask
open HeckePort.CenteredMomentCounting HeckePort.IdealMobiusDivisorSum
open HeckePort.Moments.Twist
open scoped Classical BigOperators

/-- The norm phase has no effect on the absolute size of a volume term. -/
theorem annular_volumeTerm_norm (c J : ℂ) (t X : ℝ) (hX : 0 < X) :
    ‖volumeTerm c J t X‖ = X * ‖c * J‖ := by
  have hfactor : volumeTerm c J t X =
      (X : ℂ) ^ (1 + Complex.I * t) * (c * J) := by
    unfold volumeTerm
    ring
  rw [hfactor, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp

/-- An all-scale bounded error and a linear absolute bound control the
actual phase-carrying main coefficient.  The error disappears from the
conclusion, so this step incurs no additional divisor or height loss. -/
theorem annular_volumeCoefficient_norm_le (S : ℝ → ℂ) (c J : ℂ)
    (t C E : ℝ) (hE : 0 ≤ E)
    (herror : ∀ X : ℝ, 0 < X → ‖S X - volumeTerm c J t X‖ ≤ E)
    (habsolute : ∀ X : ℝ, 0 < X → ‖S X‖ ≤ C * X) :
    ‖c * J‖ ≤ C := by
  apply norm_linear_coefficient_le
    (fun X => ((X : ℂ) ^ (Complex.I * t))⁻¹ * S X) (c * J) C E hE
  · intro X hX
    have hp : (X : ℂ) ^ (Complex.I * t) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
    have hmain : ((X : ℂ) ^ (Complex.I * t))⁻¹ * volumeTerm c J t X =
        (X : ℂ) * (c * J) := by
      have hv : volumeTerm c J t X =
          (X : ℂ) ^ (Complex.I * t) * ((X : ℂ) * (c * J)) := by
        rw [volumeTerm, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hX.ne'),
          Complex.cpow_one]
        ring
      rw [hv, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]
    have heq : ((X : ℂ) ^ (Complex.I * t))⁻¹ * S X - (X : ℂ) * (c * J) =
        ((X : ℂ) ^ (Complex.I * t))⁻¹ * (S X - volumeTerm c J t X) := by
      rw [mul_sub, hmain]
    rw [heq, norm_mul, norm_inv, norm_real_imaginary_power X t hX, inv_one, one_mul]
    exact herror X hX
  · intro X hX
    rw [norm_mul, norm_inv, norm_real_imaginary_power X t hX, inv_one, one_mul]
    exact habsolute X hX

/-- A profile size containing both the analytic Euler remainder and the
absolute-counting size of the original compact annulus. -/
def annularTerminalSize (V : SmoothAnnularTest) (n : ℕ) (M : ℝ) : ℝ :=
  annularErrorSeminorm V n + V.upper * M

theorem annularTerminalSize_nonneg (V : SmoothAnnularTest) (n : ℕ)
    {M : ℝ} (hM : 0 ≤ M) : 0 ≤ annularTerminalSize V n M :=
  add_nonneg (annularErrorSeminorm_nonneg V n)
    (mul_nonneg (V.lower_pos.le.trans V.upper_ge) hM)

theorem annularErrorSeminorm_le_terminalSize (V : SmoothAnnularTest) (n : ℕ)
    {M : ℝ} (hM : 0 ≤ M) : annularErrorSeminorm V n ≤ annularTerminalSize V n M :=
  le_add_of_nonneg_right (mul_nonneg (V.lower_pos.le.trans V.upper_ge) hM)

theorem annular_supMass_le_terminalSize (V : SmoothAnnularTest) (n : ℕ) (M : ℝ) :
    V.upper * M ≤ annularTerminalSize V n M :=
  le_add_of_nonneg_left (annularErrorSeminorm_nonneg V n)

/-- A fixed annulus turns both inputs of the terminal size into the
literal Euler test seminorm, with a scalar independent of the test. -/
theorem annularTerminalSize_le_testSeminorm (V : SmoothAnnularTest)
    (n J : ℕ) (b : ℝ) (hJ : n + 2 ≤ J) (hb : V.upper ≤ b) :
    annularTerminalSize V n
        (8 * annularContourMass * testSeminorm V.toFun J 0) ≤
      (2 + 8 * annularContourMass * b) * testSeminorm V.toFun J 0 := by
  have hseminorm : 0 ≤ testSeminorm V.toFun J 0 :=
    (HeckeSkeleton.ThetaKernel.Iint_nonneg V 0 0).trans
      (HeckeSkeleton.ThetaKernel.Iint_right_le V 0 J (Nat.zero_le J) 0)
  have hM : 0 ≤ 8 * annularContourMass * testSeminorm V.toFun J 0 :=
    mul_nonneg (mul_nonneg (by norm_num) annularContourMass_nonneg) hseminorm
  calc
    _ ≤ 2 * testSeminorm V.toFun J 0 +
        b * (8 * annularContourMass * testSeminorm V.toFun J 0) :=
      add_le_add (annularErrorSeminorm_le_testSeminorm V n J hJ)
        (mul_le_mul_of_nonneg_right hb hM)
    _ = _ := by ring

variable (K : Type) [Field K] [NumberField K]

/-- The actual continuation supplies the masked asymptotic for every
positive scale, including `X / N(D) < 1`.  Only the literal divisor count
is lost; the main term is the exact original masked residue. -/
theorem exists_actualMaskedExceptional_card_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (hχ : ExceptionalNormReduced K χ) :
    ∃ (n : ℕ) (D : ℝ), 0 < D ∧
      ∀ (R : Ideal (𝓞 K)), R ≠ ⊥ → ∀ (V : SmoothAnnularTest) (t X : ℝ), 0 < X →
        ‖heckeExceptionalSum K χ R V.toFun t X -
          volumeTerm (heckeExceptionalResidue K χ R)
            (exceptionalProfileIntegral V.toFun t) t X‖ ≤
          ((idealDivisors R).card : ℝ) *
            (D * annularErrorSeminorm V n * (1 + |t|) ^ n) := by
  obtain ⟨n, D, hD, hunmasked⟩ := exists_actualUnmaskedExceptional_bound K hcomplex χ hχ
  refine ⟨n, D, hD, ?_⟩
  intro R hR V t X hX
  let L : ℝ → ℂ := fun Y => ∑' I : Ideal (𝓞 K), heckeExceptionalCharacter K χ I *
    (Ideal.absNorm I : ℂ) ^ (Complex.I * t) * V.toFun ((Ideal.absNorm I : ℝ) / Y)
  let coeff : Ideal (𝓞 K) → ℂ := fun A =>
    (moebius A : ℂ) * heckeExceptionalCharacter K χ A *
      (Ideal.absNorm A : ℂ) ^ (Complex.I * t)
  let main : ℝ → ℂ := fun Y => volumeTerm (heckeExceptionalPoleCoefficient K χ)
    (exceptionalProfileIntegral V.toFun t) t Y
  have hn (A : Ideal (𝓞 K)) (hA : A ∈ idealDivisors R) :
      0 < (Ideal.absNorm A : ℝ) := by
    have hA0 : A ≠ ⊥ := ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hA)
    exact_mod_cast Nat.pos_of_ne_zero
      (fun hz => hA0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hcoeff (A : Ideal (𝓞 K)) (hA : A ∈ idealDivisors R) : ‖coeff A‖ ≤ 1 := by
    have hp : ‖(Ideal.absNorm A : ℂ) ^ (Complex.I * t)‖ = 1 := by
      simpa only [Complex.ofReal_natCast] using
        norm_real_imaginary_power (Ideal.absNorm A : ℝ) t (hn A hA)
    dsimp only [coeff]
    rw [norm_mul, hp, mul_one, norm_mul]
    exact (mul_le_mul (norm_ideal_moebius_le_one A)
      (norm_heckeExceptionalCharacter_le_one K χ A)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have herror (A : Ideal (𝓞 K)) (hA : A ∈ idealDivisors R) :
      ‖L (X / Ideal.absNorm A) - main (X / Ideal.absNorm A)‖ ≤
        D * annularErrorSeminorm V n * (1 + |t|) ^ n :=
    hunmasked V t (X / Ideal.absNorm A) (div_pos hX (hn A hA))
  have heq : heckeExceptionalSum K χ R V.toFun t X -
        volumeTerm (heckeExceptionalResidue K χ R)
          (exceptionalProfileIntegral V.toFun t) t X =
      ∑ A ∈ idealDivisors R, coeff A * (L (X / Ideal.absNorm A) - main (X / Ideal.absNorm A)) := by
    change twistedMaskedSum (heckeExceptionalCharacter K χ) R V.toFun t X -
      volumeTerm (exceptionalResidue (heckeExceptionalCharacter K χ)
        (heckeExceptionalPoleCoefficient K χ) R)
        (exceptionalProfileIntegral V.toFun t) t X = _
    rw [twisted_mask_deletion (heckeExceptionalCharacter K χ) R hR V.toFun V.upper t X hX
      (fun _ hy => (V.support hy).2),
      ← exceptional_residue_extraction (heckeExceptionalCharacter K χ) R hR
        (heckeExceptionalPoleCoefficient K χ) (exceptionalProfileIntegral V.toFun t) t X hX.le,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro A _
    dsimp only [coeff, L, main]
    ring
  rw [heq]
  calc
    _ ≤ ∑ A ∈ idealDivisors R,
        ‖coeff A * (L (X / Ideal.absNorm A) - main (X / Ideal.absNorm A))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _A ∈ idealDivisors R,
        D * annularErrorSeminorm V n * (1 + |t|) ^ n := by
      apply Finset.sum_le_sum
      intro A hA
      rw [norm_mul]
      exact (mul_le_mul (hcoeff A hA) (herror A hA)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

/-- Polynomially bounded masks have the manuscript's one `Z^epsilon`
loss.  The analytic order and scalar are fixed before all tests and phases. -/
theorem exists_actualMaskedExceptional_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (hχ : ExceptionalNormReduced K χ)
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ (n : ℕ) (C : ℝ), 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal (𝓞 K), R ≠ ⊥ → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ (V : SmoothAnnularTest) (t X : ℝ), 0 < X →
        ‖heckeExceptionalSum K χ R V.toFun t X -
          volumeTerm (heckeExceptionalResidue K χ R)
            (exceptionalProfileIntegral V.toFun t) t X‖ ≤
          C * Z ^ ε * annularErrorSeminorm V n * (1 + |t|) ^ n := by
  obtain ⟨n, D, hD, herror⟩ := exists_actualMaskedExceptional_card_bound K hcomplex χ hχ
  obtain ⟨A, hA, hdiv⟩ := polynomial_mask_divisor_bound (K := K) ε B hε hB
  refine ⟨n, A * D, mul_pos hA hD, ?_⟩
  intro Z hZ R hR hnorm V t X hX
  calc
    _ ≤ ((idealDivisors R).card : ℝ) *
        (D * annularErrorSeminorm V n * (1 + |t|) ^ n) := herror R hR V t X hX
    _ ≤ (A * Z ^ ε) * (D * annularErrorSeminorm V n * (1 + |t|) ^ n) :=
      mul_le_mul_of_nonneg_right (hdiv Z hZ R hR hnorm)
        (mul_nonneg (mul_nonneg hD.le (annularErrorSeminorm_nonneg V n)) (by positivity))
    _ = _ := by ring

/-- The genuine masked residue coefficient is bounded by absolute ideal
counting, with no divisor or height factor.  Its all-scale approximation
is derived above from the actual continuation. -/
theorem actualAnnularExceptional_volumeCoefficient_norm_le
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (hχ : ExceptionalNormReduced K χ)
    (R : Ideal (𝓞 K)) (hR : R ≠ ⊥) (V : SmoothAnnularTest)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ y, ‖V.toFun y‖ ≤ M) (t : ℝ) :
    ‖heckeExceptionalResidue K χ R * exceptionalProfileIntegral V.toFun t‖ ≤
      idealCountConstant K * V.upper * M := by
  obtain ⟨n, D, hD, herror⟩ := exists_actualMaskedExceptional_card_bound K hcomplex χ hχ
  let E := ((idealDivisors R).card : ℝ) *
    (D * annularErrorSeminorm V n * (1 + |t|) ^ n)
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg hD.le (annularErrorSeminorm_nonneg V n)) (by positivity))
  exact annular_volumeCoefficient_norm_le
    (fun X => heckeExceptionalSum K χ R V.toFun t X)
    (heckeExceptionalResidue K χ R) (exceptionalProfileIntegral V.toFun t)
    t (idealCountConstant K * V.upper * M) E hE
    (fun X hX => herror R hR V t X hX)
    (fun X hX => heckeExceptionalSum_absolute K χ R V.toFun V.upper M t X
      (V.lower_pos.le.trans V.upper_ge) hM hX hbound (fun _ hy => (V.support hy).2))

/-- Lemma 4.11 for the actual masked Hecke sums, with its genuine
same-mask, same-phase equal-product cancellation.  The constants are
chosen before the annular tests and their pointwise supremum bounds.
No ideal-volume input or asymptotic estimate is a hypothesis. -/
theorem exists_actualAnnularExceptional_equal_product
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (hχ : ExceptionalNormReduced K χ)
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ (n : ℕ) (C : ℝ), 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal (𝓞 K), R ≠ ⊥ → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ (V₁ V₂ : SmoothAnnularTest) (M₁ M₂ : ℝ), 0 ≤ M₁ → 0 ≤ M₂ →
      (∀ y, ‖V₁.toFun y‖ ≤ M₁) → (∀ y, ‖V₂.toFun y‖ ≤ M₂) →
      ∀ (t X₁ X₂ Y₁ Y₂ T a : ℝ), 0 ≤ a →
      Z ^ a ≤ X₁ → Z ^ a ≤ X₂ → Z ^ a ≤ Y₁ → Z ^ a ≤ Y₂ →
      X₁ * X₂ = T → Y₁ * Y₂ = T →
      ‖(Real.sqrt T : ℂ)⁻¹ *
        (heckeExceptionalSum K χ R V₁.toFun t X₁ *
            heckeExceptionalSum K χ R V₂.toFun t X₂ -
          heckeExceptionalSum K χ R V₁.toFun t Y₁ *
            heckeExceptionalSum K χ R V₂.toFun t Y₂)‖ ≤
        C * Z ^ ε * Real.sqrt T * Z ^ (-a) *
          (annularTerminalSize V₁ n M₁ + annularTerminalSize V₂ n M₂) ^ 2 *
            (1 + ‖t‖) ^ n := by
  obtain ⟨n, D, hD, herror⟩ := exists_actualMaskedExceptional_bound K hcomplex χ hχ ε B hε hB
  let C₀ := idealCountConstant K
  have hC₀ : 0 ≤ C₀ := zero_le_one.trans (one_le_idealCountConstant K)
  let C := 1 + 4 * D * C₀
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨n, C, hC, ?_⟩
  intro Z hZ R hR hnorm V₁ V₂ M₁ M₂ hM₁ hM₂ hsup₁ hsup₂
    t X₁ X₂ Y₁ Y₂ T a _ha hX₁ hX₂ hY₁ hY₂ hpX hpY
  simp only [Real.norm_eq_abs]
  let P := annularTerminalSize V₁ n M₁ + annularTerminalSize V₂ n M₂
  let E := D * Z ^ ε * P * (1 + |t|) ^ n
  let cR := heckeExceptionalResidue K χ R
  let J₁ := exceptionalProfileIntegral V₁.toFun t
  let J₂ := exceptionalProfileIntegral V₂.toFun t
  let m₁ := fun X => volumeTerm cR J₁ t X
  let m₂ := fun X => volumeTerm cR J₂ t X
  have hP₁ : 0 ≤ annularTerminalSize V₁ n M₁ := annularTerminalSize_nonneg V₁ n hM₁
  have hP₂ : 0 ≤ annularTerminalSize V₂ n M₂ := annularTerminalSize_nonneg V₂ n hM₂
  have hP : 0 ≤ P := add_nonneg hP₁ hP₂
  have hsize₁ : annularTerminalSize V₁ n M₁ ≤ P := le_add_of_nonneg_right hP₂
  have hsize₂ : annularTerminalSize V₂ n M₂ ≤ P := le_add_of_nonneg_left hP₁
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hz : 0 ≤ Z ^ ε := Real.rpow_nonneg hZ0.le _
  have ht : 0 ≤ (1 + |t|) ^ n := by positivity
  have hE : 0 ≤ E := mul_nonneg (mul_nonneg (mul_nonneg hD.le hz) hP) ht
  have hL : 0 < Z ^ a := Real.rpow_pos_of_pos hZ0 _
  have hT : 0 < T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have he₁ (X : ℝ) (hX : Z ^ a ≤ X) :
      ‖heckeExceptionalSum K χ R V₁.toFun t X - m₁ X‖ ≤ E := by
    have hs := (annularErrorSeminorm_le_terminalSize V₁ n hM₁).trans hsize₁
    exact (herror Z hZ R hR hnorm V₁ t X (hL.trans_le hX)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs (mul_nonneg hD.le hz)) ht)
  have he₂ (X : ℝ) (hX : Z ^ a ≤ X) :
      ‖heckeExceptionalSum K χ R V₂.toFun t X - m₂ X‖ ≤ E := by
    have hs := (annularErrorSeminorm_le_terminalSize V₂ n hM₂).trans hsize₂
    exact (herror Z hZ R hR hnorm V₂ t X (hL.trans_le hX)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs (mul_nonneg hD.le hz)) ht)
  have hmass₁ : C₀ * V₁.upper * M₁ ≤ C₀ * P := by
    have hs := (annular_supMass_le_terminalSize V₁ n M₁).trans hsize₁
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs hC₀
  have hmass₂ : C₀ * V₂.upper * M₂ ≤ C₀ * P := by
    have hs := (annular_supMass_le_terminalSize V₂ n M₂).trans hsize₂
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs hC₀
  have hv₁ : ‖cR * J₁‖ ≤ C₀ * P :=
    (actualAnnularExceptional_volumeCoefficient_norm_le K hcomplex χ hχ R hR V₁
      M₁ hM₁ hsup₁ t).trans hmass₁
  have hmain₁ (X : ℝ) (hX : Z ^ a ≤ X) : ‖m₁ X‖ ≤ (C₀ * P) * X := by
    rw [annular_volumeTerm_norm cR J₁ t X (hL.trans_le hX)]
    exact (mul_le_mul_of_nonneg_left hv₁ (hL.le.trans hX)).trans_eq (mul_comm _ _)
  have habs₂ (X : ℝ) (hX : Z ^ a ≤ X) :
      ‖heckeExceptionalSum K χ R V₂.toFun t X‖ ≤ (C₀ * P) * X :=
    (heckeExceptionalSum_absolute K χ R V₂.toFun V₂.upper M₂ t X
      (V₂.lower_pos.le.trans V₂.upper_ge) hM₂ (hL.trans_le hX) hsup₂
      (fun _ hy => (V₂.support hy).2)).trans
        (mul_le_mul_of_nonneg_right hmass₂ (hL.le.trans hX))
  have hmain : m₁ X₁ * m₂ X₂ = m₁ Y₁ * m₂ Y₂ :=
    volume_products_eq cR J₁ J₂ t X₁ X₂ Y₁ Y₂
      (hL.le.trans hX₁) (hL.le.trans hX₂) (hL.le.trans hY₁) (hL.le.trans hY₂)
      (hpX.trans hpY.symm)
  have hraw := centered_saving_of_approx
    (heckeExceptionalSum K χ R V₁.toFun t X₁)
    (heckeExceptionalSum K χ R V₂.toFun t X₂)
    (heckeExceptionalSum K χ R V₁.toFun t Y₁)
    (heckeExceptionalSum K χ R V₂.toFun t Y₂)
    (m₁ X₁) (m₂ X₂) (m₁ Y₁) (m₂ Y₂)
    X₁ X₂ Y₁ Y₂ T (Z ^ a) (C₀ * P) E hmain (mul_nonneg hC₀ hP) hE
    (he₁ X₁ hX₁) (he₂ X₂ hX₂) (he₁ Y₁ hY₁) (he₂ Y₂ hY₂)
    (habs₂ X₂ hX₂) (hmain₁ X₁ hX₁) (habs₂ Y₂ hY₂) (hmain₁ Y₁ hY₁)
    hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hn := normalized_centered_saving _ T (Z ^ a) (C₀ * P) E hT hraw
  have heq : Real.sqrt T / Z ^ a = Real.sqrt T * Z ^ (-a) := by
    rw [Real.rpow_neg hZ0.le, div_eq_mul_inv]
  calc
    _ ≤ 4 * E * (C₀ * P) * (Real.sqrt T / Z ^ a) := hn
    _ = (4 * D * C₀) * Z ^ ε * Real.sqrt T * Z ^ (-a) * P ^ 2 * (1 + |t|) ^ n := by
      rw [heq]
      dsimp only [E]
      ring
    _ ≤ C * Z ^ ε * Real.sqrt T * Z ^ (-a) * P ^ 2 * (1 + |t|) ^ n := by
      apply mul_le_mul_of_nonneg_right _ ht
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg P)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ0.le _)
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg T)
      apply mul_le_mul_of_nonneg_right _ hz
      dsimp only [C]
      linarith

/-- The paper-facing equal-product estimate on one fixed annulus.  Its
Euler order, height order and scalar are fixed before either test, the
mask, the norm phase and every physical scale.  No supremum or volume
estimate is supplied by the caller. -/
theorem exists_actualAnnularExceptional_equal_product_seminorm
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (hχ : ExceptionalNormReduced K χ)
    (ε B b : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) (hb : 0 ≤ b) :
    ∃ (J N : ℕ) (C : ℝ), 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal (𝓞 K), R ≠ ⊥ → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ (V₁ V₂ : SmoothAnnularTest), V₁.upper ≤ b → V₂.upper ≤ b →
      ∀ (t X₁ X₂ Y₁ Y₂ T a : ℝ), 0 ≤ a →
      Z ^ a ≤ X₁ → Z ^ a ≤ X₂ → Z ^ a ≤ Y₁ → Z ^ a ≤ Y₂ →
      X₁ * X₂ = T → Y₁ * Y₂ = T →
      ‖(Real.sqrt T : ℂ)⁻¹ *
        (heckeExceptionalSum K χ R V₁.toFun t X₁ *
            heckeExceptionalSum K χ R V₂.toFun t X₂ -
          heckeExceptionalSum K χ R V₁.toFun t Y₁ *
            heckeExceptionalSum K χ R V₂.toFun t Y₂)‖ ≤
        C * Z ^ ε * Real.sqrt T * Z ^ (-a) *
          (testSeminorm V₁.toFun J 0 + testSeminorm V₂.toFun J 0) ^ 2 *
            (1 + ‖t‖) ^ N := by
  obtain ⟨n, D, hD, hbound⟩ :=
    exists_actualAnnularExceptional_equal_product K hcomplex χ hχ ε B hε hB
  let A : ℝ := 2 + 8 * annularContourMass * b
  have hmass : 0 ≤ annularContourMass := annularContourMass_nonneg
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨n + 2, n, D * A ^ 2, mul_pos hD (pow_pos hA 2), ?_⟩
  intro Z hZ R hR hnorm V₁ V₂ hu₁ hu₂
    t X₁ X₂ Y₁ Y₂ T a ha hX₁ hX₂ hY₁ hY₂ hpX hpY
  let p₁ : ℝ := testSeminorm V₁.toFun (n + 2) 0
  let p₂ : ℝ := testSeminorm V₂.toFun (n + 2) 0
  let M₁ : ℝ := 8 * annularContourMass * p₁
  let M₂ : ℝ := 8 * annularContourMass * p₂
  have hp₁ : 0 ≤ p₁ :=
    (HeckeSkeleton.ThetaKernel.Iint_nonneg V₁ 0 0).trans
      (HeckeSkeleton.ThetaKernel.Iint_right_le V₁ 0 (n + 2) (Nat.zero_le _) 0)
  have hp₂ : 0 ≤ p₂ :=
    (HeckeSkeleton.ThetaKernel.Iint_nonneg V₂ 0 0).trans
      (HeckeSkeleton.ThetaKernel.Iint_right_le V₂ 0 (n + 2) (Nat.zero_le _) 0)
  have hM₁ : 0 ≤ M₁ :=
    mul_nonneg (mul_nonneg (by norm_num) hmass) hp₁
  have hM₂ : 0 ≤ M₂ :=
    mul_nonneg (mul_nonneg (by norm_num) hmass) hp₂
  have hsup₁ : ∀ y, ‖V₁.toFun y‖ ≤ M₁ :=
    smoothAnnular_norm_le_testSeminorm V₁ (n + 2) (by omega)
  have hsup₂ : ∀ y, ‖V₂.toFun y‖ ≤ M₂ :=
    smoothAnnular_norm_le_testSeminorm V₂ (n + 2) (by omega)
  have hs₁ : annularTerminalSize V₁ n M₁ ≤ A * p₁ :=
    annularTerminalSize_le_testSeminorm V₁ n (n + 2) b le_rfl hu₁
  have hs₂ : annularTerminalSize V₂ n M₂ ≤ A * p₂ :=
    annularTerminalSize_le_testSeminorm V₂ n (n + 2) b le_rfl hu₂
  have hs : annularTerminalSize V₁ n M₁ + annularTerminalSize V₂ n M₂ ≤
      A * (p₁ + p₂) := by
    calc
      _ ≤ A * p₁ + A * p₂ := add_le_add hs₁ hs₂
      _ = _ := by ring
  have hsq := pow_le_pow_left₀
    (add_nonneg (annularTerminalSize_nonneg V₁ n hM₁)
      (annularTerminalSize_nonneg V₂ n hM₂)) hs 2
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hcoef : 0 ≤ D * Z ^ ε * Real.sqrt T * Z ^ (-a) :=
    mul_nonneg (mul_nonneg (mul_nonneg hD.le (Real.rpow_nonneg hZ0 _))
      (Real.sqrt_nonneg T)) (Real.rpow_nonneg hZ0 _)
  have ht : 0 ≤ (1 + ‖t‖) ^ n := by positivity
  calc
    _ ≤ D * Z ^ ε * Real.sqrt T * Z ^ (-a) *
        (annularTerminalSize V₁ n M₁ + annularTerminalSize V₂ n M₂) ^ 2 *
          (1 + ‖t‖) ^ n :=
      hbound Z hZ R hR hnorm V₁ V₂ M₁ M₂ hM₁ hM₂ hsup₁ hsup₂
        t X₁ X₂ Y₁ Y₂ T a ha hX₁ hX₂ hY₁ hY₂ hpX hpY
    _ ≤ D * Z ^ ε * Real.sqrt T * Z ^ (-a) *
        (A * (p₁ + p₂)) ^ 2 * (1 + ‖t‖) ^ n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hcoef) ht
    _ = _ := by dsimp only [p₁, p₂]; ring

/-- The absolute fallback keeps the actual characters, common mask and
norm phase and needs only positive scales and equal products. -/
theorem actualAnnularExceptional_fallback
    (χ : HeckeCharacter K) (R : Ideal (𝓞 K)) (V₁ V₂ : SmoothAnnularTest)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hsup₁ : ∀ y, ‖V₁.toFun y‖ ≤ M₁) (hsup₂ : ∀ y, ‖V₂.toFun y‖ ≤ M₂)
    (t X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hpX : X₁ * X₂ = T) (hpY : Y₁ * Y₂ = T) :
    ‖(Real.sqrt T : ℂ)⁻¹ *
      (heckeExceptionalSum K χ R V₁.toFun t X₁ * heckeExceptionalSum K χ R V₂.toFun t X₂ -
        heckeExceptionalSum K χ R V₁.toFun t Y₁ * heckeExceptionalSum K χ R V₂.toFun t Y₂)‖ ≤
      2 * (idealCountConstant K * (V₁.upper * M₁ + V₂.upper * M₂)) ^ 2 * Real.sqrt T :=
  exceptional_normalized_fallback (heckeExceptionalCharacter K χ)
    (norm_heckeExceptionalCharacter_le_one K χ) (heckeExceptionalCharacter_zero K χ)
    R V₁.toFun V₂.toFun V₁.upper V₂.upper M₁ M₂
    (V₁.lower_pos.le.trans V₁.upper_ge) (V₂.lower_pos.le.trans V₂.upper_ge) hM₁ hM₂
    hsup₁ hsup₂ (fun _ hy => (V₁.support hy).2) (fun _ hy => (V₂.support hy).2)
    t X₁ X₂ Y₁ Y₂ T hX₁ hX₂ hY₁ hY₂ hpX hpY

end HeckeSkeleton.Moments.MOM_PRIME

#print axioms HeckeSkeleton.Moments.MOM_PRIME.annular_volumeCoefficient_norm_le
#print axioms HeckeSkeleton.Moments.MOM_PRIME.exists_actualMaskedExceptional_card_bound
#print axioms HeckeSkeleton.Moments.MOM_PRIME.exists_actualMaskedExceptional_bound
#print axioms HeckeSkeleton.Moments.MOM_PRIME.actualAnnularExceptional_volumeCoefficient_norm_le
#print axioms HeckeSkeleton.Moments.MOM_PRIME.exists_actualAnnularExceptional_equal_product
#print axioms HeckeSkeleton.Moments.MOM_PRIME.exists_actualAnnularExceptional_equal_product_seminorm
#print axioms HeckeSkeleton.Moments.MOM_PRIME.actualAnnularExceptional_fallback
