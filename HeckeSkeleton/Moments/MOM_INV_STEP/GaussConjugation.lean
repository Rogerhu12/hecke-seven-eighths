import HeckeSkeleton.Moments.MOM_INV_STEP.LocalSource
import HeckeSkeleton.Moments.MOM_INV_STEP.CoefficientCycle
import HeckeGeneral.Analysis.GlobalThetaData
import Mathlib.NumberTheory.GaussSum

/-!
# The actual fifth-digit Gauss coefficient

Complex conjugation reverses the additive phase. Reindexing the actual
finite sum by `x ↦ -x` leaves the explicit multiplicative factor χ(-1).
No assertion that this factor is one is used, including for the unit
conductor. The inverse coefficient cycle therefore retains it.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.GaussConjugation

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.Analysis
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

theorem pow_five_eq_conj (z : ℂ) (hz : z ^ 6 = 0 ∨ z ^ 6 = 1) :
    z ^ 5 = conj z := by
  rcases hz with hz | hz
  · have hz0 : z = 0 := (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hz
    simp only [hz0, zero_pow (by decide : (5 : ℕ) ≠ 0), map_zero]
  · have hnorm : ‖z‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one hz (by decide : (6 : ℕ) ≠ 0)
    have hmul : z ^ 5 * z = 1 := by simpa only [← pow_succ] using hz
    exact (eq_inv_of_mul_eq_one_left hmul).trans (Complex.inv_eq_conj hnorm)

/-- The conjugation formula for any actual sixth-root monoid row.
Zeros of the row are included in the proof. -/
theorem finite_gauss_five {R : Type*} [CommRing R] [Fintype R]
    (χ : R →* ℂ) (hχ : ∀ x, χ x ^ 6 = 0 ∨ χ x ^ 6 = 1)
    (ψ : AddChar R ℂ) :
    (∑ x : R, χ x ^ 5 * ψ x) =
      χ (-1) * conj (∑ x : R, χ x * ψ x) := by
  have hminus2 : χ (-1) ^ 2 = 1 := by
    rw [← map_pow]
    simp only [neg_one_sq, map_one]
  have hminus : χ (-1) * conj (χ (-1)) = 1 := by
    rw [Complex.mul_conj', Complex.norm_eq_one_of_pow_eq_one hminus2 (by decide)]
    norm_num
  have hneg (x : R) : χ (-x) = χ (-1) * χ x := by
    rw [show -x = (-1 : R) * x by ring, map_mul]
  calc
    _ = ∑ x : R, conj (χ x) * ψ x := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [pow_five_eq_conj (χ x) (hχ x)]
    _ = ∑ x : R, χ (-1) * conj (χ (-x)) * ψ x := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [hneg x, map_mul]
      calc
        _ = (χ (-1) * conj (χ (-1))) * conj (χ x) * ψ x := by
          rw [hminus, one_mul]
        _ = _ := by ring
    _ = ∑ x : R, χ (-1) * conj (χ x) * ψ (-x) := by
      exact Fintype.sum_bijective (fun x : R => -x) (Equiv.neg R).bijective _ _
        (fun x => by simp only [neg_neg])
    _ = _ := by
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [map_mul, ← AddChar.map_neg_eq_conj]
      ring

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- The literal ideal coefficient as a monoid homomorphism on its actual
finite quotient. This construction preserves its zero values. -/
def quotientRow (I : ExteriorIdeal K S) : ThetaQuotient K S I →* ℂ where
  toFun := sIntegerSexticIdealQuotientFunction K S D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp))
  map_one' := by
    simp only [sIntegerSexticIdealQuotientFunction, map_one, one_pow, Finset.prod_const_one]
  map_mul' := by
    intro a b
    simp only [sIntegerSexticIdealQuotientFunction, map_mul, mul_pow,
      Finset.prod_mul_distrib]

@[simp] theorem quotientRow_mk (I : ExteriorIdeal K S) (a : S.integer K) :
    quotientRow K S D I (Ideal.Quotient.mk _ a) = idealSymbol K S D I a :=
  sIntegerSexticIdealQuotientFunction_mk K S D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) a

theorem quotientRow_zero_or_one (I : ExteriorIdeal K S) (q : ThetaQuotient K S I) :
    quotientRow K S D I q ^ 6 = 0 ∨ quotientRow K S D I q ^ 6 = 1 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [quotientRow_mk]
  exact LocalSource.actualRow_zero_or_one K S D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) a

/-- The fifth digit is the conjugate first Gauss coefficient times the
actual χ(-1), with the same selected generator and normalization. -/
theorem thetaGamma_five (I : ExteriorIdeal K S) :
    thetaGamma K S D I 5 =
      idealSymbol K S D I (-1) * conj (thetaGamma K S D I 1) := by
  letI : Finite (ThetaQuotient K S I) :=
    finite_sIntegerSexticIdealQuotient K S I.val.val
      (nonZeroDivisors.coe_ne_zero I.val) I.property
  letI : Fintype (ThetaQuotient K S I) := Fintype.ofFinite _
  have hneg : quotientRow K S D I (-1) = idealSymbol K S D I (-1) := by
    simpa only [map_neg, map_one] using quotientRow_mk K S D I (-1)
  change (Real.sqrt (I.val.val.absNorm : ℝ) : ℂ)⁻¹ *
      (∑ q : ThetaQuotient K S I,
        quotientRow K S D I q ^ 5 * thetaPrincipalAddCharacter K S D I q) =
    idealSymbol K S D I (-1) * conj
      ((Real.sqrt (I.val.val.absNorm : ℝ) : ℂ)⁻¹ *
        ∑ q : ThetaQuotient K S I,
          quotientRow K S D I q ^ 1 * thetaPrincipalAddCharacter K S D I q)
  simp only [pow_one]
  rw [finite_gauss_five (quotientRow K S D I) (quotientRow_zero_or_one K S D I), hneg]
  simp only [map_mul, map_inv₀, Complex.conj_ofReal]
  ring

/-- The second calibration written with the actual fifth digit, with
its finite sign retained as part of the live background. -/
theorem second_cycle_five {Λ G : HeckeCharacter K}
    (hcal : ThetaCalibrationInput K S D Λ G)
    (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    (UniqueFactorizationMonoid.moebius I.val.val : ℂ) * thetaGamma K S D I 5 =
      idealSymbol K S D I (-1) * CoefficientCycle.canonicalCoefficient K S D Λ I *
        conj (heckeIdealCoefficient K G I.val) := by
  rw [thetaGamma_five]
  calc
    _ = idealSymbol K S D I (-1) *
        ((UniqueFactorizationMonoid.moebius I.val.val : ℂ) *
          conj (thetaGamma K S D I 1)) := by ring
    _ = _ := by rw [CoefficientCycle.second_cycle hcal I hI]; ring

end HeckeSkeleton.Moments.MOM_INV_STEP.GaussConjugation

end
