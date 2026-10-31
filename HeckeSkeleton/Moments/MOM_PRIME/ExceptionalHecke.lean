import HeckeSkeleton.Moments.MOM_PRIME.ExceptionalTerminal
import HeckeGeneral.Analysis.HeckeSeries

/-!
# The exceptional terminal for actual Hecke coefficients

This specializes the ideal-sum results to the repository's actual Hecke
coefficients, including the prescribed zero at ramified primes and at the
zero ideal. `heckeExceptionalSum_eq_finite_sum` identifies the original
sum with its exact bounded-norm finite sum and retains the common mask.

The principal residue is the actual Dedekind zeta residue. Its identification
with the density of `IdealVolumeInput` is an explicit analytic premise in
`hecke_exceptional_main`; this file does not manufacture that premise.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField HeckeGeneral.Characters HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckePort.CenteredMoment HeckePort.CenteredMomentVolume HeckePort.Moments.Twist
open DedekindZetaZeroFree.LargeSieve
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]

/-- The genuine Hecke coefficient, extended by zero to the zero ideal. -/
def heckeExceptionalCharacter (χ : HeckeCharacter K) : Ideal (𝓞 K) →* ℂ :=
  (idealCoefficientHom (primeCoefficient K χ)).toMonoidHom

@[simp] theorem heckeExceptionalCharacter_zero (χ : HeckeCharacter K) :
    heckeExceptionalCharacter K χ ⊥ = 0 :=
  idealCoefficient_zero (primeCoefficient K χ)

theorem norm_heckeExceptionalCharacter_le_one (χ : HeckeCharacter K) (I : Ideal (𝓞 K)) :
    ‖heckeExceptionalCharacter K χ I‖ ≤ 1 :=
  norm_idealCoefficient_le_one (primeCoefficient K χ) (norm_primeCoefficient_le_one K χ) I

/-- On nonzero ideals this is literally the coefficient of `heckeLSeries`. -/
@[simp] theorem heckeExceptionalCharacter_nonzero (χ : HeckeCharacter K)
    (I : NonzeroIdeal K) :
    heckeExceptionalCharacter K χ I.val = heckeIdealCoefficient K χ I := rfl

/-- The manuscript's unnormalized, norm-twisted sum on actual ideals. -/
def heckeExceptionalSum (χ : HeckeCharacter K) (R : Ideal (𝓞 K))
    (W : ℝ → ℂ) (t X : ℝ) : ℂ :=
  twistedMaskedSum (heckeExceptionalCharacter K χ) R W t X

/-- The exact finite sum; the support and common coprimality zeros survive
the reindex unchanged. This holds for every positive scale, including X < 1. -/
theorem heckeExceptionalSum_eq_finite_sum (χ : HeckeCharacter K)
    (R : Ideal (𝓞 K)) (W : ℝ → ℂ) (b t X : ℝ)
    (hX : 0 < X) (hs : Function.support W ⊆ Set.Iic b) :
    heckeExceptionalSum K χ R W t X =
      ∑ I ∈ boundedNormIdeals K (b * X),
        (if IsCoprime I R then (1 : ℂ) else 0) *
          (heckeExceptionalCharacter K χ I *
            (Ideal.absNorm I : ℂ) ^ (Complex.I * t) *
              W ((Ideal.absNorm I : ℝ) / X)) := by
  unfold heckeExceptionalSum twistedMaskedSum
  apply tsum_eq_sum
  intro I hI
  have hw : W ((Ideal.absNorm I : ℝ) / X) = 0 := by
    by_contra hW
    apply hI
    exact mem_boundedNormIdeals.mpr ((div_le_iff₀ hX).mp (hs hW))
  simp only [hw, mul_zero]

/-- Absolute counting for the genuine Hecke sum. -/
theorem heckeExceptionalSum_absolute (χ : HeckeCharacter K)
    (R : Ideal (𝓞 K)) (W : ℝ → ℂ) (b M t X : ℝ)
    (hb : 0 ≤ b) (hM : 0 ≤ M) (hX : 0 < X)
    (hbound : ∀ y, ‖W y‖ ≤ M) (hs : Function.support W ⊆ Set.Iic b) :
    ‖heckeExceptionalSum K χ R W t X‖ ≤
      (HeckePort.CenteredMomentCounting.idealCountConstant K * b * M) * X :=
  twistedMaskedSum_absolute_direct (heckeExceptionalCharacter K χ)
    (norm_heckeExceptionalCharacter_le_one K χ) (heckeExceptionalCharacter_zero K χ)
    R W b M t X hb hM hX hbound hs

/-- The prescribed coefficient for a norm-reduced background: the actual
Dedekind residue in the principal case and zero in the other branch.
Its analytic identification with the volume density is the explicit
`hdensity` premise of `hecke_exceptional_main`. -/
def heckeExceptionalPoleCoefficient (χ : HeckeCharacter K) : ℂ :=
  if χ = 1 then (dedekindZeta_residue K : ℂ) else 0

@[simp] theorem heckeExceptionalPoleCoefficient_of_nonprincipal
    (χ : HeckeCharacter K) (hχ : χ ≠ 1) :
    heckeExceptionalPoleCoefficient K χ = 0 := by
  simp [heckeExceptionalPoleCoefficient, hχ]

@[simp] theorem heckeExceptionalPoleCoefficient_principal :
    heckeExceptionalPoleCoefficient K 1 = (dedekindZeta_residue K : ℂ) := by
  simp [heckeExceptionalPoleCoefficient]

/-- The prescribed radical-dependent coefficient of Lemma 4.11. Its
identification as the main term is supplied by the volume-density premise. -/
def heckeExceptionalResidue (χ : HeckeCharacter K) (R : Ideal (𝓞 K)) : ℂ :=
  exceptionalResidue (heckeExceptionalCharacter K χ)
    (heckeExceptionalPoleCoefficient K χ) R

@[simp] theorem heckeExceptionalResidue_of_nonprincipal
    (χ : HeckeCharacter K) (hχ : χ ≠ 1) (R : Ideal (𝓞 K)) :
    heckeExceptionalResidue K χ R = 0 := by
  simp [heckeExceptionalResidue, heckeExceptionalPoleCoefficient_of_nonprincipal K χ hχ]

variable {K}

/-- The main term on actual Hecke coefficients, with the density-residue
identification exhibited as the precise remaining analytic premise. -/
theorem hecke_exceptional_main {ι : Type*} (χ : HeckeCharacter K)
    (V : IdealVolumeInput K (heckeExceptionalCharacter K χ))
    (F : ExceptionalProfiles V ι)
    (hdensity : ∀ i t, V.density (F.profile i t) =
      heckeExceptionalPoleCoefficient K χ * exceptionalProfileIntegral (F.weight i) t)
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal (𝓞 K), R ≠ ⊥ → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ i t X, 0 < X →
        ‖heckeExceptionalSum K χ R (F.weight i) t X -
          volumeTerm (heckeExceptionalResidue K χ R)
            (exceptionalProfileIntegral (F.weight i) t) t X‖ ≤
          C * Z ^ ε * F.seminorm i * (1 + ‖t‖) ^ F.order :=
  exceptional_main_of_volume (norm_heckeExceptionalCharacter_le_one K χ)
    (heckeExceptionalCharacter_zero K χ) F (heckeExceptionalPoleCoefficient K χ)
    hdensity ε B hε hB

/-- Under the explicit density identification, the nonprincipal branch
has no main term. -/
theorem hecke_exceptional_nonprincipal {ι : Type*} (χ : HeckeCharacter K)
    (hχ : χ ≠ 1) (V : IdealVolumeInput K (heckeExceptionalCharacter K χ))
    (F : ExceptionalProfiles V ι)
    (hdensity : ∀ i t, V.density (F.profile i t) =
      heckeExceptionalPoleCoefficient K χ * exceptionalProfileIntegral (F.weight i) t)
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal (𝓞 K), R ≠ ⊥ → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ i t X, 0 < X →
        ‖heckeExceptionalSum K χ R (F.weight i) t X‖ ≤
          C * Z ^ ε * F.seminorm i * (1 + ‖t‖) ^ F.order := by
  obtain ⟨C, hC, hmain⟩ := hecke_exceptional_main χ V F hdensity ε B hε hB
  refine ⟨C, hC, ?_⟩
  intro Z hZ R hR hnorm i t X hX
  simpa only [heckeExceptionalResidue_of_nonprincipal K χ hχ, volumeTerm,
    zero_mul, sub_zero] using hmain Z hZ R hR hnorm i t X hX

/-- Uniform normalized equal-product cancellation for a genuine Hecke
character. The analytic volume input stays explicit as required by the
parallel-task interface; the centered bound itself is proved. -/
theorem hecke_exceptional_equal_product {ι : Type*} (χ : HeckeCharacter K)
    (V : IdealVolumeInput K (heckeExceptionalCharacter K χ))
    (F : ExceptionalProfiles V ι) (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal (𝓞 K), R ≠ ⊥ → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ i j t X₁ X₂ Y₁ Y₂ T a, 0 ≤ a →
      Z ^ a ≤ X₁ → Z ^ a ≤ X₂ → Z ^ a ≤ Y₁ → Z ^ a ≤ Y₂ →
      X₁ * X₂ = T → Y₁ * Y₂ = T →
      ‖(Real.sqrt T : ℂ)⁻¹ *
        (heckeExceptionalSum K χ R (F.weight i) t X₁ *
            heckeExceptionalSum K χ R (F.weight j) t X₂ -
          heckeExceptionalSum K χ R (F.weight i) t Y₁ *
            heckeExceptionalSum K χ R (F.weight j) t Y₂)‖ ≤
        C * Z ^ ε * Real.sqrt T * Z ^ (-a) *
          (F.seminorm i + F.seminorm j) ^ 2 * (1 + ‖t‖) ^ F.order :=
  exceptional_equal_product_cancellation (norm_heckeExceptionalCharacter_le_one K χ)
    (heckeExceptionalCharacter_zero K χ) F ε B hε hB

end HeckeSkeleton.Moments.MOM_PRIME
