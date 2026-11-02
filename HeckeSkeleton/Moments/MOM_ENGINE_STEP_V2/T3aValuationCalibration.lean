import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3aValuations
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalPhaseCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalVolume

set_option autoImplicit false

/-!
# The complete exceptional single-ideal coefficient

The original active and residual characters are multiplied only on
their genuine common coprimality mask. The fixed prefix is arbitrary:
it need not itself belong to theta or be unramified. The resulting
coefficient is the full row character used by the exceptional test.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open CanonicalOriginalPhaseCalibration

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}

/-- All original deletions, including the complete residual ideal and
the sixth-power factor, as a single nonzero integral ideal. -/
def completePhaseMask (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (moving : Ideal (𝓞 K)) (root : A.Exterior)
    (oldMask : HeckeGeneral.Analysis.NonzeroIdeal K) : Ideal (𝓞 K) :=
  A.cS * u.val * moving * root.val * oldMask.val

theorem completePhaseMask_ne_zero (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (moving : Ideal (𝓞 K)) (hmoving : moving ≠ 0) (root : A.Exterior)
    (oldMask : HeckeGeneral.Analysis.NonzeroIdeal K) :
    completePhaseMask u moving root oldMask ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero A.cS_ne_zero
    (nonZeroDivisors.coe_ne_zero u)) hmoving) root.property.1)
    (nonZeroDivisors.coe_ne_zero oldMask)

theorem coprime_completePhaseMask_iff
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (moving : Ideal (𝓞 K))
    (root : A.Exterior) (oldMask J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    IsCoprime J.val (completePhaseMask u moving root oldMask) ↔
      phaseMask u moving root J ∧ IsCoprime J.val oldMask.val := by
  simp only [completePhaseMask, IsCoprime.mul_right_iff, phaseMask,
    outside_iff_coprime]
  tauto

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ih : A.Exterior} {h g : A.R} {factor : ℝ}

/-- Exact equality on each complete ideal, with all zero cases kept.
The original prefix may contain arbitrary finite moving characters. -/
theorem extracted_plain_coefficient
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS) (primes : ι → ExteriorPrime A)
    (m n : ι → ℕ) (pattern : ι → Bool)
    (row : ActualChildRow Ih h g factor)
    (hfactor : g = secondSixthRootGenerator C primes m n ^ 6 *
      secondActiveFrequencyGenerator C primes m n pattern)
    (background preχ : HeckeCharacter K)
    (oldMask J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    sourcePlainCoefficient (background * preχ) 1 (originalCoprimeMask oldMask) J *
        actualIdealResidue (A := A) (σ := σ) J.val (g * row.element) =
      (if IsCoprime J.val (completePhaseMask row.momentIdeal
          (secondOriginalMovingFactors P R C primes m n pattern).support.val
          (secondSixthRootIdeal primes m n) oldMask) then (1 : ℂ) else 0) *
        CanonicalExceptionalVolume.coefficient
          (background * (preχ *
            (secondOriginalMovingFactors P R C primes m n pattern).character *
            completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
              P R (row.sector P) row.momentIdeal)) J.val := by
  let D := secondOriginalMovingFactors P R C primes m n pattern
  let χu := completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
    P R (row.sector P) row.momentIdeal
  have hphase := extracted_residue_character P R hroot hemb C primes m n pattern
    row hfactor (row.sector P) rfl J
  simp only [sourcePlainCoefficient, coefficient_one, mul_one]
  rw [actualIdealResidue_frequency_mul, hphase, coprime_completePhaseMask_iff]
  change (heckeIdealCoefficient K (background * preχ) J *
      (if IsCoprime J.val oldMask.val then (1 : ℂ) else 0)) *
      (heckeIdealCoefficient K D.character J * heckeIdealCoefficient K χu J *
        (if phaseMask row.momentIdeal D.support.val (secondSixthRootIdeal primes m n) J
          then 1 else 0)) =
    (if phaseMask row.momentIdeal D.support.val (secondSixthRootIdeal primes m n) J ∧
        IsCoprime J.val oldMask.val then 1 else 0) *
      heckeIdealCoefficient K (background * (preχ * D.character * χu)) J
  by_cases hgood : phaseMask row.momentIdeal D.support.val
      (secondSixthRootIdeal primes m n) J ∧ IsCoprime J.val oldMask.val
  · have hmove : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ J.val →
        UnramifiedAt K D.character p := by
      intro p hp
      exact activeCharacter_unramified P R C primes m n pattern p (hgood.1.1 p hp).1
        (hgood.1.2.2.1.of_isCoprime_of_dvd_left hp)
    have hrow : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ J.val →
        UnramifiedAt K χu p := by
      intro p hp
      exact residualCharacter_unramified P R row p (hgood.1.1 p hp).1
        (hgood.1.2.1.of_isCoprime_of_dvd_left hp)
    rw [show background * (preχ * D.character * χu) =
      ((background * preχ) * D.character) * χu by ac_rfl,
      coefficient_mul_right_unramified _ _ J hrow,
      coefficient_mul_right_unramified _ _ J hmove]
    simp only [hgood, hgood.1, hgood.2, and_self, if_true, mul_one, one_mul]
    ring
  · by_cases hm : phaseMask row.momentIdeal D.support.val
        (secondSixthRootIdeal primes m n) J
    · have ho : ¬IsCoprime J.val oldMask.val := fun ho => hgood ⟨hm, ho⟩
      simp only [if_neg hgood, if_neg ho, if_pos hm, mul_zero, zero_mul]
    · simp only [if_neg hgood, if_neg hm, mul_zero, zero_mul]

/-- The actual negative frequency has exactly the same coefficient;
the original twelfth root has already proved its sign invariance. -/
theorem extracted_plain_coefficient_neg
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS) (primes : ι → ExteriorPrime A)
    (m n : ι → ℕ) (pattern : ι → Bool)
    (row : ActualChildRow Ih h g factor)
    (hfactor : g = secondSixthRootGenerator C primes m n ^ 6 *
      secondActiveFrequencyGenerator C primes m n pattern)
    (background preχ : HeckeCharacter K)
    (oldMask J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    sourcePlainCoefficient (background * preχ) 1 (originalCoprimeMask oldMask) J *
        actualIdealResidue (A := A) (σ := σ) J.val (-g * row.element) =
      (if IsCoprime J.val (completePhaseMask row.momentIdeal
          (secondOriginalMovingFactors P R C primes m n pattern).support.val
          (secondSixthRootIdeal primes m n) oldMask) then (1 : ℂ) else 0) *
        CanonicalExceptionalVolume.coefficient
          (background * (preχ *
            (secondOriginalMovingFactors P R C primes m n pattern).character *
            completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
              P R (row.sector P) row.momentIdeal)) J.val := by
  rw [neg_mul, residue_neg]
  exact extracted_plain_coefficient P R hroot hemb C primes m n pattern row hfactor
    background preχ oldMask J

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.extracted_plain_coefficient
