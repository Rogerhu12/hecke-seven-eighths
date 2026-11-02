import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPaidCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActualCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstLogMetadata

set_option linter.unusedSectionVars false

/-!
# The actual support of the paid literal source

The original effective moving support, the selected physical first
divisor, the first active radical, and the reduced pool factor pay the
entire new moving support.  The first phase's higher powers add no new
primes.  The chosen empty-mask unit is retained and has support norm one.

The passive deletion is deliberately absent from this remaining ideal:
`CanonicalLiteralPaidCharacters` transfers it to an independent finite
Mobius expansion.  In particular valuation six has no pool support cost.
No completed support window is an input to the actual four constructors.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open UniqueFactorizationMonoid HeckePort.IdealMobiusDivisorSum CommonSupportMass
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open CanonicalLiteralPhaseCalibration CanonicalLiteralActualCharacters
open CanonicalLiteralPaidCharacters

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

private theorem paid_primeSupport_mul (I J : Ideal (𝓞 K))
    (hI : I ≠ 0) (hJ : J ≠ 0) :
    primeSupport (I * J) = primeSupport I ∪ primeSupport J := by
  sorry

namespace OriginalMovingFactors

/-- Appending genuine factors only adds their displayed radical.  The
old remaining ideal is exteriorized once, exactly as in the old source. -/
theorem appendFactors_effectiveFullSupport_dvd
    (D E : OriginalMovingFactors A P Rchar)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ((D.appendFactors E).effectiveFullSupport remaining).val ∣
      (D.effectiveFullSupport remaining).val * E.support.val := by
  sorry

theorem appendFactors_effectiveFullSupport_norm_le
    (D E : OriginalMovingFactors A P Rchar)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    A.exteriorNorm ((D.appendFactors E).effectiveFullSupport remaining) ≤
      A.exteriorNorm (D.effectiveFullSupport remaining) * A.exteriorNorm E.support := by
  sorry

end OriginalMovingFactors

namespace CanonicalLiteralPaidSupport

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

/-- This uses the three actual singleton lists in their original order. -/
theorem moving_norm_le (F : FixedPhases A) (old : OriginalMovingFactors A P R)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    A.exteriorNorm ((F.moving P R old).effectiveFullSupport remaining) ≤
      ((A.exteriorNorm (old.effectiveFullSupport remaining) *
        A.exteriorNorm (F.firstMoving P R).support) *
        A.exteriorNorm (F.poolMoving P R).support) *
        A.exteriorNorm (F.unitMoving P R).support := by
  sorry

private theorem singleton_unit_norm (a : A.R)
    (ha : A.Generates (unitExterior A) a) :
    A.exteriorNorm
      (OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1).support = 1 := by
  sorry

section FirstPhase

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem powerProduct_radical_mul_dvd (p : ι → ExteriorPrime A)
    (hp : Function.Injective p) (e : ι → ℕ) (he : ∀ i, 0 < e i)
    (D : A.Exterior) :
    commonRadical (D.val * (primePowerProduct p e).val)
        (D.val * (primePowerProduct p e).val) ∣
      D.val * (primePowerProduct p (fun _ => 1)).val := by
  sorry

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces}
variable (C : A.GeneralArithmeticContext σ η hS)

theorem leftMoving_support_dvd (p : ι → ExteriorPrime A)
    (hp : Function.Injective p) (m n : ι → ℕ)
    (D : A.Exterior) (δ : A.R) (hδ : A.Generates D δ) :
    (CanonicalLiteralFirstPhase.leftMoving C P R p m n D δ hδ).support.val ∣
      D.val * (firstActiveIdeal p m n).val := by
  sorry

theorem rightMoving_support_dvd (p : ι → ExteriorPrime A)
    (hp : Function.Injective p) (m n : ι → ℕ)
    (D : A.Exterior) (δ : A.R) (hδ : A.Generates D δ) :
    (CanonicalLiteralFirstPhase.rightMoving C P R p m n D δ hδ).support.val ∣
      D.val * (firstActiveIdeal p m n).val := by
  sorry

theorem leftMoving_norm_le (p : ι → ExteriorPrime A)
    (hp : Function.Injective p) (m n : ι → ℕ)
    (D : A.Exterior) (δ : A.R) (hδ : A.Generates D δ) :
    A.exteriorNorm (CanonicalLiteralFirstPhase.leftMoving C P R p m n D δ hδ).support ≤
      A.exteriorNorm D * A.exteriorNorm (firstActiveIdeal p m n) := by
  sorry

theorem rightMoving_norm_le (p : ι → ExteriorPrime A)
    (hp : Function.Injective p) (m n : ι → ℕ)
    (D : A.Exterior) (δ : A.R) (hδ : A.Generates D δ) :
    A.exteriorNorm (CanonicalLiteralFirstPhase.rightMoving C P R p m n D δ hδ).support ≤
      A.exteriorNorm D * A.exteriorNorm (firstActiveIdeal p m n) := by
  sorry

end FirstPhase

section ActualBlocks

variable [IsPrincipalIdealRing A.R]
variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces}
variable (C : A.GeneralArithmeticContext σ η hS)
variable {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (b : FirstCommonCharacterBlock fullI fullJ DE)
variable (D : Finset (HeightOneSpectrum A.R))
variable (old : OriginalMovingFactors A P R)
variable (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)

/-- The actual selected divisor and the original active radical give
the whole first-phase window. The chosen generator is not changed. -/
theorem left_first_window (Z : ℝ) (hZ : 1 < Z) :
    A.exteriorNorm (CanonicalLiteralFirstPhase.leftMoving C P R b.primes
      b.leftMultiplicity b.rightMultiplicity (firstPhysicalDivisorIdeal (A := A) D)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
      (originalFrequencyIdeal_generates _
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).property)).support ≤
      Z ^ (idealLogLength Z (firstActiveRadical DE.1 DE.2) +
        idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val) := by
  sorry

theorem right_first_window (Z : ℝ) (hZ : 1 < Z) :
    A.exteriorNorm (CanonicalLiteralFirstPhase.rightMoving C P R b.primes
      b.leftMultiplicity b.rightMultiplicity (firstPhysicalDivisorIdeal (A := A) D)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
      (originalFrequencyIdeal_generates _
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).property)).support ≤
      Z ^ (idealLogLength Z (firstActiveRadical DE.1 DE.2) +
        idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val) := by
  sorry

private theorem unamplified_window (firstIdeal : A.Exterior) (a : A.R)
    (ha : A.Generates firstIdeal a) (Z q firstCost : ℝ) (hZ : 1 < Z)
    (hold : A.exteriorNorm (old.effectiveFullSupport remaining) ≤ Z ^ q)
    (hfirst : A.exteriorNorm
      (OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1).support ≤
      Z ^ firstCost) :
    A.exteriorNorm (((unamplifiedPhases firstIdeal a ha).moving P R old).effectiveFullSupport remaining) ≤ Z ^ (q + firstCost) := by
  sorry

private theorem reduced_window (firstIdeal : A.Exterior) (a : A.R)
    (ha : A.Generates firstIdeal a) (p : ExteriorPrime A) (e : AmplifierValuation)
    (Z q firstCost : ℝ) (hZ : 1 < Z)
    (hold : A.exteriorNorm (old.effectiveFullSupport remaining) ≤ Z ^ q)
    (hfirst : A.exteriorNorm
      (OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1).support ≤
      Z ^ firstCost) :
    A.exteriorNorm (((reducedPhases
      (amplifiedPhases C firstIdeal a ha p e.multiplicity) C p e).moving P R old).effectiveFullSupport remaining) ≤
      Z ^ (q + firstCost + (e.movingMultiplicity : ℝ) * idealLogLength Z p.val.asIdeal) := by
  sorry

/-- Direct and main, left side: only the original `q`, active `R`,
and selected physical `E` enter the actual paid support. -/
theorem unamplified_left (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed (CanonicalLiteralFirstPhase.leftElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (Z q : ℝ) (hZ : 1 < Z)
    (hold : A.exteriorNorm (old.effectiveFullSupport remaining) ≤ Z ^ q) :
    A.exteriorNorm (((unamplifiedPhases firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
      hfirst).moving P R old).effectiveFullSupport remaining) ≤
      Z ^ (q + idealLogLength Z (firstActiveRadical DE.1 DE.2) +
        idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val) := by
  sorry

theorem unamplified_right (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed (CanonicalLiteralFirstPhase.rightElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (Z q : ℝ) (hZ : 1 < Z)
    (hold : A.exteriorNorm (old.effectiveFullSupport remaining) ≤ Z ^ q) :
    A.exteriorNorm (((unamplifiedPhases firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
      hfirst).moving P R old).effectiveFullSupport remaining) ≤
      Z ^ (q + idealLogLength Z (firstActiveRadical DE.1 DE.2) +
        idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val) := by
  sorry

/-- Pool, left side: the exact reduced factor adds the original
`movingMultiplicity * logNorm p`.  Valuation six adds zero. -/
theorem reduced_amplified_left (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed (CanonicalLiteralFirstPhase.leftElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (p : ExteriorPrime A) (e : AmplifierValuation)
    (Z q : ℝ) (hZ : 1 < Z)
    (hold : A.exteriorNorm (old.effectiveFullSupport remaining) ≤ Z ^ q) :
    A.exteriorNorm (((reducedPhases (amplifiedPhases C firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
      hfirst p e.multiplicity) C p e).moving P R old).effectiveFullSupport remaining) ≤
      Z ^ (q + idealLogLength Z (firstActiveRadical DE.1 DE.2) +
        idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val +
        (e.movingMultiplicity : ℝ) * idealLogLength Z p.val.asIdeal) := by
  sorry

theorem reduced_amplified_right (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed (CanonicalLiteralFirstPhase.rightElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (p : ExteriorPrime A) (e : AmplifierValuation)
    (Z q : ℝ) (hZ : 1 < Z)
    (hold : A.exteriorNorm (old.effectiveFullSupport remaining) ≤ Z ^ q) :
    A.exteriorNorm (((reducedPhases (amplifiedPhases C firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
      hfirst p e.multiplicity) C p e).moving P R old).effectiveFullSupport remaining) ≤
      Z ^ (q + idealLogLength Z (firstActiveRadical DE.1 DE.2) +
        idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val +
        (e.movingMultiplicity : ℝ) * idealLogLength Z p.val.asIdeal) := by
  sorry

end ActualBlocks
end CanonicalLiteralPaidSupport
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalMovingFactors.appendFactors_effectiveFullSupport_dvd
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidSupport.leftMoving_support_dvd
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidSupport.rightMoving_support_dvd
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidSupport.unamplified_left
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidSupport.unamplified_right
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidSupport.reduced_amplified_left
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidSupport.reduced_amplified_right
