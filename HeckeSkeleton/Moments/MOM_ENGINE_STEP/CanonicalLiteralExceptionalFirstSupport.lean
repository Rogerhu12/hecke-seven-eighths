import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPaidSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveLabelMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCommonLabelConditions

set_option linter.unusedSectionVars false
set_option quotPrecheck false

/-!
# The original first deletion in the complete exceptional mask

The exceptional source keeps its original first deletion, including
primes whose phase is a sixth power.  Those primes need not belong to
the active first radical.  Their actual norm is bounded from the
original common-label witness and the original column window.

The pool case also keeps the original exponent `2 * n`.  Its displayed
support costs at most one copy of the actual pool prime, independently
of the exponent.  A second copy pays the original union deletion.
These costs enlarge only the fixed box used by the single-character
volume estimate; they do not change any child parameter or row count.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open UniqueFactorizationMonoid HeckePort.IdealMobiusDivisorSum CommonSupportMass
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
open HeckePort.Moments HeckePort.Moments.Support
open CanonicalLiteralPhaseCalibration CanonicalLiteralActualCharacters

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

private theorem exceptional_primeSupport_mul (I J : Ideal (𝓞 K))
    (hI : I ≠ 0) (hJ : J ≠ 0) :
    primeSupport (I * J) = primeSupport I ∪ primeSupport J := by
  sorry

namespace OriginalMovingFactors

/-- The full old support remains present when the original deletion
is multiplied into the remaining ideal.  Overlap needs no assumption. -/
theorem effectiveFullSupport_mul_dvd (D : OriginalMovingFactors A P R)
    (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (D.effectiveFullSupport (remaining * extra)).val ∣
      (D.effectiveFullSupport remaining).val * extra.val := by
  sorry

theorem effectiveFullSupport_mul_norm_le (D : OriginalMovingFactors A P R)
    (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) :
    A.exteriorNorm (D.effectiveFullSupport (remaining * extra)) ≤
      A.exteriorNorm (D.effectiveFullSupport remaining) * idealNorm K extra := by
  sorry

end OriginalMovingFactors

namespace CanonicalLiteralExceptionalFirstSupport

open CanonicalLiteralPassiveLabelMass

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

/-- A genuine common label supplies its original column witness. -/
theorem firstMask_window {α β : Type*}
    (left : Finset α) (right : Finset β)
    (I : α → A.Exterior) (J : β → A.Exterior)
    (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
    (hDE : DE ∈ commonSupportPool left right (fun i => (I i).val) (fun j => (J j).val))
    (Y : ℝ) (hI : ∀ i ∈ left, A.exteriorNorm (I i) ≤ Y) :
    idealNorm K (firstMask DE.1) ≤ Y := by
  sorry

theorem poolExtra_norm_le (D : Ideal (𝓞 K)) (p : ExteriorPrime A) :
    idealNorm K (poolExtra D p) ≤
      idealNorm K (firstMask D) * (Ideal.absNorm p.val.asIdeal : ℝ) := by
  sorry

variable [IsPrincipalIdealRing A.R]
variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces}
variable (C : A.GeneralArithmeticContext σ η hS)

/-- This bounds the literal displayed support of the original
amplifier generator, including exponent twelve. -/
theorem amplified_pool_support_dvd (first : A.Exterior) (a : A.R)
    (ha : A.Generates first a) (p : ExteriorPrime A) (n : ℕ) :
    ((amplifiedPhases C first a ha p n).poolMoving P R).support.val ∣ p.val.asIdeal := by
  sorry

theorem amplified_pool_norm_le (first : A.Exterior) (a : A.R)
    (ha : A.Generates first a) (p : ExteriorPrime A) (n : ℕ) :
    A.exteriorNorm ((amplifiedPhases C first a ha p n).poolMoving P R).support ≤
      (Ideal.absNorm p.val.asIdeal : ℝ) := by
  sorry

private theorem amplified_unit_norm (first : A.Exterior) (a : A.R)
    (ha : A.Generates first a) (p : ExteriorPrime A) (n : ℕ) :
    A.exteriorNorm ((amplifiedPhases C first a ha p n).unitMoving P R).support = 1 := by
  sorry

section ActualBlocks

variable {α β : Type*} {I : α → A.Exterior} {J : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (b : FirstCommonCharacterBlock I J DE)
variable (D : Finset (HeightOneSpectrum A.R))
variable (old : OriginalMovingFactors A P R)
variable (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (left : Finset α) (right : Finset β)
variable (hDE : DE ∈ commonSupportPool left right (fun i => (I i).val) (fun j => (J j).val))
variable (Z q columnBound : ℝ) (hZ : 1 < Z)
variable (hcolumns : ∀ i ∈ left, A.exteriorNorm (I i) ≤ Z ^ columnBound)
variable (hold : A.exteriorNorm (old.effectiveFullSupport remaining) ≤ Z ^ q)

local notation "firstCost" => idealLogLength Z (firstActiveRadical DE.1 DE.2) +
  idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val
local notation "leftElement" => CanonicalLiteralFirstPhase.leftElement C b.primes
  b.leftMultiplicity b.rightMultiplicity
  (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
local notation "rightElement" => CanonicalLiteralFirstPhase.rightElement C b.primes
  b.leftMultiplicity b.rightMultiplicity
  (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val

include hDE hcolumns hold hZ in
private theorem old_firstMask_window :
    A.exteriorNorm (old.effectiveFullSupport (remaining * firstMask DE.1)) ≤
      Z ^ (q + columnBound) := by
  sorry

include hDE hcolumns hold hZ in
/-- Direct and main retain their full first deletion.  Its cost is
the actual original column window, separate from the active radical. -/
theorem unamplified_left (first : A.Exterior)
    (hfirst : A.Generates first leftElement) :
    A.exteriorNorm (((unamplifiedPhases first leftElement hfirst).moving P R old).effectiveFullSupport (remaining * firstMask DE.1)) ≤
      Z ^ ((q + firstCost) + columnBound) := by
  sorry

include hDE hcolumns hold hZ in
theorem unamplified_right (first : A.Exterior)
    (hfirst : A.Generates first rightElement) :
    A.exteriorNorm (((unamplifiedPhases first rightElement hfirst).moving P R old).effectiveFullSupport (remaining * firstMask DE.1)) ≤
      Z ^ ((q + firstCost) + columnBound) := by
  sorry

include hDE hcolumns hold hZ in
private theorem amplified_window (first : A.Exterior) (a : A.R)
    (ha : A.Generates first a) (p : ExteriorPrime A) (n : ℕ) (ell : ℝ)
    (hp : (Ideal.absNorm p.val.asIdeal : ℝ) ≤ Z ^ ell)
    (hfirst : A.exteriorNorm
      (OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1).support ≤ Z ^ firstCost) :
    A.exteriorNorm (((amplifiedPhases C first a ha p n).moving P R old).effectiveFullSupport (remaining * poolExtra DE.1 p)) ≤
      Z ^ ((q + firstCost) + (columnBound + 2 * ell)) := by
  sorry

include hDE hcolumns hold hZ in
/-- All three literal amplifier valuations satisfy this same window.
The original twelfth-power support is charged, not erased. -/
theorem amplified_left (first : A.Exterior)
    (hfirst : A.Generates first leftElement) (p : ExteriorPrime A) (n : ℕ) (ell : ℝ)
    (hp : (Ideal.absNorm p.val.asIdeal : ℝ) ≤ Z ^ ell) :
    A.exteriorNorm (((amplifiedPhases C first leftElement hfirst p n).moving P R old).effectiveFullSupport (remaining * poolExtra DE.1 p)) ≤
      Z ^ ((q + firstCost) + (columnBound + 2 * ell)) := by
  sorry

include hDE hcolumns hold hZ in
theorem amplified_right (first : A.Exterior)
    (hfirst : A.Generates first rightElement) (p : ExteriorPrime A) (n : ℕ) (ell : ℝ)
    (hp : (Ideal.absNorm p.val.asIdeal : ℝ) ≤ Z ^ ell) :
    A.exteriorNorm (((amplifiedPhases C first rightElement hfirst p n).moving P R old).effectiveFullSupport (remaining * poolExtra DE.1 p)) ≤
      Z ^ ((q + firstCost) + (columnBound + 2 * ell)) := by
  sorry

end ActualBlocks
end CanonicalLiteralExceptionalFirstSupport
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalMovingFactors.effectiveFullSupport_mul_dvd
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFirstSupport.firstMask_window
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFirstSupport.unamplified_left
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFirstSupport.unamplified_right
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFirstSupport.amplified_left
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalFirstSupport.amplified_right
