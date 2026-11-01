import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFixedPhases
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.Ledger

/-!
# The actual amplifier phase and its passive deletion

The original amplifier residual phase evaluates the chosen prime
generator to exponent `2 * n`.  At the three actual valuations these
are 2, 12 and 14.  The twelfth power has trivial active element, but its
original prime-coprimality zero remains.  The fourteenth power has the
same zero-extended evaluation as the square: the square already vanishes
at that prime, so its extra sixth-power mask is redundant.

The reduced moving list has precisely the support charged by the original
`movingMultiplicity`.  The separate passive ideal is retained explicitly
for the subsequent finite Mobius expansion.  These are identities on each
original nonzero ideal, including ideals inside the fixed exceptional set;
no equality of independently chosen whole Hecke characters is assumed.
The original fixed phases and all previously constructed children are
unchanged.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassivePhases

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open UniqueFactorizationMonoid HeckePort.IdealMobiusDivisorSum CommonSupportMass
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- The active exponent is zero at valuation six, and two at one/seven. -/
def activeExponent (e : AmplifierValuation) : ℕ := 2 * e.movingMultiplicity

/-- Only valuation six leaves a deletion not already imposed by its
reduced active element. -/
def passiveExponent : AmplifierValuation → ℕ
  | .one => 0
  | .six => 1
  | .seven => 0

def activeIdeal (p : ExteriorPrime A) (e : AmplifierValuation) : A.Exterior :=
  powerIdeal p (activeExponent e)

def passiveIdeal (p : ExteriorPrime A) (e : AmplifierValuation) : A.Exterior :=
  powerIdeal p (passiveExponent e)

def activeElement (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (e : AmplifierValuation) : A.R :=
  generator C p ^ activeExponent e

theorem activeElement_generates (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (e : AmplifierValuation) :
    A.Generates (activeIdeal p e) (activeElement C p e) :=
  generator_power_generates C p (activeExponent e)

private theorem coprime_power_two (J : Ideal (𝓞 K)) (p : ExteriorPrime A) :
    IsCoprime J (powerIdeal p 2).val ↔ IsCoprime J p.val.asIdeal := by
  change IsCoprime J (p.val.asIdeal ^ 2) ↔ _
  exact IsCoprime.pow_right_iff (by decide : 0 < (2 : ℕ))

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

/-- The original twelfth power is a unit phase only behind its actual
prime mask.  The fixed exceptional zeros are still in the unit evaluation. -/
theorem evaluation_twelve (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J
        (generator C p ^ 12) =
      if IsCoprime J.val p.val.asIdeal then
        zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J 1
      else 0 := by
  have h := zeroExtendedSexticIdealEvaluation_generated_sixth_mul P J
    (powerIdeal p 2) (generator C p ^ 2) 1 (generator_power_generates C p 2)
  simpa only [← pow_mul, show 2 * 6 = 12 from rfl, mul_one,
    coprime_power_two J.val p] using h

/-- First retain the complete sixth-power mask in the original
fourteenth-power identity. -/
theorem evaluation_fourteen_mask (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J
        (generator C p ^ 14) =
      if IsCoprime J.val p.val.asIdeal then
        zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J
          (generator C p ^ 2)
      else 0 := by
  have h := zeroExtendedSexticIdealEvaluation_generated_sixth_mul P J
    (powerIdeal p 2) (generator C p ^ 2) (generator C p ^ 2)
    (generator_power_generates C p 2)
  have he : (generator C p ^ 2) ^ 6 * generator C p ^ 2 =
      generator C p ^ 14 := by
    rw [← pow_mul, ← pow_add]
    norm_num
  simpa only [he, coprime_power_two J.val p] using h

include R in
theorem evaluation_square_zero (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (J : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hJ : ¬IsCoprime J.val p.val.asIdeal) :
    zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J
        (generator C p ^ 2) = 0 := by
  rw [CanonicalLiteralFirstPhase.singleton_evaluation P R (powerIdeal p 2)
    (generator C p ^ 2) (generator_power_generates C p 2) J]
  rw [if_neg (fun h => hJ ((coprime_power_two J.val p).mp h.2)), mul_zero]

include R in
/-- At valuation seven the reduced square itself has the required zero,
so removing the redundant copy of the same mask is an exact identity. -/
theorem evaluation_fourteen (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J
        (generator C p ^ 14) =
      zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J
        (generator C p ^ 2) := by
  rw [evaluation_fourteen_mask P C p J]
  by_cases hJ : IsCoprime J.val p.val.asIdeal
  · rw [if_pos hJ]
  · rw [if_neg hJ, evaluation_square_zero P R C p J hJ]

include R in
/-- The exact active/passive split of each original pool residue. -/
theorem evaluation_original (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (e : AmplifierValuation)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J
        (generator C p ^ (2 * e.multiplicity)) =
      zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J
          (activeElement C p e) *
        (if IsCoprime J.val (passiveIdeal p e).val then 1 else 0) := by
  cases e with
  | one =>
      simp [AmplifierValuation.multiplicity, AmplifierValuation.movingMultiplicity,
        activeElement, activeExponent, passiveIdeal, passiveExponent, powerIdeal,
        ExteriorIdealEuler.pow, LocalFiniteSums.primeIdeal]
  | six =>
      simp only [AmplifierValuation.multiplicity, AmplifierValuation.movingMultiplicity,
        activeElement, activeExponent, passiveIdeal, passiveExponent, Nat.mul_zero,
        pow_zero]
      change _ = _ * (if IsCoprime J.val (p.val.asIdeal ^ 1) then 1 else 0)
      rw [pow_one, evaluation_twelve P C p J]
      by_cases hJ : IsCoprime J.val p.val.asIdeal <;> simp only [hJ, if_true,
        if_false, mul_one, mul_zero]
  | seven =>
      simpa [AmplifierValuation.multiplicity, AmplifierValuation.movingMultiplicity,
        activeElement, activeExponent, passiveIdeal, passiveExponent, powerIdeal,
        ExteriorIdealEuler.pow, LocalFiniteSums.primeIdeal] using
        evaluation_fourteen P R C p J

def activeMoving (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (e : AmplifierValuation) : OriginalMovingFactors A P R :=
  OriginalMovingFactors.singleton
    ⟨activeElement C p e, (activeElement_generates C p e).1⟩ 1

theorem activeMoving_fullIdeal (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (e : AmplifierValuation) :
    (activeMoving P R C p e).fullIdeal = activeIdeal p e :=
  OriginalMovingFactors.singleton_fullIdeal _ _ (activeElement_generates C p e) 1

theorem activeMoving_coprime_iff (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (e : AmplifierValuation) (J : Ideal (𝓞 K)) :
    IsCoprime J (activeMoving P R C p e).support.val ↔
      IsCoprime J (activeIdeal p e).val := by
  rw [(activeMoving P R C p e).coprime_support_iff_fullIdeal J,
    activeMoving_fullIdeal P R C p e]

/-- The displayed active support is exactly the original paid
`movingMultiplicity`, including the empty support at valuation six. -/
theorem activeMoving_support (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (e : AmplifierValuation) :
    (activeMoving P R C p e).support.val = p.val.asIdeal ^ e.movingMultiplicity := by
  rw [activeMoving, OriginalMovingFactors.singleton_support
    (activeIdeal p e) (activeElement C p e) (activeElement_generates C p e) 1]
  have hs : primeSupport (p.val.asIdeal ^ 2) = {p.val.asIdeal} := by
    change (normalizedFactors (p.val.asIdeal ^ 2)).toFinset = _
    rw [p.val.irreducible.normalizedFactors_pow, normalize_eq,
      Multiset.toFinset_replicate]
    norm_num
  change commonRadical (p.val.asIdeal ^ (2 * e.movingMultiplicity))
    (p.val.asIdeal ^ (2 * e.movingMultiplicity)) = _
  cases e with
  | one =>
      simp only [AmplifierValuation.movingMultiplicity, Nat.mul_one, pow_one,
        commonRadical, hs, Finset.inter_self, Finset.prod_singleton]
  | six =>
      simp [AmplifierValuation.movingMultiplicity, commonRadical, primeSupport]
  | seven =>
      simp only [AmplifierValuation.movingMultiplicity, Nat.mul_one, pow_one,
        commonRadical, hs, Finset.inter_self, Finset.prod_singleton]

theorem activeMoving_norm (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (e : AmplifierValuation) :
    A.exteriorNorm (activeMoving P R C p e).support =
      (Ideal.absNorm p.val.asIdeal : ℝ) ^ e.movingMultiplicity := by
  change (Ideal.absNorm (activeMoving P R C p e).support.val : ℝ) = _
  rw [activeMoving_support P R C p e, map_pow, Nat.cast_pow]

theorem activeMoving_logLength (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (e : AmplifierValuation) (Z : ℝ) :
    idealLogLength Z (activeMoving P R C p e).support.val =
      (e.movingMultiplicity : ℝ) * idealLogLength Z p.val.asIdeal := by
  rw [activeMoving_support P R C p e, idealLogLength_pow]

/-- The exact original active support window, with no charge for a
passive deletion that will instead be expanded into finite labels. -/
theorem activeMoving_norm_eq_rpow (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (e : AmplifierValuation) (Z : ℝ) (hZ : 1 < Z) :
    A.exteriorNorm (activeMoving P R C p e).support =
      Z ^ ((e.movingMultiplicity : ℝ) * idealLogLength Z p.val.asIdeal) := by
  change (Ideal.absNorm (activeMoving P R C p e).support.val : ℝ) = _
  rw [← activeMoving_logLength P R C p e Z,
    rpow_idealLogLength Z hZ _ (activeMoving P R C p e).support.property.1]

include R in
/-- Exact element-level residue identity, before selecting its moving
character or combining it with the other original fixed factors. -/
theorem residue_eq_reduced_element
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation) (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    actualIdealResidue (A := A) (σ := σ) J.val
        (generator C p ^ (2 * e.multiplicity)) =
      actualIdealResidue (A := A) (σ := σ) J.val (activeElement C p e) *
        (if IsCoprime J.val (passiveIdeal p e).val then 1 else 0) := by
  rw [CanonicalOriginalPhaseCalibration.residue_eq_probe_evaluation P hroot hemb,
    CanonicalOriginalPhaseCalibration.residue_eq_probe_evaluation P hroot hemb]
  exact evaluation_original P R C p e J

include R in
/-- The reduction also holds inside the literal product with the first,
unit and original moving factors, with all original zeros retained. -/
theorem residue_mul_eq_reduced_element
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation) (J : HeckeGeneral.Analysis.NonzeroIdeal K) (u : A.R) :
    actualIdealResidue (A := A) (σ := σ) J.val
        (generator C p ^ (2 * e.multiplicity) * u) =
      actualIdealResidue (A := A) (σ := σ) J.val (activeElement C p e * u) *
        (if IsCoprime J.val (passiveIdeal p e).val then 1 else 0) := by
  calc
    _ = (actualIdealResidue (A := A) (σ := σ) J.val (activeElement C p e) *
          (if IsCoprime J.val (passiveIdeal p e).val then 1 else 0)) *
        actualIdealResidue (A := A) (σ := σ) J.val u := by
      rw [actualIdealResidue_frequency_mul,
        residue_eq_reduced_element P R hroot hemb C p e J]
    _ = _ := by rw [actualIdealResidue_frequency_mul]; ring

/-- Single-ideal dictionary for a new paid moving recipe. The passive
mask is a separate scalar and is not silently put back in that recipe. -/
theorem residue_eq_reduced_character
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation) (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    actualIdealResidue (A := A) (σ := σ) J.val
        (generator C p ^ (2 * e.multiplicity)) =
      heckeIdealCoefficient K (activeMoving P R C p e).character J *
        (if sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) J ∧
          IsCoprime J.val (activeMoving P R C p e).support.val then 1 else 0) *
        (if IsCoprime J.val (passiveIdeal p e).val then 1 else 0) := by
  rw [CanonicalOriginalPhaseCalibration.residue_eq_probe_evaluation P hroot hemb,
    evaluation_original P R C p e J, activeMoving_coprime_iff P R C p e J.val]
  congr 1
  exact CanonicalLiteralFirstPhase.singleton_evaluation P R (activeIdeal p e)
    (activeElement C p e) (activeElement_generates C p e) J

/-- The same dictionary for the literal amplifier residual column. -/
theorem columnPhase_eq_reduced_character
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation) {I : A.Exterior}
    (D : AmplifierResidualPresentation C p e.multiplicity I) :
    D.columnPhase =
      heckeIdealCoefficient K (activeMoving P R C p e).character
        ⟨D.residual.val, mem_nonZeroDivisors_of_ne_zero D.residual.property.1⟩ *
        (if sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
              ⟨D.residual.val, mem_nonZeroDivisors_of_ne_zero D.residual.property.1⟩ ∧
          IsCoprime D.residual.val (activeMoving P R C p e).support.val then 1 else 0) *
        (if IsCoprime D.residual.val (passiveIdeal p e).val then 1 else 0) := by
  rw [D.columnPhase_eq_residue]
  exact residue_eq_reduced_character P R hroot hemb C p e
    ⟨D.residual.val, mem_nonZeroDivisors_of_ne_zero D.residual.property.1⟩

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassivePhases

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassivePhases.evaluation_twelve
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassivePhases.evaluation_fourteen
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassivePhases.evaluation_original
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassivePhases.activeMoving_support
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassivePhases.activeMoving_norm_eq_rpow
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassivePhases.residue_eq_reduced_element
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassivePhases.residue_mul_eq_reduced_element
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassivePhases.residue_eq_reduced_character
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassivePhases.columnPhase_eq_reduced_character
