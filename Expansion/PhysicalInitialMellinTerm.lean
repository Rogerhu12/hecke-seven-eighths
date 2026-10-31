import Expansion.PhysicalCompletedPoisson
import Expansion.PhysicalInitialMellinWeights

/-!
# Termwise initial Mellin identity for the actual probe

Every term retains the original squarefree and whole-index masks, theta
Gauss coefficient, finite Poisson factor, denominator ideal and sixth
power amplifier.  The positive scale calculation identifies its inverse
transform with precisely initialRowEulerTerm, on (5,5,3).
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.PhysicalInitialMellin

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualAbsolute
open Expansion.Project Expansion.PhysicalInitialHeight Expansion.PhysicalInitialPowers
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "FIdx" => FourIdealIndex K Sset

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

/-- The same term as in the full physical Poisson formula, merely indexed
by a frequency row and the original four ideal variables. -/
def physicalPoissonTerm (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K Sset)) (X Y Z : ℝ) (hX : 0 < X)
    (u : FrequencyRow K Sset) (I : FIdx) : ℂ :=
  physicalDenominatorPrefactor K S P X Y I.2.1 *
    physicalCompletedWeight K S P ψ Q Z I.1 *
      (((physicalPoissonScalar K : ℂ) * (X : ℂ) /
          (exteriorNorm K Sset (completedIdeal K Sset I.1.1 I.1.2) : ℂ) *
          (exteriorNorm K Sset I.2.1 : ℂ)) *
        physicalFrequencyProfileTerm K S μv P I.2.1 (completedIdeal K Sset I.1.1 I.1.2)
          ⟨X / exteriorNorm K Sset (completedIdeal K Sset I.1.1 I.1.2),
            div_pos hX (idealNorm_pos K _)⟩ u I.2.2)

def physicalPoissonCoefficient (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K Sset)) (X Y : ℝ)
    (u : FrequencyRow K Sset) (I : FIdx) : ℂ :=
  let c := I.1.1
  let n := I.1.2
  let A := completedIdeal K Sset c n
  if Squarefree c.val.val ∧ wholeIndexMask K Sset (primeSetIdeal K Sset ∅) Q A then
    (physicalPoissonScalar K : ℂ) * thetaGamma K Sset P.arithmetic c 2 *
      heckeIdealCoefficient K (thetaPeriod K Sset P ψ) A.val *
      finitePoissonFactor K Sset P I.2.1 A (poissonFrequency K Sset P u I.2.2) *
      (((Real.sqrt X : ℂ) / (Y : ℂ)) /
        ((Real.sqrt (exteriorNorm K Sset c) : ℂ) * (exteriorNorm K Sset n : ℂ) *
          (exteriorNorm K Sset A : ℂ)))
  else 0

/-- All non-arithmetic factors, independent of the frequency and ideal
indices, in the original initial Mellin representation. -/
def physicalInitialScalar (P : ProbeData K Sset) (X Y Z : ℝ) (s w z : ℂ) : ℂ :=
  (physicalPoissonScalar K : ℂ) * Complex.exp ((s + z - 1) ^ 2) *
    additiveMellin K Sset (fun v => μv v.val) P.additive z * mellin P.denominator.toFun w *
    (X : ℂ) ^ (1 / 2 - z) * (Z : ℂ) ^ (s + z - 1) * (Y : ℂ) ^ (w - 1)

def physicalInitialMellinTerm (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K Sset)) (X Y Z : ℝ)
    (u : FrequencyRow K Sset) (I : FIdx) (t : Fin 3 → ℝ) : ℂ :=
  physicalInitialScalar K S μv P X Y Z
      (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2)) *
    (frequencyRowNorm K Sset u : ℂ) ^ (-idealVerticalPoint 3 (t 2)) *
    initialRowEulerTerm K Sset P ψ Q u
      (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2)) I

def physicalInitialRowKernel (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K Sset)) (X Y Z : ℝ)
    (u : FrequencyRow K Sset) (s w z : ℂ) : ℂ :=
  physicalInitialScalar K S μv P X Y Z s w z *
    (frequencyRowNorm K Sset u : ℂ) ^ (-z) * initialRowEulerSeries K Sset P ψ Q u s w z

theorem physicalPoissonTerm_eq_coefficient_profiles (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset))
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (u : FrequencyRow K Sset) (I : FIdx) :
    physicalPoissonTerm K S μv P ψ Q X Y Z hX u I =
      physicalPoissonCoefficient K S P ψ Q X Y u I *
        (logGaussianProfile (exteriorNorm K Sset (completedIdeal K Sset I.1.1 I.1.2) / Z) *
          P.denominator.toFun (exteriorNorm K Sset I.2.1 / Y) *
          sUnitOrbitalProfile K Sset
            (additiveFourier K Sset (fun v => μv v.val) P.additive)
            ⟨X / exteriorNorm K Sset (completedIdeal K Sset I.1.1 I.1.2) *
                (frequencyRowNorm K Sset u * exteriorNorm K Sset I.2.2 ^ 6),
              mul_pos (div_pos hX (idealNorm_pos K _))
                (mul_pos (idealNorm_pos K _) (pow_pos (idealNorm_pos K _) 6))⟩) := by
  let A := completedIdeal K Sset I.1.1 I.1.2
  have hscale := denominator_poisson_scale X Y (exteriorNorm K Sset I.2.1)
    (exteriorNorm K Sset A) hX hY (idealNorm_pos K _) (idealNorm_pos K _)
  have hOne : idealSymbol K Sset P.arithmetic A 1 = 1 := by
    simp only [idealSymbol, sIntegerSexticIdealEvaluation_one]
  unfold physicalPoissonTerm physicalPoissonCoefficient physicalCompletedWeight completedTerm
  dsimp only
  split_ifs with hmask
  · rw [hOne]
    unfold physicalDenominatorPrefactor physicalFrequencyProfileTerm
    dsimp only
    calc
      _ = ((physicalPoissonScalar K : ℂ) * thetaGamma K Sset P.arithmetic I.1.1 2 *
          heckeIdealCoefficient K (thetaPeriod K Sset P ψ) A.val *
          finitePoissonFactor K Sset P I.2.1 A (poissonFrequency K Sset P u I.2.2)) *
        ((((Y : ℂ)⁻¹ * (Real.sqrt (exteriorNorm K Sset I.2.1 * X) : ℂ)⁻¹ *
          (Real.sqrt (exteriorNorm K Sset I.2.1) : ℂ)⁻¹) *
          ((X : ℂ) / (exteriorNorm K Sset A : ℂ) * (exteriorNorm K Sset I.2.1 : ℂ))) /
          ((Real.sqrt (exteriorNorm K Sset I.1.1) : ℂ) * (exteriorNorm K Sset I.1.2 : ℂ))) *
        (logGaussianProfile (exteriorNorm K Sset A / Z) *
          P.denominator.toFun (exteriorNorm K Sset I.2.1 / Y) *
          sUnitOrbitalProfile K Sset
            (additiveFourier K Sset (fun v => μv v.val) P.additive)
            ⟨X / exteriorNorm K Sset A *
                (frequencyRowNorm K Sset u * exteriorNorm K Sset I.2.2 ^ 6),
              mul_pos (div_pos hX (idealNorm_pos K _))
                (mul_pos (idealNorm_pos K _) (pow_pos (idealNorm_pos K _) 6))⟩) := by
        dsimp only [A]
        simp only [div_eq_mul_inv, mul_inv, mul_one]
        ring
      _ = _ := by
        rw [hscale]
        dsimp only [A]
        simp only [div_eq_mul_inv, mul_inv]
        ring
  · simp only [mul_zero, zero_mul]

theorem physicalInitialMellinTerm_eq_sheared [IsTotallyComplex K]
    (P : ProbeData K Sset) (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset))
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (u : FrequencyRow K Sset) (I : FIdx) (t : Fin 3 → ℝ) :
    physicalInitialMellinTerm K S μv P ψ Q X Y Z u I t =
      physicalPoissonCoefficient K S P ψ Q X Y u I *
        tripleProfileKernel K S μv P
          (exteriorNorm K Sset (completedIdeal K Sset I.1.1 I.1.2) / Z)
          (exteriorNorm K Sset I.2.1 / Y)
          (X / exteriorNorm K Sset (completedIdeal K Sset I.1.1 I.1.2) *
            (frequencyRowNorm K Sset u * exteriorNorm K Sset I.2.2 ^ 6)) (heightShear t) := by
  have hpower := initial_power_balance X Y Z
    (exteriorNorm K Sset I.1.1) (exteriorNorm K Sset I.1.2)
    (exteriorNorm K Sset I.2.1) (exteriorNorm K Sset I.2.2) (frequencyRowNorm K Sset u)
    hX hY hZ (idealNorm_pos K _) (idealNorm_pos K _) (idealNorm_pos K _)
    (idealNorm_pos K _) (idealNorm_pos K _)
    (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2))
  simp only [← exteriorNorm_completed K Sset I.1.1 I.1.2] at hpower
  unfold physicalInitialMellinTerm physicalInitialScalar initialRowEulerTerm
    physicalPoissonCoefficient
  dsimp only
  split_ifs with hmask
  · unfold tripleProfileKernel inverseMellinKernel
    rw [initial_shear_line, show (heightShear t) 1 = t 1 from rfl,
      show (heightShear t) 2 = t 2 from rfl]
    calc
      _ = ((physicalPoissonScalar K : ℂ) *
          thetaGamma K Sset P.arithmetic I.1.1 2 *
          heckeIdealCoefficient K (thetaPeriod K Sset P ψ)
            (completedIdeal K Sset I.1.1 I.1.2).val *
          finitePoissonFactor K Sset P I.2.1 (completedIdeal K Sset I.1.1 I.1.2)
            (poissonFrequency K Sset P u I.2.2)) *
        (Complex.exp ((idealVerticalPoint 5 (t 0) + idealVerticalPoint 3 (t 2) - 1) ^ 2) *
          mellin P.denominator.toFun (idealVerticalPoint 5 (t 1)) *
          additiveMellin K Sset (fun v => μv v.val) P.additive (idealVerticalPoint 3 (t 2))) *
        ((X : ℂ) ^ (1 / 2 - idealVerticalPoint 3 (t 2)) *
          (Z : ℂ) ^ (idealVerticalPoint 5 (t 0) + idealVerticalPoint 3 (t 2) - 1) *
          (Y : ℂ) ^ (idealVerticalPoint 5 (t 1) - 1) *
          (frequencyRowNorm K Sset u : ℂ) ^ (-idealVerticalPoint 3 (t 2)) *
          (exteriorNorm K Sset I.1.1 : ℂ) ^ (-(1 / 2 : ℂ) - idealVerticalPoint 5 (t 0)) *
          (exteriorNorm K Sset I.1.2 : ℂ) ^ (-1 - 3 * idealVerticalPoint 5 (t 0)) *
          (exteriorNorm K Sset I.2.1 : ℂ) ^ (-idealVerticalPoint 5 (t 1)) *
          (exteriorNorm K Sset I.2.2 : ℂ) ^ (-6 * idealVerticalPoint 3 (t 2))) := by ring
      _ = _ := by rw [← hpower]; ring
  · simp only [mul_zero, zero_mul]

variable [IsTotallyComplex K]
  [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

include ν in
theorem integrable_physicalInitialMellinTerm (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset))
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (u : FrequencyRow K Sset) (I : FIdx) :
    Integrable (physicalInitialMellinTerm K S μv P ψ Q X Y Z u I) := by
  have hkernel := integrable_tripleProfileKernel K S μv ν P
    (exteriorNorm K Sset (completedIdeal K Sset I.1.1 I.1.2) / Z)
    (exteriorNorm K Sset I.2.1 / Y)
    (X / exteriorNorm K Sset (completedIdeal K Sset I.1.1 I.1.2) *
      (frequencyRowNorm K Sset u * exteriorNorm K Sset I.2.2 ^ 6))
    (div_pos (idealNorm_pos K _) hZ) (div_pos (idealNorm_pos K _) hY)
    (mul_pos (div_pos hX (idealNorm_pos K _))
      (mul_pos (idealNorm_pos K _) (pow_pos (idealNorm_pos K _) 6)))
  exact (((integrable_heightShear_iff _).mpr hkernel).const_mul
    (physicalPoissonCoefficient K S P ψ Q X Y u I)).congr
      (Filter.Eventually.of_forall (fun t =>
        (physicalInitialMellinTerm_eq_sheared K S μv P ψ Q X Y Z hX hY hZ u I t).symm))

include ν in
/-- Exact termwise identity for the actual Gauss-symbol Poisson term. -/
theorem physicalPoissonTerm_eq_initial_integral (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset))
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (u : FrequencyRow K Sset) (I : FIdx) :
    physicalPoissonTerm K S μv P ψ Q X Y Z hX u I =
      tripleMellinConstant * ∫ t : Fin 3 → ℝ,
        physicalInitialMellinTerm K S μv P ψ Q X Y Z u I t := by
  have hprofiles := three_profiles_mellin_inversion_sheared K S μv ν P
    (exteriorNorm K Sset (completedIdeal K Sset I.1.1 I.1.2) / Z)
    (exteriorNorm K Sset I.2.1 / Y)
    (X / exteriorNorm K Sset (completedIdeal K Sset I.1.1 I.1.2) *
      (frequencyRowNorm K Sset u * exteriorNorm K Sset I.2.2 ^ 6))
    (div_pos (idealNorm_pos K _) hZ) (div_pos (idealNorm_pos K _) hY)
    (mul_pos (div_pos hX (idealNorm_pos K _))
      (mul_pos (idealNorm_pos K _) (pow_pos (idealNorm_pos K _) 6)))
  refine (physicalPoissonTerm_eq_coefficient_profiles K S μv P ψ Q X Y Z hX hY u I).trans
    ((congrArg (fun v : ℂ => physicalPoissonCoefficient K S P ψ Q X Y u I * v)
      hprofiles).trans ?_)
  simp_rw [physicalInitialMellinTerm_eq_sheared K S μv P ψ Q X Y Z hX hY hZ]
  rw [integral_const_mul]
  ring

end Expansion.PhysicalInitialMellin

#print axioms Expansion.PhysicalInitialMellin.physicalPoissonTerm_eq_initial_integral
