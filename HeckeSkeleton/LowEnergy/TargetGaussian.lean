import HeckeSkeleton.LowEnergy.TargetDictionary
import HeckeSkeleton.LowEnergy.GaussianTheta
import HeckeSkeleton.ActualProbeIntegralComplete

/-!
# Gaussian reconstruction of the exact target row

The prime windows and their weights remain at the original physical height
Z. Only the completed theta scale is multiplied by exp(k). Replacing Z by
Z*exp(k) in the entire marked row would move the windows and would be wrong.

This adapter imports LowCauchy's identical target definition rather than
Principal's unfinished energy theorem. Absolute convergence is supplied by
the existing actual probe integral theorem.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.TargetGaussian

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.LowEnergy.ActualRows
open HeckeSkeleton.LowEnergy.GaussianTheta
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (c : HeckeSkeleton.TargetContext K)
local notation "S" => HeckeSkeleton.places K c
local notation "P" => HeckeSkeleton.probeData K c
local notation "ψ" => HeckeSkeleton.targetCharacter K c
local notation "g" => c.geometry
local notation "T" => HeckeSkeleton.rayFilter K c

def markWeight (Z : ℝ) (p : Fin g.slots → ExteriorPrime K S)
    (J : Finset (Fin g.slots)) (p' : Fin g.slots → ExteriorPrime K S) : ℂ :=
  if ∀ i ∈ J, p' i = p i then
    (∏ i ∈ Finset.univ \ J, windowWeight K S g Z i (p' i)) *
      conj (heckeIdealCoefficient K ψ (subsetPrimeIdeal K S p' (Finset.univ \ J)).val)
  else 0

def thetaScale (Z : ℝ) (J : Finset (Fin g.slots))
    (p' : Fin g.slots → ExteriorPrime K S) : ℝ :=
  Z * exteriorNorm K S (subsetPrimeIdeal K S p' (Finset.univ \ J))

def annularMarkedRow (Z : ℝ) (p : Fin g.slots → ExteriorPrime K S)
    (J : Finset (Fin g.slots)) (k : ℤ) (m : S.integer K) : ℂ :=
  ∑ p' ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
    markWeight K c Z p J p' *
      completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ) m
        (primeSetIdeal K S ∅) ((Finset.univ \ J).image p') (annulusTest k).toFun
        (thetaScale K c Z J p' * Real.exp (k : ℝ))

theorem thetaScale_pos {Z : ℝ} (hZ : 0 < Z) (J : Finset (Fin g.slots))
    (p' : Fin g.slots → ExteriorPrime K S) : 0 < thetaScale K c Z J p' :=
  mul_pos hZ (exteriorNorm_positive K S _)

theorem markedRow_eq_weighted (Z : ℝ) (p : Fin g.slots → ExteriorPrime K S)
    (J : Finset (Fin g.slots)) (m : S.integer K) :
    markedRowWithTest K S P ψ g T Z p J logGaussianProfile m =
      ∑ p' ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
        markWeight K c Z p J p' *
          completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ) m
            (primeSetIdeal K S ∅) ((Finset.univ \ J).image p') logGaussianProfile
            (thetaScale K c Z J p') := by
  simp only [markedRowWithTest, markWeight, thetaScale, ite_mul, zero_mul]

theorem annularMarkedRow_summable {Z : ℝ} (hZ : 0 < Z)
    (p : Fin g.slots → ExteriorPrime K S) (J : Finset (Fin g.slots))
    (m : S.integer K) : Summable (fun k : ℤ => annularMarkedRow K c Z p J k m) := by
  unfold annularMarkedRow
  apply summable_sum
  intro p' hp'
  exact (completedThetaSum_annuli_summable K S P.arithmetic (thetaPeriod K S P ψ) m
    (primeSetIdeal K S ∅) ((Finset.univ \ J).image p')
    (thetaScale_pos K c hZ J p')
    ((actual_probeIntegralInput K S P ψ).theta_absolute m
      ((Finset.univ \ J).image p') (thetaScale K c Z J p')
      (thetaScale_pos K c hZ J p'))).mul_left (markWeight K c Z p J p')

/-- Exact target-row identity; surviving marks stay inside the row sum. -/
theorem completedMarkedRow_gaussian_annuli {Z : ℝ} (hZ : 0 < Z)
    (p : Fin g.slots → ExteriorPrime K S) (J : Finset (Fin g.slots))
    (m : NonzeroRingElements (S.integer K)) :
    HeckeSkeleton.LowCauchy.completedMarkedRow K c Z p J m =
      ∑' k : ℤ, annularMarkedRow K c Z p J k m.val := by
  rw [TargetDictionary.completedMarkedRow_eq K c, markedRow_eq_weighted K c]
  exact finite_marked_gaussian_annuli K S P.arithmetic
    (Fintype.piFinset (fun i => primeWindow K S g T Z i))
    (markWeight K c Z p J) (thetaPeriod K S P ψ) m.val (primeSetIdeal K S ∅)
    (fun p' => (Finset.univ \ J).image p') (thetaScale K c Z J)
    (fun p' _ => thetaScale_pos K c hZ J p')
    (fun p' _ => (actual_probeIntegralInput K S P ψ).theta_absolute m.val
      ((Finset.univ \ J).image p') (thetaScale K c Z J p')
      (thetaScale_pos K c hZ J p'))

theorem annularMarkedRow_sixthInvariant (Z : ℝ)
    (p : Fin g.slots → ExteriorPrime K S) (J : Finset (Fin g.slots)) (k : ℤ) :
    SixthInvariant K S (annularMarkedRow K c Z p J k) := by
  intro u m
  apply Finset.sum_congr rfl
  intro p' _
  rw [completedThetaSum_sixthInvariant K S P.arithmetic (thetaPeriod K S P ψ)
    (primeSetIdeal K S ∅) ((Finset.univ \ J).image p') (annulusTest k).toFun
    (thetaScale K c Z J p' * Real.exp (k : ℝ)) u m]

/-- The original orbit cutoff commutes with the reconstructed linear row.
No new row family or reduced set of unit sectors is substituted. -/
theorem cutoff_completedMarkedRow_eq_tsum {Z : ℝ} (hZ : 0 < Z) (R : ℝ)
    (p : Fin g.slots → ExteriorPrime K S) (J : Finset (Fin g.slots))
    (u : HeckeSkeleton.Gram.Orbit K S) :
    (if (sIntegerOrbitNorm K S (sixthPowerUnits K S) u).val ≤ R then
      HeckeSkeleton.LowCauchy.completedMarkedRow K c Z p J u.out else 0) =
    ∑' k : ℤ, if (sIntegerOrbitNorm K S (sixthPowerUnits K S) u).val ≤ R then
      annularMarkedRow K c Z p J k u.out.val else 0 := by
  split_ifs
  · exact completedMarkedRow_gaussian_annuli K c hZ p J u.out
  · simp

#print axioms completedMarkedRow_gaussian_annuli
#print axioms annularMarkedRow_summable

end HeckeSkeleton.LowEnergy.TargetGaussian
