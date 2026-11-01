import Expansion.PhysicalInitialMellinIdentity
import HeckeSkeleton.HighBinSupport.ActualInitialCalibration

/-!
# The normalized physical probe on its actual initial contour

Finite prime-window compensation commutes with the proved absolute
initial integral.  The actual four-ideal Euler identity then identifies
the integrand with compensatedRowMellinKernel, with its original masks,
subset scales, target phases and primeNormalizer.  No Poisson or Mellin
identity is an additional hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.PhysicalInitialMellin

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HighBinActualInitial
open Expansion.PhysicalInitialHeight
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

def physicalCompensationX (g : PrimeWindowGeometry) (Z : ℝ)
    (p : Fin g.slots → ExteriorPrime K Sset) (J : Finset (Fin g.slots)) : ℝ :=
  Z ^ (17 / 48 : ℝ) / exteriorNorm K Sset (subsetPrimeIdeal K Sset p J)

def physicalCompensationY (g : PrimeWindowGeometry) (Z : ℝ)
    (p : Fin g.slots → ExteriorPrime K Sset) (J : Finset (Fin g.slots)) : ℝ :=
  Z ^ (23 / 48 : ℝ) / exteriorNorm K Sset (subsetPrimeIdeal K Sset p J)

def physicalCompensationZ (g : PrimeWindowGeometry) (Z : ℝ)
    (p : Fin g.slots → ExteriorPrime K Sset) (J : Finset (Fin g.slots)) : ℝ :=
  Z * exteriorNorm K Sset (subsetPrimeIdeal K Sset p (Finset.univ \ J))

def physicalCompensationCoefficient (ψ : HeckeCharacter K) (g : PrimeWindowGeometry)
    (p : Fin g.slots → ExteriorPrime K Sset) (J : Finset (Fin g.slots)) : ℂ :=
  (-1 : ℂ) ^ J.card * (exteriorNorm K Sset (subsetPrimeIdeal K Sset p J) : ℂ) ^ (-(3 / 2 : ℂ)) *
    conj (heckeIdealCoefficient K ψ (subsetPrimeIdeal K Sset p (Finset.univ \ J)).val)

theorem physicalCompensationX_pos (g : PrimeWindowGeometry) {Z : ℝ} (hZ : 0 < Z)
    (p : Fin g.slots → ExteriorPrime K Sset) (J : Finset (Fin g.slots)) :
    0 < physicalCompensationX K S g Z p J := div_pos (Real.rpow_pos_of_pos hZ _) (idealNorm_pos K _)

theorem physicalCompensationY_pos (g : PrimeWindowGeometry) {Z : ℝ} (hZ : 0 < Z)
    (p : Fin g.slots → ExteriorPrime K Sset) (J : Finset (Fin g.slots)) :
    0 < physicalCompensationY K S g Z p J := div_pos (Real.rpow_pos_of_pos hZ _) (idealNorm_pos K _)

theorem physicalCompensationZ_pos (g : PrimeWindowGeometry) {Z : ℝ} (hZ : 0 < Z)
    (p : Fin g.slots → ExteriorPrime K Sset) (J : Finset (Fin g.slots)) :
    0 < physicalCompensationZ K S g Z p J := mul_pos hZ (idealNorm_pos K _)

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

def compensatedInitialKernel (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (u : FrequencyRow K Sset) (s w z : ℂ) : ℂ :=
  (∑ p ∈ Fintype.piFinset (fun i => primeWindow K Sset g T Z i),
    (∏ i : Fin g.slots, windowWeight K Sset g Z i (p i)) *
      ∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
        physicalCompensationCoefficient K S ψ g p J *
          physicalInitialRowKernel K S μv P ψ ((Finset.univ \ J).image p)
            (physicalCompensationX K S g Z p J) (physicalCompensationY K S g Z p J)
            (physicalCompensationZ K S g Z p J) u s w z) /
    (physicalResidueNormalizer K Sset (fun v => μv v.val) P * primeNormalizer K Sset g T Z)

theorem compensatedInitialKernel_eq_actual (P : ProbeData K Sset)
    (hP : AllowedGeneratorInput K Sset P.arithmetic) (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hψ : ∀ p : ExteriorPrime K Sset, UnramifiedAt K ψ p.val)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (u : FrequencyRow K Sset) (s w z : ℂ)
    (hs : 4 < s.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    compensatedInitialKernel K S μv P ψ g T Z u s w z =
      compensatedRowMellinKernel K Sset (fun v => μv v.val) P ψ
        (arithmeticHighEulerData K Sset P ψ) g T u Z s w z := by
  have he (Q : Finset (ExteriorPrime K Sset)) :=
    initialRowEulerSeries_eq_rowEulerContinuation K Sset P hP ψ hcal hψ Q u s w z hs hw hz
  unfold compensatedInitialKernel physicalInitialRowKernel
  simp_rw [he]
  unfold physicalInitialScalar compensatedRowMellinKernel physicalCompensationCoefficient
    physicalCompensationX physicalCompensationY physicalCompensationZ
  dsimp only
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro J hJ
  ring

theorem summable_physicalInitialRowKernel_at (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset))
    (X Y Z : ℝ) (t : Fin 3 → ℝ) :
    Summable (fun u : FrequencyRow K Sset => physicalInitialRowKernel K S μv P ψ Q X Y Z u
      (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2))) := by
  have h := ((summable_norm_physicalInitialMellinTerm K S μv P ψ Q X Y Z t).of_norm).prod
  exact h.congr (fun u => (physicalInitialRowKernel_eq_tsum K S μv P ψ Q X Y Z u t).symm)

/-- Finite compensation is rearranged with the genuine row series only
after summability of every marked and rescaled original row series. -/
theorem tsum_compensatedInitialKernel (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ) (t : Fin 3 → ℝ) :
    (∑' u : FrequencyRow K Sset, compensatedInitialKernel K S μv P ψ g T Z u
      (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2))) =
    (∑ p ∈ Fintype.piFinset (fun i => primeWindow K Sset g T Z i),
      (∏ i : Fin g.slots, windowWeight K Sset g Z i (p i)) *
        ∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
          physicalCompensationCoefficient K S ψ g p J *
            ∑' u : FrequencyRow K Sset, physicalInitialRowKernel K S μv P ψ
              ((Finset.univ \ J).image p)
              (physicalCompensationX K S g Z p J) (physicalCompensationY K S g Z p J)
              (physicalCompensationZ K S g Z p J) u
              (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2))) /
      (physicalResidueNormalizer K Sset (fun v => μv v.val) P * primeNormalizer K Sset g T Z) := by
  let rows (p : Fin g.slots → ExteriorPrime K Sset) (J : Finset (Fin g.slots))
      (u : FrequencyRow K Sset) : ℂ := physicalInitialRowKernel K S μv P ψ
    ((Finset.univ \ J).image p)
    (physicalCompensationX K S g Z p J) (physicalCompensationY K S g Z p J)
    (physicalCompensationZ K S g Z p J) u
    (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2))
  have hr (p : Fin g.slots → ExteriorPrime K Sset) (J : Finset (Fin g.slots)) :
      Summable (rows p J) := summable_physicalInitialRowKernel_at K S μv P ψ _ _ _ _ t
  unfold compensatedInitialKernel
  simp only [div_eq_mul_inv, tsum_mul_right]
  congr 1
  rw [Summable.tsum_finsetSum (fun p _ =>
    (summable_sum (s := (Finset.univ : Finset (Fin g.slots)).powerset)
      (fun J _ => (hr p J).mul_left (physicalCompensationCoefficient K S ψ g p J))).mul_left
      (∏ i : Fin g.slots, windowWeight K Sset g Z i (p i)))]
  apply Finset.sum_congr rfl
  intro p hp
  rw [tsum_mul_left, Summable.tsum_finsetSum
    (fun J _ => (hr p J).mul_left (physicalCompensationCoefficient K S ψ g p J))]
  simp only [tsum_mul_left, rows]

variable [IsTotallyComplex K]
  [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

def compensatedInitialSum (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ) (t : Fin 3 → ℝ) : ℂ :=
  ∑ p ∈ Fintype.piFinset (fun i => primeWindow K Sset g T Z i),
    (∏ i : Fin g.slots, windowWeight K Sset g Z i (p i)) *
      ∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
        physicalCompensationCoefficient K S ψ g p J *
          ∑' u : FrequencyRow K Sset, physicalInitialRowKernel K S μv P ψ
            ((Finset.univ \ J).image p)
            (physicalCompensationX K S g Z p J) (physicalCompensationY K S g Z p J)
            (physicalCompensationZ K S g Z p J) u
            (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2))

include ν in
theorem integrable_compensatedInitialSum (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z) :
    Integrable (compensatedInitialSum K S μv P ψ g T Z) := by
  apply integrable_finsetSum
  intro p hp
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro J hJ
  exact (integrable_physicalInitial_row_sum K S μv ν P ψ _ _ _ _
    (physicalCompensationX_pos K S g hZ p J) (physicalCompensationY_pos K S g hZ p J)
    (physicalCompensationZ_pos K S g hZ p J)).const_mul _

include ν μ in
theorem compensatedProbe_eq_initial_integral (P : ProbeData K Sset)
    (hzero : additiveFourierAtZero K Sset (fun v => μv v.val) P.additive = 0)
    (ψ : HeckeCharacter K) (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    {Z : ℝ} (hZ : 0 < Z) :
    compensatedProbe K Sset P ψ g T Z =
      tripleMellinConstant * ∫ t : Fin 3 → ℝ, compensatedInitialSum K S μv P ψ g T Z t := by
  let H (p : Fin g.slots → ExteriorPrime K Sset) (J : Finset (Fin g.slots))
      (t : Fin 3 → ℝ) : ℂ :=
    physicalCompensationCoefficient K S ψ g p J *
      ∑' u : FrequencyRow K Sset, physicalInitialRowKernel K S μv P ψ
        ((Finset.univ \ J).image p)
        (physicalCompensationX K S g Z p J) (physicalCompensationY K S g Z p J)
        (physicalCompensationZ K S g Z p J) u
        (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2))
  have hH (p : Fin g.slots → ExteriorPrime K Sset) (J : Finset (Fin g.slots)) :
      Integrable (H p J) :=
    (integrable_physicalInitial_row_sum K S μv ν P ψ _ _ _ _
      (physicalCompensationX_pos K S g hZ p J) (physicalCompensationY_pos K S g hZ p J)
      (physicalCompensationZ_pos K S g hZ p J)).const_mul _
  have hterm (p : Fin g.slots → ExteriorPrime K Sset) (J : Finset (Fin g.slots)) :
      compensationTerm K Sset P ψ g Z p J =
        tripleMellinConstant * ∫ t : Fin 3 → ℝ, H p J t := by
    change physicalCompensationCoefficient K S ψ g p J *
      physicalProbe K Sset P ψ ((Finset.univ \ J).image p)
        (physicalCompensationX K S g Z p J) (physicalCompensationY K S g Z p J)
        (physicalCompensationZ K S g Z p J) = _
    rw [physicalProbe_eq_initial_rows K S μv ν μ P hzero ψ _ _ _ _
      (physicalCompensationX_pos K S g hZ p J) (physicalCompensationY_pos K S g hZ p J)
      (physicalCompensationZ_pos K S g hZ p J)]
    dsimp only [H]
    rw [integral_const_mul]
    ring
  have hint : (∫ t : Fin 3 → ℝ, compensatedInitialSum K S μv P ψ g T Z t) =
      ∑ p ∈ Fintype.piFinset (fun i => primeWindow K Sset g T Z i),
        (∏ i : Fin g.slots, windowWeight K Sset g Z i (p i)) *
          ∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
            ∫ t : Fin 3 → ℝ, H p J t := by
    unfold compensatedInitialSum
    rw [integral_finsetSum _ (fun p _ =>
      (integrable_finsetSum _ (fun J _ => hH p J)).const_mul _)]
    apply Finset.sum_congr rfl
    intro p hp
    rw [integral_const_mul, integral_finsetSum _ (fun J _ => hH p J)]
  rw [hint]
  unfold compensatedProbe
  simp_rw [hterm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro J hJ
  ring

include ν μ in
theorem normalizedProbe_eq_initial_compensatedKernel (P : ProbeData K Sset)
    (hzero : additiveFourierAtZero K Sset (fun v => μv v.val) P.additive = 0)
    (ψ : HeckeCharacter K) (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    {Z : ℝ} (hZ : 0 < Z) :
    normalizedProbe K Sset (fun v => μv v.val) P ψ g T Z =
      tripleMellinConstant * ∫ t : Fin 3 → ℝ, ∑' u : FrequencyRow K Sset,
        compensatedInitialKernel K S μv P ψ g T Z u
          (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2)) := by
  rw [normalizedProbe, compensatedProbe_eq_initial_integral K S μv ν μ P hzero ψ g T hZ]
  simp_rw [tsum_compensatedInitialKernel]
  change (tripleMellinConstant * ∫ t : Fin 3 → ℝ, compensatedInitialSum K S μv P ψ g T Z t) / _ =
    tripleMellinConstant * ∫ t : Fin 3 → ℝ, compensatedInitialSum K S μv P ψ g T Z t / _
  simp only [div_eq_mul_inv, integral_mul_const, mul_assoc]

include ν in
theorem integrable_actual_initial_compensated_row_sum (P : ProbeData K Sset)
    (hP : AllowedGeneratorInput K Sset P.arithmetic) (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hψ : ∀ p : ExteriorPrime K Sset, UnramifiedAt K ψ p.val)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z) :
    Integrable (fun t : Fin 3 → ℝ => ∑' u : FrequencyRow K Sset,
      compensatedRowMellinKernel K Sset (fun v => μv v.val) P ψ
        (arithmeticHighEulerData K Sset P ψ) g T u Z
        (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2))) := by
  have he (t : Fin 3 → ℝ) (u : FrequencyRow K Sset) :=
    compensatedInitialKernel_eq_actual K S μv P hP ψ hcal hψ g T Z u
      (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2))
      (by norm_num) (by norm_num) (by norm_num)
  simp_rw [← he, tsum_compensatedInitialKernel]
  exact (integrable_compensatedInitialSum K S μv ν P ψ g T hZ).div_const _

include ν μ in
/-- The target endpoint uses the original normalizedProbe and the original
compensatedRowMellinKernel with the actual calibrated Euler data. -/
theorem normalizedProbe_eq_actual_initial_rows (P : ProbeData K Sset)
    (hzero : additiveFourierAtZero K Sset (fun v => μv v.val) P.additive = 0)
    (hP : AllowedGeneratorInput K Sset P.arithmetic) (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hψ : ∀ p : ExteriorPrime K Sset, UnramifiedAt K ψ p.val)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z) :
    normalizedProbe K Sset (fun v => μv v.val) P ψ g T Z =
      tripleMellinConstant * ∫ t : Fin 3 → ℝ, ∑' u : FrequencyRow K Sset,
        compensatedRowMellinKernel K Sset (fun v => μv v.val) P ψ
          (arithmeticHighEulerData K Sset P ψ) g T u Z
          (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2)) := by
  rw [normalizedProbe_eq_initial_compensatedKernel K S μv ν μ P hzero ψ g T hZ]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => tsum_congr (fun u =>
    compensatedInitialKernel_eq_actual K S μv P hP ψ hcal hψ g T Z u
      (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2))
      (by norm_num) (by norm_num) (by norm_num)))

include ν μ in
theorem normalizedProbe_eq_actual_initial_iterated_rows (P : ProbeData K Sset)
    (hzero : additiveFourierAtZero K Sset (fun v => μv v.val) P.additive = 0)
    (hP : AllowedGeneratorInput K Sset P.arithmetic) (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hψ : ∀ p : ExteriorPrime K Sset, UnramifiedAt K ψ p.val)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z) :
    normalizedProbe K Sset (fun v => μv v.val) P ψ g T Z =
      tripleMellinConstant * ∫ ts : ℝ, ∫ tw : ℝ, ∫ tz : ℝ, ∑' u : FrequencyRow K Sset,
        compensatedRowMellinKernel K Sset (fun v => μv v.val) P ψ
          (arithmeticHighEulerData K Sset P ψ) g T u Z
          (idealVerticalPoint 5 ts) (idealVerticalPoint 5 tw) (idealVerticalPoint 3 tz) := by
  rw [normalizedProbe_eq_actual_initial_rows K S μv ν μ P hzero hP ψ hcal hψ g T hZ]
  rw [integral_eq_initial_order _
    (integrable_actual_initial_compensated_row_sum K S μv ν P hP ψ hcal hψ g T hZ)]
  rfl

end Expansion.PhysicalInitialMellin

#print axioms Expansion.PhysicalInitialMellin.normalizedProbe_eq_actual_initial_iterated_rows
