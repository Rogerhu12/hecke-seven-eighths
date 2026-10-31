import Expansion.ActualFiniteRowHeightBudget
import Expansion.PhysicalInitialRowTruncation

/-!
# The actual full initial row and its finite outer destination

The remainder consists of two independently defined actual integrals:
the exterior of the initial height cube, and the six rectangle faces.
The initial full integral, finite destination and their identity are not
assumptions.  Uniform three-height decay proves arbitrary powers of
height saving for the literal initial tail.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain Set MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.Expansion.KernelRegularity
open Expansion.PhysicalInitialMellin Expansion.PhysicalRapidTruncation
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
local notation "muS" => (fun p : Sset => mu p.val)

def actualOuterInitialRemainder
    (P : ProbeData K Sset) (psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    (u : FrequencyRow K Sset) (Z H sigma nuLine zLine : ℝ) : ℂ :=
  actualInitialRowTailIntegral K S mu P psi g ∅ Z H u +
    actualOuterHorizontalFaces K S mu P psi g ∅ u Z H sigma nuLine zLine

include nu in
/-- Full initial-to-outer transport with the actual exterior-height tail
and actual horizontal faces retained separately in the remainder. -/
theorem actual_outer_initial_transport [IsTotallyComplex K]
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) (u : FrequencyRow K Sset)
    (hu : ¬principalFrequencyRow K Sset u)
    {B e Z H sigma nuLine zLine : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (he : 0 < e) (he1 : e < 1 / 1000) (hZ : 0 < Z) (hH : 0 ≤ H)
    (hsigma : B + e ≤ sigma) (hnu : 1 / 2 ≤ nuLine) (hz : 17 / 50 ≤ zLine)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    actualInitialRowIntegral K S mu P psi g ∅ Z u -
      rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g ∅ u Z H sigma nuLine zLine =
      actualOuterInitialRemainder K S mu P psi g u Z H sigma nuLine zLine := by
  have hi := actualInitialRowIntegral_eq_box_add_tail K S mu nu P hAllowed psi hcal hunram
    g ∅ hZ H u
  have hc := actual_outer_finite_transport K S mu nu P omega psi hpsi hAllowed g ∅ u hu
    hB hB1 he he1 hZ hH hsigma hnu hz hboundary
  unfold actualOuterInitialRemainder
  linear_combination hi + hc

include nu in
/-- The same full initial identity lands on the exact original moderate
starting contour, including its possible negative real w coordinate. -/
theorem actual_moderate_initial_transport [IsTotallyComplex K]
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) (u : FrequencyRow K Sset)
    (hu : ¬principalFrequencyRow K Sset u)
    {B e a Z H : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (ha : 51 / 100 ≤ a) (haB : a ≤ B) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hZ : 0 < Z) (hH : 0 ≤ H)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    actualInitialRowIntegral K S mu P psi g ∅ Z u -
      rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g ∅ u Z H (B + 20 * e) (1 - a - 6 * e) (17 / 50) =
      actualOuterInitialRemainder K S mu P psi g u Z H
        (B + 20 * e) (1 - a - 6 * e) (17 / 50) := by
  have hi := actualInitialRowIntegral_eq_box_add_tail K S mu nu P hAllowed psi hcal hunram
    g ∅ hZ H u
  have hc := actual_moderate_row_initial_finite_transport K S mu nu P omega psi hpsi hAllowed
    g ∅ u hu hB hB1 ha haB he he1 hZ hH hboundary
  unfold actualOuterInitialRemainder
  linear_combination hi + hc

include nu in
/-- Arbitrary height saving for the actual exterior of the initial cube,
uniform before every nonprincipal row.  The profile and all normalizing
factors are the original ones. -/
theorem exists_actual_finite_initial_tail_row_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) {B e : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (n : ℕ) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z H : ℝ, Z0 ≤ Z → 0 ≤ H →
      ∀ u : FrequencyRow K Sset, ¬principalFrequencyRow K Sset u →
      ‖actualInitialRowTailIntegral K S mu P psi g ∅ Z H u‖ ≤
        C * Z ^ moderateBoundaryScalePower * frequencyRowNorm K Sset u ^ (113 / 50 : ℝ) /
          (1 + H) ^ n := by
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  obtain ⟨Ck, Z0, hCk, hZ0, hk⟩ := exists_actual_moderate_sweep_kernel_rapid
    K S mu nu hcomplex P omega psi hpsi hAllowed g hB hB1 he he1 hboundary (n + 2)
  let C0 : ℝ := ‖tripleMellinConstant‖ * Ck * heightMass
  have hC0 : 0 ≤ C0 := mul_nonneg (mul_nonneg (norm_nonneg _) hCk.le) heightMass_nonneg
  refine ⟨C0 + 1, Z0, by positivity, hZ0, ?_⟩
  intro Z H hZ hH u hu
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZ0.trans hZ)
  have hNpos : 0 < frequencyRowNorm K Sset u := idealNorm_pos K u.ideal.val
  have hf : Continuous (actualInitialProductKernel K S mu P psi g ∅ Z u) :=
    continuous_actual_rowVerticalKernel_absolute K S mu nu P psi g ∅ u Z hZpos
      5 5 3 (by norm_num) (by norm_num) (by norm_num)
  let M : ℝ := Ck * Z ^ moderateBoundaryScalePower * frequencyRowNorm K Sset u ^ (113 / 50 : ℝ)
  have hb (t : Heights) : heightWeight (n + 2) t *
      ‖actualInitialProductKernel K S mu P psi g ∅ Z u t‖ ≤ M := by
    have hp := hk Z hZ (51 / 100) (by norm_num) (by linarith) u hu
      ((5 : ℂ) + (t.1 : ℂ) * Complex.I)
      ((5 : ℂ) + (t.2.1 : ℂ) * Complex.I)
      ((3 : ℂ) + (t.2.2 : ℂ) * Complex.I)
      (by simpa using (show B + 20 * e ≤ 5 by linarith)) (by simp)
      (by simpa using (show (1 : ℝ) - 51 / 100 - 6 * e ≤ 5 by linarith)) (by simp)
      (by norm_num) (by simp)
    simpa [heightWeight, tripleHeightWeight, actualInitialProductKernel, rowVerticalKernel, M] using hp
  have ht := norm_tail_integral_le hf.aestronglyMeasurable n M hb hH
  rw [actualInitialRowTailIntegral, norm_mul]
  calc
    _ ≤ ‖tripleMellinConstant‖ * (M * heightMass / (1 + H) ^ n) :=
      mul_le_mul_of_nonneg_left ht (norm_nonneg _)
    _ = C0 * Z ^ moderateBoundaryScalePower * frequencyRowNorm K Sset u ^ (113 / 50 : ℝ) /
        (1 + H) ^ n := by dsimp [C0, M]; ring
    _ ≤ _ := by gcongr; linarith

include nu in
/-- In the large range the actual initial tail carries a row power
strictly below -1.  Thus its height loss survives the genuine infinite
row sum, without a separate summability assumption. -/
theorem exists_actual_large_initial_tail_row_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {zeta : ℝ} (hzeta : 0 < zeta) (n : ℕ) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z H : ℝ, Z0 ≤ Z → 0 ≤ H →
      ∀ u : FrequencyRow K Sset, ¬principalFrequencyRow K Sset u →
      ‖actualInitialRowTailIntegral K S mu P psi g ∅ Z H u‖ ≤
        C * Z ^ (outerBoundaryScalePower 5 5 (largeSweepUpper zeta)) *
          frequencyRowNorm K Sset u ^ largeSweepRowPower zeta / (1 + H) ^ n := by
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  obtain ⟨Ck, Z0, hCk, hZ0, hk⟩ := exists_actual_large_sweep_kernel_rapid
    K S mu nu hcomplex P psi hcal hunram g hzeta (n + 2)
  let C0 : ℝ := ‖tripleMellinConstant‖ * Ck * heightMass
  have hC0 : 0 ≤ C0 := mul_nonneg (mul_nonneg (norm_nonneg _) hCk.le) heightMass_nonneg
  refine ⟨C0 + 1, Z0, by positivity, hZ0, ?_⟩
  intro Z H hZ hH u hu
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZ0.trans hZ)
  have hNpos : 0 < frequencyRowNorm K Sset u := idealNorm_pos K u.ideal.val
  have hf : Continuous (actualInitialProductKernel K S mu P psi g ∅ Z u) :=
    continuous_actual_rowVerticalKernel_absolute K S mu nu P psi g ∅ u Z hZpos
      5 5 3 (by norm_num) (by norm_num) (by norm_num)
  let M : ℝ := Ck * Z ^ (outerBoundaryScalePower 5 5 (largeSweepUpper zeta)) *
    frequencyRowNorm K Sset u ^ largeSweepRowPower zeta
  have hb (t : Heights) : heightWeight (n + 2) t *
      ‖actualInitialProductKernel K S mu P psi g ∅ Z u t‖ ≤ M := by
    have hp := hk Z hZ u hu
      ((5 : ℂ) + (t.1 : ℂ) * Complex.I)
      ((5 : ℂ) + (t.2.1 : ℂ) * Complex.I)
      ((3 : ℂ) + (t.2.2 : ℂ) * Complex.I)
      (by norm_num) (by simp) (by norm_num) (by simp)
      (by simpa [largeSweepLower] using (min_le_left (3 : ℝ) (1 + 3 / zeta)))
      (by simpa [largeSweepUpper] using (le_max_left (3 : ℝ) (1 + 3 / zeta)))
    simpa [heightWeight, tripleHeightWeight, actualInitialProductKernel, rowVerticalKernel, M] using hp
  have ht := norm_tail_integral_le hf.aestronglyMeasurable n M hb hH
  rw [actualInitialRowTailIntegral, norm_mul]
  calc
    _ ≤ ‖tripleMellinConstant‖ * (M * heightMass / (1 + H) ^ n) :=
      mul_le_mul_of_nonneg_left ht (norm_nonneg _)
    _ = C0 * Z ^ (outerBoundaryScalePower 5 5 (largeSweepUpper zeta)) *
        frequencyRowNorm K Sset u ^ largeSweepRowPower zeta / (1 + H) ^ n := by
      dsimp [C0, M]
      ring
    _ ≤ _ := by gcongr; linarith

end Expansion.Project

#print axioms Expansion.Project.actual_outer_initial_transport
#print axioms Expansion.Project.actual_moderate_initial_transport
#print axioms Expansion.Project.exists_actual_finite_initial_tail_row_bound
#print axioms Expansion.Project.exists_actual_large_initial_tail_row_bound
