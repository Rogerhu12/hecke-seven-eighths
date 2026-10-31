import Expansion.PhysicalInitialRowSum
import Expansion.PhysicalRapidTruncation
import Expansion.PhysicalContourMeasure

/-!
# Initial physical boxes and their literal exterior-height tails

The full Fin-3 row integral is identified with the original ordered
three-variable contour.  Its truncation error is an actual integral on
the complement of the common cube.  Absolute row convergence also gives
the full initial box sum plus the complete, summable exterior-height tail.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.PhysicalInitialMellin

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler
open Expansion.Project Expansion.PhysicalInitialHeight Expansion.PhysicalRapidTruncation
open scoped Classical BigOperators

theorem rowHeightVolume_eq_volume : rowHeightVolume = (volume : Measure Heights) := rfl

theorem physicalHeightVolume_eq_volume : physicalHeightVolume = (volume : Measure (Fin 3 → ℝ)) := by
  have he : physicalHeightEquiv = heightEquiv.symm := by
    ext t j
    fin_cases j <;> rfl
  rw [physicalHeightVolume, rowHeightVolume_eq_volume, he]
  exact (heightEquiv_preserving.symm heightEquiv).map_eq

theorem tripleMellinConstant_eq_zpow :
    tripleMellinConstant = (2 * (Real.pi : ℂ)) ^ (-(3 : ℤ)) := by
  simp only [tripleMellinConstant, zpow_neg, zpow_ofNat, inv_pow]

theorem heightCube_eq_rowRetainedHeightBox (H : ℝ) : heightCube H = rowRetainedHeightBox H := rfl

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (sLocalNormOneGroup K Sset)] [BorelSpace (sLocalNormOneGroup K Sset)]

def actualInitialProductKernel (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (u : FrequencyRow K Sset) (t : Heights) : ℂ :=
  rowVerticalKernel K Sset (fun v => μv v.val) P ψ (arithmeticHighEulerData K Sset P ψ)
    g T u Z 5 5 3 t

def actualInitialRowTailIntegral (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z H : ℝ)
    (u : FrequencyRow K Sset) : ℂ :=
  tripleMellinConstant * ∫ t in (heightCube H)ᶜ,
    actualInitialProductKernel K S μv P ψ g T Z u t

def actualInitialTailSum (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z H : ℝ) : ℂ :=
  ∑' u : FrequencyRow K Sset, actualInitialRowTailIntegral K S μv P ψ g T Z H u

theorem actualInitialProductKernel_heightEquiv (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (u : FrequencyRow K Sset) (t : Fin 3 → ℝ) :
    actualInitialProductKernel K S μv P ψ g T Z u (heightEquiv t) =
      actualInitialRowAt K S μv P ψ g T Z u t := by
  rw [heightEquiv_apply]
  rfl

theorem actualInitialRowIntegral_eq_product_integral (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z : ℝ) (u : FrequencyRow K Sset) :
    actualInitialRowIntegral K S μv P ψ g T Z u =
      tripleMellinConstant * ∫ t : Heights, actualInitialProductKernel K S μv P ψ g T Z u t := by
  unfold actualInitialRowIntegral
  congr 1
  simpa only [actualInitialProductKernel_heightEquiv] using
    heightEquiv_preserving.integral_comp' (actualInitialProductKernel K S μv P ψ g T Z u)

theorem actual_initial_rowContourBox_eq_cube_integral (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z H : ℝ) (u : FrequencyRow K Sset)
    (hf : Integrable (actualInitialProductKernel K S μv P ψ g T Z u)) :
    rowContourBox K Sset (fun v => μv v.val) P ψ (arithmeticHighEulerData K Sset P ψ)
      g T u Z H 5 5 3 =
      tripleMellinConstant * ∫ t in heightCube H, actualInitialProductKernel K S μv P ψ g T Z u t := by
  have hbox : IntegrableOn (actualInitialProductKernel K S μv P ψ g T Z u)
      (rowRetainedHeightBox H) rowHeightVolume := by
    rw [rowHeightVolume_eq_volume]
    exact hf.integrableOn
  rw [heightCube_eq_rowRetainedHeightBox, ← rowHeightVolume_eq_volume,
    integral_rowRetainedHeightBox H _ hbox, tripleMellinConstant_eq_zpow]
  rfl

theorem actualInitialRowIntegral_eq_box_add_tail_of_integrable (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z H : ℝ) (u : FrequencyRow K Sset)
    (hf : Integrable (actualInitialProductKernel K S μv P ψ g T Z u)) :
    actualInitialRowIntegral K S μv P ψ g T Z u =
      rowContourBox K Sset (fun v => μv v.val) P ψ (arithmeticHighEulerData K Sset P ψ)
        g T u Z H 5 5 3 + actualInitialRowTailIntegral K S μv P ψ g T Z H u := by
  rw [actualInitialRowIntegral_eq_product_integral,
    actual_initial_rowContourBox_eq_cube_integral K S μv P ψ g T Z H u hf]
  unfold actualInitialRowTailIntegral
  rw [← mul_add, integral_add_compl (measurableSet_heightCube H) hf]

/-- Conversion of an actual row's rapid bound to its original contour-box
error, with the original (2 pi)^(-3) normalization. -/
theorem actualInitialRowIntegral_sub_box_le_of_rapid (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z : ℝ) (u : FrequencyRow K Sset) (n : ℕ) (M : ℝ)
    (hf : AEStronglyMeasurable (actualInitialProductKernel K S μv P ψ g T Z u))
    (hb : ∀ t : Heights, heightWeight (n + 2) t *
      ‖actualInitialProductKernel K S μv P ψ g T Z u t‖ ≤ M)
    {H : ℝ} (hH : 0 ≤ H) :
    ‖actualInitialRowIntegral K S μv P ψ g T Z u -
      rowContourBox K Sset (fun v => μv v.val) P ψ (arithmeticHighEulerData K Sset P ψ)
        g T u Z H 5 5 3‖ ≤
      ‖tripleMellinConstant‖ * M * heightMass / (1 + H) ^ n := by
  have hi := integrable_of_rapid hf n M hb
  rw [actualInitialRowIntegral_eq_box_add_tail_of_integrable K S μv P ψ g T Z H u hi,
    add_sub_cancel_left, actualInitialRowTailIntegral, norm_mul]
  exact (mul_le_mul_of_nonneg_left (norm_tail_integral_le hf n M hb hH)
    (norm_nonneg _)).trans_eq (by ring)

variable [IsTotallyComplex K]
  [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

include ν in
theorem actualInitialProductRows_absolute (P : ProbeData K Sset)
    (hP : AllowedGeneratorInput K Sset P.arithmetic) (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hψ : ∀ p : ExteriorPrime K Sset, UnramifiedAt K ψ p.val)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z) :
    (∀ u : FrequencyRow K Sset, Integrable (actualInitialProductKernel K S μv P ψ g T Z u)) ∧
    Summable (fun u : FrequencyRow K Sset =>
      ∫ t : Heights, ‖actualInitialProductKernel K S μv P ψ g T Z u t‖) := by
  obtain ⟨hi, hs⟩ := actualInitialRows_absolute K S μv ν P hP ψ hcal hψ g T hZ
  constructor
  · intro u
    apply (heightEquiv_preserving.integrable_comp_emb heightEquiv.measurableEmbedding).mp
    simpa only [actualInitialProductKernel_heightEquiv] using hi u
  · apply hs.congr
    intro u
    simpa only [actualInitialProductKernel_heightEquiv] using
      heightEquiv_preserving.integral_comp'
        (fun t : Heights => ‖actualInitialProductKernel K S μv P ψ g T Z u t‖)

include ν in
theorem actualInitialRowIntegral_eq_box_add_tail (P : ProbeData K Sset)
    (hP : AllowedGeneratorInput K Sset P.arithmetic) (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hψ : ∀ p : ExteriorPrime K Sset, UnramifiedAt K ψ p.val)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z)
    (H : ℝ) (u : FrequencyRow K Sset) :
    actualInitialRowIntegral K S μv P ψ g T Z u =
      rowContourBox K Sset (fun v => μv v.val) P ψ (arithmeticHighEulerData K Sset P ψ)
        g T u Z H 5 5 3 + actualInitialRowTailIntegral K S μv P ψ g T Z H u :=
  actualInitialRowIntegral_eq_box_add_tail_of_integrable K S μv P ψ g T Z H u
    ((actualInitialProductRows_absolute K S μv ν P hP ψ hcal hψ g T hZ).1 u)

include ν in
theorem summable_norm_actualInitialRestriction (P : ProbeData K Sset)
    (hP : AllowedGeneratorInput K Sset P.arithmetic) (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hψ : ∀ p : ExteriorPrime K Sset, UnramifiedAt K ψ p.val)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z)
    (A : Set Heights) :
    Summable (fun u : FrequencyRow K Sset =>
      ‖tripleMellinConstant * ∫ t in A, actualInitialProductKernel K S μv P ψ g T Z u t‖) := by
  obtain ⟨hi, hs⟩ := actualInitialProductRows_absolute K S μv ν P hP ψ hcal hψ g T hZ
  apply (hs.mul_left ‖tripleMellinConstant‖).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro u
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (norm_integral_le_integral_norm _).trans
    (setIntegral_le_integral (hi u).norm (Filter.Eventually.of_forall fun _ => norm_nonneg _))

include ν in
theorem summable_actualInitialRowTailIntegral (P : ProbeData K Sset)
    (hP : AllowedGeneratorInput K Sset P.arithmetic) (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hψ : ∀ p : ExteriorPrime K Sset, UnramifiedAt K ψ p.val)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z) (H : ℝ) :
    Summable (actualInitialRowTailIntegral K S μv P ψ g T Z H) :=
  (summable_norm_actualInitialRestriction K S μv ν P hP ψ hcal hψ g T hZ (heightCube H)ᶜ).of_norm

include ν in
theorem summable_actualInitialRowBoxes (P : ProbeData K Sset)
    (hP : AllowedGeneratorInput K Sset P.arithmetic) (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hψ : ∀ p : ExteriorPrime K Sset, UnramifiedAt K ψ p.val)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z) (H : ℝ) :
    Summable (fun u : FrequencyRow K Sset =>
      rowContourBox K Sset (fun v => μv v.val) P ψ (arithmeticHighEulerData K Sset P ψ)
        g T u Z H 5 5 3) := by
  have hi := (actualInitialProductRows_absolute K S μv ν P hP ψ hcal hψ g T hZ).1
  have hs := (summable_norm_actualInitialRestriction K S μv ν P hP ψ hcal hψ g T hZ
    (heightCube H)).of_norm
  exact hs.congr (fun u =>
    (actual_initial_rowContourBox_eq_cube_integral K S μv P ψ g T Z H u (hi u)).symm)

variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- The complete original initial contour is the summable collection of
common finite boxes plus the literal, summable exterior-height integrals. -/
theorem normalizedProbe_eq_initial_boxes_add_tail (P : ProbeData K Sset)
    (hzero : additiveFourierAtZero K Sset (fun v => μv v.val) P.additive = 0)
    (hP : AllowedGeneratorInput K Sset P.arithmetic) (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hψ : ∀ p : ExteriorPrime K Sset, UnramifiedAt K ψ p.val)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z) (H : ℝ) :
    normalizedProbe K Sset (fun v => μv v.val) P ψ g T Z =
      (∑' u : FrequencyRow K Sset,
        rowContourBox K Sset (fun v => μv v.val) P ψ (arithmeticHighEulerData K Sset P ψ)
          g T u Z H 5 5 3) + actualInitialTailSum K S μv P ψ g T Z H := by
  rw [normalizedProbe_eq_sum_actualInitialRowIntegral K S μv ν μ P hzero hP ψ hcal hψ g T hZ]
  simp_rw [actualInitialRowIntegral_eq_box_add_tail K S μv ν P hP ψ hcal hψ g T hZ]
  exact (summable_actualInitialRowBoxes K S μv ν P hP ψ hcal hψ g T hZ H).tsum_add
    (summable_actualInitialRowTailIntegral K S μv ν P hP ψ hcal hψ g T hZ H)

end Expansion.PhysicalInitialMellin

#print axioms Expansion.PhysicalInitialMellin.actualInitialRowIntegral_sub_box_le_of_rapid
#print axioms Expansion.PhysicalInitialMellin.normalizedProbe_eq_initial_boxes_add_tail
