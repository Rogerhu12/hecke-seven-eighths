import HeckeSkeleton.HighBinSupport.EulerRegionUniqueness
import HeckeSkeleton.HighBinSupport.ActualEulerInput
import RowCharacterInputUniqueness

/-!
# Actual Euler continuation uniqueness on its original region

The original calibration forces the row characters to agree. On the
initial domain, the three deleted Hecke factors are nonzero, so the
calibrated identity forces equality of the corrections. Joint analyticity
then propagates that equality through the original `rowEulerRegion`.

No equality of `RowEulerData` structures is required. This proves equality
on the stated region; it does not extend arbitrary finite rational tables
to the high-bin contours where the second real coordinate can be negative.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinEulerUniqueness

open NumberField IsDedekindDomain Set Filter MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HeckeSkeleton.HighBinActualInitial
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Calibration of the genuine prime coefficients determines the finite
family of characters used to detect zeros, regardless of the exceptional
rational tables. -/
theorem physicalRowFamily_eq_of_calibrated
    (P : ProbeData K S) (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K))
    (E₁ E₂ : RowEulerData K S P) (u : FrequencyRow K S) :
    physicalRowFamily K S ψ Θ P E₁ u = physicalRowFamily K S ψ Θ P E₂ u := by
  unfold physicalRowFamily
  rw [rowCharacterInput_character_unique K S P E₁.rows E₂.rows u]

theorem rowZeroBelow_iff_of_calibrated
    (P : ProbeData K S) (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K))
    (E₁ E₂ : RowEulerData K S P) (u : FrequencyRow K S) (height upper : ℝ) :
    rowZeroBelow K S ψ Θ P E₁ u height upper ↔
      rowZeroBelow K S ψ Θ P E₂ u height upper := by
  unfold rowZeroBelow
  rw [physicalRowFamily_eq_of_calibrated K S P ψ Θ E₁ E₂ u]

theorem rowZeroAbove_iff_of_calibrated
    (P : ProbeData K S) (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K))
    (E₁ E₂ : RowEulerData K S P) (u : FrequencyRow K S) (height lower : ℝ) :
    rowZeroAbove K S ψ Θ P E₁ u height lower ↔
      rowZeroAbove K S ψ Θ P E₂ u height lower := by
  unfold rowZeroAbove
  rw [physicalRowFamily_eq_of_calibrated K S P ψ Θ E₁ E₂ u]

theorem physicalRowBin_eq_of_calibrated
    (P : ProbeData K S) (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K))
    (E₁ E₂ : RowEulerData K S P)
    (height normLower normUpper aLower aUpper : ℝ) :
    physicalRowBin K S ψ Θ P E₁ height normLower normUpper aLower aUpper =
      physicalRowBin K S ψ Θ P E₂ height normLower normUpper aLower aUpper := by
  unfold physicalRowBin
  simp_rw [rowZeroAbove_iff_of_calibrated K S P ψ Θ E₁ E₂,
    rowZeroBelow_iff_of_calibrated K S P ψ Θ E₁ E₂]

/-- Nonvanishing of the actual deleted L-ratio on the original initial
domain cancels it from the two calibrated series identities. -/
theorem rowCorrection_eq_initial_of_calibrated
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E₁ E₂ : RowEulerData K S P)
    (h₁ : RowEulerCalibrationInput K S P ψ E₁)
    (h₂ : RowEulerCalibrationInput K S P ψ E₂)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (s w z : ℂ) (hs : 4 < s.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    rowCorrection K S P ψ E₁ Q u s w z =
      rowCorrection K S P ψ E₂ Q u s w z := by
  have hchar := rowCharacterInput_character_unique K S P E₁.rows E₂.rows u
  have hcont := (h₁.initial_identity Q u s w z hs hw hz).symm.trans
    (h₂.initial_identity Q u s w z hs hw hz)
  unfold rowEulerContinuation at hcont
  rw [hchar] at hcont
  have hz6 : 1 < (6 * z).re := by
    norm_num [Complex.mul_re]
    linarith
  have hratio :
      heckeDeletedContinuation K 1 (exceptionalPrimes K S) (6 * z) *
        heckeDeletedContinuation K (E₂.rows.character u) (exceptionalPrimes K S) w /
        heckeDeletedContinuation K (ψ * conjugate (E₂.rows.character u))
          (exceptionalPrimes K S) s ≠ 0 :=
    div_ne_zero
      (mul_ne_zero (heckeDeletedContinuation_ne_zero_initial K S 1 hz6)
        (heckeDeletedContinuation_ne_zero_initial K S _ (by linarith)))
      (heckeDeletedContinuation_ne_zero_initial K S _ (by linarith))
  exact mul_left_cancel₀ hratio hcont

/-- The original `TRowEulerInput` determines the correction on its exact
stated domain, even if the finite rational presentations differ. -/
theorem rowCorrection_eq_of_calibrated
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E₁ E₂ : RowEulerData K S P)
    (h₁ : TRowEulerInput K S P ψ E₁) (h₂ : TRowEulerInput K S P ψ E₂)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (v : ℂ × ℂ × ℂ) (hv : v ∈ rowEulerRegion) :
    rowCorrection K S P ψ E₁ Q u v.1 v.2.1 v.2.2 =
      rowCorrection K S P ψ E₂ Q u v.1 v.2.1 v.2.2 := by
  exact eqOn_rowEulerRegion_of_initial (h₁.correction_analytic Q u)
    (h₂.correction_analytic Q u)
    (fun v hs hw hz => rowCorrection_eq_initial_of_calibrated K S P ψ E₁ E₂
      h₁.initial h₂.initial Q u v.1 v.2.1 v.2.2 hs hw hz) hv

/-- Equality of the literal repository continuations follows without
assuming that the three L-factors are regular at the later point. -/
theorem rowEulerContinuation_eq_of_calibrated
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E₁ E₂ : RowEulerData K S P)
    (h₁ : TRowEulerInput K S P ψ E₁) (h₂ : TRowEulerInput K S P ψ E₂)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (v : ℂ × ℂ × ℂ) (hv : v ∈ rowEulerRegion) :
    rowEulerContinuation K S P ψ E₁ Q u v.1 v.2.1 v.2.2 =
      rowEulerContinuation K S P ψ E₂ Q u v.1 v.2.1 v.2.2 := by
  unfold rowEulerContinuation
  rw [rowCharacterInput_character_unique K S P E₁.rows E₂.rows u,
    rowCorrection_eq_of_calibrated K S P ψ E₁ E₂ h₁ h₂ Q u v hv]

/-- The arithmetic provider is a conclusion of the actual local and
global Euler proofs; the other provider only supplies the original input. -/
theorem rowCorrection_eq_arithmetic
    (P : ProbeData K S) (hP : AllowedGeneratorInput K S P.arithmetic)
    (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
    (hψ : ∀ p : ExteriorPrime K S, UnramifiedAt K ψ p.val)
    (E : RowEulerData K S P) (hE : TRowEulerInput K S P ψ E)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (v : ℂ × ℂ × ℂ) (hv : v ∈ rowEulerRegion) :
    rowCorrection K S P ψ E Q u v.1 v.2.1 v.2.2 =
      rowCorrection K S P ψ (arithmeticHighEulerData K S P ψ) Q u v.1 v.2.1 v.2.2 :=
  rowCorrection_eq_of_calibrated K S P ψ E _ hE
    (arithmeticTRowEulerInput K S P hP ψ hcal hψ) Q u v hv

theorem rowEulerContinuation_eq_arithmetic
    (P : ProbeData K S) (hP : AllowedGeneratorInput K S P.arithmetic)
    (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
    (hψ : ∀ p : ExteriorPrime K S, UnramifiedAt K ψ p.val)
    (E : RowEulerData K S P) (hE : TRowEulerInput K S P ψ E)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (v : ℂ × ℂ × ℂ) (hv : v ∈ rowEulerRegion) :
    rowEulerContinuation K S P ψ E Q u v.1 v.2.1 v.2.2 =
      rowEulerContinuation K S P ψ (arithmeticHighEulerData K S P ψ)
        Q u v.1 v.2.1 v.2.2 :=
  rowEulerContinuation_eq_of_calibrated K S P ψ E _ hE
    (arithmeticTRowEulerInput K S P hP ψ hcal hψ) Q u v hv

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S) → Measure (p.val.adicCompletion K))
variable [∀ p : S, (μ p).IsAddHaarMeasure]

theorem compensatedRowMellinKernel_eq_of_calibrated
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E₁ E₂ : RowEulerData K S P)
    (h₁ : TRowEulerInput K S P ψ E₁) (h₂ : TRowEulerInput K S P ψ E₂)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z : ℝ) (v : ℂ × ℂ × ℂ) (hv : v ∈ rowEulerRegion) :
    compensatedRowMellinKernel K S μ P ψ E₁ g T u Z v.1 v.2.1 v.2.2 =
      compensatedRowMellinKernel K S μ P ψ E₂ g T u Z v.1 v.2.1 v.2.2 := by
  have hcont := fun Q =>
    rowEulerContinuation_eq_of_calibrated K S P ψ E₁ E₂ h₁ h₂ Q u v hv
  simp only [compensatedRowMellinKernel, hcont]

/-- A whole original contour box agrees whenever its three real parts
belong to the original Euler region. The imaginary coordinates are
unrestricted, and equality of the literal integrals needs no added
integrability hypothesis. -/
theorem rowContourBox_eq_of_calibrated
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E₁ E₂ : RowEulerData K S P)
    (h₁ : TRowEulerInput K S P ψ E₁) (h₂ : TRowEulerInput K S P ψ E₂)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z height σ ν zLine : ℝ)
    (hv : ((σ : ℂ), (ν : ℂ), (zLine : ℂ)) ∈ rowEulerRegion) :
    rowContourBox K S μ P ψ E₁ g T u Z height σ ν zLine =
      rowContourBox K S μ P ψ E₂ g T u Z height σ ν zLine := by
  have hk : ∀ ts tw tz : ℝ,
      compensatedRowMellinKernel K S μ P ψ E₁ g T u Z
        ((σ : ℂ) + (ts : ℂ) * Complex.I)
        ((ν : ℂ) + (tw : ℂ) * Complex.I)
        ((zLine : ℂ) + (tz : ℂ) * Complex.I) =
      compensatedRowMellinKernel K S μ P ψ E₂ g T u Z
        ((σ : ℂ) + (ts : ℂ) * Complex.I)
        ((ν : ℂ) + (tw : ℂ) * Complex.I)
        ((zLine : ℂ) + (tz : ℂ) * Complex.I) := by
    intro ts tw tz
    apply compensatedRowMellinKernel_eq_of_calibrated K S μ P ψ E₁ E₂ h₁ h₂
      g T u Z
      (((σ : ℂ) + (ts : ℂ) * Complex.I),
        ((ν : ℂ) + (tw : ℂ) * Complex.I),
        ((zLine : ℂ) + (tz : ℂ) * Complex.I))
    simpa only [rowEulerRegion, Set.mem_setOf_eq, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero] using hv
  unfold rowContourBox
  simp_rw [hk]

#print axioms physicalRowFamily_eq_of_calibrated
#print axioms rowZeroBelow_iff_of_calibrated
#print axioms rowZeroAbove_iff_of_calibrated
#print axioms physicalRowBin_eq_of_calibrated
#print axioms rowCorrection_eq_initial_of_calibrated
#print axioms rowCorrection_eq_of_calibrated
#print axioms rowEulerContinuation_eq_of_calibrated
#print axioms rowCorrection_eq_arithmetic
#print axioms rowEulerContinuation_eq_arithmetic
#print axioms compensatedRowMellinKernel_eq_of_calibrated
#print axioms rowContourBox_eq_of_calibrated

end HeckeSkeleton.HighBinEulerUniqueness
