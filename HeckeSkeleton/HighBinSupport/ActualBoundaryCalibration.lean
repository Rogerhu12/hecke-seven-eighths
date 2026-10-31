import HeckeSkeleton.HighBinSupport.ActualTargetEuler
import HeckeSkeleton.HighBinSupport.ActualBoundaryPresentation
import HeckeSkeleton.HighBinSupport.ActualEulerVerticalAE

/-!
# Boundary compatibility for the fixed arithmetic Euler provider

`ActualHighPresentation.euler` is now the actual arithmetic construction
by definition. The existing calibration entry point consequently returns
the original presentation, with its original parameters, companions,
heights, labels, and pieces. Its initial-block and boundary identities are
definitional equalities. The calibration parameter is retained for callers
of the existing API.

The generic row-bin comparison remains useful for arbitrary Euler data.
The companions, height coverage, retained-block count, and original
expansion identifications are still separate geometric requirements.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinBoundaryPresentation

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HeckeSkeleton.HighBinActualInitial HeckeSkeleton.HighBinEulerUniqueness
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] presentationNormOneMeasurable presentationNormOneBorel
  presentationLocalMeasurable presentationLocalBorel presentationLocalHaar

/-- Both original branches of the buffered high bin depend on the
provider only through its already-calibrated row character. -/
theorem highFixedRowBin_eq_of_calibrated (c : TargetContext K)
    (D : ProbeData K ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K))))
    (E₁ E₂ : RowEulerData K _ D) (Θ : Finset (HeckeCharacter K))
    (selectedHeight upperHeight normLower normUpper a e : ℝ) :
    highFixedRowBin K c D E₁ Θ selectedHeight upperHeight normLower normUpper a e =
      highFixedRowBin K c D E₂ Θ selectedHeight upperHeight normLower normUpper a e := by
  unfold highFixedRowBin bufferedPhysicalRowBin
  simp_rw [rowZeroBelow_iff_of_calibrated K _ D (targetCharacter K c) Θ E₁ E₂,
    rowZeroAbove_iff_of_calibrated K _ D (targetCharacter K c) Θ E₁ E₂]

private theorem presentationContour_eq_arithmetic
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hinit : RowEulerCalibrationInput K _ (targetData K c).probe
      (targetCharacter K c) P.euler)
    (Z T : ℝ) (hZ : 1 ≤ Z) (hT : 1 ≤ T) (b : HighBlockIndex K c Z T)
    (u : HighRow K c) (σ : ℝ)
    (hσ : (((targetData K c).expansion Z T).block b).bin + 15 * P.e < σ) :
    rowContourBox K _ (targetData K c).measures.haar (targetData K c).probe
      (targetCharacter K c) P.euler c.geometry (targetData K c).rayFilter u Z
      (P.contourHeight Z T b) σ
      (1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e) (17 / 50) =
    rowContourBox K _ (targetData K c).measures.haar (targetData K c).probe
      (targetCharacter K c)
      (arithmeticHighEulerData K _ (targetData K c).probe (targetCharacter K c))
      c.geometry (targetData K c).rayFilter u Z (P.contourHeight Z T b) σ
      (1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e) (17 / 50) := by
  rfl

/-- Compatibility entry point for the former provider replacement.
The presentation already has the fixed arithmetic provider, so its value
is exactly `P`. The original calibration parameter remains in the API. -/
def arithmeticPresentationOfCalibration
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hinit : RowEulerCalibrationInput K _ (targetData K c).probe
      (targetCharacter K c) P.euler) : ActualHighPresentation K c :=
  P

/-- The compatibility entry point preserves the initial block by definition. -/
theorem presentationInitialBlock_eq_arithmeticPresentation
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hinit : RowEulerCalibrationInput K _ (targetData K c).probe
      (targetCharacter K c) P.euler)
    (Z T : ℝ) (hZ : 1 ≤ Z) (hT : 1 ≤ T) (b : HighBlockIndex K c Z T) :
    presentationInitialBlock K c P Z T b =
      presentationInitialBlock K c (arithmeticPresentationOfCalibration K c P hinit) Z T b := by
  rfl

/-- The whole boundary, including its original sign, is preserved by definition. -/
theorem wholeBinBoundary_eq_arithmeticPresentation
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hinit : RowEulerCalibrationInput K _ (targetData K c).probe
      (targetCharacter K c) P.euler)
    (Z T : ℝ) (hZ : 1 ≤ Z) (hT : 1 ≤ T) :
    wholeBinBoundary K c P Z T =
      wholeBinBoundary K c (arithmeticPresentationOfCalibration K c P hinit) Z T := by
  rfl

/-- Original boundary-control quantifiers, using only the original initial
Euler calibration and the remaining genuine expansion geometry. The old
provider-record equality is discharged by the contour transport above.
The N+k height absorption and retained-block count are inherited unchanged. -/
theorem highBoundaryControl_of_calibrated_lower_geometry
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hinit : RowEulerCalibrationInput K _ (targetData K c).probe
      (targetCharacter K c) P.euler)
    (hcompanions : 1 ∈ P.companions) (δ : ℝ) (hδ : 0 < δ)
    (AB RB ceiling : ℝ) (hAB : 0 ≤ AB) (hceiling : 0 < ceiling)
    (hgeometry : ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
      ∃ Cb Zg : ℝ, 0 < Cb ∧ 1 ≤ Zg ∧ ∀ Z : ℝ, Zg ≤ Z →
        (((targetData K c).expansion Z (Z ^ τ)).blockCount : ℝ) ≤
            Cb * Z ^ RB * (1 + Z ^ τ) ^ AB ∧
        ∀ b : HighBlockIndex K c Z (Z ^ τ),
          δ * (Z ^ τ) ≤ P.contourHeight Z (Z ^ τ) b ∧
          P.contourHeight Z (Z ^ τ) b + 3 / 2 ≤ P.upperHeight Z (Z ^ τ) b) :
    HighBoundaryControl K c P := by
  let P' := arithmeticPresentationOfCalibration K c P hinit
  have hb : HighBoundaryControl K c P' :=
    highBoundaryControl_of_arithmetic_lower_geometry K c P' rfl
      hcompanions δ hδ AB RB ceiling hAB hceiling hgeometry
  obtain ⟨A, R, ceiling', hA, hceiling', hbound⟩ := hb
  refine ⟨A, R, ceiling', hA, hceiling', ?_⟩
  intro τ hτ hτc N
  obtain ⟨C, Z0, hC, hZ0, h⟩ := hbound τ hτ hτc N
  refine ⟨C, Z0, hC, hZ0, ?_⟩
  intro Z hZ
  rw [wholeBinBoundary_eq_arithmeticPresentation K c P hinit Z (Z ^ τ)
    (hZ0.trans hZ) (Real.one_le_rpow (hZ0.trans hZ) hτ.le)]
  exact h Z hZ

#print axioms highFixedRowBin_eq_of_calibrated
#print axioms arithmeticPresentationOfCalibration
#print axioms presentationInitialBlock_eq_arithmeticPresentation
#print axioms wholeBinBoundary_eq_arithmeticPresentation
#print axioms highBoundaryControl_of_calibrated_lower_geometry

end HeckeSkeleton.HighBinBoundaryPresentation
