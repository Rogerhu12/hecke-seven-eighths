import HeckeSkeleton.HighBinSupport.ActualTargetEuler
import HeckeSkeleton.HighBinSupport.ActualNormFormRegionTarget
import HeckeSkeleton.HighBinSupport.ActualEulerVerticalAE

/-!
Original calibrated Euler providers on the computed amplitude regions.

The regions are the same actual full-slot fibers already constructed in
`ActualNormFormRegions`. Restricting the proved almost-everywhere kernel
identity identifies their literal integrals for any provider satisfying
the original `RowEulerCalibrationInput`. No equality of provider records,
integrability of the old provider, or desired piece bound is assumed.

The final consumer retains the original height, label-code and mean
identifications. Its shifted-piece identity now uses the presentation's
own Euler provider, rather than an arithmetic-provider identity supplied
by the caller. This does not identify the opaque named expansion or
construct the independent witness subdivisions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HighBinVerified.NormFormRegionCalibration

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HeckeSkeleton.HighBinEulerUniqueness
open HighBinBoundary.ActualIntegrability
open NormFormRegions NormFormRegionIntegral
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S₀" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : (S : Set (HeightOneSpectrum (𝓞 K)))) → Measure (p.val.adicCompletion K))
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), (μ p).IsAddHaarMeasure]

/-- The computed restricted piece evaluated with the specified original
Euler provider. Its region, normalization, and contour lines are fixed. -/
def actualRegionPieceWithEuler (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (E : RowEulerData K S₀ P) (g : PrimeWindowGeometry) (u : FrequencyRow K S₀)
    (Z a e H theta : ℝ) (N : ℕ) (label : Fin g.slots → Fin (N + 1)) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ (-(3 : ℤ)) *
    ∫ x in actualSlotRegion K S₀ P psi g u Z a e H theta N label,
      compensatedRowMellinKernel K S₀ μ P psi E g ∅ u Z
        (sLine (a + 16 * e) x) (wLine (1 - a - 6 * e) x) (zLine x)

/-- The actual initial-series calibrations determine every restricted
piece, including the closed a=1 bin. Almost-everywhere equality restricts
to the literal region without a separate measurability or integrability
premise for the arbitrary provider. -/
theorem actualRegionPieceWithEuler_eq_of_calibrated
    (P : ProbeData K S₀) (psi : HeckeCharacter K) (E : RowEulerData K S₀ P)
    (hE : RowEulerCalibrationInput K S₀ P psi E)
    (hA : RowEulerCalibrationInput K S₀ P psi (arithmeticHighEulerData K S₀ P psi))
    (g : PrimeWindowGeometry) (u : FrequencyRow K S₀)
    (Z a e H theta : ℝ) (N : ℕ) (label : Fin g.slots → Fin (N + 1))
    (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000) :
    actualRegionPieceWithEuler K S μ P psi E g u Z a e H theta N label =
      actualRegionPiece K S μ P psi g u Z a e H theta N label := by
  have hσ : (((a + 16 * e : ℝ) : ℂ), ((1 - a - 6 * e : ℝ) : ℂ),
      ((17 / 50 : ℝ) : ℂ)) ∈ sweptTube a e := by
    change a + 15 * e < a + 16 * e ∧
      1 - a - 7 * e < 1 - a - 6 * e ∧ 17 / 50 - e < 17 / 50
    exact ⟨by linarith, by linarith, by linarith⟩
  have hk := compensatedRowMellinKernel_ae_eq_vertical_of_calibrated
    K S₀ μ P psi E (arithmeticHighEulerData K S₀ P psi) hE hA g ∅ u Z
    ha ha1 he he1 (a + 16 * e, 1 - a - 6 * e, 17 / 50) hσ
  unfold actualRegionPieceWithEuler actualRegionPiece
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae
    (s := actualSlotRegion K S₀ P psi g u Z a e H theta N label) hk] with x hx
  simpa only [actualRegionKernel, sLine, wLine, zLine,
    Complex.ofReal_div, Complex.ofReal_ofNat] using hx

end HighBinVerified.NormFormRegionCalibration

namespace HeckeSkeleton.HighBinNormFormRegionTarget

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HighBinActualInitial
open HeckeSkeleton.HighBinBoundaryPresentation
open HighBinVerified HighBinVerified.NormFormRegions
open HighBinVerified.NormFormRegionIntegral HighBinVerified.NormFormRegionCalibration
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] presentationNormOneMeasurable presentationNormOneBorel
  presentationLocalMeasurable presentationLocalBorel presentationLocalHaar

/-- Original norm-form quantifiers with the presentation's own calibrated
provider in the literal shifted-piece identity. The required numerical
and per-label structural identities are unchanged. -/
theorem exists_target_highShiftedNormForm_calibrated_region_connection
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hinit : RowEulerCalibrationInput K _ (targetData K c).probe
      (targetCharacter K c) P.euler)
    (hcomp : (1 : HeckeCharacter K) ∈ P.companions) :
    ∃ kappa theta : ℝ, ∃ N : ℕ, ∃ C Z0 : ℝ,
      0 < kappa ∧ 0 < theta ∧ 0 < C ∧ 1 ≤ Z0 ∧
      ((∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
        ∀ b : HighBlockIndex K c Z T,
          P.contourHeight Z T b = NormForm.internalHeight Z T kappa) →
      (∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
        ∀ b : HighBlockIndex K c Z T,
          2 * NormForm.internalHeight Z T kappa + 2 ≤ P.upperHeight Z T b) →
      ∀ code : PresentationRegionLabels K c N,
        (∀ (Z T : ℝ), Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
          ∀ (b : HighBlockIndex K c Z T) (label : HighLabel K c Z T b),
          label ∈ P.labels Z T b →
          ((((targetData K c).expansion Z T).block b).amplitudeSet label).mean =
            actualRegionMean c.geometry (((targetData K c).expansion Z T).block b).bin
              theta N (code Z T b label)) →
        (∀ (Z T : ℝ), Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
          ∀ (b : HighBlockIndex K c Z T) (label : HighLabel K c Z T b),
          label ∈ P.labels Z T b → ∀ u : HighRow K c,
          u ∈ ((((targetData K c).expansion Z T).block b).amplitudeSet label).rows →
          P.shiftedPiece Z T b label u =
            actualRegionPieceWithEuler K (targetData K c).S (targetData K c).measures.haar
              (targetData K c).probe (targetCharacter K c) P.euler c.geometry u Z
              (((targetData K c).expansion Z T).block b).bin P.e
              (P.contourHeight Z T b) theta N (code Z T b label)) →
        HighShiftedNormForm K c P) := by
  obtain ⟨kappa, theta, N, C, Z0, hkappa, htheta, hC, hZ0, hconnect⟩ :=
    exists_target_highShiftedNormForm_region_connection K c P hcomp
  refine ⟨kappa, theta, N, C, Z0, hkappa, htheta, hC, hZ0, ?_⟩
  intro hheight hupper code hmean hpiece
  apply hconnect hheight hupper code hmean
  intro Z T hZ hT hTcap b label hlabel u hu
  calc
    P.shiftedPiece Z T b label u =
        actualRegionPieceWithEuler K (targetData K c).S (targetData K c).measures.haar
          (targetData K c).probe (targetCharacter K c) P.euler c.geometry u Z
          (((targetData K c).expansion Z T).block b).bin P.e
          (P.contourHeight Z T b) theta N (code Z T b label) :=
      hpiece Z T hZ hT hTcap b label hlabel u hu
    _ = _ := actualRegionPieceWithEuler_eq_of_calibrated
      K (targetData K c).S (targetData K c).measures.haar
      (targetData K c).probe (targetCharacter K c) P.euler hinit
      (targetRowEulerCalibrationInput K c) c.geometry u Z
      (((targetData K c).expansion Z T).block b).bin P.e
      (P.contourHeight Z T b) theta N (code Z T b label)
      (P.bin_range Z T (hZ0.trans hZ) hT b).1
      ((P.bin_range Z T (hZ0.trans hZ) hT b).2.trans c.family.B_upper)
      P.e_pos (presentation_e_small K c P)

end HeckeSkeleton.HighBinNormFormRegionTarget

#print axioms HighBinVerified.NormFormRegionCalibration.actualRegionPieceWithEuler_eq_of_calibrated
#print axioms HeckeSkeleton.HighBinNormFormRegionTarget.exists_target_highShiftedNormForm_calibrated_region_connection
