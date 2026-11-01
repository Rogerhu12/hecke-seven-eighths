import HeckeSkeleton.HighBinSupport.ActualDetectorBoundary
import HeckeSkeleton.HighBinSupport.ActualNormFormComputedPacket

/-!
Canonical HIGHBIN blocks from the actual detector partition and the
actual restricted-height integrals. The row selector is exactly the one
used by `ActualDetectorBoundary`; the initial/final boundary and the
norm-form packet therefore use the same fixed finite row fibers.

All amplitude means and individual pieces are definitions. The main
norm theorem constructs one grid and one internal-height exponent before
scales, shells, detector choices and witness recipes. It supplies every
retained block's quarter-loss norm form without a presentation-identity
assumption. The witness recipes remain explicit data; their cover and
moment calibration belong to the source construction.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinCanonical

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.TIP
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HighBinDetectorGeometry
open HeckeSkeleton.HighBinActualBoundaryGeometry HeckeSkeleton.HighBinCanonicalBoundary
open HighBinVerified HighBinVerified.NormFormRegions
open HighBinVerified.NormFormRegionIntegral HighBinVerified.NormFormRegionPacket
open HighBinVerified.NormFormComputedPacket
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (psi : HeckeCharacter K)
variable (companions : Finset (HeckeCharacter K))
variable (R : Finset (FrequencyRow K S))
variable (B e : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
variable (hcommon : ∀ u : FrequencyRow K S, ∀ height : ℝ,
  rowZeroBelow K S psi companions P (arithmeticHighEulerData K S P psi) u height B)

/-- The literal assigned row fiber at twice the internal contour height. -/
def canonicalRows (Z T kappa d : ℝ) (k : DetectorIndex (detectorDepth e)) :
    Finset (FrequencyRow K S) :=
  assignedRows K S P psi companions (arithmeticHighEulerData K S P psi)
    B e (2 * NormForm.internalHeight Z T kappa) he hB hcommon (maskedShellRows K S R Z d) k

/-- Retain exactly the nonempty original detector fibers. -/
def canonicalChoices (Z T kappa d : ℝ) : Finset (DetectorIndex (detectorDepth e)) :=
  retainedChoices K S P psi companions (arithmeticHighEulerData K S P psi)
    B e (2 * NormForm.internalHeight Z T kappa) he hB hcommon (maskedShellRows K S R Z d)

abbrev CanonicalBlockIndex (Z T kappa d : ℝ) :=
  ↥(canonicalChoices K S P psi companions R B e he hB hcommon Z T kappa d)

theorem canonicalRows_subset_shell (Z T kappa d : ℝ)
    (k : DetectorIndex (detectorDepth e)) :
    canonicalRows K S P psi companions R B e he hB hcommon Z T kappa d k ⊆
      shellRows K S Z d := by
  intro u hu
  have hm := assignedRows_subset K S P psi companions (arithmeticHighEulerData K S P psi)
    B e (2 * NormForm.internalHeight Z T kappa) he hB hcommon (maskedShellRows K S R Z d) k hu
  exact (Finset.mem_filter.mp hm).1

theorem canonicalRows_subset_source (Z T kappa d : ℝ)
    (k : DetectorIndex (detectorDepth e)) :
    canonicalRows K S P psi companions R B e he hB hcommon Z T kappa d k ⊆ R := by
  intro u hu
  have hm := assignedRows_subset K S P psi companions (arithmeticHighEulerData K S P psi)
    B e (2 * NormForm.internalHeight Z T kappa) he hB hcommon (maskedShellRows K S R Z d) k hu
  exact (Finset.mem_filter.mp hm).2

/-- A mask containing the whole shell recovers the original full-shell
detector fiber exactly. -/
theorem canonicalRows_eq_unmasked (Z T kappa d : ℝ)
    (k : DetectorIndex (detectorDepth e)) (hR : shellRows K S Z d ⊆ R) :
    canonicalRows K S P psi companions R B e he hB hcommon Z T kappa d k =
      assignedRows K S P psi companions (arithmeticHighEulerData K S P psi)
        B e (2 * NormForm.internalHeight Z T kappa) he hB hcommon (shellRows K S Z d) k := by
  have hm : maskedShellRows K S R Z d = shellRows K S Z d := by
    exact Finset.filter_eq_self.mpr hR
  simp only [canonicalRows, hm]

theorem canonicalRows_fullShell (Z T kappa d : ℝ)
    (k : DetectorIndex (detectorDepth e)) :
    canonicalRows K S P psi companions (frequencyRows K S (2 * Z ^ d))
      B e he hB hcommon Z T kappa d k =
      assignedRows K S P psi companions (arithmeticHighEulerData K S P psi)
        B e (2 * NormForm.internalHeight Z T kappa) he hB hcommon (shellRows K S Z d) k :=
  canonicalRows_eq_unmasked K S P psi companions (frequencyRows K S (2 * Z ^ d))
    B e he hB hcommon Z T kappa d k (shellRows_subset K S Z d)

theorem canonicalRows_envelope (Z T kappa d : ℝ)
    (k : DetectorIndex (detectorDepth e)) :
    canonicalRows K S P psi companions R B e he hB hcommon Z T kappa d k ⊆
      frequencyRows K S (2 * Z ^ d) :=
  (canonicalRows_subset_shell K S P psi companions R B e he hB hcommon Z T kappa d k).trans
    (shellRows_subset K S Z d)

theorem canonicalRows_lower (Z T kappa d : ℝ)
    (k : DetectorIndex (detectorDepth e)) (u : FrequencyRow K S)
    (hu : u ∈ canonicalRows K S P psi companions R B e he hB hcommon Z T kappa d k) :
    Z ^ d < frequencyRowNorm K S u :=
  shellRows_lower K S Z d u
    (canonicalRows_subset_shell K S P psi companions R B e he hB hcommon Z T kappa d k hu)

theorem canonicalRows_nonprincipal (Z T kappa d : ℝ)
    (k : DetectorIndex (detectorDepth e)) (u : FrequencyRow K S)
    (hu : u ∈ canonicalRows K S P psi companions R B e he hB hcommon Z T kappa d k) :
    ¬ principalFrequencyRow K S u :=
  shellRows_nonprincipal K S Z d u
    (canonicalRows_subset_shell K S P psi companions R B e he hB hcommon Z T kappa d k hu)

theorem canonicalRows_detectorSpec (Z T kappa d : ℝ)
    (k : DetectorIndex (detectorDepth e)) (u : FrequencyRow K S)
    (hu : u ∈ canonicalRows K S P psi companions R B e he hB hcommon Z T kappa d k) :
    DetectorSpec K S P psi companions (arithmeticHighEulerData K S P psi)
      B e (2 * NormForm.internalHeight Z T kappa) u k :=
  assignedRows_detectorSpec K S P psi companions (arithmeticHighEulerData K S P psi)
    B e (2 * NormForm.internalHeight Z T kappa) he hB hcommon (maskedShellRows K S R Z d) k u hu

theorem canonicalRows_nonempty (Z T kappa d : ℝ)
    (k : CanonicalBlockIndex K S P psi companions R B e he hB hcommon Z T kappa d) :
    (canonicalRows K S P psi companions R B e he hB hcommon Z T kappa d k.val).Nonempty :=
  (Finset.mem_filter.mp k.property).2

theorem canonicalBin_bounds (Z T kappa d : ℝ)
    (k : CanonicalBlockIndex K S P psi companions R B e he hB hcommon Z T kappa d) :
    51 / 100 ≤ gridRealPart e k.val.2.val ∧ gridRealPart e k.val.2.val ≤ B := by
  obtain ⟨u, hu⟩ := canonicalRows_nonempty K S P psi companions R B e he hB hcommon Z T kappa d k
  have hs := canonicalRows_detectorSpec K S P psi companions R B e he hB hcommon
    Z T kappa d k.val u hu
  exact ⟨hs.1, hs.2.1⟩

theorem canonicalChoices_card (Z T kappa d : ℝ) :
    (canonicalChoices K S P psi companions R B e he hB hcommon Z T kappa d).card ≤
      (detectorDepth e + 1) ^ 2 :=
  retainedChoices_card K S P psi companions (arithmeticHighEulerData K S P psi)
    B e (2 * NormForm.internalHeight Z T kappa) he hB hcommon (maskedShellRows K S R Z d)

/-- Every retained row meets the exact norm-form detector buffer. The
upper height is the one selected by the common finite detector. -/
theorem canonicalRows_normForm_data (Z T kappa d : ℝ) (hZ : 1 ≤ Z) (hT : 1 ≤ T)
    (k : DetectorIndex (detectorDepth e)) (u : FrequencyRow K S)
    (hu : u ∈ canonicalRows K S P psi companions R B e he hB hcommon Z T kappa d k) :
    Z ^ d ≤ frequencyRowNorm K S u ∧
      frequencyRowNorm K S u ≤ 2 * Z ^ d ∧
      rowZeroBelow K S psi companions P (arithmeticHighEulerData K S P psi) u
        (2 * NormForm.internalHeight Z T kappa + 2) (gridRealPart e k.2.val + 2 * e) := by
  refine ⟨(canonicalRows_lower K S P psi companions R B e he hB hcommon
    Z T kappa d k u hu).le, ?_, ?_⟩
  · exact HighBinBoundary.ActualEstimate.frequencyRowNorm_le_of_mem_rows K S
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (zero_le_one.trans hZ) _)) u
      (canonicalRows_envelope K S P psi companions R B e he hB hcommon Z T kappa d k hu)
  · have hdet := (canonicalRows_detectorSpec K S P psi companions R B e he hB hcommon
      Z T kappa d k u hu).2.2.2
    have hheight := (internal_detector_geometry Z T kappa hT k.1.val).2.2
    intro chi hchi rho hrho hlo hhi him
    exact hdet chi hchi rho hrho hlo hhi (him.trans hheight)

end HeckeSkeleton.HighBinCanonical

namespace HeckeSkeleton.HighBinCanonical

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.TIP
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HighBinDetectorGeometry
open HeckeSkeleton.HighBinActualBoundaryGeometry HeckeSkeleton.HighBinCanonicalBoundary
open HighBinVerified HighBinVerified.NormFormRegions
open HighBinVerified.NormFormRegionIntegral HighBinVerified.NormFormRegionPacket
open HighBinVerified.NormFormComputedPacket
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
variable (P : ProbeData K (S : Set (HeightOneSpectrum (𝓞 K)))) (psi : HeckeCharacter K)
variable (companions : Finset (HeckeCharacter K))
variable (R : Finset (FrequencyRow K (S : Set (HeightOneSpectrum (𝓞 K)))))
variable (B e : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
variable (hcommon : ∀ u : FrequencyRow K (S : Set (HeightOneSpectrum (𝓞 K))), ∀ height : ℝ,
  rowZeroBelow K (S : Set (HeightOneSpectrum (𝓞 K))) psi companions P
    (arithmeticHighEulerData K (S : Set (HeightOneSpectrum (𝓞 K))) P psi) u height B)

/-- The original ModerateBlock populated directly by the canonical
detector fiber and the literal restricted-height integrals. -/
def canonicalBlock (g : PrimeWindowGeometry) (Z T kappa d theta : ℝ) (N : ℕ)
    (k : CanonicalBlockIndex K S₀ P psi companions R B e he hB hcommon Z T kappa d)
    (subdivisionCount : (Fin g.slots → Fin (N + 1)) → ℝ → ℕ)
    (subdivision : (label : Fin g.slots → Fin (N + 1)) →
      (t : ℝ) → Fin (subdivisionCount label t) → WitnessSubdivision (FrequencyRow K S₀)) :
    ModerateBlock (FrequencyRow K S₀) g.slots :=
  computedRegionBlock K S μ P psi g
    (canonicalRows K S₀ P psi companions R B e he hB hcommon Z T kappa d k.val)
    Z d (gridRealPart e k.val.2.val) e (NormForm.internalHeight Z T kappa) theta N
    subdivisionCount subdivision

theorem canonicalBlock_shell_bin (g : PrimeWindowGeometry) (Z T kappa d theta : ℝ) (N : ℕ)
    (k : CanonicalBlockIndex K S₀ P psi companions R B e he hB hcommon Z T kappa d)
    (sc : (Fin g.slots → Fin (N + 1)) → ℝ → ℕ)
    (sub : (label : Fin g.slots → Fin (N + 1)) →
      (t : ℝ) → Fin (sc label t) → WitnessSubdivision (FrequencyRow K S₀)) :
    (canonicalBlock K S μ P psi companions R B e he hB hcommon g Z T kappa d theta N k sc sub).shell = d ∧
    (canonicalBlock K S μ P psi companions R B e he hB hcommon g Z T kappa d theta N k sc sub).bin =
      gridRealPart e k.val.2.val := ⟨rfl, rfl⟩

theorem canonicalBlock_mean (g : PrimeWindowGeometry) (Z T kappa d theta : ℝ) (N : ℕ)
    (k : CanonicalBlockIndex K S₀ P psi companions R B e he hB hcommon Z T kappa d)
    (sc : (Fin g.slots → Fin (N + 1)) → ℝ → ℕ)
    (sub : (label : Fin g.slots → Fin (N + 1)) →
      (t : ℝ) → Fin (sc label t) → WitnessSubdivision (FrequencyRow K S₀))
    (label : Fin g.slots → Fin (N + 1)) :
    ((canonicalBlock K S μ P psi companions R B e he hB hcommon g
      Z T kappa d theta N k sc sub).amplitudeSet label).mean =
      actualRegionMean g (gridRealPart e k.val.2.val) theta N label := rfl

theorem canonicalBlock_rows_envelope (g : PrimeWindowGeometry)
    (Z T kappa d theta : ℝ) (N : ℕ)
    (k : CanonicalBlockIndex K S₀ P psi companions R B e he hB hcommon Z T kappa d)
    (sc : (Fin g.slots → Fin (N + 1)) → ℝ → ℕ)
    (sub : (label : Fin g.slots → Fin (N + 1)) →
      (t : ℝ) → Fin (sc label t) → WitnessSubdivision (FrequencyRow K S₀))
    (label : Fin g.slots → Fin (N + 1)) :
    ((canonicalBlock K S μ P psi companions R B e he hB hcommon g
      Z T kappa d theta N k sc sub).amplitudeSet label).rows ⊆
      frequencyRows K S₀ (2 * Z ^ d) := by
  exact (actualRegionRows_subset K S P psi g _ Z (gridRealPart e k.val.2.val) e
      (NormForm.internalHeight Z T kappa) theta N label).trans
    ((integrableRows_subset K S μ P psi g _ Z (gridRealPart e k.val.2.val) e
      (NormForm.internalHeight Z T kappa)).trans
      (canonicalRows_envelope K S₀ P psi companions R B e he hB hcommon Z T kappa d k.val))

theorem canonicalBlock_rows_subset_source (g : PrimeWindowGeometry)
    (Z T kappa d theta : ℝ) (N : ℕ)
    (k : CanonicalBlockIndex K S₀ P psi companions R B e he hB hcommon Z T kappa d)
    (sc : (Fin g.slots → Fin (N + 1)) → ℝ → ℕ)
    (sub : (label : Fin g.slots → Fin (N + 1)) →
      (t : ℝ) → Fin (sc label t) → WitnessSubdivision (FrequencyRow K S₀))
    (label : Fin g.slots → Fin (N + 1)) :
    ((canonicalBlock K S μ P psi companions R B e he hB hcommon g
      Z T kappa d theta N k sc sub).amplitudeSet label).rows ⊆ R := by
  exact (actualRegionRows_subset K S P psi g _ Z (gridRealPart e k.val.2.val) e
      (NormForm.internalHeight Z T kappa) theta N label).trans
    ((integrableRows_subset K S μ P psi g _ Z (gridRealPart e k.val.2.val) e
      (NormForm.internalHeight Z T kappa)).trans
      (canonicalRows_subset_source K S₀ P psi companions R B e he hB hcommon Z T kappa d k.val))

/-- The individual piece identity is built into the canonical block,
so the actual finite integral identity is available at every scale. -/
theorem canonicalBlock_value_eq_pieces (g : PrimeWindowGeometry)
    (Z T kappa d theta : ℝ) (N : ℕ)
    (k : CanonicalBlockIndex K S₀ P psi companions R B e he hB hcommon Z T kappa d)
    (sc : (Fin g.slots → Fin (N + 1)) → ℝ → ℕ)
    (sub : (label : Fin g.slots → Fin (N + 1)) →
      (t : ℝ) → Fin (sc label t) → WitnessSubdivision (FrequencyRow K S₀)) :
    (canonicalBlock K S μ P psi companions R B e he hB hcommon g
      Z T kappa d theta N k sc sub).value =
      ∑ label : Fin g.slots → Fin (N + 1),
        ∑ u ∈ ((canonicalBlock K S μ P psi companions R B e he hB hcommon g
          Z T kappa d theta N k sc sub).amplitudeSet label).rows,
          actualRegionPiece K S μ P psi g u Z (gridRealPart e k.val.2.val) e
            (NormForm.internalHeight Z T kappa) theta N label :=
  computedRegionBlock_value_eq_pieces K S μ P psi g _ Z d (gridRealPart e k.val.2.val) e
    (NormForm.internalHeight Z T kappa) theta N sc sub (gridRealPart_lower e he.le _) he

/-- A canonical actual construction with the original norm-form exponent.
One grid and one height exponent serve all scales, shells, retained
detector choices, labels and supplied witness recipes. The conclusion
also proves that every original assigned row passes the integrability gate. -/
theorem exists_canonicalBlock_normForm
    (hcomp : (1 : HeckeCharacter K) ∈ companions) (g : PrimeWindowGeometry)
    (hcal : ThetaCalibrationInput K S₀ P.arithmetic P.Lambda P.G)
    (hpsi : ∀ p : ExteriorPrime K S₀, UnramifiedAt K psi p.val)
    (he1 : e ≤ 1 / 10000) (hB1 : B ≤ 1)
    {lam : ℝ} (hlam : 0 < lam) (heLam : e ≤ lam / 100) :
    ∃ kappa theta : ℝ, ∃ N : ℕ, ∃ C Z0 : ℝ,
      0 < kappa ∧ 0 < theta ∧ 0 < C ∧ 1 ≤ Z0 ∧
      ∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → d ≤ 1 →
      ∀ R : Finset (FrequencyRow K S₀),
      ∀ k : CanonicalBlockIndex K S₀ P psi companions R B e he hB hcommon Z T kappa d,
      let F := canonicalRows K S₀ P psi companions R B e he hB hcommon Z T kappa d k.val
      let a := gridRealPart e k.val.2.val
      integrableRows K S μ P psi g F Z a e (NormForm.internalHeight Z T kappa) = F ∧
      ∀ sc : (Fin g.slots → Fin (N + 1)) → ℝ → ℕ,
      ∀ sub : (label : Fin g.slots → Fin (N + 1)) →
        (t : ℝ) → Fin (sc label t) → WitnessSubdivision (FrequencyRow K S₀),
      let block := canonicalBlock K S μ P psi companions R B e he hB hcommon g
        Z T kappa d theta N k sc sub
      block.value = ∑ u ∈ F,
        rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
          (NormForm.internalHeight Z T kappa) (a + 16 * e) (1 - a - 6 * e) (17 / 50) ∧
      ∀ label : Fin g.slots → Fin (N + 1),
      (∀ u ∈ (block.amplitudeSet label).rows,
        ActualRegionSlotBounds K S₀ P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N label) ∧
      (∑ u ∈ (block.amplitudeSet label).rows,
        ‖actualRegionPiece K S μ P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N label‖) ≤
        C * ((block.amplitudeSet label).rows.card : ℝ) *
          Z ^ (3 / 16 + moderateExponent block.shell (2 * block.bin - 1)
            (block.amplitudeSet label).mean 0 + lam / 4) := by
  obtain ⟨kappa, theta, N, C, Z0, hkappa, htheta, hC, hZ0, hpacket⟩ :=
    exists_computedRegionBlock_normForm K S μ psi companions hcomp P g
      hcal hpsi he he1 hlam heLam
  refine ⟨kappa, theta, N, C, Z0, hkappa, htheta, hC, hZ0, ?_⟩
  intro Z T hZ hT hTcap d hd hd1 R k
  let F := canonicalRows K S₀ P psi companions R B e he hB hcommon Z T kappa d k.val
  let a := gridRealPart e k.val.2.val
  have ha := canonicalBin_bounds K S₀ P psi companions R B e he hB hcommon Z T kappa d k
  have hF := canonicalRows_normForm_data K S₀ P psi companions R B e he hB hcommon
    Z T kappa d (hZ0.trans hZ) hT k.val
  obtain ⟨hgate, hnorm⟩ := hpacket Z T hZ hT hTcap d hd hd1 a ha.1
    (ha.2.trans hB1) F hF
  refine ⟨hgate, ?_⟩
  intro sc sub
  constructor
  · change (∑ u ∈ integrableRows K S μ P psi g F Z a e
      (NormForm.internalHeight Z T kappa),
      rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
        (NormForm.internalHeight Z T kappa) (a + 16 * e) (1 - a - 6 * e) (17 / 50)) = _
    rw [hgate]
  · intro label
    obtain ⟨hslot, hb⟩ := hnorm sc sub label
    refine ⟨hslot, ?_⟩
    simpa only [NormForm.rowExponent_eq_moderate] using hb

end HeckeSkeleton.HighBinCanonical

#print axioms HeckeSkeleton.HighBinCanonical.canonicalRows_normForm_data
#print axioms HeckeSkeleton.HighBinCanonical.canonicalBlock_value_eq_pieces
#print axioms HeckeSkeleton.HighBinCanonical.exists_canonicalBlock_normForm
