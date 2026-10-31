import HeckeSkeleton.HighBinSupport.ActualBoundaryGeometry
import HeckeSkeleton.HighBinSupport.ActualBoundaryEstimate
import HeckeSkeleton.HighBinSupport.BoundaryHeightAbsorption
import HeckeSkeleton.HighBinSupport.HighNormFormHeight

/-!
# Boundary tails for the constructed detector partition

The actual row partition is constructed in `ActualBoundaryGeometry`.
Its detector runs at twice the actual internal height, so the contour
height is exactly `max T (Z^kappa)`. Every retained piece has a genuine
buffered upper detector and the number of pieces has an explicit bound.

The main theorem proves an arbitrary-order external tail for this
constructed family. It takes no presentation, block-count, contour-height,
or individual boundary-estimate hypothesis. The common packet boundary
remains the old boundary used to construct the actual detector.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinCanonicalBoundary

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HighBinDetectorGeometry
open HeckeSkeleton.HighBinActualBoundaryGeometry
open HighBinBoundary.ActualEstimate
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The entire actual nonprincipal shell, before selecting detector data. -/
def shellRows (Z d : ℝ) : Finset (FrequencyRow K S) :=
  (frequencyRows K S (2 * Z ^ d)).filter fun u =>
    Z ^ d < frequencyRowNorm K S u ∧ ¬ principalFrequencyRow K S u

theorem shellRows_subset (Z d : ℝ) :
    shellRows K S Z d ⊆ frequencyRows K S (2 * Z ^ d) := Finset.filter_subset _ _

theorem shellRows_lower (Z d : ℝ) (u : FrequencyRow K S)
    (hu : u ∈ shellRows K S Z d) : Z ^ d < frequencyRowNorm K S u :=
  (Finset.mem_filter.mp hu).2.1

theorem shellRows_nonprincipal (Z d : ℝ) (u : FrequencyRow K S)
    (hu : u ∈ shellRows K S Z d) : ¬ principalFrequencyRow K S u :=
  (Finset.mem_filter.mp hu).2.2

/-- Intersect the original full shell with a supplied finite arithmetic
source. This preserves a global moderate cutoff in the final shell. -/
def maskedShellRows (source : Finset (FrequencyRow K S)) (Z d : ℝ) :
    Finset (FrequencyRow K S) :=
  (shellRows K S Z d).filter fun u => u ∈ source

theorem maskedShellRows_subset_shell (source : Finset (FrequencyRow K S)) (Z d : ℝ) :
    maskedShellRows K S source Z d ⊆ shellRows K S Z d := Finset.filter_subset _ _

theorem maskedShellRows_subset_source (source : Finset (FrequencyRow K S)) (Z d : ℝ) :
    maskedShellRows K S source Z d ⊆ source := by
  intro u hu
  exact (Finset.mem_filter.mp hu).2

theorem maskedShellRows_subset (source : Finset (FrequencyRow K S)) (Z d : ℝ) :
    maskedShellRows K S source Z d ⊆ frequencyRows K S (2 * Z ^ d) :=
  (maskedShellRows_subset_shell K S source Z d).trans (shellRows_subset K S Z d)

theorem maskedShellRows_lower (source : Finset (FrequencyRow K S)) (Z d : ℝ)
    (u : FrequencyRow K S) (hu : u ∈ maskedShellRows K S source Z d) :
    Z ^ d < frequencyRowNorm K S u :=
  shellRows_lower K S Z d u (maskedShellRows_subset_shell K S source Z d hu)

theorem maskedShellRows_nonprincipal (source : Finset (FrequencyRow K S)) (Z d : ℝ)
    (u : FrequencyRow K S) (hu : u ∈ maskedShellRows K S source Z d) :
    ¬ principalFrequencyRow K S u :=
  shellRows_nonprincipal K S Z d u (maskedShellRows_subset_shell K S source Z d hu)

@[simp] theorem maskedShellRows_self (Z d : ℝ) :
    maskedShellRows K S (shellRows K S Z d) Z d = shellRows K S Z d := by
  ext u
  simp only [maskedShellRows, Finset.mem_filter, and_self]

/-- The same constructed height schedule meets both the boundary
buffer and the stronger norm-form buffer. -/
theorem internal_detector_geometry (Z T κ : ℝ) (hT : 1 ≤ T) (i : ℕ) :
    contourHeight (2 * HighBinVerified.NormForm.internalHeight Z T κ) =
        HighBinVerified.NormForm.internalHeight Z T κ ∧
      T ≤ HighBinVerified.NormForm.internalHeight Z T κ ∧
      2 * HighBinVerified.NormForm.internalHeight Z T κ + 2 ≤
        upperHeight (2 * HighBinVerified.NormForm.internalHeight Z T κ) i := by
  let H := HighBinVerified.NormForm.internalHeight Z T κ
  have hH : 1 ≤ H := hT.trans (HighBinVerified.NormForm.le_internalHeight Z T κ)
  have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  have hiH : 0 ≤ (i : ℝ) * H := mul_nonneg hi (by linarith)
  refine ⟨?_, HighBinVerified.NormForm.le_internalHeight Z T κ, ?_⟩
  · dsimp [contourHeight]
    ring
  · change 2 * H + 2 ≤ upperHeight (2 * H) i
    dsimp [upperHeight]
    nlinarith

end HeckeSkeleton.HighBinCanonicalBoundary

namespace HeckeSkeleton.HighBinCanonicalBoundary

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HighBinDetectorGeometry
open HeckeSkeleton.HighBinActualBoundaryGeometry
open HighBinBoundary.ActualEstimate
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S₀" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : (S : Set (HeightOneSpectrum (𝓞 K)))) → Measure (p.val.adicCompletion K))
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), (μ p).IsAddHaarMeasure]

/-- One initial-minus-final contour difference for the selected actual
row fiber. Both contours use exactly the same fixed arithmetic rows. -/
def boundaryPiece (P : ProbeData K S₀) (ψ : HeckeCharacter K)
    (Θ : Finset (HeckeCharacter K)) (g : PrimeWindowGeometry)
    (B e : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S₀, ∀ height : ℝ,
      rowZeroBelow K S₀ ψ Θ P (arithmeticHighEulerData K S₀ P ψ) u height B)
    (ray : Finset (HeckeCharacter K)) (Z T κ d : ℝ)
    (k : DetectorIndex (detectorDepth e)) : ℂ :=
  let H := HighBinVerified.NormForm.internalHeight Z T κ
  let R := assignedRows K S₀ P ψ Θ (arithmeticHighEulerData K S₀ P ψ)
    B e (2 * H) he hB hcommon (shellRows K S₀ Z d) k
  let a := gridRealPart e k.2.val
  (∑ u ∈ R, rowContourBox K S₀ μ P ψ (arithmeticHighEulerData K S₀ P ψ)
    g ray u Z H (B + 20 * e) (1 - a - 6 * e) (17 / 50)) -
  (∑ u ∈ R, rowContourBox K S₀ μ P ψ (arithmeticHighEulerData K S₀ P ψ)
    g ray u Z H (a + 16 * e) (1 - a - 6 * e) (17 / 50))

/-- The genuine whole boundary of the finite detector partition in one
dyadic shell. Empty selector fibers are omitted explicitly. -/
def shellBoundary (P : ProbeData K S₀) (ψ : HeckeCharacter K)
    (Θ : Finset (HeckeCharacter K)) (g : PrimeWindowGeometry)
    (B e : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S₀, ∀ height : ℝ,
      rowZeroBelow K S₀ ψ Θ P (arithmeticHighEulerData K S₀ P ψ) u height B)
    (ray : Finset (HeckeCharacter K)) (Z T κ d : ℝ) : ℂ :=
  ∑ k ∈ retainedChoices K S₀ P ψ Θ (arithmeticHighEulerData K S₀ P ψ)
    B e (2 * HighBinVerified.NormForm.internalHeight Z T κ) he hB hcommon
    (shellRows K S₀ Z d),
      boundaryPiece K S μ P ψ Θ g B e he hB hcommon ray Z T κ d k

/-- The same contour difference with a literal finite source mask. The
mask is held fixed throughout the move and the detector partition. -/
def maskedBoundaryPiece (P : ProbeData K S₀) (ψ : HeckeCharacter K)
    (Θ : Finset (HeckeCharacter K)) (g : PrimeWindowGeometry)
    (B e : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S₀, ∀ height : ℝ,
      rowZeroBelow K S₀ ψ Θ P (arithmeticHighEulerData K S₀ P ψ) u height B)
    (ray : Finset (HeckeCharacter K)) (source : Finset (FrequencyRow K S₀))
    (Z T κ d : ℝ) (k : DetectorIndex (detectorDepth e)) : ℂ :=
  let H := HighBinVerified.NormForm.internalHeight Z T κ
  let R := assignedRows K S₀ P ψ Θ (arithmeticHighEulerData K S₀ P ψ)
    B e (2 * H) he hB hcommon (maskedShellRows K S₀ source Z d) k
  let a := gridRealPart e k.2.val
  (∑ u ∈ R, rowContourBox K S₀ μ P ψ (arithmeticHighEulerData K S₀ P ψ)
    g ray u Z H (B + 20 * e) (1 - a - 6 * e) (17 / 50)) -
  (∑ u ∈ R, rowContourBox K S₀ μ P ψ (arithmeticHighEulerData K S₀ P ψ)
    g ray u Z H (a + 16 * e) (1 - a - 6 * e) (17 / 50))

def maskedShellBoundary (P : ProbeData K S₀) (ψ : HeckeCharacter K)
    (Θ : Finset (HeckeCharacter K)) (g : PrimeWindowGeometry)
    (B e : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S₀, ∀ height : ℝ,
      rowZeroBelow K S₀ ψ Θ P (arithmeticHighEulerData K S₀ P ψ) u height B)
    (ray : Finset (HeckeCharacter K)) (source : Finset (FrequencyRow K S₀))
    (Z T κ d : ℝ) : ℂ :=
  ∑ k ∈ retainedChoices K S₀ P ψ Θ (arithmeticHighEulerData K S₀ P ψ)
    B e (2 * HighBinVerified.NormForm.internalHeight Z T κ) he hB hcommon
    (maskedShellRows K S₀ source Z d),
      maskedBoundaryPiece K S μ P ψ Θ g B e he hB hcommon ray source Z T κ d k

/-- The actual contour difference for one row at its canonical detector
choice. The `w` line depends on that choice. The expression is independent
of the shell and source mask containing the row. -/
def rowBoundaryAtChoice (P : ProbeData K S₀) (ψ : HeckeCharacter K)
    (Θ : Finset (HeckeCharacter K)) (g : PrimeWindowGeometry)
    (B e : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S₀, ∀ height : ℝ,
      rowZeroBelow K S₀ ψ Θ P (arithmeticHighEulerData K S₀ P ψ) u height B)
    (ray : Finset (HeckeCharacter K)) (Z T κ : ℝ) (u : FrequencyRow K S₀) : ℂ :=
  let H := HighBinVerified.NormForm.internalHeight Z T κ
  let k := detectorChoice K S₀ P ψ Θ (arithmeticHighEulerData K S₀ P ψ)
    B e (2 * H) he hB hcommon u
  let a := gridRealPart e k.2.val
  rowContourBox K S₀ μ P ψ (arithmeticHighEulerData K S₀ P ψ)
    g ray u Z H (B + 20 * e) (1 - a - 6 * e) (17 / 50) -
  rowContourBox K S₀ μ P ψ (arithmeticHighEulerData K S₀ P ψ)
    g ray u Z H (a + 16 * e) (1 - a - 6 * e) (17 / 50)

/-- The shell boundary is exactly the sum of its original row contour
differences, including each row's chosen `w` line. No constancy across
different detector indices is used. -/
theorem maskedShellBoundary_eq_rowSum (P : ProbeData K S₀) (ψ : HeckeCharacter K)
    (Θ : Finset (HeckeCharacter K)) (g : PrimeWindowGeometry)
    (B e : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S₀, ∀ height : ℝ,
      rowZeroBelow K S₀ ψ Θ P (arithmeticHighEulerData K S₀ P ψ) u height B)
    (ray : Finset (HeckeCharacter K)) (source : Finset (FrequencyRow K S₀))
    (Z T κ d : ℝ) :
    maskedShellBoundary K S μ P ψ Θ g B e he hB hcommon ray source Z T κ d =
      ∑ u ∈ maskedShellRows K S₀ source Z d,
        rowBoundaryAtChoice K S μ P ψ Θ g B e he hB hcommon ray Z T κ u := by
  unfold maskedShellBoundary maskedBoundaryPiece rowBoundaryAtChoice
  simp_rw [← Finset.sum_sub_distrib]
  exact sum_retainedChoices_indexed K S₀ P ψ Θ (arithmeticHighEulerData K S₀ P ψ)
    B e (2 * HighBinVerified.NormForm.internalHeight Z T κ) he hB hcommon
    (maskedShellRows K S₀ source Z d) (fun k u =>
      rowContourBox K S₀ μ P ψ (arithmeticHighEulerData K S₀ P ψ) g ray u Z
        (HighBinVerified.NormForm.internalHeight Z T κ)
        (B + 20 * e) (1 - gridRealPart e k.2.val - 6 * e) (17 / 50) -
      rowContourBox K S₀ μ P ψ (arithmeticHighEulerData K S₀ P ψ) g ray u Z
        (HighBinVerified.NormForm.internalHeight Z T κ)
        (gridRealPart e k.2.val + 16 * e) (1 - gridRealPart e k.2.val - 6 * e) (17 / 50))

theorem maskedShellBoundary_full_eq (P : ProbeData K S₀) (ψ : HeckeCharacter K)
    (Θ : Finset (HeckeCharacter K)) (g : PrimeWindowGeometry)
    (B e : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S₀, ∀ height : ℝ,
      rowZeroBelow K S₀ ψ Θ P (arithmeticHighEulerData K S₀ P ψ) u height B)
    (ray : Finset (HeckeCharacter K)) (Z T κ d : ℝ) :
    maskedShellBoundary K S μ P ψ Θ g B e he hB hcommon ray (shellRows K S₀ Z d)
      Z T κ d = shellBoundary K S μ P ψ Θ g B e he hB hcommon ray Z T κ d := by
  simp only [maskedShellBoundary, shellBoundary, maskedBoundaryPiece, boundaryPiece,
    maskedShellRows_self]

/-- The finite arithmetic detector partition has arbitrary external
tail order. The scale exponent is 13; the height exponent is zero.
The threshold precedes the decay order, and the estimate is uniform in
the shell, ray filter and internal-height exponent.

All geometric and counting information is supplied by the constructed
finite detector, rather than added as a hypothesis. -/
theorem exists_maskedShellBoundary_external_tail
    (P : ProbeData K S₀) (ψ : HeckeCharacter K)
    (Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ) (g : PrimeWindowGeometry)
    (B e : ℝ) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hB : 51 / 100 ≤ B) (hB1 : B ≤ 1)
    (hcommon : ∀ u : FrequencyRow K S₀, ∀ height : ℝ,
      rowZeroBelow K S₀ ψ Θ P (arithmeticHighEulerData K S₀ P ψ) u height B) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (ray : Finset (HeckeCharacter K)) (source : Finset (FrequencyRow K S₀))
        (Z T κ d : ℝ),
      Z₀ ≤ Z → 1 ≤ T → 1 / 16 ≤ d → d ≤ 1 →
      ‖maskedShellBoundary K S μ P ψ Θ g B e he hB hcommon ray source Z T κ d‖ ≤
        C * Z ^ 13 * T ^ (-(N : ℝ)) := by
  let m := detectorDepth e
  let q := HighBinBoundary.ActualLRatioStrip.boundaryHeightDegree K
  obtain ⟨Z₀, hZ₀, hb⟩ := exists_arithmetic_fixedRows_external_tail
    K S μ P ψ Θ hΘ g he he1
  refine ⟨Z₀, hZ₀, ?_⟩
  intro N
  obtain ⟨C, hC, hfixed⟩ := hb (N + q)
  let D : ℝ := C * (5 : ℝ) ^ q
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨((m + 1 : ℕ) : ℝ) ^ 2 * D, by positivity, ?_⟩
  intro ray source Z T κ d hZ hT hd hd1
  let H := HighBinVerified.NormForm.internalHeight Z T κ
  let E := arithmeticHighEulerData K S₀ P ψ
  let R := maskedShellRows K S₀ source Z d
  let choices := retainedChoices K S₀ P ψ Θ E B e (2 * H) he hB hcommon R
  have hH : 1 ≤ H := hT.trans (HighBinVerified.NormForm.le_internalHeight Z T κ)
  have hTH : T ≤ H := HighBinVerified.NormForm.le_internalHeight Z T κ
  have hZ0 : 0 ≤ Z := zero_le_one.trans (hZ₀.trans hZ)
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hpiece : ∀ k ∈ choices,
      ‖maskedBoundaryPiece K S μ P ψ Θ g B e he hB hcommon ray source Z T κ d k‖ ≤
        D * Z ^ 13 * T ^ (-(N : ℝ)) := by
    intro k hk
    let rows := assignedRows K S₀ P ψ Θ E B e (2 * H) he hB hcommon R k
    let a := gridRealPart e k.2.val
    obtain ⟨u, hu⟩ : rows.Nonempty := (Finset.mem_filter.mp hk).2
    have hspec := assignedRows_detectorSpec K S₀ P ψ Θ E B e (2 * H)
      he hB hcommon R k u hu
    have ha : 51 / 100 ≤ a := hspec.1
    have haB : a ≤ B := hspec.2.1
    have hsub : rows ⊆ R := assignedRows_subset K S₀ P ψ Θ E B e (2 * H)
      he hB hcommon R k
    have hrows : rows ⊆ frequencyRows K S₀ (2 * Z ^ d) :=
      hsub.trans (maskedShellRows_subset K S₀ source Z d)
    have hlower : ∀ u ∈ rows, Z ^ d ≤ frequencyRowNorm K S₀ u := by
      intro u hu
      exact (maskedShellRows_lower K S₀ source Z d u (hsub hu)).le
    have hgap : H + 3 / 2 ≤ upperHeight (2 * H) k.1.val := by
      have hg := (contourHeight_geometry (2 * H) (by linarith) k.1.val).2
      have heqH : contourHeight (2 * H) = H := by dsimp [contourHeight]; ring
      simpa only [heqH] using hg
    have hbelow : ∀ u ∈ rows, rowZeroBelow K S₀ ψ Θ P E u
        (H + 3 / 2) (a + 2 * e) := by
      intro u hu χ hχ ρ hρ hρ0 hρ1 hheight
      have hs := assignedRows_detectorSpec K S₀ P ψ Θ E B e (2 * H)
        he hB hcommon R k u hu
      exact hs.2.2.2 χ hχ ρ hρ hρ0 hρ1 (hheight.trans hgap)
    have hp := hfixed ray Z hZ d hd hd1 rows hrows hlower a B H (H + 3 / 2) H
      ha haB hB1 hH le_rfl le_rfl hbelow
    have hp' : ‖maskedBoundaryPiece K S μ P ψ Θ g B e he hB hcommon ray source Z T κ d k‖ ≤
        C * Z ^ 13 * (H + 7 / 2) ^ q * H ^ (-((N + q : ℕ) : ℝ)) := by
      have heq : 2 + (H + 3 / 2) = H + 7 / 2 := by ring
      rw [heq] at hp
      simpa only [maskedBoundaryPiece, H, rows, R, E, a, q] using hp
    have habs := HighBinBoundary.height_tail_absorption_external H 1 T N q hH
      (by norm_num) (zero_lt_one.trans_le hT) (by simpa only [one_mul] using hTH)
    simp only [Real.one_rpow, mul_one] at habs
    apply hp'.trans
    calc
      _ = C * Z ^ 13 * ((H + 7 / 2) ^ q * H ^ (-((N + q : ℕ) : ℝ))) := by ring
      _ ≤ C * Z ^ 13 * ((5 : ℝ) ^ q * T ^ (-(N : ℝ))) :=
        mul_le_mul_of_nonneg_left habs (by positivity)
      _ = D * Z ^ 13 * T ^ (-(N : ℝ)) := by dsimp [D]; ring
  have hcard : (choices.card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast retainedChoices_card K S₀ P ψ Θ E B e (2 * H) he hB hcommon R
  change ‖∑ k ∈ choices,
    maskedBoundaryPiece K S μ P ψ Θ g B e he hB hcommon ray source Z T κ d k‖ ≤ _
  calc
    _ ≤ ∑ k ∈ choices,
        ‖maskedBoundaryPiece K S μ P ψ Θ g B e he hB hcommon ray source Z T κ d k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ choices, D * Z ^ 13 * T ^ (-(N : ℝ)) := Finset.sum_le_sum hpiece
    _ = (choices.card : ℝ) * (D * Z ^ 13 * T ^ (-(N : ℝ))) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((m + 1 : ℕ) : ℝ) ^ 2 * (D * Z ^ 13 * T ^ (-(N : ℝ))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-- The unmasked shell is the specialization to its own finite source. -/
theorem exists_shellBoundary_external_tail
    (P : ProbeData K S₀) (ψ : HeckeCharacter K)
    (Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ) (g : PrimeWindowGeometry)
    (B e : ℝ) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hB : 51 / 100 ≤ B) (hB1 : B ≤ 1)
    (hcommon : ∀ u : FrequencyRow K S₀, ∀ height : ℝ,
      rowZeroBelow K S₀ ψ Θ P (arithmeticHighEulerData K S₀ P ψ) u height B) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (ray : Finset (HeckeCharacter K)) (Z T κ d : ℝ),
      Z₀ ≤ Z → 1 ≤ T → 1 / 16 ≤ d → d ≤ 1 →
      ‖shellBoundary K S μ P ψ Θ g B e he hB hcommon ray Z T κ d‖ ≤
        C * Z ^ 13 * T ^ (-(N : ℝ)) := by
  obtain ⟨Z₀, hZ₀, hb⟩ := exists_maskedShellBoundary_external_tail
    K S μ P ψ Θ hΘ g B e he he1 hB hB1 hcommon
  refine ⟨Z₀, hZ₀, ?_⟩
  intro N
  obtain ⟨C, hC, h⟩ := hb N
  refine ⟨C, hC, ?_⟩
  intro ray Z T κ d hZ hT hd hd1
  simpa only [maskedShellBoundary_full_eq] using
    h ray (shellRows K S₀ Z d) Z T κ d hZ hT hd hd1

end HeckeSkeleton.HighBinCanonicalBoundary
