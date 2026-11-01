import HeckeSkeleton.HighBin
import HeckeSkeleton.HighBinSupport.ActualBoundaryEstimate
import HeckeSkeleton.HighBinSupport.HighNormFormHeight
import HeckeSkeleton.HighBinSupport.BoundaryHeightAbsorption

/-!
# The actual whole-bin boundary and its remaining geometric data

This module applies the proved arithmetic fixed-row contour estimate to
the literal `wholeBinBoundary` in `HeckeSkeleton.HighBin`. The fixed bins,
all retained blocks, the original contour heights and the original
subtraction are retained.

The block identifications recover the original main-term/boundary
decomposition. The analytic estimate may shorten the upper-zero detector
without changing the fixed rows. Increasing the internal decay order then
absorbs the complete polynomial height cost. Lower height bounds, detector
coverage and the retained-block count yield the
repository's `HighBoundaryControl`. The named `actualHighPresentation` now uses the original raw recipe.
These general consumers retain its assigned `fixedRows`; the larger
zero-control bins are used only for membership and analytic estimates.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinBoundaryPresentation

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open HighBinBoundary.ActualEstimate
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

local instance presentationNormOneMeasurable (c : TargetContext K) :
    MeasurableSpace (sLocalNormOneGroup K
      ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :=
  (targetData K c).measures.normOneSpace

local instance presentationNormOneBorel (c : TargetContext K) :
    BorelSpace (sLocalNormOneGroup K
      ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :=
  (targetData K c).measures.normOneBorel

local instance presentationLocalMeasurable (c : TargetContext K)
    (p : ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :
    MeasurableSpace (p.val.adicCompletion K) :=
  (targetData K c).measures.localSpace p

local instance presentationLocalBorel (c : TargetContext K)
    (p : ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :
    BorelSpace (p.val.adicCompletion K) :=
  (targetData K c).measures.localBorel p

local instance presentationLocalHaar (c : TargetContext K)
    (p : ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :
    ((targetData K c).measures.haar p).IsAddHaarMeasure :=
  (targetData K c).measures.haar_isAddHaar p

/-- Both branches of the original fixed bin have the same actual norm
envelope, strict lower shell bound, and buffered upper-zero detector. -/
theorem highFixedRowBin_member_data (c : TargetContext K)
    (P : ProbeData K ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K))))
    (E : RowEulerData K _ P) (Θ : Finset (HeckeCharacter K))
    (selectedHeight upperHeight normLower normUpper a e : ℝ) (u : HighRow K c)
    (hu : u ∈ highFixedRowBin K c P E Θ
      selectedHeight upperHeight normLower normUpper a e) :
    u ∈ frequencyRows K _ normUpper ∧ normLower < frequencyRowNorm K _ u ∧
      rowZeroBelow K _ (targetCharacter K c) Θ P E u upperHeight (a + 2 * e) := by
  by_cases ha : a = 51 / 100
  · rw [highFixedRowBin, if_pos ha] at hu
    have h := Finset.mem_filter.mp hu
    exact ⟨h.1, h.2.1, h.2.2.2⟩
  · rw [highFixedRowBin, if_neg ha] at hu
    have h := (mem_bufferedPhysicalRowBin_iff K _ (targetCharacter K c) Θ P E
      selectedHeight upperHeight normLower normUpper a e u).mp hu
    exact ⟨h.1, h.2.1, h.2.2.2.2⟩

/-- The original presentation's smallness and shell fields already imply
the numerical ranges needed by the coarse arithmetic boundary theorem. -/
theorem presentation_e_small (c : TargetContext K) (P : ActualHighPresentation K c) :
    P.e ≤ 1 / 10000 := by
  linarith [P.e_small, min_le_left c.family.lamA c.lamB, c.family.lamA_small]

theorem presentation_shell_le_one (c : TargetContext K) (P : ActualHighPresentation K c)
    (Z T : ℝ) (hZ : 1 ≤ Z) (hT : 1 ≤ T) (b : HighBlockIndex K c Z T) :
    (((targetData K c).expansion Z T).block b).shell ≤ 1 := by
  linarith [(P.shell_range Z T hZ hT b).2, P.zeta_small]

/-- Exactly one summand of the repository's whole-bin boundary. This is
only an abbreviation of the original initial-minus-final assigned-row sum. -/
def presentationBoundaryPiece (c : TargetContext K) (P : ActualHighPresentation K c)
    (Z T : ℝ) (b : HighBlockIndex K c Z T) : ℂ :=
  (∑ u ∈ P.fixedRows Z T b,
    rowContourBox K _ (targetData K c).measures.haar (targetData K c).probe
      (targetCharacter K c) P.euler c.geometry (targetData K c).rayFilter u
      Z (P.contourHeight Z T b) (c.family.B + 20 * P.e)
      (1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e) (17 / 50)) -
  (∑ u ∈ P.fixedRows Z T b,
    rowContourBox K _ (targetData K c).measures.haar (targetData K c).probe
      (targetCharacter K c) P.euler c.geometry (targetData K c).rayFilter u
      Z (P.contourHeight Z T b)
      ((((targetData K c).expansion Z T).block b).bin + 16 * P.e)
      (1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e) (17 / 50))

theorem wholeBinBoundary_eq_sum (c : TargetContext K) (P : ActualHighPresentation K c)
    (Z T : ℝ) :
    wholeBinBoundary K c P Z T =
      ∑ b : HighBlockIndex K c Z T, presentationBoundaryPiece K c P Z T b := rfl

/-- The initial fixed-bin integral for one original retained block. -/
def presentationInitialBlock (c : TargetContext K) (P : ActualHighPresentation K c)
    (Z T : ℝ) (b : HighBlockIndex K c Z T) : ℂ :=
  ∑ u ∈ P.fixedRows Z T b,
    rowContourBox K _ (targetData K c).measures.haar (targetData K c).probe
      (targetCharacter K c) P.euler c.geometry (targetData K c).rayFilter u
      Z (P.contourHeight Z T b) (c.family.B + 20 * P.e)
      (1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e) (17 / 50)

/-- The original presentation identifies each block value with
the final contour on its unchanged assigned rows. No individual label-piece identity or
disjointness of its row labels is needed. -/
theorem presentationBlock_value_eq_finalRows
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (Z T : ℝ) (hZ : 1 ≤ Z) (hT : 1 ≤ T) (b : HighBlockIndex K c Z T) :
    (((targetData K c).expansion Z T).block b).value =
      ∑ u ∈ P.fixedRows Z T b,
        rowContourBox K _ (targetData K c).measures.haar (targetData K c).probe
          (targetCharacter K c) P.euler c.geometry (targetData K c).rayFilter u
          Z (P.contourHeight Z T b)
          ((((targetData K c).expansion Z T).block b).bin + 16 * P.e)
          (1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e) (17 / 50) :=
  (P.block_identification Z T hZ hT b).trans
    (P.shifted_identification Z T hZ hT b)

/-- The actual block main term and this same boundary reconstruct the
initial fixed-bin integral, with the original initial-minus-final sign. -/
theorem presentationInitialBlock_eq_value_add_boundary
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (Z T : ℝ) (hZ : 1 ≤ Z) (hT : 1 ≤ T) (b : HighBlockIndex K c Z T) :
    presentationInitialBlock K c P Z T b =
      (((targetData K c).expansion Z T).block b).value +
        presentationBoundaryPiece K c P Z T b := by
  rw [presentationBoundaryPiece,
    ← presentationBlock_value_eq_finalRows K c P Z T hZ hT b]
  unfold presentationInitialBlock
  ring

/-- Main-term/tail assembly for the complete original retained block
family. This follows only from the presentation fields and preserves
overlapping amplitude labels. It does not identify the expansion's other
principal, small, large or tail components. -/
theorem presentationInitialSum_eq_blocks_add_boundary
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (Z T : ℝ) (hZ : 1 ≤ Z) (hT : 1 ≤ T) :
    (∑ b : HighBlockIndex K c Z T, presentationInitialBlock K c P Z T b) =
      (∑ b : HighBlockIndex K c Z T, (((targetData K c).expansion Z T).block b).value) +
        wholeBinBoundary K c P Z T := by
  calc
    _ = ∑ b : HighBlockIndex K c Z T,
        ((((targetData K c).expansion Z T).block b).value +
          presentationBoundaryPiece K c P Z T b) :=
      Finset.sum_congr rfl (fun b _ =>
        presentationInitialBlock_eq_value_add_boundary K c P Z T hZ hT b)
    _ = _ := by rw [Finset.sum_add_distrib, ← wholeBinBoundary_eq_sum]

theorem wholeBinBoundary_eq_initialSum_sub_blocks
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (Z T : ℝ) (hZ : 1 ≤ Z) (hT : 1 ≤ T) :
    wholeBinBoundary K c P Z T =
      (∑ b : HighBlockIndex K c Z T, presentationInitialBlock K c P Z T b) -
        (∑ b : HighBlockIndex K c Z T, (((targetData K c).expansion Z T).block b).value) := by
  rw [presentationInitialSum_eq_blocks_add_boundary K c P Z T hZ hT]
  ring

/-- The fixed rows keep their original upper detector. For the analytic
estimate that detector can be shortened to any U still covering the
contour and its required buffer; the row set is not changed. -/
theorem exists_presentationBoundaryPiece_detector_tail
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c))
    (hcompanions : 1 ∈ P.companions) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ Z T : ℝ, Z₀ ≤ Z → 1 ≤ T → 1 ≤ δ * T → ∀ b : HighBlockIndex K c Z T,
      ∀ U : ℝ,
      δ * T ≤ P.contourHeight Z T b →
      P.contourHeight Z T b + 3 / 2 ≤ U → U ≤ P.upperHeight Z T b →
      ‖presentationBoundaryPiece K c P Z T b‖ ≤
        C * Z ^ 13 * (2 + U) ^
          HighBinBoundary.ActualLRatioStrip.boundaryHeightDegree K * T ^ (-(N : ℝ)) := by
  obtain ⟨Z₀, hZ₀, hb⟩ := exists_arithmetic_fixedRows_external_tail
    K (targetData K c).S (targetData K c).measures.haar (targetData K c).probe
    (targetCharacter K c) P.companions hcompanions c.geometry P.e_pos
    (presentation_e_small K c P)
  refine ⟨Z₀, hZ₀, ?_⟩
  intro N
  obtain ⟨C, hC, hfixed⟩ := hb N
  refine ⟨C * δ ^ (-(N : ℝ)), mul_pos hC (Real.rpow_pos_of_pos hδ _), ?_⟩
  intro Z T hZ hT hδT b U hTH hHU hU
  have hZ1 : 1 ≤ Z := hZ₀.trans hZ
  let d := (((targetData K c).expansion Z T).block b).shell
  let a := (((targetData K c).expansion Z T).block b).bin
  let R := P.fixedRows Z T b
  have hdata (u : HighRow K c) (hu : u ∈ R) := highFixedRowBin_member_data K c
    (targetData K c).probe P.euler P.companions (P.selectedHeight Z T b)
    (P.upperHeight Z T b) (Z ^ d) (2 * Z ^ d) a P.e u
    (P.fixedRows_in_bin Z T hZ1 hT b hu)
  have hR : R ⊆ frequencyRows K _ (2 * Z ^ d) := fun u hu => (hdata u hu).1
  have hlo : ∀ u ∈ R, Z ^ d ≤ frequencyRowNorm K _ u :=
    fun u hu => (hdata u hu).2.1.le
  have hbelow : ∀ u ∈ R, rowZeroBelow K _ (targetCharacter K c) P.companions
      (targetData K c).probe
      (HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
        (targetData K c).probe (targetCharacter K c))
      u U (a + 2 * P.e) := by
    intro u hu
    have hfull : rowZeroBelow K _ (targetCharacter K c) P.companions
        (targetData K c).probe
        (HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
          (targetData K c).probe (targetCharacter K c))
        u (P.upperHeight Z T b) (a + 2 * P.e) := by
      simpa only [← hEuler] using (hdata u hu).2.2
    intro χ hχ ρ hord hlo hhi him
    exact hfull χ hχ ρ hord hlo hhi (him.trans hU)
  have hbound := hfixed (targetData K c).rayFilter Z hZ d
    (P.shell_range Z T hZ1 hT b).1 (presentation_shell_le_one K c P Z T hZ1 hT b)
    R hR hlo a c.family.B (P.contourHeight Z T b) U (δ * T)
    (P.bin_range Z T hZ1 hT b).1 (P.bin_range Z T hZ1 hT b).2 c.family.B_upper
    hδT hTH hHU hbelow
  have hbound' : ‖presentationBoundaryPiece K c P Z T b‖ ≤
      C * Z ^ 13 * (2 + U) ^
        HighBinBoundary.ActualLRatioStrip.boundaryHeightDegree K * (δ * T) ^ (-(N : ℝ)) := by
    simpa only [presentationBoundaryPiece, R, d, a, ← hEuler] using hbound
  apply hbound'.trans_eq
  rw [Real.mul_rpow hδ.le (zero_le_one.trans hT)]
  ring

/-- The original upper-height form of the boundary estimate. -/
theorem exists_presentationBoundaryPiece_external_tail
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c))
    (hcompanions : 1 ∈ P.companions) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ Z T : ℝ, Z₀ ≤ Z → 1 ≤ T → 1 ≤ δ * T → ∀ b : HighBlockIndex K c Z T,
      δ * T ≤ P.contourHeight Z T b →
      P.contourHeight Z T b + 3 / 2 ≤ P.upperHeight Z T b →
      ‖presentationBoundaryPiece K c P Z T b‖ ≤
        C * Z ^ 13 * (2 + P.upperHeight Z T b) ^
          HighBinBoundary.ActualLRatioStrip.boundaryHeightDegree K * T ^ (-(N : ℝ)) := by
  obtain ⟨Z₀, hZ₀, hb⟩ :=
    exists_presentationBoundaryPiece_detector_tail K c P hEuler hcompanions δ hδ
  refine ⟨Z₀, hZ₀, ?_⟩
  intro N
  obtain ⟨C, hC, hp⟩ := hb N
  refine ⟨C, hC, ?_⟩
  intro Z T hZ hT hδT b hTH hHU
  exact hp Z T hZ hT hδT b (P.upperHeight Z T b) hTH hHU le_rfl

/-- The original detector need not have a polynomial upper bound.
Shortening it to H+3/2 leaves exactly the buffered rectangle required by
the contour theorem. Its polynomial cost is absorbed into (1+H)^k. -/
theorem exists_presentationBoundaryPiece_contourHeight_tail
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c))
    (hcompanions : 1 ∈ P.companions) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ Z T : ℝ, Z₀ ≤ Z → 1 ≤ T → 1 ≤ δ * T → ∀ b : HighBlockIndex K c Z T,
      δ * T ≤ P.contourHeight Z T b →
      P.contourHeight Z T b + 3 / 2 ≤ P.upperHeight Z T b →
      ‖presentationBoundaryPiece K c P Z T b‖ ≤
        C * Z ^ 13 * (1 + P.contourHeight Z T b) ^
          HighBinBoundary.ActualLRatioStrip.boundaryHeightDegree K * T ^ (-(N : ℝ)) := by
  let k : ℕ := HighBinBoundary.ActualLRatioStrip.boundaryHeightDegree K
  obtain ⟨Z₀, hZ₀, hb⟩ :=
    exists_presentationBoundaryPiece_detector_tail K c P hEuler hcompanions δ hδ
  refine ⟨Z₀, hZ₀, ?_⟩
  intro N
  obtain ⟨C, hC, hp⟩ := hb N
  refine ⟨C * (7 / 2 : ℝ) ^ k, by positivity, ?_⟩
  intro Z T hZ hT hδT b hTH hHU
  have hZnonneg : 0 ≤ Z := zero_le_one.trans (hZ₀.trans hZ)
  have hH : 0 ≤ P.contourHeight Z T b := by linarith
  have hbound := hp Z T hZ hT hδT b (P.contourHeight Z T b + 3 / 2)
    hTH le_rfl hHU
  have hheight : (2 + (P.contourHeight Z T b + 3 / 2)) ^ k ≤
      (7 / 2 : ℝ) ^ k * (1 + P.contourHeight Z T b) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by nlinarith) k
  calc
    _ ≤ C * Z ^ 13 * (2 + (P.contourHeight Z T b + 3 / 2)) ^ k *
        T ^ (-(N : ℝ)) := hbound
    _ ≤ C * Z ^ 13 * ((7 / 2 : ℝ) ^ k * (1 + P.contourHeight Z T b) ^ k) *
        T ^ (-(N : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hheight (by positivity))
        (Real.rpow_nonneg (zero_le_one.trans hT) _)
    _ = _ := by ring

/-- The arbitrary decay order absorbs the entire polynomial height
cost. The original bin is retained, the analytic detector is shortened to
H+3/2, and the contour theorem is used at order N+k with external height H.
No polynomial upper bound on any presentation height is required. -/
theorem exists_presentationBoundaryPiece_heightfree_tail
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c))
    (hcompanions : 1 ∈ P.companions) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ Z T : ℝ, Z₀ ≤ Z → 1 ≤ T → 1 ≤ δ * T → ∀ b : HighBlockIndex K c Z T,
      δ * T ≤ P.contourHeight Z T b →
      P.contourHeight Z T b + 3 / 2 ≤ P.upperHeight Z T b →
      ‖presentationBoundaryPiece K c P Z T b‖ ≤
        C * Z ^ 13 * T ^ (-(N : ℝ)) := by
  let k : ℕ := HighBinBoundary.ActualLRatioStrip.boundaryHeightDegree K
  obtain ⟨Z₀, hZ₀, hb⟩ := exists_arithmetic_fixedRows_external_tail
    K (targetData K c).S (targetData K c).measures.haar (targetData K c).probe
    (targetCharacter K c) P.companions hcompanions c.geometry P.e_pos
    (presentation_e_small K c P)
  refine ⟨Z₀, hZ₀, ?_⟩
  intro N
  obtain ⟨C, hC, hfixed⟩ := hb (N + k)
  refine ⟨C * (5 : ℝ) ^ k * δ ^ (-(N : ℝ)), by
    exact mul_pos (mul_pos hC (by positivity)) (Real.rpow_pos_of_pos hδ _), ?_⟩
  intro Z T hZ hT hδT b hTH hHU
  have hZ1 : 1 ≤ Z := hZ₀.trans hZ
  have hZnonneg : 0 ≤ Z := zero_le_one.trans hZ1
  let H := P.contourHeight Z T b
  have hH : 1 ≤ H := hδT.trans hTH
  let d := (((targetData K c).expansion Z T).block b).shell
  let a := (((targetData K c).expansion Z T).block b).bin
  let R := P.fixedRows Z T b
  have hdata (u : HighRow K c) (hu : u ∈ R) := highFixedRowBin_member_data K c
    (targetData K c).probe P.euler P.companions (P.selectedHeight Z T b)
    (P.upperHeight Z T b) (Z ^ d) (2 * Z ^ d) a P.e u
    (P.fixedRows_in_bin Z T hZ1 hT b hu)
  have hR : R ⊆ frequencyRows K _ (2 * Z ^ d) := fun u hu => (hdata u hu).1
  have hlo : ∀ u ∈ R, Z ^ d ≤ frequencyRowNorm K _ u :=
    fun u hu => (hdata u hu).2.1.le
  have hbelow : ∀ u ∈ R, rowZeroBelow K _ (targetCharacter K c) P.companions
      (targetData K c).probe
      (HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
        (targetData K c).probe (targetCharacter K c))
      u (H + 3 / 2) (a + 2 * P.e) := by
    intro u hu
    have hfull : rowZeroBelow K _ (targetCharacter K c) P.companions
        (targetData K c).probe
        (HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
          (targetData K c).probe (targetCharacter K c))
        u (P.upperHeight Z T b) (a + 2 * P.e) := by
      simpa only [← hEuler] using (hdata u hu).2.2
    intro χ hχ ρ hord hlo hhi him
    exact hfull χ hχ ρ hord hlo hhi (him.trans hHU)
  have hbound := hfixed (targetData K c).rayFilter Z hZ d
    (P.shell_range Z T hZ1 hT b).1 (presentation_shell_le_one K c P Z T hZ1 hT b)
    R hR hlo a c.family.B H (H + 3 / 2) H
    (P.bin_range Z T hZ1 hT b).1 (P.bin_range Z T hZ1 hT b).2 c.family.B_upper
    hH le_rfl le_rfl hbelow
  have hheight_eq : 2 + (H + 3 / 2) = H + 7 / 2 := by ring
  rw [hheight_eq] at hbound
  have hbound' : ‖presentationBoundaryPiece K c P Z T b‖ ≤
      C * Z ^ 13 * (H + 7 / 2) ^ k * H ^ (-((N + k : ℕ) : ℝ)) := by
    simpa only [presentationBoundaryPiece, R, d, a, H, k, ← hEuler] using hbound
  have habs := HighBinBoundary.height_tail_absorption_external H δ T N k hH hδ
    (zero_lt_one.trans_le hT) hTH
  apply hbound'.trans
  calc
    C * Z ^ 13 * (H + 7 / 2) ^ k * H ^ (-((N + k : ℕ) : ℝ)) =
        C * Z ^ 13 * ((H + 7 / 2) ^ k * H ^ (-((N + k : ℕ) : ℝ))) := by ring
    _ ≤ C * Z ^ 13 * (((5 : ℝ) ^ k * δ ^ (-(N : ℝ))) * T ^ (-(N : ℝ))) :=
      mul_le_mul_of_nonneg_left habs (by positivity)
    _ = _ := by ring

/-- The only geometric mass remaining after arbitrary-order absorption
is the actual retained-block count. No height-growth envelope is used. -/
theorem exists_wholeBinBoundary_blockCount_bound
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c))
    (hcompanions : 1 ∈ P.companions) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ Z T : ℝ, Z₀ ≤ Z → 1 ≤ T → 1 ≤ δ * T →
      (∀ b : HighBlockIndex K c Z T, δ * T ≤ P.contourHeight Z T b) →
      (∀ b : HighBlockIndex K c Z T,
        P.contourHeight Z T b + 3 / 2 ≤ P.upperHeight Z T b) →
      ‖wholeBinBoundary K c P Z T‖ ≤ C * Z ^ 13 *
        (((targetData K c).expansion Z T).blockCount : ℝ) * T ^ (-(N : ℝ)) := by
  obtain ⟨Z₀, hZ₀, hb⟩ :=
    exists_presentationBoundaryPiece_heightfree_tail K c P hEuler hcompanions δ hδ
  refine ⟨Z₀, hZ₀, ?_⟩
  intro N
  obtain ⟨C, hC, hpiece⟩ := hb N
  refine ⟨C, hC, ?_⟩
  intro Z T hZ hT hδT hTH hHU
  rw [wholeBinBoundary_eq_sum]
  calc
    _ ≤ ∑ b : HighBlockIndex K c Z T, ‖presentationBoundaryPiece K c P Z T b‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _b : HighBlockIndex K c Z T, C * Z ^ 13 * T ^ (-(N : ℝ)) :=
      Finset.sum_le_sum (fun b _ => hpiece Z T hZ hT hδT b (hTH b) (hHU b))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Original boundary-control quantifiers with only a lower contour-height
bound and detector coverage. All polynomial height cost is absorbed by
choosing the internal decay order N+k before estimating each fixed bin. -/
theorem highBoundaryControl_of_arithmetic_lower_geometry
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c))
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
  obtain ⟨Zb, hZb, hb⟩ :=
    exists_wholeBinBoundary_blockCount_bound K c P hEuler hcompanions δ hδ
  refine ⟨AB, 13 + RB, ceiling, hAB, hceiling, ?_⟩
  intro τ hτ hτc
  obtain ⟨Cb, Zg, hCb, hZg, hgeometryτ⟩ := hgeometry τ hτ hτc
  intro N
  obtain ⟨C, hC, hmain⟩ := hb N
  let Zδ : ℝ := (1 / δ) ^ (1 / τ)
  refine ⟨C * Cb, max (max Zb Zg) Zδ, mul_pos hC hCb,
    hZb.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro Z hZ
  have hZZb : Zb ≤ Z := (le_max_left _ _).trans ((le_max_left _ _).trans hZ)
  have hZZg : Zg ≤ Z := (le_max_right _ _).trans ((le_max_left _ _).trans hZ)
  have hZZδ : Zδ ≤ Z := (le_max_right _ _).trans hZ
  have hZ1 : 1 ≤ Z := hZb.trans hZZb
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ1
  let T := Z ^ τ
  have hT : 1 ≤ T := Real.one_le_rpow hZ1 hτ.le
  have hδT : 1 ≤ δ * T := by
    have hrecip : 1 / δ ≤ T := by
      calc
        1 / δ = Zδ ^ τ := by
          dsimp [Zδ]
          rw [← Real.rpow_mul (one_div_pos.mpr hδ).le]
          simp only [one_div, inv_mul_cancel₀ hτ.ne', Real.rpow_one]
        _ ≤ T := Real.rpow_le_rpow (Real.rpow_nonneg (one_div_pos.mpr hδ).le _) hZZδ hτ.le
    have hm := mul_le_mul_of_nonneg_left hrecip hδ.le
    simpa only [one_div, mul_inv_cancel₀ hδ.ne'] using hm
  have hh := (hgeometryτ Z hZZg).2
  have hbound := hmain Z T hZZb hT hδT (fun b => (hh b).1) (fun b => (hh b).2)
  apply hbound.trans
  calc
    C * Z ^ 13 * (((targetData K c).expansion Z T).blockCount : ℝ) * T ^ (-(N : ℝ)) ≤
        C * Z ^ 13 * (Cb * Z ^ RB * (1 + T) ^ AB) * T ^ (-(N : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hgeometryτ Z hZZg).1 (by positivity))
        (Real.rpow_nonneg (zero_le_one.trans hT) _)
    _ = (C * Cb) * Z ^ (13 + RB) * (1 + T) ^ AB * T ^ (-(N : ℝ)) := by
      simp only [Real.rpow_add hZ0, Real.rpow_natCast, Real.rpow_ofNat Z 13]
      ring

/-- The whole original retained family has an arbitrary external tail.
The only remaining arithmetic weight is the displayed finite sum of
upper-height powers, selected independently of the decay order. -/
theorem exists_wholeBinBoundary_heightSum_bound
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c))
    (hcompanions : 1 ∈ P.companions) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ Z T : ℝ, Z₀ ≤ Z → 1 ≤ T → 1 ≤ δ * T →
      (∀ b : HighBlockIndex K c Z T, δ * T ≤ P.contourHeight Z T b) →
      (∀ b : HighBlockIndex K c Z T,
        P.contourHeight Z T b + 3 / 2 ≤ P.upperHeight Z T b) →
      ‖wholeBinBoundary K c P Z T‖ ≤ C * Z ^ 13 *
        (∑ b : HighBlockIndex K c Z T,
          (2 + P.upperHeight Z T b) ^
            HighBinBoundary.ActualLRatioStrip.boundaryHeightDegree K) * T ^ (-(N : ℝ)) := by
  obtain ⟨Z₀, hZ₀, hb⟩ :=
    exists_presentationBoundaryPiece_external_tail K c P hEuler hcompanions δ hδ
  refine ⟨Z₀, hZ₀, ?_⟩
  intro N
  obtain ⟨C, hC, hpiece⟩ := hb N
  refine ⟨C, hC, ?_⟩
  intro Z T hZ hT hδT hTH hHU
  rw [wholeBinBoundary_eq_sum]
  calc
    _ ≤ ∑ b : HighBlockIndex K c Z T, ‖presentationBoundaryPiece K c P Z T b‖ :=
      norm_sum_le _ _
    _ ≤ ∑ b : HighBlockIndex K c Z T,
        C * Z ^ 13 * (2 + P.upperHeight Z T b) ^
          HighBinBoundary.ActualLRatioStrip.boundaryHeightDegree K * T ^ (-(N : ℝ)) :=
      Finset.sum_le_sum (fun b _ => hpiece Z T hZ hT hδT b (hTH b) (hHU b))
    _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul]

/-- Summing the original blocks after shortening only the detector used
by the estimate. The actual fixed bins and their original detector heights
are unchanged, and no label count occurs in this sum. -/
theorem exists_wholeBinBoundary_contourHeightSum_bound
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c))
    (hcompanions : 1 ∈ P.companions) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ Z T : ℝ, Z₀ ≤ Z → 1 ≤ T → 1 ≤ δ * T →
      (∀ b : HighBlockIndex K c Z T, δ * T ≤ P.contourHeight Z T b) →
      (∀ b : HighBlockIndex K c Z T,
        P.contourHeight Z T b + 3 / 2 ≤ P.upperHeight Z T b) →
      ‖wholeBinBoundary K c P Z T‖ ≤ C * Z ^ 13 *
        (∑ b : HighBlockIndex K c Z T,
          (1 + P.contourHeight Z T b) ^
            HighBinBoundary.ActualLRatioStrip.boundaryHeightDegree K) * T ^ (-(N : ℝ)) := by
  obtain ⟨Z₀, hZ₀, hb⟩ :=
    exists_presentationBoundaryPiece_contourHeight_tail K c P hEuler hcompanions δ hδ
  refine ⟨Z₀, hZ₀, ?_⟩
  intro N
  obtain ⟨C, hC, hpiece⟩ := hb N
  refine ⟨C, hC, ?_⟩
  intro Z T hZ hT hδT hTH hHU
  rw [wholeBinBoundary_eq_sum]
  calc
    _ ≤ ∑ b : HighBlockIndex K c Z T, ‖presentationBoundaryPiece K c P Z T b‖ :=
      norm_sum_le _ _
    _ ≤ ∑ b : HighBlockIndex K c Z T,
        C * Z ^ 13 * (1 + P.contourHeight Z T b) ^
          HighBinBoundary.ActualLRatioStrip.boundaryHeightDegree K * T ^ (-(N : ℝ)) :=
      Finset.sum_le_sum (fun b _ => hpiece Z T hZ hT hδT b (hTH b) (hHU b))
    _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul]

/-- The actual power-height quantifiers: all polynomial degrees precede
tau, while the geometric constants and lower threshold may depend on tau.
The hypotheses are genuine block counts and height choices, and contain
no contour estimate or boundary conclusion. -/
theorem highBoundaryControl_of_arithmetic_power_geometry
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c))
    (hcompanions : 1 ∈ P.companions) (δ : ℝ) (hδ : 0 < δ)
    (AB RB AU RU ceiling : ℝ)
    (hAB : 0 ≤ AB) (hAU : 0 ≤ AU) (hceiling : 0 < ceiling)
    (hgeometry : ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
      ∃ Cb Cu Zg : ℝ, 0 < Cb ∧ 0 < Cu ∧ 1 ≤ Zg ∧
        ∀ Z : ℝ, Zg ≤ Z →
          (((targetData K c).expansion Z (Z ^ τ)).blockCount : ℝ) ≤
              Cb * Z ^ RB * (1 + Z ^ τ) ^ AB ∧
          ∀ b : HighBlockIndex K c Z (Z ^ τ),
            δ * (Z ^ τ) ≤ P.contourHeight Z (Z ^ τ) b ∧
            P.contourHeight Z (Z ^ τ) b + 3 / 2 ≤ P.upperHeight Z (Z ^ τ) b ∧
            2 + P.upperHeight Z (Z ^ τ) b ≤ Cu * Z ^ RU * (1 + Z ^ τ) ^ AU) :
    HighBoundaryControl K c P := by
  let k : ℕ := HighBinBoundary.ActualLRatioStrip.boundaryHeightDegree K
  obtain ⟨Zb, hZb, hb⟩ :=
    exists_wholeBinBoundary_heightSum_bound K c P hEuler hcompanions δ hδ
  refine ⟨AB + AU * (k : ℝ), 13 + RB + RU * (k : ℝ), ceiling,
    by positivity, hceiling, ?_⟩
  intro τ hτ hτc
  obtain ⟨Cb, Cu, Zg, hCb, hCu, hZg, hgeometryτ⟩ := hgeometry τ hτ hτc
  intro N
  obtain ⟨C, hC, hmain⟩ := hb N
  let Zδ : ℝ := (1 / δ) ^ (1 / τ)
  refine ⟨C * Cb * Cu ^ k, max (max Zb Zg) Zδ, by positivity,
    hZb.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro Z hZ
  have hZZb : Zb ≤ Z := (le_max_left _ _).trans ((le_max_left _ _).trans hZ)
  have hZZg : Zg ≤ Z := (le_max_right _ _).trans ((le_max_left _ _).trans hZ)
  have hZZδ : Zδ ≤ Z := (le_max_right _ _).trans hZ
  have hZ1 : 1 ≤ Z := hZb.trans hZZb
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ1
  let T := Z ^ τ
  have hT : 1 ≤ T := Real.one_le_rpow hZ1 hτ.le
  have hδT : 1 ≤ δ * T := by
    have hrecip : 1 / δ ≤ T := by
      calc
        1 / δ = Zδ ^ τ := by
          dsimp [Zδ]
          rw [← Real.rpow_mul (one_div_pos.mpr hδ).le]
          simp only [one_div, inv_mul_cancel₀ hτ.ne', Real.rpow_one]
        _ ≤ T := Real.rpow_le_rpow (Real.rpow_nonneg (one_div_pos.mpr hδ).le _) hZZδ hτ.le
    have hm := mul_le_mul_of_nonneg_left hrecip hδ.le
    simpa only [one_div, mul_inv_cancel₀ hδ.ne'] using hm
  have hT0 : 0 < 1 + T := by linarith
  have hh := (hgeometryτ Z hZZg).2
  have hbound := hmain Z T hZZb hT hδT (fun b => (hh b).1) (fun b => (hh b).2.1)
  have hheightSum :
      (∑ b : HighBlockIndex K c Z T, (2 + P.upperHeight Z T b) ^ k) ≤
        (((targetData K c).expansion Z T).blockCount : ℝ) *
          (Cu * Z ^ RU * (1 + T) ^ AU) ^ k := by
    calc
      _ ≤ ∑ _b : HighBlockIndex K c Z T, (Cu * Z ^ RU * (1 + T) ^ AU) ^ k := by
        apply Finset.sum_le_sum
        intro b _
        have hU0 : 0 ≤ 2 + P.upperHeight Z T b := by
          have h₁ := (hh b).1
          have h₂ := (hh b).2.1
          linarith
        exact pow_le_pow_left₀ hU0 (hh b).2.2 k
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmass := hheightSum.trans (mul_le_mul_of_nonneg_right
    (hgeometryτ Z hZZg).1 (by positivity))
  apply hbound.trans
  calc
    C * Z ^ 13 *
        (∑ b : HighBlockIndex K c Z T, (2 + P.upperHeight Z T b) ^ k) *
        T ^ (-(N : ℝ)) ≤
      C * Z ^ 13 *
        ((Cb * Z ^ RB * (1 + T) ^ AB) * (Cu * Z ^ RU * (1 + T) ^ AU) ^ k) *
        T ^ (-(N : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (by positivity))
        (Real.rpow_nonneg (by linarith : 0 ≤ T) _)
    _ = (C * Cb * Cu ^ k) * Z ^ (13 + RB + RU * (k : ℝ)) *
        (1 + T) ^ (AB + AU * (k : ℝ)) * T ^ (-(N : ℝ)) := by
      simp only [Real.rpow_add hZ0, Real.rpow_add hT0,
        Real.rpow_mul hZ0.le, Real.rpow_mul hT0.le, Real.rpow_natCast,
        Real.rpow_ofNat Z 13, mul_pow]
      ring

/-- The power-height boundary conclusion requires polynomial growth only
for the contour height. The upper detector can grow arbitrarily fast,
provided it covers the same H+3/2 buffer. All degrees precede tau and N. -/
theorem highBoundaryControl_of_arithmetic_contour_power_geometry
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c))
    (hcompanions : 1 ∈ P.companions) (δ : ℝ) (hδ : 0 < δ)
    (AB RB AH RH ceiling : ℝ)
    (hAB : 0 ≤ AB) (hAH : 0 ≤ AH) (hceiling : 0 < ceiling)
    (hgeometry : ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
      ∃ Cb Ch Zg : ℝ, 0 < Cb ∧ 0 < Ch ∧ 1 ≤ Zg ∧
        ∀ Z : ℝ, Zg ≤ Z →
          (((targetData K c).expansion Z (Z ^ τ)).blockCount : ℝ) ≤
              Cb * Z ^ RB * (1 + Z ^ τ) ^ AB ∧
          ∀ b : HighBlockIndex K c Z (Z ^ τ),
            δ * (Z ^ τ) ≤ P.contourHeight Z (Z ^ τ) b ∧
            P.contourHeight Z (Z ^ τ) b + 3 / 2 ≤ P.upperHeight Z (Z ^ τ) b ∧
            1 + P.contourHeight Z (Z ^ τ) b ≤ Ch * Z ^ RH * (1 + Z ^ τ) ^ AH) :
    HighBoundaryControl K c P := by
  let k : ℕ := HighBinBoundary.ActualLRatioStrip.boundaryHeightDegree K
  obtain ⟨Zb, hZb, hb⟩ :=
    exists_wholeBinBoundary_contourHeightSum_bound K c P hEuler hcompanions δ hδ
  refine ⟨AB + AH * (k : ℝ), 13 + RB + RH * (k : ℝ), ceiling,
    by positivity, hceiling, ?_⟩
  intro τ hτ hτc
  obtain ⟨Cb, Ch, Zg, hCb, hCh, hZg, hgeometryτ⟩ := hgeometry τ hτ hτc
  intro N
  obtain ⟨C, hC, hmain⟩ := hb N
  let Zδ : ℝ := (1 / δ) ^ (1 / τ)
  refine ⟨C * Cb * Ch ^ k, max (max Zb Zg) Zδ, by positivity,
    hZb.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro Z hZ
  have hZZb : Zb ≤ Z := (le_max_left _ _).trans ((le_max_left _ _).trans hZ)
  have hZZg : Zg ≤ Z := (le_max_right _ _).trans ((le_max_left _ _).trans hZ)
  have hZZδ : Zδ ≤ Z := (le_max_right _ _).trans hZ
  have hZ1 : 1 ≤ Z := hZb.trans hZZb
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ1
  let T := Z ^ τ
  have hT : 1 ≤ T := Real.one_le_rpow hZ1 hτ.le
  have hδT : 1 ≤ δ * T := by
    have hrecip : 1 / δ ≤ T := by
      calc
        1 / δ = Zδ ^ τ := by
          dsimp [Zδ]
          rw [← Real.rpow_mul (one_div_pos.mpr hδ).le]
          simp only [one_div, inv_mul_cancel₀ hτ.ne', Real.rpow_one]
        _ ≤ T := Real.rpow_le_rpow (Real.rpow_nonneg (one_div_pos.mpr hδ).le _) hZZδ hτ.le
    have hm := mul_le_mul_of_nonneg_left hrecip hδ.le
    simpa only [one_div, mul_inv_cancel₀ hδ.ne'] using hm
  have hT0 : 0 < 1 + T := by linarith
  have hh := (hgeometryτ Z hZZg).2
  have hbound := hmain Z T hZZb hT hδT (fun b => (hh b).1) (fun b => (hh b).2.1)
  have hheightSum :
      (∑ b : HighBlockIndex K c Z T, (1 + P.contourHeight Z T b) ^ k) ≤
        (((targetData K c).expansion Z T).blockCount : ℝ) *
          (Ch * Z ^ RH * (1 + T) ^ AH) ^ k := by
    calc
      _ ≤ ∑ _b : HighBlockIndex K c Z T, (Ch * Z ^ RH * (1 + T) ^ AH) ^ k := by
        apply Finset.sum_le_sum
        intro b _
        have hU0 : 0 ≤ 1 + P.contourHeight Z T b := by
          have h₁ := (hh b).1
          have h₂ := (hh b).2.1
          linarith
        exact pow_le_pow_left₀ hU0 (hh b).2.2 k
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmass := hheightSum.trans (mul_le_mul_of_nonneg_right
    (hgeometryτ Z hZZg).1 (by positivity))
  apply hbound.trans
  calc
    C * Z ^ 13 *
        (∑ b : HighBlockIndex K c Z T, (1 + P.contourHeight Z T b) ^ k) *
        T ^ (-(N : ℝ)) ≤
      C * Z ^ 13 *
        ((Cb * Z ^ RB * (1 + T) ^ AB) * (Ch * Z ^ RH * (1 + T) ^ AH) ^ k) *
        T ^ (-(N : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (by positivity))
        (Real.rpow_nonneg (by linarith : 0 ≤ T) _)
    _ = (C * Cb * Ch ^ k) * Z ^ (13 + RB + RH * (k : ℝ)) *
        (1 + T) ^ (AB + AH * (k : ℝ)) * T ^ (-(N : ℝ)) := by
      simp only [Real.rpow_add hZ0, Real.rpow_add hT0,
        Real.rpow_mul hZ0.le, Real.rpow_mul hT0.le, Real.rpow_natCast,
        Real.rpow_ofNat Z 13, mul_pow]
      ring

/-- Uniform geometric constants on a full height range are a sufficient
special case of the original power-height quantifiers. -/
theorem highBoundaryControl_of_arithmetic_geometry
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c))
    (hcompanions : 1 ∈ P.companions) (δ : ℝ) (hδ : 0 < δ)
    (AB RB AU RU ceiling Cb Cu Zg : ℝ)
    (hAB : 0 ≤ AB) (hAU : 0 ≤ AU) (hceiling : 0 < ceiling)
    (hCb : 0 < Cb) (hCu : 0 < Cu) (hZg : 1 ≤ Zg)
    (hcount : ∀ Z T : ℝ, Zg ≤ Z → 1 ≤ T → T ≤ Z ^ ceiling →
      (((targetData K c).expansion Z T).blockCount : ℝ) ≤
        Cb * Z ^ RB * (1 + T) ^ AB)
    (hheights : ∀ Z T : ℝ, Zg ≤ Z → 1 ≤ T → T ≤ Z ^ ceiling →
      ∀ b : HighBlockIndex K c Z T,
        δ * T ≤ P.contourHeight Z T b ∧
        P.contourHeight Z T b + 3 / 2 ≤ P.upperHeight Z T b ∧
        2 + P.upperHeight Z T b ≤ Cu * Z ^ RU * (1 + T) ^ AU) :
    HighBoundaryControl K c P := by
  apply highBoundaryControl_of_arithmetic_power_geometry K c P hEuler hcompanions δ hδ
    AB RB AU RU ceiling hAB hAU hceiling
  intro τ hτ hτc
  refine ⟨Cb, Cu, Zg, hCb, hCu, hZg, ?_⟩
  intro Z hZ
  have hZ1 : 1 ≤ Z := hZg.trans hZ
  have hT : 1 ≤ Z ^ τ := Real.one_le_rpow hZ1 hτ.le
  have hTc : Z ^ τ ≤ Z ^ ceiling := Real.rpow_le_rpow_of_exponent_le hZ1 hτc
  exact ⟨hcount Z (Z ^ τ) hZ hT hTc, hheights Z (Z ^ τ) hZ hT hTc⟩

/-- The standard buffered heights have the required gap and a fixed
polynomial envelope. The same internal power height already used by the
norm-form schedule is retained. No tail order occurs in its exponent. -/
theorem buffered_height_geometry (Z T κ δ : ℝ) (i I : ℕ)
    (hZ : 1 ≤ Z) (hT : 1 ≤ T) (hκ : 0 ≤ κ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hi : i ≤ I) :
    δ * T ≤ δ * HighBinVerified.NormForm.internalHeight Z T κ ∧
      δ * HighBinVerified.NormForm.internalHeight Z T κ + 3 / 2 ≤
        3 * ((i : ℝ) + 1) * HighBinVerified.NormForm.internalHeight Z T κ ∧
      2 + 3 * ((i : ℝ) + 1) * HighBinVerified.NormForm.internalHeight Z T κ ≤
        (3 * ((I : ℝ) + 1) + 2) * Z ^ κ * (1 + T) := by
  let H := HighBinVerified.NormForm.internalHeight Z T κ
  have hTH : T ≤ H := HighBinVerified.NormForm.le_internalHeight Z T κ
  have hH1 : 1 ≤ H := hT.trans hTH
  have hH0 : 0 ≤ H := zero_le_one.trans hH1
  have hHupper : H ≤ Z ^ κ * (1 + T) :=
    HighBinVerified.NormForm.internalHeight_le_power_mul Z T κ hZ
      (zero_le_one.trans hT) hκ
  have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
  have hI0 : 0 ≤ (I : ℝ) := Nat.cast_nonneg _
  have hiI : (i : ℝ) ≤ I := Nat.cast_le.mpr hi
  have hδH : δ * H ≤ H := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hδ1 hH0
  refine ⟨mul_le_mul_of_nonneg_left hTH hδ.le, ?_, ?_⟩
  · have hiH : 0 ≤ (i : ℝ) * H := mul_nonneg hi0 hH0
    change δ * H + 3 / 2 ≤ 3 * ((i : ℝ) + 1) * H
    nlinarith
  · change 2 + 3 * ((i : ℝ) + 1) * H ≤ _
    calc
      _ ≤ (3 * ((I : ℝ) + 1) + 2) * H := by
        have hmono := mul_le_mul_of_nonneg_right hiI hH0
        nlinarith
      _ ≤ (3 * ((I : ℝ) + 1) + 2) * (Z ^ κ * (1 + T)) :=
        mul_le_mul_of_nonneg_left hHupper (by positivity)
      _ = _ := by ring

/-- Specialization to concrete buffered-height formulas. Once the actual
presentation uses these formulas, no independent height-growth estimate
remains to be supplied; only its genuine retained-block count is needed. -/
theorem highBoundaryControl_of_buffered_schedule
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c))
    (hcompanions : 1 ∈ P.companions)
    (δ κ : ℝ) (I : ℕ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hκ : 0 ≤ κ)
    (AB RB ceiling Cb Zg : ℝ) (hAB : 0 ≤ AB) (hceiling : 0 < ceiling)
    (hCb : 0 < Cb) (hZg : 1 ≤ Zg)
    (hcount : ∀ Z T : ℝ, Zg ≤ Z → 1 ≤ T → T ≤ Z ^ ceiling →
      (((targetData K c).expansion Z T).blockCount : ℝ) ≤
        Cb * Z ^ RB * (1 + T) ^ AB)
    (hschedule : ∀ Z T : ℝ, Zg ≤ Z → 1 ≤ T → T ≤ Z ^ ceiling →
      ∀ b : HighBlockIndex K c Z T, ∃ i : ℕ, i ≤ I ∧
        P.contourHeight Z T b = δ * HighBinVerified.NormForm.internalHeight Z T κ ∧
        P.upperHeight Z T b =
          3 * ((i : ℝ) + 1) * HighBinVerified.NormForm.internalHeight Z T κ) :
    HighBoundaryControl K c P := by
  apply highBoundaryControl_of_arithmetic_geometry K c P hEuler hcompanions δ hδ
    AB RB 1 κ ceiling Cb (3 * ((I : ℝ) + 1) + 2) Zg hAB (by norm_num)
    hceiling hCb (by positivity) hZg hcount
  intro Z T hZ hT hTc b
  obtain ⟨i, hi, hH, hU⟩ := hschedule Z T hZ hT hTc b
  simp only [hH, hU, Real.rpow_one]
  exact buffered_height_geometry Z T κ δ i I (hZg.trans hZ) hT hκ hδ hδ1 hi

/-- Buffered heights at the actual power heights. Block-count constants
and the starting threshold are selected after tau, exactly as in the
repository's expansion block-count obligation. The degrees and buffered
height index are still fixed before tau and the external decay order. -/
theorem highBoundaryControl_of_buffered_power_schedule
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c))
    (hcompanions : 1 ∈ P.companions)
    (δ κ : ℝ) (I : ℕ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hκ : 0 ≤ κ)
    (AB RB ceiling : ℝ) (hAB : 0 ≤ AB) (hceiling : 0 < ceiling)
    (hgeometry : ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
      ∃ Cb Zg : ℝ, 0 < Cb ∧ 1 ≤ Zg ∧
        ∀ Z : ℝ, Zg ≤ Z →
          (((targetData K c).expansion Z (Z ^ τ)).blockCount : ℝ) ≤
              Cb * Z ^ RB * (1 + Z ^ τ) ^ AB ∧
          ∀ b : HighBlockIndex K c Z (Z ^ τ), ∃ i : ℕ, i ≤ I ∧
            P.contourHeight Z (Z ^ τ) b =
              δ * HighBinVerified.NormForm.internalHeight Z (Z ^ τ) κ ∧
            P.upperHeight Z (Z ^ τ) b =
              3 * ((i : ℝ) + 1) * HighBinVerified.NormForm.internalHeight Z (Z ^ τ) κ) :
    HighBoundaryControl K c P := by
  apply highBoundaryControl_of_arithmetic_power_geometry K c P hEuler hcompanions δ hδ
    AB RB 1 κ ceiling hAB (by norm_num) hceiling
  intro τ hτ hτc
  obtain ⟨Cb, Zg, hCb, hZg, hgeometryτ⟩ := hgeometry τ hτ hτc
  refine ⟨Cb, 3 * ((I : ℝ) + 1) + 2, Zg, hCb, by positivity, hZg, ?_⟩
  intro Z hZ
  refine ⟨(hgeometryτ Z hZ).1, ?_⟩
  intro b
  obtain ⟨i, hi, hH, hU⟩ := (hgeometryτ Z hZ).2 b
  simp only [hH, hU, Real.rpow_one]
  have hZ1 : 1 ≤ Z := hZg.trans hZ
  exact buffered_height_geometry Z (Z ^ τ) κ δ i I hZ1
    (Real.one_le_rpow hZ1 hτ.le) hκ hδ hδ1 hi

/-- Buffered schedules do not require a uniform upper bound on the
detector's subdivision index. The row set uses its original upper height;
the proof estimates it with the shorter H+3/2 detector instead. -/
theorem highBoundaryControl_of_buffered_power_schedule_unbounded_detector
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c))
    (hcompanions : 1 ∈ P.companions)
    (δ κ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hκ : 0 ≤ κ)
    (AB RB ceiling : ℝ) (hAB : 0 ≤ AB) (hceiling : 0 < ceiling)
    (hgeometry : ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
      ∃ Cb Zg : ℝ, 0 < Cb ∧ 1 ≤ Zg ∧
        ∀ Z : ℝ, Zg ≤ Z →
          (((targetData K c).expansion Z (Z ^ τ)).blockCount : ℝ) ≤
              Cb * Z ^ RB * (1 + Z ^ τ) ^ AB ∧
          ∀ b : HighBlockIndex K c Z (Z ^ τ), ∃ i : ℕ,
            P.contourHeight Z (Z ^ τ) b =
              δ * HighBinVerified.NormForm.internalHeight Z (Z ^ τ) κ ∧
            P.upperHeight Z (Z ^ τ) b =
              3 * ((i : ℝ) + 1) * HighBinVerified.NormForm.internalHeight Z (Z ^ τ) κ) :
    HighBoundaryControl K c P := by
  apply highBoundaryControl_of_arithmetic_lower_geometry K c P hEuler hcompanions δ hδ
    AB RB ceiling hAB hceiling
  intro τ hτ hτc
  obtain ⟨Cb, Zg, hCb, hZg, hgeometryτ⟩ := hgeometry τ hτ hτc
  refine ⟨Cb, Zg, hCb, hZg, ?_⟩
  intro Z hZ
  refine ⟨(hgeometryτ Z hZ).1, ?_⟩
  intro b
  obtain ⟨i, hH, hU⟩ := (hgeometryτ Z hZ).2 b
  have hZ1 : 1 ≤ Z := hZg.trans hZ
  have hT : 1 ≤ Z ^ τ := Real.one_le_rpow hZ1 hτ.le
  have hbuffer := buffered_height_geometry Z (Z ^ τ) κ δ i i
    hZ1 hT hκ hδ hδ1 le_rfl
  simp only [hH, hU]
  exact ⟨hbuffer.1, hbuffer.2.1⟩

#print axioms highFixedRowBin_member_data
#print axioms presentationInitialBlock
#print axioms presentationBlock_value_eq_finalRows
#print axioms presentationInitialBlock_eq_value_add_boundary
#print axioms presentationInitialSum_eq_blocks_add_boundary
#print axioms wholeBinBoundary_eq_initialSum_sub_blocks
#print axioms exists_presentationBoundaryPiece_detector_tail
#print axioms exists_presentationBoundaryPiece_external_tail
#print axioms exists_presentationBoundaryPiece_contourHeight_tail
#print axioms exists_presentationBoundaryPiece_heightfree_tail
#print axioms exists_wholeBinBoundary_blockCount_bound
#print axioms highBoundaryControl_of_arithmetic_lower_geometry
#print axioms exists_wholeBinBoundary_heightSum_bound
#print axioms exists_wholeBinBoundary_contourHeightSum_bound
#print axioms highBoundaryControl_of_arithmetic_power_geometry
#print axioms highBoundaryControl_of_arithmetic_contour_power_geometry
#print axioms highBoundaryControl_of_arithmetic_geometry
#print axioms buffered_height_geometry
#print axioms highBoundaryControl_of_buffered_schedule
#print axioms highBoundaryControl_of_buffered_power_schedule
#print axioms highBoundaryControl_of_buffered_power_schedule_unbounded_detector

end HeckeSkeleton.HighBinBoundaryPresentation
