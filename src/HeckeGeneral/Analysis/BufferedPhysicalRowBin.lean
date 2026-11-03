import HeckeGeneral.Analysis.TInputRanges

/-!
Actual fixed arithmetic bins with separate selected-zero and upper-zero
heights, and a contour center independent of the upper-zero threshold.
Q 4281--4311 uses selectedHeight = 3*i*T and upperHeight = 3*(i+1)*T.
Q 5810--5833 then moves the ORIGINAL fixed-bin kernel to the center a.
The older same-height physicalRowBin/fixedBinContour wrappers cannot express
these two distinctions simultaneously. No Poisson identity, contour shift,
buffered analytic estimate or witness/count estimate is asserted here.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def bufferedPhysicalRowBin (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K))
    (P : ProbeData K S) (E : RowEulerData K S P)
    (selectedHeight upperHeight normLower normUpper a e : ℝ) : Finset (FrequencyRow K S) :=
  (frequencyRows K S normUpper).filter fun u =>
    normLower < frequencyRowNorm K S u ∧ ¬principalFrequencyRow K S u ∧
      rowZeroAbove K S ψ Θ P E u selectedHeight a ∧
      rowZeroBelow K S ψ Θ P E u upperHeight (a + 2 * e)

theorem mem_bufferedPhysicalRowBin_iff (ψ : HeckeCharacter K)
    (Θ : Finset (HeckeCharacter K)) (P : ProbeData K S) (E : RowEulerData K S P)
    (selectedHeight upperHeight normLower normUpper a e : ℝ) (u : FrequencyRow K S) :
    u ∈ bufferedPhysicalRowBin K S ψ Θ P E
      selectedHeight upperHeight normLower normUpper a e ↔
      u ∈ frequencyRows K S normUpper ∧
        normLower < frequencyRowNorm K S u ∧ ¬principalFrequencyRow K S u ∧
          rowZeroAbove K S ψ Θ P E u selectedHeight a ∧
          rowZeroBelow K S ψ Θ P E u upperHeight (a + 2 * e) := by
  simp only [bufferedPhysicalRowBin, Finset.mem_filter]

theorem bufferedPhysicalRowBin_subset (ψ : HeckeCharacter K)
    (Θ : Finset (HeckeCharacter K)) (P : ProbeData K S) (E : RowEulerData K S P)
    (selectedHeight upperHeight normLower normUpper a e : ℝ) :
    bufferedPhysicalRowBin K S ψ Θ P E selectedHeight upperHeight normLower normUpper a e ⊆
      frequencyRows K S normUpper := Finset.filter_subset _ _

theorem bufferedPhysicalRowBin_zero_bounds (ψ : HeckeCharacter K)
    (Θ : Finset (HeckeCharacter K)) (P : ProbeData K S) (E : RowEulerData K S P)
    (selectedHeight upperHeight normLower normUpper a e : ℝ) (u : FrequencyRow K S)
    (hu : u ∈ bufferedPhysicalRowBin K S ψ Θ P E
      selectedHeight upperHeight normLower normUpper a e) :
    rowZeroAbove K S ψ Θ P E u selectedHeight a ∧
      rowZeroBelow K S ψ Θ P E u upperHeight (a + 2 * e) :=
  ((mem_bufferedPhysicalRowBin_iff K S ψ Θ P E
    selectedHeight upperHeight normLower normUpper a e u).mp hu).2.2.2

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S) → Measure (p.val.adicCompletion K))
variable [∀ p : S, (μ p).IsAddHaarMeasure]

/-- A finite fixed-bin contour expression, not a shifted-contour theorem.
The three height roles and the contour center a are independent data. -/
def bufferedFixedBinContour (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) (g : PrimeWindowGeometry)
    (T Θ : Finset (HeckeCharacter K))
    (Z contourHeight selectedHeight upperHeight normLower normUpper a e : ℝ) : ℂ :=
  ∑ u ∈ bufferedPhysicalRowBin K S ψ Θ P E
      selectedHeight upperHeight normLower normUpper a e,
    rowContourBox K S μ P ψ E g T u Z contourHeight
      (a + 16 * e) (1 - a - 6 * e) (17 / 50)

omit [∀ p : S, BorelSpace (p.val.adicCompletion K)]
    [∀ p : S, (μ p).IsAddHaarMeasure] in
theorem bufferedFixedBinContour_eq_sum (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) (g : PrimeWindowGeometry)
    (T Θ : Finset (HeckeCharacter K))
    (Z contourHeight selectedHeight upperHeight normLower normUpper a e : ℝ) :
    bufferedFixedBinContour K S μ P ψ E g T Θ Z contourHeight
      selectedHeight upperHeight normLower normUpper a e =
      ∑ u ∈ bufferedPhysicalRowBin K S ψ Θ P E
          selectedHeight upperHeight normLower normUpper a e,
        rowContourBox K S μ P ψ E g T u Z contourHeight
          (a + 16 * e) (1 - a - 6 * e) (17 / 50) := rfl

end HeckeGeneral.ThetaSkeleton.Physical
