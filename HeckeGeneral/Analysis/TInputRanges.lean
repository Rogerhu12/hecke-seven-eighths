import HeckeGeneral.Analysis.PhysicalProbeContours

/-!
Concrete arithmetic zero bins and source primitive small/absolute-large
range inputs. These are partial T components, not the final high estimate.
The moderate input still requires pointwise full-correction amplitude sets
and witness coverage; it is deliberately not replaced by a row-count field.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain MeasureTheory Set Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Exactly M (family); the target's infinite-order part is retained. -/
def physicalRowFamily (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K))
    (P : ProbeData K S) (E : RowEulerData K S P) (u : FrequencyRow K S) :
    Finset (HeckeCharacter K) :=
  Θ.biUnion fun θ =>
    {θ * E.rows.character u, θ * conjugate (E.rows.character u),
      ψ * θ * conjugate (E.rows.character u), conjugate ψ * θ * E.rows.character u}

def rowZeroBelow (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K))
    (P : ProbeData K S) (E : RowEulerData K S P) (u : FrequencyRow K S)
    (height upper : ℝ) : Prop :=
  ∀ χ ∈ physicalRowFamily K S ψ Θ P E u, ∀ ρ : ℂ,
    0 < meromorphicOrderAt (heckeContinuation K χ) ρ →
      1 / 2 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ height → ρ.re ≤ upper

def rowZeroAbove (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K))
    (P : ProbeData K S) (E : RowEulerData K S P) (u : FrequencyRow K S)
    (height lower : ℝ) : Prop :=
  ∃ χ ∈ physicalRowFamily K S ψ Θ P E u, ∃ ρ : ℂ,
    0 < meromorphicOrderAt (heckeContinuation K χ) ρ ∧
      lower ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ height

/-- Fixed arithmetic bin. Moving amplitude sets are NOT integrated as
separate contours: those will enter pointwise estimates after this move. -/
def physicalRowBin (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K))
    (P : ProbeData K S) (E : RowEulerData K S P)
    (height normLower normUpper aLower aUpper : ℝ) : Finset (FrequencyRow K S) :=
  (frequencyRows K S normUpper).filter fun u =>
    normLower < frequencyRowNorm K S u ∧ ¬principalFrequencyRow K S u ∧
      rowZeroAbove K S ψ Θ P E u height aLower ∧ rowZeroBelow K S ψ Θ P E u height aUpper

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S) → Measure (p.val.adicCompletion K))
variable [∀ p : S, (μ p).IsAddHaarMeasure]

/-- A sufficient open region containing the central moderate, small-row,
principal-residue and absolute-large contours used here. This is not a
claim that the local correction has no continuation outside this region. -/
def rowEulerRegion : Set (ℂ × ℂ × ℂ) :=
  {v | 1 / 2 < v.1.re ∧ 0 < v.2.1.re ∧ 0 < v.2.2.re ∧
    1 < v.1.re + v.2.1.re ∧ 5 / 6 < v.1.re + v.2.2.re ∧
      2 < v.1.re + v.2.1.re + 6 * v.2.2.re ∧
      1 < v.2.1.re + 6 * v.2.2.re ∧ 1 < v.1.re + 6 * v.2.2.re}

/-- Local-Euler analytic calibration, distinct from holomorphy of any
reciprocal target L-function. No zero-free conclusion is in these fields. -/
structure TRowEulerInput (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) : Prop where
  initial : RowEulerCalibrationInput K S P ψ E
  local_product : ∀ (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (v : ℂ × ℂ × ℂ), v ∈ rowEulerRegion →
    Multipliable (fun p : ExteriorPrime K S =>
      if hp : p ∈ rowExceptionalPrimes K S Q u then
        finiteEulerRationalValue (E.exceptionalFactor Q u ⟨p, hp⟩)
          (p.val.asIdeal.absNorm : ℝ) v.1 v.2.1 v.2.2
      else localRowCorrection K S P ψ (E.rows.character u) p v.1 v.2.1 v.2.2)
  correction_analytic : ∀ (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S),
    AnalyticOnNhd ℂ (fun v : ℂ × ℂ × ℂ =>
      rowCorrection K S P ψ E Q u v.1 v.2.1 v.2.2) rowEulerRegion

def fixedBinContour (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) (g : PrimeWindowGeometry)
    (T Θ : Finset (HeckeCharacter K))
    (Z height normLower normUpper aLower aUpper e : ℝ) : ℂ :=
  ∑ u ∈ physicalRowBin K S ψ Θ P E height normLower normUpper aLower aUpper,
    rowContourBox K S μ P ψ E g T u Z height (aUpper + 16 * e)
      (1 - aUpper - 6 * e) (17 / 50)

def absoluteLargeRowTerm (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z height ζ zInfinity : ℝ) (u : FrequencyRow K S) : ℝ :=
  if Z ^ (13 / 16 + ζ) < frequencyRowNorm K S u then
    ‖rowContourBox K S μ P ψ E g T u Z height 2 2 zInfinity‖
  else 0

/-- The actual small-row comparison on (B+e,1/2,17/50), with constants and
height degree chosen after the target. B is a supplied common boundary;
there is no improved zero-free boundary in this input. -/
structure TSmallRowInput (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (B e loss : ℝ) : Prop where
  bound : ∃ C Z₀ A ceiling : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧ 0 ≤ A ∧ 0 < ceiling ∧
    ∀ Z height : ℝ, Z₀ ≤ Z → 1 ≤ height → height ≤ Z ^ ceiling →
      ‖finiteRowContourBlock K S μ P ψ E g T Z height 0
          (Z ^ (1 / 100 : ℝ)) (B + e) (1 / 2) (17 / 50)‖ ≤
        C * Z ^ (B - 11 / 16 - 63 / 800 + e + loss) * (1 + height) ^ A

/-- The arbitrary absolute decay of rows above h+ζ on (2,2,zInfinity).
ζ,zInfinity and the requested scale decay are pretarget real choices.
The sum is explicitly Summable, avoiding tsum's zero default. -/
structure TLargeRowInput (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (ζ zInfinity decay : ℝ) : Prop where
  absolute : ∀ Z height : ℝ, 1 ≤ Z → 1 ≤ height →
    Summable (absoluteLargeRowTerm K S μ P ψ E g T Z height ζ zInfinity)
  bound : ∃ C Z₀ A ceiling : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧ 0 ≤ A ∧ 0 < ceiling ∧
    ∀ Z height : ℝ, Z₀ ≤ Z → 1 ≤ height → height ≤ Z ^ ceiling →
      (∑' u, absoluteLargeRowTerm K S μ P ψ E g T Z height ζ zInfinity u) ≤
        C * Z ^ (-decay) * (1 + height) ^ A

end HeckeGeneral.ThetaSkeleton.Physical
