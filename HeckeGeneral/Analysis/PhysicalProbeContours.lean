import HeckeGeneral.Analysis.PhysicalProbeRows
import HeckeGeneral.Analysis.RowEulerRational

/-!
Concrete row Euler continuation and compensated three-variable integrals.
The only uninstantiated local data are FINITE rational Euler tables at the
actual row/mark primes and genuine finite-order inducing characters. Their
calibration is equality to the actual four-ideal Fourier series on an open
absolute-convergence domain. They are not arbitrary target functions.

No shifted-contour identity or estimate is proved by these definitions.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators ComplexConjugate Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def rowExceptionalPrimes (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) :
    Finset (ExteriorPrime K S) := exteriorSupport K S u.ideal ∪ Q

structure RowEulerData (P : ProbeData K S) where
  rows : RowCharacterInput K S P
  exceptionalFactor : ∀ (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S),
    {p : ExteriorPrime K S // p ∈ rowExceptionalPrimes K S Q u} → FiniteEulerRational

/-- Regular-prime rational continuation after cancelling the geometric
denominators. The remaining poles come from 1-E and 1-D. -/
def localRowCorrection (P : ProbeData K S) (ψ χ : HeckeCharacter K)
    (p : ExteriorPrime K S) (s w z : ℂ) : ℂ :=
  let q : ℂ := (p.val.asIdeal.absNorm : ℂ)
  let V := q ^ (-6 * z)
  let W := primeCoefficient K χ p.val * q ^ (-w)
  let D := primeCoefficient K ψ p.val * conj (primeCoefficient K χ p.val) * q ^ (-s)
  let E := primeCoefficient K (thetaPeriod K S P ψ) p.val ^ 6 * q ^ (4 - 6 * s) * V
  rowEulerRationalValue q q⁻¹ V W D E

def rowCorrection (P : ProbeData K S) (ψ : HeckeCharacter K) (E : RowEulerData K S P)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (s w z : ℂ) : ℂ :=
  ∏' p : ExteriorPrime K S,
    if hp : p ∈ rowExceptionalPrimes K S Q u then
      finiteEulerRationalValue (E.exceptionalFactor Q u ⟨p, hp⟩)
        (p.val.asIdeal.absNorm : ℝ) s w z
    else localRowCorrection K S P ψ (E.rows.character u) p s w z

def rowEulerContinuation (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) (Q : Finset (ExteriorPrime K S))
    (u : FrequencyRow K S) (s w z : ℂ) : ℂ :=
  heckeDeletedContinuation K 1 (exceptionalPrimes K S) (6 * z) *
    heckeDeletedContinuation K (E.rows.character u) (exceptionalPrimes K S) w /
    heckeDeletedContinuation K (ψ * conjugate (E.rows.character u))
      (exceptionalPrimes K S) s * rowCorrection K S P ψ E Q u s w z

/-- Initial Euler calibration, including marks and all ramified zeros.
The domain is open, not just one vertical line. Thus this cannot be supplied
by unrelated values chosen separately on later contours. -/
structure RowEulerCalibrationInput (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) : Prop where
  initial_absolute : ∀ (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (s w z : ℂ), 4 < s.re → 4 < w.re → 2 < z.re →
      Summable (initialRowEulerTerm K S P ψ Q u s w z)
  initial_identity : ∀ (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (s w z : ℂ), 4 < s.re → 4 < w.re → 2 < z.re →
      initialRowEulerSeries K S P ψ Q u s w z = rowEulerContinuation K S P ψ E Q u s w z

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S) → Measure (p.val.adicCompletion K))
variable [∀ p : S, (μ p).IsAddHaarMeasure]

/-- A single compensated physical row before the three line integrations.
Every subset uses its actual whole-index-marked Euler continuation. -/
def compensatedRowMellinKernel (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z : ℝ) (s w z : ℂ) : ℂ :=
  Complex.exp ((s + z - 1) ^ 2) * additiveMellin K S μ P.additive z *
    mellin P.denominator.toFun w * (frequencyRowNorm K S u : ℂ) ^ (-z) *
    (∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
      (∏ i : Fin g.slots, windowWeight K S g Z i (p i)) *
      ∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
        let selected := subsetPrimeIdeal K S p J
        let marked := subsetPrimeIdeal K S p (Finset.univ \ J)
        (-1 : ℂ) ^ J.card * (exteriorNorm K S selected : ℂ) ^ (-(3 / 2 : ℂ)) *
          conj (heckeIdealCoefficient K ψ marked.val) *
          ((Z ^ (17 / 48 : ℝ) / exteriorNorm K S selected : ℝ) : ℂ) ^ (1 / 2 - z) *
          ((Z * exteriorNorm K S marked : ℝ) : ℂ) ^ (s + z - 1) *
          ((Z ^ (23 / 48 : ℝ) / exteriorNorm K S selected : ℝ) : ℂ) ^ (w - 1) *
          rowEulerContinuation K S P ψ E ((Finset.univ \ J).image p) u s w z) /
    (physicalResidueNormalizer K S μ P * primeNormalizer K S g T Z)

def rowContourBox (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z height σ ν zLine : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ (-(3 : ℤ)) *
    ∫ ts in Icc (-height) height, ∫ tw in Icc (-height) height, ∫ tz in Icc (-height) height,
      compensatedRowMellinKernel K S μ P ψ E g T u Z
        ((σ : ℂ) + (ts : ℂ) * Complex.I) ((ν : ℂ) + (tw : ℂ) * Complex.I)
        ((zLine : ℂ) + (tz : ℂ) * Complex.I)

def finiteRowContourBlock (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z height lower upper σ ν zLine : ℝ) : ℂ :=
  ∑ u ∈ (frequencyRows K S upper).filter
      (fun u => lower < frequencyRowNorm K S u ∧ ¬principalFrequencyRow K S u),
    rowContourBox K S μ P ψ E g T u Z height σ ν zLine

end HeckeGeneral.ThetaSkeleton.Physical
