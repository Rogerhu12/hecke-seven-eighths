import HeckeGeneral.Analysis.BufferedPhysicalRowBin
import HeckeGeneral.Analysis.MellinZeroDetector
import Mathlib.MeasureTheory.Integral.Prod

/-!
An UNINSTANTIATED source primitive for the actual fixed arithmetic bin.
Q 5606--5623, 5672--5710 and 5810--5903: move the full original bin BEFORE
introducing pointwise amplitude/witness sets. The full vertical integral
below uses the literal compensatedRowMellinKernel and product Lebesgue
measure. Absolute integrability is explicit, not inferred from a total
Bochner integral that might otherwise default to zero.

We start at (5,5,3), strictly inside RowEulerCalibrationInput's open domain
Re(s),Re(w)>4, Re(z)>2. This is an analytic starting integral only: equality
to a physical Poisson expansion is NOT asserted. Q displays (3,3,2); moving
from the present safer absolute lines is part of the source transfer.

An OLD common boundary and actual nonprincipality are explicit premises.
Finite-height zero data alone do not justify moving the whole infinite
contour through the global line. The retained center a and the selected,
upper-zero and contour heights are separate. No moving subset is used as
a contour object, and no optimized count/high estimate is an input.

All geometry precedes the target in the eventual packet wrapper. This
fixed-target input permits its S and constants to depend on that target.
A,B,ceiling are chosen before external N. The displayed tail retains a
fixed polynomial height factor (1+T1)^A, to be absorbed by a later larger
N; Q's original pure T1^(-N) statement is stronger in that notation.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Numerical choices only; no target, row count or analytic conclusion. -/
structure FixedBinTransferGeometry where
  boundary : ℝ
  boundary_lower : 7 / 8 ≤ boundary
  boundary_upper : boundary ≤ 11 / 12
  dMin : ℝ
  dMax : ℝ
  dMin_pos : 0 < dMin
  dMin_lt_dMax : dMin < dMax
  e : ℝ
  e_pos : 0 < e
  e_small : e < 1 / 1000
  contourFraction : ℝ
  contourFraction_pos : 0 < contourFraction
  contourFraction_le_half : contourFraction ≤ 1 / 2

/-- Only real/index restrictions from the buffered-bin contour argument. -/
def FixedBinTransferRange (G : FixedBinTransferGeometry) (Z d τ a : ℝ) (i : ℕ) : Prop :=
  1 ≤ Z ∧ d ∈ Icc G.dMin G.dMax ∧ 0 < τ ∧ τ ≤ G.dMin / 100 ∧
    2 < Z ^ τ ∧ a ∈ Icc (51 / 100) G.boundary ∧
    1 ≤ i ∧ i ≤ Nat.ceil (1 / G.e) + 1

/-- The row set is fixed before all three Mellin integration variables.
This selected-zero branch does not claim coverage of the no-zero floor bin. -/
def sourceBufferedRowBin (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) (Θ : Finset (HeckeCharacter K))
    (G : FixedBinTransferGeometry) (Z d τ a : ℝ) (i : ℕ) : Finset (FrequencyRow K S) :=
  bufferedPhysicalRowBin K S ψ Θ P E
    (3 * (i : ℝ) * Z ^ τ) (3 * ((i : ℝ) + 1) * Z ^ τ)
    (Z ^ d / 2) (Z ^ d) a G.e

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S) → Measure (p.val.adicCompletion K))
variable [∀ p : S, (μ p).IsAddHaarMeasure]

def rowHeightVolume : Measure (ℝ × ℝ × ℝ) :=
  (volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))

def rowVerticalKernel (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z σ ν zLine : ℝ) (t : ℝ × ℝ × ℝ) : ℂ :=
  compensatedRowMellinKernel K S μ P ψ E g T u Z
    ((σ : ℂ) + (t.1 : ℂ) * Complex.I)
    ((ν : ℂ) + (t.2.1 : ℂ) * Complex.I)
    ((zLine : ℂ) + (t.2.2 : ℂ) * Complex.I)

/-- Integrable of a complex function is absolute Bochner integrability,
including strong measurability; no conditional principal value is meant. -/
def rowVerticalAbsolutelyIntegrable (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z σ ν zLine : ℝ) : Prop :=
  Integrable (rowVerticalKernel K S μ P ψ E g T u Z σ ν zLine) rowHeightVolume

/-- Actual full three-dimensional vertical integral of the original finite bin. -/
def fixedBinFullVerticalIntegral (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (B : Finset (FrequencyRow K S)) (Z σ ν zLine : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ (-(3 : ℤ)) *
    ∫ t : ℝ × ℝ × ℝ, ∑ u ∈ B, rowVerticalKernel K S μ P ψ E g T u Z σ ν zLine t
      ∂rowHeightVolume

def rowRetainedHeightBox (height : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Icc (-height) height ×ˢ (Icc (-height) height ×ˢ Icc (-height) height)

omit [∀ p : S, BorelSpace (p.val.adicCompletion K)]
    [∀ p : S, (μ p).IsAddHaarMeasure] in
theorem integrable_fixedBinVerticalKernel
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E : RowEulerData K S P)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (B : Finset (FrequencyRow K S)) (Z σ ν zLine : ℝ)
    (h : ∀ u ∈ B, rowVerticalAbsolutelyIntegrable K S μ P ψ E g T u Z σ ν zLine) :
    Integrable (fun t => ∑ u ∈ B,
      rowVerticalKernel K S μ P ψ E g T u Z σ ν zLine t) rowHeightVolume :=
  integrable_finsetSum B h

omit [∀ p : S, BorelSpace (p.val.adicCompletion K)]
    [∀ p : S, (μ p).IsAddHaarMeasure] in
theorem fixedBinFullVerticalIntegral_eq_sum
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E : RowEulerData K S P)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (B : Finset (FrequencyRow K S)) (Z σ ν zLine : ℝ)
    (h : ∀ u ∈ B, rowVerticalAbsolutelyIntegrable K S μ P ψ E g T u Z σ ν zLine) :
    fixedBinFullVerticalIntegral K S μ P ψ E g T B Z σ ν zLine =
      ∑ u ∈ B, (2 * (Real.pi : ℂ)) ^ (-(3 : ℤ)) *
        ∫ t : ℝ × ℝ × ℝ, rowVerticalKernel K S μ P ψ E g T u Z σ ν zLine t
          ∂rowHeightVolume := by
  unfold fixedBinFullVerticalIntegral
  rw [integral_finsetSum B h, Finset.mul_sum]

/-- Exact source transfer obligation, NOT an analytic shift theorem proved here.
The global old boundary, nonprincipal presentations, absolute starting
integrals and central integrability all remain visible in this statement. -/
def TFixedBinTransferInput (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) (g : PrimeWindowGeometry)
    (T Θ : Finset (HeckeCharacter K)) (G : FixedBinTransferGeometry) : Prop :=
  (∀ u : FrequencyRow K S, ∀ χ ∈ physicalRowFamily K S ψ Θ P E u,
    MeromorphicZeroFreeOn (heckeContinuation K χ) (rightHalfPlane G.boundary)) →
  ∃ A B ceiling Z₀ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < ceiling ∧ 1 ≤ Z₀ ∧
    (∀ (Z d τ a : ℝ) (i : ℕ), Z₀ ≤ Z →
      FixedBinTransferRange G Z d τ a i → τ ≤ ceiling →
      (∀ u ∈ sourceBufferedRowBin K S P ψ E Θ G Z d τ a i,
        ∀ χ ∈ physicalRowFamily K S ψ Θ P E u, χ ≠ 1) →
      ∀ u ∈ sourceBufferedRowBin K S P ψ E Θ G Z d τ a i,
        rowVerticalAbsolutelyIntegrable K S μ P ψ E g T u Z 5 5 3 ∧
        IntegrableOn (rowVerticalKernel K S μ P ψ E g T u Z
          (a + 16 * G.e) (1 - a - 6 * G.e) (17 / 50))
          (rowRetainedHeightBox (G.contourFraction * Z ^ τ)) rowHeightVolume) ∧
    ∀ N : ℕ, ∃ C ZN : ℝ, 0 < C ∧ Z₀ ≤ ZN ∧
      ∀ (Z d τ a : ℝ) (i : ℕ), ZN ≤ Z →
        FixedBinTransferRange G Z d τ a i → τ ≤ ceiling →
        (∀ u ∈ sourceBufferedRowBin K S P ψ E Θ G Z d τ a i,
          ∀ χ ∈ physicalRowFamily K S ψ Θ P E u, χ ≠ 1) →
        ‖fixedBinFullVerticalIntegral K S μ P ψ E g T
            (sourceBufferedRowBin K S P ψ E Θ G Z d τ a i) Z 5 5 3 -
          bufferedFixedBinContour K S μ P ψ E g T Θ Z
            (G.contourFraction * Z ^ τ)
            (3 * (i : ℝ) * Z ^ τ) (3 * ((i : ℝ) + 1) * Z ^ τ)
            (Z ^ d / 2) (Z ^ d) a G.e‖ ≤
          C * Z ^ B * (1 + Z ^ τ) ^ A * (Z ^ τ) ^ (-(N : ℝ))

end HeckeGeneral.ThetaSkeleton.Physical
