import HeckeGeneral.Analysis.PhysicalProbeData
import HeckeGeneral.Analysis.HeckeEulerDeletion
import HeckeGeneral.Bridge.SIntegerFourierFactorization

/-!
Actual principal Euler factor, finite positive normalizer, additive Fourier
Mellin normalization, and the height-free line-2 detector of M Section 5.
No analyticity, contraction, residue calculation, or line identity is
asserted merely by defining these expressions.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global NumberField.AdelicFourier
open NumberField.StandardAddChar
open scoped Classical BigOperators ComplexConjugate Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def exceptionalPrimes : Finset (HeightOneSpectrum (𝓞 K)) :=
  Finset.univ.image (fun p : S => p.val)

/-- P's literal local sum before extracting the three Euler factors. -/
def localProbeEulerSum (P : ProbeData K S) (ψ χ : HeckeCharacter K)
    (p : ExteriorPrime K S) (s w z : ℂ) : ℂ :=
  let Q : ℂ := (p.val.asIdeal.absNorm : ℂ)
  let V := Q ^ (-6 * z)
  let W := primeCoefficient K χ p.val * Q ^ (-w)
  let D := primeCoefficient K ψ p.val * conj (primeCoefficient K χ p.val) * Q ^ (-s)
  let E := primeCoefficient K (thetaPeriod K S P ψ) p.val ^ 6 * Q ^ (4 - 6 * s) * V
  (1 - V)⁻¹ + W / (1 - W) +
    E / (1 - E) * ((1 - Q⁻¹) / (1 - V) + W) -
    D / (1 - E) * (1 + (Q - 1) * W * V / (1 - V))

def localPrincipalCorrection (P : ProbeData K S) (ψ : HeckeCharacter K)
    (p : ExteriorPrime K S) (s : ℂ) : ℂ :=
  let Q : ℂ := (p.val.asIdeal.absNorm : ℂ)
  localProbeEulerSum K S P ψ 1 p s 1 (1 / 6) *
    (1 - Q⁻¹) * (1 - Q⁻¹) / (1 - primeCoefficient K ψ p.val * Q ^ (-s))

def principalCorrection (P : ProbeData K S) (ψ : HeckeCharacter K) (s : ℂ) : ℂ :=
  ∏' p : ExteriorPrime K S, localPrincipalCorrection K S P ψ p s

/-- The marked part is obtained by removing exactly the unmarked n=0
branches of the literal local sum. This does not divide by that sum. -/
def localMarkedProbeEulerSum (P : ProbeData K S) (ψ χ : HeckeCharacter K)
    (p : ExteriorPrime K S) (s w z : ℂ) : ℂ :=
  let Q : ℂ := (p.val.asIdeal.absNorm : ℂ)
  let V := Q ^ (-6 * z)
  let W := primeCoefficient K χ p.val * Q ^ (-w)
  localProbeEulerSum K S P ψ χ p s w z - ((1 - V)⁻¹ + W / (1 - W))

/-- The full correction G_p from M, with no division by possibly zero P_p. -/
def localCompensatedEulerCorrection (P : ProbeData K S) (ψ χ : HeckeCharacter K)
    (p : ExteriorPrime K S) (s w z : ℂ) : ℂ :=
  let Q : ℂ := (p.val.asIdeal.absNorm : ℂ)
  let V := Q ^ (-6 * z)
  let W := primeCoefficient K χ p.val * Q ^ (-w)
  let D := primeCoefficient K ψ p.val * conj (primeCoefficient K χ p.val) * Q ^ (-s)
  ((conj (primeCoefficient K ψ p.val) * Q ^ s - Q ^ (-w)) *
    (1 - V) * (1 - W) * localMarkedProbeEulerSum K S P ψ χ p s w z -
      Q ^ (-w) * (1 - V * W)) / (1 - D)

/-- The principal correction after the actual finite window sums. For each
tuple the selected Euler factors are replaced before taking the product;
there is no division by H_p either. -/
def compensatedPrincipalCorrection (P : ProbeData K S) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ) (s : ℂ) : ℂ :=
  ∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
    (∏' q : ExteriorPrime K S,
      if q ∈ Finset.univ.image p then 1 else localPrincipalCorrection K S P ψ q s) *
    ∏ i : Fin g.slots,
      windowWeight K S g Z i (p i) * ((p i).val.asIdeal.absNorm : ℂ) ^ (-(5 / 6 : ℂ)) *
        localCompensatedEulerCorrection K S P ψ 1 (p i) s 1 (1 / 6)

def normalizerSlot (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z : ℝ) (i : Fin g.slots) : ℂ :=
  ∑ p ∈ primeWindow K S g T Z i,
    windowWeight K S g Z i p * (p.val.asIdeal.absNorm : ℂ) ^ (-(5 / 6 : ℂ))

def primeNormalizer (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z : ℝ) : ℂ :=
  (-1 : ℂ) ^ g.slots * (Z : ℂ) ^ (-(1 / 36 : ℂ)) *
    ∏ i : Fin g.slots, normalizerSlot K S g T Z i

def principalSlotSaving (g : PrimeWindowGeometry) : ℝ := 7 / (96 * g.slots)

theorem principalSlotSaving_pos (g : PrimeWindowGeometry) :
    0 < principalSlotSaving g := by
  have hslots : (0 : ℝ) < g.slots := by exact_mod_cast g.slots_pos
  unfold principalSlotSaving
  positivity

/-- A specific actual entire pole-cleared Dedekind zeta numerator, supplied
by the audited Dedekind theorem, rather than an arbitrary residue scalar. -/
def dedekindPoleCleared : ℂ → ℂ :=
  Classical.choose
    (NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero K)

def deletedZetaResidue : ℂ :=
  dedekindPoleCleared K 1 * heckeEulerDeletionPolynomial K 1 (exceptionalPrimes K S) 1

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S, BorelSpace (p.val.adicCompletion K)]

/- Measures are explicit additive Haar measures at the actual S-places.
The normalization of the tensor transform below retains their masses. -/
variable (μ : (p : S) → Measure (p.val.adicCompletion K))
variable [∀ p : S, (μ p).IsAddHaarMeasure]

def additiveFourier (W : AdditiveProbeTest K S)
    (x : sLocalMultiplicativeGroup K S) : ℂ :=
  fourierIntegral (HeckeGeneral.Bridge.standardMixedAddCharacter K) volume
    (fun y => W.infiniteTest ((traceToMixed K).symm y))
    (x.1 : mixedEmbedding.mixedSpace K) *
  ∏ p : S, (((μ p).real (p.val.adicCompletionIntegers K : Set (p.val.adicCompletion K)) : ℂ))⁻¹ *
    fourierIntegral (psiLocal K p.val) (μ p) (W.finiteTest p) (x.2 p).val

def additiveFourierAtZero (W : AdditiveProbeTest K S) : ℂ :=
  fourierIntegral (HeckeGeneral.Bridge.standardMixedAddCharacter K) volume
    (fun y => W.infiniteTest ((traceToMixed K).symm y)) 0 *
  ∏ p : S, (((μ p).real (p.val.adicCompletionIntegers K : Set (p.val.adicCompletion K)) : ℂ))⁻¹ *
    fourierIntegral (psiLocal K p.val) (μ p) (W.finiteTest p) 0

/-- The multiplicative Haar measure is defined by the source's radial
decomposition du/u dt, with precisely the same norm-one Haar as the probe.
Its comparison with the additive/Fourier measures is a separate input. -/
def additiveMellin (W : AdditiveProbeTest K S) (z : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ),
    if hu : 0 < u then
      (∫ t : sLocalNormOneGroup K S,
        additiveFourier K S μ W
          ((t : sLocalMultiplicativeGroup K S) * sLocalNormSection K S ⟨u, hu⟩)
          ∂(sUnitHaarMeasure K S)) * (u : ℂ) ^ z / (u : ℂ)
    else 0

def physicalResidueNormalizer (P : ProbeData K S) : ℂ :=
  (1 / 6 : ℂ) * deletedZetaResidue K S ^ 2 *
    additiveMellin K S μ P.additive (1 / 6) * mellin P.denominator.toFun 1

def normalizedProbe (P : ProbeData K S) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ) : ℂ :=
  compensatedProbe K S P ψ g T Z /
    (physicalResidueNormalizer K S μ P * primeNormalizer K S g T Z)

/-- M's f has no target-dependent height cutoff. Parametrizing s=2+it
cancels the i in ds/(2 pi i). The numerator and denominator are actual. -/
def principalLineProbe (P : ProbeData K S) (ψ : HeckeCharacter K) (Z : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ,
    let s : ℂ := 2 + (t : ℂ) * Complex.I
    (Z : ℂ) ^ (s - 11 / 16) * Complex.exp ((s - 5 / 6) ^ 2) *
      principalCorrection K S P ψ s /
        heckeDeletedContinuation K ψ (exceptionalPrimes K S) s

end HeckeGeneral.ThetaSkeleton.Physical
