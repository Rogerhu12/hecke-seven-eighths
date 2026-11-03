import HeckeGeneral.Analysis.PrimeWindowGeometry
import HeckeGeneral.Analysis.MarkedThetaReflection
import HeckeGeneral.Analysis.SUnitSchwartzSlice
import HeckeGeneral.Analysis.SUnitHaar
import HeckeGeneral.Analysis.SIntegerSexticDyadicAmplification

/-!
The literal physical probe (P, poisson-probe) and M's finite compensation.
The Gaussian completed ideal sum, Gauss sum, S-unit fundamental domain,
tensor test, prime windows, subset rescalings and target phases are fixed
definitions. No free physical function or row-count estimate is data here.

This file does NOT assert convergence, descent of the integrand, a Poisson
identity, or the source's Haar/Fourier normalization. Those obligations must
be stated for these expressions before using them as the source's probe.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.SquarefreeAmplification
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors ContDiff

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Tensor Bruhat--Schwartz data, restricted to the local multiplicative
group. The actual tensor has compact support away from norm zero. -/
structure AdditiveProbeTest where
  infiniteTest : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ
  finiteTest : (p : S) → p.val.adicCompletion K → ℂ
  finite_locallyConstant : ∀ p, IsLocallyConstant (finiteTest p)
  finite_compactSupport : ∀ p, HasCompactSupport (finiteTest p)
  tensor_compactSupport : HasCompactSupport
    (sLocalTensorTestFunction K S infiniteTest (fun x => ∏ p : S, finiteTest p (x p)))
  lowerNorm : ℝ
  lowerNorm_pos : 0 < lowerNorm
  norm_support : ∀ x : sLocalMultiplicativeGroup K S,
    sLocalTensorTestFunction K S infiniteTest (fun y => ∏ p : S, finiteTest p (y p)) x ≠ 0 →
      lowerNorm ≤ sLocalProductNorm K S x

def additiveTest (W : AdditiveProbeTest K S) (x : sLocalMultiplicativeGroup K S) : ℂ :=
  sLocalTensorTestFunction K S W.infiniteTest (fun y => ∏ p : S, W.finiteTest p (y p)) x

/-- The annular additive-denominator weight is genuinely nonnegative. -/
structure DenominatorTest extends SmoothAnnularTest where
  nonnegative : ∀ y : ℝ, 0 ≤ (toFun y).re
  real_valued : ∀ y : ℝ, (toFun y).im = 0
  nonzero : ∃ y : ℝ, toFun y ≠ 0

structure ProbeData where
  arithmetic : ThetaArithmeticData K S
  Lambda : HeckeCharacter K
  G : HeckeCharacter K
  additive : AdditiveProbeTest K S
  denominator : DenominatorTest

def thetaPeriod (P : ProbeData K S) (ψ : HeckeCharacter K) : HeckeCharacter K :=
  conjugate P.Lambda * conjugate P.G * ψ

/-- The actual finite sum g_s(k), including the one-element quotient at s=1.
No squarefreeness restriction is imposed on the denominator ideal. -/
def probeGauss (P : ProbeData K S) (I : ExteriorIdeal K S) (k : S.integer K) : ℂ := by
  letI : Finite (ThetaQuotient K S I) :=
    finite_sIntegerSexticIdealQuotient K S I.val.val
      (nonZeroDivisors.coe_ne_zero I.val) I.property
  letI : Fintype (ThetaQuotient K S I) := Fintype.ofFinite _
  let χ := sIntegerSexticIdealQuotientFunction K S P.arithmetic.root6
    P.arithmetic.primitive6 P.arithmetic.embedding I.val.val
    (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => P.arithmetic.away_six p (I.property p hp))
  exact ∑ d : ThetaQuotient K S I,
    χ d * thetaPrincipalAddCharacter K S P.arithmetic I ((Ideal.Quotient.mk _ k) * d)

def probeRowTerm (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (X Z : ℝ)
    (t : sLocalNormOneGroup K S) (I : ExteriorIdeal K S)
    (m : NonzeroRingElements (S.integer K)) : ℂ :=
  if h : 0 < exteriorNorm K S I * X then
    (Real.sqrt (exteriorNorm K S I) : ℂ)⁻¹ * probeGauss K S P I (-m.val) *
      additiveTest K S P.additive
        (sLocalNonzeroIntegerDiagonal K S m /
          ((t : sLocalMultiplicativeGroup K S) *
            sLocalNormSection K S ⟨exteriorNorm K S I * X, h⟩)) *
      completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ) m.val
        (primeSetIdeal K S ∅) Q logGaussianProfile Z
  else 0

def probeDenominatorTerm (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (X Y Z : ℝ)
    (t : sLocalNormOneGroup K S) (I : ExteriorIdeal K S) : ℂ :=
  (Y : ℂ)⁻¹ * P.denominator.toFun (exteriorNorm K S I / Y) *
    (Real.sqrt (exteriorNorm K S I * X) : ℂ)⁻¹ *
      ∑' m : NonzeroRingElements (S.integer K), probeRowTerm K S P ψ Q X Z t I m

def sixthPowerUnits : Subgroup (S.unit K) :=
  (powMonoidHom 6 : S.unit K →* S.unit K).range

def probeIntegrand (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (X Y Z : ℝ)
    (t : sLocalNormOneGroup K S) : ℂ :=
  ∑' I : ExteriorIdeal K S, probeDenominatorTerm K S P ψ Q X Y Z t I

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]

/-- An integral over actual Haar representatives of U_S^6. Equality to a
quotient integral requires the concrete integrand's descent/integrability. -/
def physicalProbe (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (X Y Z : ℝ) : ℂ := by
  letI : (sixthPowerUnits K S).FiniteIndex :=
    sUnit_power_range_finiteIndex K S 6 (by decide)
  exact ∫ t in sUnitFundamentalDomain K S (sixthPowerUnits K S),
    probeIntegrand K S P ψ Q X Y Z t ∂(sUnitHaarMeasure K S)

/-- The window is filtered from the actual norm-bounded prime envelope.
The finite collection T defines the actual identity ray, rather than an
unconstrained prime predicate. Its source calibration remains explicit. -/
def primeWindow (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z : ℝ) (i : Fin g.slots) : Finset (ExteriorPrime K S) :=
  let F : Finset (HeightOneSpectrum (𝓞 K)) :=
    (finitePrimeEnvelope K (dyadicIdealSupport K (primeScale g Z))).filter
    (fun p => p ∉ S ∧ (∀ χ ∈ T, primeCoefficient K χ p = 1) ∧
      (g.weight i).toFun ((p.asIdeal.absNorm : ℝ) / primeScale g Z) ≠ 0)
  F.attach.image fun (p : {p : HeightOneSpectrum (𝓞 K) // p ∈ F}) =>
    (⟨p.val, (Finset.mem_filter.mp p.property).2.1⟩ : ExteriorPrime K S)

def windowWeight (g : PrimeWindowGeometry) (Z : ℝ) (i : Fin g.slots)
    (p : ExteriorPrime K S) : ℂ :=
  (g.weight i).toFun ((p.val.asIdeal.absNorm : ℝ) / primeScale g Z)

def subsetPrimeIdeal {g : PrimeWindowGeometry}
    (p : Fin g.slots → ExteriorPrime K S) (J : Finset (Fin g.slots)) : ExteriorIdeal K S :=
  primeSetIdeal K S (J.image p)

def compensationTerm (P : ProbeData K S) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z : ℝ) (p : Fin g.slots → ExteriorPrime K S)
    (J : Finset (Fin g.slots)) : ℂ :=
  let selected := subsetPrimeIdeal K S p J
  let marked := subsetPrimeIdeal K S p (Finset.univ \ J)
  (-1 : ℂ) ^ J.card * (exteriorNorm K S selected : ℂ) ^ (-(3 / 2 : ℂ)) *
    conj (heckeIdealCoefficient K ψ marked.val) *
    physicalProbe K S P ψ ((Finset.univ \ J).image p)
      (Z ^ (17 / 48 : ℝ) / exteriorNorm K S selected)
      (Z ^ (23 / 48 : ℝ) / exteriorNorm K S selected)
      (Z * exteriorNorm K S marked)

/-- Literal finite-window compensation; both subset ideals are whole-index
marks. All target factors are actual Hecke ideal coefficients. -/
def compensatedProbe (P : ProbeData K S) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ) : ℂ :=
  ∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
    (∏ i : Fin g.slots, windowWeight K S g Z i (p i)) *
      ∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
        compensationTerm K S P ψ g Z p J

end HeckeGeneral.ThetaSkeleton.Physical
