import HeckeGeneral.Analysis.PhysicalProbeData
import HeckeGeneral.Arithmetic.SIntegerOrbitNorm
import HeckeGeneral.Analysis.SIntegerSixthPowerDecomposition
import HeckeGeneral.Analysis.FrequencyRowCounting
import HeckeGeneral.Analysis.TraceJointProfileBounds

/-! Exploratory sorry skeleton. The amplitude is the literal c=1 instance
of ActualAdditiveGramAmplitude.lean (revised (3.33)), copied without importing
that cache closure. No analytic estimate is a field of the definitions. -/
set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.Gram
open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open scoped Classical BigOperators ComplexConjugate
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

abbrev Orbit := SIntegerOrbits K S (sixthPowerUnits K S)

def gramTerm (P : ProbeData K S) (W : SmoothAnnularTest)
    (Y ν : ℝ) (m : S.integer K) (I : ExteriorIdeal K S) : ℂ :=
  W.toFun (exteriorNorm K S I / Y) *
    (((exteriorNorm K S I / Y : ℝ) : ℂ) ^
      ((-1 : ℂ) + Complex.I * (ν : ℂ))) * probeGauss K S P I (-m)

def amplitude (P : ProbeData K S) (W : SmoothAnnularTest)
    (Y ν : ℝ) (m : S.integer K) : ℂ :=
  ((Y ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
    ∑' I : ExteriorIdeal K S, gramTerm K S P W Y ν m I

/-- Representative evaluation is an honest definition; descent is a separate
obligation in Gram.lean. The index is the ORIGINAL sixth-unit quotient. -/
def orbitAmplitude (P : ProbeData K S) (W : SmoothAnnularTest)
    (Y ν : ℝ) (q : Orbit K S) : ℂ := amplitude K S P W Y ν q.out.val

def rowEnergy (P : ProbeData K S) (W : SmoothAnnularTest)
    (B Q Y ν : ℝ) : ℝ :=
  ∑' q : Orbit K S,
    if (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val ≤ B * Q
    then ‖orbitAmplitude K S P W Y ν q‖ ^ 2 else 0

def Pa (Q Y : ℝ) : ℝ := Y ^ 2 / Q

def gramScale (Q Y : ℝ) : ℝ :=
  Q / Y * (1 + Pa Q Y ^ (1 / 6 : ℝ) + Pa Q Y ^ 2 / Y)

/-- Revised Proposition 3.8 (pp.14–15), restricted to the ACTUAL T route
c=1, for the ACTUAL physical denominator `P.denominator` (the only test the
Low-Cauchy compensation uses). Polynomial budget L, row constant B and requested loss precede all
moving scales. The Mellin derivative order may depend on ε, but precedes all moving scales.
This does not claim the source's arbitrary finite-ray coefficient version. -/
def GramBound (P : ProbeData K S) : Prop :=
  ∀ (B L : ℝ), 0 < B → 0 < L →
    ∀ ε : ℝ, 0 < ε → ∃ J : ℕ,
      ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧
        ∀ (Z Q Y ν : ℝ), Z₀ ≤ Z → 1 ≤ Q → 1 ≤ Y →
          Q ≤ Z ^ L → Y ≤ Z ^ L → 1 ≤ Pa Q Y →
          rowEnergy K S P P.denominator.toSmoothAnnularTest B Q Y ν ≤
            C * (1 + |ν|) ^ J * gramScale Q Y * Z ^ ε

/-- All sixth-power descendants and all global unit sectors are counted. -/
def exceptional (C : NonzeroIdeal K) (q : Orbit K S) : Prop :=
  ∀ p : HeightOneSpectrum (𝓞 K), p ∉ idealPrimeSupport K C →
    6 ∣ primeExponents (actualSIntegerOrbitIdeal K S q) p

def ordinaryCutoff (X : ℝ) :=
  {q : Orbit K S // (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val ≤ X}
def exceptionalCutoff (C : NonzeroIdeal K) (X : ℝ) :=
  {q : ordinaryCutoff K S X // exceptional K S C q.val}

/-- The genuine zero-extended ideal residue character (including I=1). -/
def columnCharacter (P : ProbeData K S) (I : ExteriorIdeal K S)
    (x : ThetaQuotient K S I) : ℂ :=
  sIntegerSexticIdealQuotientFunction K S P.arithmetic.root6
    P.arithmetic.primitive6 P.arithmetic.embedding I.val.val
    (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => P.arithmetic.away_six p (I.property p hp)) x

/-- Literal complete two-column congruence sum. Choosing representatives
here does not discard nonunits or collision zeros. Its independence and
Fourier identification are obligations, not additional data. -/
def correlation (P : ProbeData K S) (I J : ExteriorIdeal K S)
    (j : S.integer K) : ℂ := by
  letI : Finite (ThetaQuotient K S I) := finite_sIntegerSexticIdealQuotient K S
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
  letI : Finite (ThetaQuotient K S J) := finite_sIntegerSexticIdealQuotient K S
    J.val.val (nonZeroDivisors.coe_ne_zero J.val) J.property
  letI : Fintype (ThetaQuotient K S I) := Fintype.ofFinite _
  letI : Fintype (ThetaQuotient K S J) := Fintype.ofFinite _
  exact ∑ x : ThetaQuotient K S I, ∑ y : ThetaQuotient K S J,
    if P.arithmetic.generator J * Classical.choose (Ideal.Quotient.mk_surjective x) -
        P.arithmetic.generator I * Classical.choose (Ideal.Quotient.mk_surjective y) - j ∈
        (exteriorMul K S I J).val.val.map (algebraMap (𝓞 K) (S.integer K))
    then columnCharacter K S P I x * conj (columnCharacter K S P J y) else 0

end HeckeSkeleton.Gram
