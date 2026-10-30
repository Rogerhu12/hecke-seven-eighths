import HeckeGeneral.Characters.SIntegerModulusPhaseUnit
import HeckeGeneral.Characters.SIntegerSexticIdealEvaluation
import HeckeGeneral.Characters.InfinityPacket
import HeckeGeneral.Analysis.HeckeSeries
import HeckeGeneral.Arithmetic.IdealMobiusMask

/-!

Explicit arithmetic and LOCAL DIGIT fragments of the theta input.
`LocalThetaInput` below is deliberately only the local digit interface of
P Proposition 5.1(ii). It is not a global KP theta construction.
No existing KP representation/Whittaker type is claimed. In particular,
this file does not provide a global Fourier expansion or reflection theorem.

The Gauss quantities are actual sums on actual S-integer quotients with
the literal principal phase e(x/c), using the already proved phase-unit
correction. Generators are explicit input data. Their compatibility with
an isotropic allowed-generator section remains a separate obligation.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton
open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.Arithmetic.ResidueTraceCharacters
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Ordinary nonzero integral ideals with every prime divisor outside S. -/
abbrev ExteriorIdeal :=
  {I : NonzeroIdeal K // ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → p ∉ S}

abbrev ExteriorPrime := {p : HeightOneSpectrum (𝓞 K) // p ∉ S}

/-- Actual number-field arithmetic data; no representation-theoretic datum
or analytic conclusion is hidden in this structure. -/
structure ThetaArithmeticData where
  root12 : K
  primitive12 : IsPrimitiveRoot root12 12
  root6 : K
  primitive6 : IsPrimitiveRoot root6 6
  embedding : K →+* ℂ
  away_six : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → (6 : 𝓞 K) ∉ p.asIdeal
  different_outside : ∀ p : HeightOneSpectrum (𝓞 K),
    p ∉ S → localDifferentExponent K p = 0
  generator : ExteriorIdeal K S → S.integer K
  generator_ne_zero : ∀ I, generator I ≠ 0
  generator_span : ∀ I,
    Ideal.span ({generator I} : Set (S.integer K)) =
      I.val.val.map (algebraMap (𝓞 K) (S.integer K))

variable (D : ThetaArithmeticData K S)

abbrev ThetaQuotient (I : ExteriorIdeal K S) :=
  S.integer K ⧸ I.val.val.map (algebraMap (𝓞 K) (S.integer K))

/-- The actual additive character e(x/c), transported only across the
proved equality span(c) = I.map. Its phase-unit correction is retained. -/
def thetaPrincipalAddCharacter (I : ExteriorIdeal K S) :
    AddChar (ThetaQuotient K S I) ℂ :=
  transportCharacter (Ideal.quotEquivOfEq (D.generator_span I).symm)
    (sIntegerActualModulusAddCharacter K S D.different_outside
      (D.generator I) (D.generator_ne_zero I))

theorem thetaPrincipalAddCharacter_mk (I : ExteriorIdeal K S) (a : S.integer K) :
    thetaPrincipalAddCharacter K S D I (Ideal.Quotient.mk _ a) =
      sLocalPrincipalPhase K S ((a : K) / (D.generator I : K)) := by
  unfold thetaPrincipalAddCharacter
  rw [transportCharacter_apply, Ideal.quotEquivOfEq_mk,
    sIntegerActualModulusAddCharacter_mk]

theorem thetaPrincipalAddCharacter_isPrimitive (I : ExteriorIdeal K S) :
    (thetaPrincipalAddCharacter K S D I).IsPrimitive :=
  transportCharacter_isPrimitive _ _
    (sIntegerActualModulusAddCharacter_isPrimitive K S D.different_outside
      (D.generator I) (D.generator_ne_zero I))

/-- Actual normalized finite Gauss sum. Only positive j (in particular
j=1,2,3) is used; no convention for the zeroth MulChar power is asserted. -/
def thetaGamma (I : ExteriorIdeal K S) (j : ℕ) : ℂ := by
  letI : Finite (ThetaQuotient K S I) :=
    finite_sIntegerSexticIdealQuotient K S I.val.val
      (nonZeroDivisors.coe_ne_zero I.val) I.property
  letI : Fintype (ThetaQuotient K S I) := Fintype.ofFinite _
  let χ := sIntegerSexticIdealQuotientFunction K S D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp))
  exact (Real.sqrt (I.val.val.absNorm : ℝ) : ℂ)⁻¹ *
    ∑ x : ThetaQuotient K S I, χ x ^ j * thetaPrincipalAddCharacter K S D I x

def exteriorPrimeIdeal (p : ExteriorPrime K S) : ExteriorIdeal K S :=
  ⟨⟨p.val.asIdeal, mem_nonZeroDivisors_of_ne_zero p.val.ne_bot⟩, by
    intro q hq
    have he : p.val.asIdeal = q.asIdeal :=
      p.val.isMaximal.eq_of_le q.isPrime.ne_top (Ideal.dvd_iff_le.mp hq)
    have hqp : q = p.val := HeightOneSpectrum.ext he.symm
    simpa only [hqp] using p.property⟩

def thetaPrimeCharacter (p : ExteriorPrime K S) : MulChar (𝓞 K ⧸ p.val.asIdeal) ℂ :=
  sexticResidueCharacter K D.root6 D.primitive6 D.embedding p.val
    (D.away_six p.val p.property)

/-- A table indexed by actual valuations and actual residue-field units.
This is not called a KP representation or an existing Whittaker function. -/
abbrev ThetaDigitTable :=
  ∀ p : ExteriorPrime K S, ℤ → (𝓞 K ⧸ p.val.asIdeal)ˣ → ℂ

/-- The precise local digit fragment of P Proposition 5.1(ii).
The supplied table must obey the actual Gauss normalization and all four
valuation branches. Existence/realization as KP Whittaker data is not proved. -/
structure LocalThetaInput (W : ThetaDigitTable K S) : Prop where
  gauss_norm : ∀ p : ExteriorPrime K S,
    ‖thetaGamma K S D (exteriorPrimeIdeal K S p) 2‖ = 1
  negative : ∀ p e u, e < 0 → W p e u = 0
  triple : ∀ (p : ExteriorPrime K S) (k : ℕ) u,
    W p (3 * (k : ℤ)) u =
      thetaPrimeCharacter K S D p u ^ (6 * k) * (p.val.asIdeal.absNorm : ℂ)⁻¹ ^ k
  triple_one : ∀ (p : ExteriorPrime K S) (k : ℕ) u,
    W p (3 * (k : ℤ) + 1) u =
      thetaPrimeCharacter K S D p u ^ (6 * k + 2) *
        (p.val.asIdeal.absNorm : ℂ)⁻¹ ^ k *
        (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ *
        thetaGamma K S D (exteriorPrimeIdeal K S p) 2
  triple_two : ∀ (p : ExteriorPrime K S) (k : ℕ) u,
    W p (3 * (k : ℤ) + 2) u = 0

theorem LocalThetaInput.normalized (W : ThetaDigitTable K S)
    (h : LocalThetaInput K S D W) (p : ExteriorPrime K S) : W p 0 1 = 1 := by
  simpa using h.triple p 0 1

/-- Independent arithmetic calibration. Lambda and G are genuine continuous
unitary idèle-class characters; their coefficients are the existing actual
Hecke ideal coefficients. The identities are assumptions, not axioms and
not definitions of Lambda or G from the Gauss sums. -/
structure ThetaCalibrationInput (Lambda G : HeckeCharacter K) : Prop where
  lambda_unramified : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K Lambda p
  G_unramified : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K G p
  G_finite_order : FiniteOrder G
  lambda_angular : ∀ (v : InfinitePlace K) (hv : v.IsComplex),
    heckeComplexWeight K v hv Lambda = 1 ∨ heckeComplexWeight K v hv Lambda = -1
  lambda_radial_zero : ∀ (v : InfinitePlace K) (hv : v.IsComplex),
    heckeComplexParameter K v hv Lambda = 0
  cube_calibration : ∀ I : ExteriorIdeal K S, Squarefree I.val.val →
    thetaGamma K S D I 2 ^ 3 =
      (UniqueFactorizationMonoid.moebius I.val.val : ℂ) * heckeIdealCoefficient K Lambda I.val
  mixed_calibration : ∀ I : ExteriorIdeal K S, Squarefree I.val.val →
    conj (heckeIdealCoefficient K Lambda I.val) * thetaGamma K S D I 2 *
      thetaGamma K S D I 1 =
        (UniqueFactorizationMonoid.moebius I.val.val : ℂ) * heckeIdealCoefficient K G I.val

end HeckeGeneral.ThetaSkeleton
