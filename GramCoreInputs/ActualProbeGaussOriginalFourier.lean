import HeckeGeneral.Analysis.PhysicalProbeData
import SIntegerSexticOriginalFullTraceFourier

/-!
UNCOMPILED / native 0. The physical probe's ideal-quotient Gauss sums are
identified with the literal positive-trace columns of the original full
correlation. The principal generator contraction is proved from generator_span
and S-coprimality. Zero and nonunit frequencies, nonsquarefree denominators,
and the one-element unit-ideal quotient are retained. No new additive phase,
primitivity, coprimality between the columns, or calibration input is assumed.
-/

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualProbeGaussFourierDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic.PeriodicFourier
open HeckeGeneral.Arithmetic.ResidueTraceCharacters
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "R" => S.integer K
local notation "N" => NonzeroRingElements R
local notation "Column" => (fun u : N => R ⧸ commonFactorColumnIdeal (⊤ : Ideal R) (Subtype.val u))
local notation "Total" => (fun u v : N => R ⧸ commonFactorTotalIdeal (⊤ : Ideal R) (Subtype.val u) (Subtype.val v))

local instance probeOriginal_columnFinite (u : N) : Finite (Column u) := by
  change Finite (R ⧸ ((⊤ : Ideal R) * Ideal.span ({u.val} : Set R)))
  rw [Ideal.top_mul]
  exact finite_sIntegerPrincipalResidue K S u.val u.property

local instance probeOriginal_columnFintype (u : N) : Fintype (Column u) := Fintype.ofFinite _

local instance probeOriginal_totalFinite (u v : N) : Finite (Total u v) := by
  letI : Finite (R ⧸ Ideal.span ({u.val * v.val} : Set R)) :=
    finite_sIntegerPrincipalResidue K S _ (mul_ne_zero u.property v.property)
  exact Finite.of_equiv _ (originalFullTotalPrincipalEquiv K S u v).symm.toEquiv

local instance probeOriginal_totalFintype (u v : N) : Fintype (Total u v) := Fintype.ofFinite _

local instance probeOriginal_thetaFinite (I : ExteriorIdeal K S) :
    Finite (ThetaQuotient K S I) :=
  finite_sIntegerSexticIdealQuotient K S I.val.val
    (nonZeroDivisors.coe_ne_zero I.val) I.property

local instance probeOriginal_thetaFintype (I : ExteriorIdeal K S) :
    Fintype (ThetaQuotient K S I) := Fintype.ofFinite _

/-- The actual nonzero generator, with its existing proof of nonvanishing. -/
def probeGenerator (D : ThetaArithmeticData K S) (I : ExteriorIdeal K S) : N :=
  ⟨D.generator I, D.generator_ne_zero I⟩

/-- The original symbol's bad-six support is constructed from the arithmetic
field, rather than added as an independent premise. -/
theorem probeArithmetic_six_support (D : ThetaArithmeticData K S) :
    integerPrimeSupport (6 : 𝓞 K) ⊆ S := by
  intro p hp
  by_contra hpS
  exact D.away_six p hpS hp

/-- Same proof as the verified contraction_thetaGenerator: principal span,
then the actual extension/contraction identity for an S-coprime ideal. -/
theorem probeGenerator_contraction (D : ThetaArithmeticData K S) (I : ExteriorIdeal K S) :
    sIntegerModulusContraction K S (probeGenerator K S D I).val = I.val.val := by
  change Ideal.under (𝓞 K) (Ideal.span ({D.generator I} : Set R)) = I.val.val
  rw [D.generator_span]
  exact under_map_coprime_sIntegerIdeal K S I.val.val
    (sexticIdeal_coprime_S K S I.val.val I.property)

/-- The full original principal column is exactly the probe's actual ideal
quotient. Its representative is unchanged; no choice of integer lift occurs. -/
def probeGeneratorColumnEquiv (D : ThetaArithmeticData K S) (I : ExteriorIdeal K S) :
    Column (probeGenerator K S D I) ≃+* ThetaQuotient K S I :=
  Ideal.quotEquivOfEq (by
    rw [commonFactorColumnIdeal, Ideal.top_mul]
    exact D.generator_span I)

@[simp] theorem probeGeneratorColumnEquiv_mk (D : ThetaArithmeticData K S)
    (I : ExteriorIdeal K S) (a : R) :
    probeGeneratorColumnEquiv K S D I (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ a :=
  Ideal.quotEquivOfEq_mk _ _

/-- The actual ideal quotient function is the original full column symbol,
including its zero values at every bad numerator. -/
theorem probeQuotientFunction_eq_originalColumnWeight (D : ThetaArithmeticData K S)
    (I : ExteriorIdeal K S) (x : Column (probeGenerator K S D I)) :
    sIntegerSexticIdealQuotientFunction K S D.root6 D.primitive6 D.embedding
        I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
        (fun p hp => D.away_six p (I.property p hp))
        (probeGeneratorColumnEquiv K S D I x) =
      originalColumnWeight K S D.root6 D.primitive6 D.embedding
        (probeArithmetic_six_support K S D) (probeGenerator K S D I) x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [probeGeneratorColumnEquiv_mk, sIntegerSexticIdealQuotientFunction_mk,
    originalColumnWeight_mk]
  unfold sIntegerSexticSymbol
  simp only [probeGenerator_contraction K S D I]

/-- On actual representatives the positive total trace character restricts
to the probe phase e(m*a/u). The other generator v cancels in K. -/
theorem probePrincipalPhase_eq_original_first (D : ThetaArithmeticData K S)
    (I J : ExteriorIdeal K S) (m : R) (x : Column (probeGenerator K S D I)) :
    thetaPrincipalAddCharacter K S D I
        (Ideal.Quotient.mk _ m * probeGeneratorColumnEquiv K S D I x) =
      originalFullPositiveTraceCharacter K S D.different_outside
        (probeGenerator K S D I) (probeGenerator K S D J)
        (Ideal.Quotient.mk _ m * commonFactorFirstMultiplier (⊤ : Ideal R)
          (probeGenerator K S D I).val (probeGenerator K S D J).val x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [probeGeneratorColumnEquiv_mk, ← map_mul, thetaPrincipalAddCharacter_mk]
  change sLocalPrincipalPhase K S (((m * a : R) : K) / (D.generator I : K)) =
    originalFullPositiveTraceCharacter K S D.different_outside
      (probeGenerator K S D I) (probeGenerator K S D J)
      (Ideal.Quotient.mk _ (m * (D.generator J * a)))
  rw [originalFullPositiveTraceCharacter_mk]
  apply congrArg (sLocalPrincipalPhase K S)
  have hu : (D.generator I : K) ≠ 0 := fun h => D.generator_ne_zero I (Subtype.ext h)
  have hv : (D.generator J : K) ≠ 0 := fun h => D.generator_ne_zero J (Subtype.ext h)
  change (m : K) * (a : K) / (D.generator I : K) =
    (m : K) * ((D.generator J : K) * (a : K)) /
      ((D.generator I : K) * (D.generator J : K))
  field_simp [hu, hv] <;> ring

/-- The second column has the same positive sign e(m*a/v); the subtraction
in the original correlation is accounted for only by conjugating this column. -/
theorem probePrincipalPhase_eq_original_second (D : ThetaArithmeticData K S)
    (I J : ExteriorIdeal K S) (m : R) (x : Column (probeGenerator K S D J)) :
    thetaPrincipalAddCharacter K S D J
        (Ideal.Quotient.mk _ m * probeGeneratorColumnEquiv K S D J x) =
      originalFullPositiveTraceCharacter K S D.different_outside
        (probeGenerator K S D I) (probeGenerator K S D J)
        (Ideal.Quotient.mk _ m * commonFactorSecondMultiplier (⊤ : Ideal R)
          (probeGenerator K S D I).val (probeGenerator K S D J).val x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [probeGeneratorColumnEquiv_mk, ← map_mul, thetaPrincipalAddCharacter_mk]
  change sLocalPrincipalPhase K S (((m * a : R) : K) / (D.generator J : K)) =
    originalFullPositiveTraceCharacter K S D.different_outside
      (probeGenerator K S D I) (probeGenerator K S D J)
      (Ideal.Quotient.mk _ (m * (D.generator I * a)))
  rw [originalFullPositiveTraceCharacter_mk]
  apply congrArg (sLocalPrincipalPhase K S)
  have hu : (D.generator I : K) ≠ 0 := fun h => D.generator_ne_zero I (Subtype.ext h)
  have hv : (D.generator J : K) ≠ 0 := fun h => D.generator_ne_zero J (Subtype.ext h)
  change (m : K) * (a : K) / (D.generator J : K) =
    (m : K) * ((D.generator I : K) * (a : K)) /
      ((D.generator I : K) * (D.generator J : K))
  field_simp [hu, hv] <;> ring

/-- The actual physical Gauss sum is the first positive-trace Fourier column.
The frequency m is arbitrary and the second ideal need not be coprime to I. -/
theorem probeGauss_eq_original_firstColumn (P : ProbeData K S)
    (I J : ExteriorIdeal K S) (m : R) :
    probeGauss K S P I m =
      ∑ x : Column (probeGenerator K S P.arithmetic I),
        originalColumnWeight K S P.arithmetic.root6 P.arithmetic.primitive6
          P.arithmetic.embedding (probeArithmetic_six_support K S P.arithmetic)
          (probeGenerator K S P.arithmetic I) x *
        originalFullPositiveTraceCharacter K S P.arithmetic.different_outside
          (probeGenerator K S P.arithmetic I) (probeGenerator K S P.arithmetic J)
          (Ideal.Quotient.mk _ m * commonFactorFirstMultiplier (⊤ : Ideal R)
            (probeGenerator K S P.arithmetic I).val (probeGenerator K S P.arithmetic J).val x) := by
  unfold probeGauss
  symm
  apply Fintype.sum_equiv (probeGeneratorColumnEquiv K S P.arithmetic I).toEquiv
  intro x
  exact congrArg₂ (fun a b : ℂ => a * b)
    (probeQuotientFunction_eq_originalColumnWeight K S P.arithmetic I x).symm
    (probePrincipalPhase_eq_original_first K S P.arithmetic I J m x).symm

/-- The actual second probe Gauss sum is the second positive-trace column. -/
theorem probeGauss_eq_original_secondColumn (P : ProbeData K S)
    (I J : ExteriorIdeal K S) (m : R) :
    probeGauss K S P J m =
      ∑ x : Column (probeGenerator K S P.arithmetic J),
        originalColumnWeight K S P.arithmetic.root6 P.arithmetic.primitive6
          P.arithmetic.embedding (probeArithmetic_six_support K S P.arithmetic)
          (probeGenerator K S P.arithmetic J) x *
        originalFullPositiveTraceCharacter K S P.arithmetic.different_outside
          (probeGenerator K S P.arithmetic I) (probeGenerator K S P.arithmetic J)
          (Ideal.Quotient.mk _ m * commonFactorSecondMultiplier (⊤ : Ideal R)
            (probeGenerator K S P.arithmetic I).val (probeGenerator K S P.arithmetic J).val x) := by
  unfold probeGauss
  symm
  apply Fintype.sum_equiv (probeGeneratorColumnEquiv K S P.arithmetic J).toEquiv
  intro x
  exact congrArg₂ (fun a b : ℂ => a * b)
    (probeQuotientFunction_eq_originalColumnWeight K S P.arithmetic J x).symm
    (probePrincipalPhase_eq_original_second K S P.arithmetic I J m x).symm

/-- Exact positive-sign, unnormalized finite Fourier identity on OS/(u*v),
where u and v are the SAME actual P generators. All frequencies remain. -/
theorem probeGauss_mul_conj_eq_originalFull_fourier (P : ProbeData K S)
    (I J : ExteriorIdeal K S) (m : R) :
    probeGauss K S P I m * conj (probeGauss K S P J m) =
      fourier
        (originalFullPositiveTraceCharacter K S P.arithmetic.different_outside
          (probeGenerator K S P.arithmetic I) (probeGenerator K S P.arithmetic J))
        (sIntegerSexticOriginalFullQuotientCorrelation K S
          P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding
          (probeArithmetic_six_support K S P.arithmetic)
          (probeGenerator K S P.arithmetic I) (probeGenerator K S P.arithmetic J))
        (Ideal.Quotient.mk _ m) := by
  rw [fourier_sIntegerSexticOriginalFullQuotientCorrelation,
    ← probeGauss_eq_original_firstColumn K S P I J m,
    ← probeGauss_eq_original_secondColumn K S P I J m]

end HeckeGeneral.ThetaSkeleton.Physical.ActualProbeGaussFourierDraft
