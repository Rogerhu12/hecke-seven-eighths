import HeckeGeneral.Analysis.GlobalThetaData
import HeckeGeneral.Analysis.IdealSquarefreeSupport

/-!
Coefficient-level marked reflection, supplement (Omega)--(expansion).
Every summand below is defined from actual ideals, actual residue characters,
actual finite Gauss sums, and the explicit Mellin kernel of GlobalThetaData.
The reflection equality is an INPUT Prop, not a theorem constructing KP.
The redundant sums over class slices s_d,s_c are removed by evaluating the
kernel at the actual frequency class; no arithmetic sector is discarded.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Global
open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.SquarefreeAmplification
open scoped Classical BigOperators nonZeroDivisors ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

def primeSetIdeal (T : Finset (ExteriorPrime K S)) : ExteriorIdeal K S :=
  ⟨squarefreeIdeal K (T.image Subtype.val), by
    intro p hp
    have hm : p ∈ T.image Subtype.val := by
      have h := (mem_idealPrimeSupport_iff K _ p).mpr hp
      simpa only [idealPrimeSupport_squarefreeIdeal] using h
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hm
    exact hq ▸ q.property⟩

def exteriorSupport (I : ExteriorIdeal K S) : Finset (ExteriorPrime K S) :=
  (idealPrimeSupport K I.val).attach.image fun
    (p : {p : HeightOneSpectrum (𝓞 K) // p ∈ idealPrimeSupport K I.val}) =>
    (⟨p.val, I.property p.val ((mem_idealPrimeSupport_iff K I.val p.val).mp p.property)⟩ :
      ExteriorPrime K S)

/-- Remove ALL copies of p from the actual ideal exponent vector. -/
def removePrime (I : ExteriorIdeal K S) (p : ExteriorPrime K S) : ExteriorIdeal K S :=
  ⟨idealOfPrimeExponents ((primeExponents I.val).erase p.val), by
    intro q hq
    have hne : primeExponents
        (idealOfPrimeExponents ((primeExponents I.val).erase p.val)) q ≠ 0 :=
      Finsupp.mem_support_iff.mp ((mem_idealPrimeSupport_iff K _ q).mpr hq)
    rw [primeExponents_idealOfPrimeExponents] at hne
    have hqi : primeExponents I.val q ≠ 0 := by
      by_cases he : q = p.val
      · subst q
        simp at hne
      · simpa only [Finsupp.erase_ne he] using hne
    exact I.property q ((mem_idealPrimeSupport_iff K I.val q).mp
      (Finsupp.mem_support_iff.mpr hqi))⟩

def primeEvaluation (p : ExteriorPrime K S) (a : S.integer K) : ℂ :=
  sIntegerSexticEvaluation K S p.val p.property D.root6 D.primitive6 D.embedding
    (D.away_six p.val p.property) a

def primePhase (p : ExteriorPrime K S) (x : 𝓞 K ⧸ p.val.asIdeal) : ℂ :=
  thetaPrincipalAddCharacter K S D (exteriorPrimeIdeal K S p)
    (sIntegerResidueEquiv K S p.val.asIdeal
      (sIntegerSexticResidue_coprime K S p.val p.property) x)

def localTau (p : ExteriorPrime K S) (j : Fin 6) : ℂ := by
  letI : Fintype (𝓞 K ⧸ p.val.asIdeal) := Fintype.ofFinite _
  exact ∑ x : (𝓞 K ⧸ p.val.asIdeal)ˣ,
    thetaPrimeCharacter K S D p x ^ (-(j.val : ℤ)) * primePhase K S D p x

/-- j=0 is the unit mask, not the constant zeroth MulChar power. -/
def digitMask (p : ExteriorPrime K S) (j : Fin 6)
    (x : 𝓞 K ⧸ p.val.asIdeal) : ℂ :=
  if j.val = 0 then
    if x = 0 then 1 - (p.val.asIdeal.absNorm : ℂ)⁻¹
    else -(p.val.asIdeal.absNorm : ℂ)⁻¹
  else (localTau K S D p j)⁻¹ * thetaPrimeCharacter K S D p x ^ (-(j.val : ℤ))

def sphericalDigit (p : ExteriorPrime K S) (e : ℕ) : ℂ :=
  if e % 3 = 0 then (p.val.asIdeal.absNorm : ℂ)⁻¹ ^ (e / 3)
  else if e % 3 = 1 then
    (p.val.asIdeal.absNorm : ℂ)⁻¹ ^ (e / 3) *
      (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ *
      thetaGamma K S D (exteriorPrimeIdeal K S p) 2
  else 0

/-- P's local Weyl scalar R_(p,j,e)(1), defined by the ACTUAL finite sum.
For e>0 the additive argument p^(e-1)/v is integral and its phase is 1. -/
def localWeylScalar (p : ExteriorPrime K S) (j : Fin 6) (e : ℕ) : ℂ := by
  letI : Fintype (𝓞 K ⧸ p.val.asIdeal) := Fintype.ofFinite _
  exact sphericalDigit K S D p e *
    ∑ x : (𝓞 K ⧸ p.val.asIdeal)ˣ,
      digitMask K S D p j x * thetaPrimeCharacter K S D p x ^ 4 *
        (if e = 0 then primePhase K S D p ((x⁻¹ : (𝓞 K ⧸ p.val.asIdeal)ˣ) :
          𝓞 K ⧸ p.val.asIdeal) else 1)

def localWeylExponent (j : Fin 6) (e : ℕ) : ℕ :=
  if e = 0 then (8 - j.val) % 6 else (4 + 2 * e) % 6

/-- The remaining generator-section compatibility is stated explicitly;
span(generator I)=I.map alone does not supply either assertion. -/
structure AllowedGeneratorInput : Prop where
  multiplicative : ∀ I J : ExteriorIdeal K S, ∃ u : S.unit K,
    D.generator (exteriorMul K S I J) =
      (S.unitEquivUnitsInteger K u).val ^ 6 * D.generator I * D.generator J
  reciprocity : ∀ I J : ExteriorIdeal K S,
    idealSymbol K S D I (D.generator J) = idealSymbol K S D J (D.generator I)
  generator_norm : ∀ I : ExteriorIdeal K S,
    sLocalProductNorm K S (sLocalNonzeroIntegerDiagonal K S
      ⟨D.generator I, D.generator_ne_zero I⟩) = exteriorNorm K S I

structure MarkedDatum where
  moving : ExteriorIdeal K S
  frozen : ExteriorIdeal K S
  puncture : ExteriorIdeal K S
  moving_squarefree : Squarefree moving.val.val
  puncture_squarefree : Squarefree puncture.val.val
  moving_frozen_coprime : IsCoprime moving.val.val frozen.val.val
  moving_puncture_coprime : IsCoprime moving.val.val puncture.val.val
  rowUnit : S.unit K
  marks : Finset (ExteriorPrime K S)
  marks_coprime : ∀ p ∈ marks,
    ¬p.val.asIdeal ∣ moving.val.val ∧ ¬p.val.asIdeal ∣ frozen.val.val ∧
      ¬p.val.asIdeal ∣ puncture.val.val

variable (d : MarkedDatum K S)

def rowElement : S.integer K :=
  (S.unitEquivUnitsInteger K d.rowUnit).val *
    D.generator (exteriorMul K S d.moving d.frozen)

def frozenPrimes : Finset (ExteriorPrime K S) :=
  exteriorSupport K S d.frozen ∪ exteriorSupport K S d.puncture

def rowDigit (p : ExteriorPrime K S) : Fin 6 :=
  ⟨primeExponents (exteriorMul K S d.moving d.frozen).val p.val % 6,
    Nat.mod_lt _ (by decide)⟩

def periodValue (θ : HeckeCharacter K) (I : ExteriorIdeal K S) : ℂ :=
  heckeIdealCoefficient K θ I.val *
    idealSymbol K S D I (S.unitEquivUnitsInteger K d.rowUnit).val

structure ReflectionIndex where
  activeMarks : Finset (ExteriorPrime K S)
  marks_subset : activeMarks ⊆ d.marks
  activeFrozen : Finset (ExteriorPrime K S)
  frozen_subset : activeFrozen ⊆ frozenPrimes K S d
  nonzero_active : ∀ p ∈ frozenPrimes K S d,
    (rowDigit K S d p).val ≠ 0 → p ∈ activeFrozen
  numeratorFrozen : ExteriorIdeal K S
  frozen_support : exteriorSupport K S numeratorFrozen ⊆ activeFrozen
  frozen_digits : ∀ p : ExteriorPrime K S,
    primeExponents numeratorFrozen.val p.val % 3 ≠ 2
  n : ExteriorIdeal K S
  n_coprime : IsCoprime n.val.val
    (exteriorMul K S (primeSetIdeal K S activeFrozen) (primeSetIdeal K S activeMarks)).val.val
  c : ExteriorIdeal K S
  c_squarefree : Squarefree c.val.val
  c_coprime : IsCoprime c.val.val (primeSetIdeal K S activeFrozen).val.val
  unitSector : SixthUnitClasses K S

variable (i : ReflectionIndex K S d)

def frequencyUnit : S.unit K := Quotient.out i.unitSector
def activeFrozenIdeal : ExteriorIdeal K S := primeSetIdeal K S i.activeFrozen
def activeMarkedIdeal : ExteriorIdeal K S := primeSetIdeal K S i.activeMarks

def frozenOmega (θ : HeckeCharacter K) : ℂ :=
  (Finset.prod (frozenPrimes K S d \ i.activeFrozen)
    (fun (p : ExteriorPrime K S) => 1 - (p.val.asIdeal.absNorm : ℂ)⁻¹)) *
  (periodValue K S D d θ i.numeratorFrozen)⁻¹ *
  (periodValue K S D d θ i.n) ^ (-3 : ℤ) *
  (periodValue K S D d θ (activeFrozenIdeal K S d i)) ^ 2 *
  ∏ p ∈ i.activeFrozen,
    let e := primeExponents i.numeratorFrozen.val p.val
    localWeylScalar K S D p (rowDigit K S d p) e *
      (primeEvaluation K S D p (S.unitEquivUnitsInteger K (frequencyUnit K S d i)).val *
       primeEvaluation K S D p (D.generator (removePrime K S i.numeratorFrozen p)) *
       primeEvaluation K S D p (D.generator i.n) ^ 3 *
       primeEvaluation K S D p (D.generator (removePrime K S (activeFrozenIdeal K S d i) p)) ^
         (-2 : ℤ)) ^ localWeylExponent (rowDigit K S d p) e

def reflectedRowFactor (θ : HeckeCharacter K) : ℂ :=
  periodValue K S D d θ d.moving ^ 2 *
  (∏ p ∈ exteriorSupport K S d.moving,
    localWeylScalar K S D p ⟨1, by decide⟩ 0 *
    (primeEvaluation K S D p (S.unitEquivUnitsInteger K (frequencyUnit K S d i)).val *
     primeEvaluation K S D p (D.generator i.numeratorFrozen) *
     primeEvaluation K S D p (D.generator (removePrime K S d.moving p)) ^ (-2 : ℤ) *
     primeEvaluation K S D p (D.generator (activeFrozenIdeal K S d i)) ^ (-2 : ℤ))) *
  ∏ p ∈ i.activeFrozen, primeEvaluation K S D p (D.generator d.moving) ^
    (-(2 * localWeylExponent (rowDigit K S d p)
      (primeExponents i.numeratorFrozen.val p.val) : ℤ))

def reflectedMarkFactor (θ : HeckeCharacter K) : ℂ :=
  periodValue K S D d θ (activeMarkedIdeal K S d i) ^ 2 *
  (∏ p ∈ i.activeMarks,
    thetaGamma K S D (exteriorPrimeIdeal K S p) 2 *
    (primeEvaluation K S D p (S.unitEquivUnitsInteger K (frequencyUnit K S d i)).val *
     primeEvaluation K S D p (D.generator i.numeratorFrozen) *
     primeEvaluation K S D p (D.generator (removePrime K S (activeMarkedIdeal K S d i) p)) ^
       (-2 : ℤ) *
     primeEvaluation K S D p (D.generator (activeFrozenIdeal K S d i)) ^ (-2 : ℤ)) ^ 2) *
  ∏ p ∈ i.activeFrozen,
    primeEvaluation K S D p (D.generator (activeMarkedIdeal K S d i)) ^
      (-(2 * localWeylExponent (rowDigit K S d p)
        (primeExponents i.numeratorFrozen.val p.val) : ℤ))

def reflectedColumnFactor (θ : HeckeCharacter K) : ℂ :=
  (periodValue K S D d θ i.c)⁻¹ *
  (∏ p ∈ i.activeFrozen, primeEvaluation K S D p (D.generator i.c) ^
    localWeylExponent (rowDigit K S d p) (primeExponents i.numeratorFrozen.val p.val)) *
  ∏ p ∈ exteriorSupport K S i.c,
    thetaGamma K S D (exteriorPrimeIdeal K S p) 2 *
    (primeEvaluation K S D p (S.unitEquivUnitsInteger K (frequencyUnit K S d i)).val *
     primeEvaluation K S D p (D.generator i.numeratorFrozen) *
     primeEvaluation K S D p (D.generator (removePrime K S i.c p)) *
     primeEvaluation K S D p (D.generator (activeFrozenIdeal K S d i)) ^ (-2 : ℤ)) ^ 2

def frequencyClass : SixthLocalClasses K S :=
  unitLocalClass K S (frequencyUnit K S d i) *
    generatorLocalClass K S D i.numeratorFrozen * generatorLocalClass K S D i.c *
    generatorLocalClass K S D i.n ^ 3 * generatorLocalClass K S D d.moving ^ (-2 : ℤ) *
    generatorLocalClass K S D (activeFrozenIdeal K S d i) ^ (-2 : ℤ) *
    generatorLocalClass K S D (activeMarkedIdeal K S d i) ^ (-2 : ℤ)

def reflectedTerm (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (V : ℝ → ℂ) (X : ℝ) : ℂ :=
  (∏ p ∈ d.marks \ i.activeMarks, (p.val.asIdeal.absNorm : ℂ)⁻¹) *
  (Real.sqrt (exteriorNorm K S (activeMarkedIdeal K S d i)) : ℂ)⁻¹ *
  frozenOmega K S D d i θ / (exteriorNorm K S i.n : ℂ) *
  reflectedMarkFactor K S D d i θ * reflectedRowFactor K S D d i θ *
  reflectedColumnFactor K S D d i θ / (Real.sqrt (exteriorNorm K S i.c) : ℂ) *
  idealSymbol K S D d.moving (D.generator i.c * D.generator i.n) ^ 3 *
  idealSymbol K S D (activeMarkedIdeal K S d i) (D.generator i.c) ^ (-2 : ℤ) *
  mellinReflectionKernel K S F θ (QuotientGroup.mk d.rowUnit)
    (frequencyClass K S D d i) V 0
    (X * exteriorNorm K S i.numeratorFrozen * exteriorNorm K S i.c *
      exteriorNorm K S i.n ^ 3 /
      (exteriorNorm K S d.moving * exteriorNorm K S (activeFrozenIdeal K S d i) *
        exteriorNorm K S (activeMarkedIdeal K S d i)) ^ 2)

/-- A concrete conditional coefficient theorem. Its existence and the KP
realization remain unproved. This is only the reflection component of T,
not the complete theta/Poisson/physical-probe transfer of M §4--7. -/
structure MarkedCoefficientReflectionInput (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) : Prop where
  allowed_generators : AllowedGeneratorInput K S D
  exterior_unramified : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p
  angular_nonzero : ∃ (v : InfinitePlace K) (hv : v.IsComplex),
    heckeComplexWeight K v hv θ ≠ 0
  kernel : MellinKernelInput K S F θ
  completed_absolute : ∀ (d : MarkedDatum K S) (V : SmoothAnnularTest) X, 0 < X →
    Summable (completedTerm K S D θ (rowElement K S D d) d.puncture d.marks V.toFun X)
  reflected_absolute : ∀ (d : MarkedDatum K S) (V : SmoothAnnularTest) X, 0 < X →
    Summable (fun i : ReflectionIndex K S d => reflectedTerm K S D d i F θ V.toFun X)
  reflection : ∀ (d : MarkedDatum K S) (V : SmoothAnnularTest) X, 0 < X →
    completedThetaSum K S D θ (rowElement K S D d) d.puncture d.marks V.toFun X =
      ∑' i : ReflectionIndex K S d, reflectedTerm K S D d i F θ V.toFun X

end HeckeGeneral.ThetaSkeleton.Global
