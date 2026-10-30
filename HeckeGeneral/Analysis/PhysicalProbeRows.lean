import HeckeGeneral.Analysis.PhysicalProbePrincipal
import HeckeGeneral.Analysis.FiniteEulerRational

/-!
Actual Poisson frequency rows and the initial four-ideal Euler series.
Frequency rows retain every sixth-unit sector. Finite Fourier factors use
the genuine Gauss sum, genuine residue symbol and literal phase h*m/(s*A).
The quotient representatives are explicit; representative independence,
Poisson summation and the subsequent Euler calibration are not asserted.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.SquarefreeAmplification
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The arithmetic sixth-power-free row, with its actual finite unit class.
It is not an arbitrary finite row set. -/
structure FrequencyRow where
  ideal : ExteriorIdeal K S
  sixthPowerFree : ∀ p : HeightOneSpectrum (𝓞 K), primeExponents ideal.val p < 6
  sector : SixthUnitClasses K S

def frequencyRowNorm (u : FrequencyRow K S) : ℝ := exteriorNorm K S u.ideal

def frequencyRowElement (P : ProbeData K S) (u : FrequencyRow K S) : S.integer K :=
  (S.unitEquivUnitsInteger K (Quotient.out u.sector) : S.integer K) *
    P.arithmetic.generator u.ideal

def principalFrequencyRow (u : FrequencyRow K S) : Prop :=
  u.ideal.val = 1 ∧ u.sector = 1

/-- Every ideal of norm at most U is inspected; the only filters are the
literal exterior and sixth-power-free conditions. All unit sectors remain. -/
def frequencyRows (U : ℝ) : Finset (FrequencyRow K S) := by
  letI : Fintype (SixthUnitClasses K S) := Fintype.ofFinite _
  let F := (dyadicIdealSupport K (U / 2)).filter fun I =>
    (∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → p ∉ S) ∧
      (∀ p : HeightOneSpectrum (𝓞 K), primeExponents I p < 6)
  exact (F.attach.product (Finset.univ : Finset (SixthUnitClasses K S))).image
    fun (I : {I : NonzeroIdeal K // I ∈ F} × SixthUnitClasses K S) =>
      { ideal := ⟨I.1.val, (Finset.mem_filter.mp I.1.property).2.1⟩
        sixthPowerFree := (Finset.mem_filter.mp I.1.property).2.2
        sector := I.2 }

def poissonFrequency (P : ProbeData K S) (u : FrequencyRow K S)
    (r : ExteriorIdeal K S) : S.integer K :=
  frequencyRowElement K S P u * P.arithmetic.generator r ^ 6

/-- P's F(s,A,h), equivalently its finite Fourier transform divided by q_s.
The finite quotient is that of the actual product ideal s*A, including top.
No coprimality between s and A is imposed. -/
def finitePoissonFactor (P : ProbeData K S) (den A : ExteriorIdeal K S)
    (h : S.integer K) : ℂ := by
  let B := exteriorMul K S den A
  letI : Finite (ThetaQuotient K S B) :=
    finite_sIntegerSexticIdealQuotient K S B.val.val
      (nonZeroDivisors.coe_ne_zero B.val) B.property
  letI : Fintype (ThetaQuotient K S B) := Fintype.ofFinite _
  exact (exteriorNorm K S den : ℂ)⁻¹ * ∑ x : ThetaQuotient K S B,
    let m : S.integer K := Quotient.out x
    probeGauss K S P den (-m) * idealSymbol K S P.arithmetic A m *
      sLocalPrincipalPhase K S
        (((h : K) * (m : K)) /
          ((P.arithmetic.generator den : K) * (P.arithmetic.generator A : K)))

abbrev FourIdealIndex :=
  (ExteriorIdeal K S × ExteriorIdeal K S) × (ExteriorIdeal K S × ExteriorIdeal K S)

/-- Literal marked calF_u from P, calF-definition. It retains all completed
cube factors n, all denominator ideals and all sixth-power factors r. -/
def initialRowEulerTerm (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (s w z : ℂ) (I : FourIdealIndex K S) : ℂ :=
  let c := I.1.1
  let n := I.1.2
  let den := I.2.1
  let r := I.2.2
  let A := completedIdeal K S c n
  if Squarefree c.val.val ∧ wholeIndexMask K S (primeSetIdeal K S ∅) Q A then
    thetaGamma K S P.arithmetic c 2 * heckeIdealCoefficient K (thetaPeriod K S P ψ) A.val *
      finitePoissonFactor K S P den A (poissonFrequency K S P u r) *
      (exteriorNorm K S c : ℂ) ^ (-(1 / 2 : ℂ) - s) *
      (exteriorNorm K S n : ℂ) ^ (-1 - 3 * s) *
      (exteriorNorm K S den : ℂ) ^ (-w) * (exteriorNorm K S r : ℂ) ^ (-6 * z)
  else 0

def initialRowEulerSeries (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (s w z : ℂ) : ℂ :=
  ∑' I, initialRowEulerTerm K S P ψ Q u s w z I

/-- Actual primitive inducing characters require a common deletion mask:
sixth-power descendants keep zeros at primes of the original row. -/
structure RowCharacterInput (P : ProbeData K S) where
  character : FrequencyRow K S → HeckeCharacter K
  finite_order : ∀ u, FiniteOrder (character u)
  coefficient_calibration : ∀ (u : FrequencyRow K S) (I : ExteriorIdeal K S),
    (if IsCoprime I.val.val u.ideal.val.val then heckeIdealCoefficient K (character u) I.val else 0) =
      idealSymbol K S P.arithmetic I (frequencyRowElement K S P u)

end HeckeGeneral.ThetaSkeleton.Physical
