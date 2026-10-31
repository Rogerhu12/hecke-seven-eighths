import Expansion.PhysicalFourierNormalization
import HeckeSkeleton.HighBinSupport.ActualEulerCRT

/-!
# Actual Gauss-symbol coefficients in orbital Poisson

This module connects the literal finite coefficient of the physical probe
to the genuine principal-quotient Poisson theorem.  The quotient core and
its two zero extensions are the ones proved in HIGHBIN's arithmetic CRT
module.  The product of the two original generators is retained exactly.
No coprimality, Euler identity, Poisson identity, or source bound is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.PhysicalFinitePoisson

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualAbsolute HeckeSkeleton.HighBinActualCRT
open Expansion.PhysicalFourierNormalization
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

section Coefficients

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def poissonModulus (P : ProbeData K S) (den A : ExteriorIdeal K S) : S.integer K :=
  P.arithmetic.generator den * P.arithmetic.generator A

theorem poissonModulus_ne_zero (P : ProbeData K S) (den A : ExteriorIdeal K S) :
    poissonModulus K S P den A ≠ 0 :=
  mul_ne_zero (P.arithmetic.generator_ne_zero den) (P.arithmetic.generator_ne_zero A)

/-- Transport only across the proved equality of the actual product ideal. -/
def poissonQuotientEquiv (P : ProbeData K S) (den A : ExteriorIdeal K S) :
    (S.integer K ⧸ Ideal.span ({poissonModulus K S P den A} : Set (S.integer K))) ≃+*
      ThetaQuotient K S (exteriorMul K S den A) :=
  Ideal.quotEquivOfEq (product_generator_span K S P.arithmetic den A)

@[simp] theorem poissonQuotientEquiv_mk (P : ProbeData K S)
    (den A : ExteriorIdeal K S) (m : S.integer K) :
    poissonQuotientEquiv K S P den A (Ideal.Quotient.mk _ m) =
      Ideal.Quotient.mk _ m := rfl

def principalPoissonCoefficient (P : ProbeData K S) (den A : ExteriorIdeal K S) :
    (S.integer K ⧸ Ideal.span ({poissonModulus K S P den A} : Set (S.integer K))) → ℂ :=
  fun x => poissonCore K S P den A (poissonQuotientEquiv K S P den A x)

@[simp] theorem principalPoissonCoefficient_mk (P : ProbeData K S)
    (den A : ExteriorIdeal K S) (m : S.integer K) :
    principalPoissonCoefficient K S P den A (Ideal.Quotient.mk _ m) =
      probeGauss K S P den (-m) * idealSymbol K S P.arithmetic A m := by
  rw [principalPoissonCoefficient, poissonQuotientEquiv_mk, poissonCore_mk]

theorem principalPoissonCoefficient_zero (P : ProbeData K S)
    (den A : ExteriorIdeal K S) :
    principalPoissonCoefficient K S P den A 0 =
      probeGauss K S P den 0 * idealSymbol K S P.arithmetic A 0 := by
  simpa only [map_zero, neg_zero] using principalPoissonCoefficient_mk K S P den A 0

/-- Literal invariance under the original sixth-power subgroup is proved
from the actual quotient core, not supplied as an additional input. -/
theorem principalPoissonCoefficient_invariant (P : ProbeData K S)
    (den A : ExteriorIdeal K S) (γ : sixthPowerUnits K S) (m : S.integer K) :
    principalPoissonCoefficient K S P den A
        (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K γ.val).val * m)) =
      principalPoissonCoefficient K S P den A (Ideal.Quotient.mk _ m) := by
  obtain ⟨v, hv⟩ := γ.property
  change v ^ 6 = γ.val at hv
  unfold principalPoissonCoefficient
  rw [poissonQuotientEquiv_mk, poissonQuotientEquiv_mk, ← hv]
  simp only [map_pow, Units.val_pow_eq_pow_val, map_mul]
  exact poissonCore_sixth_unit K S P den A
    (Units.map (Ideal.Quotient.mk _).toMonoidHom (S.unitEquivUnitsInteger K v))
    (Ideal.Quotient.mk _ m)

theorem productCharacter_quotientEquiv (P : ProbeData K S)
    (den A : ExteriorIdeal K S)
    (x : S.integer K ⧸ Ideal.span ({poissonModulus K S P den A} : Set (S.integer K))) :
    productPrincipalCharacter K S P.arithmetic den A (poissonQuotientEquiv K S P den A x) =
      sIntegerActualModulusAddCharacter K S P.arithmetic.different_outside
        (poissonModulus K S P den A) (poissonModulus_ne_zero K S P den A) x := by
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [poissonQuotientEquiv_mk, productPrincipalCharacter_mk,
    sIntegerActualModulusAddCharacter_mk]
  rfl

/-- The divisor-one Fourier transform in genuine Poisson is the literal
finite Fourier transform from the arithmetic CRT computation. -/
theorem principalDivisorFourier_eq (P : ProbeData K S)
    (den A : ExteriorIdeal K S) (h : S.integer K) :
    sIntegerPeriodicDivisorFourier K S P.arithmetic.different_outside
        (poissonModulus K S P den A) (poissonModulus_ne_zero K S P den A)
        (principalPoissonCoefficient K S P den A) 1 (Ideal.Quotient.mk _ h) =
      letI : Finite (ThetaQuotient K S (exteriorMul K S den A)) :=
        finite_sIntegerSexticIdealQuotient K S (exteriorMul K S den A).val.val
          (nonZeroDivisors.coe_ne_zero (exteriorMul K S den A).val)
          (exteriorMul K S den A).property
      letI : Fintype (ThetaQuotient K S (exteriorMul K S den A)) := Fintype.ofFinite _
      HighBin.FiniteResidueFourier.fourier
        (productPrincipalCharacter K S P.arithmetic den A) (poissonCore K S P den A)
        (Ideal.Quotient.mk _ h) := by
  letI : Finite (ThetaQuotient K S (exteriorMul K S den A)) :=
    finite_sIntegerSexticIdealQuotient K S (exteriorMul K S den A).val.val
      (nonZeroDivisors.coe_ne_zero (exteriorMul K S den A).val)
      (exteriorMul K S den A).property
  letI : Fintype (ThetaQuotient K S (exteriorMul K S den A)) := Fintype.ofFinite _
  letI := finite_sIntegerPrincipalResidue K S (poissonModulus K S P den A)
    (poissonModulus_ne_zero K S P den A)
  letI := Fintype.ofFinite
    (S.integer K ⧸ Ideal.span ({poissonModulus K S P den A} : Set (S.integer K)))
  rw [sIntegerPeriodicDivisorFourier_apply]
  simp only [map_one, one_mul, HighBin.FiniteResidueFourier.fourier]
  apply Fintype.sum_equiv (poissonQuotientEquiv K S P den A).toEquiv
  intro x
  change poissonCore K S P den A (poissonQuotientEquiv K S P den A x) * _ = _
  congr 1
  calc
    _ = productPrincipalCharacter K S P.arithmetic den A
        (poissonQuotientEquiv K S P den A (Ideal.Quotient.mk _ h * x)) :=
      (productCharacter_quotientEquiv K S P den A _).symm
    _ = _ := by rw [map_mul, poissonQuotientEquiv_mk]

/-- Exact physical finite Fourier coefficient, including its original
inverse denominator norm.  Common factors of den and A are unrestricted. -/
theorem finitePoissonFactor_eq_principalDivisorFourier (P : ProbeData K S)
    (den A : ExteriorIdeal K S) (h : S.integer K) :
    finitePoissonFactor K S P den A h =
      (exteriorNorm K S den : ℂ)⁻¹ *
        sIntegerPeriodicDivisorFourier K S P.arithmetic.different_outside
          (poissonModulus K S P den A) (poissonModulus_ne_zero K S P den A)
          (principalPoissonCoefficient K S P den A) 1 (Ideal.Quotient.mk _ h) := by
  rw [principalDivisorFourier_eq, finitePoissonFactor_eq_fourier]

theorem principalDivisorFourier_eq_norm_mul (P : ProbeData K S)
    (den A : ExteriorIdeal K S) (h : S.integer K) :
    sIntegerPeriodicDivisorFourier K S P.arithmetic.different_outside
        (poissonModulus K S P den A) (poissonModulus_ne_zero K S P den A)
        (principalPoissonCoefficient K S P den A) 1 (Ideal.Quotient.mk _ h) =
      (exteriorNorm K S den : ℂ) * finitePoissonFactor K S P den A h := by
  rw [finitePoissonFactor_eq_principalDivisorFourier, ← mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (idealNorm_pos K den.val).ne'), one_mul]

def gaussSymbolOrbitWeight (P : ProbeData K S) (den A : ExteriorIdeal K S)
    (q : SIntegerOrbits K S (sixthPowerUnits K S)) : ℂ :=
  probeGauss K S P den (-q.out.val) * idealSymbol K S P.arithmetic A q.out.val

def finitePoissonOrbitWeight (P : ProbeData K S) (den A : ExteriorIdeal K S)
    (q : SIntegerOrbits K S (sixthPowerUnits K S)) : ℂ :=
  finitePoissonFactor K S P den A q.out.val

theorem periodicOrbitWeight_eq (P : ProbeData K S) (den A : ExteriorIdeal K S) :
    sIntegerPeriodicOrbitWeight K S (sixthPowerUnits K S) (poissonModulus K S P den A)
        (principalPoissonCoefficient K S P den A)
        (principalPoissonCoefficient_invariant K S P den A) =
      gaussSymbolOrbitWeight K S P den A := by
  funext q
  have h := sIntegerPeriodicOrbitWeight_mk K S (sixthPowerUnits K S)
    (poissonModulus K S P den A) (principalPoissonCoefficient K S P den A)
    (principalPoissonCoefficient_invariant K S P den A) q.out
  rw [Quotient.out_eq, principalPoissonCoefficient_mk] at h
  exact h

theorem periodicFourierOrbitWeight_eq (P : ProbeData K S) (den A : ExteriorIdeal K S) :
    sIntegerPeriodicFourierOrbitWeight K S P.arithmetic.different_outside
        (sixthPowerUnits K S) (poissonModulus K S P den A) (poissonModulus_ne_zero K S P den A)
        (principalPoissonCoefficient K S P den A)
        (principalPoissonCoefficient_invariant K S P den A) 1 =
      fun q => (exteriorNorm K S den : ℂ) * finitePoissonOrbitWeight K S P den A q := by
  funext q
  have h := sIntegerPeriodicFourierOrbitWeight_mk K S P.arithmetic.different_outside
    (sixthPowerUnits K S) (poissonModulus K S P den A) (poissonModulus_ne_zero K S P den A)
    (principalPoissonCoefficient K S P den A)
    (principalPoissonCoefficient_invariant K S P den A) 1 q.out
  rw [Quotient.out_eq, principalDivisorFourier_eq_norm_mul] at h
  exact h

end Coefficients

section OrbitalIdentity

variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Γ" => sixthPowerUnits K Sset

local instance : Γ.FiniteIndex := sUnit_power_range_finiteIndex K Sset 6 (by decide)

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include μ ν in
/-- Actual Gauss-symbol orbital Poisson.  The finite coefficient and its
subgroup invariance have both been proved above.  Every nonzero frequency
and both genuine zero terms remain in the equality. -/
theorem gaussSymbolOrbitalPoisson (P : ProbeData K Sset) (den A : ExteriorIdeal K Sset)
    (r : {r : ℝ // 0 < r}) :
    let q := sIntegerElementNorm K Sset
      ⟨poissonModulus K Sset P den A, poissonModulus_ne_zero K Sset P den A⟩
    let C : ℂ := (r.val : ℂ)⁻¹ * (physicalPoissonScalar K : ℂ) * (q.val : ℂ)⁻¹
    let rDual : {r : ℝ // 0 < r} :=
      ⟨(r.val * q.val)⁻¹, inv_pos.mpr (mul_pos r.property q.property)⟩
    weightedPhysicalOrbitalSeries K S Γ (additiveTest K Sset P.additive) r
        (gaussSymbolOrbitWeight K Sset P den A) =
      C * weightedPhysicalOrbitalSeries K S Γ
        (additiveFourier K Sset (fun v => μv v.val) P.additive) rDual
        (fun q => (exteriorNorm K Sset den : ℂ) * finitePoissonOrbitWeight K Sset P den A q) +
      ((sUnitHaarCovolume K Sset Γ).toReal : ℂ) *
        (C * ((exteriorNorm K Sset den : ℂ) * finitePoissonFactor K Sset P den A 0 *
          additiveFourierAtZero K Sset (fun v => μv v.val) P.additive) -
          (probeGauss K Sset P den 0 * idealSymbol K Sset P.arithmetic A 0) *
            additiveValueAtZero K S P.additive) := by
  have h := probePeriodicOrbitalPoisson K S μv Γ ν μ P
    (poissonModulus K Sset P den A) (poissonModulus_ne_zero K Sset P den A)
    (principalPoissonCoefficient K Sset P den A)
    (principalPoissonCoefficient_invariant K Sset P den A) 1 r
  have hz := principalDivisorFourier_eq_norm_mul K Sset P den A 0
  simp only [map_zero] at hz
  dsimp only at h ⊢
  simpa only [map_one, one_mul, periodicOrbitWeight_eq, periodicFourierOrbitWeight_eq,
    principalPoissonCoefficient_zero, hz] using h

end OrbitalIdentity

end Expansion.PhysicalFinitePoisson

#print axioms Expansion.PhysicalFinitePoisson.finitePoissonFactor_eq_principalDivisorFourier
#print axioms Expansion.PhysicalFinitePoisson.gaussSymbolOrbitalPoisson
