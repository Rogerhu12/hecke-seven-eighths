import HeckeGeneral.Characters.ConductorCanonicalGauss

set_option backward.isDefEq.respectTransparency false

/-! Identify the conductor pairing with the standard character on an actual finite-support adèle.
The local scale is the chosen uniformizer to the negative of the sum of
the conductor depth and the different exponent.
The resulting character value is independent of all local integer representatives. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain NumberField.StandardAddChar
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- The standard finite character has the negative trace sign on a principal finite adèle. -/
theorem stdAddChar_finitePrincipal (a : K) :
    stdAddChar K ((0 : InfiniteAdeleRing K),
      algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) a) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℚ K a : ℂ)) := by
  change psiQ ((adelicTraceData K).adelicTrace _) = _
  rw [AdelicTraceData.adelicTrace_apply, psiQ_apply]
  change psiArch ((adelicTraceData K).traceInf 0) *
    psiFin ((adelicTraceData K).traceFin
      (algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) a)) = _
  rw [map_zero, AddChar.map_zero_eq_one, one_mul,
    (adelicTraceData K).traceFin_algebraMap, psiFin_algebraMap]

/-- Consequently the positive archimedean trace phase cancels the finite standard character. -/
theorem positiveTracePhase_mul_finitePrincipal (a : K) :
    Complex.exp ((2 * Real.pi * Complex.I) * (Algebra.trace ℚ K a : ℂ)) *
      stdAddChar K ((0 : InfiniteAdeleRing K),
        algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) a) = 1 := by
  rw [stdAddChar_finitePrincipal, ← Complex.exp_add]
  simp only [neg_mul, add_neg_cancel, Complex.exp_zero]

abbrev ConductorLocalIntegers (χ : HeckeCharacter K) :=
  ∀ v : conductorPlaces K χ, LocalIntegerRing K v.val

/-- Convert local integer representatives into the actual global conductor quotient by CRT. -/
def conductorLocalIntegerReduction (χ : HeckeCharacter K) (x : ConductorLocalIntegers K χ) :
    𝓞 K ⧸ (finiteConductor K χ).val :=
  (conductorResidueCRT K χ).symm (fun v => Ideal.Quotient.mk _ (x v))

/-- A genuine adèle with zero infinite part and finitely many trace-scaled finite coordinates. -/
def canonicalConductorTraceAdele (χ : HeckeCharacter K) (x : ConductorLocalIntegers K χ) :
    AdeleRing (𝓞 K) K :=
  ∑ v : conductorPlaces K χ, adeleSingleAt K v.val
    (localAdditiveScale K v.val (localConductorExponent K χ v.val)
      (FractionalIdeal.count K v.val
        (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)) *
      (x v : v.val.adicCompletion K))

private theorem standardAddCharacter_sum {ι : Type*} (s : Finset ι)
    (f : ι → AdeleRing (𝓞 K) K) :
    stdAddChar K (∑ i ∈ s, f i) = ∏ i ∈ s, stdAddChar K (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, AddChar.map_add_eq_mul, ih]

/-- The standard global trace character restricted to these finite adèles is precisely the
proved canonical residue character, with the actual local different exponents. -/
theorem stdAddChar_canonicalConductorTraceAdele (χ : HeckeCharacter K)
    (x : ConductorLocalIntegers K χ) :
    stdAddChar K (canonicalConductorTraceAdele K χ x) =
      canonicalConductorAddCharacter K χ (conductorLocalIntegerReduction K χ x) := by
  rw [canonicalConductorTraceAdele, standardAddCharacter_sum,
    canonicalConductorAddCharacter_CRT, conductorLocalIntegerReduction,
    RingEquiv.apply_symm_apply]
  apply Finset.prod_congr rfl
  intro v _
  rw [localCanonicalAddCharacter_mk]
  rfl

/-- Changing the representatives by the conductor powers changes no standard trace value. -/
theorem canonicalConductorTraceAdele_lift_independent (χ : HeckeCharacter K)
    (x y : ConductorLocalIntegers K χ)
    (hxy : ∀ v, x v - y v ∈ localMaximalIdeal K v.val ^ localConductorExponent K χ v.val) :
    stdAddChar K (canonicalConductorTraceAdele K χ x) =
      stdAddChar K (canonicalConductorTraceAdele K χ y) := by
  rw [stdAddChar_canonicalConductorTraceAdele, stdAddChar_canonicalConductorTraceAdele]
  congr 1
  apply (conductorResidueCRT K χ).injective
  simp only [conductorLocalIntegerReduction, RingEquiv.apply_symm_apply]
  funext v
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem (x v) (y v)).mpr (hxy v)

end HeckeGeneral.Characters
