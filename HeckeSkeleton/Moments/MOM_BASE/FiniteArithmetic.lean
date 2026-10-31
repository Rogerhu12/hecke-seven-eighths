import HeckeSkeleton.Moments.MOM_BASE.Arithmetic
import HeckeSkeleton.Moments.MOM_BASE.FiniteCoefficients

/-!
# The finite CRT character is the actual ideal row

These identities connect the finite-prime-power tables to the original
S-integer symbol and the completed coefficient. Localization handles
every S-integer numerator. The original Hecke and puncture zeros remain
in the same factors throughout.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_BASE

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- At an exterior prime the ideal homomorphism retains the specified-root
residue value, including its zero at a bad numerator. -/
theorem exteriorSymbolHom_prime (m : S.integer K) (p : ExteriorPrime K S) :
    exteriorSymbolHom K S D m p.val.asIdeal =
      sIntegerSexticEvaluation K S p.val p.property
        D.root6 D.primitive6 D.embedding (D.away_six p.val p.property) m := by
  change idealCoefficient (exteriorSymbolPrime K S D m) p.val.asIdeal = _
  rw [idealCoefficient_prime]
  simp only [exteriorSymbolPrime, dif_pos p.property]

theorem exteriorSymbolHom_prime_algebraMap (x : 𝓞 K) (p : ExteriorPrime K S) :
    exteriorSymbolHom K S D (algebraMap (𝓞 K) (S.integer K) x) p.val.asIdeal =
      thetaPrimeCharacter K S D p (Ideal.Quotient.mk p.val.asIdeal x) := by
  rw [exteriorSymbolHom_prime, sIntegerSexticEvaluation_algebraMap] <;> rfl

section CRT

variable {ι : Type*} [Fintype ι]
variable (p : ι → ExteriorPrime K S) (hp : Function.Injective p)
variable (a : ι → ℕ) (ha : ∀ i, 1 ≤ a i)

/-- The finite CRT character equals the actual completely multiplicative
ideal symbol evaluated on the whole prime-power product. -/
theorem actualCRTCharacter_eq_symbolHom (x : 𝓞 K) :
    actualCRTCharacter K S D p hp a ha (Ideal.Quotient.mk _ x) =
      exteriorSymbolHom K S D (algebraMap (𝓞 K) (S.integer K) x)
        (∏ i, (p i).val.asIdeal ^ a i) := by
  simp only [actualCRTCharacter_mk, map_prod, map_pow,
    exteriorSymbolHom_prime_algebraMap]

/-- The actual ideal row, with its full prime multiplicities. -/
theorem actualCRTCharacter_eq_idealSymbol (I : ExteriorIdeal K S)
    (hI : I.val.val = ∏ i, (p i).val.asIdeal ^ a i) (x : 𝓞 K) :
    actualCRTCharacter K S D p hp a ha (Ideal.Quotient.mk _ x) =
      idealSymbol K S D I (algebraMap (𝓞 K) (S.integer K) x) := by
  rw [← exteriorSymbolHom_apply, hI]
  exact actualCRTCharacter_eq_symbolHom K S D p hp a ha x

/-- The actual localization quotient followed by the displayed ordinary
prime-power factorization; no integer numerator representative is fixed. -/
def actualIdealCRTResidueEquiv (I : ExteriorIdeal K S)
    (hI : I.val.val = ∏ i, (p i).val.asIdeal ^ a i) :
    ThetaQuotient K S I ≃+* (𝓞 K ⧸ ∏ i, (p i).val.asIdeal ^ a i) :=
  (sIntegerResidueEquiv K S I.val.val
    (sexticIdeal_coprime_S K S I.val.val I.property)).symm.trans
      (Ideal.quotEquivOfEq hI)

@[simp] theorem actualIdealCRTResidueEquiv_mk (I : ExteriorIdeal K S)
    (hI : I.val.val = ∏ i, (p i).val.asIdeal ^ a i) (x : 𝓞 K) :
    actualIdealCRTResidueEquiv K S p a I hI
        (Ideal.Quotient.mk _ (algebraMap (𝓞 K) (S.integer K) x)) =
      Ideal.Quotient.mk _ x := by
  rw [actualIdealCRTResidueEquiv, RingEquiv.trans_apply,
    sIntegerResidueEquiv_symm_mk, Ideal.quotEquivOfEq_mk]

/-- Equality with the original quotient function at every residue,
including nonunits. This is the finite-input bridge for the canonical row. -/
theorem actualCRTCharacter_eq_quotientFunction (I : ExteriorIdeal K S)
    (hI : I.val.val = ∏ i, (p i).val.asIdeal ^ a i) (q : ThetaQuotient K S I) :
    actualCRTCharacter K S D p hp a ha (actualIdealCRTResidueEquiv K S p a I hI q) =
      sIntegerSexticIdealQuotientFunction K S D.root6 D.primitive6 D.embedding
        I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
        (fun v hv => D.away_six v (I.property v hv)) q := by
  let e := sIntegerResidueEquiv K S I.val.val
    (sexticIdeal_coprime_S K S I.val.val I.property)
  obtain ⟨y, hy⟩ := e.surjective q
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← hy, sIntegerResidueEquiv_mk, actualIdealCRTResidueEquiv_mk,
    sIntegerSexticIdealQuotientFunction_mk]
  exact actualCRTCharacter_eq_idealSymbol K S D p hp a ha I hI x

/-- All S-integer numerators, including those with nontrivial denominators,
have the same original ideal-symbol value after the finite CRT bridge. -/
theorem actualCRTCharacter_eq_idealSymbol_sInteger (I : ExteriorIdeal K S)
    (hI : I.val.val = ∏ i, (p i).val.asIdeal ^ a i) (m : S.integer K) :
    actualCRTCharacter K S D p hp a ha
        (actualIdealCRTResidueEquiv K S p a I hI (Ideal.Quotient.mk _ m)) =
      idealSymbol K S D I m := by
  rw [actualCRTCharacter_eq_quotientFunction, sIntegerSexticIdealQuotientFunction_mk] <;> rfl

/-- The completed coefficient has the actual finite CRT row, the original
Hecke factor, and exactly the original puncture indicator. -/
theorem canonicalTau_actualCRT (θ : HeckeCharacter K) (m : S.integer K)
    (r : Ideal (𝓞 K)) (I : ExteriorIdeal K S)
    (hI : I.val.val = ∏ i, (p i).val.asIdeal ^ a i) :
    canonicalTau K S D θ m r I.val.val =
      heckeIdealCoefficient K θ I.val *
        actualCRTCharacter K S D p hp a ha
          (actualIdealCRTResidueEquiv K S p a I hI (Ideal.Quotient.mk _ m)) *
        (if IsCoprime I.val.val r then 1 else 0) := by
  rw [canonicalTau_apply, actualCRTCharacter_eq_idealSymbol_sInteger]

/-- The ordinary-integer presentation of the same completed coefficient. -/
theorem canonicalTau_actualCRT_algebraMap (θ : HeckeCharacter K) (x : 𝓞 K)
    (r : Ideal (𝓞 K)) (I : ExteriorIdeal K S)
    (hI : I.val.val = ∏ i, (p i).val.asIdeal ^ a i) :
    canonicalTau K S D θ (algebraMap (𝓞 K) (S.integer K) x) r I.val.val =
      heckeIdealCoefficient K θ I.val *
        actualCRTCharacter K S D p hp a ha (Ideal.Quotient.mk _ x) *
        (if IsCoprime I.val.val r then 1 else 0) := by
  rw [canonicalTau_apply, actualCRTCharacter_eq_idealSymbol K S D p hp a ha I hI]

end CRT

end HeckeSkeleton.Moments.MOM_BASE

