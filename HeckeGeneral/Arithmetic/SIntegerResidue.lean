import HeckeGeneral.Arithmetic.SIntegerFiniteLocalization
import HeckeGeneral.Arithmetic.LocalizationResidueEquiv
import HeckeGeneral.Characters.LocalResidueTower
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Actual exterior residue rings of S-integers

An ordinary ideal coprime to the primes in the original finite set `S`
has the same residue ring after passage to the actual S-integers. Its
cardinality is the ordinary absolute ideal norm. Composing with the
proved local completion residue equivalences gives the actual exterior
CRT, with the quotient map identified on ordinary integers. No enlargement
of `S`, principal-ideal hypothesis, or assumed CRT equivalence is used.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]

/-- An S-integer is an actual completed local integer outside `S`. -/
def sIntegerToLocalInteger (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    S.integer K →+* LocalIntegerRing K v where
  toFun a := ⟨algebraMap K (v.adicCompletion K) a.val, by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v (a.val : v.adicCompletion K) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact a.property v hv⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

/-- Reduction of the actual local image, defined on every S-integer. -/
def sIntegerToLocalResidue (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) (n : ℕ) :
    S.integer K →+* LocalResidueRing K v n :=
  (Ideal.Quotient.mk (localMaximalIdeal K v ^ n)).comp
    (sIntegerToLocalInteger K S v hv)

@[simp] theorem sIntegerToLocalResidue_algebraMap
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) (n : ℕ) (a : 𝓞 K) :
    sIntegerToLocalResidue K S v hv n (algebraMap (𝓞 K) (S.integer K) a) =
      globalToLocalResidue K v n a := rfl

/-- Coprimality at the original exceptional primes makes the single actual
localization denominator coprime to the modulus. -/
theorem sup_span_finiteSIntegerDenominator_eq_top (I : Ideal (𝓞 K))
    (hI : ∀ v ∈ S, I ⊔ v.asIdeal = ⊤) :
    I ⊔ Ideal.span ({finiteSIntegerDenominator K S} : Set (𝓞 K)) = ⊤ := by
  unfold finiteSIntegerDenominator
  rw [← Ideal.prod_span_singleton]
  apply Ideal.sup_prod_eq_top
  intro v hv
  rw [span_primePowerGenerator]
  exact Ideal.sup_pow_eq_top (hI v ((Set.toFinite S).mem_toFinset.mp hv))

/-- The actual quotient by the extended exterior ideal. -/
def sIntegerResidueEquiv (I : Ideal (𝓞 K))
    (hI : ∀ v ∈ S, I ⊔ v.asIdeal = ⊤) :
    (𝓞 K ⧸ I) ≃+* (S.integer K ⧸ I.map (algebraMap (𝓞 K) (S.integer K))) := by
  letI := sInteger_isLocalizationAway_finiteDenominator K S
  exact awayResidueEquiv (S.integer K) (finiteSIntegerDenominator K S) I
    (sup_span_finiteSIntegerDenominator_eq_top K S I hI)

@[simp] theorem sIntegerResidueEquiv_mk (I : Ideal (𝓞 K))
    (hI : ∀ v ∈ S, I ⊔ v.asIdeal = ⊤) (a : 𝓞 K) :
    sIntegerResidueEquiv K S I hI (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (I.map (algebraMap (𝓞 K) (S.integer K)))
        (algebraMap (𝓞 K) (S.integer K) a) := rfl

@[simp] theorem sIntegerResidueEquiv_symm_mk (I : Ideal (𝓞 K))
    (hI : ∀ v ∈ S, I ⊔ v.asIdeal = ⊤) (a : 𝓞 K) :
    (sIntegerResidueEquiv K S I hI).symm
        (Ideal.Quotient.mk (I.map (algebraMap (𝓞 K) (S.integer K)))
          (algebraMap (𝓞 K) (S.integer K) a)) = Ideal.Quotient.mk I a := by
  apply (sIntegerResidueEquiv K S I hI).injective
  rw [RingEquiv.apply_symm_apply, sIntegerResidueEquiv_mk]

theorem finite_sIntegerResidue (I : Ideal (𝓞 K)) (hI0 : I ≠ ⊥)
    (hI : ∀ v ∈ S, I ⊔ v.asIdeal = ⊤) :
    Finite (S.integer K ⧸ I.map (algebraMap (𝓞 K) (S.integer K))) := by
  letI : Finite (𝓞 K ⧸ I) := Ring.HasFiniteQuotients.finiteQuotient hI0
  exact Finite.of_equiv (𝓞 K ⧸ I) (sIntegerResidueEquiv K S I hI).toEquiv

theorem natCard_sIntegerResidue (I : Ideal (𝓞 K))
    (hI : ∀ v ∈ S, I ⊔ v.asIdeal = ⊤) :
    Nat.card (S.integer K ⧸ I.map (algebraMap (𝓞 K) (S.integer K))) = I.absNorm :=
  Nat.card_congr (sIntegerResidueEquiv K S I hI).symm.toEquiv

variable {ι : Type*} [Fintype ι]

/-- A product supported outside the original exceptional set satisfies the
coprimality condition above, at every exponent including exponent zero. -/
theorem exteriorPrimePowerProduct_coprime
    (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hPS : ∀ i, P i ∉ S) :
    ∀ v ∈ S, (∏ i, (P i).asIdeal ^ n i) ⊔ v.asIdeal = ⊤ := by
  intro v hv
  apply Ideal.prod_sup_eq_top
  intro i _hi
  have hne : P i ≠ v := fun h => hPS i (h.symm ▸ hv)
  simpa only [pow_one] using
    ((P i).isCoprime_pow_of_ne v hne (n i) 1).sup_eq

/-- The residue ring of an actual S-integer ideal, decomposed into the
actual residue rings of the completions using its ordinary factorization. -/
def sIntegerResidueCRT (I : Ideal (𝓞 K))
    (hI : ∀ v ∈ S, I ⊔ v.asIdeal = ⊤)
    (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j)
    (hprod : ∏ i, (P i).asIdeal ^ n i = I) :
    (S.integer K ⧸ I.map (algebraMap (𝓞 K) (S.integer K))) ≃+*
      ∀ i, LocalResidueRing K (P i) (n i) :=
  (sIntegerResidueEquiv K S I hI).symm.trans
    ((HeightOneSpectrum.quotientEquivPiOfProdEq I P n hP hprod).trans
      (RingEquiv.piCongrRight fun i => localResidueRingEquivGlobal K (P i) (n i)))

@[simp] theorem sIntegerResidueCRT_mk (I : Ideal (𝓞 K))
    (hI : ∀ v ∈ S, I ⊔ v.asIdeal = ⊤)
    (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j)
    (hprod : ∏ i, (P i).asIdeal ^ n i = I) (a : 𝓞 K) (i : ι) :
    sIntegerResidueCRT K S I hI P n hP hprod
        (Ideal.Quotient.mk (I.map (algebraMap (𝓞 K) (S.integer K)))
          (algebraMap (𝓞 K) (S.integer K) a)) i =
      globalToLocalResidue K (P i) (n i) a := by
  unfold sIntegerResidueCRT
  simp only [RingEquiv.trans_apply, sIntegerResidueEquiv_symm_mk]
  rfl

/-- Every CRT coordinate is the literal completed local reduction, including
for S-integers with denominators. Localization uniqueness upgrades the
ordinary-integer identity to the whole actual S-integer ring. -/
theorem sIntegerResidueCRT_apply_mk (I : Ideal (𝓞 K))
    (hI : ∀ v ∈ S, I ⊔ v.asIdeal = ⊤)
    (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j)
    (hprod : ∏ i, (P i).asIdeal ^ n i = I)
    (a : S.integer K) (i : ι) (hi : P i ∉ S) :
    sIntegerResidueCRT K S I hI P n hP hprod
        (Ideal.Quotient.mk (I.map (algebraMap (𝓞 K) (S.integer K))) a) i =
      sIntegerToLocalResidue K S (P i) hi (n i) a := by
  letI := sInteger_isLocalizationAway_finiteDenominator K S
  let j : S.integer K →+* LocalResidueRing K (P i) (n i) :=
    ((Pi.evalRingHom (fun i => LocalResidueRing K (P i) (n i)) i).comp
      (sIntegerResidueCRT K S I hI P n hP hprod).toRingHom).comp
        (Ideal.Quotient.mk (I.map (algebraMap (𝓞 K) (S.integer K))))
  have hsame : j = sIntegerToLocalResidue K S (P i) hi (n i) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (finiteSIntegerDenominator K S))
    apply RingHom.ext
    intro b
    change sIntegerResidueCRT K S I hI P n hP hprod
        (Ideal.Quotient.mk (I.map (algebraMap (𝓞 K) (S.integer K)))
          (algebraMap (𝓞 K) (S.integer K) b)) i =
      sIntegerToLocalResidue K S (P i) hi (n i)
        (algebraMap (𝓞 K) (S.integer K) b)
    rw [sIntegerResidueCRT_mk, sIntegerToLocalResidue_algebraMap]
  exact RingHom.congr_fun hsame a

end HeckeGeneral.Arithmetic
