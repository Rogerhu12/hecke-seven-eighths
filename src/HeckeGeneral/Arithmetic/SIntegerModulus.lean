import HeckeGeneral.Arithmetic.SIntegerResidue
import Mathlib.Algebra.Ring.NonZeroDivisors

/-! Every nonzero principal S-integer modulus contracts to a genuine nonzero
ordinary ideal coprime to S. No principal ideal property is required. -/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]

/-- The actual contraction of the principal modulus. -/
def sIntegerModulusContraction (c : S.integer K) : Ideal (𝓞 K) :=
  (Ideal.span ({c} : Set (S.integer K))).under (𝓞 K)

theorem map_sIntegerModulusContraction (c : S.integer K) :
    (sIntegerModulusContraction K S c).map (algebraMap (𝓞 K) (S.integer K)) =
      Ideal.span ({c} : Set (S.integer K)) := by
  letI := sInteger_isLocalizationAway_finiteDenominator K S
  exact IsLocalization.map_under
    (Submonoid.powers (finiteSIntegerDenominator K S)) (S.integer K) _

theorem sIntegerModulusContraction_ne_bot (c : S.integer K) (hc : c ≠ 0) :
    sIntegerModulusContraction K S c ≠ ⊥ := by
  intro h
  have he := map_sIntegerModulusContraction K S c
  rw [h, Ideal.map_bot] at he
  exact hc (Ideal.span_singleton_eq_bot.mp he.symm)

/-- A localization denominator is already a unit modulo the contracted
nonzero ideal: injectivity into the localized quotient and finiteness suffice. -/
theorem isUnit_denominator_sIntegerModulusContraction
    (c : S.integer K) (hc : c ≠ 0) :
    IsUnit (Ideal.Quotient.mk (sIntegerModulusContraction K S c)
      (finiteSIntegerDenominator K S)) := by
  letI := sInteger_isLocalizationAway_finiteDenominator K S
  let I := sIntegerModulusContraction K S c
  let J := Ideal.span ({c} : Set (S.integer K))
  let q : (𝓞 K ⧸ I) →+* (S.integer K ⧸ J) :=
    Ideal.quotientMap J (algebraMap (𝓞 K) (S.integer K)) le_rfl
  have hq : Function.Injective q := Ideal.quotientMap_injective' le_rfl
  letI : Finite (𝓞 K ⧸ I) :=
    Ring.HasFiniteQuotients.finiteQuotient (sIntegerModulusContraction_ne_bot K S c hc)
  have hu : IsUnit (q (Ideal.Quotient.mk I (finiteSIntegerDenominator K S))) := by
    change IsUnit (Ideal.Quotient.mk J
      (algebraMap (𝓞 K) (S.integer K) (finiteSIntegerDenominator K S)))
    exact (IsLocalization.Away.algebraMap_isUnit
      (S := S.integer K) (finiteSIntegerDenominator K S)).map (Ideal.Quotient.mk J)
  apply IsLeftRegular.isUnit_of_finite
  intro x y hxy
  apply hq
  apply hu.mul_left_cancel
  simpa only [map_mul] using congrArg q hxy

theorem sIntegerModulusContraction_sup_denominator
    (c : S.integer K) (hc : c ≠ 0) :
    sIntegerModulusContraction K S c ⊔
      Ideal.span ({finiteSIntegerDenominator K S} : Set (𝓞 K)) = ⊤ := by
  let I := sIntegerModulusContraction K S c
  let a := finiteSIntegerDenominator K S
  obtain ⟨b, hb⟩ := (isUnit_denominator_sIntegerModulusContraction K S c hc).exists_right_inv
  obtain ⟨b₀, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hi : 1 - a * b₀ ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simp only [I, a, map_sub, map_one, map_mul, hb, sub_self]
  have ha : a * b₀ ∈ Ideal.span ({a} : Set (𝓞 K)) :=
    Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton a))
  apply (Ideal.eq_top_iff_one _).mpr
  have hsum := Ideal.add_mem (I ⊔ Ideal.span ({a} : Set (𝓞 K)))
    (Ideal.mem_sup_left hi) (Ideal.mem_sup_right ha)
  simpa only [sub_add_cancel] using hsum

/-- The contracted ideal is coprime to every original exceptional prime. -/
theorem sIntegerModulusContraction_coprime
    (c : S.integer K) (hc : c ≠ 0) :
    ∀ v ∈ S, sIntegerModulusContraction K S c ⊔ v.asIdeal = ⊤ := by
  intro v hv
  have ha : finiteSIntegerDenominator K S ∈ v.asIdeal := by
    have hs : v ∈ integerPrimeSupport (finiteSIntegerDenominator K S) := by
      rw [integerPrimeSupport_finiteSIntegerDenominator K S]
      exact hv
    exact hs
  apply top_unique
  rw [← sIntegerModulusContraction_sup_denominator K S c hc]
  exact sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ha) _

/-- The quotient by an arbitrary nonzero S-integer modulus is the ordinary
residue ring of its actual contraction. -/
def sIntegerPrincipalResidueEquiv (c : S.integer K) (hc : c ≠ 0) :
    (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) ≃+*
      (𝓞 K ⧸ sIntegerModulusContraction K S c) :=
  (Ideal.quotEquivOfEq (map_sIntegerModulusContraction K S c).symm).trans
    (sIntegerResidueEquiv K S (sIntegerModulusContraction K S c)
      (sIntegerModulusContraction_coprime K S c hc)).symm

@[simp] theorem sIntegerPrincipalResidueEquiv_mk
    (c : S.integer K) (hc : c ≠ 0) (a : 𝓞 K) :
    sIntegerPrincipalResidueEquiv K S c hc
      (Ideal.Quotient.mk (Ideal.span ({c} : Set (S.integer K)))
        (algebraMap (𝓞 K) (S.integer K) a)) =
      Ideal.Quotient.mk (sIntegerModulusContraction K S c) a := by
  simp only [sIntegerPrincipalResidueEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, sIntegerResidueEquiv_symm_mk]

theorem finite_sIntegerPrincipalResidue (c : S.integer K) (hc : c ≠ 0) :
    Finite (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) := by
  letI : Finite (𝓞 K ⧸ sIntegerModulusContraction K S c) :=
    Ring.HasFiniteQuotients.finiteQuotient (sIntegerModulusContraction_ne_bot K S c hc)
  exact Finite.of_equiv (𝓞 K ⧸ sIntegerModulusContraction K S c)
    (sIntegerPrincipalResidueEquiv K S c hc).symm.toEquiv

theorem natCard_sIntegerPrincipalResidue (c : S.integer K) (hc : c ≠ 0) :
    Nat.card (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) =
      (sIntegerModulusContraction K S c).absNorm :=
  Nat.card_congr (sIntegerPrincipalResidueEquiv K S c hc).toEquiv

end HeckeGeneral.Arithmetic
