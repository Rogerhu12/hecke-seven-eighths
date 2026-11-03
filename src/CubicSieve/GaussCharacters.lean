import CubicSieve.GaussSquarefree
import Mathlib.Algebra.Group.Pi.Units

/-! Genuine multiplicative cubic characters on the squarefree quotient.
The character keeps the actual nonunit zeros, also at the unit ideal.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.GaussCharacters

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open CubicSieve.GaussSquarefree
open scoped Classical BigOperators nonZeroDivisors

section General
variable {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, CommRing (A i)]

def productCharacter (χ : ∀ i, MulChar (A i) ℂ) : MulChar (∀ i, A i) ℂ where
  toFun x := ∏ i, χ i (x i)
  map_one' := by simp
  map_mul' x y := by simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]
  map_nonunit' x hx := by
    have h : ∃ i, ¬ IsUnit (x i) := by
      by_contra h
      exact hx (Pi.isUnit_iff.mpr (by simpa only [not_exists, not_not] using h))
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (MulChar.map_nonunit (χ i) hi)

def transport {R T : Type*} [CommRing R] [CommRing T]
    (e : R ≃+* T) (χ : MulChar T ℂ) : MulChar R ℂ where
  toFun x := χ (e x)
  map_one' := by simp
  map_mul' x y := by simp only [map_mul]
  map_nonunit' x hx := MulChar.map_nonunit χ
    (fun h => hx (by simpa using h.map e.symm.toMonoidHom))

end General

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

def quotientCubicCharacter (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    MulChar (ThetaQuotient K S I) ℂ :=
  transport (residueEquiv K S I hI)
    (productCharacter (fun p => localCharacter K S D I p ^ (2 : ℕ)))

@[simp] theorem quotientCubicCharacter_apply (I : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) (q : ThetaQuotient K S I) :
    quotientCubicCharacter K S D I hI q = quotientFunction K S D I q ^ 2 :=
  mixedRow_constant K S D I hI 2 (by decide) q

theorem quotientCubicCharacter_cube (I : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) : quotientCubicCharacter K S D I hI ^ 3 = 1 := by
  apply DFunLike.ext
  intro q
  by_cases hq : IsUnit q
  · rw [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0),
      quotientCubicCharacter_apply, ← pow_mul,
      quotientFunction_eq_product K S D I hI, ← Finset.prod_pow,
      MulChar.one_apply hq]
    apply Finset.prod_eq_one
    intro p _
    have hpunit : IsUnit (residueEquiv K S I hI q p) :=
      (Pi.isUnit_iff.mp (hq.map (residueEquiv K S I hI).toMonoidHom)) p
    have horder : localCharacter K S D I p ^ 6 = 1 := by
      have h := pow_orderOf_eq_one (localCharacter K S D I p)
      rw [localCharacter_order K S D I p] at h
      exact h
    have h := congrArg (fun χ : MulChar _ ℂ => χ (residueEquiv K S I hI q p)) horder
    simpa only [MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0),
      MulChar.one_apply hpunit] using h
  · rw [MulChar.map_nonunit _ hq, MulChar.map_nonunit _ hq]

theorem quotientCubicCharacter_neg_one (I : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) : quotientCubicCharacter K S D I hI (-1) = 1 := by
  exact MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd (3 : ℕ))
    (quotientCubicCharacter_cube K S D I hI)

def principalEquiv (I : ExteriorIdeal K S) :
    (S.integer K ⧸ Ideal.span ({D.generator I} : Set (S.integer K))) ≃+*
      ThetaQuotient K S I := Ideal.quotEquivOfEq (D.generator_span I)

def principalCubicCharacter (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    MulChar (S.integer K ⧸ Ideal.span ({D.generator I} : Set (S.integer K))) ℂ :=
  transport (principalEquiv K S D I) (quotientCubicCharacter K S D I hI)

@[simp] theorem principalCubicCharacter_mk (I : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) (a : S.integer K) :
    principalCubicCharacter K S D I hI (Ideal.Quotient.mk _ a) =
      sIntegerSexticIdealEvaluation K S D.root6 D.primitive6 D.embedding
        I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
        (fun p hp => D.away_six p (I.property p hp)) a ^ 2 := by
  change quotientCubicCharacter K S D I hI
    ((Ideal.quotEquivOfEq (D.generator_span I)) (Ideal.Quotient.mk _ a)) = _
  rw [Ideal.quotEquivOfEq_mk, quotientCubicCharacter_apply]
  simp only [quotientFunction, sIntegerSexticIdealQuotientFunction_mk]

theorem principalCubicCharacter_neg_one (I : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) : principalCubicCharacter K S D I hI (-1) = 1 := by
  change quotientCubicCharacter K S D I hI (principalEquiv K S D I (-1)) = 1
  have he : principalEquiv K S D I (-1) = -1 := by
    exact RingEquiv.map_neg_one (principalEquiv K S D I)
  rw [he, quotientCubicCharacter_neg_one]

end CubicSieve.GaussCharacters
