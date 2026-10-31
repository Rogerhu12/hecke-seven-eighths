module

public import HeckeSkeleton.Moments.MOM_INV_STEP.LocalGauss
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# Exact Gauss factorization for any primitive character on a field product

The local additive characters are restrictions of the given global
character to the actual CRT coordinates.  Their product formula and
primitivity are proved here, so there is no independently chosen additive
phase and no assumed CRT Fourier identity.  The empty product is included.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ProductGauss

open scoped Classical BigOperators

variable {ι : Type*} [Fintype ι] {F : ι → Type*}
  [∀ i, Field (F i)] [∀ i, Fintype (F i)]

/-- The exact additive phase restricted to one CRT coordinate. -/
def coordinateCharacter (ψ : AddChar (∀ i, F i) ℂ) (i : ι) : AddChar (F i) ℂ where
  toFun a := ψ (Pi.single i a)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    rw [Pi.single_add, AddChar.map_add_eq_mul]

@[simp] theorem coordinateCharacter_apply
    (ψ : AddChar (∀ i, F i) ℂ) (i : ι) (a : F i) :
    coordinateCharacter ψ i a = ψ (Pi.single i a) := rfl

private theorem addChar_sum {A : Type*} [AddCommMonoid A]
    (ψ : AddChar A ℂ) (T : Finset ι) (x : ι → A) :
    ψ (∑ i ∈ T, x i) = ∏ i ∈ T, ψ (x i) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi,
      AddChar.map_add_eq_mul, ih]

/-- Any additive character of the product is the product of its actual
coordinate restrictions. -/
theorem character_eq_product (ψ : AddChar (∀ i, F i) ℂ) (x : ∀ i, F i) :
    ψ x = ∏ i, coordinateCharacter ψ i (x i) := by
  have hx : x = ∑ i, Pi.single i (x i) := by
    ext j
    simp
  calc
    ψ x = ψ (∑ i, Pi.single i (x i)) := congrArg ψ hx
    _ = _ := addChar_sum ψ Finset.univ _

theorem coordinateCharacter_ne_one (ψ : AddChar (∀ i, F i) ℂ)
    (hψ : ψ.IsPrimitive) (i : ι) : coordinateCharacter ψ i ≠ 1 := by
  intro hi
  have hnonzero : (Pi.single i (1 : F i) : ∀ j, F j) ≠ 0 := by
    intro hz
    have h := congrFun hz i
    simpa using h
  apply hψ hnonzero
  ext x
  have hmul : Pi.single i (1 : F i) * x = Pi.single i (x i) := by
    ext j
    by_cases hij : j = i
    · subst j
      simp
    · simp [Pi.single_eq_of_ne hij]
  simp only [AddChar.mulShift_apply, AddChar.one_apply, hmul]
  exact congrArg (fun χ : AddChar (F i) ℂ => χ (x i)) hi

def tensorCoefficient (χ : ∀ i, MulChar (F i) ℂ) (x : ∀ i, F i) : ℂ :=
  ∏ i, χ i (x i)

def gaussProduct (χ : ∀ i, MulChar (F i) ℂ)
    (ψ : AddChar (∀ i, F i) ℂ) : ℂ :=
  ∏ i, gaussSum (χ i) (coordinateCharacter ψ i)

/-- Genuine finite Fourier evaluation, including every nonunit frequency
and the zero frequency of the product ring. -/
theorem finite_fourier (χ : ∀ i, MulChar (F i) ℂ) (hχ : ∀ i, χ i ≠ 1)
    (ψ : AddChar (∀ i, F i) ℂ) (k : ∀ i, F i) :
    (∑ x : ∀ i, F i, tensorCoefficient χ x * ψ (k * x)) =
      star (tensorCoefficient χ k) * gaussProduct χ ψ := by
  calc
    _ = ∑ x : ∀ i, F i, ∏ i, χ i (x i) *
        coordinateCharacter ψ i (k i * x i) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [character_eq_product]
      simp only [tensorCoefficient, Pi.mul_apply, Finset.prod_mul_distrib]
    _ = ∏ i, ∑ x : F i, χ i x * coordinateCharacter ψ i (k i * x) :=
      (Fintype.prod_sum _).symm
    _ = ∏ i, star (χ i (k i)) * gaussSum (χ i) (coordinateCharacter ψ i) := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact LocalGauss.nonprincipal_fourier (χ i) (hχ i) _ _
    _ = _ := by
      simp only [tensorCoefficient, gaussProduct, Finset.prod_mul_distrib, star_prod]

/-- The product of actual local Gauss factors has the exact square-root
cardinality; the local additive nontriviality follows from global
primitivity. -/
theorem gaussProduct_norm (χ : ∀ i, MulChar (F i) ℂ) (hχ : ∀ i, χ i ≠ 1)
    (ψ : AddChar (∀ i, F i) ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussProduct χ ψ‖ = Real.sqrt (Fintype.card (∀ i, F i) : ℝ) := by
  simp only [gaussProduct, norm_prod]
  rw [Fintype.card_pi, Nat.cast_prod,
    Real.sqrt_prod Finset.univ (fun i _hi => Nat.cast_nonneg (Fintype.card (F i)))]
  apply Finset.prod_congr rfl
  intro i _hi
  exact LocalGauss.nonprincipal_gauss_norm (χ i) (hχ i)
    (coordinateCharacter ψ i) (coordinateCharacter_ne_one ψ hψ i)

end HeckeSkeleton.Moments.MOM_INV_STEP.ProductGauss

end
