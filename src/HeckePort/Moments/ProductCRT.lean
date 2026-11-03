import HeckePort.Moments.HeterogeneousCRT
import HeckePort.Moments.CommonSupport
import HeckePort.Moments.Canonical

/-!
# Correlations over products of coprime moduli

Port of the generic part of openai/math `OAI/NumberTheory/DirichletL/Moments/ProductCRT.lean`
(revision `fd4aeeb2`): the CRT splitting of the full-modulus correlation of products of pairwise
coprime moduli (statements over an arbitrary commutative ring `A`), verbatim.  The
`Eisenstein` section (`supported_character_product`, `actualCorrelation_product_norm`) is about
the sextic supported-modulus characters of `ℤ[ω]` and is not ported; it is the instance of
`fullModulusCorrelation_product_norm` for those characters.
-/

noncomputable section
open scoped BigOperators Classical
namespace HeckePort.Moments.ProductCRT
open HeckePort.Moments HeckePort.Moments.CommonSupport HeckePort.Moments.HeterogeneousCRT

theorem norm_char_unit {R : Type*} [CommRing R] [Finite Rˣ] (χ : MulChar R ℂ) (u : Rˣ) :
    ‖χ (u : R)‖ = 1 := by
  have := Fintype.ofFinite Rˣ
  simpa only [MulChar.coe_equivToUnitHom] using
    Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

variable {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]

def productCRT (a : ι → A)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i}))) :
    Residue (∏ i, a i) ≃+* ∀ i, Residue (a i) :=
  (Ideal.quotEquivOfEq (Ideal.prod_span_singleton Finset.univ a).symm).trans
    (quotientProdEquivPi (fun i => Ideal.span {a i}) hcop)

omit [DecidableEq ι] in
@[simp] theorem productCRT_mk (a : ι → A)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i})))
    (x : A) (i : ι) :
    productCRT a hcop (Ideal.Quotient.mk _ x) i = Ideal.Quotient.mk _ x := by
  simp only [productCRT, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    quotientProdEquivPi_mk]

def jointCRT (a b : ι → A)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i}))) :
    Residue ((∏ i, a i) * ∏ i, b i) ≃+* ∀ i, Residue (a i * b i) :=
  (Ideal.quotEquivOfEq (congrArg (fun x : A => Ideal.span {x})
    (Finset.prod_mul_distrib (s := Finset.univ) (f := a) (g := b)).symm)).trans
      (productCRT (fun i => a i * b i) hcop)

omit [DecidableEq ι] in
@[simp] theorem jointCRT_mk (a b : ι → A)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    (x : A) (i : ι) :
    jointCRT a b hcop (Ideal.Quotient.mk _ x) i = Ideal.Quotient.mk _ x := by
  simp only [jointCRT, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, productCRT_mk]

def cofactor (a : ι → A) (i : ι) : A := ∏ j ∈ Finset.univ.erase i, a j

theorem factor_mul_cofactor (a : ι → A) (i : ι) : a i * cofactor a i = ∏ j, a j :=
  Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)

theorem left_crt_component (a b : ι → A)
    (ha : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i})))
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    (x : Residue (∏ i, a i)) (i : ι) :
    jointCRT a b hab
      (scaledResidue (∏ i, a i) (∏ i, b i) ((∏ i, a i) * ∏ i, b i) rfl x) i =
      scaledResidue (a i) (b i) (a i * b i) rfl
        (Ideal.Quotient.mk _ (cofactor b i) * productCRT a ha x i) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [scaledResidue_mk, jointCRT_mk, productCRT_mk, ← map_mul, scaledResidue_mk]
  congr 1
  rw [← factor_mul_cofactor b i]
  ring

theorem right_crt_component (a b : ι → A)
    (hb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i})))
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    (y : Residue (∏ i, b i)) (i : ι) :
    jointCRT a b hab
      (scaledResidue (∏ i, b i) (∏ i, a i) ((∏ i, a i) * ∏ i, b i) (mul_comm _ _) y) i =
      scaledResidue (b i) (a i) (a i * b i) (mul_comm _ _)
        (Ideal.Quotient.mk _ (cofactor a i) * productCRT b hb y i) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, jointCRT_mk, productCRT_mk, ← map_mul, scaledResidue_mk]
  congr 1
  rw [← factor_mul_cofactor a i]
  ring

theorem fullModulusCorrelation_product (a b : ι → A)
    (ha : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i})))
    (hb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i})))
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    [Fintype (Residue (∏ i, a i))] [Fintype (Residue (∏ i, b i))]
    [∀ i, Fintype (Residue (a i))] [∀ i, Fintype (Residue (b i))]
    (χ : ∀ i, MulChar (Residue (a i)) ℂ) (ψ : ∀ i, MulChar (Residue (b i)) ℂ) (h : A) :
    fullModulusCorrelation (∏ i, a i) (∏ i, b i)
      (crtCharacter (productCRT a ha) χ) (crtCharacter (productCRT b hb) ψ) h =
      ∏ i, fullCorrelation
        (fun x => scaledResidue (a i) (b i) (a i * b i) rfl
          (Ideal.Quotient.mk _ (cofactor b i) * x))
        (fun y => scaledResidue (b i) (a i) (a i * b i) (mul_comm _ _)
          (Ideal.Quotient.mk _ (cofactor a i) * y))
        (χ i) (ψ i) (Ideal.Quotient.mk _ h) := by
  have hcrt := fullCorrelation_three_equiv (productCRT a ha).toEquiv (productCRT b hb).toEquiv
    (jointCRT a b hab)
    (scaledResidue (∏ i, a i) (∏ i, b i) ((∏ i, a i) * ∏ i, b i) rfl)
    (scaledResidue (∏ i, b i) (∏ i, a i) ((∏ i, a i) * ∏ i, b i) (mul_comm _ _))
    (fun i x => scaledResidue (a i) (b i) (a i * b i) rfl
      (Ideal.Quotient.mk _ (cofactor b i) * x))
    (fun i y => scaledResidue (b i) (a i) (a i * b i) (mul_comm _ _)
      (Ideal.Quotient.mk _ (cofactor a i) * y))
    (left_crt_component a b ha hab) (right_crt_component a b hb hab)
    (fun i => χ i) (fun i => ψ i) (Ideal.Quotient.mk _ h)
  simpa only [fullModulusCorrelation, fullCorrelation, crtCharacter_apply, jointCRT_mk,
    RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe] using hcrt

theorem cross_cofactor_coprime (a b : ι → A)
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    (i : ι) : IsCoprime (a i) (cofactor b i) := by
  unfold cofactor
  apply IsCoprime.prod_right
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hij := (Ideal.isCoprime_span_singleton_iff _ _).mp (hab hji.symm)
  exact (IsCoprime.mul_right_iff.mp (IsCoprime.mul_left_iff.mp hij).1).2

theorem local_cofactor_norm (a b : ι → A)
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    [∀ i, Fintype (Residue (a i))] [∀ i, Fintype (Residue (b i))]
    (χ : ∀ i, MulChar (Residue (a i)) ℂ) (ψ : ∀ i, MulChar (Residue (b i)) ℂ)
    (h : A) (i : ι) :
    ‖fullCorrelation
        (fun x => scaledResidue (a i) (b i) (a i * b i) rfl
          (Ideal.Quotient.mk _ (cofactor b i) * x))
        (fun y => scaledResidue (b i) (a i) (a i * b i) (mul_comm _ _)
          (Ideal.Quotient.mk _ (cofactor a i) * y))
        (χ i) (ψ i) (Ideal.Quotient.mk _ h)‖ =
      ‖fullModulusCorrelation (a i) (b i) (χ i) (ψ i) h‖ := by
  obtain ⟨u, hu⟩ := isUnit_residue_of_coprime (a i) (cofactor b i)
    (cross_cofactor_coprime a b hab i)
  have hba : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i * a i})) := by
    simpa only [mul_comm] using hab
  obtain ⟨v, hv⟩ := isUnit_residue_of_coprime (b i) (cofactor a i)
    (cross_cofactor_coprime b a hba i)
  rw [← hu, ← hv, fullCorrelation_unit_change, norm_mul, norm_mul, norm_star,
    norm_char_unit, norm_char_unit, one_mul, one_mul]
  rfl

theorem fullModulusCorrelation_product_norm (a b : ι → A)
    (ha : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i})))
    (hb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i})))
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    [Fintype (Residue (∏ i, a i))] [Fintype (Residue (∏ i, b i))]
    [∀ i, Fintype (Residue (a i))] [∀ i, Fintype (Residue (b i))]
    (χ : ∀ i, MulChar (Residue (a i)) ℂ) (ψ : ∀ i, MulChar (Residue (b i)) ℂ) (h : A) :
    ‖fullModulusCorrelation (∏ i, a i) (∏ i, b i)
      (crtCharacter (productCRT a ha) χ) (crtCharacter (productCRT b hb) ψ) h‖ =
      ∏ i, ‖fullModulusCorrelation (a i) (b i) (χ i) (ψ i) h‖ := by
  rw [fullModulusCorrelation_product a b ha hb hab χ ψ h, norm_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact local_cofactor_norm a b hab χ ψ h i

end HeckePort.Moments.ProductCRT

end
