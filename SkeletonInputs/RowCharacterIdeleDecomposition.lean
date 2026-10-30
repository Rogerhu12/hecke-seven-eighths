import HeckeGeneral.Characters.ProductCharacter
import ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeGeneral.Characters.RowUniquenessDraft

open NumberField IsDedekindDomain
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

abbrev ProviderIdele := _root_.IdeleGroup K
abbrev LocalIntegralUnit (p : HeightOneSpectrum (𝓞 K)) :=
  (p.adicCompletionIntegers K).units

/-- The entire product of local integral units, not merely its direct sum. -/
def integralProductIdele :
    (∀ p : HeightOneSpectrum (𝓞 K), LocalIntegralUnit K p) →ₜ* ProviderIdele K where
  toFun u := (1, RestrictedProduct.structureMap
    (fun p : HeightOneSpectrum (𝓞 K) => (p.adicCompletion K)ˣ)
    (fun p => ((p.adicCompletionIntegers K).units : Set (p.adicCompletion K)ˣ))
    Filter.cofinite u)
  map_one' := by
    apply Prod.ext
    · rfl
    · apply RestrictedProduct.ext
      intro p
      rfl
  map_mul' u v := by
    apply Prod.ext
    · simp
    · apply RestrictedProduct.ext
      intro p
      rfl
  continuous_toFun := continuous_const.prodMk
    (RestrictedProduct.isEmbedding_structureMap
      (R := fun p : HeightOneSpectrum (𝓞 K) => (p.adicCompletion K)ˣ)
      (A := fun p => ((p.adicCompletionIntegers K).units : Set (p.adicCompletion K)ˣ))
      (𝓕 := Filter.cofinite)).continuous

theorem integralProductIdele_single (p : HeightOneSpectrum (𝓞 K))
    (u : LocalIntegralUnit K p) :
    integralProductIdele K (Pi.mulSingle p u) =
      _root_.IdeleGroup.finitePlaceIdele p u.val := by
  apply Prod.ext
  · rfl
  · apply RestrictedProduct.ext
    intro q
    change (Pi.mulSingle (M := fun p => LocalIntegralUnit K p) p u q).val =
      _root_.IdeleGroup.finiteComponent q (_root_.IdeleGroup.finitePlaceIdele p u.val)
    by_cases hq : q = p
    · subst q
      rw [Pi.mulSingle_eq_same,
        _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same]
    · rw [Pi.mulSingle_eq_of_ne hq,
        _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne p q u.val hq]
      rfl

def infiniteProductIdele :
    (∀ v : InfinitePlace K, v.Completionˣ) →ₜ* ProviderIdele K where
  toFun u := (ContinuousMulEquiv.piUnits.symm u, 1)
  map_one' := by rw [map_one]; rfl
  map_mul' u v := by
    apply Prod.ext
    · exact map_mul _ u v
    · simp
  continuous_toFun := ContinuousMulEquiv.piUnits.symm.continuous.prodMk continuous_const

theorem infiniteProductIdele_single (v : InfinitePlace K) (u : v.Completionˣ) :
    infiniteProductIdele K (Pi.mulSingle v u) =
      _root_.IdeleGroup.infinitePlaceIdele v u := rfl

def finiteSupportedIdele (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ p : HeightOneSpectrum (𝓞 K), (p.adicCompletion K)ˣ) : ProviderIdele K :=
  ∏ p ∈ S, _root_.IdeleGroup.finitePlaceIdele p (a p)

theorem finiteSupportedIdele_infinite (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ p : HeightOneSpectrum (𝓞 K), (p.adicCompletion K)ˣ) :
    (finiteSupportedIdele K S a).1 = 1 := by
  rw [finiteSupportedIdele, Prod.fst_prod]
  change (∏ p ∈ S, (1 : _root_.InfiniteIdeleGroup K)) = 1
  simp

theorem finiteSupportedIdele_finite (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ p : HeightOneSpectrum (𝓞 K), (p.adicCompletion K)ˣ)
    (q : HeightOneSpectrum (𝓞 K)) :
    _root_.IdeleGroup.finiteComponent q (finiteSupportedIdele K S a) =
      if q ∈ S then a q else 1 := by
  change _root_.IdeleGroup.finiteComponent q
    (∏ p ∈ S, _root_.IdeleGroup.finitePlaceIdele p (a p)) = _
  rw [map_prod]
  by_cases hq : q ∈ S
  · rw [if_pos hq, Finset.prod_eq_single q]
    · exact _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same q (a q)
    · intro p _ hpq
      exact _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne p q (a p) hpq.symm
    · intro hnot
      exact False.elim (hnot hq)
  · rw [if_neg hq]
    apply Finset.prod_eq_one
    intro p hp
    apply _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne
    intro h
    subst q
    exact hq hp

/-- Pointwise local values determine a continuous character's value on an
actual idele. The integral unit product is treated as a whole product. -/
theorem ideleCharacter_value_eq_one_of_local_values
    (η : ProviderIdele K →ₜ* Circle) (a : ProviderIdele K)
    (hfinite : ∀ p : HeightOneSpectrum (𝓞 K),
      η (_root_.IdeleGroup.finitePlaceIdele p (a.2 p)) = 1)
    (hinfinite : ∀ v : InfinitePlace K,
      η (_root_.IdeleGroup.infinitePlaceIdele v
        (_root_.IdeleGroup.infiniteComponent v a)) = 1) :
    η a = 1 := by
  have hbad : {p : HeightOneSpectrum (𝓞 K) |
      a.2 p ∉ (p.adicCompletionIntegers K).units}.Finite :=
    Filter.eventually_cofinite.mp (_root_.FiniteIdeleGroup.eventually_mem_localUnits a.2)
  let S := hbad.toFinset
  have haway : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S →
      a.2 p ∈ (p.adicCompletionIntegers K).units := by
    intro p hp
    by_contra hn
    exact hp (hbad.mem_toFinset.mpr hn)
  let u : ∀ p : HeightOneSpectrum (𝓞 K), LocalIntegralUnit K p :=
    fun p => if hp : p ∈ S then 1 else ⟨a.2 p, haway p hp⟩
  have huSingle : ∀ p : HeightOneSpectrum (𝓞 K),
      η (integralProductIdele K (Pi.mulSingle p (u p))) = 1 := by
    intro p
    rw [integralProductIdele_single]
    by_cases hp : p ∈ S
    · have hu : (u p).val = 1 := by simp [u, hp]
      simp only [hu, map_one]
    · have hu : (u p).val = a.2 p := by simp [u, hp]
      rw [hu]
      exact hfinite p
  have hIntegral : η (integralProductIdele K u) = 1 := by
    let ηU := η.comp (integralProductIdele K)
    obtain ⟨T, hT⟩ := exists_finset_product_character_eq_prod ηU
    change ηU u = 1
    rw [hT u]
    apply Finset.prod_eq_one
    intro p _
    exact huSingle p
  have hFinite : η (finiteSupportedIdele K S (fun p => a.2 p)) = 1 := by
    rw [finiteSupportedIdele, map_prod]
    exact Finset.prod_eq_one fun p _ => hfinite p
  have hInfinite : η (infiniteProductIdele K (ContinuousMulEquiv.piUnits a.1)) = 1 := by
    let ηInf := η.comp (infiniteProductIdele K)
    obtain ⟨T, hT⟩ := exists_finset_product_character_eq_prod ηInf
    change ηInf (ContinuousMulEquiv.piUnits a.1) = 1
    rw [hT (ContinuousMulEquiv.piUnits a.1)]
    apply Finset.prod_eq_one
    intro v _
    exact hinfinite v
  have hdecomp : a =
      infiniteProductIdele K (ContinuousMulEquiv.piUnits a.1) *
        finiteSupportedIdele K S (fun p => a.2 p) * integralProductIdele K u := by
    have hInf : (infiniteProductIdele K (ContinuousMulEquiv.piUnits a.1)).1 = a.1 :=
      ContinuousMulEquiv.symm_apply_apply ContinuousMulEquiv.piUnits a.1
    have hInt : (integralProductIdele K u).1 = (1 : _root_.InfiniteIdeleGroup K) := rfl
    apply Prod.ext
    · change a.1 =
        ((infiniteProductIdele K (ContinuousMulEquiv.piUnits a.1)).1 *
          (finiteSupportedIdele K S (fun p => a.2 p)).1) * (integralProductIdele K u).1
      rw [hInf, finiteSupportedIdele_infinite, hInt, mul_one, mul_one]
    · apply RestrictedProduct.ext
      intro p
      change a.2 p = (1 *
        _root_.IdeleGroup.finiteComponent p (finiteSupportedIdele K S (fun q => a.2 q))) * (u p).val
      rw [one_mul, finiteSupportedIdele_finite]
      by_cases hp : p ∈ S <;> simp [u, hp]
  rw [hdecomp, map_mul, map_mul, hInfinite, hFinite, hIntegral]
  simp

end HeckeGeneral.Characters.RowUniquenessDraft
