import RowCharacterIdeleDecomposition
import HeckeSkeleton.FiniteOrderKernelOpen
import HeckeGeneral.Characters.LocalCharacterDecomposition
import HeckeGeneral.Analysis.HeckeSeries
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeGeneral.Characters.RowUniquenessDraft

open NumberField IsDedekindDomain
open HeckeSkeleton.FiniteOrderKernelOpen
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

def ideleComparison : ProviderIdele K ≃ₜ* NumberField.IdeleGroup (𝓞 K) K :=
  _root_.IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv K

def comparisonHom : ProviderIdele K →ₜ* NumberField.IdeleGroup (𝓞 K) K where
  toMonoidHom := (ideleComparison K).toMulEquiv.toMonoidHom
  continuous_toFun := (ideleComparison K).continuous

def comparisonInvHom : NumberField.IdeleGroup (𝓞 K) K →ₜ* ProviderIdele K where
  toMonoidHom := (ideleComparison K).symm.toMulEquiv.toMonoidHom
  continuous_toFun := (ideleComparison K).symm.continuous

/-- A continuous presentation of the actual provider finite-place map.
Continuity is transported through the proved topological equivalence. -/
def finitePlaceContinuous (p : HeightOneSpectrum (𝓞 K)) :
    (p.adicCompletion K)ˣ →ₜ* ProviderIdele K :=
  (comparisonInvHom K).comp (localIdeleEmbedding K p)

theorem finitePlaceContinuous_apply (p : HeightOneSpectrum (𝓞 K))
    (z : (p.adicCompletion K)ˣ) :
    finitePlaceContinuous K p z = _root_.IdeleGroup.finitePlaceIdele p z := by
  apply (ideleComparison K).injective
  change (ideleComparison K) ((ideleComparison K).symm (localIdeleEmbedding K p z)) =
    (ideleComparison K) (_root_.IdeleGroup.finitePlaceIdele p z)
  rw [ContinuousMulEquiv.apply_symm_apply]
  exact (_root_.IdeleGroup.equivAdeleRingUnits_finitePlaceIdele K p z).symm

def providerCharacter (χ : HeckeCharacter K) : ProviderIdele K →ₜ* Circle :=
  (toIdeleCharacter K χ).comp (comparisonHom K)

theorem providerCharacter_finiteOrder (χ : HeckeCharacter K) (hχ : FiniteOrder χ) :
    FiniteOrder (providerCharacter K χ) := by
  obtain ⟨n, hn, hpow⟩ := (finiteOrder_iff_pointwise χ).mp hχ
  apply (finiteOrder_iff_pointwise (providerCharacter K χ)).mpr
  refine ⟨n, hn, fun a => ?_⟩
  change (χ (ideleClassMap K (comparisonHom K a))) ^ n = 1
  exact hpow (ideleClassMap K (comparisonHom K a))

theorem providerCharacter_principal (χ : HeckeCharacter K) (x : Kˣ) :
    providerCharacter K χ (_root_.IdeleGroup.principalIdele K x) = 1 := by
  change toIdeleCharacter K χ
    (_root_.IdeleGroup.equivAdeleRingUnits (_root_.IdeleGroup.principalIdele K x)) = 1
  rw [_root_.IdeleGroup.equivAdeleRingUnits_principalIdele K x]
  exact toIdeleCharacter_trivial K χ x

theorem providerCharacter_finite (χ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) (z : (p.adicCompletion K)ˣ) :
    providerCharacter K χ (_root_.IdeleGroup.finitePlaceIdele p z) =
      localComponent K p χ z := by
  change toIdeleCharacter K χ
    (_root_.IdeleGroup.equivAdeleRingUnits (_root_.IdeleGroup.finitePlaceIdele p z)) = _
  rw [_root_.IdeleGroup.equivAdeleRingUnits_finitePlaceIdele K p z]
  rfl

theorem providerCharacter_injective : Function.Injective (providerCharacter K) := by
  intro χ ψ h
  apply ContinuousMonoidHom.ext
  intro c
  refine QuotientGroup.induction_on c (fun a => ?_)
  change χ (ideleClassMap K a) = ψ (ideleClassMap K a)
  have ha := DFunLike.congr_fun h ((ideleComparison K).symm a)
  change χ (ideleClassMap K ((ideleComparison K) ((ideleComparison K).symm a))) =
    ψ (ideleClassMap K ((ideleComparison K) ((ideleComparison K).symm a))) at ha
  simpa only [ContinuousMulEquiv.apply_symm_apply] using ha

@[simp] theorem providerCharacter_one : providerCharacter K (1 : HeckeCharacter K) = 1 := by
  ext a
  rfl

/-- A principal-trivial finite-order idele character cannot have only
finitely many nontrivial finite local restrictions. All infinite places
are included in the genuine weak approximation step. -/
theorem finiteOrder_providerCharacter_eq_one_of_local_away
    (η : ProviderIdele K →ₜ* Circle) (hη : FiniteOrder η)
    (hprincipal : ∀ x : Kˣ, η (_root_.IdeleGroup.principalIdele K x) = 1)
    (B : Finset (HeightOneSpectrum (𝓞 K)))
    (haway : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ B →
      ∀ z : (p.adicCompletion K)ˣ,
        η (_root_.IdeleGroup.finitePlaceIdele p z) = 1) : η = 1 := by
  let U : ∀ p : B, Subgroup (p.val.adicCompletion K)ˣ :=
    fun p => (η.comp (finitePlaceContinuous K p.val)).toMonoidHom.ker
  let V : ∀ v : InfinitePlace K, Subgroup v.Completionˣ :=
    fun v => (η.comp (_root_.IdeleGroup.infinitePlaceIdeleContinuous v)).toMonoidHom.ker
  have hU : ∀ p : B, IsOpen (U p : Set (p.val.adicCompletion K)ˣ) := by
    intro p
    exact isOpen_ker_circle_of_finiteOrder
      (η.comp (finitePlaceContinuous K p.val))
      (finiteOrder_pullback (finitePlaceContinuous K p.val) hη)
  have hV : ∀ v : InfinitePlace K, IsOpen (V v : Set v.Completionˣ) := by
    intro v
    exact isOpen_ker_circle_of_finiteOrder
      (η.comp (_root_.IdeleGroup.infinitePlaceIdeleContinuous v))
      (finiteOrder_pullback (_root_.IdeleGroup.infinitePlaceIdeleContinuous v) hη)
  apply ContinuousMonoidHom.ext
  intro a
  obtain ⟨x, hxf, hxi⟩ :=
    _root_.IdeleGroup.exists_principal_quotient_mem_openAllLocalSubgroups_finset
      (K := K) B a U V hU hV
  let y := a * (_root_.IdeleGroup.principalIdele K x)⁻¹
  have hyf : ∀ p : HeightOneSpectrum (𝓞 K),
      η (_root_.IdeleGroup.finitePlaceIdele p (y.2 p)) = 1 := by
    intro p
    by_cases hp : p ∈ B
    · have h := hxf ⟨p, hp⟩
      change η (finitePlaceContinuous K p
        (a.2 p * ((_root_.IdeleGroup.principalIdele K x).2 p)⁻¹)) = 1 at h
      rw [finitePlaceContinuous_apply] at h
      exact h
    · exact haway p hp (y.2 p)
  have hyi : ∀ v : InfinitePlace K,
      η (_root_.IdeleGroup.infinitePlaceIdele v
        (_root_.IdeleGroup.infiniteComponent v y)) = 1 := by
    intro v
    have h := hxi v
    change η (_root_.IdeleGroup.infinitePlaceIdele v
      (_root_.IdeleGroup.infiniteComponent v a *
        (_root_.IdeleGroup.infiniteComponent v (_root_.IdeleGroup.principalIdele K x))⁻¹)) = 1 at h
    simpa only [y, map_mul, map_inv] using h
  have hy := ideleCharacter_value_eq_one_of_local_values K η y hyf hyi
  change η (a * (_root_.IdeleGroup.principalIdele K x)⁻¹) = 1 at hy
  rw [map_mul, map_inv, hprincipal x, inv_one, mul_one] at hy
  exact hy

theorem localComponent_eq_of_unramified_primeCoefficient_eq
    (χ ψ : HeckeCharacter K) (p : HeightOneSpectrum (𝓞 K))
    (hχ : UnramifiedAt K χ p) (hψ : UnramifiedAt K ψ p)
    (hcoeff : primeCoefficient K χ p = primeCoefficient K ψ p) :
    localComponent K p χ = localComponent K p ψ := by
  apply localCharacter_ext K p
  · intro u
    exact (hχ _ (localIntegerUnitsEmbedding_norm K p u)).trans
      (hψ _ (localIntegerUnitsEmbedding_norm K p u)).symm
  · apply Circle.ext
    exact (primeCoefficient_of_unramified K χ p hχ).symm.trans
      (hcoeff.trans (primeCoefficient_of_unramified K ψ p hψ))

/-- Finite-order GL(1) uniqueness, proved from actual local decompositions
and weak approximation, with no supplied global extensionality premise. -/
theorem finiteOrder_heckeCharacter_eq_of_primeCoefficient_eq_away
    (χ ψ : HeckeCharacter K) (hχ : FiniteOrder χ) (hψ : FiniteOrder ψ)
    (B : Finset (HeightOneSpectrum (𝓞 K)))
    (hcoeff : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ B →
      primeCoefficient K χ p = primeCoefficient K ψ p) : χ = ψ := by
  obtain ⟨Bχ, hBχ⟩ := exists_finset_unramified K χ
  obtain ⟨Bψ, hBψ⟩ := exists_finset_unramified K ψ
  let B' := B ∪ (Bχ ∪ Bψ)
  let δ := χ * ψ⁻¹
  have hδ : FiniteOrder δ := hχ.mul hψ.inv
  have hlocal : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ B' →
      localComponent K p χ = localComponent K p ψ := by
    intro p hp
    have hpB : p ∉ B := fun h => hp (Finset.mem_union_left _ h)
    have hpχ : p ∉ Bχ := fun h =>
      hp (Finset.mem_union_right _ (Finset.mem_union_left _ h))
    have hpψ : p ∉ Bψ := fun h =>
      hp (Finset.mem_union_right _ (Finset.mem_union_right _ h))
    exact localComponent_eq_of_unramified_primeCoefficient_eq K χ ψ p
      (hBχ p hpχ) (hBψ p hpψ) (hcoeff p hpB)
  have hη := finiteOrder_providerCharacter_eq_one_of_local_away K
    (providerCharacter K δ) (providerCharacter_finiteOrder K δ hδ)
    (providerCharacter_principal K δ) B' (by
      intro p hp z
      rw [providerCharacter_finite]
      change localComponent K p χ z * (localComponent K p ψ z)⁻¹ = 1
      rw [DFunLike.congr_fun (hlocal p hp) z, mul_inv_cancel])
  have hd : δ = 1 := by
    apply providerCharacter_injective K
    simpa only [providerCharacter_one] using hη
  exact mul_inv_eq_one.mp hd

end HeckeGeneral.Characters.RowUniquenessDraft
