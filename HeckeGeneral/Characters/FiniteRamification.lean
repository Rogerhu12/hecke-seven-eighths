import HeckeGeneral.Characters.Unramified
import HeckeGeneral.Characters.SmallSubgroups

/-! A continuous unitary Hecke character is unramified at all but finitely many finite places. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter Topology
open scoped RestrictedProduct Classical

variable (K : Type*) [Field K] [NumberField K]

abbrev IntegralLocalUnits (v : HeightOneSpectrum (𝓞 K)) :=
  (v.adicCompletionIntegers K).units

private def integralFiniteUnit (u : ∀ v, IntegralLocalUnits K v) :
    (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ :=
  RestrictedProduct.mkUnit (fun v => (u v).val) (Eventually.of_forall fun v => (u v).property)

private theorem continuous_integralFiniteUnit : Continuous (integralFiniteUnit K) := by
  apply Units.continuous_iff.mpr
  constructor
  · have h := (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      (𝓕 := cofinite)).continuous
    exact h.comp (continuous_pi fun v =>
      ((Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v)).subtype_mk
        (fun u => (u v).property.1))
  · have h := (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      (𝓕 := cofinite)).continuous
    exact h.comp (continuous_pi fun v =>
      ((Units.continuous_coe_inv.comp continuous_subtype_val).comp
        (continuous_apply v)).subtype_mk (fun u => (u v).property.2))

/-- The idèle with infinite component one and an arbitrary integral unit at each finite place. -/
def integralIdele (u : ∀ v, IntegralLocalUnits K v) : IdeleGroup (𝓞 K) K where
  val := (1, (integralFiniteUnit K u).val)
  inv := (1, (integralFiniteUnit K u).inv)
  val_inv := Prod.ext (one_mul _) (integralFiniteUnit K u).val_inv
  inv_val := Prod.ext (one_mul _) (integralFiniteUnit K u).inv_val

theorem continuous_integralIdele : Continuous (integralIdele K) := by
  apply Units.continuous_iff.mpr
  exact ⟨continuous_const.prodMk (Units.continuous_val.comp (continuous_integralFiniteUnit K)),
    continuous_const.prodMk (Units.continuous_coe_inv.comp (continuous_integralFiniteUnit K))⟩

@[simp] theorem integralIdele_one : integralIdele K 1 = 1 := by
  apply Units.ext
  apply Prod.ext
  · rfl
  · rfl

theorem integralIdele_single (v : HeightOneSpectrum (𝓞 K)) (u : IntegralLocalUnits K v) :
    integralIdele K (Pi.mulSingle v u) = localIdeleEmbedding K v u.val := by
  apply Units.ext
  apply Prod.ext
  · rfl
  · apply RestrictedProduct.ext
    intro w
    change (((Pi.mulSingle (M := fun w => IntegralLocalUnits K w) v u w).val) :
      w.adicCompletion K) =
      IsDedekindDomain.FiniteAdeleRing.ofAdicCompletion K v u.val.val w
    by_cases h : w = v
    · subst w
      rw [Pi.mulSingle_eq_same, finiteOfAdicCompletion_same]
    · rw [Pi.mulSingle_eq_of_ne h, finiteOfAdicCompletion_ne K v w _ h]
      rfl

theorem exists_finset_unramified (χ : HeckeCharacter K) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ v, v ∉ S → UnramifiedAt K χ v := by
  let f := fun u : ∀ v, IntegralLocalUnits K v =>
    toIdeleCharacter K χ (integralIdele K u)
  have hf : Continuous f := (toIdeleCharacter K χ).continuous.comp (continuous_integralIdele K)
  have hone : f 1 = 1 := by simp [f]
  have hsmallone : f 1 ∈ circleSmallArc := by
    rw [hone]
    exact one_mem_circleSmallArc
  have hneigh : f ⁻¹' circleSmallArc ∈ 𝓝 (1 : ∀ v, IntegralLocalUnits K v) := by
    exact hf.continuousAt.preimage_mem_nhds (isOpen_circleSmallArc.mem_nhds hsmallone)
  rw [nhds_pi] at hneigh
  obtain ⟨S, t, ht, hsub⟩ := Filter.mem_pi'.mp hneigh
  refine ⟨S, fun v hv => (unramifiedAt_iff_integral_units K χ v).mpr ?_⟩
  intro u hu
  apply circle_eq_one_of_powers_re
  intro n
  let a : IntegralLocalUnits K v := ⟨u, hu⟩
  have hs : Pi.mulSingle v (a ^ n) ∈ Set.pi (↑S) t := by
    intro w hw
    have hne : w ≠ v := by intro he; subst w; exact hv hw
    rw [Pi.mulSingle_eq_of_ne hne]
    exact mem_of_mem_nhds (ht w)
  have hsmall := hsub hs
  change (1 / 2 : ℝ) < (f (Pi.mulSingle v (a ^ n)) : ℂ).re at hsmall
  have heq : f (Pi.mulSingle v (a ^ n)) = localComponent K v χ u ^ n := by
    rw [show f (Pi.mulSingle v (a ^ n)) =
      toIdeleCharacter K χ (integralIdele K (Pi.mulSingle v (a ^ n))) from rfl,
      integralIdele_single]
    exact map_pow (localComponent K v χ) u n
  rw [heq] at hsmall
  exact le_of_lt hsmall

theorem finite_ramifiedPlaces (χ : HeckeCharacter K) :
    {v : HeightOneSpectrum (𝓞 K) | ¬ UnramifiedAt K χ v}.Finite := by
  obtain ⟨S, hS⟩ := exists_finset_unramified K χ
  exact S.finite_toSet.subset fun v hv => by
    by_contra h
    exact hv (hS v h)

end HeckeGeneral.Characters
