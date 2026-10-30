import HeckeGeneral.Characters.LocalResidueTower
import HeckeGeneral.Characters.ProductCharacter

/-! The restriction to all finite integral idèle units descends to a finite conductor quotient. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

abbrev GlobalIntegralUnits := ∀ v : HeightOneSpectrum (𝓞 K), (LocalIntegerRing K v)ˣ

def integerUnitToIntegralLocalUnit (v : HeightOneSpectrum (𝓞 K)) :
    (LocalIntegerRing K v)ˣ →ₜ* IntegralLocalUnits K v where
  toFun u := ⟨localIntegerUnitsEmbedding K v u, localIntegerUnitsEmbedding_mem K v u⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u w := Subtype.ext (map_mul _ u w)
  continuous_toFun := (localIntegerUnitsEmbedding K v).continuous.subtype_mk _

/-- Infinite component one, with independently chosen integer units at every finite place. -/
def globalIntegralIdele : GlobalIntegralUnits K →ₜ* IdeleGroup (𝓞 K) K where
  toFun u := integralIdele K (fun v => integerUnitToIntegralLocalUnit K v (u v))
  map_one' := by
    have h : (fun v => integerUnitToIntegralLocalUnit K v ((1 : GlobalIntegralUnits K) v)) = 1 :=
      funext fun v => map_one _
    rw [h, integralIdele_one]
  map_mul' u w := by
    apply Units.ext
    apply Prod.ext
    · change (1 : InfiniteAdeleRing K) = 1 * 1
      simp
    · apply RestrictedProduct.ext
      intro v
      rfl
  continuous_toFun := (continuous_integralIdele K).comp
    (continuous_pi fun v => (integerUnitToIntegralLocalUnit K v).continuous.comp
      (continuous_apply v))

theorem globalIntegralIdele_single (v : HeightOneSpectrum (𝓞 K))
    (u : (LocalIntegerRing K v)ˣ) :
    globalIntegralIdele K (Pi.mulSingle v u) =
      localIdeleEmbedding K v (localIntegerUnitsEmbedding K v u) := by
  change integralIdele K _ = _
  have h : (fun w => integerUnitToIntegralLocalUnit K w
      (Pi.mulSingle (M := fun w => (LocalIntegerRing K w)ˣ) v u w)) =
      Pi.mulSingle v (integerUnitToIntegralLocalUnit K v u) := by
    funext w
    by_cases hw : w = v
    · subst w; simp
    · simp [Pi.mulSingle_eq_of_ne hw]
  rw [h, integralIdele_single]
  rfl

def globalIntegralComponent (χ : HeckeCharacter K) : UnitaryCharacter (GlobalIntegralUnits K) :=
  (toIdeleCharacter K χ).comp (globalIntegralIdele K)

@[simp] theorem globalIntegralComponent_single (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) (u : (LocalIntegerRing K v)ˣ) :
    globalIntegralComponent K χ (Pi.mulSingle v u) = localIntegralComponent K v χ u := by
  change toIdeleCharacter K χ (globalIntegralIdele K (Pi.mulSingle v u)) = _
  rw [globalIntegralIdele_single]
  rfl

def conductorPlaces (χ : HeckeCharacter K) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (conductorExponents K χ).support

@[simp] theorem mem_conductorPlaces (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) : v ∈ conductorPlaces K χ ↔ ¬ UnramifiedAt K χ v := by
  simp only [conductorPlaces, Finsupp.mem_support_iff]
  exact not_congr (localConductorExponent_eq_zero_iff K χ v)

/-- The product is over precisely the ramified finite places. -/
theorem globalIntegralComponent_eq_prod (χ : HeckeCharacter K) (u : GlobalIntegralUnits K) :
    globalIntegralComponent K χ u =
      ∏ v ∈ conductorPlaces K χ, localIntegralComponent K v χ (u v) := by
  simpa only [globalIntegralComponent_single] using
    product_character_eq_prod_of_trivial_outside (globalIntegralComponent K χ)
      (conductorPlaces K χ) (fun v hv x => by
        rw [globalIntegralComponent_single]
        have hur : UnramifiedAt K χ v := by
          by_contra h
          exact hv ((mem_conductorPlaces K χ v).mpr h)
        exact hur _ (localIntegerUnitsEmbedding_norm K v x)) u

/-- A genuinely finite product of the actual local residue unit groups. -/
abbrev GlobalConductorResidueUnits (χ : HeckeCharacter K) :=
  ∀ v : conductorPlaces K χ,
    (LocalResidueRing K v.val (localConductorExponent K χ v.val))ˣ

instance finite_globalConductorResidueUnits (χ : HeckeCharacter K) :
    Finite (GlobalConductorResidueUnits K χ) := inferInstance

def globalConductorReduction (χ : HeckeCharacter K) :
    GlobalIntegralUnits K →* GlobalConductorResidueUnits K χ where
  toFun u v := localUnitReduction K v.val _ (u v.val)
  map_one' := by funext v; exact map_one _
  map_mul' u w := by funext v; exact map_mul _ _ _

theorem globalConductorReduction_surjective (χ : HeckeCharacter K) :
    Function.Surjective (globalConductorReduction K χ) := by
  intro y
  choose u hu using fun v : conductorPlaces K χ =>
    localUnitReduction_surjective K v.val (localConductorExponent K χ v.val) (y v)
  let w : GlobalIntegralUnits K := fun v => if hv : v ∈ conductorPlaces K χ then u ⟨v, hv⟩ else 1
  refine ⟨w, funext fun v => ?_⟩
  change localUnitReduction K v.val _ (w v.val) = y v
  simpa only [w, dite_eq_left v.property] using hu v

def globalConductorResidueCharacter (χ : HeckeCharacter K) :
    GlobalConductorResidueUnits K χ →* Circle where
  toFun y := ∏ v, conductorResidueCharacter K v.val χ (y v)
  map_one' := by simp
  map_mul' y z := by simp [map_mul, Finset.prod_mul_distrib]

@[simp] theorem globalConductorResidueCharacter_reduction (χ : HeckeCharacter K)
    (u : GlobalIntegralUnits K) :
    globalConductorResidueCharacter K χ (globalConductorReduction K χ u) =
      globalIntegralComponent K χ u := by
  change (∏ v : conductorPlaces K χ,
    conductorResidueCharacter K v.val χ (localUnitReduction K v.val _ (u v.val))) = _
  simp only [conductorResidueCharacter_reduction]
  rw [globalIntegralComponent_eq_prod]
  exact Finset.prod_coe_sort (conductorPlaces K χ) (fun v => localIntegralComponent K v χ (u v))

theorem globalConductorResidueCharacter_unique (χ : HeckeCharacter K)
    (ψ : GlobalConductorResidueUnits K χ →* Circle)
    (hψ : ψ.comp (globalConductorReduction K χ) = (globalIntegralComponent K χ).toMonoidHom) :
    ψ = globalConductorResidueCharacter K χ := by
  apply MonoidHom.ext
  intro y
  obtain ⟨u, rfl⟩ := globalConductorReduction_surjective K χ y
  rw [globalConductorResidueCharacter_reduction]
  exact congrArg (fun f : GlobalIntegralUnits K →* Circle => f u) hψ

theorem globalIntegralComponent_range_eq (χ : HeckeCharacter K) :
    Set.range (globalIntegralComponent K χ) = Set.range (globalConductorResidueCharacter K χ) := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨globalConductorReduction K χ u, globalConductorResidueCharacter_reduction K χ u⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨u, rfl⟩ := globalConductorReduction_surjective K χ y
    exact ⟨u, (globalConductorResidueCharacter_reduction K χ u).symm⟩

theorem finite_globalIntegralComponent_range (χ : HeckeCharacter K) :
    (Set.range (globalIntegralComponent K χ)).Finite := by
  rw [globalIntegralComponent_range_eq]
  exact Set.finite_range _

theorem globalIntegralComponent_pow_card (χ : HeckeCharacter K) (u : GlobalIntegralUnits K) :
    globalIntegralComponent K χ u ^ Nat.card (GlobalConductorResidueUnits K χ) = 1 := by
  rw [← globalConductorResidueCharacter_reduction K χ u, ← map_pow, pow_card_eq_one', map_one]

theorem finiteOrder_globalIntegralComponent (χ : HeckeCharacter K) :
    FiniteOrder (globalIntegralComponent K χ) :=
  (finiteOrder_iff_pointwise _).mpr ⟨Nat.card (GlobalConductorResidueUnits K χ),
    Nat.card_pos, globalIntegralComponent_pow_card K χ⟩

theorem globalConductorReduction_ker_le (χ : HeckeCharacter K) :
    (globalConductorReduction K χ).ker ≤ (globalIntegralComponent K χ).toMonoidHom.ker := by
  intro u hu
  change globalIntegralComponent K χ u = 1
  rw [← globalConductorResidueCharacter_reduction K χ u,
    show globalConductorReduction K χ u = 1 from hu, map_one]

theorem globalIntegralComponent_eq_one_iff (χ : HeckeCharacter K) :
    globalIntegralComponent K χ = 1 ↔ ∀ v, UnramifiedAt K χ v := by
  constructor
  · intro h v
    apply (unramifiedAt_iff_localIntegralComponent_eq_one K v χ).mpr
    apply ContinuousMonoidHom.ext
    intro u
    have he := congrArg (fun f : UnitaryCharacter (GlobalIntegralUnits K) => f (Pi.mulSingle v u)) h
    simpa only [globalIntegralComponent_single, ContinuousMonoidHom.coe_one, Pi.one_apply] using he
  · intro h
    apply ContinuousMonoidHom.ext
    intro u
    rw [globalIntegralComponent_eq_prod]
    exact Finset.prod_eq_one fun v _ => h v _ (localIntegerUnitsEmbedding_norm K v (u v))

theorem globalIntegralComponent_mul_normTwist (χ : HeckeCharacter K) (t : ℝ) :
    globalIntegralComponent K (χ * heckeNormTwist K t) = globalIntegralComponent K χ := by
  have ht : globalIntegralComponent K (heckeNormTwist K t) = 1 :=
    (globalIntegralComponent_eq_one_iff K _).mpr (unramifiedAt_normTwist K t)
  apply ContinuousMonoidHom.ext
  intro u
  change globalIntegralComponent K χ u * globalIntegralComponent K (heckeNormTwist K t) u = _
  rw [ht]
  exact mul_one _

end HeckeGeneral.Characters
