import HeckeGeneral.Characters.LocalResidueFinite
import HeckeGeneral.Characters.ConductorArithmetic

/-! Descent of actual local components to the finite residue unit groups. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

def localIntegerUnitsEmbedding (v : HeightOneSpectrum (𝓞 K)) :
    (LocalIntegerRing K v)ˣ →ₜ* (v.adicCompletion K)ˣ where
  toMonoidHom := Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom
  continuous_toFun := Units.continuous_map continuous_subtype_val

theorem localIntegerUnitsEmbedding_mem (v : HeightOneSpectrum (𝓞 K))
    (u : (LocalIntegerRing K v)ˣ) :
    localIntegerUnitsEmbedding K v u ∈ (v.adicCompletionIntegers K).units :=
  ⟨u.val.property, u.inv.property⟩

theorem localIntegerUnitsEmbedding_norm (v : HeightOneSpectrum (𝓞 K))
    (u : (LocalIntegerRing K v)ˣ) : ‖(localIntegerUnitsEmbedding K v u).val‖ = 1 :=
  (local_norm_one_iff_integral_unit K v _).mpr (localIntegerUnitsEmbedding_mem K v u)

def integerUnitOfLocalUnit (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) (hu : u ∈ (v.adicCompletionIntegers K).units) :
    (LocalIntegerRing K v)ˣ where
  val := ⟨u.val, hu.1⟩
  inv := ⟨u.inv, hu.2⟩
  val_inv := Subtype.ext u.val_inv
  inv_val := Subtype.ext u.inv_val

@[simp] theorem localIntegerUnitsEmbedding_integerUnitOfLocalUnit
    (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ)
    (hu : u ∈ (v.adicCompletionIntegers K).units) :
    localIntegerUnitsEmbedding K v (integerUnitOfLocalUnit K v u hu) = u := by
  apply Units.ext
  rfl

/-- The actual local component restricted to the local integer unit group. -/
def localIntegralComponent (v : HeightOneSpectrum (𝓞 K)) (χ : HeckeCharacter K) :
    UnitaryCharacter (LocalIntegerRing K v)ˣ :=
  (localComponent K v χ).comp (localIntegerUnitsEmbedding K v)

@[simp] theorem localIntegralComponent_apply (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) (u : (LocalIntegerRing K v)ˣ) :
    localIntegralComponent K v χ u = localComponent K v χ (localIntegerUnitsEmbedding K v u) := rfl

theorem unramifiedAt_iff_localIntegralComponent_eq_one (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) : UnramifiedAt K χ v ↔ localIntegralComponent K v χ = 1 := by
  constructor
  · intro h
    apply ContinuousMonoidHom.ext
    intro u
    exact h _ (localIntegerUnitsEmbedding_norm K v u)
  · intro h u hu
    let w := integerUnitOfLocalUnit K v u ((local_norm_one_iff_integral_unit K v u).mp hu)
    have hw := congrArg (fun f : UnitaryCharacter (LocalIntegerRing K v)ˣ => f w) h
    simpa [localIntegralComponent_apply, w] using hw

theorem trivialAtDepth_iff_principalUnits_le_ker (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) (n : ℕ) :
    TrivialAtDepth K χ v n ↔
      principalUnits K v n ≤ (localIntegralComponent K v χ).toMonoidHom.ker := by
  cases n with
  | zero =>
    rw [principalUnits_zero]
    constructor
    · intro h u _
      exact h _ (localIntegerUnitsEmbedding_norm K v u)
    · intro h
      apply (unramifiedAt_iff_localIntegralComponent_eq_one K v χ).mpr
      apply ContinuousMonoidHom.ext
      intro u
      exact h (show u ∈ (⊤ : Subgroup (LocalIntegerRing K v)ˣ) from trivial)
  | succ n =>
    constructor
    · intro h u hu
      exact h (localIntegerUnitsEmbedding K v u) ((mem_principalUnits_iff_norm K v _ u).mp hu)
    · intro h u hu
      have hint := principalUnit_mem_integral_units K v u (n + 1) (Nat.succ_pos n) hu
      let w := integerUnitOfLocalUnit K v u hint
      have hw : w ∈ principalUnits K v (n + 1) :=
        (mem_principalUnits_iff_norm K v _ w).mpr hu
      have he := h hw
      change localIntegralComponent K v χ w = 1 at he
      simpa [localIntegralComponent_apply, w] using he

theorem conductor_principalUnits_le_ker (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) :
    principalUnits K v (localConductorExponent K χ v) ≤
      (localIntegralComponent K v χ).toMonoidHom.ker :=
  (trivialAtDepth_iff_principalUnits_le_ker K v χ _).mp
    (trivialAtDepth_localConductorExponent K χ v)

/-- Descent at any proved depth bound; the bound is a theorem about this actual character. -/
def localResidueCharacter (v : HeightOneSpectrum (𝓞 K)) (χ : HeckeCharacter K)
    (n : ℕ) (hn : localConductorExponent K χ v ≤ n) : (LocalResidueRing K v n)ˣ →* Circle :=
  (localUnitReduction K v n).liftOfSurjective (localUnitReduction_surjective K v n)
    ⟨(localIntegralComponent K v χ).toMonoidHom,
      (trivialAtDepth_iff_principalUnits_le_ker K v χ n).mp
        ((localConductorExponent_le_iff K χ v n).mp hn)⟩

@[simp] theorem localResidueCharacter_reduction (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) (n : ℕ) (hn : localConductorExponent K χ v ≤ n)
    (u : (LocalIntegerRing K v)ˣ) :
    localResidueCharacter K v χ n hn (localUnitReduction K v n u) =
      localIntegralComponent K v χ u :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem localResidueCharacter_unique (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) (n : ℕ) (hn : localConductorExponent K χ v ≤ n)
    (ψ : (LocalResidueRing K v n)ˣ →* Circle)
    (hψ : ψ.comp (localUnitReduction K v n) = (localIntegralComponent K v χ).toMonoidHom) :
    ψ = localResidueCharacter K v χ n hn := by
  apply MonoidHom.ext
  intro y
  obtain ⟨u, rfl⟩ := localUnitReduction_surjective K v n y
  rw [localResidueCharacter_reduction]
  exact congrArg (fun f : (LocalIntegerRing K v)ˣ →* Circle => f u) hψ

/-- The canonical finite residue character at the least actual conductor depth. -/
def conductorResidueCharacter (v : HeightOneSpectrum (𝓞 K)) (χ : HeckeCharacter K) :
    (LocalResidueRing K v (localConductorExponent K χ v))ˣ →* Circle :=
  localResidueCharacter K v χ _ le_rfl

@[simp] theorem conductorResidueCharacter_reduction (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) (u : (LocalIntegerRing K v)ˣ) :
    conductorResidueCharacter K v χ (localUnitReduction K v (localConductorExponent K χ v) u) =
      localIntegralComponent K v χ u := localResidueCharacter_reduction K v χ _ le_rfl u

theorem localIntegralComponent_range_eq (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) :
    Set.range (localIntegralComponent K v χ) = Set.range (conductorResidueCharacter K v χ) := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨localUnitReduction K v _ u, conductorResidueCharacter_reduction K v χ u⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨u, rfl⟩ := localUnitReduction_surjective K v (localConductorExponent K χ v) y
    exact ⟨u, (conductorResidueCharacter_reduction K v χ u).symm⟩

theorem finite_localIntegralComponent_range (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) : (Set.range (localIntegralComponent K v χ)).Finite := by
  rw [localIntegralComponent_range_eq]
  exact Set.finite_range _

theorem localIntegralComponent_pow_card (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) (u : (LocalIntegerRing K v)ˣ) :
    localIntegralComponent K v χ u ^
      Nat.card (LocalResidueRing K v (localConductorExponent K χ v))ˣ = 1 := by
  rw [← conductorResidueCharacter_reduction K v χ u, ← map_pow, pow_card_eq_one', map_one]

theorem finiteOrder_localIntegralComponent (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) : FiniteOrder (localIntegralComponent K v χ) := by
  apply (finiteOrder_iff_pointwise _).mpr
  exact ⟨Nat.card (LocalResidueRing K v (localConductorExponent K χ v))ˣ,
    Nat.card_pos, localIntegralComponent_pow_card K v χ⟩

end HeckeGeneral.Characters
