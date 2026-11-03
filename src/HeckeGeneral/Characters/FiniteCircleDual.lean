import HeckeGeneral.Characters.Packet
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! The full circle-valued dual of a finite commutative group, with orthogonality. -/

noncomputable section

namespace HeckeGeneral.Characters

open scoped Classical

variable (G : Type*) [CommGroup G] [Finite G]

def complexUnitCharacterToCircle (f : G →* ℂˣ) : G →* Circle where
  toFun x := ⟨(f x : ℂ), mem_sphere_zero_iff_norm.mpr
    (Complex.norm_eq_one_of_pow_eq_one (by
      have h : (f x) ^ Nat.card G = 1 := by rw [← map_pow, pow_card_eq_one', map_one]
      exact congrArg Units.val h) Nat.card_pos.ne')⟩
  map_one' := Circle.ext (by simp)
  map_mul' x y := Circle.ext (by change ((f (x * y) : ℂˣ) : ℂ) = (f x : ℂ) * (f y : ℂ); simp)

set_option linter.unusedSectionVars false in
@[simp] theorem complexUnitCharacterToCircle_coe (f : G →* ℂˣ) (x : G) :
    (complexUnitCharacterToCircle G f x : ℂ) = (f x : ℂ) := rfl

def finiteCircleDualEquivComplex : (G →* Circle) ≃* (G →* ℂˣ) where
  toFun f := Circle.toUnits.comp f
  invFun := complexUnitCharacterToCircle G
  left_inv f := by
    apply MonoidHom.ext
    intro x
    apply Circle.ext
    rfl
  right_inv f := by
    apply MonoidHom.ext
    intro x
    apply Units.ext
    rfl
  map_mul' f g := by
    apply MonoidHom.ext
    intro x
    apply Units.ext
    rfl

omit [CommGroup G] [Finite G] in
theorem complex_hasEnoughRootsOfUnity (n : ℕ) (hn : n ≠ 0) :
    HasEnoughRootsOfUnity ℂ n := by
  have : NeZero n := ⟨hn⟩
  exact ⟨⟨_, Complex.isPrimitiveRoot_exp n hn⟩, rootsOfUnity.isCyclic ℂ n⟩

/-- Noncanonical self-duality; the characters themselves have no chosen generators. -/
def finiteCircleDualSelfEquiv : (G →* Circle) ≃* G := by
  have : HasEnoughRootsOfUnity ℂ (Monoid.exponent G) :=
    complex_hasEnoughRootsOfUnity _ Monoid.exponent_ne_zero_of_finite
  exact (finiteCircleDualEquivComplex G).trans
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G ℂ).some

instance finite_circleDual : Finite (G →* Circle) :=
  Finite.of_equiv G (finiteCircleDualSelfEquiv G).symm.toEquiv

theorem natCard_circleDual : Nat.card (G →* Circle) = Nat.card G :=
  Nat.card_congr (finiteCircleDualSelfEquiv G).toEquiv

theorem circleDual_separates {x : G} (hx : x ≠ 1) : ∃ f : G →* Circle, f x ≠ 1 := by
  have : HasEnoughRootsOfUnity ℂ (Monoid.exponent G) :=
    complex_hasEnoughRootsOfUnity _ Monoid.exponent_ne_zero_of_finite
  obtain ⟨f, hf⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hx
  refine ⟨complexUnitCharacterToCircle G f, fun h => hf ?_⟩
  apply Units.ext
  exact congrArg (fun z : Circle => (z : ℂ)) h

theorem forall_circleDual_apply_eq_one_iff (x : G) :
    (∀ f : G →* Circle, f x = 1) ↔ x = 1 := by
  constructor
  · intro h
    by_contra hx
    obtain ⟨f, hf⟩ := circleDual_separates G hx
    exact hf (h f)
  · rintro rfl f
    exact map_one f

theorem forall_circleDual_apply_eq_iff (x y : G) :
    (∀ f : G →* Circle, f x = f y) ↔ x = y := by
  rw [← mul_inv_eq_one, ← forall_circleDual_apply_eq_one_iff G]
  simp only [map_mul, map_inv, mul_inv_eq_one]

omit [Finite G] in
theorem circleCharacter_pow_card (f : G →* Circle) (x : G) : f x ^ Nat.card G = 1 := by
  rw [← map_pow, pow_card_eq_one', map_one]

theorem circleCharacter_isOfFinOrder (f : G →* Circle) : IsOfFinOrder f := by
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨Nat.card G, Nat.card_pos, ?_⟩
  apply MonoidHom.ext
  intro x
  exact circleCharacter_pow_card G f x

theorem circleCharacter_extend (H : Subgroup G) (f : H →* Circle) :
    ∃ F : G →* Circle, F.domRestrict H = f := by
  have : HasEnoughRootsOfUnity ℂ (Monoid.exponent G) :=
    complex_hasEnoughRootsOfUnity _ Monoid.exponent_ne_zero_of_finite
  obtain ⟨F, hF⟩ := MonoidHom.domRestrict_surjective (M := ℂ) H (Circle.toUnits.comp f)
  refine ⟨complexUnitCharacterToCircle G F, ?_⟩
  apply MonoidHom.ext
  intro x
  apply Circle.ext
  exact congrArg (fun q : H →* ℂˣ => (q x : ℂ)) hF

section Sums

variable [Fintype G]

omit [Finite G] in
theorem sum_circleCharacter_eq_zero {f : G →* Circle} (hf : f ≠ 1) :
    (∑ x : G, (f x : ℂ)) = 0 := by
  obtain ⟨a, ha⟩ : ∃ a : G, f a ≠ 1 := by
    by_contra h
    exact hf (MonoidHom.ext fun x => by
      by_contra hx
      exact h ⟨x, hx⟩)
  apply eq_zero_of_mul_eq_self_left (Circle.coe_eq_one.not.mpr ha)
  simpa only [Finset.mul_sum, ← Circle.coe_mul, ← map_mul] using
    (Group.mulLeft_bijective a).sum_comp (fun x : G => (f x : ℂ))

omit [Finite G] in
theorem sum_circleCharacter (f : G →* Circle) :
    (∑ x : G, (f x : ℂ)) = if f = 1 then (Nat.card G : ℂ) else 0 := by
  by_cases hf : f = 1
  · subst f
    simp [Nat.card_eq_fintype_card]
  · simp only [ite_eq_right hf]
    exact sum_circleCharacter_eq_zero G hf

omit [Finite G] in
theorem sum_circleCharacter_mul_inv (f g : G →* Circle) :
    (∑ x : G, (f x : ℂ) * (g x : ℂ)⁻¹) = if f = g then (Nat.card G : ℂ) else 0 := by
  simpa only [MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv,
    mul_inv_eq_one] using sum_circleCharacter G (f * g⁻¹)

omit [Finite G] in
theorem sum_circleCharacter_mul_conj (f g : G →* Circle) :
    (∑ x : G, (f x : ℂ) * star (g x : ℂ)) = if f = g then (Nat.card G : ℂ) else 0 := by
  have hinv (x : G) : (g x : ℂ)⁻¹ = star (g x : ℂ) := Circle.coe_inv_eq_conj _
  simpa only [hinv] using sum_circleCharacter_mul_inv G f g

variable [Fintype (G →* Circle)]

omit [Fintype G] in
theorem sum_circleDual_eq_zero {x : G} (hx : x ≠ 1) :
    (∑ f : G →* Circle, (f x : ℂ)) = 0 := by
  let ev : (G →* Circle) →* Circle :=
    { toFun := fun f => f x
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hev : ev ≠ 1 := by
    obtain ⟨f, hf⟩ := circleDual_separates G hx
    intro he
    exact hf (congrArg (fun q : (G →* Circle) →* Circle => q f) he)
  exact sum_circleCharacter_eq_zero (G →* Circle) hev

end Sums

end HeckeGeneral.Characters
