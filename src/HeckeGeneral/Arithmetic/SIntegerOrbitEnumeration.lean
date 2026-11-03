import HeckeGeneral.Arithmetic.SIntegerLocalDiagonal

/-!
# Enumerate every actual nonzero S-integer by its orbit and a subgroup element

The map from an orbit and a global S-unit subgroup element is the literal
product of that unit with the chosen orbit representative. Nonzero elements
of a domain have free unit action, so this map is bijective. The construction
uses the actual valuation-defined S-integer ring and the existing transport
of global S-units to its units. It needs neither principalization nor finite
index, and it retains every element of the subgroup.

The local diagonal formula is pointwise. The final sum identity only
reindexes by an equivalence; no interchange of infinite sums is used.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup (S.unit K))

/-- Multiplication by the actual global S-unit, transported to the S-integer ring. -/
def sIntegerOrbitTranslate (u : Γ) (a : NonzeroRingElements (S.integer K)) :
    NonzeroRingElements (S.integer K) :=
  (S.unitEquivUnitsInteger K u.val) • a

@[simp] theorem sIntegerOrbitTranslate_val (u : Γ)
    (a : NonzeroRingElements (S.integer K)) :
    ((sIntegerOrbitTranslate K S Γ u a).val : K) =
      ((u.val : Kˣ) : K) * (a.val : K) := rfl

@[simp] theorem sIntegerOrbitTranslate_one (a : NonzeroRingElements (S.integer K)) :
    sIntegerOrbitTranslate K S Γ 1 a = a := by
  unfold sIntegerOrbitTranslate
  simp

theorem sIntegerOrbitTranslate_mul (u v : Γ)
    (a : NonzeroRingElements (S.integer K)) :
    sIntegerOrbitTranslate K S Γ (u * v) a =
      sIntegerOrbitTranslate K S Γ u (sIntegerOrbitTranslate K S Γ v a) := by
  unfold sIntegerOrbitTranslate
  rw [Subgroup.coe_mul, map_mul, mul_smul]

/-- Translation does not change the actual subgroup orbit. -/
@[simp] theorem sIntegerOrbitTranslate_quotient (u : Γ)
    (a : NonzeroRingElements (S.integer K)) :
    (Quotient.mk _ (sIntegerOrbitTranslate K S Γ u a) : SIntegerOrbits K S Γ) =
      Quotient.mk _ a := by
  apply Quotient.sound
  exact (sIntegerOrbitRelation_iff K S Γ _ a).mpr ⟨u, rfl⟩

/-- The explicit enumeration map, with no selected subgroup elements discarded. -/
def sIntegerOrbitEnumeration (p : SIntegerOrbits K S Γ × Γ) :
    NonzeroRingElements (S.integer K) :=
  sIntegerOrbitTranslate K S Γ p.2 p.1.out

@[simp] theorem sIntegerOrbitEnumeration_quotient (p : SIntegerOrbits K S Γ × Γ) :
    (Quotient.mk _ (sIntegerOrbitEnumeration K S Γ p) : SIntegerOrbits K S Γ) = p.1 := by
  rw [sIntegerOrbitEnumeration, sIntegerOrbitTranslate_quotient, Quotient.out_eq]

/-- The subgroup multiplier is unique because the representative is nonzero. -/
theorem sIntegerOrbitEnumeration_injective :
    Function.Injective (sIntegerOrbitEnumeration K S Γ) := by
  rintro ⟨q, u⟩ ⟨r, v⟩ huv
  have hq : q = r := by
    have h := congrArg (fun a : NonzeroRingElements (S.integer K) =>
      (Quotient.mk _ a : SIntegerOrbits K S Γ)) huv
    simpa only [sIntegerOrbitEnumeration_quotient] using h
  subst r
  have huv' : u = v := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    have h := congrArg (fun a : NonzeroRingElements (S.integer K) => (a.val : K)) huv
    change ((u.val : Kˣ) : K) * (q.out.val : K) =
      ((v.val : Kˣ) : K) * (q.out.val : K) at h
    exact mul_right_cancel₀ (nonzeroSIntegerFieldUnit K S q.out).ne_zero h
  exact congrArg (fun w : Γ => (q, w)) huv'

/-- The actual orbit relation supplies a subgroup element taking the selected
representative to any given nonzero S-integer. -/
theorem sIntegerOrbitEnumeration_surjective :
    Function.Surjective (sIntegerOrbitEnumeration K S Γ) := by
  intro a
  let q : SIntegerOrbits K S Γ := Quotient.mk _ a
  have hrel : MulAction.orbitRel (sIntegerUnitSubgroup K S Γ)
      (NonzeroRingElements (S.integer K)) a q.out :=
    Quotient.exact (Quotient.out_eq q).symm
  obtain ⟨u, hu⟩ := (sIntegerOrbitRelation_iff K S Γ a q.out).mp hrel
  refine ⟨(q, u), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hu

/-- The inverse map is literally `(q,u) ↦ u*q.out`. -/
def nonzeroSIntegerEquivOrbitProduct :
    NonzeroRingElements (S.integer K) ≃ SIntegerOrbits K S Γ × Γ :=
  (Equiv.ofBijective (sIntegerOrbitEnumeration K S Γ)
    ⟨sIntegerOrbitEnumeration_injective K S Γ,
      sIntegerOrbitEnumeration_surjective K S Γ⟩).symm

@[simp] theorem nonzeroSIntegerEquivOrbitProduct_symm_apply
    (q : SIntegerOrbits K S Γ) (u : Γ) :
    (nonzeroSIntegerEquivOrbitProduct K S Γ).symm (q, u) =
      sIntegerOrbitTranslate K S Γ u q.out := rfl

@[simp] theorem nonzeroSIntegerEquivOrbitProduct_fst
    (a : NonzeroRingElements (S.integer K)) :
    (nonzeroSIntegerEquivOrbitProduct K S Γ a).1 = Quotient.mk _ a := by
  have h := sIntegerOrbitEnumeration_quotient K S Γ
    (nonzeroSIntegerEquivOrbitProduct K S Γ a)
  have hinv : sIntegerOrbitEnumeration K S Γ
      (nonzeroSIntegerEquivOrbitProduct K S Γ a) = a :=
    (nonzeroSIntegerEquivOrbitProduct K S Γ).symm_apply_apply a
  rw [hinv] at h
  exact h.symm

/-- The actual field unit of a translated S-integer is the corresponding product. -/
theorem nonzeroSIntegerFieldUnit_translate (u : Γ)
    (a : NonzeroRingElements (S.integer K)) :
    nonzeroSIntegerFieldUnit K S (sIntegerOrbitTranslate K S Γ u a) =
      (u.val : Kˣ) * nonzeroSIntegerFieldUnit K S a := by
  apply Units.ext
  rfl

/-- The local diagonal intertwines literal translation with the existing
global S-unit diagonal, without any finiteness assumption on S. -/
theorem sLocalNonzeroIntegerDiagonal_translate (u : Γ)
    (a : NonzeroRingElements (S.integer K)) :
    sLocalNonzeroIntegerDiagonal K S (sIntegerOrbitTranslate K S Γ u a) =
      sLocalDiagonal K S u.val * sLocalNonzeroIntegerDiagonal K S a := by
  unfold sLocalNonzeroIntegerDiagonal
  rw [nonzeroSIntegerFieldUnit_translate, map_mul, sLocalFieldUnitDiagonal_sUnit]

@[simp] theorem sLocalNonzeroIntegerDiagonal_orbitProduct_symm
    (q : SIntegerOrbits K S Γ) (u : Γ) :
    sLocalNonzeroIntegerDiagonal K S
      ((nonzeroSIntegerEquivOrbitProduct K S Γ).symm (q, u)) =
      sLocalDiagonal K S u.val * sLocalNonzeroIntegerDiagonal K S q.out := by
  rw [nonzeroSIntegerEquivOrbitProduct_symm_apply, sLocalNonzeroIntegerDiagonal_translate]

/-- Reindexing by the actual orbit enumeration. This is a single product-indexed
sum; turning it into iterated sums still requires the appropriate summability. -/
theorem tsum_nonzeroSInteger_eq_tsum_orbitProduct
    (f : NonzeroRingElements (S.integer K) → ℂ) :
    (∑' a : NonzeroRingElements (S.integer K), f a) =
      ∑' p : SIntegerOrbits K S Γ × Γ,
        f (sIntegerOrbitTranslate K S Γ p.2 p.1.out) := by
  exact ((nonzeroSIntegerEquivOrbitProduct K S Γ).symm.tsum_eq f).symm

end HeckeGeneral.Arithmetic
