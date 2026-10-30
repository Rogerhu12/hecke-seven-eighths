import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Exact unit-sector multiplicity of principal generators

For a nonzero principal ideal, its actual generators are a torsor under the
unit group. Quotienting those generators by a subgroup `Γ` therefore leaves
exactly `[Rˣ : Γ]` sectors. The ring is an arbitrary domain: no assumption
that every ideal is principal is made. Nonprincipal ideals have empty fibers.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open scoped Classical

variable {R : Type*} [CommRing R]

abbrev PrincipalGenerators (I : Ideal R) := {a : R // Ideal.span {a} = I}

instance principalGeneratorsMulAction (I : Ideal R) : MulAction Rˣ (PrincipalGenerators I) where
  smul u a := ⟨(u : R) * a.val, by
    rw [Ideal.span_singleton_mul_left_unit u.isUnit, a.property]⟩
  one_smul a := Subtype.ext (one_mul a.val)
  mul_smul u v a := Subtype.ext (mul_assoc (u : R) (v : R) a.val)

@[simp] theorem principalGenerators_smul_val (I : Ideal R) (u : Rˣ) (a : PrincipalGenerators I) :
    (u • a).val = (u : R) * a.val := rfl

variable [IsDomain R]

instance principalGeneratorsPretransitive (I : Ideal R) :
    MulAction.IsPretransitive Rˣ (PrincipalGenerators I) where
  exists_smul_eq a b := by
    have h : Associated a.val b.val :=
      Ideal.span_singleton_eq_span_singleton.mp (a.property.trans b.property.symm)
    obtain ⟨u, hu⟩ := h
    exact ⟨u, Subtype.ext (by simpa [mul_comm] using hu)⟩

omit [IsDomain R] in
theorem principalGenerators_ne_zero (I : Ideal R) [NeZero I] (a : PrincipalGenerators I) :
    a.val ≠ 0 := by
  intro ha
  have h := a.property
  rw [ha, Ideal.span_singleton_eq_bot.mpr rfl] at h
  exact (NeZero.ne I) h.symm

instance principalGeneratorsCancel (I : Ideal R) [NeZero I] :
    IsCancelSMul Rˣ (PrincipalGenerators I) where
  right_cancel' u v a h := by
    apply Units.ext
    apply mul_right_cancel₀ (principalGenerators_ne_zero I a)
    exact congrArg Subtype.val h

def GeneratorOrbits (Γ : Subgroup Rˣ) (I : Ideal R) :=
  MulAction.orbitRel.Quotient Γ (PrincipalGenerators I)

instance finite_generatorOrbits (Γ : Subgroup Rˣ) [Γ.FiniteIndex] (I : Ideal R) :
    Finite (GeneratorOrbits Γ I) := by
  unfold GeneratorOrbits
  infer_instance

def generatorOrbitsEquivUnits (Γ : Subgroup Rˣ) (I : Ideal R) [NeZero I]
    (a : PrincipalGenerators I) : GeneratorOrbits Γ I ≃ Rˣ ⧸ Γ :=
  MulAction.equivSubgroupOrbitsQuotientGroup a Γ

/-- Each nonempty nonzero ideal fiber contributes the full unit-sector index. -/
theorem card_generatorOrbits (Γ : Subgroup Rˣ) (I : Ideal R) [NeZero I]
    (a : PrincipalGenerators I) : Nat.card (GeneratorOrbits Γ I) = Γ.index := by
  rw [Nat.card_congr (generatorOrbitsEquivUnits Γ I a), Subgroup.index_eq_card]

def chosenPrincipalGenerator (I : Ideal R) [I.IsPrincipal] : PrincipalGenerators I :=
  ⟨Submodule.IsPrincipal.generator I, Submodule.IsPrincipal.span_singleton_generator I⟩

omit [IsDomain R] in
theorem principalGenerators_nonempty_iff (I : Ideal R) :
    Nonempty (PrincipalGenerators I) ↔ I.IsPrincipal := by
  constructor
  · rintro ⟨⟨a, ha⟩⟩
    exact ⟨a, ha.symm⟩
  · intro h
    let := h
    exact ⟨chosenPrincipalGenerator I⟩

theorem isEmpty_principalGenerators_of_not_principal (I : Ideal R) (hI : ¬ I.IsPrincipal) :
    IsEmpty (PrincipalGenerators I) :=
  not_nonempty_iff.mp (hI ∘ (principalGenerators_nonempty_iff I).mp)

theorem isEmpty_generatorOrbits_of_not_principal (Γ : Subgroup Rˣ) (I : Ideal R)
    (hI : ¬ I.IsPrincipal) : IsEmpty (GeneratorOrbits Γ I) := by
  let := isEmpty_principalGenerators_of_not_principal I hI
  unfold GeneratorOrbits
  infer_instance

/-- A principal-ideal assumption is tested on the individual ideal, rather than on the ring. -/
theorem card_generatorOrbits_eq_indicator (Γ : Subgroup Rˣ) (I : Ideal R) [NeZero I] :
    Nat.card (GeneratorOrbits Γ I) = if I.IsPrincipal then Γ.index else 0 := by
  classical
  by_cases hI : I.IsPrincipal
  · let := hI
    rw [ite_eq_left hI]
    exact card_generatorOrbits Γ I (chosenPrincipalGenerator I)
  · let := isEmpty_generatorOrbits_of_not_principal Γ I hI
    simp [hI]

theorem card_generatorOrbits_le_index (Γ : Subgroup Rˣ) (I : Ideal R) [NeZero I] :
    Nat.card (GeneratorOrbits Γ I) ≤ Γ.index := by
  rw [card_generatorOrbits_eq_indicator]
  split_ifs <;> omega

end HeckeGeneral.Arithmetic
