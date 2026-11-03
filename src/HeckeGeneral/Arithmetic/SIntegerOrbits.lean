import HeckeGeneral.Arithmetic.PrincipalUnitOrbits
import HeckeGeneral.Arithmetic.SIntegerPrincipalization
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Actual S-integer orbits and ideal sectors

The quotient of nonzero elements of a principal ideal domain by a subgroup
of its units is the disjoint union, over actual nonzero ideals, of the
subgroup orbits of their actual generators. Applying the genuine
`Set.unitEquivUnitsInteger` transports a subgroup of global S-units into
the unit group of the actual S-integer ring and preserves its index.
Consequently every nonzero ideal fiber retains exactly that index of
sectors. No orbit is silently replaced by one ideal.

Build and declaration-audit evidence is tracked in docs/NEXT_POISSON.md.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain
open scoped Classical

section Domain

variable (R : Type*) [CommRing R] [IsDomain R]

/-- Nonzero ring elements, rather than a choice of principal generators. -/
abbrev NonzeroRingElements := {a : R // a ≠ 0}

instance nonzeroRingElementsMulAction : MulAction Rˣ (NonzeroRingElements R) where
  smul u a := ⟨(u : R) * a.val, mul_ne_zero u.ne_zero a.property⟩
  one_smul a := Subtype.ext (one_mul a.val)
  mul_smul u v a := Subtype.ext (mul_assoc (u : R) (v : R) a.val)

@[simp]
theorem nonzeroRingElements_smul_val (u : Rˣ) (a : NonzeroRingElements R) :
    (u • a).val = (u : R) * a.val := rfl

/-- Actual nonzero ideals; this definition includes nonprincipal ideals. -/
abbrev NonzeroRingIdeals := {I : Ideal R // I ≠ 0}

instance nonzeroRingIdeals_neZero (I : NonzeroRingIdeals R) : NeZero I.val :=
  ⟨I.property⟩

def nonzeroElementIdeal (a : NonzeroRingElements R) : NonzeroRingIdeals R :=
  ⟨Ideal.span {a.val}, by
    intro h
    apply a.property
    apply Ideal.span_singleton_eq_bot.mp
    simpa only [Ideal.zero_eq_bot] using h⟩

@[simp]
theorem nonzeroElementIdeal_smul (u : Rˣ) (a : NonzeroRingElements R) :
    nonzeroElementIdeal R (u • a) = nonzeroElementIdeal R a := by
  apply Subtype.ext
  exact Ideal.span_singleton_mul_left_unit u.isUnit a.val

/-- The actual principal ideal of a full unit orbit. -/
def unitOrbitIdeal (q : MulAction.orbitRel.Quotient Rˣ (NonzeroRingElements R)) :
    NonzeroRingIdeals R :=
  Quotient.liftOn q (nonzeroElementIdeal R) fun a b h => by
    obtain ⟨u, hu⟩ := h
    rw [← hu, nonzeroElementIdeal_smul]

@[simp]
theorem unitOrbitIdeal_mk (a : NonzeroRingElements R) :
    unitOrbitIdeal R (Quotient.mk _ a) = nonzeroElementIdeal R a := rfl

theorem unitOrbitIdeal_injective : Function.Injective (unitOrbitIdeal R) := by
  intro q q'
  refine Quotient.inductionOn₂ q q' ?_
  intro a b hab
  apply Quotient.sound
  have hspan : Ideal.span {a.val} = Ideal.span {b.val} :=
    congrArg Subtype.val hab
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan.symm
  refine ⟨u, Subtype.ext ?_⟩
  change (u : R) * b.val = a.val
  simpa only [mul_comm] using hu

variable [IsPrincipalIdealRing R]

/-- Principalization supplies surjectivity onto all actual nonzero ideals. -/
theorem unitOrbitIdeal_surjective : Function.Surjective (unitOrbitIdeal R) := by
  intro I
  let a := chosenPrincipalGenerator I.val
  refine ⟨Quotient.mk _ ⟨a.val, principalGenerators_ne_zero I.val a⟩, ?_⟩
  exact Subtype.ext a.property

def unitOrbitsEquivNonzeroIdeals :
    MulAction.orbitRel.Quotient Rˣ (NonzeroRingElements R) ≃ NonzeroRingIdeals R :=
  Equiv.ofBijective (unitOrbitIdeal R)
    ⟨unitOrbitIdeal_injective R, unitOrbitIdeal_surjective R⟩

/-- A full unit orbit is exactly the torsor of generators of its ideal. -/
def unitOrbitEquivGenerators
    (q : MulAction.orbitRel.Quotient Rˣ (NonzeroRingElements R)) :
    q.orbit ≃ PrincipalGenerators (unitOrbitIdeal R q).val where
  toFun a := ⟨a.val.val, by
    have hq := (MulAction.orbitRel.Quotient.mem_orbit).mp a.property
    exact congrArg Subtype.val (congrArg (unitOrbitIdeal R) hq)⟩
  invFun a :=
    ⟨⟨a.val, principalGenerators_ne_zero (unitOrbitIdeal R q).val a⟩, by
      apply MulAction.orbitRel.Quotient.mem_orbit.mpr
      apply unitOrbitIdeal_injective R
      exact Subtype.ext a.property⟩
  left_inv a := Subtype.ext (Subtype.ext rfl)
  right_inv a := Subtype.ext rfl

omit [IsPrincipalIdealRing R] in
theorem unitOrbitEquivGenerators_smul
    (q : MulAction.orbitRel.Quotient Rˣ (NonzeroRingElements R))
    (u : Rˣ) (a : q.orbit) :
    unitOrbitEquivGenerators R q (u • a) = u • unitOrbitEquivGenerators R q a :=
  Subtype.ext rfl

/-- The generator identification respects the literal subgroup orbit relation. -/
def subgroupUnitOrbitEquivGeneratorOrbits (Γ : Subgroup Rˣ)
    (q : MulAction.orbitRel.Quotient Rˣ (NonzeroRingElements R)) :
    MulAction.orbitRel.Quotient Γ q.orbit ≃
      GeneratorOrbits Γ (unitOrbitIdeal R q).val :=
  Quotient.congr (unitOrbitEquivGenerators R q) fun a b => by
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨u, ?_⟩
      rw [← hu]
      exact (unitOrbitEquivGenerators_smul R q (u : Rˣ) b).symm
    · rintro ⟨u, hu⟩
      refine ⟨u, ?_⟩
      apply (unitOrbitEquivGenerators R q).injective
      exact (unitOrbitEquivGenerators_smul R q (u : Rˣ) b).trans hu

/-- The complete reindexing: subgroup element-orbits, with every ideal sector retained. -/
def nonzeroOrbitsEquivIdealSectors (Γ : Subgroup Rˣ) :
    MulAction.orbitRel.Quotient Γ (NonzeroRingElements R) ≃
      Σ I : NonzeroRingIdeals R, GeneratorOrbits Γ I.val :=
  (MulAction.equivSubgroupOrbits (NonzeroRingElements R) Γ).trans
    ((Equiv.sigmaCongrRight fun q =>
      subgroupUnitOrbitEquivGeneratorOrbits R Γ q).trans
      (Equiv.sigmaCongrLeft
        (β := fun I : NonzeroRingIdeals R => GeneratorOrbits Γ I.val)
        (unitOrbitsEquivNonzeroIdeals R)))

end Domain

section SIntegers

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The actual unit subgroup obtained from global S-units. -/
def sIntegerUnitSubgroup (Γ : Subgroup (S.unit K)) : Subgroup (S.integer K)ˣ :=
  Γ.map (S.unitEquivUnitsInteger K).toMonoidHom

theorem sIntegerUnitSubgroup_index (Γ : Subgroup (S.unit K)) :
    (sIntegerUnitSubgroup K S Γ).index = Γ.index :=
  Γ.index_map_equiv (S.unitEquivUnitsInteger K)

instance sIntegerUnitSubgroup_finiteIndex (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex] :
    (sIntegerUnitSubgroup K S Γ).FiniteIndex :=
  Subgroup.FiniteIndex.map_of_surjective Γ (S.unitEquivUnitsInteger K).surjective

/-- Orbits of actual nonzero S-integers under the transported global subgroup. -/
abbrev SIntegerOrbits (Γ : Subgroup (S.unit K)) :=
  MulAction.orbitRel.Quotient (sIntegerUnitSubgroup K S Γ)
    (NonzeroRingElements (S.integer K))

/-- This quotient is the literal global S-unit multiplication relation. -/
theorem sIntegerOrbitRelation_iff (Γ : Subgroup (S.unit K))
    (a b : NonzeroRingElements (S.integer K)) :
    MulAction.orbitRel (sIntegerUnitSubgroup K S Γ) (NonzeroRingElements (S.integer K)) a b ↔
      ∃ u : Γ, ((u.val : Kˣ) : K) * (b.val : K) = (a.val : K) := by
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨u, hu, hgu⟩ := g.property
    refine ⟨⟨u, hu⟩, ?_⟩
    have h := congrArg (fun x : NonzeroRingElements (S.integer K) => (x.val : K)) hg
    change (((g.val : (S.integer K)ˣ) : S.integer K) : K) *
      (b.val : K) = (a.val : K) at h
    rw [← hgu] at h
    exact h
  · rintro ⟨u, hu⟩
    let g : sIntegerUnitSubgroup K S Γ :=
      ⟨S.unitEquivUnitsInteger K u.val, ⟨u.val, u.property, rfl⟩⟩
    refine ⟨g, Subtype.ext (Subtype.ext ?_)⟩
    exact hu

variable [IsPrincipalIdealRing (S.integer K)]

/-- Actual S-integer orbits reindex by actual nonzero ideals and their sectors. -/
def sIntegerOrbitsEquivIdealSectors (Γ : Subgroup (S.unit K)) :
    SIntegerOrbits K S Γ ≃
      Σ I : NonzeroRingIdeals (S.integer K),
        GeneratorOrbits (sIntegerUnitSubgroup K S Γ) I.val :=
  nonzeroOrbitsEquivIdealSectors (S.integer K) (sIntegerUnitSubgroup K S Γ)

/-- Every ideal fiber has exactly the original global-subgroup index. -/
theorem card_sIntegerIdealSector (Γ : Subgroup (S.unit K))
    (I : NonzeroRingIdeals (S.integer K)) :
    Nat.card (GeneratorOrbits (sIntegerUnitSubgroup K S Γ) I.val) = Γ.index := by
  rw [card_generatorOrbits (sIntegerUnitSubgroup K S Γ) I.val
    (chosenPrincipalGenerator I.val)]
  exact sIntegerUnitSubgroup_index K S Γ

end SIntegers

end HeckeGeneral.Arithmetic
