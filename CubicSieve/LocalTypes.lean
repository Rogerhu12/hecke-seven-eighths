import HeckeGeneral.Characters.FiniteCircleDual
import DedekindZetaZeroFree.Arithmetic.LocalFields.PowerClassIndices
import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdditiveResidueQuotients

/-! A finite, explicitly constructed set of all cubic full local types at S. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.LocalTypes

open NumberField IsDedekindDomain
open DedekindZetaZeroFree DedekindZetaZeroFree.Detector
open HeckeGeneral.Characters
open scoped Classical NumberField

variable {K : Type} [Field K] [NumberField K]

abbrev three : ℕ+ := ⟨3, by decide⟩

abbrev LocalQuotient (A : SArithmeticData K) (v : {v // v ∈ A.Sf}) :=
  ClassFieldTheory.PowerClassGroup (v.val.adicCompletion K) three

instance localQuotientFinite (A : SArithmeticData K) (v : {v // v ∈ A.Sf}) :
    Finite (LocalQuotient A v) :=
  A.finite_power_class_finite three (Or.inr rfl) v.val v.property

abbrev LocalDual (A : SArithmeticData K) (v : {v // v ∈ A.Sf}) :=
  LocalQuotient A v →* ℂˣ

instance localDualFinite (A : SArithmeticData K) (v : {v // v ∈ A.Sf}) :
    Finite (LocalDual A v) :=
  Finite.of_equiv (LocalQuotient A v →* Circle)
    (finiteCircleDualEquivComplex (LocalQuotient A v)).toEquiv

abbrev TypeIndex (A : SArithmeticData K) := (v : {v // v ∈ A.Sf}) → LocalDual A v

def tuple (A : SArithmeticData K) (ρ : TypeIndex A) : FixedSResidue.FullLocalCharacters A :=
  (fun _ => 1, fun v => (ρ v).comp
    (ClassFieldTheory.powerClass (v.val.adicCompletion K) three))

def typeSet (A : SArithmeticData K) : Set (FixedSResidue.FullLocalCharacters A) :=
  Set.range (tuple A)

theorem typeSet_finite (A : SArithmeticData K) : (typeSet A).Finite :=
  Set.finite_range (tuple A)

theorem tuple_finiteOrder (A : SArithmeticData K) (ρ : TypeIndex A) :
    FixedSResidue.HasFiniteOrder A (tuple A ρ) := by
  refine ⟨3, by norm_num, ?_, ?_⟩
  · intro w x
    simp [tuple]
  · intro v x
    change ρ v (ClassFieldTheory.powerClass (v.val.adicCompletion K) three x) ^ 3 = 1
    rw [← map_pow, ← map_pow]
    have hx : ClassFieldTheory.powerClass (v.val.adicCompletion K) three (x ^ 3) = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      exact ⟨x, rfl⟩
    rw [hx, map_one]

theorem typeSet_finiteOrder (A : SArithmeticData K)
    {σ : FixedSResidue.FullLocalCharacters A} (hσ : σ ∈ typeSet A) :
    FixedSResidue.HasFiniteOrder A σ := by
  obtain ⟨ρ, rfl⟩ := hσ
  exact tuple_finiteOrder A ρ

def liftLocal (A : SArithmeticData K) (v : {v // v ∈ A.Sf})
    (δ : (v.val.adicCompletion K)ˣ →* ℂˣ) (hδ : ∀ x, δ x ^ 3 = 1) :
    LocalDual A v :=
  QuotientGroup.lift (powMonoidHom 3 : (v.val.adicCompletion K)ˣ →*
      (v.val.adicCompletion K)ˣ).range δ (by
    rintro x ⟨y, rfl⟩
    change δ (y ^ 3) = 1
    rw [map_pow, hδ])

@[simp] theorem liftLocal_apply (A : SArithmeticData K) (v : {v // v ∈ A.Sf})
    (δ : (v.val.adicCompletion K)ˣ →* ℂˣ) (hδ : ∀ x, δ x ^ 3 = 1)
    (x : (v.val.adicCompletion K)ˣ) :
    liftLocal A v δ hδ (ClassFieldTheory.powerClass (v.val.adicCompletion K) three x) =
      δ x := rfl

/-- Any actual continuous cubic local family lands in the fixed finite set.
The local components themselves, rather than an unproved finiteness statement,
are the inputs to this universal algebraic covering lemma. -/
theorem cover_of_cubic_local_components (A : SArithmeticData K)
    (ω : PrimitiveFrequencyCharacter K)
    (δ : (v : {v // v ∈ A.Sf}) → (v.val.adicCompletion K)ˣ →ₜ* ℂˣ)
    (hδ : ∀ v x, δ v x ^ 3 = 1)
    (hlocal : ∀ v, IsFrequencyLocalComponent K ω v.val (δ v)) :
    ∃ σ ∈ typeSet A, HasFixedFullSLocalTuple K A ω σ := by
  let ρ : TypeIndex A := fun v => liftLocal A v (δ v).toMonoidHom (hδ v)
  refine ⟨tuple A ρ, ⟨ρ, rfl⟩, ?_, ?_⟩
  · intro w
    rfl
  · intro v
    refine ⟨δ v, ?_, hlocal v⟩
    apply MonoidHom.ext
    intro x
    rfl

end CubicSieve.LocalTypes
