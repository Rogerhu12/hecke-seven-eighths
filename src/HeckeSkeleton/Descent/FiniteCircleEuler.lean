import HeckeGeneral.Characters.FiniteCircleDual
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Data.Fintype.EquivFin

/-! The full finite Circle dual has the expected local Euler polynomial.
Restriction onto the generated cyclic subgroup supplies every root of unity
with its actual equal multiplicity. No Euler factor is divided out. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeSkeleton.Descent.FiniteCircleEuler

open HeckeGeneral.Characters
open scoped Classical BigOperators

variable (G : Type*) [CommGroup G] [Finite G]

def circleDualRestriction (H : Subgroup G) :
    (G →* Circle) →* (H →* Circle) := MonoidHom.domRestrictHom H Circle

theorem circleDualRestriction_surjective (H : Subgroup G) :
    Function.Surjective (circleDualRestriction G H) := by
  intro θ
  exact circleCharacter_extend G H θ

/-- Every restricted character has the same full-dual multiplicity. -/
theorem card_restrictionFiber (H : Subgroup G) (θ : H →* Circle) :
    Nat.card {ρ : G →* Circle // circleDualRestriction G H ρ = θ} =
      Nat.card G / Nat.card H := by
  let R := circleDualRestriction G H
  have hsurj : Function.Surjective R := circleDualRestriction_surjective G H
  have hcard : Nat.card (G →* Circle) =
      Nat.card (H →* Circle) * Nat.card R.ker := by
    calc
      Nat.card (G →* Circle) =
          Nat.card ((G →* Circle) ⧸ R.ker) * Nat.card R.ker :=
        R.ker.card_eq_card_quotient_mul_card_subgroup
      _ = Nat.card (H →* Circle) * Nat.card R.ker := by
        rw [Nat.card_congr
          (QuotientGroup.quotientKerEquivOfSurjective R hsurj).toEquiv]
  calc
    Nat.card {ρ : G →* Circle // R ρ = θ} = Nat.card R.ker :=
      Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hsurj θ)
    _ = Nat.card (G →* Circle) / Nat.card (H →* Circle) := by
      rw [hcard, Nat.mul_div_cancel_left _ Nat.card_pos]
    _ = Nat.card G / Nat.card H := by
      rw [natCard_circleDual G, natCard_circleDual H]

theorem card_cyclicRestrictionFiber (g : G) (θ : Subgroup.zpowers g →* Circle) :
    Nat.card {ρ : G →* Circle // circleDualRestriction G (Subgroup.zpowers g) ρ = θ} =
      Nat.card G / orderOf g := by
  rw [card_restrictionFiber G, Nat.card_zpowers]

def cyclicGenerator (g : G) : Subgroup.zpowers g := ⟨g, Subgroup.mem_zpowers g⟩

/-- Evaluation at the actual generator lands in the complete roots finset. -/
def cyclicDualEval (g : G) : (Subgroup.zpowers g →* Circle) →
    ↥(Polynomial.nthRootsFinset (orderOf g) (1 : ℂ)) := fun θ => by
  refine ⟨(θ (cyclicGenerator G g) : ℂ), ?_⟩
  apply (Polynomial.mem_nthRootsFinset (orderOf_pos g) (1 : ℂ)).mpr
  have hg : cyclicGenerator G g ^ orderOf g = 1 :=
    Subtype.ext (pow_orderOf_eq_one g)
  have hθ : θ (cyclicGenerator G g) ^ orderOf g = 1 := by
    rw [← map_pow, hg, map_one]
  simpa only [Circle.coe_pow, Circle.coe_one] using
    congrArg (fun u : Circle => (u : ℂ)) hθ

theorem cyclicDualEval_injective (g : G) :
    Function.Injective (cyclicDualEval G g) := by
  intro θ η h
  have hcomplex : (θ (cyclicGenerator G g) : ℂ) =
      (η (cyclicGenerator G g) : ℂ) :=
    congrArg (fun u : ↥(Polynomial.nthRootsFinset (orderOf g) (1 : ℂ)) =>
      (u : ℂ)) h
  have hv : θ (cyclicGenerator G g) = η (cyclicGenerator G g) :=
    Circle.ext hcomplex
  apply MonoidHom.ext
  intro x
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.property
  have hx : cyclicGenerator G g ^ k = x := Subtype.ext hk
  rw [← hx, map_zpow, map_zpow, hv]

/-- Equal cardinality turns generator evaluation into a bijection. -/
theorem cyclicDualEval_bijective (g : G) :
    Function.Bijective (cyclicDualEval G g) := by
  letI : Fintype (Subgroup.zpowers g →* Circle) := Fintype.ofFinite _
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨cyclicDualEval_injective G g, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    natCard_circleDual (Subgroup.zpowers g), Nat.card_zpowers, Nat.card_eq_finsetCard]
  exact (Complex.isPrimitiveRoot_exp (orderOf g) (orderOf_pos g).ne').card_nthRootsFinset.symm

/-- This polynomial identity also permits zero factors. -/
theorem prod_roots_one_sub_mul (n : ℕ) (hn : 0 < n) (z : ℂ) :
    (∏ ζ ∈ Polynomial.nthRootsFinset n (1 : ℂ), (1 - ζ * z)) = 1 - z ^ n := by
  have h := IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul (1 : ℂ) z hn
    (Complex.isPrimitiveRoot_exp n hn.ne')
  simpa only [one_pow] using h.symm

theorem prod_cyclicDual_one_sub_mul (g : G) (z : ℂ)
    [Fintype (Subgroup.zpowers g →* Circle)] :
    (∏ θ : Subgroup.zpowers g →* Circle,
      (1 - (θ (cyclicGenerator G g) : ℂ) * z)) = 1 - z ^ orderOf g := by
  let e := Equiv.ofBijective (cyclicDualEval G g) (cyclicDualEval_bijective G g)
  calc
    (∏ θ : Subgroup.zpowers g →* Circle,
        (1 - (θ (cyclicGenerator G g) : ℂ) * z)) =
        ∏ ζ : ↥(Polynomial.nthRootsFinset (orderOf g) (1 : ℂ)),
          (1 - (ζ : ℂ) * z) :=
      Fintype.prod_equiv e _ _ (fun _ => rfl)
    _ = ∏ ζ ∈ Polynomial.nthRootsFinset (orderOf g) (1 : ℂ), (1 - ζ * z) :=
      Finset.prod_coe_sort (Polynomial.nthRootsFinset (orderOf g) (1 : ℂ))
        (fun ζ : ℂ => 1 - ζ * z)
    _ = 1 - z ^ orderOf g := prod_roots_one_sub_mul _ (orderOf_pos g) z

/-- Restriction to the generated cyclic subgroup gives exact multiplicities. -/
theorem prod_fullDual_eq_pow_prod_cyclicDual (g : G) (z : ℂ)
    [Fintype (G →* Circle)] [Fintype (Subgroup.zpowers g →* Circle)] :
    (∏ ρ : G →* Circle, (1 - (ρ g : ℂ) * z)) =
      (∏ θ : Subgroup.zpowers g →* Circle,
        (1 - (θ (cyclicGenerator G g) : ℂ) * z)) ^ (Nat.card G / orderOf g) := by
  let R := circleDualRestriction G (Subgroup.zpowers g)
  let f : (Subgroup.zpowers g →* Circle) → ℂ :=
    fun θ => 1 - (θ (cyclicGenerator G g) : ℂ) * z
  have hprod : (∏ ρ : G →* Circle, f (R ρ)) =
      ∏ θ : Subgroup.zpowers g →* Circle, f θ ^ (Nat.card G / orderOf g) := by
    rw [← Fintype.prod_fiberwise' R f]
    apply Finset.prod_congr rfl
    intro θ _hθ
    have hc : Fintype.card {ρ : G →* Circle // R ρ = θ} =
        Nat.card G / orderOf g := by
      rw [← Nat.card_eq_fintype_card]
      exact card_cyclicRestrictionFiber G g θ
    simp only [Finset.prod_const, Finset.card_univ, hc]
  simpa only [R, f, circleDualRestriction, MonoidHom.domRestrictHom_apply,
    MonoidHom.domRestrict_apply, cyclicGenerator, Finset.prod_pow] using hprod

/-- Full finite Circle-dual local Euler identity. -/
theorem prod_fullCircleDual_one_sub_mul (g : G) (z : ℂ)
    [Fintype (G →* Circle)] :
    (∏ ρ : G →* Circle, (1 - (ρ g : ℂ) * z)) =
      (1 - z ^ orderOf g) ^ (Nat.card G / orderOf g) := by
  letI : Fintype (Subgroup.zpowers g →* Circle) := Fintype.ofFinite _
  rw [prod_fullDual_eq_pow_prod_cyclicDual G g z,
    prod_cyclicDual_one_sub_mul G g z]

end HeckeSkeleton.Descent.FiniteCircleEuler
