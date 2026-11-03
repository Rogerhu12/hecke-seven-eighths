import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# A sextic power-residue character with a specified root normalization

Both primitive roots are inputs. The character first takes the actual
power residue in the finite field and then sends the chosen finite-field
root to the chosen complex root. No choice of an unrelated character is
made. This module does not identify number-field residue characters or
prove a reciprocity law.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic.FiniteFieldSexticCharacter

open scoped Classical

variable (F : Type*) [Field F] [Fintype F]
variable (h6 : 6 ∣ Fintype.card F - 1)
variable (ζF : Fˣ) (ζC : ℂˣ)
variable (hF : IsPrimitiveRoot ζF 6) (hC : IsPrimitiveRoot ζC 6)

variable {F} in
/-- The specified matching of sixth roots, obtained from their exponents
in `ZMod 6`. In particular its orientation is ζF ↦ ζC. -/
def rootPair : Subgroup.zpowers ζF ≃* Subgroup.zpowers ζC :=
  (AddEquiv.toMultiplicativeLeft hF.zmodEquivZPowers).symm.trans
    (AddEquiv.toMultiplicativeLeft hC.zmodEquivZPowers)

theorem rootPair_pow (i : ℕ) :
    rootPair ζF ζC hF hC (⟨ζF ^ i, i, by simp⟩ : Subgroup.zpowers ζF) =
      (⟨ζC ^ i, i, by simp⟩ : Subgroup.zpowers ζC) := by
  change hC.zmodEquivZPowers
      (hF.zmodEquivZPowers.symm (Additive.ofMul ⟨ζF ^ i, i, by simp⟩)) =
    Additive.ofMul ⟨ζC ^ i, i, by simp⟩
  rw [hF.zmodEquivZPowers_symm_apply_pow, hC.zmodEquivZPowers_apply_coe_nat]

def residueExponent : ℕ := (Fintype.card F - 1) / 6

include h6 in
theorem residueExponent_mul_six : residueExponent F * 6 = Fintype.card F - 1 :=
  Nat.div_mul_cancel h6

/-- The power-residue map, before matching the complex root. -/
def powerResidueHom : Fˣ →* Subgroup.zpowers ζF where
  toFun u := ⟨u ^ residueExponent F, by
    rw [hF.zpowers_eq]
    apply (mem_rootsOfUnity 6 _).mpr
    rw [← pow_mul, residueExponent_mul_six F h6]
    apply Units.ext
    exact FiniteField.pow_card_sub_one_eq_one (u : F) u.ne_zero⟩
  map_one' := by ext; simp
  map_mul' u v := by ext; simp [mul_pow]

/-- The normalized unit character followed by zero extension. -/
def unitCharacter : Fˣ →* ℂˣ :=
  (Subgroup.subtype (Subgroup.zpowers ζC)).comp
    ((rootPair ζF ζC hF hC).toMonoidHom.comp (powerResidueHom F h6 ζF hF))

def character : MulChar F ℂ :=
  MulChar.ofUnitHom (unitCharacter F h6 ζF ζC hF hC)

@[simp] theorem character_zero : character F h6 ζF ζC hF hC 0 = 0 := by
  exact MulChar.map_nonunit _ (by simp)

@[simp] theorem character_unit (u : Fˣ) :
    character F h6 ζF ζC hF hC (u : F) =
      (unitCharacter F h6 ζF ζC hF hC u : ℂ) :=
  MulChar.ofUnitHom_coe _ _

/-- This is the defining power-residue normalization, including the chosen
identification of the two sets of roots. -/
theorem character_power_residue (u : Fˣ) :
    character F h6 ζF ζC hF hC (u : F) =
      (((rootPair ζF ζC hF hC) (powerResidueHom F h6 ζF hF u) :
        Subgroup.zpowers ζC) : ℂˣ) := by
  rw [character_unit]
  rfl

theorem unitCharacter_pow_six (u : Fˣ) :
    unitCharacter F h6 ζF ζC hF hC u ^ 6 = 1 := by
  have hm : unitCharacter F h6 ζF ζC hF hC u ∈ Subgroup.zpowers ζC :=
    (rootPair ζF ζC hF hC (powerResidueHom F h6 ζF hF u)).property
  rw [hC.zpowers_eq] at hm
  exact (mem_rootsOfUnity 6 _).mp hm

theorem coe_unitCharacter_pow_six (u : Fˣ) :
    (unitCharacter F h6 ζF ζC hF hC u : ℂ) ^ 6 = 1 := by
  exact congrArg (fun z : ℂˣ => (z : ℂ))
    (unitCharacter_pow_six F h6 ζF ζC hF hC u)

theorem character_unit_norm (u : Fˣ) :
    ‖character F h6 ζF ζC hF hC (u : F)‖ = 1 := by
  rw [character_unit]
  apply Complex.norm_eq_one_of_pow_eq_one
    (n := 6) (coe_unitCharacter_pow_six F h6 ζF ζC hF hC u)
    (by decide)

theorem character_sixth_power (u : Fˣ) :
    character F h6 ζF ζC hF hC ((u : F) ^ 6) = 1 := by
  rw [map_pow, character_unit]
  exact coe_unitCharacter_pow_six F h6 ζF ζC hF hC u

theorem character_sixth_power_of_ne_zero (x : F) (hx : x ≠ 0) :
    character F h6 ζF ζC hF hC (x ^ 6) = 1 := by
  exact character_sixth_power F h6 ζF ζC hF hC (Units.mk0 x hx)

/-- Sixth-power unit invariance holds also at zero and at every nonunit
argument of the zero-extended character. -/
theorem character_mul_sixth_power (u : Fˣ) (x : F) :
    character F h6 ζF ζC hF hC ((u : F) ^ 6 * x) =
      character F h6 ζF ζC hF hC x := by
  rw [map_mul, character_sixth_power, one_mul]

theorem character_pow_six : character F h6 ζF ζC hF hC ^ 6 = 1 := by
  apply MulChar.ext
  intro u
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, character_unit]
  exact coe_unitCharacter_pow_six F h6 ζF ζC hF hC u

/-- A generator of the actual finite-field unit group has a power residue
of exact order six. This also proves nontriviality without selecting an
arbitrary sixth-order character. -/
theorem exists_unitCharacter_order_six :
    ∃ u : Fˣ, orderOf (unitCharacter F h6 ζF ζC hF hC u) = 6 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hgorder : orderOf g = Fintype.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      Fintype.card_units]
  have hgpos : orderOf g ≠ 0 := by
    rw [hgorder]
    have : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  have hdiv : 6 ∣ orderOf g := by rwa [hgorder]
  have hp : orderOf (g ^ residueExponent F) = 6 := by
    simpa [residueExponent, hgorder] using orderOf_pow_orderOf_div hgpos hdiv
  refine ⟨g, ?_⟩
  have hfirst := orderOf_injective (Subgroup.zpowers ζF).subtype
    Subtype.coe_injective (powerResidueHom F h6 ζF hF g)
  have hpair := orderOf_injective (rootPair ζF ζC hF hC).toMonoidHom
    (rootPair ζF ζC hF hC).injective (powerResidueHom F h6 ζF hF g)
  have hlast := orderOf_injective (Subgroup.zpowers ζC).subtype
    Subtype.coe_injective (rootPair ζF ζC hF hC (powerResidueHom F h6 ζF hF g))
  exact hlast.trans (hpair.trans (hfirst.symm.trans hp))

theorem character_isPrimitiveRoot :
    IsPrimitiveRoot (character F h6 ζF ζC hF hC) 6 := by
  refine ⟨character_pow_six F h6 ζF ζC hF hC, ?_⟩
  intro n hn
  obtain ⟨u, hu⟩ := exists_unitCharacter_order_six F h6 ζF ζC hF hC
  have he := congrArg (fun χ : MulChar F ℂ => χ (u : F)) hn
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, character_unit] at he
  have he' : unitCharacter F h6 ζF ζC hF hC u ^ n = 1 := by
    apply Units.ext
    exact he
  rw [← hu]
  exact orderOf_dvd_of_pow_eq_one he'

theorem character_order : orderOf (character F h6 ζF ζC hF hC) = 6 :=
  (character_isPrimitiveRoot F h6 ζF ζC hF hC).eq_orderOf.symm

theorem character_ne_one : character F h6 ζF ζC hF hC ≠ 1 :=
  (character_isPrimitiveRoot F h6 ζF ζC hF hC).ne_one (by decide)

end HeckeGeneral.Arithmetic.FiniteFieldSexticCharacter
