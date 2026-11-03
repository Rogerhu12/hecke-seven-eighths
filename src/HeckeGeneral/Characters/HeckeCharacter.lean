import HeckeGeneral.Characters.Packet
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.FiniteAdeleRing
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Unitary Hecke characters of an actual number field

Characters are defined on Mathlib's idèle class group, with its quotient topology.
They are equivalent to continuous circle-valued characters on the idèle group that
are trivial on the image of `Kˣ`.  No L-function or nonvanishing assertion appears
in this definition.

The actual adelic norm and its value on principal idèles are also recorded.  Constructing
the continuous logarithmic norm on the quotient still requires multiplicativity and
continuity of this norm; those facts are not assumed here.

The conventional idelic modulus sends a prime uniformizer idèle to `q⁻¹`.  To match
ideal coefficients twisted by `q^(i*t)`, the intended logarithmic norm is
`-Real.log (idelicNorm x)`.  The local uniformizer formula and the corresponding
L-function vertical-shift identity remain separate obligations.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- All continuous unitary Hecke characters of the number field `K`. -/
abbrev HeckeCharacter := UnitaryCharacter (IdeleClassGroup (𝓞 K) K)

/-- The continuous quotient map from idèles to idèle classes. -/
def ideleClassMap : IdeleGroup (𝓞 K) K →ₜ* IdeleClassGroup (𝓞 K) K where
  toMonoidHom := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)
  continuous_toFun := QuotientGroup.continuous_mk

/-- View a Hecke character as a character on the idèle group. -/
def toIdeleCharacter (χ : HeckeCharacter K) : UnitaryCharacter (IdeleGroup (𝓞 K) K) :=
  pullback (ideleClassMap K) χ

/-- Triviality on the actual subgroup of principal idèles. -/
def TrivialOnPrincipal (ψ : UnitaryCharacter (IdeleGroup (𝓞 K) K)) : Prop :=
  ∀ u : Kˣ, ψ (IdeleGroup.unitEmbedding (𝓞 K) K u) = 1

@[simp] theorem ideleClassMap_principal (u : Kˣ) :
    ideleClassMap K (IdeleGroup.unitEmbedding (𝓞 K) K u) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨u, rfl⟩

theorem toIdeleCharacter_trivial (χ : HeckeCharacter K) :
    TrivialOnPrincipal K (toIdeleCharacter K χ) := by
  intro u
  change χ (ideleClassMap K (IdeleGroup.unitEmbedding (𝓞 K) K u)) = 1
  rw [ideleClassMap_principal, map_one]

theorem principal_le_ker (ψ : UnitaryCharacter (IdeleGroup (𝓞 K) K))
    (hψ : TrivialOnPrincipal K ψ) :
    IdeleGroup.principalSubgroup (𝓞 K) K ≤ ψ.toMonoidHom.ker := by
  rintro x ⟨u, rfl⟩
  exact hψ u

/-- Descend a continuous character trivial on principal idèles to the quotient. -/
def descendIdeleCharacter (ψ : UnitaryCharacter (IdeleGroup (𝓞 K) K))
    (hψ : TrivialOnPrincipal K ψ) : HeckeCharacter K where
  toMonoidHom := QuotientGroup.lift (IdeleGroup.principalSubgroup (𝓞 K) K)
    ψ.toMonoidHom (principal_le_ker K ψ hψ)
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk
      (IdeleGroup.principalSubgroup (𝓞 K) K)).continuous_iff.mpr
    exact ψ.continuous

@[simp] theorem descendIdeleCharacter_apply (ψ : UnitaryCharacter (IdeleGroup (𝓞 K) K))
    (hψ : TrivialOnPrincipal K ψ) (x : IdeleGroup (𝓞 K) K) :
    descendIdeleCharacter K ψ hψ (ideleClassMap K x) = ψ x := rfl

@[simp] theorem toIdeleCharacter_descend (ψ : UnitaryCharacter (IdeleGroup (𝓞 K) K))
    (hψ : TrivialOnPrincipal K ψ) :
    toIdeleCharacter K (descendIdeleCharacter K ψ hψ) = ψ := by
  ext x
  rfl

@[simp] theorem descend_toIdeleCharacter (χ : HeckeCharacter K) :
    descendIdeleCharacter K (toIdeleCharacter K χ) (toIdeleCharacter_trivial K χ) = χ := by
  ext x
  refine QuotientGroup.induction_on x fun y => ?_
  rfl

/-- The two standard definitions of continuous unitary Hecke characters agree. -/
def heckeCharacterEquivPrincipalTrivial :
    HeckeCharacter K ≃
      {ψ : UnitaryCharacter (IdeleGroup (𝓞 K) K) // TrivialOnPrincipal K ψ} where
  toFun χ := ⟨toIdeleCharacter K χ, toIdeleCharacter_trivial K χ⟩
  invFun ψ := descendIdeleCharacter K ψ.1 ψ.2
  left_inv := descend_toIdeleCharacter K
  right_inv ψ := by
    apply Subtype.ext
    exact toIdeleCharacter_descend K ψ.1 ψ.2

/-- The real idelic norm, including normalized infinite and finite local norms. -/
def idelicNorm (x : IdeleGroup (𝓞 K) K) : ℝ := ‖x.val.1‖ * ‖x.val.2‖

/-- The product formula makes the idelic norm trivial on principal idèles. -/
theorem idelicNorm_principal (u : Kˣ) :
    idelicNorm K (IdeleGroup.unitEmbedding (𝓞 K) K u) = 1 := by
  change ‖algebraMap K (InfiniteAdeleRing K) (u : K)‖ *
    ‖algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (u : K)‖ = 1
  rw [InfiniteAdeleRing.coe_norm_eq_abs_norm,
    FiniteAdeleRing.coe_norm_eq_inv_abs_norm u.ne_zero]
  have hnorm : Algebra.norm ℚ (u : K) ≠ 0 := Algebra.norm_ne_zero_iff.mpr u.ne_zero
  exact_mod_cast (mul_inv_cancel₀ (abs_ne_zero.mpr hnorm))

end HeckeGeneral.Characters
