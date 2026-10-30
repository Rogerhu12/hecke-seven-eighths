import HeckeGeneral.Characters.SIntegerSexticSymbol

/-! Literal symbol covariance on actual S-integer
elements under the original subgroup. Shared-prime zeros remain present:
no coprimality or nonvanishing restriction is imposed. The R coefficient
below is only the displayed symbol product, not an identified reciprocity
correction. No full F, bad-place reciprocity, L_C or analytic correlation
identity is asserted. -/

noncomputable section
namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "N" => NonzeroRingElements (S.integer K)

/-- The actual raw coefficient, with the minus sign in the second
numerator retained literally, including its zero extension. -/
def sIntegerSexticRawCoefficient (n₁ n₂ k : N) : ℂ :=
  sIntegerSexticSymbol K S ζ hζ σ hS6 k.val n₁ *
    starRingEnd ℂ (sIntegerSexticSymbol K S ζ hζ σ hS6 (-k.val) n₂)

/-- A candidate arithmetic factor; no identification with a full
reciprocity correction is part of this definition or the covariance. -/
def sIntegerSexticRCandidate (n₁ n₂ : N) : ℂ :=
  sIntegerSexticSymbol K S ζ hζ σ hS6 n₁.val n₂ *
    starRingEnd ℂ (sIntegerSexticSymbol K S ζ hζ σ hS6 n₂.val n₁)

variable (Γ : Subgroup (S.unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 : S.unit K →* S.unit K).range)
include hΓ

/-- Independent literal numerator/denominator unit actions. The numerator
action uses the actual sixth-power range inclusion; denominator invariance
uses the actual unchanged principal ideal. -/
theorem sIntegerSexticSymbol_independent_unit_invariant
    (u v : Γ) (a : S.integer K) (c : N) :
    sIntegerSexticSymbol K S ζ hζ σ hS6
      ((S.unitEquivUnitsInteger K u.val).val * a)
      ((S.unitEquivUnitsInteger K v.val) • c) =
      sIntegerSexticSymbol K S ζ hζ σ hS6 a c := by
  rw [sIntegerSexticSymbol_denominator_invariant K S ζ hζ σ hS6]
  exact sIntegerSexticSymbol_numerator_invariant K S ζ hζ σ hS6 Γ hΓ u a c

/-- Actual covariance for (n₁,n₂,k) ↦ (u*n₁,v*n₂,(u*v)*k).
Both conjugation and the negative second numerator are kept. -/
theorem sIntegerSexticRawCoefficient_unit_covariance
    (u v : Γ) (n₁ n₂ k : N) :
    sIntegerSexticRawCoefficient K S ζ hζ σ hS6
      ((S.unitEquivUnitsInteger K u.val) • n₁)
      ((S.unitEquivUnitsInteger K v.val) • n₂)
      ((S.unitEquivUnitsInteger K (u * v).val) • k) =
      sIntegerSexticRawCoefficient K S ζ hζ σ hS6 n₁ n₂ k := by
  change
    sIntegerSexticSymbol K S ζ hζ σ hS6
        ((S.unitEquivUnitsInteger K (u * v).val).val * k.val)
        ((S.unitEquivUnitsInteger K u.val) • n₁) *
      starRingEnd ℂ (sIntegerSexticSymbol K S ζ hζ σ hS6
        (-((S.unitEquivUnitsInteger K (u * v).val).val * k.val))
        ((S.unitEquivUnitsInteger K v.val) • n₂)) = _
  rw [show -((S.unitEquivUnitsInteger K (u * v).val).val * k.val) =
      (S.unitEquivUnitsInteger K (u * v).val).val * (-k.val) by
        rw [mul_neg]]
  rw [sIntegerSexticSymbol_independent_unit_invariant K S ζ hζ σ hS6 Γ hΓ
      (u * v) u k.val n₁,
    sIntegerSexticSymbol_independent_unit_invariant K S ζ hζ σ hS6 Γ hΓ
      (u * v) v (-k.val) n₂]
  rfl

/-- The candidate R product is invariant under independent denominator
index actions, including cases where one or both symbol values vanish. -/
theorem sIntegerSexticRCandidate_unit_covariance
    (u v : Γ) (n₁ n₂ : N) :
    sIntegerSexticRCandidate K S ζ hζ σ hS6
      ((S.unitEquivUnitsInteger K u.val) • n₁)
      ((S.unitEquivUnitsInteger K v.val) • n₂) =
      sIntegerSexticRCandidate K S ζ hζ σ hS6 n₁ n₂ := by
  change
    sIntegerSexticSymbol K S ζ hζ σ hS6
        ((S.unitEquivUnitsInteger K u.val).val * n₁.val)
        ((S.unitEquivUnitsInteger K v.val) • n₂) *
      starRingEnd ℂ (sIntegerSexticSymbol K S ζ hζ σ hS6
        ((S.unitEquivUnitsInteger K v.val).val * n₂.val)
        ((S.unitEquivUnitsInteger K u.val) • n₁)) = _
  rw [sIntegerSexticSymbol_independent_unit_invariant K S ζ hζ σ hS6 Γ hΓ
      u v n₁.val n₂,
    sIntegerSexticSymbol_independent_unit_invariant K S ζ hζ σ hS6 Γ hΓ
      v u n₂.val n₁]
  rfl

/-- Covariance of the literal raw coefficient times the displayed R
candidate, without asserting that this product is the full coefficient. -/
theorem sIntegerSexticRaw_mul_RCandidate_unit_covariance
    (u v : Γ) (n₁ n₂ k : N) :
    sIntegerSexticRawCoefficient K S ζ hζ σ hS6
        ((S.unitEquivUnitsInteger K u.val) • n₁)
        ((S.unitEquivUnitsInteger K v.val) • n₂)
        ((S.unitEquivUnitsInteger K (u * v).val) • k) *
      sIntegerSexticRCandidate K S ζ hζ σ hS6
        ((S.unitEquivUnitsInteger K u.val) • n₁)
        ((S.unitEquivUnitsInteger K v.val) • n₂) =
      sIntegerSexticRawCoefficient K S ζ hζ σ hS6 n₁ n₂ k *
        sIntegerSexticRCandidate K S ζ hζ σ hS6 n₁ n₂ := by
  rw [sIntegerSexticRawCoefficient_unit_covariance K S ζ hζ σ hS6 Γ hΓ,
    sIntegerSexticRCandidate_unit_covariance K S ζ hζ σ hS6 Γ hΓ]

end HeckeGeneral.Characters
