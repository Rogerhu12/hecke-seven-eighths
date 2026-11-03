import ActualFixedSBoxDenominator
import HeckeGeneral.Arithmetic.SIntegerBalancedRepresentatives

/-!
UNCOMPILED candidate. A single unit of the original subgroup puts the
normalized divisor in the actual fixed compact local set and gives the
fixed D^H clearing data. The archimedean shape and finite valuation box
therefore refer to the same representative. This does not assert a
Schwartz seminorm bound under arbitrary unit precomposition.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic.ActualGramFixedDenominatorDraft

open NumberField IsDedekindDomain HeckeGeneral.Analysis
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "NZ" => NonzeroRingElements (S.integer K)
local notation "G" => sLocalMultiplicativeGroup K S
local notation "D" => finiteSIntegerDenominator K S
local notation "H" => finiteIndexSUnitBoxWidth K S Γ

/-- The actual S-local radial normalization, including the original
finite coordinates, which are unchanged by this normalization. -/
def normalizedDivisorLocalPoint (d : NZ) : G :=
  (sLocalNormSection K S (sIntegerElementNorm K S d))⁻¹ *
    sLocalNonzeroIntegerDiagonal K S d

theorem normalizedDivisorLocalPoint_norm (d : NZ) :
    sLocalProductNorm K S (normalizedDivisorLocalPoint K S d) = 1 := by
  unfold normalizedDivisorLocalPoint
  rw [sLocalProductNorm_mul, sLocalProductNorm_inv, sLocalProductNorm_section]
  change (sIntegerElementNorm K S d).val⁻¹ * (sIntegerElementNorm K S d).val = 1
  exact inv_mul_cancel₀ (sIntegerElementNorm K S d).property.ne'

@[simp] theorem normalizedDivisorLocalPoint_finite (d : NZ) :
    (normalizedDivisorLocalPoint K S d).2 = (sLocalNonzeroIntegerDiagonal K S d).2 := by
  change (1 : SFiniteLocalGroup K S)⁻¹ * (sLocalNonzeroIntegerDiagonal K S d).2 = _
  simp only [inv_one, one_mul]

theorem elementNorm_subgroup_translate (u : Γ) (d : NZ) :
    sIntegerElementNorm K S (sIntegerOrbitTranslate K S Γ u d) =
      sIntegerElementNorm K S d := by
  apply Subtype.ext
  change sLocalProductNorm K S
    (sLocalNonzeroIntegerDiagonal K S (sIntegerOrbitTranslate K S Γ u d)) = _
  rw [sLocalNonzeroIntegerDiagonal_translate]
  exact sLocalProductNorm_diagonal_mul K S (u : S.unit K) _

/-- The same subgroup action commutes with the positive norm section. -/
theorem normalizedDivisorLocalPoint_translate (u : Γ) (d : NZ) :
    normalizedDivisorLocalPoint K S (sIntegerOrbitTranslate K S Γ u d) =
      sLocalDiagonal K S (u : S.unit K) * normalizedDivisorLocalPoint K S d := by
  unfold normalizedDivisorLocalPoint
  rw [elementNorm_subgroup_translate, sLocalNonzeroIntegerDiagonal_translate]
  ac_rfl

/-- No shape or denominator hypothesis is supplied. One actual u in Gamma
gives both the fixed compact normalized shape and D^H for the divisor and
every quotient whose original product is active. -/
theorem exists_compact_divisor_with_fixed_denominator (d : NZ) :
    ∃ u : Γ, let d' := sIntegerOrbitTranslate K S Γ u d
      normalizedDivisorLocalPoint K S d' ∈ sUnitCompactRepresentativeSet K S Γ ∧
      (sLocalNonzeroIntegerDiagonal K S d').2 ∈ finiteLocalValuationBox K S H ∧
      (∃ z : 𝓞 K, algebraMap (𝓞 K) (S.integer K) (D ^ H) * d'.val =
        algebraMap (𝓞 K) (S.integer K) z) ∧
      ∀ m : NZ,
        (sLocalNonzeroIntegerDiagonal K S (sIntegerNonzeroMul K S d' m)).2 ∈
          finiteLocalValuationBox K S H →
        ∃ z : 𝓞 K, algebraMap (𝓞 K) (S.integer K) (D ^ H) * m.val =
          algebraMap (𝓞 K) (S.integer K) z := by
  obtain ⟨u, hu⟩ := exists_subgroup_mem_sUnitCompactRepresentativeSet K S Γ
    (normalizedDivisorLocalPoint K S d) (normalizedDivisorLocalPoint_norm K S d)
  let d' := sIntegerOrbitTranslate K S Γ u d
  have hcompact : normalizedDivisorLocalPoint K S d' ∈
      sUnitCompactRepresentativeSet K S Γ := by
    rw [normalizedDivisorLocalPoint_translate]
    exact hu
  have hbox : (sLocalNonzeroIntegerDiagonal K S d').2 ∈
      finiteLocalValuationBox K S H := by
    obtain ⟨p, hp⟩ := hcompact
    have hfinite : (sLocalNonzeroIntegerDiagonal K S d').2 = p.2.val := by
      rw [← normalizedDivisorLocalPoint_finite K S d', ← hp]
      rfl
    rw [hfinite]
    exact p.2.property
  exact ⟨u, hcompact, hbox,
    exactSDenominator_pow_clears_active K S H d' hbox,
    fun m hm => exactSDenominator_pow_clears_divisor_quotient K S H d' m hbox hm⟩

end HeckeGeneral.Arithmetic.ActualGramFixedDenominatorDraft
