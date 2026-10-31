import SIntegerPrincipalUnitCongruence
import ActualFinitePlaceCompletionComparison
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
import ValuedFieldTheory.Valuation.LocalRingEquiv

/-! SOURCE ONLY, UNRUN. The first import names the intended integration of
SIntegerPrincipalUnitCongruence.lean. Both integer-ring models are subtypes
of the same actual adic completion; their predicates agree by compatibility
of the canonical valuation relation. No congruence transport is assumed. -/
noncomputable section
namespace HeckeGeneral.Arithmetic
open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped ValuativeRel
variable (K : Type) [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))
local instance principalUnitCongruence_adicValuativeRel : ValuativeRel (v.adicCompletion K) :=
  ActualFiniteCompletionDraft.adicCompletionValuativeRel K v

/-- Equality of the integer predicates, rather than equality of the two
value groups (which have different types). -/
theorem adicCompletion_upstream_integer_iff (x : v.adicCompletion K) :
    x ∈ (ValuativeRel.valuation (v.adicCompletion K)).integer ↔
      x ∈ v.adicCompletionIntegers K := by
  rw [Valuation.mem_integer_iff]
  rw [← map_one (ValuativeRel.valuation (v.adicCompletion K))]
  rw [← Valuation.Compatible.vle_iff_le]
  change Valued.v x ≤ Valued.v 1 ↔ Valued.v x ≤ 1
  rw [map_one]

/-- Identity on field elements identifies the two actual integer rings. -/
def adicCompletionIntegerRingEquiv :
    LocalIntegerRing K v ≃+* 𝒪[v.adicCompletion K] where
  toFun x := ⟨x.val, (adicCompletion_upstream_integer_iff K v x.val).mpr x.property⟩
  invFun x := ⟨x.val, (adicCompletion_upstream_integer_iff K v x.val).mp x.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

@[simp] theorem adicCompletionIntegerRingEquiv_coe (x : LocalIntegerRing K v) :
    ((adicCompletionIntegerRingEquiv K v x : 𝒪[v.adicCompletion K]) :
      v.adicCompletion K) = (x : v.adicCompletion K) := rfl

theorem adicCompletionIntegerRingEquiv_maximalIdeal_pow (d : ℕ) :
    Ideal.map (adicCompletionIntegerRingEquiv K v).toRingHom
      (IsLocalRing.maximalIdeal (LocalIntegerRing K v) ^ d) =
        IsLocalRing.maximalIdeal 𝒪[v.adicCompletion K] ^ d :=
  ValuationTheory.ringEquiv_map_maximalIdeal_pow _ d

theorem adicCompletionIntegerRingEquiv_principalUnits (d : ℕ)
    (u : (LocalIntegerRing K v)ˣ) :
    Units.mapEquiv (adicCompletionIntegerRingEquiv K v).toMulEquiv u ∈
        LocalFieldTheory.principalUnits (v.adicCompletion K) d ↔
      u ∈ HeckeGeneral.Characters.principalUnits K v d := by
  rw [LocalFieldTheory.mem_principalUnits_iff,
    HeckeGeneral.Characters.mem_principalUnits_iff]
  change adicCompletionIntegerRingEquiv K v (u.val - 1) ∈
      IsLocalRing.maximalIdeal 𝒪[v.adicCompletion K] ^ d ↔
    u.val - 1 ∈ IsLocalRing.maximalIdeal (LocalIntegerRing K v) ^ d
  exact ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff _ d _

@[simp] theorem adicCompletionIntegerRingEquiv_units_field
    (u : (LocalIntegerRing K v)ˣ) :
    LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits (v.adicCompletion K)
      (Units.mapEquiv (adicCompletionIntegerRingEquiv K v).toMulEquiv u) =
        localIntegerUnitsEmbedding K v u := by
  apply Units.ext
  rfl

variable (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "NZI" => NonzeroRingElements (S.integer K)

/-- Actual upstream field principal-unit membership for an ordinary prime
power increment and a finite-active denominator. The numerator remains an
arbitrary nonzero S-integer satisfying the literal additive congruence. -/
theorem sIntegerLocalQuotient_mem_upstream_fieldPrincipalUnits
    (w : S) (d : ℕ) (hd : 1 ≤ d) (n m : NZI) (t : 𝓞 K)
    (ht : t ∈ w.val.asIdeal ^ d)
    (hdiff : n.val - m.val = algebraMap (𝓞 K) (S.integer K) t)
    (hm : 0 ≤ -(HeckeGeneral.Characters.localOrderHom K w.val
      ((sLocalNonzeroIntegerDiagonal K S m).2 w)).toAdd) :
    letI : ValuativeRel (w.val.adicCompletion K) :=
      ActualFiniteCompletionDraft.adicCompletionValuativeRel K w.val
    sIntegerLocalQuotient K S w n m ∈
      LocalFieldTheory.fieldPrincipalUnits (w.val.adicCompletion K) d := by
  letI : ValuativeRel (w.val.adicCompletion K) :=
    ActualFiniteCompletionDraft.adicCompletionValuativeRel K w.val
  obtain ⟨u, hu, he⟩ :=
    exists_sIntegerLocalQuotient_principalUnit K S w d hd n m t ht hdiff hm
  refine ⟨Units.mapEquiv (adicCompletionIntegerRingEquiv K w.val).toMulEquiv u,
    (adicCompletionIntegerRingEquiv_principalUnits K w.val d u).mpr hu, ?_⟩
  rw [adicCompletionIntegerRingEquiv_units_field, he]
end HeckeGeneral.Arithmetic

