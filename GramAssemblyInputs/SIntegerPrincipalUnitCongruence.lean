import HeckeGeneral.Arithmetic.SIntegerLocalDiagonal
import HeckeGeneral.Analysis.SUnitPartitionFiniteFibres

/-! SOURCE ONLY, UNRUN. Ordinary ideal-power increments give ACTUAL
principal-unit ratios of nonzero S-integers in the canonical adic completion.
The project principalUnits group is the existing kernel of reduction modulo
the actual local maximal-ideal power. No congruence implication is assumed.
This module deliberately stops before identifying that integer-ring model
with the upstream ValuativeRel integer ring and before global reciprocity. -/

noncomputable section
namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Analysis
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "NZI" => NonzeroRingElements (S.integer K)

/-- The ratio is formed in the actual local field unit group, even when
the denominator is not a unit of the S-integer ring. -/
def sIntegerLocalQuotient (v : S) (n m : NZI) : (v.val.adicCompletion K)ˣ :=
  (sLocalNonzeroIntegerDiagonal K S n).2 v /
    (sLocalNonzeroIntegerDiagonal K S m).2 v

theorem sIntegerLocalQuotient_val (v : S) (n m : NZI) :
    (sIntegerLocalQuotient K S v n m).val =
      algebraMap K (v.val.adicCompletion K) ((n.val : K) / (m.val : K)) := by
  rw [sIntegerLocalQuotient, Units.val_div_eq_div_val]
  change algebraMap K (v.val.adicCompletion K) (n.val : K) /
      algebraMap K (v.val.adicCompletion K) (m.val : K) = _
  rw [map_div₀]

/-- Exact ordinary-prime-power transport to the completion's distinguished
integer-valued valuation. This includes t=0. -/
theorem ordinary_prime_pow_completion_valuation
    (v : HeightOneSpectrum (𝓞 K)) (d : ℕ) (t : 𝓞 K)
    (ht : t ∈ v.asIdeal ^ d) :
    (Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) t) :
      WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-(d : ℤ)) := by
  change Valued.v ((algebraMap (𝓞 K) K t : K) : v.adicCompletion K) ≤ _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', v.valuation_of_algebraMap]
  exact (v.intValuation_le_pow_iff_mem t d).mpr ht

/-- Ordinary ideal-power membership transports to the actual maximal-ideal
power of the completion integer ring, with no denominator choice. -/
theorem ordinary_prime_pow_completion_integer_membership
    (v : HeightOneSpectrum (𝓞 K)) (d : ℕ) (t : 𝓞 K)
    (ht : t ∈ v.asIdeal ^ d) :
    algebraMap (𝓞 K) (v.adicCompletionIntegers K) t ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ d := by
  apply (local_mem_maximalIdeal_pow_iff_valuation K v _ d).mpr
  change Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) t) ≤ _
  exact ordinary_prime_pow_completion_valuation K v d t ht

/-- The order sign is essential: ord(m)<=0 means v(m)>=1 for the
multiplicative valuation. Thus dividing an integral increment by m can
only improve its principal-unit depth. No lower order bound is needed. -/
theorem sIntegerLocalQuotient_sub_one_valuation
    (v : S) (d : ℕ) (n m : NZI) (t : 𝓞 K)
    (ht : t ∈ v.val.asIdeal ^ d)
    (hdiff : n.val - m.val = algebraMap (𝓞 K) (S.integer K) t)
    (hm : 0 ≤ -(localOrderHom K v.val
      ((sLocalNonzeroIntegerDiagonal K S m).2 v)).toAdd) :
    (Valued.v ((sIntegerLocalQuotient K S v n m).val - 1) :
      WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-(d : ℤ)) := by
  let a := (sLocalNonzeroIntegerDiagonal K S m).2 v
  let b := (sLocalNonzeroIntegerDiagonal K S n).2 v
  have hfield : (n.val : K) - (m.val : K) = algebraMap (𝓞 K) K t :=
    congrArg (fun z : S.integer K => (z : K)) hdiff
  have hlocal : b.val - a.val = algebraMap (𝓞 K) (v.val.adicCompletion K) t := by
    change algebraMap K (v.val.adicCompletion K) (n.val : K) -
      algebraMap K (v.val.adicCompletion K) (m.val : K) = _
    rw [← map_sub, hfield]
    rfl
  have hratio : (sIntegerLocalQuotient K S v n m).val - 1 =
      algebraMap (𝓞 K) (v.val.adicCompletion K) t * a.val⁻¹ := by
    rw [sIntegerLocalQuotient, Units.val_div_eq_div_val]
    change b.val / a.val - 1 = _
    rw [← hlocal]
    have ha : a.val ≠ 0 := Units.ne_zero a
    field_simp [ha]
    <;> ring
  have hlarge : (1 : WithZero (Multiplicative ℤ)) ≤ Valued.v a.val := by
    rw [localOrder_valuation]
    exact WithZero.one_le_exp_iff.mpr hm
  rw [hratio, map_mul, map_inv₀]
  exact (mul_le_mul' (ordinary_prime_pow_completion_valuation K v.val d t ht)
    (inv_le_one_of_one_le₀ hlarge)).trans_eq (mul_one _)

/-- Actual depth-d principal-unit membership, including an explicit
integer-ring unit whose field image is n/m. Positive depth supplies both
integrality and invertibility; these are not assumptions. -/
theorem exists_sIntegerLocalQuotient_principalUnit
    (v : S) (d : ℕ) (hd : 1 ≤ d) (n m : NZI) (t : 𝓞 K)
    (ht : t ∈ v.val.asIdeal ^ d)
    (hdiff : n.val - m.val = algebraMap (𝓞 K) (S.integer K) t)
    (hm : 0 ≤ -(localOrderHom K v.val
      ((sLocalNonzeroIntegerDiagonal K S m).2 v)).toAdd) :
    ∃ u : (LocalIntegerRing K v.val)ˣ,
      u ∈ HeckeGeneral.Characters.principalUnits K v.val d ∧
      localIntegerUnitsEmbedding K v.val u = sIntegerLocalQuotient K S v n m := by
  let r := sIntegerLocalQuotient K S v n m
  have hv := sIntegerLocalQuotient_sub_one_valuation K S v d n m t ht hdiff hm
  have hnorm : ‖r.val - 1‖ ≤ (residueCard K v.val : ℝ)⁻¹ ^ d :=
    (principalUnit_norm_iff_valuation K v.val r d).mpr hv
  have hint := principalUnit_mem_integral_units K v.val r d (by omega) hnorm
  let u := integerUnitOfLocalUnit K v.val r hint
  refine ⟨u, ?_, localIntegerUnitsEmbedding_integerUnitOfLocalUnit K v.val r hint⟩
  apply (mem_principalUnits_iff_norm K v.val d u).mpr
  exact hnorm

variable [Fintype S]

/-- The ordinary modulus for a finite vector of positive local depths. -/
def sIntegerPrincipalUnitModulus (d : S → ℕ) : Ideal (𝓞 K) :=
  ∏ v : S, v.val.asIdeal ^ d v

theorem sIntegerPrincipalUnitModulus_ne_bot (d : S → ℕ) :
    sIntegerPrincipalUnitModulus K S d ≠ ⊥ := by
  exact Finset.prod_ne_zero_iff.mpr (fun v _ => pow_ne_zero _ v.val.ne_bot)

theorem sIntegerPrincipalUnitModulus_le_prime_pow (d : S → ℕ) (v : S) :
    sIntegerPrincipalUnitModulus K S d ≤ v.val.asIdeal ^ d v :=
  Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ v))

/-- Simultaneous principal-unit ratios for the whole ORIGINAL finite-active
box, with one actual ordinary ideal. Every element and every S-place is
retained, and the modulus is selected before the moving n,m. -/
theorem exists_sIntegerLocalQuotients_principalUnits_of_active
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (d : S → ℕ) (hd : ∀ v, 1 ≤ d v)
    (n m : NZI) (t : 𝓞 K)
    (ht : t ∈ sIntegerPrincipalUnitModulus K S d)
    (hdiff : n.val - m.val = algebraMap (𝓞 K) (S.integer K) t)
    (hm : (sLocalNonzeroIntegerDiagonal K S m).2 ∈
      finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)) :
    ∀ v : S, ∃ u : (LocalIntegerRing K v.val)ˣ,
      u ∈ HeckeGeneral.Characters.principalUnits K v.val (d v) ∧
      localIntegerUnitsEmbedding K v.val u = sIntegerLocalQuotient K S v n m := by
  intro v
  apply exists_sIntegerLocalQuotient_principalUnit K S v (d v) (hd v) n m t
    (sIntegerPrincipalUnitModulus_le_prime_pow K S d v ht) hdiff
  exact ((mem_localValuationBox_iff_order_bounds K v.val
    (finiteIndexSUnitBoxWidth K S Γ) _).mp (hm v)).1

end HeckeGeneral.Arithmetic
