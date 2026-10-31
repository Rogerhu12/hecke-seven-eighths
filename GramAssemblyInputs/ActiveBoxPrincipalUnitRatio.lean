import HeckeGeneral.Analysis.SUnitFinitePartitionBox
import HeckeGeneral.Characters.PrincipalUnitFiltration
import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology

/-!
UNCOMPILED / native 0. A positive additive congruence depth preserves the
actual local valuation box and changes its units only by canonical higher
units. The box contains uniformizer powers pi^(-e), so its valuation is
exp(e) >= 1. Consequently the depth has no loss depending on the box width.
No power-class invariance, period, or finite-quotient discreteness is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters

namespace HeckeGeneral.Arithmetic.ActiveBoxPrincipalUnitDraft

variable (K : Type*) [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))

/-- The active box is on the valuation-at-least-one side of the local field. -/
theorem localValuationBox_valuation_ge_one (H : ℕ)
    (x : (v.adicCompletion K)ˣ) (hx : x ∈ localValuationBox K v H) :
    (1 : WithZero (Multiplicative ℤ)) ≤ Valued.v x.val := by
  rw [localOrder_valuation]
  exact WithZero.one_le_exp_iff.mpr
    ((mem_localValuationBox_iff_order_bounds K v H x).mp hx).1

/-- Positive-depth close units have the same actual valuation in the box. -/
theorem localValuationBox_valuation_eq_of_sub_le (H n : ℕ) (hn : 1 ≤ n)
    (x y : (v.adicCompletion K)ˣ) (hx : x ∈ localValuationBox K v H)
    (hdiff : (Valued.v (y.val - x.val) : WithZero (Multiplicative ℤ)) ≤
      WithZero.exp (-(n : ℤ))) :
    (Valued.v y.val : WithZero (Multiplicative ℤ)) = Valued.v x.val := by
  have hn0 : (0 : ℤ) < (n : ℤ) := by omega
  have hsmall : (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) < 1 :=
    WithZero.exp_lt_one_iff.mpr (neg_neg_of_pos hn0)
  exact (Valued.v : Valuation (v.adicCompletion K)
    (WithZero (Multiplicative ℤ))).map_eq_of_sub_lt
      ((hdiff.trans_lt hsmall).trans_le (localValuationBox_valuation_ge_one K v H x hx))

/-- A close pair in the active box differs multiplicatively by a genuine
RayClass higher unit at the SAME depth, independent of H. -/
theorem localRatio_mem_localHigherUnitGroup_of_mem_localValuationBox
    (H n : ℕ) (hn : 1 ≤ n) (x y : (v.adicCompletion K)ˣ)
    (hx : x ∈ localValuationBox K v H)
    (hdiff : (Valued.v (y.val - x.val) : WithZero (Multiplicative ℤ)) ≤
      WithZero.exp (-(n : ℤ))) :
    y / x ∈ RayClass.localHigherUnitGroup v n := by
  have hx1 := localValuationBox_valuation_ge_one K v H x hx
  have hy := localValuationBox_valuation_eq_of_sub_le K v H n hn x y hx hdiff
  have hunit : y / x ∈ (v.adicCompletionIntegers K).units := by
    apply adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
    rw [Units.val_div_eq_div_val, Valuation.map_div, hy,
      div_self (localUnit_valuation_ne_zero K v x)]
  let z : (v.adicCompletionIntegers K).units := ⟨y / x, hunit⟩
  apply (RayClass.mem_localHigherUnitGroup_iff v n (y / x)).mpr
  refine ⟨z, rfl, ?_⟩
  apply (RayClass.localHigherUnitMap_eq_one_iff v n z).mpr
  apply (local_mem_maximalIdeal_pow_iff_valuation K v _ n).mpr
  change (Valued.v ((y / x).val - 1) : WithZero (Multiplicative ℤ)) ≤ _
  rw [Units.val_div_eq_div_val, div_sub_one (Units.ne_zero x), Valuation.map_div]
  apply (div_le_iff₀ (zero_lt_one.trans_le hx1)).mpr
  calc
    (Valued.v (y.val - x.val) : WithZero (Multiplicative ℤ)) ≤
        WithZero.exp (-(n : ℤ)) := hdiff
    _ = WithZero.exp (-(n : ℤ)) * 1 := (mul_one _).symm
    _ ≤ WithZero.exp (-(n : ℤ)) * Valued.v x.val := mul_le_mul_of_nonneg_left hx1 zero_le

/-- An ordinary prime-power congruence has exactly the required completion
valuation bound; no class-number or box-width factor enters. -/
theorem localRatio_mem_localHigherUnitGroup_of_ordinary_increment
    (H n : ℕ) (hn : 1 ≤ n) (x y : (v.adicCompletion K)ˣ)
    (hx : x ∈ localValuationBox K v H) (t : 𝓞 K)
    (ht : t ∈ v.asIdeal ^ n)
    (hdiff : y.val - x.val = algebraMap (𝓞 K) (v.adicCompletion K) t) :
    y / x ∈ RayClass.localHigherUnitGroup v n := by
  apply localRatio_mem_localHigherUnitGroup_of_mem_localValuationBox K v H n hn x y hx
  have hmap : algebraMap (𝓞 K) (v.adicCompletion K) t =
      ((algebraMap (𝓞 K) K t : K) : v.adicCompletion K) := by
    rfl
  rw [hdiff, hmap, valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]
  exact (v.intValuation_le_pow_iff_mem t n).mpr ht

/-- Ambient additive increments cannot hit zero on an active box and preserve
both the box and the actual higher-unit class at the original positive depth. -/
theorem exists_localValuationBox_translate_higherUnit
    (H n : ℕ) (hn : 1 ≤ n) (x : (v.adicCompletion K)ˣ)
    (hx : x ∈ localValuationBox K v H) (b : v.adicCompletion K)
    (hb : (Valued.v b : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-(n : ℤ))) :
    ∃ y : (v.adicCompletion K)ˣ, y.val = x.val + b ∧
      localOrderHom K v y = localOrderHom K v x ∧
      y ∈ localValuationBox K v H ∧ y / x ∈ RayClass.localHigherUnitGroup v n := by
  have hn0 : (0 : ℤ) < (n : ℤ) := by omega
  have hsmall : (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) < 1 :=
    WithZero.exp_lt_one_iff.mpr (neg_neg_of_pos hn0)
  have hval : (Valued.v (x.val + b) : WithZero (Multiplicative ℤ)) = Valued.v x.val :=
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).map_add_eq_of_lt_left
      ((hb.trans_lt hsmall).trans_le (localValuationBox_valuation_ge_one K v H x hx))
  have hne : x.val + b ≠ 0 := by
    intro heq
    apply localUnit_valuation_ne_zero K v x
    rw [← hval, heq, map_zero]
  let y := Units.mk0 (x.val + b) hne
  have horder : localOrderHom K v y = localOrderHom K v x := by
    change Multiplicative.ofAdd (-WithZero.log (Valued.v (x.val + b))) =
      Multiplicative.ofAdd (-WithZero.log (Valued.v x.val))
    rw [hval]
  refine ⟨y, rfl, horder, ?_, ?_⟩
  · rw [mem_localValuationBox_iff_order_bounds, horder,
      ← mem_localValuationBox_iff_order_bounds]
    exact hx
  · apply localRatio_mem_localHigherUnitGroup_of_mem_localValuationBox K v H n hn x y hx
    simpa [y] using hb

end HeckeGeneral.Arithmetic.ActiveBoxPrincipalUnitDraft
