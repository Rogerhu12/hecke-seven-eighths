import HeckeGeneral.Arithmetic.SIntegerFiniteLocalization
import HeckeGeneral.Arithmetic.SIntegerOrbitDilation
import HeckeGeneral.Analysis.SUnitFinitePartitionBox

/-! UNCOMPILED / native 0. A fixed exact-S power clears every S-integer
whose actual finite valuation exponents have the fixed upper bound H.
The same power clears the quotient of two active columns when the divisor
is also in the original fixed box. No archimedean seminorm is estimated. -/

noncomputable section
namespace HeckeGeneral.Arithmetic.ActualGramFixedDenominatorDraft
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open HeckeGeneral.Characters HeckeGeneral.Analysis
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "D" => finiteSIntegerDenominator K S
local notation "NZ" => NonzeroRingElements (S.integer K)

/-- D has valuation exponent minus the class number at every original S prime. -/
theorem valuation_exactSDenominator (v : S) :
    v.val.valuation K (algebraMap (𝓞 K) K D) =
      WithZero.exp (-(classNumber K : ℤ)) := by
  rw [valuation_of_algebraMap]
  unfold finiteSIntegerDenominator
  rw [map_prod]
  calc
    _ = v.val.intValuation (primePowerGenerator K v.val) := by
      apply Finset.prod_eq_single_of_mem v.val
        ((Set.toFinite S).mem_toFinset.mpr v.property)
      intro w _ hw
      exact intValuation_primePowerGenerator_ne K w v.val (Ne.symm hw)
    _ = _ := intValuation_primePowerGenerator_self K v.val

/-- The completion's localOrder sign agrees with the actual field valuation:
sLocalValuation is the valuation exponent, the negative uniformizer order. -/
theorem valuation_nonzeroSInteger_eq_exp (m : NZ) (v : S) :
    v.val.valuation K (m.val : K) =
      WithZero.exp (sLocalValuation K S (sLocalNonzeroIntegerDiagonal K S m) v) := by
  have h := localOrder_valuation K v.val
    ((sLocalNonzeroIntegerDiagonal K S m).2 v)
  change (Valued.v (algebraMap K (v.val.adicCompletion K) (m.val : K)) :
    WithZero (Multiplicative ℤ)) =
      WithZero.exp (sLocalValuation K S (sLocalNonzeroIntegerDiagonal K S m) v) at h
  exact Eq.trans (adicCompletion.valued_coe (K := K) (v := v.val) (m.val : K)).symm h

/-- The exponent is exactly H, not H times a moving denominator exponent.
The class-number factor helps: H * classNumber K is at least H. -/
theorem exactSDenominator_pow_clears_of_valuation_le (H : ℕ) (m : NZ)
    (hm : ∀ v : S,
      sLocalValuation K S (sLocalNonzeroIntegerDiagonal K S m) v ≤ (H : ℤ)) :
    ∃ z : 𝓞 K,
      algebraMap (𝓞 K) (S.integer K) (D ^ H) * m.val =
        algebraMap (𝓞 K) (S.integer K) z := by
  have hint : algebraMap (𝓞 K) K (D ^ H) * (m.val : K) ∈
      (algebraMap (𝓞 K) K).range := by
    apply mem_integers_of_valuation_le_one K
    intro v
    by_cases hv : v ∈ S
    · let w : S := ⟨v, hv⟩
      have hclass : (1 : ℤ) ≤ (classNumber K : ℤ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (classNumber_pos K).ne')
      have hH : (H : ℤ) ≤ (H : ℤ) * (classNumber K : ℤ) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hclass (Int.natCast_nonneg H)
      rw [map_mul, map_pow, map_pow, valuation_exactSDenominator K S w,
        valuation_nonzeroSInteger_eq_exp K S m w, ← WithZero.exp_nsmul,
        ← WithZero.exp_add]
      apply WithZero.exp_le_one_iff.mpr
      simp only [nsmul_eq_mul]
      have hmw := hm w
      nlinarith
    · rw [map_mul]
      exact (mul_le_mul' (v.valuation_le_one (D ^ H)) (m.val.property v hv)).trans
        (by simp)
  obtain ⟨z, hz⟩ := hint
  refine ⟨z, ?_⟩
  apply Subtype.ext
  exact hz.symm

theorem exactSDenominator_pow_clears_active (H : ℕ) (m : NZ)
    (hm : (sLocalNonzeroIntegerDiagonal K S m).2 ∈ finiteLocalValuationBox K S H) :
    ∃ z : 𝓞 K,
      algebraMap (𝓞 K) (S.integer K) (D ^ H) * m.val =
        algebraMap (𝓞 K) (S.integer K) z := by
  apply exactSDenominator_pow_clears_of_valuation_le K S H m
  intro v
  exact ((mem_localValuationBox_iff_order_bounds K v.val H _).mp (hm v)).2.le

/-- n=d*m and d in the same fixed box imply a uniform upper exponent for m.
The quotient need not itself lie in the nonnegative valuation box. -/
theorem exactSDenominator_pow_clears_divisor_quotient (H : ℕ) (d m : NZ)
    (hd : (sLocalNonzeroIntegerDiagonal K S d).2 ∈ finiteLocalValuationBox K S H)
    (hn : (sLocalNonzeroIntegerDiagonal K S (sIntegerNonzeroMul K S d m)).2 ∈
      finiteLocalValuationBox K S H) :
    ∃ z : 𝓞 K,
      algebraMap (𝓞 K) (S.integer K) (D ^ H) * m.val =
        algebraMap (𝓞 K) (S.integer K) z := by
  apply exactSDenominator_pow_clears_of_valuation_le K S H m
  intro v
  have hdl := ((mem_localValuationBox_iff_order_bounds K v.val H _).mp (hd v)).1
  have hnu := ((mem_localValuationBox_iff_order_bounds K v.val H _).mp (hn v)).2
  have he : sLocalValuation K S
      (sLocalNonzeroIntegerDiagonal K S (sIntegerNonzeroMul K S d m)) v =
      sLocalValuation K S (sLocalNonzeroIntegerDiagonal K S d) v +
      sLocalValuation K S (sLocalNonzeroIntegerDiagonal K S m) v := by
    rw [sLocalNonzeroIntegerDiagonal_nonzeroMul, sLocalValuation_mul]
  change 0 ≤ sLocalValuation K S (sLocalNonzeroIntegerDiagonal K S d) v at hdl
  change sLocalValuation K S
    (sLocalNonzeroIntegerDiagonal K S (sIntegerNonzeroMul K S d m)) v < (H : ℤ) at hnu
  omega

/-- The three clearing data needed by the existing chart bridge share
the fixed exponent H; its combined period exponent is H+H. -/
theorem fixed_clearing_triple (H : ℕ) (d m₁ m₂ : NZ)
    (hd : (sLocalNonzeroIntegerDiagonal K S d).2 ∈ finiteLocalValuationBox K S H)
    (h₁ : (sLocalNonzeroIntegerDiagonal K S (sIntegerNonzeroMul K S d m₁)).2 ∈
      finiteLocalValuationBox K S H)
    (h₂ : (sLocalNonzeroIntegerDiagonal K S (sIntegerNonzeroMul K S d m₂)).2 ∈
      finiteLocalValuationBox K S H) :
    ∃ a z₁ z₂ : 𝓞 K,
      algebraMap (𝓞 K) (S.integer K) (D ^ H) * d.val =
        algebraMap (𝓞 K) (S.integer K) a ∧
      algebraMap (𝓞 K) (S.integer K) (D ^ H) * m₁.val =
        algebraMap (𝓞 K) (S.integer K) z₁ ∧
      algebraMap (𝓞 K) (S.integer K) (D ^ H) * m₂.val =
        algebraMap (𝓞 K) (S.integer K) z₂ := by
  obtain ⟨a, ha⟩ := exactSDenominator_pow_clears_active K S H d hd
  obtain ⟨z₁, hz₁⟩ := exactSDenominator_pow_clears_divisor_quotient K S H d m₁ hd h₁
  obtain ⟨z₂, hz₂⟩ := exactSDenominator_pow_clears_divisor_quotient K S H d m₂ hd h₂
  exact ⟨a, z₁, z₂, ha, hz₁, hz₂⟩

variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "H" => finiteIndexSUnitBoxWidth K S Γ

/-- The genuine joint reduction supplies a unit of the original subgroup.
After this selection, divisor and every active quotient use the fixed power
D^H, hence the two clearing exponents may both be H (CRT depth 2*H). -/
theorem exists_subgroup_translate_with_fixed_denominator (d : NZ) :
    ∃ u : Γ, let d' := sIntegerOrbitTranslate K S Γ u d
      (sLocalNonzeroIntegerDiagonal K S d').2 ∈ finiteLocalValuationBox K S H ∧
      (∃ z : 𝓞 K, algebraMap (𝓞 K) (S.integer K) (D ^ H) * d'.val =
        algebraMap (𝓞 K) (S.integer K) z) ∧
      ∀ m : NZ,
        (sLocalNonzeroIntegerDiagonal K S (sIntegerNonzeroMul K S d' m)).2 ∈
          finiteLocalValuationBox K S H →
        ∃ z : 𝓞 K, algebraMap (𝓞 K) (S.integer K) (D ^ H) * m.val =
          algebraMap (𝓞 K) (S.integer K) z := by
  obtain ⟨u, v, _, hbox⟩ := exists_subgroup_joint_local_reduction K S Γ
    (sLocalNonzeroIntegerDiagonal K S d)
  let d' := sIntegerOrbitTranslate K S Γ (v * u) d
  have hd' : (sLocalNonzeroIntegerDiagonal K S d').2 ∈
      finiteLocalValuationBox K S H := by
    intro w
    apply (mem_localValuationBox_iff_order_bounds K w.val H _).mpr
    change 0 ≤ sLocalValuation K S (sLocalNonzeroIntegerDiagonal K S d') w ∧
      sLocalValuation K S (sLocalNonzeroIntegerDiagonal K S d') w < (H : ℤ)
    rw [sLocalNonzeroIntegerDiagonal_translate]
    exact hbox w
  exact ⟨v * u, hd', exactSDenominator_pow_clears_active K S H d' hd',
    fun m hm => exactSDenominator_pow_clears_divisor_quotient K S H d' m hd' hm⟩

end HeckeGeneral.Arithmetic.ActualGramFixedDenominatorDraft
