import HeckeSkeleton.Moments.MOM_INV_STEP.SUnitHeightCounting
import HeckeGeneral.Arithmetic.IdealTraceLattice

/-!
# Arbitrarily small powers for actual S-unit height counts

The constants here are constructed from the genuine logarithmic lattice
mass and torsion size. The exponent may be any positive real number.
It is not constrained by the degree of the additive trace lattice.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SUnitSmallPowerCount

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open SUnitLogCounting SUnitHeightCounting
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- A logarithmic-height polynomial is bounded by every prescribed
positive power, with the constant fixed before the height and finite set. -/
theorem exists_local_height_small_power_count (F : ℝ) (hF : 1 ≤ F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, 1 ≤ H → ∀ s : Finset (S.unit K),
      (∀ u ∈ s, ∀ w : InfinitePlace K, w ((u : Kˣ) : K) ≤ H) →
      (∀ u ∈ s, ∀ v : S, finiteNorm K S u v ≤ F) →
      (s.card : ℝ) ≤ C * H ^ ε := by
  let M : ℕ := NumberField.Units.rank K + 1
  let d : ℕ := Fintype.card S + M
  let δ : ℝ := ε / (d + 1 : ℕ)
  have hδ : 0 < δ := div_pos hε (by positivity)
  let a : ℝ := (logDimension K S : ℝ) * (2 / δ + Real.log F)
  have ha : 0 ≤ a := by
    dsimp only [a]
    exact mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (div_nonneg (by norm_num) hδ.le) (Real.log_nonneg hF))
  let B : ℝ := finiteLogScale K S
  have hB : 0 ≤ B := (finiteLogScale_pos K S).le
  let Q : ℝ := latticeInversePowerMass (NumberField.Units.unitLattice K) M
  have hQ : 0 ≤ Q := tsum_nonneg (fun _ => by positivity)
  let A : ℝ := 2 * B * a + 3
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let C : ℝ := A ^ Fintype.card S *
    ((Nat.card (NumberField.Units.torsion K) : ℝ) * (1 + (2 * a) ^ M * Q))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun H hH s harch hfin => ?_⟩
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  let P : ℝ := H ^ δ
  have hP : 1 ≤ P := Real.one_le_rpow hH hδ.le
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  let T : ℝ := logBoxRadius K S F H
  have hT : 0 ≤ T := logBoxRadius_nonneg K S F H hF hH
  have hTbound : T ≤ a * P := by
    have hl := Real.log_le_rpow_div hHpos.le hδ
    have hf := mul_le_mul_of_nonneg_left hP (Real.log_nonneg hF)
    dsimp only [T, logBoxRadius, a]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    change 2 * Real.log H + Real.log F ≤ (2 / δ + Real.log F) * P
    dsimp only [P] at hl hf ⊢
    nlinarith
  have hceil : (⌈B * T⌉₊ : ℝ) ≤ B * T + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hB hT)).le
  have hN : ((2 * ⌈B * T⌉₊ + 1 : ℕ) : ℝ) ≤ A * P := by
    have hb := mul_le_mul_of_nonneg_left hTbound hB
    push_cast
    dsimp only [A]
    nlinarith
  have hpow : 1 ≤ P ^ M := one_le_pow₀ hP
  have hinside : 1 + (2 * T) ^ M * Q ≤ (1 + (2 * a) ^ M * Q) * P ^ M := by
    have hb : (2 * T) ^ M ≤ (2 * a * P) ^ M :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) M
    rw [mul_pow] at hb
    have hmul := mul_le_mul_of_nonneg_right hb hQ
    nlinarith
  have hraw := local_height_count K S M (Nat.lt_succ_self _) F H hF hH s harch hfin
  change (s.card : ℝ) ≤ ((2 * ⌈B * T⌉₊ + 1 : ℕ) : ℝ) ^ Fintype.card S *
    ((Nat.card (NumberField.Units.torsion K) : ℝ) * (1 + (2 * T) ^ M * Q)) at hraw
  have hgrowth : (s.card : ℝ) ≤ C * P ^ d := by
    calc
      _ ≤ _ := hraw
      _ ≤ (A * P) ^ Fintype.card S *
          ((Nat.card (NumberField.Units.torsion K) : ℝ) *
            ((1 + (2 * a) ^ M * Q) * P ^ M)) :=
        mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hN _)
          (mul_le_mul_of_nonneg_left hinside (Nat.cast_nonneg _))
          (by positivity) (by positivity)
      _ = _ := by dsimp only [C, d]; rw [mul_pow, pow_add]; ring
  have hexp : δ * (d : ℝ) ≤ ε := by
    have hd : (0 : ℝ) < (d + 1 : ℕ) := by positivity
    have hm : δ * (d + 1 : ℕ) = ε := by
      dsimp only [δ]
      exact div_mul_cancel₀ _ hd.ne'
    have hmono := mul_le_mul_of_nonneg_left
      (show (d : ℝ) ≤ (d + 1 : ℕ) by exact_mod_cast Nat.le_succ d) hδ.le
    exact hmono.trans_eq hm
  have hp : P ^ d ≤ H ^ ε := by
    rw [show P ^ d = H ^ (δ * (d : ℝ)) by
      dsimp only [P]
      rw [Real.rpow_mul hHpos.le, Real.rpow_natCast]]
    exact Real.rpow_le_rpow_of_exponent_le hH hexp
  exact hgrowth.trans (mul_le_mul_of_nonneg_left hp hC)

/-- Each actual infinite-place absolute value is bounded by the mixed
norm, hence by the operator norm of the fixed trace-to-mixed map. -/
theorem infinitePlace_le_trace_norm (u : S.unit K) (w : InfinitePlace K) :
    w ((u : Kˣ) : K) ≤
      ‖(traceToMixed K).toContinuousLinearMap‖ * ‖traceEmbedding K ((u : Kˣ) : K)‖ := by
  have hplace : mixedEmbedding.normAtPlace w (mixedEmbedding K ((u : Kˣ) : K)) ≤
      ‖mixedEmbedding K ((u : Kˣ) : K)‖ := by
    rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
    exact Finset.le_sup' (fun w => mixedEmbedding.normAtPlace w
      (mixedEmbedding K ((u : Kˣ) : K))) (Finset.mem_univ w)
  rw [mixedEmbedding.normAtPlace_apply] at hplace
  exact hplace.trans (by
    simpa only [traceEmbedding, ContinuousLinearEquiv.apply_symm_apply] using
      (traceToMixed K).toContinuousLinearMap.le_opNorm (traceEmbedding K ((u : Kˣ) : K)))

/-- The same sparse count in the exact Euclidean trace norm used by the
Schwartz function and Poisson theorem. -/
theorem exists_trace_height_small_power_count (F : ℝ) (hF : 1 ≤ F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, 1 ≤ H → ∀ s : Finset (S.unit K),
      (∀ u ∈ s, ‖traceEmbedding K ((u : Kˣ) : K)‖ ≤ H) →
      (∀ u ∈ s, ∀ v : S, finiteNorm K S u v ≤ F) →
      (s.card : ℝ) ≤ C * H ^ ε := by
  obtain ⟨C, hC, hb⟩ := exists_local_height_small_power_count K S F hF ε hε
  let B : ℝ := max 1 ‖(traceToMixed K).toContinuousLinearMap‖
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨C * B ^ ε, mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans hB) _),
    fun H hH s harch hfin => ?_⟩
  have hBH : 1 ≤ B * H := one_le_mul₀ hB hH
  have h := hb (B * H) hBH s (by
    intro u hu w
    exact (infinitePlace_le_trace_norm K S u w).trans
      (mul_le_mul (le_max_right _ _) (harch u hu) (norm_nonneg _)
        (zero_le_one.trans hB))) hfin
  rw [Real.mul_rpow (zero_le_one.trans hB) (zero_le_one.trans hH)] at h
  simpa only [mul_assoc] using h

end HeckeSkeleton.Moments.MOM_INV_STEP.SUnitSmallPowerCount

end
