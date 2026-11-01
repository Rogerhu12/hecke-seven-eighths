module

public import DedekindZetaZeroFree.Arithmetic.Ideals.Counting.PowerfulIdeals
public import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorEpsilonBounds
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Actual powerful-product diagonal counting

A whole index is encoded by its complete tuple of ideal factors.  Every
factor in a fiber over a product `P` is an actual divisor of `P`, so that
fiber has at most `tau(P)^k` members.  The existing number-field powerful
ideal count and divisor epsilon bound then control the complete diagonal.

The normalized complex-sum theorem assumes only pointwise support and
coefficient bounds, together with an injective factor encoding.  It does
not assume a diagonal cardinality bound or a moment inequality.  The
empty factor tuple (`k = 0`) is included in the same proof.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep.PowerfulDiagonal

open NumberField DedekindZetaZeroFree DedekindZetaZeroFree.LargeSieve

variable {K : Type} [Field K] [NumberField K]

def tupleIdeal {k : ℕ} (v : Fin k → Ideal (𝓞 K)) : Ideal (𝓞 K) := ∏ i, v i

/-- The multiplicity is derived from actual ideal divisors, for every
number of factors including zero. -/
theorem tuple_product_fiber_card {k : ℕ} (S : Finset (Fin k → Ideal (𝓞 K)))
    (P : Ideal (𝓞 K)) (hP : P ≠ 0) :
    (S.filter (fun v => tupleIdeal v = P)).card ≤ idealDivisorCount P ^ k := by
  have hin : S.filter (fun v => tupleIdeal v = P) ⊆
      Fintype.piFinset (fun _ : Fin k => idealDivisors P) := by
    intro v hv
    apply Fintype.mem_piFinset.mpr
    intro i
    apply (mem_idealDivisors hP).mpr
    have hd : v i ∣ tupleIdeal v := Finset.dvd_prod_of_mem v (Finset.mem_univ i)
    simpa only [(Finset.mem_filter.mp hv).2] using hd
  have hc := Finset.card_le_card hin
  simpa only [Fintype.card_piFinset_const, idealDivisorCount] using hc

/-- The existing powerful-ideal theorem applies to any actual finite
ideal set with a closed norm cutoff. -/
theorem finite_powerful_ideal_count (K : Type) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal (𝓞 K))) (X : ℝ), 1 ≤ X →
      (∀ I ∈ S, I ≠ 0) → (∀ I ∈ S, Powerful I) →
      (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ X) →
      (S.card : ℝ) ≤ C * Real.sqrt X := by
  obtain ⟨C, hC, hcount⟩ := powerful_ideal_count_bound K
  refine ⟨C * Real.sqrt 2, mul_pos hC (Real.sqrt_pos.mpr (by norm_num)), ?_⟩
  intro S X hX hzero hpower hN
  let lift : S → DedekindZetaZeroFree.NonzeroIdeal K :=
    fun I => ⟨I.val, hzero I.val I.property⟩
  have hinj : Function.Injective lift := by
    intro I J he
    apply Subtype.ext
    exact congrArg (fun Q : DedekindZetaZeroFree.NonzeroIdeal K => Q.val) he
  let T := S.attach.image lift
  have hcard : T.card = S.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
  have hsub : (T : Set (DedekindZetaZeroFree.NonzeroIdeal K)) ⊆ normPowerfulIdeals K (2 * X) := by
    intro I hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    change Powerful J.val ∧ (Ideal.absNorm J.val : ℝ) < 2 * X
    exact ⟨hpower J.val J.property, (hN J.val J.property).trans_lt (by linarith)⟩
  have hc : T.card ≤ (normPowerfulIdeals K (2 * X)).ncard := by
    simpa only [Set.ncard_coe_finset] using
      Set.ncard_le_ncard hsub (normPowerfulIdeals_finite K (2 * X))
  calc
    (S.card : ℝ) = (T.card : ℝ) := by rw [hcard]
    _ ≤ ((normPowerfulIdeals K (2 * X)).ncard : ℝ) := Nat.cast_le.mpr hc
    _ ≤ C * Real.sqrt (2 * X) := hcount (2 * X) (by linarith)
    _ = (C * Real.sqrt 2) * Real.sqrt X := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring

/-- A genuine powerful product diagonal, with all factor multiplicities.
The counting constant is fixed before the scale or tuple family. -/
theorem powerful_tuple_count (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Fin k → Ideal (𝓞 K))) (X : ℝ), 1 ≤ X →
      (∀ v ∈ S, tupleIdeal v ≠ 0) → (∀ v ∈ S, Powerful (tupleIdeal v)) →
      (∀ v ∈ S, (Ideal.absNorm (tupleIdeal v) : ℝ) ≤ X) →
      (S.card : ℝ) ≤ C * Real.sqrt X * X ^ ε := by
  let δ : ℝ := ε / ((k : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hbudget : δ * (k : ℝ) ≤ ε := by
    have he : δ * ((k : ℝ) + 1) = ε := div_mul_cancel₀ ε (by positivity)
    nlinarith
  obtain ⟨D, hD, hdiv⟩ := ideal_divisor_count_le_rpow K δ hδ
  obtain ⟨C, hC, hpower⟩ := finite_powerful_ideal_count K
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  refine ⟨C * D ^ k, mul_pos hC (pow_pos hDpos k), ?_⟩
  intro S X hX hzero hp hN
  let products := S.image tupleIdeal
  have hP0 (P : Ideal (𝓞 K)) (hP : P ∈ products) : P ≠ 0 := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hP
    exact hzero v hv
  have hPN (P : Ideal (𝓞 K)) (hP : P ∈ products) : (Ideal.absNorm P : ℝ) ≤ X := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hP
    exact hN v hv
  have hPpower (P : Ideal (𝓞 K)) (hP : P ∈ products) : Powerful P := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hP
    exact hp v hv
  have hcount := hpower products X hX hP0 hPpower hPN
  have hfiber (P : Ideal (𝓞 K)) (hP : P ∈ products) :
      ((S.filter (fun v => tupleIdeal v = P)).card : ℝ) ≤ D ^ k * X ^ ε := by
    have hc : ((S.filter (fun v => tupleIdeal v = P)).card : ℝ) ≤
        (idealDivisorCount P : ℝ) ^ k := by
      exact_mod_cast tuple_product_fiber_card S P (hP0 P hP)
    calc
      _ ≤ (idealDivisorCount P : ℝ) ^ k := hc
      _ ≤ (D * (Ideal.absNorm P : ℝ) ^ δ) ^ k :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv P) k
      _ = D ^ k * (Ideal.absNorm P : ℝ) ^ (δ * (k : ℝ)) := by
        rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
      _ ≤ D ^ k * X ^ ε := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hDpos.le k)
        exact (Real.rpow_le_rpow (Nat.cast_nonneg _) (hPN P hP)
          (mul_nonneg hδ.le (Nat.cast_nonneg k))).trans
          (Real.rpow_le_rpow_of_exponent_le hX hbudget)
  have he := Finset.card_eq_sum_card_fiberwise
    (fun v (hv : v ∈ S) => Finset.mem_image_of_mem tupleIdeal hv)
  calc
    _ = ∑ P ∈ products, ((S.filter (fun v => tupleIdeal v = P)).card : ℝ) := by exact_mod_cast he
    _ ≤ ∑ _P ∈ products, D ^ k * X ^ ε := Finset.sum_le_sum hfiber
    _ = (products.card : ℝ) * (D ^ k * X ^ ε) := by simp
    _ ≤ (C * Real.sqrt X) * (D ^ k * X ^ ε) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by ring

/-- A normalized whole-index diagonal is bounded directly from its
powerful-product support.  Any masks and centered differences remain
inside the original coefficient `c` throughout the finite sum. -/
theorem powerful_whole_index_normalized_sum (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : Type*} (S : Finset α)
      (factors : α → Fin k → Ideal (𝓞 K)), Set.InjOn factors (S : Set α) →
      ∀ (X A : ℝ) (c : α → ℂ), 1 ≤ X → 0 ≤ A →
      (∀ v ∈ S, tupleIdeal (factors v) ≠ 0) →
      (∀ v ∈ S, (Ideal.absNorm (tupleIdeal (factors v)) : ℝ) ≤ X) →
      (∀ v ∈ S, ¬Powerful (tupleIdeal (factors v)) → c v = 0) →
      (∀ v ∈ S, ‖c v‖ ≤ A / Real.sqrt X) →
      ‖∑ v ∈ S, c v‖ ≤ C * A * X ^ ε := by
  obtain ⟨C, hC, hcount⟩ := powerful_tuple_count (K := K) k ε hε
  refine ⟨C, hC, ?_⟩
  intro α S factors hinj X A c hX hA hzero hN hvanish hcoeff
  let T := S.filter (fun v => Powerful (tupleIdeal (factors v)))
  have hTin : Set.InjOn factors (T : Set α) := by
    intro v hv w hw he
    exact hinj (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hw).1 he
  have hcard := hcount (T.image factors) X hX
    (by intro v hv; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
        exact hzero w (Finset.mem_filter.mp hw).1)
    (by intro v hv; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
        exact (Finset.mem_filter.mp hw).2)
    (by intro v hv; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
        exact hN w (Finset.mem_filter.mp hw).1)
  rw [Finset.card_image_of_injOn hTin] at hcard
  have hsum : (∑ v ∈ S, c v) = ∑ v ∈ T, c v := by
    dsimp only [T]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hp : Powerful (tupleIdeal (factors v))
    · simp only [hp, ite_true]
    · simp only [hp, ite_false, hvanish v hv hp]
  have hsqrt : 0 < Real.sqrt X := Real.sqrt_pos.mpr (zero_lt_one.trans_le hX)
  rw [hsum]
  calc
    _ ≤ ∑ v ∈ T, ‖c v‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ T, A / Real.sqrt X :=
      Finset.sum_le_sum (fun v hv => hcoeff v (Finset.mem_filter.mp hv).1)
    _ = (T.card : ℝ) * (A / Real.sqrt X) := by simp
    _ ≤ (C * Real.sqrt X * X ^ ε) * (A / Real.sqrt X) :=
      mul_le_mul_of_nonneg_right hcard (div_nonneg hA hsqrt.le)
    _ = C * A * X ^ ε := by field_simp [hsqrt.ne'] <;> ring

end HeckeSkeleton.Moments.EngineStep.PowerfulDiagonal

end

#print axioms HeckeSkeleton.Moments.EngineStep.PowerfulDiagonal.powerful_tuple_count
#print axioms HeckeSkeleton.Moments.EngineStep.PowerfulDiagonal.powerful_whole_index_normalized_sum
