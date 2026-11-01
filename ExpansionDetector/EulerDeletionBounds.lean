import ExpansionDetector.IdealCutoff
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-! Subpower bounds for the actual finite Euler deletion factors. The
row prime set is the genuine prime support of an integral ideal. The
constant comes from the finitely many small-norm ideals, with no prime
number theorem or assumed divisor bound. -/
noncomputable section
namespace ExpansionDetector.EulerDeletion
open ExpansionDetector.IdealCutoff Filter
open scoped NumberField Classical BigOperators Topology

def localMajorant (δ q : ℝ) : ℝ := (1 - q ^ (-δ))⁻¹

lemma localMajorant_pos {δ q : ℝ} (hδ : 0 < δ) (hq : 1 < q) :
    0 < localMajorant δ q := by
  apply inv_pos.mpr
  exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg hq (neg_neg_of_pos hδ))

lemma one_le_localMajorant {δ q : ℝ} (hδ : 0 < δ) (hq : 1 < q) :
    1 ≤ localMajorant δ q := by
  have hp : 0 < 1 - q ^ (-δ) :=
    sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg hq (neg_neg_of_pos hδ))
  rw [localMajorant, ← one_div]
  apply (le_div_iff₀ hp).mpr
  linarith [Real.rpow_nonneg (zero_lt_one.trans hq).le (-δ)]

lemma localMajorant_le_two_base {δ q : ℝ} (hδ : 0 < δ) (hq : 2 ≤ q) :
    localMajorant δ q ≤ localMajorant δ 2 := by
  have hpow := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 2) hq
    (neg_nonpos.mpr hδ.le)
  have hpos : 0 < 1 - (2 : ℝ) ^ (-δ) :=
    sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hδ))
  apply inv_le_inv₀ (by linarith : 0 < 1 - q ^ (-δ)) hpos |>.mpr
  linarith

theorem localEuler_norm_and_inverse_bound (δ q : ℝ) (hδ : 0 < δ) (hq : 1 < q)
    (a s : ℂ) (ha : ‖a‖ ≤ 1) (hs : δ ≤ s.re) :
    ‖1 - a * (q : ℂ) ^ (-s)‖ ≤ localMajorant δ q ∧
      ‖(1 - a * (q : ℂ) ^ (-s))⁻¹‖ ≤ localMajorant δ q := by
  have hqp : 0 < q := zero_lt_one.trans hq
  let x : ℝ := q ^ (-δ)
  have hx0 : 0 ≤ x := Real.rpow_nonneg hqp.le _
  have hx1 : x < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (neg_neg_of_pos hδ)
  have hz : ‖a * (q : ℂ) ^ (-s)‖ ≤ x := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hqp, Complex.neg_re]
    calc
      _ ≤ 1 * q ^ (-s.re) := mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hqp.le _)
      _ ≤ x := by
        rw [one_mul]
        exact Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
  have hlo : 1 - x ≤ ‖1 - a * (q : ℂ) ^ (-s)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (a * (q : ℂ) ^ (-s))
    rw [norm_one] at h
    linarith
  constructor
  · apply (norm_sub_le (1 : ℂ) (a * (q : ℂ) ^ (-s))).trans
    rw [norm_one]
    apply (show 1 + ‖a * (q : ℂ) ^ (-s)‖ ≤ 1 + x by linarith).trans
    change 1 + x ≤ (1 - x)⁻¹
    rw [← one_div]
    apply (le_div_iff₀ (by linarith : 0 < 1 - x)).mpr
    nlinarith [sq_nonneg x]
  · rw [norm_inv]
    change ‖1 - a * (q : ℂ) ^ (-s)‖⁻¹ ≤ (1 - x)⁻¹
    exact inv_le_inv₀ (by linarith) (by linarith) |>.mpr hlo

lemma eventually_localMajorant_le_rpow (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ q : ℝ, R ≤ q → localMajorant δ q ≤ q ^ ε := by
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp
    ((tendsto_order.mp (tendsto_rpow_neg_atTop hδ)).2 (1 / 2) (by norm_num))
  obtain ⟨R₂, hR₂⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hε).eventually (eventually_ge_atTop (2 : ℝ)))
  refine ⟨max 2 (max R₁ R₂), le_max_left _ _, ?_⟩
  intro q hq
  have hp : q ^ (-δ) < (1 / 2 : ℝ) := hR₁ q ((le_max_left R₁ R₂).trans ((le_max_right _ _).trans hq))
  have hpow : (2 : ℝ) ≤ q ^ ε := hR₂ q ((le_max_right R₁ R₂).trans ((le_max_right _ _).trans hq))
  have hm : localMajorant δ q ≤ 2 := by
    change (1 - q ^ (-δ))⁻¹ ≤ 2
    rw [← one_div]
    apply (div_le_iff₀ (by linarith : 0 < 1 - q ^ (-δ))).mpr
    linarith
  exact hm.trans hpow

variable {K : Type*} [Field K] [NumberField K]

/-- Uniform subpower control over precisely the moving row-prime set.
This also bounds the reciprocal Euler polynomial on any fixed positive
half-plane, independently of the imaginary part and character phases. -/
theorem primeSupport_localMajorant_subpower (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal (𝓞 K), I ≠ 0 →
      (∏ P ∈ primeSupport I, localMajorant δ (Ideal.absNorm P : ℝ)) ≤
        C * (Ideal.absNorm I : ℝ) ^ ε := by
  obtain ⟨R, hR, hlarge⟩ := eventually_localMajorant_le_rpow δ ε hδ hε
  let F : Finset (Ideal (𝓞 K)) := (Ideal.finite_setOfPred_absNorm_le ⌈R⌉₊).toFinset
  let C₀ : ℝ := localMajorant δ 2
  have hC₀ : 1 ≤ C₀ := one_le_localMajorant hδ (by norm_num)
  have hC₀p : 0 < C₀ := zero_lt_one.trans_le hC₀
  refine ⟨C₀ ^ F.card, pow_pos hC₀p _, ?_⟩
  intro I hI
  let b : Ideal (𝓞 K) → ℝ := fun P => if (Ideal.absNorm P : ℝ) ≤ R then C₀ else 1
  have hb (P : Ideal (𝓞 K)) : 0 ≤ b P := by dsimp [b]; split_ifs <;> positivity
  have hN (P : Ideal (𝓞 K)) (hP : P ∈ primeSupport I) : 2 ≤ (Ideal.absNorm P : ℝ) := by
    exact_mod_cast two_le_norm_of_prime (support_prime hP)
  have heach (P : Ideal (𝓞 K)) (hP : P ∈ primeSupport I) :
      localMajorant δ (Ideal.absNorm P : ℝ) ≤ b P * (Ideal.absNorm P : ℝ) ^ ε := by
    by_cases hsmall : (Ideal.absNorm P : ℝ) ≤ R
    · dsimp only [b]
      rw [if_pos hsmall]
      apply (localMajorant_le_two_base hδ (hN P hP)).trans
      exact le_mul_of_one_le_right hC₀p.le
        (Real.one_le_rpow (by linarith [hN P hP]) hε.le)
    · dsimp only [b]
      rw [if_neg hsmall, one_mul]
      exact hlarge _ (lt_of_not_ge hsmall).le
  have hsubset : (primeSupport I).filter (fun P => (Ideal.absNorm P : ℝ) ≤ R) ⊆ F := by
    intro P hP
    have hp := (Finset.mem_filter.mp hP).2
    change P ∈ (Ideal.finite_setOfPred_absNorm_le ⌈R⌉₊).toFinset
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact_mod_cast hp.trans (Nat.le_ceil R)
  have hbprod : (∏ P ∈ primeSupport I, b P) ≤ C₀ ^ F.card := by
    dsimp [b]
    rw [← Finset.prod_filter, Finset.prod_const]
    exact pow_le_pow_right₀ hC₀ (Finset.card_le_card hsubset)
  have hprodNorm : (∏ P ∈ primeSupport I, (Ideal.absNorm P : ℝ)) ≤ (Ideal.absNorm I : ℝ) := by
    have hd := divisor_norm_le hI (show primeSupport I ⊆ primeSupport I from fun _ h => h)
    rw [map_prod] at hd
    exact_mod_cast hd
  calc
    _ ≤ ∏ P ∈ primeSupport I, b P * (Ideal.absNorm P : ℝ) ^ ε := by
      apply Finset.prod_le_prod₀
      · intro P hP
        exact (localMajorant_pos hδ (by linarith [hN P hP])).le
      · exact heach
    _ = (∏ P ∈ primeSupport I, b P) * (∏ P ∈ primeSupport I, (Ideal.absNorm P : ℝ) ^ ε) :=
      Finset.prod_mul_distrib
    _ ≤ (C₀ ^ F.card) * (Ideal.absNorm I : ℝ) ^ ε := by
      apply mul_le_mul hbprod _ (Finset.prod_nonneg (fun P _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (pow_nonneg hC₀p.le _)
      rw [Real.finsetProd_rpow _ _ (fun P _ => Nat.cast_nonneg _) ε]
      exact Real.rpow_le_rpow (Finset.prod_nonneg (fun P _ => Nat.cast_nonneg _)) hprodNorm hε.le

end ExpansionDetector.EulerDeletion
