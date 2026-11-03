import HeckePort.Moments.NaturalReflection

/-!
# The mass of the deleted reflection terms

Port of openai/math `OAI/NumberTheory/DirichletL/Moments/ReflectionMass.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

The characters `η, ηi` are replaced, as in `ReflectionDeletion`, by coefficient functions
`a ai : Ideal (𝓞 K) → ℂ` with `IdealCoeff`.  The Euler-product bound (`euler_mass_subpower`) is
verbatim, the finite set of small ideals `ConcretePrimeRowBridge.idealsUpTo` being replaced by
`(Ideal.finite_setOfPred_absNorm_le K n).toFinset`.  `reflectedTerm_eq_coefficient` states that
`reflectedTerm` is `coefficient` times the deleted polynomial (by `rfl`).
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators
open HeckePort.IdealMobiusDivisorSum UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]

namespace ReflectionMass

def weight (I : Ideal (𝓞 K)) : ℝ := (Real.sqrt (I.absNorm : ℝ))⁻¹

lemma weight_nonneg (I : Ideal (𝓞 K)) : 0 ≤ weight I := by unfold weight; positivity

lemma weight_mul (I J : Ideal (𝓞 K)) : weight (I * J) = weight I * weight J := by
  simp only [weight, map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), mul_inv_rev]
  ring

lemma weight_one : weight (1 : Ideal (𝓞 K)) = 1 := by simp [weight]

lemma weight_pow (I : Ideal (𝓞 K)) (n : ℕ) : weight (I ^ n) = weight I ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using weight_one
  | succ n ih => rw [pow_succ, weight_mul, ih, pow_succ]

lemma weight_prod (S : Finset (Ideal (𝓞 K))) (f : Ideal (𝓞 K) → Ideal (𝓞 K)) :
    weight (∏ P ∈ S, f P) = ∏ P ∈ S, weight (f P) := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using weight_one
  | @insert P S h ih => simp only [Finset.prod_insert h, weight_mul, ih]

/-- A prime ideal has norm at least two (openai `SmoothMobiusCorrection.prime_norm_two_le`). -/
lemma prime_norm_two_le (P : Ideal (𝓞 K)) (hP : Prime P) : 2 ≤ P.absNorm := by
  have h0 : P.absNorm ≠ 0 := fun hz => hP.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz)
  have h1 : P.absNorm ≠ 1 := fun hz =>
    hP.not_isUnit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp hz))
  omega

lemma prime_weight_lt_one (P : Ideal (𝓞 K)) (hP : Prime P) : weight P < 1 := by
  have h : (1 : ℝ) < P.absNorm := by
    have hh : 2 ≤ P.absNorm := prime_norm_two_le P hP
    exact_mod_cast (by omega : 1 < P.absNorm)
  have hs : 1 < Real.sqrt (P.absNorm : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    simpa using h
  exact inv_lt_one_of_one_lt₀ hs

def exponents (S : Finset (Ideal (𝓞 K))) (I : SmoothIdeal S) (P : S) : ℕ :=
  (normalizedFactors I.val.val).count P.val

lemma reconstruct_exponents (S : Finset (Ideal (𝓞 K))) (I : SmoothIdeal S) :
    (∏ P : S, P.val ^ exponents S I P) = I.val.val := by
  simp only [exponents]
  rw [Finset.prod_coe_sort S (fun P => P ^ (normalizedFactors I.val.val).count P)]
  exact (Finset.prod_multiset_count_of_subset (normalizedFactors I.val.val) S I.property).symm.trans
    (Ideal.prod_normalizedFactors_eq_self I.val.property)

lemma exponents_injective (S : Finset (Ideal (𝓞 K))) : Function.Injective (exponents S) := by
  intro I J h
  apply Subtype.ext
  apply Subtype.ext
  rw [← reconstruct_exponents S I, ← reconstruct_exponents S J, h]

lemma weight_exponents (S : Finset (Ideal (𝓞 K))) (I : SmoothIdeal S) :
    weight I.val.val = ∏ P : S, weight P.val ^ exponents S I P := by
  conv_lhs => rw [← reconstruct_exponents S I]
  simp only [exponents]
  rw [Finset.prod_coe_sort S (fun P => P ^ (normalizedFactors I.val.val).count P),
    Finset.prod_coe_sort S (fun P => weight P ^ (normalizedFactors I.val.val).count P), weight_prod]
  simp only [weight_pow]

lemma hasSum_geometric_pi {α : Type*} [Fintype α] (r : α → ℝ)
    (hr : ∀ a, 0 ≤ r a) (hr1 : ∀ a, r a < 1) :
    HasSum (fun n : α → ℕ => ∏ a, r a ^ n a) (∏ a, (1 - r a)⁻¹) := by
  classical
  apply Fintype.induction_empty_option (P := fun β _ => ∀ (r : β → ℝ),
    (∀ a, 0 ≤ r a) → (∀ a, r a < 1) →
    HasSum (fun n : β → ℕ => ∏ a, r a ^ n a) (∏ a, (1 - r a)⁻¹)) ?_ ?_ ?_ α r hr hr1
  · intro α β _ e ih r hr hr1
    let : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (r ∘ e) (fun a => hr (e a)) (fun a => hr1 (e a))
    let E : (β → ℕ) ≃ (α → ℕ) := Equiv.arrowCongr e.symm (Equiv.refl ℕ)
    have he := E.hasSum_iff.mpr h
    convert he using 1
    · funext n
      exact (e.prod_comp (fun b => r b ^ n b)).symm
    · exact (e.prod_comp (fun b => (1 - r b)⁻¹)).symm
  · intro r _ _
    simp
  · intro α _ ih r hr hr1
    have h0 := hasSum_geometric_of_lt_one (hr none) (hr1 none)
    have ht := ih (fun a => r (some a)) (fun a => hr (some a)) (fun a => hr1 (some a))
    have hs := h0.summable.mul_of_nonneg ht.summable (fun n => pow_nonneg (hr none) n)
      (fun n => Finset.prod_nonneg (fun a _ => pow_nonneg (hr (some a)) (n a)))
    have hp := h0.mul ht hs
    have he := (Equiv.piOptionEquivProd (β := fun _ : Option α => ℕ)).hasSum_iff.mpr hp
    simpa only [Function.comp_def, Fintype.prod_option, Equiv.piOptionEquivProd_apply] using he

lemma smooth_summable (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P) :
    Summable (fun I : SmoothIdeal S => weight I.val.val) := by
  have hs := (hasSum_geometric_pi (fun P : S => weight P.val)
    (fun P => weight_nonneg P.val)
    (fun P => prime_weight_lt_one P.val (hS P.val P.property))).summable
  exact (hs.comp_injective (exponents_injective S)).congr (fun I => (weight_exponents S I).symm)

lemma smooth_mass_le_euler (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P) :
    (∑' I : SmoothIdeal S, weight I.val.val) ≤ ∏ P ∈ S, (1 - weight P)⁻¹ := by
  have hh := hasSum_geometric_pi (fun P : S => weight P.val)
    (fun P => weight_nonneg P.val)
    (fun P => prime_weight_lt_one P.val (hS P.val P.property))
  have h := Summable.tsum_le_tsum_of_inj (exponents S) (exponents_injective S)
    (fun n _ => Finset.prod_nonneg (fun P _ => pow_nonneg (weight_nonneg P.val) (n P)))
    (fun I => (weight_exponents S I).le) (smooth_summable S hS) hh.summable
  rw [hh.tsum_eq, Finset.prod_coe_sort S (fun P => (1 - weight P)⁻¹)] at h
  exact h

lemma deletion_mass (S : Finset (Ideal (𝓞 K))) :
    (∑ D ∈ S.powerset, weight (∏ P ∈ D, P)) = ∏ P ∈ S, (1 + weight P) := by
  simp_rw [weight_prod]
  exact (Finset.prod_one_add S).symm

def localMass (P : Ideal (𝓞 K)) : ℝ := (1 + weight P) / (1 - weight P)

lemma localMass_nonneg (P : Ideal (𝓞 K)) (hP : Prime P) : 0 ≤ localMass P :=
  div_nonneg (by linarith [weight_nonneg P]) (sub_pos.mpr (prime_weight_lt_one P hP)).le

lemma prime_weight_le (P : Ideal (𝓞 K)) (hP : Prime P) : weight P ≤ 3 / 4 := by
  have hn : (2 : ℝ) ≤ P.absNorm := by
    exact_mod_cast (prime_norm_two_le P hP : 2 ≤ P.absNorm)
  have hs : 4 / 3 ≤ Real.sqrt (P.absNorm : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  rw [weight, inv_eq_one_div, div_le_iff₀ (by linarith : 0 < Real.sqrt (P.absNorm : ℝ))]
  nlinarith

lemma localMass_le_seven (P : Ideal (𝓞 K)) (hP : Prime P) : localMass P ≤ 7 := by
  apply (div_le_iff₀ (sub_pos.mpr (prime_weight_lt_one P hP))).mpr
  linarith [prime_weight_le P hP]

lemma localMass_le_three (P : Ideal (𝓞 K)) (hP : Prime P) (hn : (4 : ℝ) ≤ P.absNorm) :
    localMass P ≤ 3 := by
  have hs : 2 ≤ Real.sqrt (P.absNorm : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith
  have hw : weight P ≤ 1 / 2 := by
    rw [weight, inv_eq_one_div, div_le_iff₀ (by linarith : 0 < Real.sqrt (P.absNorm : ℝ))]
    linarith
  apply (div_le_iff₀ (sub_pos.mpr (prime_weight_lt_one P hP))).mpr
  linarith

/-- The ideals of norm at most `n` (openai `ConcretePrimeRowBridge.idealsUpTo`). -/
def idealsUpTo (K : Type*) [Field K] [NumberField K] (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) n).toFinset

theorem euler_mass_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal (𝓞 K))) (_hS : ∀ P ∈ S, Prime P),
      (∏ P ∈ S, localMass P) ≤ C * (Ideal.absNorm (∏ P ∈ S, P) : ℝ) ^ ε := by
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hε).eventually (Filter.eventually_ge_atTop (3 : ℝ)))
  let N : ℕ := ⌈max 4 B⌉₊
  let smallIdeals := idealsUpTo K N
  have hK : max 4 B ≤ (N : ℝ) := Nat.le_ceil _
  refine ⟨(7 : ℝ) ^ smallIdeals.card, by positivity, ?_⟩
  intro S hS
  have hpoint (P : Ideal (𝓞 K)) (hP : P ∈ S) :
      localMass P ≤ (if P ∈ smallIdeals then 7 else 1) * (P.absNorm : ℝ) ^ ε := by
    have hn : (1 : ℝ) ≤ P.absNorm := by
      have hh : 2 ≤ P.absNorm := prime_norm_two_le P (hS P hP)
      exact_mod_cast (by omega : 1 ≤ P.absNorm)
    have he : 1 ≤ (P.absNorm : ℝ) ^ ε := Real.one_le_rpow hn hε.le
    by_cases hp : P ∈ smallIdeals
    · simp only [hp, ite_true]
      exact (localMass_le_seven P (hS P hP)).trans (by nlinarith)
    · have hpk : (N : ℝ) < P.absNorm := by
        have hh : ¬ P.absNorm ≤ N := by
          intro h
          apply hp
          simpa [smallIdeals, idealsUpTo] using h
        exact_mod_cast Nat.lt_of_not_ge hh
      have h4 : (4 : ℝ) ≤ P.absNorm := (le_max_left _ _).trans (hK.trans hpk.le)
      have hb : B ≤ (P.absNorm : ℝ) := (le_max_right _ _).trans (hK.trans hpk.le)
      simp only [hp, ite_false, one_mul]
      exact (localMass_le_three P (hS P hP) h4).trans (hB _ hb)
  have hc : (S.filter (· ∈ smallIdeals)).card ≤ smallIdeals.card :=
    Finset.card_le_card (fun P hP => (Finset.mem_filter.mp hP).2)
  calc
    (∏ P ∈ S, localMass P) ≤ ∏ P ∈ S, ((if P ∈ smallIdeals then 7 else 1) * (P.absNorm : ℝ) ^ ε) :=
      Finset.prod_le_prod₀ (fun P hP => localMass_nonneg P (hS P hP)) hpoint
    _ = (7 : ℝ) ^ (S.filter (· ∈ smallIdeals)).card * (Ideal.absNorm (∏ P ∈ S, P) : ℝ) ^ ε := by
      rw [Finset.prod_mul_distrib, ← Finset.prod_filter]
      simp only [Finset.prod_const, Real.finsetProd_rpow S _ (fun _ _ => Nat.cast_nonneg _) ε,
        map_prod, Nat.cast_prod]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hc)
      (Real.rpow_nonneg (by positivity) _)

def coefficient (a ai : Ideal (𝓞 K) → ℂ) (S : Finset (Ideal (𝓞 K)))
    (D : Finset (Ideal (𝓞 K))) (H : SmoothIdeal S) : ℂ :=
  (moebius (∏ P ∈ D, P) : ℂ) * a (∏ P ∈ D, P) * ai H.val.val /
    (Real.sqrt ((Ideal.absNorm (∏ P ∈ D, P) : ℝ) * inorm H.val) : ℂ)

lemma coefficient_norm_le {a ai : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a) (hai : IdealCoeff ai)
    (S : Finset (Ideal (𝓞 K)))
    (D : Finset (Ideal (𝓞 K))) (hD : ∀ P ∈ D, Prime P) (H : SmoothIdeal S) :
    ‖coefficient a ai S D H‖ ≤ weight (∏ P ∈ D, P) * weight H.val.val := by
  rw [coefficient, subset_product_moebius D hD]
  simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h : ‖a (∏ P ∈ D, P)‖ * ‖ai H.val.val‖ ≤ 1 :=
    (mul_le_mul (ha.norm_le_one _) (hai.norm_le_one _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  apply (div_le_div_of_nonneg_right h (Real.sqrt_nonneg _)).trans_eq
  simp only [inorm, weight, Real.sqrt_mul (Nat.cast_nonneg _), one_div, mul_inv_rev]
  ring

lemma coefficient_summable_norm {a ai : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a)
    (hai : IdealCoeff ai) (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ P ∈ S, Prime P) (D : Finset (Ideal (𝓞 K))) (hD : D ⊆ S) :
    Summable (fun H : SmoothIdeal S => ‖coefficient a ai S D H‖) := by
  apply ((smooth_summable S hS).mul_left (weight (∏ P ∈ D, P))).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  exact fun H => coefficient_norm_le ha hai S D (fun P hP => hS P (hD hP)) H

lemma coefficient_summable {a ai : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a)
    (hai : IdealCoeff ai) (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ P ∈ S, Prime P) (D : Finset (Ideal (𝓞 K))) (hD : D ⊆ S) :
    Summable (coefficient a ai S D) := (coefficient_summable_norm ha hai S hS D hD).of_norm

lemma coefficient_mass_le_euler {a ai : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a)
    (hai : IdealCoeff ai) (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ P ∈ S, Prime P) :
    (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, ‖coefficient a ai S D H‖) ≤
      ∏ P ∈ S, localMass P := by
  have hD (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset) :
      (∑' H : SmoothIdeal S, ‖coefficient a ai S D H‖) ≤
        weight (∏ P ∈ D, P) * (∏ P ∈ S, (1 - weight P)⁻¹) := by
    have hsub := Finset.mem_powerset.mp hD
    apply ((coefficient_summable_norm ha hai S hS D hsub).tsum_le_tsum
      (fun H => coefficient_norm_le ha hai S D (fun P hP => hS P (hsub hP)) H)
      ((smooth_summable S hS).mul_left (weight (∏ P ∈ D, P)))).trans
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (smooth_mass_le_euler S hS) (weight_nonneg _)
  apply (Finset.sum_le_sum hD).trans_eq
  rw [← Finset.sum_mul, deletion_mass, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P _
  exact (div_eq_mul_inv _ _).symm

lemma coefficient_mass_summable {a ai : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a)
    (hai : IdealCoeff ai) (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ P ∈ S, Prime P) :
    Summable (fun H : SmoothIdeal S => ∑ D ∈ S.powerset, ‖coefficient a ai S D H‖) :=
  summable_sum (fun D hD => coefficient_summable_norm ha hai S hS D (Finset.mem_powerset.mp hD))

theorem reflection_mass_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal (𝓞 K))) (_hS : ∀ P ∈ S, Prime P)
      (a ai : Ideal (𝓞 K) → ℂ) (_ha : IdealCoeff a) (_hai : IdealCoeff ai),
      Summable (fun H : SmoothIdeal S => ∑ D ∈ S.powerset, ‖coefficient a ai S D H‖) ∧
      (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, ‖coefficient a ai S D H‖) ≤
        C * (Ideal.absNorm (∏ P ∈ S, P) : ℝ) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := euler_mass_subpower (K := K) ε hε
  exact ⟨C, hC, fun S hS a ai ha hai => ⟨coefficient_mass_summable ha hai S hS,
    (coefficient_mass_le_euler ha hai S hS).trans (hbound S hS)⟩⟩

def unitSmooth (S : Finset (Ideal (𝓞 K))) : SmoothIdeal S :=
  ⟨⟨1, one_ne_zero⟩, by
    change (normalizedFactors (1 : Ideal (𝓞 K))).toFinset ⊆ S
    rw [normalizedFactors_one]
    exact Finset.empty_subset _⟩

lemma coefficient_empty_unit {a ai : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a)
    (hai : IdealCoeff ai) (S : Finset (Ideal (𝓞 K))) :
    coefficient a ai S ∅ (unitSmooth S) = 1 := by
  have hm : (moebius (1 : Ideal (𝓞 K)) : ℂ) = 1 := by
    simpa only [Finset.prod_empty, Finset.card_empty, pow_zero] using
      subset_product_moebius (K := K) ∅ (by simp)
  change (moebius (1 : Ideal (𝓞 K)) : ℂ) * a 1 * ai 1 /
    (Real.sqrt ((Ideal.absNorm (1 : Ideal (𝓞 K)) : ℝ) *
      (Ideal.absNorm (1 : Ideal (𝓞 K)) : ℝ)) : ℂ) = 1
  rw [hm, ha.map_one, hai.map_one, map_one]
  norm_num

/-- `reflectedTerm` is `coefficient` times the deleted polynomial (openai
`reflectedTerm_eq_coefficient`, where the polynomial is `HeckeDyadic.polynomial`). -/
lemma reflectedTerm_eq_coefficient (a ai : Ideal (𝓞 K) → ℂ) (S : Finset (Ideal (𝓞 K)))
    (F : ℝ → ℂ) (X Q : ℝ)
    (D : Finset (Ideal (𝓞 K))) (H : SmoothIdeal S) :
    reflectedTerm a ai S F X Q D H = coefficient a ai S D H *
      plainPoly (excl S ai) F (Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val)) := rfl

end ReflectionMass

end HeckePort.Moments

end
