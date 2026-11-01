import HeckePort.Moments.ReflectionMass

/-!
# Weighted deletion and restoration masses on noncentral Mellin lines

The old square-root mass is insufficient on the ordinary reflected
Mellin lines with real part 1/4 or 3/4.  This module proves the actual
Euler mass estimate for every fixed positive ideal-norm exponent.

The finite deletion index remains a subset of the original prime set;
the restoration index remains the full set of ideals smooth on that
same finite set.  Both their summability and their combined subpower
mass are proved from prime ideal norms and unique factorization.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField UniqueFactorizationMonoid
open HeckePort.Moments HeckePort.Moments.ReflectionMass
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]

/-- A genuine ideal-norm weight, with its exponent kept explicit. -/
def reflectionPowerWeight (β : ℝ) (I : Ideal (𝓞 K)) : ℝ :=
  (I.absNorm : ℝ) ^ (-β)

theorem reflectionPowerWeight_nonneg (β : ℝ) (I : Ideal (𝓞 K)) :
    0 ≤ reflectionPowerWeight β I := Real.rpow_nonneg (Nat.cast_nonneg _) _

private theorem powerWeight_mul (β : ℝ) (I J : Ideal (𝓞 K)) :
    reflectionPowerWeight β (I * J) =
      reflectionPowerWeight β I * reflectionPowerWeight β J := by
  unfold reflectionPowerWeight
  rw [map_mul, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg I.absNorm) (Nat.cast_nonneg J.absNorm)]

private theorem powerWeight_one (β : ℝ) :
    reflectionPowerWeight β (1 : Ideal (𝓞 K)) = 1 := by
  simp [reflectionPowerWeight]

private theorem powerWeight_pow (β : ℝ) (I : Ideal (𝓞 K)) (n : ℕ) :
    reflectionPowerWeight β (I ^ n) = reflectionPowerWeight β I ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using powerWeight_one (K := K) β
  | succ n ih => rw [pow_succ, powerWeight_mul, ih, pow_succ]

private theorem powerWeight_prod (β : ℝ) (S : Finset (Ideal (𝓞 K)))
    (f : Ideal (𝓞 K) → Ideal (𝓞 K)) :
    reflectionPowerWeight β (∏ P ∈ S, f P) =
      ∏ P ∈ S, reflectionPowerWeight β (f P) := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using powerWeight_one (K := K) β
  | @insert P S h ih => simp only [Finset.prod_insert h, powerWeight_mul, ih]

private theorem prime_powerWeight_lt_one {β : ℝ} (hβ : 0 < β)
    (P : Ideal (𝓞 K)) (hP : Prime P) : reflectionPowerWeight β P < 1 := by
  have hnorm : (1 : ℝ) < P.absNorm := by
    exact_mod_cast (show 1 < P.absNorm by
      have h := prime_norm_two_le P hP
      omega)
  exact Real.rpow_lt_one_of_one_lt_of_neg hnorm (neg_neg_of_pos hβ)

private theorem powerWeight_exponents (β : ℝ) (S : Finset (Ideal (𝓞 K)))
    (I : SmoothIdeal S) :
    reflectionPowerWeight β I.val.val =
      ∏ P : S, reflectionPowerWeight β P.val ^ exponents S I P := by
  conv_lhs => rw [← reconstruct_exponents S I]
  simp only [exponents]
  rw [Finset.prod_coe_sort S (fun P => P ^ (normalizedFactors I.val.val).count P),
    Finset.prod_coe_sort S (fun P =>
      reflectionPowerWeight β P ^ (normalizedFactors I.val.val).count P), powerWeight_prod]
  simp only [powerWeight_pow]

/-- The infinite restoration sum genuinely converges for every positive
weight exponent, including 1/4. -/
theorem weightedSmoothSummable (β : ℝ) (hβ : 0 < β)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P) :
    Summable (fun I : SmoothIdeal S => reflectionPowerWeight β I.val.val) := by
  have hs := (hasSum_geometric_pi (fun P : S => reflectionPowerWeight β P.val)
    (fun P => reflectionPowerWeight_nonneg β P.val)
    (fun P => prime_powerWeight_lt_one hβ P.val (hS P.val P.property))).summable
  exact (hs.comp_injective (exponents_injective S)).congr
    (fun I => (powerWeight_exponents β S I).symm)

theorem weightedSmoothMass_le_euler (β : ℝ) (hβ : 0 < β)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P) :
    (∑' I : SmoothIdeal S, reflectionPowerWeight β I.val.val) ≤
      ∏ P ∈ S, (1 - reflectionPowerWeight β P)⁻¹ := by
  have hh := hasSum_geometric_pi (fun P : S => reflectionPowerWeight β P.val)
    (fun P => reflectionPowerWeight_nonneg β P.val)
    (fun P => prime_powerWeight_lt_one hβ P.val (hS P.val P.property))
  have h := Summable.tsum_le_tsum_of_inj (exponents S) (exponents_injective S)
    (fun n _ => Finset.prod_nonneg
      (fun P _ => pow_nonneg (reflectionPowerWeight_nonneg β P.val) (n P)))
    (fun I => (powerWeight_exponents β S I).le)
    (weightedSmoothSummable β hβ S hS) hh.summable
  rw [hh.tsum_eq,
    Finset.prod_coe_sort S (fun P => (1 - reflectionPowerWeight β P)⁻¹)] at h
  exact h

/-- The finite squarefree deletion has its exact Euler expansion. -/
theorem weightedDeletionMass_eq_euler (β : ℝ) (S : Finset (Ideal (𝓞 K))) :
    (∑ D ∈ S.powerset, reflectionPowerWeight β (∏ P ∈ D, P)) =
      ∏ P ∈ S, (1 + reflectionPowerWeight β P) := by
  simp_rw [powerWeight_prod]
  exact (Finset.prod_one_add S).symm

def weightedReflectionLocalMass (β : ℝ) (P : Ideal (𝓞 K)) : ℝ :=
  (1 + reflectionPowerWeight β P) / (1 - reflectionPowerWeight β P)

private theorem weightedLocalMass_nonneg {β : ℝ} (hβ : 0 < β)
    (P : Ideal (𝓞 K)) (hP : Prime P) : 0 ≤ weightedReflectionLocalMass β P :=
  div_nonneg (by linarith [reflectionPowerWeight_nonneg β P])
    (sub_pos.mpr (prime_powerWeight_lt_one hβ P hP)).le

/-- The full deletion/restoration mass is controlled by its actual Euler
product, not by the number of original rows. -/
theorem weightedDoubleMass_le_euler (β : ℝ) (hβ : 0 < β)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P) :
    (∑ D ∈ S.powerset, ∑' I : SmoothIdeal S,
        reflectionPowerWeight β (∏ P ∈ D, P) * reflectionPowerWeight β I.val.val) ≤
      ∏ P ∈ S, weightedReflectionLocalMass β P := by
  have hD (D : Finset (Ideal (𝓞 K))) :
      (∑' I : SmoothIdeal S,
          reflectionPowerWeight β (∏ P ∈ D, P) * reflectionPowerWeight β I.val.val) ≤
        reflectionPowerWeight β (∏ P ∈ D, P) *
          (∏ P ∈ S, (1 - reflectionPowerWeight β P)⁻¹) := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (weightedSmoothMass_le_euler β hβ S hS)
      (reflectionPowerWeight_nonneg β _)
  apply (Finset.sum_le_sum (fun D _ => hD D)).trans_eq
  rw [← Finset.sum_mul, weightedDeletionMass_eq_euler, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P _
  exact (div_eq_mul_inv _ _).symm

/-- Every fixed positive exponent gives an arbitrarily small power of
the norm of the actual deleted radical. Constants precede the prime set. -/
theorem weightedEulerMass_subpower (β ε : ℝ) (hβ : 0 < β) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal (𝓞 K)))
      (hS : ∀ P ∈ S, Prime P),
      (∏ P ∈ S, weightedReflectionLocalMass β P) ≤
        C * (Ideal.absNorm (∏ P ∈ S, P) : ℝ) ^ ε := by
  let r : ℝ := (2 : ℝ) ^ (-β)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hβ)
  let B : ℝ := (1 + r) / (1 - r)
  have hB1 : 1 ≤ B := (le_div_iff₀ (sub_pos.mpr hr1)).mpr (by linarith)
  have hBpos : 0 < B := zero_lt_one.trans_le hB1
  obtain ⟨Nβ, hNβ⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hβ).eventually (Filter.eventually_ge_atTop (2 : ℝ)))
  obtain ⟨Nε, hNε⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hε).eventually (Filter.eventually_ge_atTop (3 : ℝ)))
  let N : ℕ := ⌈max 2 (max Nβ Nε)⌉₊
  let small := idealsUpTo K N
  have hN : max 2 (max Nβ Nε) ≤ (N : ℝ) := Nat.le_ceil _
  refine ⟨B ^ small.card, pow_pos hBpos _, ?_⟩
  intro S hS
  have hpoint (P : Ideal (𝓞 K)) (hP : P ∈ S) :
      weightedReflectionLocalMass β P ≤
        (if P ∈ small then B else 1) * (P.absNorm : ℝ) ^ ε := by
    have htwo : (2 : ℝ) ≤ P.absNorm := by exact_mod_cast prime_norm_two_le P (hS P hP)
    have hweight : reflectionPowerWeight β P ≤ r :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) htwo (neg_nonpos.mpr hβ.le)
    have hden : 0 < 1 - reflectionPowerWeight β P :=
      sub_pos.mpr (prime_powerWeight_lt_one hβ P (hS P hP))
    have hlocal : weightedReflectionLocalMass β P ≤ B := by
      apply (div_le_div_iff₀ hden (sub_pos.mpr hr1)).mpr
      nlinarith
    have hpower : 1 ≤ (P.absNorm : ℝ) ^ ε :=
      Real.one_le_rpow (by linarith) hε.le
    by_cases hp : P ∈ small
    · simp only [if_pos hp]
      exact hlocal.trans (le_mul_of_one_le_right hBpos.le hpower)
    · have hlarge : (N : ℝ) < P.absNorm := by
        have hh : ¬P.absNorm ≤ N := by
          intro hn
          apply hp
          simpa [small, idealsUpTo] using hn
        exact_mod_cast Nat.lt_of_not_ge hh
      have hb : Nβ ≤ (P.absNorm : ℝ) :=
        (le_max_left Nβ Nε).trans ((le_max_right 2 (max Nβ Nε)).trans (hN.trans hlarge.le))
      have he : Nε ≤ (P.absNorm : ℝ) :=
        (le_max_right Nβ Nε).trans ((le_max_right 2 (max Nβ Nε)).trans (hN.trans hlarge.le))
      have hhalf : reflectionPowerWeight β P ≤ 1 / 2 := by
        unfold reflectionPowerWeight
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        simpa only [inv_eq_one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) (hNβ _ hb)
      have hthree : weightedReflectionLocalMass β P ≤ 3 := by
        apply (div_le_iff₀ hden).mpr
        linarith
      simpa only [if_neg hp, one_mul] using hthree.trans (hNε _ he)
  have hcard : (S.filter (· ∈ small)).card ≤ small.card :=
    Finset.card_le_card (fun P hP => (Finset.mem_filter.mp hP).2)
  calc
    _ ≤ ∏ P ∈ S, ((if P ∈ small then B else 1) * (P.absNorm : ℝ) ^ ε) :=
      Finset.prod_le_prod₀ (fun P hP => weightedLocalMass_nonneg hβ P (hS P hP)) hpoint
    _ = B ^ (S.filter (· ∈ small)).card * (Ideal.absNorm (∏ P ∈ S, P) : ℝ) ^ ε := by
      rw [Finset.prod_mul_distrib, ← Finset.prod_filter]
      simp only [Finset.prod_const,
        Real.finsetProd_rpow S _ (fun _ _ => Nat.cast_nonneg _) ε, map_prod, Nat.cast_prod]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 hcard)
      (Real.rpow_nonneg (by positivity) _)

/-- The full weighted mass theorem with actual summability. Instantiating
`β = 1/4` supplies both ordinary reflected Mellin lines. -/
theorem weightedDoubleMass_subpower (β ε : ℝ) (hβ : 0 < β) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal (𝓞 K)))
      (hS : ∀ P ∈ S, Prime P),
      Summable (fun I : SmoothIdeal S => ∑ D ∈ S.powerset,
        reflectionPowerWeight β (∏ P ∈ D, P) * reflectionPowerWeight β I.val.val) ∧
      (∑ D ∈ S.powerset, ∑' I : SmoothIdeal S,
        reflectionPowerWeight β (∏ P ∈ D, P) * reflectionPowerWeight β I.val.val) ≤
          C * (Ideal.absNorm (∏ P ∈ S, P) : ℝ) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := weightedEulerMass_subpower (K := K) β ε hβ hε
  refine ⟨C, hC, fun S hS => ⟨?_,
    (weightedDoubleMass_le_euler β hβ S hS).trans (hbound S hS)⟩⟩
  exact summable_sum (fun D _ =>
    (weightedSmoothSummable β hβ S hS).mul_left (reflectionPowerWeight β (∏ P ∈ D, P)))

/-- On the two noncentral reflection lines, both the deletion and the
restoration weight are bounded by the same fixed positive exponent. -/
theorem mixedReflectionWeight_le (β σ : ℝ) (hlower : β ≤ σ)
    (hupper : σ ≤ 1 - β) (D H : HeckePort.Moments.NI K) :
    (D.val.absNorm : ℝ) ^ (-σ) * (H.val.absNorm : ℝ) ^ (σ - 1) ≤
      reflectionPowerWeight β D.val * reflectionPowerWeight β H.val := by
  have hD : (1 : ℝ) ≤ D.val.absNorm := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero
      (fun hz => D.property (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hH : (1 : ℝ) ≤ H.val.absNorm := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero
      (fun hz => H.property (Ideal.absNorm_eq_zero_iff.mp hz)))
  exact mul_le_mul
    (Real.rpow_le_rpow_of_exponent_le hD (neg_le_neg hlower))
    (Real.rpow_le_rpow_of_exponent_le hH (by linarith))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) (reflectionPowerWeight_nonneg β _)

/-- Uniform in the entire closed pair of Mellin lines `[β,1-β]`.
For `β=1/4`, this directly controls the actual weights
`N(D)^(-σ) N(H)^(σ-1)` at both 1/4 and 3/4. -/
theorem weightedMixedMass_subpower (β ε : ℝ) (hβ : 0 < β) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal (𝓞 K)))
      (hS : ∀ P ∈ S, Prime P) (σ : ℝ), β ≤ σ → σ ≤ 1 - β →
      Summable (fun I : SmoothIdeal S => ∑ D ∈ S.powerset,
        (Ideal.absNorm (∏ P ∈ D, P) : ℝ) ^ (-σ) * (I.val.val.absNorm : ℝ) ^ (σ - 1)) ∧
      (∑ D ∈ S.powerset, ∑' I : SmoothIdeal S,
        (Ideal.absNorm (∏ P ∈ D, P) : ℝ) ^ (-σ) * (I.val.val.absNorm : ℝ) ^ (σ - 1)) ≤
          C * (Ideal.absNorm (∏ P ∈ S, P) : ℝ) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := weightedDoubleMass_subpower (K := K) β ε hβ hε
  refine ⟨C, hC, ?_⟩
  intro S hS σ hlower hupper
  have hterm (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset)
      (I : SmoothIdeal S) :
      (Ideal.absNorm (∏ P ∈ D, P) : ℝ) ^ (-σ) * (I.val.val.absNorm : ℝ) ^ (σ - 1) ≤
        reflectionPowerWeight β (∏ P ∈ D, P) * reflectionPowerWeight β I.val.val :=
    mixedReflectionWeight_le β σ hlower hupper
      ⟨∏ P ∈ D, P, subset_product_nonzero D
        (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP))⟩ I.val
  have hsum (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset) :
      Summable (fun I : SmoothIdeal S =>
        (Ideal.absNorm (∏ P ∈ D, P) : ℝ) ^ (-σ) * (I.val.val.absNorm : ℝ) ^ (σ - 1)) := by
    apply ((weightedSmoothSummable β hβ S hS).mul_left
      (reflectionPowerWeight β (∏ P ∈ D, P))).of_nonneg_of_le
    · exact fun _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · exact hterm D hD
  refine ⟨summable_sum hsum, ?_⟩
  apply (Finset.sum_le_sum (fun D hD =>
    (hsum D hD).tsum_le_tsum (hterm D hD)
      ((weightedSmoothSummable β hβ S hS).mul_left
        (reflectionPowerWeight β (∏ P ∈ D, P))))).trans
  exact (hbound S hS).2

end HeckeSkeleton.Moments.EngineInduction
