import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocationMass
import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorEpsilonBounds

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The true passive divisor and occurrence labels have subpower mass

The finite carrier is the one restored by N2.  Its compatibility filter
can only remove labels.  No new copy of an allocation label is inserted,
and the two original comparison bits contribute their exact factor four.
All constants are chosen before the ideal mask and smooth carriers.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField DedekindZetaZeroFree UniqueFactorizationMonoid
open HeckePort.IdealMobiusDivisorSum
open EngineStep

variable {K : Type} [Field K] [NumberField K]

namespace PassiveAllocation

variable {k : ℕ}

theorem sign_norm_le_one (a : Key K k) : ‖sign a‖ ≤ 1 := by
  simp only [sign, norm_mul, AllocationMass.norm_sign, mul_one]
  unfold UniqueFactorizationMonoid.moebius
  split_ifs <;> simp

theorem sign_norm_eq_one_of_ne_zero (a : Key K k) (ha : sign a ≠ 0) :
    ‖sign a‖ = 1 := by
  have hmu : (moebius a.1 : ℂ) ≠ 0 := (mul_ne_zero_iff.mp ha).1
  simp only [sign, norm_mul, AllocationMass.norm_sign, mul_one]
  unfold UniqueFactorizationMonoid.moebius at hmu ⊢
  split_ifs <;> simp_all

theorem label_sign_norm (B : Carrier K k) (mask : Ideal (𝓞 K))
    (a : labels B mask) : ‖sign a.val‖ = 1 :=
  sign_norm_eq_one_of_ne_zero a.val (Finset.mem_filter.mp a.property).2.1

theorem label_divisor_squarefree (B : Carrier K k) (mask : Ideal (𝓞 K))
    (a : labels B mask) : Squarefree a.val.1 := by
  have ha : sign a.val ≠ 0 := (Finset.mem_filter.mp a.property).2.1
  by_contra h
  apply ha
  simp [sign, UniqueFactorizationMonoid.moebius, h]

theorem label_divisor_ne_zero (B : Carrier K k) (mask : Ideal (𝓞 K))
    (a : labels B mask) : a.val.1 ≠ 0 :=
  (label_divisor_squarefree B mask a).ne_zero

theorem label_selection (B : Carrier K k) (mask : Ideal (𝓞 K))
    (a : labels B mask) :
    a.val.2 ∈ AllocationMass.idealAllocations a.val.1 (k + 2) :=
  (Finset.mem_sigma.mp (Finset.mem_filter.mp a.property).1).2

theorem sum_label_sign_norm (B : Carrier K k) (mask : Ideal (𝓞 K)) :
    (∑ a : labels B mask, ‖sign a.val‖) = ((labels B mask).card : ℝ) := by
  simp only [label_sign_norm, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, nsmul_eq_mul, mul_one]

private theorem norm_le_of_mem_divisors {mask D : Ideal (𝓞 K)}
    (hmask : mask ≠ 0) (hD : D ∈ idealDivisors mask) :
    (Ideal.absNorm D : ℝ) ≤ Ideal.absNorm mask := by
  have hdvd := (mem_idealDivisors hmask).mp hD
  obtain ⟨E, hE⟩ := hdvd
  have hn : 0 < Ideal.absNorm mask :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hmask)
  apply Nat.cast_le.mpr
  apply Nat.le_of_dvd hn
  exact ⟨Ideal.absNorm E, by rw [hE, map_mul]⟩

theorem candidates_card_bound (cap : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ mask : Ideal (𝓞 K), mask ≠ 0 →
      ∀ k : ℕ, k ≤ cap →
        ((candidates mask k).card : ℝ) ≤ C * (Ideal.absNorm mask : ℝ) ^ ε := by
  obtain ⟨A, hA, halloc⟩ :=
    AllocationMass.ideal_allocation_card_bound K (cap + 2) (ε / 2) (by positivity)
  obtain ⟨D, hD, hdiv⟩ :=
    LargeSieve.ideal_divisor_count_le_rpow K (ε / 2) (by positivity)
  refine ⟨A * D, mul_pos hA (zero_lt_one.trans_le hD), ?_⟩
  intro mask hmask k hk
  have hn : 0 < (Ideal.absNorm mask : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hmask)
  have hfactor : 0 ≤ A * (Ideal.absNorm mask : ℝ) ^ (ε / 2) :=
    mul_nonneg hA.le (Real.rpow_nonneg hn.le _)
  have hone (I : Ideal (𝓞 K)) (hI : I ∈ idealDivisors mask) :
      ((AllocationMass.idealAllocations I (k + 2)).card : ℝ) ≤
        A * (Ideal.absNorm mask : ℝ) ^ (ε / 2) := by
    have hI0 : I ≠ 0 := ne_zero_of_dvd_ne_zero hmask ((mem_idealDivisors hmask).mp hI)
    exact (halloc I hI0 (k + 2) (Nat.add_le_add_right hk 2)).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (norm_le_of_mem_divisors hmask hI)
          (by positivity)) hA.le)
  calc
    _ = ∑ I ∈ idealDivisors mask,
        ((AllocationMass.idealAllocations I (k + 2)).card : ℝ) := by
      rw [candidates, Finset.card_sigma, Nat.cast_sum]
    _ ≤ ∑ _I ∈ idealDivisors mask,
        A * (Ideal.absNorm mask : ℝ) ^ (ε / 2) := Finset.sum_le_sum hone
    _ = ((idealDivisors mask).card : ℝ) *
        (A * (Ideal.absNorm mask : ℝ) ^ (ε / 2)) := by simp
    _ ≤ (D * (Ideal.absNorm mask : ℝ) ^ (ε / 2)) *
        (A * (Ideal.absNorm mask : ℝ) ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_right (hdiv mask) hfactor
    _ = (A * D) * (Ideal.absNorm mask : ℝ) ^ ε := by
      rw [show ε = ε / 2 + ε / 2 by ring, Real.rpow_add hn]
      ring

theorem labels_card_bound (cap : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ mask : Ideal (𝓞 K), mask ≠ 0 →
      ∀ k : ℕ, k ≤ cap → ∀ B : Carrier K k,
        ((labels B mask).card : ℝ) ≤ C * (Ideal.absNorm mask : ℝ) ^ ε := by
  obtain ⟨C, hC, hb⟩ := candidates_card_bound (K := K) cap ε hε
  refine ⟨C, hC, ?_⟩
  intro mask hmask k hk B
  exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (hb mask hmask k hk)

/-- This theorem concerns the exact signed labels, including the
actual compatibility filter, and is uniform over both smooth carriers. -/
theorem labels_mass_bound (cap : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ mask : Ideal (𝓞 K), mask ≠ 0 →
      ∀ k : ℕ, k ≤ cap → ∀ B : Carrier K k,
        (∑ a : labels B mask, ‖sign a.val‖) ≤
          C * (Ideal.absNorm mask : ℝ) ^ ε := by
  obtain ⟨C, hC, hb⟩ := labels_card_bound (K := K) cap ε hε
  refine ⟨C, hC, ?_⟩
  intro mask hmask k hk B
  rw [sum_label_sign_norm]
  exact hb mask hmask k hk B

theorem labels_card_power_scale (cap : ℕ) (A ε : ℝ)
    (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ mask : Ideal (𝓞 K),
      (Ideal.absNorm mask : ℝ) ≤ Z ^ A → ∀ k : ℕ, k ≤ cap →
        ∀ B : Carrier K k, ((labels B mask).card : ℝ) ≤ C * Z ^ ε := by
  let δ : ℝ := ε / (A + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C, hC, hb⟩ := labels_card_bound (K := K) cap δ hδ
  refine ⟨C, hC, ?_⟩
  intro Z hZ mask hmask k hk B
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  by_cases hm : mask = 0
  · subst mask
    have hzcard : ((labels B (0 : Ideal (𝓞 K))).card : ℝ) = 0 := by
      simp [labels, candidates, Ideal.zero_eq_bot, LargeSieve.idealDivisors_bot]
    rw [hzcard]
    exact mul_nonneg hC.le (Real.rpow_nonneg hz.le _)
  have he : A * δ ≤ ε := by
    have hid : δ * (A + 1) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith
  calc
    _ ≤ C * (Ideal.absNorm mask : ℝ) ^ δ := hb mask hm k hk B
    _ ≤ C * (Z ^ A) ^ δ :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hmask hδ.le) hC.le
    _ = C * Z ^ (A * δ) := by rw [← Real.rpow_mul hz.le]
    _ ≤ C * Z ^ ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ he) hC.le

end PassiveAllocation

namespace OrdinaryData.PassiveSupport

open HeckeGeneral.ThetaSkeleton.Global

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p} {O : OrdinaryData packet}
variable {input : ProfileInput call} (support : O.PassiveSupport input)

/-- Each of the two original comparison bits occurs once, even when a
comparison profile happens to vanish.  Subsequent activity filtering
can remove that zero branch but cannot multiply its outer coefficient. -/
theorem outer_eq_leaf_weight (b : support.Label) :
    support.outer b = packet.leaf.weight := by
  simp only [outer, PassiveAllocation.label_sign_norm, mul_one]

theorem sum_outer :
    (∑ b : support.Label, support.outer b) =
      4 * packet.leaf.weight * ((support.labels false).card : ℝ) *
        ((support.labels true).card : ℝ) := by
  simp only [outer_eq_leaf_weight, Finset.sum_const, Finset.card_univ,
    Label, Fintype.card_prod, Fintype.card_coe, Fintype.card_bool,
    nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  ring

end OrdinaryData.PassiveSupport
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveAllocation.candidates_card_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveAllocation.labels_mass_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryData.PassiveSupport.sum_outer
