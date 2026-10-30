import HeckeGeneral.Analysis.TIPSources
import HeckeGeneral.Analysis.TIPNumerics

/-!
# The accounting of M Section 7, from the Euler-product bound

From T, I and P at a common boundary `7/8 < B ≤ 1`, with the pretarget choices
of the closure, the actual normalized probe and the actual principal signal
satisfy the power-height comparison with the common saving `tipFinalSaving g B`.
Row counts are derived from the witnesses and the two moments
(`WitnessRowCount`, `TIPNumerics`), inserted in the conditional single-bin
estimate of T, and compared with the certificate and range margins of
M Table 7.3.  Four block types occur: the floor bin; large bins `δ > 5/6`
(witness parameter `3/2`, no selected slots); bins `δ ≤ 5/6` in shells
`d ≤ 1/2` (witness parameter `1`, no selected slots); and bins `δ ≤ 5/6` in
shells `d > 1/2` (balanced witness parameter, selected slots).
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.TIP

open NumberField IsDedekindDomain MeasureTheory Filter Asymptotics
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open OAI.SevenEighths.Endpoint (balancedRowCount balancedCutoff)
open scoped BigOperators Topology Classical

variable {K : Type} [Field K] [NumberField K]

private lemma certificateMargin_eq : certificateMargin = 49 / 440640 := rfl

/-- The common saving: `0 < σ ≤ Δ/4`, `8σ ≤ c₀` and `8σ ≤ principalSlotSaving g`. -/
private lemma tipFinalSaving_facts (g : PrimeWindowGeometry) {B : ℝ} (hB : 7 / 8 < B) :
    0 < tipFinalSaving g B ∧ tipFinalSaving g B ≤ (B - 7 / 8) / 4 ∧
      8 * tipFinalSaving g B ≤ certificateMargin ∧
      8 * tipFinalSaving g B ≤ principalSlotSaving g := by
  have hc : 0 < certificateMargin := by rw [certificateMargin_eq]; norm_num
  have hp := principalSlotSaving_pos g
  have h1 : tipFinalSaving g B ≤ tipSaving g := min_le_left _ _
  have h2 : tipFinalSaving g B ≤ (B - 7 / 8) / 4 := min_le_right _ _
  have h3 : tipSaving g ≤ (1 / 8) * certificateMargin := by
    unfold tipSaving
    have := min_le_left certificateMargin (principalSlotSaving g)
    linarith
  have h4 : tipSaving g ≤ (1 / 8) * principalSlotSaving g := by
    unfold tipSaving
    have := min_le_right certificateMargin (principalSlotSaving g)
    linarith
  have h5 : 0 < tipSaving g := by
    unfold tipSaving
    have := lt_min hc hp
    linarith
  exact ⟨lt_min h5 (by linarith), h2, by linarith, by linarith⟩

/-- The outer-row margins consume the source loss σ/2 and leave 2σ.
The revised small-row margin is 1/50; the retained large-row margin is 63/800. -/
private lemma tipFinalSaving_outer_margins (g : PrimeWindowGeometry)
    {B : ℝ} (hB : 7 / 8 < B) :
    (5 / 2) * tipFinalSaving g B ≤ 1 / 50 ∧
      (5 / 2) * tipFinalSaving g B ≤ 63 / 800 := by
  have hσc := (tipFinalSaving_facts g hB).2.2.1
  rw [certificateMargin_eq] at hσc
  constructor <;> linarith

/-- Passing a moment bound to larger common constants. -/
private lemma weaken_bound {S k k' X H H' : ℝ} (h : S ≤ k * X * H) (hk : 0 ≤ k)
    (hkk : k ≤ k') (hX : 0 ≤ X) (hH : 0 ≤ H) (hHH : H ≤ H') : S ≤ k' * X * H' := by
  refine h.trans ?_
  have h1 : k * X ≤ k' * X := mul_le_mul_of_nonneg_right hkk hX
  exact mul_le_mul h1 hHH hH ((mul_nonneg hk hX).trans h1)

/-- Summing a count per witness subdivision over the witness cover of
Q `prop:detector-witness`. -/
private lemma card_le_of_witnessCover {Row : Type} {J₀ : ℕ} (A : AmplitudeSet Row J₀)
    {t δ U lam k K R H : ℝ} (hU : 0 < U) (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hcov : WitnessCover A t δ U lam k)
    (hsub : ∀ j, ((A.subdivision t j).rows.card : ℝ) ≤ K * U ^ R * H) :
    (A.rows.card : ℝ) ≤ k * K * U ^ (R + lam) * H := by
  obtain ⟨hcount, hcover, -⟩ := hcov
  have hsubset : A.rows ⊆ Finset.univ.biUnion (fun j => (A.subdivision t j).rows) := by
    intro u hu
    obtain ⟨j, hj⟩ := hcover u hu
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hj⟩
  have h1 : (A.rows.card : ℝ) ≤ ∑ j, ((A.subdivision t j).rows.card : ℝ) := by
    have h := (Finset.card_le_card hsubset).trans Finset.card_biUnion_le
    exact_mod_cast h
  have h2 : ∑ j, ((A.subdivision t j).rows.card : ℝ) ≤
      ∑ _j : Fin (A.subdivisionCount t), K * U ^ R * H :=
    Finset.sum_le_sum fun j _ => hsub j
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
  have hX : 0 ≤ K * U ^ R * H := mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hU.le _)) hH
  calc (A.rows.card : ℝ) ≤ (A.subdivisionCount t : ℝ) * (K * U ^ R * H) := h1.trans h2
    _ ≤ k * U ^ lam * (K * U ^ R * H) := mul_le_mul_of_nonneg_right hcount hX
    _ = k * K * U ^ (R + lam) * H := by rw [Real.rpow_add hU]; ring

/-- Slot lengths at base `Z^d` in the upper shells `1/2 < d ≤ 13/16 + λ`. -/
private lemma slotLength_facts {J : ℕ} (hJ : 0 < J) {d lamA : ℝ} (hd : 1 / 2 < d)
    (hdhi : d ≤ 13 / 16 + lamA) (hlamA1 : lamA ≤ 1 / 1000) :
    0 < slotLength J d ∧ slotLength J d ≤ (1 / 3 : ℝ) / J ∧
      (7 / 37 : ℝ) ≤ J * slotLength J d := by
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hd0 : 0 < d := by linarith
  have hJd : (0 : ℝ) < J * d := mul_pos hJ' hd0
  unfold slotLength
  refine ⟨div_pos (by norm_num) hJd, ?_, ?_⟩
  · rw [div_le_div_iff₀ hJd hJ']
    nlinarith [mul_lt_mul_of_pos_left hd hJ']
  · have e : (J : ℝ) * (1 / 6 / (J * d)) = 1 / 6 / d * (J / J) := by ring
    rw [e, div_self hJ'.ne', mul_one, le_div_iff₀ hd0]
    linarith

/-- The mean of amplitudes in `[0, c]` lies in `[0, c]`. -/
private lemma mean_bounds {Row : Type} {J₀ : ℕ} (hJ : 0 < J₀) (A : AmplitudeSet Row J₀)
    {c : ℝ} (hamp : ∀ i, 0 ≤ A.amplitude i ∧ A.amplitude i ≤ c) :
    0 ≤ A.mean ∧ A.mean ≤ c := by
  have hJ' : (0 : ℝ) < J₀ := by exact_mod_cast hJ
  unfold AmplitudeSet.mean
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ => (hamp i).1) hJ'.le
  · rw [div_le_iff₀ hJ']
    calc ∑ i, A.amplitude i ≤ ∑ _i : Fin J₀, c := Finset.sum_le_sum fun i _ => (hamp i).2
      _ = c * J₀ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- For equal slot lengths the mean amplitude is the length-weighted mean. -/
private lemma mean_mul_sum {Row : Type} {J₀ : ℕ} (hJ : 0 < J₀) (A : AmplitudeSet Row J₀)
    (s : ℝ) : A.mean * ∑ _i : Fin J₀, s = ∑ i : Fin J₀, s * A.amplitude i := by
  have hJ' : (J₀ : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  unfold AmplitudeSet.mean
  calc (∑ i, A.amplitude i) / J₀ * (J₀ * s) = s * (∑ i, A.amplitude i) * (J₀ / J₀) := by ring
    _ = s * ∑ i, A.amplitude i := by rw [div_self hJ', mul_one]

/-- The floor bin `a = 51/100`: the trivial count against the floor margin. -/
private lemma floor_exponent {d q Δ lamA : ℝ} (hd : 0 ≤ d) (hdhi : d ≤ 13 / 16 + lamA)
    (hq : q ≤ 1 / 100) (hlamA : 0 < lamA) (hlamA' : lamA ≤ certificateMargin / 40)
    (hΔ : 0 < Δ) :
    moderateExponent d (1 / 50) q 1 ≤ Δ - certificateMargin / 2 := by
  have hc := certificateMargin_eq
  have h := floor_bin_saving_extended hd hdhi hlamA.le hq le_rfl
  linarith

/-- Large bins `δ > 5/6`: the unselected count at `t = 3/2` against the large-bin margin. -/
private lemma large_exponent {d δ q Δ lamA : ℝ} (hd : 0 ≤ d) (hdhi : d ≤ 13 / 16 + lamA)
    (hδ0 : 5 / 6 ≤ δ) (hδ1 : δ ≤ 1) (hq : q ≤ δ / 2) (hlamA : 0 < lamA)
    (hlamA' : lamA ≤ certificateMargin / 40) (hΔ : 0 < Δ) :
    moderateExponent d δ q (1 - δ + (3 * lamA + 2 * lamA)) ≤
      Δ - certificateMargin / 2 := by
  have hc := certificateMargin_eq
  have h := large_bin_saving hd hdhi hlamA.le hδ0 hδ1 hq (ε := 5 * lamA)
    (R := 1 - δ + (3 * lamA + 2 * lamA)) (by linarith) (by linarith) (by linarith)
  linarith

/-- The middle shells `d ≤ 1/2`: the unselected count against the middle margin. -/
private lemma middle_exponent {d δ q Δ lamA : ℝ} (hd : 0 ≤ d) (hdhi : d ≤ 1 / 2)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hq : q ≤ δ / 2) (hlamA : 0 < lamA)
    (hlamA' : lamA ≤ certificateMargin / 40) (hΔ : 0 < Δ) :
    moderateExponent d δ q (1 - 2 * δ / 3 + (3 * lamA + 2 * lamA)) ≤
      Δ - certificateMargin / 2 := by
  have hc := certificateMargin_eq
  have h := middle_bin_saving hd hdhi hδ0 hδ1 hq
    (R := 1 - 2 * δ / 3 + (3 * lamA + 2 * lamA)) (by linarith)
  linarith

/-- The upper shells: the balanced count against the certificate margin, for every
dynamic capacity up to `κ = 1`. -/
private lemma balanced_exponent {d δ q Δ lamA : ℝ} (hd : 0 ≤ d) (hdhi : d ≤ 13 / 16 + lamA)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 5 / 6) (hq0 : 0 ≤ q) (hq1 : q ≤ δ / 2)
    (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1 / 8) (hlamA : 0 < lamA)
    (hlamA' : lamA ≤ certificateMargin / 40) :
    moderateExponent d δ q (balancedRowCount δ (1 / 2 - q / δ) + Δ / 4 + 20 * lamA) ≤
      Δ - certificateMargin / 2 := by
  have hc := certificateMargin_eq
  have hy0 : 0 ≤ 1 / 2 - q / δ := by
    rw [sub_nonneg, div_le_iff₀ hδ0]; linarith
  have hy1 : 1 / 2 - q / δ ≤ 1 / 2 := by
    have := div_nonneg hq0 hδ0.le; linarith
  have h := dynamic_moderate_range_saving_extended hd hdhi hδ0.le hδ1 hy0 hy1 hΔ0 hΔ1
    (ε := 20 * lamA) (by linarith) (by linarith) hlamA.le le_rfl
  have hq : δ * (1 / 2 - (1 / 2 - q / δ)) = q := by
    rw [sub_sub_cancel]; exact mul_div_cancel₀ q hδ0.ne'
  rw [hq] at h
  linarith

/-- Middle shells: the unselected count of Q 15438 summed over the cover at `t = 1`. -/
private lemma middle_set_count {Row : Type} {J₀ : ℕ} (A : AmplitudeSet Row J₀)
    {lamA kT kI kP AI AP Z T₁ d δ : ℝ}
    (hU : 1 < Z ^ d) (hδ0 : 0 < δ) (hδ1 : δ ≤ 5 / 6) (hlamA : 0 < lamA) (hT₁ : 1 ≤ T₁)
    (hkI : 0 ≤ kI) (hkP : 0 ≤ kP)
    (hcov : WitnessCover A 1 δ (Z ^ d) lamA kT)
    (hIamp : ∀ j : Fin (A.subdivisionCount 1),
      ∑ u ∈ (A.subdivision 1 j).rows, ‖(A.subdivision 1 j).inverseValue u‖ ^ 2 ≤
        kI * (Z ^ d) ^ (amplifiedInverseExponent (A.subdivision 1 j).inverseLength + lamA) *
          (1 + T₁) ^ AI)
    (hP0 : ∀ j : Fin (A.subdivisionCount 1),
      ∑ u ∈ (A.subdivision 1 j).rows, ‖(A.subdivision 1 j).plainValue u ^ 2‖ ^ 2 ≤
        kP * (Z ^ d) ^ (1 + lamA) * (1 + T₁) ^ AP) :
    (A.rows.card : ℝ) ≤ kT * (kI + kP + 1) *
      (Z ^ d) ^ ((1 - 2 * δ / 3 + (3 * lamA + 2 * lamA)) + lamA) * (1 + T₁) ^ max AI AP := by
  have hU0 : 0 < Z ^ d := by linarith
  have hT0 : (0 : ℝ) ≤ 1 + T₁ := by linarith
  have hH0 : (0 : ℝ) ≤ (1 + T₁) ^ max AI AP := Real.rpow_nonneg hT0 _
  have hHI : (1 + T₁) ^ AI ≤ (1 + T₁) ^ max AI AP :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
  have hHP : (1 + T₁) ^ AP ≤ (1 + T₁) ^ max AI AP :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_right _ _)
  have hK0 : 0 ≤ kI + kP + 1 := by linarith
  refine card_le_of_witnessCover A hU0 hK0 hH0 hcov fun j => ?_
  obtain ⟨-, -, hj⟩ := hcov
  obtain ⟨-, hr0, hm0, hrt, hrmt, hMs, hSs⟩ := hj j
  exact witness_row_count_unselected _ _ _ hU hδ0 hδ1 hr0 hm0 hrt hrmt hlamA.le hlamA.le
    hK0 hH0 hMs hSs
    (weaken_bound (hIamp j) hkI (by linarith) (Real.rpow_nonneg hU0.le _)
      (Real.rpow_nonneg hT0 _) hHI)
    (weaken_bound (hP0 j) hkP (by linarith) (Real.rpow_nonneg hU0.le _)
      (Real.rpow_nonneg hT0 _) hHP)

/-- Large bins: the unselected count at witness parameter `3/2` summed over the cover. -/
private lemma large_set_count {Row : Type} {J₀ : ℕ} (A : AmplitudeSet Row J₀)
    {lamA kT kI kP AI AP Z T₁ d δ : ℝ}
    (hU : 1 < Z ^ d) (hδ0 : 5 / 6 ≤ δ) (hδ1 : δ ≤ 1) (hlamA : 0 < lamA) (hT₁ : 1 ≤ T₁)
    (hkI : 0 ≤ kI) (hkP : 0 ≤ kP)
    (hcov : WitnessCover A (3 / 2) δ (Z ^ d) lamA kT)
    (hIamp : ∀ j : Fin (A.subdivisionCount (3 / 2)),
      ∑ u ∈ (A.subdivision (3 / 2) j).rows, ‖(A.subdivision (3 / 2) j).inverseValue u‖ ^ 2 ≤
        kI * (Z ^ d) ^ (amplifiedInverseExponent (A.subdivision (3 / 2) j).inverseLength +
          lamA) * (1 + T₁) ^ AI)
    (hP0 : ∀ j : Fin (A.subdivisionCount (3 / 2)),
      ∑ u ∈ (A.subdivision (3 / 2) j).rows, ‖(A.subdivision (3 / 2) j).plainValue u ^ 2‖ ^ 2 ≤
        kP * (Z ^ d) ^ (1 + lamA) * (1 + T₁) ^ AP) :
    (A.rows.card : ℝ) ≤ kT * (kI + kP + 1) *
      (Z ^ d) ^ ((1 - δ + (3 * lamA + 2 * lamA)) + lamA) * (1 + T₁) ^ max AI AP := by
  have hU0 : 0 < Z ^ d := by linarith
  have hT0 : (0 : ℝ) ≤ 1 + T₁ := by linarith
  have hH0 : (0 : ℝ) ≤ (1 + T₁) ^ max AI AP := Real.rpow_nonneg hT0 _
  have hHI : (1 + T₁) ^ AI ≤ (1 + T₁) ^ max AI AP :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
  have hHP : (1 + T₁) ^ AP ≤ (1 + T₁) ^ max AI AP :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_right _ _)
  have hK0 : 0 ≤ kI + kP + 1 := by linarith
  refine card_le_of_witnessCover A hU0 hK0 hH0 hcov fun j => ?_
  obtain ⟨-, -, hj⟩ := hcov
  obtain ⟨-, hr0, hm0, -, hrmt, hMs, hSs⟩ := hj j
  exact witness_row_count_large _ _ _ hU hδ0 hδ1 hr0 hm0 hrmt hlamA.le hlamA.le
    hK0 hH0 hMs hSs
    (weaken_bound (hIamp j) hkI (by linarith) (Real.rpow_nonneg hU0.le _)
      (Real.rpow_nonneg hT0 _) hHI)
    (weaken_bound (hP0 j) hkP (by linarith) (Real.rpow_nonneg hU0.le _)
      (Real.rpow_nonneg hT0 _) hHP)

/-- Upper shells: the balanced count of Q `eq:target-cutoff` summed over the cover at the
balanced witness parameter, with all slots, slot length `slotLength J₀ d` and losses `λ`. -/
private lemma balanced_set_count {Row : Type} {J₀ : ℕ} (hJ₀ : 0 < J₀) (A : AmplitudeSet Row J₀)
    {B lamA mesh kT kI kP AI AP Z T₁ d δ t : ℝ}
    (hB : 7 / 8 < B) (hB' : B ≤ 1) (hZ : 1 < Z) (hd : 1 / 2 < d)
    (hdhi : d ≤ 13 / 16 + lamA) (hδ0 : 0 < δ) (hδ1 : δ ≤ 5 / 6)
    (hlamA : 0 < lamA) (hlam1 : lamA ≤ 1 / 1000)
    (hmesh : (1 / 3 : ℝ) / J₀ ≤ mesh) (hround : (1 / 3 : ℝ) / J₀ ≤ lamA)
    (hT₁ : 1 ≤ T₁) (hkI : 0 ≤ kI) (hkP : 0 ≤ kP)
    (hamp : ∀ i, 0 ≤ A.amplitude i ∧ A.amplitude i ≤ δ / 2)
    (hslot : ∀ i, 0 < A.amplitude i → ∀ u ∈ A.rows,
      Z ^ ((1 / 6) / J₀ * A.amplitude i) ≤ ‖A.slotValue i u‖)
    (ht : t = balancedCutoff δ (1 / 2 - A.mean / δ))
    (hcov : WitnessCover A t δ (Z ^ d) lamA kT)
    (hIsel : ∀ j : Fin (A.subdivisionCount t), ∀ I : Finset (Fin J₀),
      (A.subdivision t j).inverseLength + 2 * ∑ _i ∈ I, slotLength J₀ d ≤ 1 - 2 * lamA →
      2 * (A.subdivision t j).inverseLength + 8 * ∑ _i ∈ I, slotLength J₀ d ≤ 3 - 2 * lamA →
      ∑ u ∈ (A.subdivision t j).rows,
          ‖(A.subdivision t j).inverseValue u * ∏ i ∈ I, A.slotValue i u‖ ^ 2 ≤
        kI * (Z ^ d) ^ (1 + lamA) * (1 + T₁) ^ AI)
    (hIamp : ∀ j : Fin (A.subdivisionCount t),
      ∑ u ∈ (A.subdivision t j).rows, ‖(A.subdivision t j).inverseValue u‖ ^ 2 ≤
        kI * (Z ^ d) ^ (amplifiedInverseExponent (A.subdivision t j).inverseLength + lamA) *
          (1 + T₁) ^ AI)
    (hPsel : ∀ j : Fin (A.subdivisionCount t), ∀ I : Finset (Fin J₀),
      (∀ _i ∈ I, slotLength J₀ d ≤ mesh) →
      2 * (A.subdivision t j).plainLength + 6 * (2 * B - 1) * ∑ _i ∈ I, slotLength J₀ d ≤ 1 →
      ∑ u ∈ (A.subdivision t j).rows,
          ‖(A.subdivision t j).plainValue u ^ 2 * ∏ i ∈ I, A.slotValue i u‖ ^ 2 ≤
        kP * (Z ^ d) ^ (1 + lamA) * (1 + T₁) ^ AP)
    (hP0 : ∀ j : Fin (A.subdivisionCount t),
      ∑ u ∈ (A.subdivision t j).rows, ‖(A.subdivision t j).plainValue u ^ 2‖ ^ 2 ≤
        kP * (Z ^ d) ^ (1 + lamA) * (1 + T₁) ^ AP) :
    (A.rows.card : ℝ) ≤ kT * (kI + kP + 1) *
      (Z ^ d) ^ ((balancedRowCount δ (1 / 2 - A.mean / δ) + (B - 7 / 8) / 4 + 20 * lamA) +
        lamA) * (1 + T₁) ^ max AI AP := by
  subst ht
  have hshpos : 0 < d := by linarith
  have hU : 1 < Z ^ d := Real.one_lt_rpow hZ hshpos
  have hU0 : 0 < Z ^ d := by linarith
  have hZ0 : (0 : ℝ) ≤ Z := by linarith
  have hT0 : (0 : ℝ) ≤ 1 + T₁ := by linarith
  have hH0 : (0 : ℝ) ≤ (1 + T₁) ^ max AI AP := Real.rpow_nonneg hT0 _
  have hHI : (1 + T₁) ^ AI ≤ (1 + T₁) ^ max AI AP :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
  have hHP : (1 + T₁) ^ AP ≤ (1 + T₁) ^ max AI AP :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_right _ _)
  have hK0 : 0 ≤ kI + kP + 1 := by linarith
  obtain ⟨hs0, hsJ, hsupply⟩ := slotLength_facts hJ₀ hd hdhi hlam1
  have hsmesh : slotLength J₀ d ≤ mesh := hsJ.trans hmesh
  have hδs : δ * slotLength J₀ d ≤ lamA :=
    (mul_le_of_le_one_left hs0.le (by linarith)).trans (hsJ.trans hround)
  obtain ⟨hq0, hq1⟩ := mean_bounds hJ₀ A hamp
  have hsup : (7 / 37 : ℝ) ≤ ∑ _i : Fin J₀, slotLength J₀ d := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact hsupply
  refine card_le_of_witnessCover A hU0 hK0 hH0 hcov fun j => ?_
  obtain ⟨-, -, hj⟩ := hcov
  obtain ⟨hsub, hr0, hm0, hrt, hrmt, hMs, hSs⟩ := hj j
  have hQ : ∀ i ∈ (Finset.univ : Finset (Fin J₀)), 0 < A.amplitude i →
      ∀ u ∈ (A.subdivision (balancedCutoff δ (1 / 2 - A.mean / δ)) j).rows,
        (Z ^ d) ^ (slotLength J₀ d * A.amplitude i) ≤ ‖A.slotValue i u‖ := by
    intro i _ hi u hu
    have e : d * (slotLength J₀ d * A.amplitude i) = (1 / 6) / J₀ * A.amplitude i := by
      calc d * (slotLength J₀ d * A.amplitude i) =
          1 / 6 / J₀ * A.amplitude i * (d / d) := by unfold slotLength; ring
        _ = 1 / 6 / J₀ * A.amplitude i := by rw [div_self hshpos.ne', mul_one]
    rw [← Real.rpow_mul hZ0, e]
    exact hslot i hi u (hsub hu)
  have hw := witness_row_count_balanced
    (A.subdivision (balancedCutoff δ (1 / 2 - A.mean / δ)) j).rows Finset.univ
    (fun _ => slotLength J₀ d) A.amplitude A.slotValue
    (A.subdivision (balancedCutoff δ (1 / 2 - A.mean / δ)) j).inverseValue
    (A.subdivision (balancedCutoff δ (1 / 2 - A.mean / δ)) j).plainValue
    (Δ := B - 7 / 8) (ν := lamA) (wmax := slotLength J₀ d) (k := kI + kP + 1)
    (H := (1 + T₁) ^ max AI AP)
    hU hδ0 hδ1 (by linarith) (by linarith) hq0 hq1 (mean_mul_sum hJ₀ A (slotLength J₀ d))
    (fun _ _ => hs0) (fun i _ => (hamp i).1) (fun i _ => (hamp i).2) (fun _ _ => le_rfl)
    hs0.le hsup hr0 hm0 hrt hrmt hlamA.le hlamA.le (by linarith) hlamA (by linarith) hK0 hH0
    hMs hSs hQ
    (fun I _ h1 h2 => weaken_bound (hIsel j I h1 h2) hkI (by linarith)
      (Real.rpow_nonneg hU0.le _) (Real.rpow_nonneg hT0 _) hHI)
    (weaken_bound (hIamp j) hkI (by linarith) (Real.rpow_nonneg hU0.le _)
      (Real.rpow_nonneg hT0 _) hHI)
    (fun I _ hcap => weaken_bound (hPsel j I (fun _ _ => hsmesh)
        (by
          have e : (3 / 4 : ℝ) + 2 * (B - 7 / 8) = 2 * B - 1 := by ring
          rw [e] at hcap
          exact hcap))
      hkP (by linarith) (Real.rpow_nonneg hU0.le _) (Real.rpow_nonneg hT0 _) hHP)
    (weaken_bound (hP0 j) hkP (by linarith) (Real.rpow_nonneg hU0.le _)
      (Real.rpow_nonneg hT0 _) hHP)
  refine hw.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hU.le (by linarith)) hK0) hH0)

/-- One moderate block: count exponents `R ℓ ∈ [0, 2]` for all its amplitude sets, with
the row counts in the form required by T's single-bin estimate and every moderate
exponent at most `Δ - c₀/2`. -/
private lemma block_count_and_exponent {Row : Type} {g : PrimeWindowGeometry}
    (b : ModerateBlock Row g.slots) {B lamA mesh kT kI kP AI AP Z T₁ : ℝ}
    (hB : 7 / 8 < B) (hB' : B ≤ 1) (hlamA : 0 < lamA)
    (hlamA' : lamA ≤ certificateMargin / 40)
    (hmesh : (1 / 3 : ℝ) / g.slots ≤ mesh) (hround : (1 / 3 : ℝ) / g.slots ≤ lamA)
    (hZ : 2 ≤ Z) (hT₁ : 1 ≤ T₁) (hkT : 0 ≤ kT) (hkI : 0 ≤ kI) (hkP : 0 ≤ kP)
    (hAI : 0 ≤ AI)
    (hBS : BlockSource g b B lamA kT Z)
    (hfloorCount : ∀ ℓ, ((b.amplitudeSet ℓ).rows.card : ℝ) ≤
      kT * (Z ^ b.shell) ^ (1 + lamA))
    (hIS : InverseBlockSource g b lamA kI AI Z T₁)
    (hPS : PlainBlockSource g b B lamA mesh kP AP Z T₁) :
    ∃ R : b.Label → ℝ, (∀ ℓ, 0 ≤ R ℓ ∧ R ℓ ≤ 2) ∧
      (∀ ℓ, ((b.amplitudeSet ℓ).rows.card : ℝ) ≤
          kT * (kI + kP + 1) * (Z ^ b.shell) ^ (R ℓ + lamA) * (1 + T₁) ^ max AI AP) ∧
      (∀ ℓ, moderateExponent b.shell (2 * b.bin - 1) (b.amplitudeSet ℓ).mean (R ℓ) ≤
          B - 7 / 8 - certificateMargin / 2) := by
  obtain ⟨hsh0, hsh1, hbin0, hbin1, hlab⟩ := hBS
  have hc := certificateMargin_eq
  have hlam1 : lamA ≤ 1 / 1000 := by linarith
  have hZ1 : (1 : ℝ) < Z := by linarith
  have hshpos : 0 < b.shell := by linarith
  have hU : 1 < Z ^ b.shell := Real.one_lt_rpow hZ1 hshpos
  have hΔ : 0 < B - 7 / 8 := by linarith
  by_cases hfloor : b.bin = 51 / 100
  · -- the floor bin: the proved actual shell count
    refine ⟨fun _ => 1, fun _ => ⟨by norm_num, by norm_num⟩, fun ℓ => ?_, fun ℓ => ?_⟩
    · show ((b.amplitudeSet ℓ).rows.card : ℝ) ≤
        kT * (kI + kP + 1) * (Z ^ b.shell) ^ (1 + lamA) * (1 + T₁) ^ max AI AP
      have hcard := hfloorCount ℓ
      have hX : 0 ≤ kT * (Z ^ b.shell) ^ (1 + lamA) :=
        mul_nonneg hkT (Real.rpow_nonneg (by linarith) _)
      have hH1 : 1 ≤ (1 + T₁) ^ max AI AP :=
        Real.one_le_rpow (by linarith) (le_max_of_le_left hAI)
      have h1 : 1 ≤ (kI + kP + 1) * (1 + T₁) ^ max AI AP :=
        one_le_mul_of_one_le_of_one_le (by linarith) hH1
      calc ((b.amplitudeSet ℓ).rows.card : ℝ) ≤ kT * (Z ^ b.shell) ^ (1 + lamA) := hcard
        _ ≤ kT * (Z ^ b.shell) ^ (1 + lamA) * ((kI + kP + 1) * (1 + T₁) ^ max AI AP) :=
          le_mul_of_one_le_right hX h1
        _ = kT * (kI + kP + 1) * (Z ^ b.shell) ^ (1 + lamA) * (1 + T₁) ^ max AI AP := by ring
    · show moderateExponent b.shell (2 * b.bin - 1) (b.amplitudeSet ℓ).mean 1 ≤
        B - 7 / 8 - certificateMargin / 2
      have hδ : 2 * b.bin - 1 = 1 / 50 := by rw [hfloor]; norm_num
      have hq : (b.amplitudeSet ℓ).mean ≤ 1 / 100 := by
        have h := (mean_bounds g.slots_pos _ (hlab ℓ).1).2
        linarith
      rw [hδ]
      exact floor_exponent hshpos.le hsh1 hq hlamA hlamA' hΔ
  · have hbin : 51 / 100 < b.bin := lt_of_le_of_ne hbin0 (Ne.symm hfloor)
    have hδ0 : 0 < 2 * b.bin - 1 := by linarith
    by_cases hlarge : 5 / 6 < 2 * b.bin - 1
    · -- large bins `δ > 5/6`: the unselected count at `t = 3/2`
      have hδ5 : 5 / 6 ≤ 2 * b.bin - 1 := hlarge.le
      have hδ1 : 2 * b.bin - 1 ≤ 1 := by linarith
      refine ⟨fun _ => 1 - (2 * b.bin - 1) + (3 * lamA + 2 * lamA),
        fun _ => ⟨by linarith, by linarith⟩, fun ℓ => ?_, fun ℓ => ?_⟩
      · exact large_set_count (b.amplitudeSet ℓ) hU hδ5 hδ1 hlamA hT₁ hkI hkP
          ((hlab ℓ).2.2 hbin (3 / 2) (by norm_num) le_rfl)
          (fun j => (hIS hbin ℓ (3 / 2) (by norm_num) le_rfl j).2)
          (fun j => (hPS hbin ℓ (3 / 2) (by norm_num) le_rfl j).2)
      · exact large_exponent hshpos.le hsh1 hδ5 hδ1
          (mean_bounds g.slots_pos _ (hlab ℓ).1).2 hlamA hlamA' hΔ
    have hδ1 : 2 * b.bin - 1 ≤ 5 / 6 := not_lt.mp hlarge
    by_cases hmid : b.shell ≤ 1 / 2
    · -- the middle shells: the unselected count at `t = 1`
      refine ⟨fun _ => 1 - 2 * (2 * b.bin - 1) / 3 + (3 * lamA + 2 * lamA),
        fun _ => ⟨by linarith, by linarith⟩, fun ℓ => ?_, fun ℓ => ?_⟩
      · exact middle_set_count (b.amplitudeSet ℓ) hU hδ0 hδ1 hlamA hT₁ hkI hkP
          ((hlab ℓ).2.2 hbin 1 le_rfl (by norm_num))
          (fun j => (hIS hbin ℓ 1 le_rfl (by norm_num) j).2)
          (fun j => (hPS hbin ℓ 1 le_rfl (by norm_num) j).2)
      · exact middle_exponent hshpos.le hmid hδ0.le hδ1
          (mean_bounds g.slots_pos _ (hlab ℓ).1).2 hlamA hlamA' hΔ
    · -- the upper shells: the balanced witness parameter
      have hsh : 1 / 2 < b.shell := not_le.mp hmid
      refine ⟨fun ℓ => balancedRowCount (2 * b.bin - 1)
          (1 / 2 - (b.amplitudeSet ℓ).mean / (2 * b.bin - 1)) + (B - 7 / 8) / 4 + 20 * lamA,
        fun ℓ => ?_, fun ℓ => ?_, fun ℓ => ?_⟩
      · obtain ⟨hq0, hq1⟩ := mean_bounds g.slots_pos _ (hlab ℓ).1
        have hy0 : 0 ≤ 1 / 2 - (b.amplitudeSet ℓ).mean / (2 * b.bin - 1) := by
          rw [sub_nonneg, div_le_iff₀ hδ0]; linarith
        have hy1 : 1 / 2 - (b.amplitudeSet ℓ).mean / (2 * b.bin - 1) ≤ 1 / 2 := by
          have := div_nonneg hq0 hδ0.le; linarith
        obtain ⟨hl, hu⟩ := balancedRowCount_range hδ0.le hδ1 hy0 hy1
        constructor <;> linarith
      · obtain ⟨hq0, hq1⟩ := mean_bounds g.slots_pos _ (hlab ℓ).1
        have hy0 : 0 ≤ 1 / 2 - (b.amplitudeSet ℓ).mean / (2 * b.bin - 1) := by
          rw [sub_nonneg, div_le_iff₀ hδ0]; linarith
        have hy1 : 1 / 2 - (b.amplitudeSet ℓ).mean / (2 * b.bin - 1) ≤ 1 / 2 := by
          have := div_nonneg hq0 hδ0.le; linarith
        obtain ⟨ht1, ht2⟩ := balancedCutoff_mem_Icc hδ0.le hδ1 hy0 hy1
        exact balanced_set_count g.slots_pos (b.amplitudeSet ℓ) hB hB' hZ1 hsh hsh1 hδ0 hδ1
          hlamA hlam1 hmesh hround hT₁ hkI hkP (hlab ℓ).1 (hlab ℓ).2.1 rfl
          ((hlab ℓ).2.2 hbin _ ht1 ht2)
          (fun j => (hIS hbin ℓ _ ht1 ht2 j).1) (fun j => (hIS hbin ℓ _ ht1 ht2 j).2)
          (fun j => (hPS hbin ℓ _ ht1 ht2 j).1) (fun j => (hPS hbin ℓ _ ht1 ht2 j).2)
      · obtain ⟨hq0, hq1⟩ := mean_bounds g.slots_pos _ (hlab ℓ).1
        exact balanced_exponent hshpos.le hsh1 hδ0 hδ1 hq0 hq1 hΔ.le (by linarith) hlamA
          hlamA'

/-- The retained part of the high expansion at one scale `Z` and one analysis height
`T₁`: the principal remainder, the small and large rows and the moderate blocks are
bounded by `Z^{B - 11/16 - 2σ}`, the blocks through the derived counts and T's
single-bin estimate. -/
private lemma retained_bound {g : PrimeWindowGeometry} {ψ : HeckeCharacter K}
    {D : TargetData K g} {B lamA mesh kT kI kP AI AP AT k' A' Z T₁ : ℝ}
    (hB : 7 / 8 < B) (hB' : B ≤ 1)
    (hlamA : 0 < lamA) (hlamA' : lamA ≤ certificateMargin / 40)
    (hmesh : (1 / 3 : ℝ) / g.slots ≤ mesh) (hround : (1 / 3 : ℝ) / g.slots ≤ lamA)
    (hZ : 2 ≤ Z) (hT₁ : 1 ≤ T₁) (hkT : 0 ≤ kT) (hkI : 0 ≤ kI) (hkP : 0 ≤ kP)
    (hk' : 0 ≤ k') (hAI : 0 ≤ AI)
    (hrows : ∀ Z d lam : ℝ, 1 ≤ Z → 0 ≤ d → 0 ≤ lam →
      ∀ R : Finset (FrequencyRow K (D.S : Set (HeightOneSpectrum (𝓞 K)))),
        R ⊆ frequencyRows K (D.S : Set (HeightOneSpectrum (𝓞 K))) (2 * Z ^ d) →
          (R.card : ℝ) ≤ kT * (Z ^ d) ^ (1 + lam))
    (hexp : ExpansionSource g ψ D B lamA (tipFinalSaving g B / 2) kT AT Z T₁)
    (hIS : ∀ b, InverseBlockSource g ((D.expansion Z T₁).block b) lamA kI AI Z T₁)
    (hPS : ∀ b, PlainBlockSource g ((D.expansion Z T₁).block b) B lamA mesh kP AP Z T₁)
    (hhigh : ∀ b : Fin (D.expansion Z T₁).blockCount,
      ∀ R : ((D.expansion Z T₁).block b).Label → ℝ, ∀ Ebar : ℝ,
        (∀ ℓ, 0 ≤ R ℓ ∧ R ℓ ≤ 2) →
        (∀ ℓ, ((((D.expansion Z T₁).block b).amplitudeSet ℓ).rows.card : ℝ) ≤
          kT * (kI + kP + 1) * (Z ^ ((D.expansion Z T₁).block b).shell) ^ (R ℓ + lamA) *
            (1 + T₁) ^ max AI AP) →
        (∀ ℓ, moderateExponent ((D.expansion Z T₁).block b).shell
          (2 * ((D.expansion Z T₁).block b).bin - 1)
          (((D.expansion Z T₁).block b).amplitudeSet ℓ).mean (R ℓ) ≤ Ebar) →
        ‖((D.expansion Z T₁).block b).value‖ ≤
          k' * Z ^ (3 / 16 + Ebar + lamA + tipFinalSaving g B / 2) * (1 + T₁) ^ A') :
    ‖(D.expansion Z T₁).principal + (D.expansion Z T₁).small + (D.expansion Z T₁).large +
        ∑ b, ((D.expansion Z T₁).block b).value‖ ≤
      (5 * kT + kT * k') * Z ^ (B - 11 / 16 - 2 * tipFinalSaving g B) *
        (1 + T₁) ^ max AT A' := by
  obtain ⟨hσ0, -, hσc, hσp⟩ := tipFinalSaving_facts g hB
  have hσouter := tipFinalSaving_outer_margins g hB
  have hc := certificateMargin_eq
  have hZ1 : 1 ≤ Z := by linarith
  have hZ0 : 0 < Z := by linarith
  obtain ⟨-, hprin, hsmall, hlarge, hcount, hblocks⟩ := hexp
  -- every block, through the derived counts and T's single-bin estimate
  have hblock : ∀ b, ‖((D.expansion Z T₁).block b).value‖ ≤
      k' * Z ^ (3 / 16 + (B - 7 / 8 - certificateMargin / 2) + lamA +
        tipFinalSaving g B / 2) * (1 + T₁) ^ A' := by
    intro b
    obtain ⟨R, hRb, hRc, hRe⟩ := block_count_and_exponent ((D.expansion Z T₁).block b) hB hB'
      hlamA hlamA' hmesh hround hZ hT₁ hkT hkI hkP hAI (hblocks b)
      (fun ℓ => hrows Z _ lamA hZ1 (by linarith [(hblocks b).1]) hlamA.le _
        (D.rows_in_norm_envelope Z T₁ hZ1 hT₁ b ℓ)) (hIS b) (hPS b)
    exact hhigh b R _ hRb hRc hRe
  have hT0 : (0 : ℝ) ≤ 1 + T₁ := by linarith
  have hX0 : 0 ≤ Z ^ (B - 11 / 16 - 2 * tipFinalSaving g B) := Real.rpow_nonneg hZ0.le _
  have hHT : (1 + T₁) ^ AT ≤ (1 + T₁) ^ max AT A' :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
  have hH' : (1 + T₁) ^ A' ≤ (1 + T₁) ^ max AT A' :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_right _ _)
  -- the principal remainder: three margins, each at least `8σ`
  have hp : ‖(D.expansion Z T₁).principal‖ ≤
      kT * (3 * Z ^ (B - 11 / 16 - 2 * tipFinalSaving g B)) * (1 + T₁) ^ max AT A' := by
    refine hprin.trans (mul_le_mul (mul_le_mul_of_nonneg_left ?_ hkT) hHT
      (Real.rpow_nonneg hT0 _) (mul_nonneg hkT (by linarith)))
    have h1 : Z ^ (B - 11 / 16 - 23 / 960 + tipFinalSaving g B / 2) ≤
        Z ^ (B - 11 / 16 - 2 * tipFinalSaving g B) :=
      Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
    have h2 : Z ^ (B - 11 / 16 - 13 / 9600 + tipFinalSaving g B / 2) ≤
        Z ^ (B - 11 / 16 - 2 * tipFinalSaving g B) :=
      Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
    have h3 : Z ^ (B - 11 / 16 - principalSlotSaving g + tipFinalSaving g B / 2) ≤
        Z ^ (B - 11 / 16 - 2 * tipFinalSaving g B) :=
      Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
    linarith
  -- Outer rows: revised small margin `1/50`, retained large margin `63/800`.
  have hs : ‖(D.expansion Z T₁).small‖ ≤
      kT * Z ^ (B - 11 / 16 - 2 * tipFinalSaving g B) * (1 + T₁) ^ max AT A' := by
    refine hsmall.trans (mul_le_mul (mul_le_mul_of_nonneg_left ?_ hkT) hHT
      (Real.rpow_nonneg hT0 _) (mul_nonneg hkT hX0))
    exact Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith [hσouter.1])
  have hl : ‖(D.expansion Z T₁).large‖ ≤
      kT * Z ^ (B - 11 / 16 - 2 * tipFinalSaving g B) * (1 + T₁) ^ max AT A' := by
    refine hlarge.trans (mul_le_mul (mul_le_mul_of_nonneg_left ?_ hkT) hHT
      (Real.rpow_nonneg hT0 _) (mul_nonneg hkT hX0))
    exact Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith [hσouter.2])
  -- the moderate blocks: `blockCount ≤ k Z^{λb}` and `3/16 + Δ = B - 11/16`
  have hbl : ‖∑ b, ((D.expansion Z T₁).block b).value‖ ≤
      kT * k' * Z ^ (B - 11 / 16 - 2 * tipFinalSaving g B) * (1 + T₁) ^ max AT A' := by
    have hE : Z ^ (tipFinalSaving g B / 2) * Z ^ (3 / 16 + (B - 7 / 8 - certificateMargin / 2) +
        lamA + tipFinalSaving g B / 2) ≤ Z ^ (B - 11 / 16 - 2 * tipFinalSaving g B) := by
      rw [← Real.rpow_add hZ0]
      exact Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
    have hV0 : 0 ≤ k' * Z ^ (3 / 16 + (B - 7 / 8 - certificateMargin / 2) + lamA +
        tipFinalSaving g B / 2) * (1 + T₁) ^ A' :=
      mul_nonneg (mul_nonneg hk' (Real.rpow_nonneg hZ0.le _)) (Real.rpow_nonneg hT0 _)
    calc ‖∑ b, ((D.expansion Z T₁).block b).value‖
        ≤ ∑ b, ‖((D.expansion Z T₁).block b).value‖ := norm_sum_le _ _
      _ ≤ ∑ _b : Fin (D.expansion Z T₁).blockCount, k' * Z ^ (3 / 16 +
          (B - 7 / 8 - certificateMargin / 2) + lamA + tipFinalSaving g B / 2) *
            (1 + T₁) ^ A' :=
        Finset.sum_le_sum fun b _ => hblock b
      _ = ((D.expansion Z T₁).blockCount : ℝ) * (k' * Z ^ (3 / 16 +
          (B - 7 / 8 - certificateMargin / 2) + lamA + tipFinalSaving g B / 2) *
            (1 + T₁) ^ A') := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ (kT * Z ^ (tipFinalSaving g B / 2)) * (k' * Z ^ (3 / 16 +
          (B - 7 / 8 - certificateMargin / 2) + lamA + tipFinalSaving g B / 2) *
            (1 + T₁) ^ A') :=
        mul_le_mul_of_nonneg_right hcount hV0
      _ = kT * k' * (Z ^ (tipFinalSaving g B / 2) * Z ^ (3 / 16 +
          (B - 7 / 8 - certificateMargin / 2) + lamA + tipFinalSaving g B / 2)) *
            (1 + T₁) ^ A' := by
        ring
      _ ≤ kT * k' * Z ^ (B - 11 / 16 - 2 * tipFinalSaving g B) * (1 + T₁) ^ max AT A' :=
        mul_le_mul (mul_le_mul_of_nonneg_left hE (mul_nonneg hkT hk')) hH'
          (Real.rpow_nonneg hT0 _) (mul_nonneg (mul_nonneg hkT hk') hX0)
  calc ‖(D.expansion Z T₁).principal + (D.expansion Z T₁).small + (D.expansion Z T₁).large +
        ∑ b, ((D.expansion Z T₁).block b).value‖
      ≤ ‖(D.expansion Z T₁).principal‖ + ‖(D.expansion Z T₁).small‖ +
        ‖(D.expansion Z T₁).large‖ + ‖∑ b, ((D.expansion Z T₁).block b).value‖ :=
        (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ kT * (3 * Z ^ (B - 11 / 16 - 2 * tipFinalSaving g B)) * (1 + T₁) ^ max AT A' +
        kT * Z ^ (B - 11 / 16 - 2 * tipFinalSaving g B) * (1 + T₁) ^ max AT A' +
        kT * Z ^ (B - 11 / 16 - 2 * tipFinalSaving g B) * (1 + T₁) ^ max AT A' +
        kT * k' * Z ^ (B - 11 / 16 - 2 * tipFinalSaving g B) * (1 + T₁) ^ max AT A' :=
        add_le_add (add_le_add (add_le_add hp hs) hl) hbl
    _ = (5 * kT + kT * k') * Z ^ (B - 11 / 16 - 2 * tipFinalSaving g B) *
        (1 + T₁) ^ max AT A' := by ring

/-- The accounting of M Section 7 for one target. -/
theorem powerHeightComparison_of_sources {g : PrimeWindowGeometry} {ψ : HeckeCharacter K}
    {D : TargetData K g} {B lamA mesh : ℝ}
    (hB : 7 / 8 < B) (hB' : B ≤ 1)
    (hlamA : 0 < lamA) (hlamA' : lamA ≤ certificateMargin / 40)
    (hmesh : (1 / 3 : ℝ) / g.slots ≤ mesh) (hround : (1 / 3 : ℝ) / g.slots ≤ lamA)
    (hT : TSource g ψ D B lamA (tipFinalSaving g B / 2))
    (hI : ISource g D lamA) (hP : PSource g D B lamA mesh) :
    PowerHeightComparison (D.probeFunction ψ) (D.signal ψ) (B - 11 / 16)
      (tipFinalSaving g B) := by
  -- The height degrees and ceilings precede the analysis height `τ`.
  obtain ⟨cRows, hcRows, hRows⟩ := physicalRows_floor_count_of_subset K
    (D.S : Set (HeightOneSpectrum (𝓞 K))) (c := 2) (by norm_num)
  obtain ⟨AT, cT, hAT, hcT, hexp⟩ := hT.expansion
  obtain ⟨AI, cI, hAI, hcI, hIsrc⟩ := hI
  obtain ⟨AP, cP, -, hcP, hPsrc⟩ := hP
  obtain ⟨A', cH, -, hcH, hhigh⟩ := hT.highBin (max AI AP) (le_max_of_le_left hAI)
  refine powerHeightComparison_of_decomposition (A := max AT A')
    (ceiling := min (min cT cI) (min cP cH))
    (E := fun Z T => (D.expansion Z T).principal + (D.expansion Z T).small +
      (D.expansion Z T).large + ∑ b, ((D.expansion Z T).block b).value)
    (Q := fun Z T => (D.expansion Z T).tail)
    (le_max_of_le_left hAT) (lt_min (lt_min hcT hcI) (lt_min hcP hcH)) ?_ hT.tail
  -- For one admissible `τ`: the constants and thresholds of T, I, P and the single-bin
  -- estimate, the count constant of the latter chosen after those of T, I and P.
  intro τ hτ hτc
  have hτT : τ ≤ cT := hτc.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hτI : τ ≤ cI := hτc.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hτP : τ ≤ cP := hτc.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτH : τ ≤ cH := hτc.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨ZT, k₀, hZT, hk₀, hexp₀⟩ := hexp τ hτ hτT
  let kT := max k₀ cRows
  have hkT : 0 ≤ kT := hk₀.trans (le_max_left _ _)
  have hexpτ : ∀ Z : ℝ, ZT ≤ Z →
      ExpansionSource g ψ D B lamA (tipFinalSaving g B / 2) kT AT Z (Z ^ τ) := by
    intro Z hZ
    have hZ0 : 0 ≤ Z := by linarith
    exact (hexp₀ Z hZ).mono hZ0 (by positivity) (le_max_left _ _)
  have hrows : ∀ Z d lam : ℝ, 1 ≤ Z → 0 ≤ d → 0 ≤ lam →
      ∀ R : Finset (FrequencyRow K (D.S : Set (HeightOneSpectrum (𝓞 K)))),
        R ⊆ frequencyRows K (D.S : Set (HeightOneSpectrum (𝓞 K))) (2 * Z ^ d) →
          (R.card : ℝ) ≤ kT * (Z ^ d) ^ (1 + lam) := by
    intro Z d lam hZ hd hl R hR
    exact (hRows Z d lam hZ hd hl R hR).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _))
  obtain ⟨ZI, kI, -, hkI, hIτ⟩ := hIsrc τ hτ hτI
  obtain ⟨ZP, kP, -, hkP, hPτ⟩ := hPsrc τ hτ hτP
  obtain ⟨k', ZH, hk', -, hhighτ⟩ :=
    hhigh τ hτ hτH (kT * (kI + kP + 1)) (mul_nonneg hkT (by linarith))
  refine ⟨5 * kT + kT * k', max (max ZT ZI) (max ZP ZH),
    add_nonneg (by linarith) (mul_nonneg hkT hk'), fun Z hZ => ?_⟩
  have hZT' : ZT ≤ Z := ((le_max_left ZT ZI).trans (le_max_left _ _)).trans hZ
  have hZI' : ZI ≤ Z := ((le_max_right ZT ZI).trans (le_max_left _ _)).trans hZ
  have hZP' : ZP ≤ Z := ((le_max_left ZP ZH).trans (le_max_right _ _)).trans hZ
  have hZH' : ZH ≤ Z := ((le_max_right ZP ZH).trans (le_max_right _ _)).trans hZ
  have hZ2 : 2 ≤ Z := hZT.trans hZT'
  have hT1 : 1 ≤ Z ^ τ := Real.one_le_rpow (by linarith) hτ.le
  exact ⟨(hexpτ Z hZT').1, retained_bound hB hB' hlamA hlamA' hmesh hround hZ2 hT1 hkT hkI
    hkP hk' hAI hrows (hexpτ Z hZT') (hIτ Z hZI') (hPτ Z hZP') (hhighτ Z hZH')⟩

end HeckeGeneral.ThetaSkeleton.TIP
