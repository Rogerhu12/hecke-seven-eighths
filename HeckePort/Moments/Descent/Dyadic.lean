import HeckePort.Moments.Descent.Reconstruction
import HeckePort.Moments.Descent.SieveComposition
import HeckePort.Moments.Descent.DivisorSum

/-!
# Dyadic decomposition of the hybrid columns

Port of openai/math `OAI/NumberTheory/DirichletL/Descent/Dyadic.lean` (revision `fd4aeeb2`)
from `ℤ[ω]` to `𝓞 K`, together with the dyadic-bin machinery it takes from
`Eisenstein/SmoothSummands` (`divisorDyadicLabel/Bin/Scale` and their bounds, generic for ideals
of a number ring) and `QuadraticSieve/AnnularRecursion` (`exists_dyadic_shell`), reproved here.

The constants `256 = 2 * 128` become `2 * idealCountConstant K`.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators
open HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

theorem exists_dyadic_shell (n lengthScale : ℕ) (hn : 1 ≤ n) (hL : (n : ℝ) ≤ (2 : ℝ) ^ lengthScale) :
    ∃ j ∈ Finset.range (lengthScale + 1), (2 : ℝ) ^ j / 2 < n ∧ (n : ℝ) ≤ (2 : ℝ) ^ j := by
  have hex : ∃ j : ℕ, (n : ℝ) ≤ (2 : ℝ) ^ j := ⟨lengthScale, hL⟩
  let j := Nat.find hex
  have hj : (n : ℝ) ≤ (2 : ℝ) ^ j := Nat.find_spec hex
  have hjL : j ≤ lengthScale := Nat.find_min' hex hL
  refine ⟨j, Finset.mem_range.mpr (by omega), ?_, hj⟩
  have hjfind : j = Nat.find hex := rfl
  rcases hjj : j with _ | j'
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    norm_num
    linarith
  · have hprev : ¬ (n : ℝ) ≤ (2 : ℝ) ^ j' := Nat.find_min hex (by omega)
    have hp := lt_of_not_ge hprev
    simpa only [pow_succ, mul_div_cancel_right₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hp

lemma positive_ideal_dyadic_exists (N : ℝ) (D : Ideal (𝓞 K))
    (hD : 1 ≤ (Ideal.absNorm D : ℝ)) (hDN : (Ideal.absNorm D : ℝ) ≤ N) :
    ∃ j ∈ Finset.range (columnDyadicLength N + 1),
      (2 : ℝ) ^ j / 2 < (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ (2 : ℝ) ^ j := by
  have hp : 1 ≤ Ideal.absNorm D := by exact_mod_cast hD
  exact exists_dyadic_shell (Ideal.absNorm D) (columnDyadicLength N) hp
    (hDN.trans (columnDyadicLength_cover N))

def divisorDyadicLabel (N : ℝ) (D : Ideal (𝓞 K)) : Fin (columnDyadicLength N + 1) :=
  if h : 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N then
    ⟨(positive_ideal_dyadic_exists N D h.1 h.2).choose,
      Finset.mem_range.mp (positive_ideal_dyadic_exists N D h.1 h.2).choose_spec.1⟩
  else ⟨0, by omega⟩

def divisorDyadicBin (S : Finset (Ideal (𝓞 K))) (N : ℝ)
    (j : Fin (columnDyadicLength N + 1)) : Finset (Ideal (𝓞 K)) :=
  S.filter (fun D => divisorDyadicLabel N D = j)

def divisorDyadicScale (j : ℕ) : ℝ := max 1 ((2 : ℝ) ^ j / 2)

lemma divisorDyadicLabel_bounds (N : ℝ) (D : Ideal (𝓞 K))
    (hD : 1 ≤ (Ideal.absNorm D : ℝ)) (hDN : (Ideal.absNorm D : ℝ) ≤ N) :
    (2 : ℝ) ^ (divisorDyadicLabel N D).val / 2 < (Ideal.absNorm D : ℝ) ∧
      (Ideal.absNorm D : ℝ) ≤ (2 : ℝ) ^ (divisorDyadicLabel N D).val := by
  unfold divisorDyadicLabel
  rw [dif_pos ⟨hD, hDN⟩]
  exact (positive_ideal_dyadic_exists N D hD hDN).choose_spec.2

lemma divisorDyadicScale_ge_one (j : ℕ) : 1 ≤ divisorDyadicScale j := le_max_left _ _

theorem divisorDyadicBin_bounds (S : Finset (Ideal (𝓞 K))) (N : ℝ)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (j : Fin (columnDyadicLength N + 1)) (D : Ideal (𝓞 K)) (hD : D ∈ divisorDyadicBin S N j) :
    divisorDyadicScale j.val ≤ (Ideal.absNorm D : ℝ) ∧
      (Ideal.absNorm D : ℝ) ≤ 2 * divisorDyadicScale j.val := by
  obtain ⟨hDS, hj⟩ := Finset.mem_filter.mp hD
  have hd := hS D hDS
  have hb := divisorDyadicLabel_bounds N D hd.1 hd.2
  rw [hj] at hb
  refine ⟨max_le hd.1 hb.1.le, ?_⟩
  have hm : (2 : ℝ) ^ j.val / 2 ≤ divisorDyadicScale j.val := le_max_right _ _
  linarith [hb.2]

theorem divisorDyadicBin_scale_le (S : Finset (Ideal (𝓞 K))) (N : ℝ)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (j : Fin (columnDyadicLength N + 1)) (hj : (divisorDyadicBin S N j).Nonempty) :
    divisorDyadicScale j.val ≤ N := by
  obtain ⟨D, hD⟩ := hj
  exact (divisorDyadicBin_bounds S N hS j D hD).1.trans (hS D (Finset.mem_filter.mp hD).1).2

theorem sum_divisorDyadicBins {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal (𝓞 K))) (N : ℝ) (f : Ideal (𝓞 K) → A) :
    (∑ D ∈ S, f D) = ∑ j : Fin (columnDyadicLength N + 1), ∑ D ∈ divisorDyadicBin S N j, f D := by
  simp only [divisorDyadicBin, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  simp

theorem sum_divisorDyadicRectangles {A : Type*} [AddCommMonoid A]
    (S T : Finset (Ideal (𝓞 K))) (N : ℝ) (f : Ideal (𝓞 K) → Ideal (𝓞 K) → A) :
    (∑ D ∈ S, ∑ E ∈ T, f D E) =
      ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1),
        ∑ D ∈ divisorDyadicBin S N j, ∑ E ∈ divisorDyadicBin T N k, f D E := by
  calc
    _ = ∑ j : Fin (columnDyadicLength N + 1), ∑ D ∈ divisorDyadicBin S N j,
        ∑ E ∈ T, f D E := sum_divisorDyadicBins S N _
    _ = ∑ j : Fin (columnDyadicLength N + 1), ∑ D ∈ divisorDyadicBin S N j,
        ∑ k : Fin (columnDyadicLength N + 1), ∑ E ∈ divisorDyadicBin T N k, f D E := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro D hD
      exact sum_divisorDyadicBins T N (f D)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm

/-! ### The hybrid columns -/

def hybridSquarePool (S : Finset (Ideal (𝓞 K) × Ideal (𝓞 K))) : Finset (Ideal (𝓞 K)) :=
  (hybridColumnSupport S).image HybridColumnData.square

def hybridCommonBlock (S : Finset (Ideal (𝓞 K) × Ideal (𝓞 K))) (N : ℝ)
    (i : Fin (columnDyadicLength N + 1)) (t : Ideal (𝓞 K)) : Finset (HybridColumnData K) :=
  (hybridColumnSupport S).filter fun d =>
    d.square = t ∧ divisorDyadicLabel N d.common = i

theorem hybrid_dyadic_reindex {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal (𝓞 K) × Ideal (𝓞 K))) (N B : ℝ) (f : HybridColumnData K → A) :
    (∑ d ∈ hybridColumnSupport S, f d) =
      ∑ j : Fin (columnDyadicLength B + 1),
        ∑ i : Fin (columnDyadicLength N + 1),
          ∑ t ∈ divisorDyadicBin (hybridSquarePool S) B j,
            ∑ d ∈ hybridCommonBlock S N i t, f d := by
  have ht : (∑ d ∈ hybridColumnSupport S, f d) =
      ∑ t ∈ hybridSquarePool S, ∑ d ∈ hybridColumnSupport S with d.square = t, f d := by
    symm
    exact Finset.sum_fiberwise_of_maps_to
      (fun d hd => Finset.mem_image.mpr ⟨d, hd, rfl⟩) f
  rw [ht, sum_divisorDyadicBins (hybridSquarePool S) B]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hi := Finset.sum_fiberwise
    ((hybridColumnSupport S).filter fun d => d.square = t)
    (fun d => divisorDyadicLabel N d.common) f
  simpa only [Finset.filter_filter, hybridCommonBlock] using hi.symm

theorem norm_one_le_of_ne_bot {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : (1 : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))

theorem hybridSquarePool_bounds (S : Finset (Ideal (𝓞 K) × Ideal (𝓞 K))) (B : ℝ)
    (hS : ∀ p ∈ S, (Ideal.absNorm p.2 : ℝ) ≤ B)
    (t : Ideal (𝓞 K)) (ht : t ∈ hybridSquarePool S) :
    1 ≤ (Ideal.absNorm t : ℝ) ∧ (Ideal.absNorm t : ℝ) ≤ B := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ht
  have hb0 : (d.common * d.residualB) * d.square ^ 2 ≠ ⊥ :=
    mul_ne_zero d.g_squarefree.ne_zero (pow_ne_zero _ d.square_ne_zero)
  refine ⟨norm_one_le_of_ne_bot d.square_ne_zero, ?_⟩
  apply (norm_le_of_dvd hb0 ?_).trans
    (hS d.reconstruct ((mem_hybridColumnSupport S d).mp hd))
  exact dvd_mul_of_dvd_right (dvd_pow_self d.square (by norm_num : 2 ≠ 0)) _

theorem hybridSquarePool_bin_count (S : Finset (Ideal (𝓞 K) × Ideal (𝓞 K))) (B : ℝ)
    (hS : ∀ p ∈ S, (Ideal.absNorm p.2 : ℝ) ≤ B)
    (j : Fin (columnDyadicLength B + 1)) :
    ((divisorDyadicBin (hybridSquarePool S) B j).card : ℝ) ≤
      2 * idealCountConstant K * divisorDyadicScale j.val := by
  have hscale := divisorDyadicScale_ge_one j.val
  have hb := divisorDyadicBin_bounds (hybridSquarePool S) B
    (hybridSquarePool_bounds S B hS) j
  have hc := card_le_idealCountConstant K
    (divisorDyadicBin (hybridSquarePool S) B j) (2 * divisorDyadicScale j.val)
    (by linarith) (fun t ht => (hb t ht).2)
  linarith

theorem hybridCommonBlock_bounds
    (S : Finset (Ideal (𝓞 K) × Ideal (𝓞 K))) (N B : ℝ) (hN : 0 ≤ N) (hB : 0 ≤ B)
    (hS : ∀ p ∈ S, (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B)
    (i : Fin (columnDyadicLength N + 1)) (j : Fin (columnDyadicLength B + 1))
    (t : Ideal (𝓞 K)) (ht : t ∈ divisorDyadicBin (hybridSquarePool S) B j)
    (d : HybridColumnData K) (hd : d ∈ hybridCommonBlock S N i t) :
    let C := divisorDyadicScale i.val
    let T := divisorDyadicScale j.val
    C ≤ (Ideal.absNorm d.common : ℝ) ∧ (Ideal.absNorm d.common : ℝ) ≤ 2 * C ∧
    (Ideal.absNorm d.residualN : ℝ) ≤ N / C ∧
    (Ideal.absNorm d.residualB : ℝ) ≤ B / (C * T ^ 2) ∧
    (Ideal.absNorm (d.residualN * d.residualB) : ℝ) ≤ N * B / (C ^ 2 * T ^ 2) := by
  obtain ⟨hdS, hdt, hdi⟩ := Finset.mem_filter.mp hd
  have hs := hS d.reconstruct ((mem_hybridColumnSupport S d).mp hdS)
  have hc1 := norm_one_le_of_ne_bot d.common_ne_zero
  have hcn : (Ideal.absNorm d.common : ℝ) ≤ N :=
    (norm_le_of_dvd d.n_squarefree.ne_zero (dvd_mul_right _ _)).trans hs.1
  have hcb := divisorDyadicLabel_bounds N d.common hc1 hcn
  rw [hdi] at hcb
  have hcLow : divisorDyadicScale i.val ≤ (Ideal.absNorm d.common : ℝ) :=
    max_le hc1 hcb.1.le
  have hcHigh : (Ideal.absNorm d.common : ℝ) ≤ 2 * divisorDyadicScale i.val := by
    have hh : (2 : ℝ) ^ i.val / 2 ≤ divisorDyadicScale i.val := le_max_right _ _
    linarith [hcb.2]
  have htLow := (divisorDyadicBin_bounds (hybridSquarePool S) B
    (hybridSquarePool_bounds S B (fun p hp => (hS p hp).2)) j t ht).1
  rw [← hdt] at htLow
  refine ⟨hcLow, hcHigh, ?_⟩
  exact d.residual_norm_bounds N B (divisorDyadicScale i.val) (divisorDyadicScale j.val)
    hN hB (by linarith [divisorDyadicScale_ge_one i.val])
    (by linarith [divisorDyadicScale_ge_one j.val]) hs.1 hs.2 hcLow htLow

theorem hybrid_square_dyad_energy
    (S : Finset (Ideal (𝓞 K) × Ideal (𝓞 K))) (B : ℝ)
    (hS : ∀ p ∈ S, (Ideal.absNorm p.2 : ℝ) ≤ B)
    (j : Fin (columnDyadicLength B + 1)) (rows : Finset (Ideal (𝓞 K)))
    (F : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hF : ∀ t ∈ divisorDyadicBin (hybridSquarePool S) B j,
      (∑ k ∈ rows, ‖F t k‖ ^ 2) ≤ E) :
    (∑ k ∈ rows, ‖∑ t ∈ divisorDyadicBin (hybridSquarePool S) B j, F t k‖ ^ 2) ≤
      (2 * idealCountConstant K * divisorDyadicScale j.val) ^ 2 * E := by
  let Tset := divisorDyadicBin (hybridSquarePool S) B j
  have hc := hybridSquarePool_bin_count S B hS j
  calc
    _ ≤ (Tset.card : ℝ) * ∑ t ∈ Tset, ∑ k ∈ rows, ‖F t k‖ ^ 2 := by
      calc
        _ ≤ ∑ k ∈ rows, (Tset.card : ℝ) * ∑ t ∈ Tset, ‖F t k‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro k hk
          simpa using bounded_finset_coefficient_sum_sq Tset (fun _ => 1) (fun t => F t k)
            (by simp)
        _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (Tset.card : ℝ) * ∑ _t ∈ Tset, E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hF) (Nat.cast_nonneg _)
    _ = (Tset.card : ℝ) ^ 2 * E := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2) hE

end HeckePort.Moments

end
