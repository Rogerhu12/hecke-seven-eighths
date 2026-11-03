/-
Copyright (c) 2026 OpenAI. Released under the Apache 2.0 license.
-/
import PrimeCancellation
import PrimeCancellationAux
import Mathlib.Tactic.Choose
import Mathlib.Tactic.GCongr

/-!
# Paired prime moments from zero-free analytic data

`SlotData` contains the original Euler series, absolute convergence,
elementary prime counting, and the zero-free analytic input. It contains
no prime-sum cancellation estimate. The theorems below derive that estimate
from `exists_uniform_fixed_window_prime_bound`, pay for a finite Boolean
deletion mask, normalize by the square root of the slot scale, and then
multiply and sum over the prescribed finite row set.

Window constants are chosen before the rows, characters, zero boundary,
buffer, outer scale, and slot lengths. No positive lower bound on a slot
length is required: the hypotheses are exactly `1 <= X ^ ell i` and a
bound on the sum of the buffer losses.
-/

set_option autoImplicit false
noncomputable section

namespace PrimeCancellation.Paired

open PrimeCancellation.Analytic PrimeCancellationPrimeSeries
open scoped Classical BigOperators ContDiff

variable {α ι ρ : Type*}

/-- Original arithmetic and analytic data for one prime slot. -/
structure SlotData (α : Type*) (β degreeBound : ℝ) where
  norm : α → ℝ
  coefficient : α → ℂ
  function : ℂ → ℂ
  arithmetic : PrimeArithmetic norm coefficient degreeBound
  analytic : ZeroFreeData function β
  absolute : Summable (fun np : ℕ × α =>
    ‖primePowerCoefficient norm coefficient np‖ *
      (primePowerNorm norm np) ^ (-(2 : ℝ)))
  euler : ∀ s : ℂ, 1 < s.re →
    (∑' np : ℕ × α,
      primePowerCoefficient norm coefficient np * (primePowerNorm norm np : ℂ) ^ (-s)) =
        -deriv function s / function s

/-- The row-independent prime bound obtained by replacing the analytic
height constant by its supplied uniform upper bound H. -/
def uniformPrimeConstant (δ D M degreeBound P₀ H : ℝ) : ℝ :=
  24 * (D * H) / δ ^ 2 + M * degreeBound * (1 + Real.sqrt 2) +
    2 * M * degreeBound * P₀

/-- A finite deletion of at most B terms costs at most M B. -/
def maskedPrimeConstant (δ D M degreeBound P₀ H B : ℝ) : ℝ :=
  uniformPrimeConstant δ D M degreeBound P₀ H + M * B

def maskedPrimeSum {β degreeBound : ℝ} (data : SlotData α β degreeBound)
    (W : ℝ → ℂ) (P : ℝ) (pool : Finset α) (keep : α → Bool) : ℂ :=
  PrimeCancellationAux.maskedSum pool
    (fun p => data.coefficient p * W (data.norm p / P)) keep

def normalizedMaskedPrimeSum {β degreeBound : ℝ} (data : SlotData α β degreeBound)
    (W : ℝ → ℂ) (P : ℝ) (pool : Finset α) (keep : α → Bool) : ℂ :=
  (Real.sqrt P : ℂ)⁻¹ * maskedPrimeSum data W P pool keep

theorem maskedPrimeConstant_nonneg (δ D M degreeBound P₀ H B : ℝ)
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hd : 0 ≤ degreeBound)
    (hP₀ : 0 ≤ P₀) (hH : 0 ≤ H) (hB : 0 ≤ B) :
    0 ≤ maskedPrimeConstant δ D M degreeBound P₀ H B := by
  unfold maskedPrimeConstant uniformPrimeConstant
  positivity

theorem primeBoundConstant_le_uniform {F : ℂ → ℂ} {β : ℝ}
    (data : ZeroFreeData F β) (δ D M degreeBound P₀ H : ℝ)
    (hD : 0 ≤ D) (hH : heightConstant data + 3 * (data.k : ℝ) ≤ H) :
    primeBoundConstant data δ D M degreeBound P₀ ≤
      uniformPrimeConstant δ D M degreeBound P₀ H := by
  unfold primeBoundConstant uniformPrimeConstant
  gcongr

/-- A support cover identifies the finite polynomial with the full
absolutely convergent prime sum. No cancellation is used here. -/
theorem finite_sum_eq_primeSum {β degreeBound : ℝ}
    (data : SlotData α β degreeBound) (W : ℝ → ℂ) (P : ℝ) (pool : Finset α)
    (hcover : ∀ p : α, W (data.norm p / P) ≠ 0 → p ∈ pool) :
    (∑ p ∈ pool, data.coefficient p * W (data.norm p / P)) =
      primeSum data.norm data.coefficient W P := by
  symm
  unfold primeSum
  apply tsum_eq_sum
  intro p hp
  have hz : W (data.norm p / P) = 0 := by
    by_contra hn
    exact hp (hcover p hn)
  simp only [hz, mul_zero]

/-- A genuine analytic bound for a masked prime slot. The only mask
assumption is a count of deleted terms. -/
theorem exists_uniform_masked_prime_bound (W : ℝ → ℂ)
    (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Set.Icc (1 : ℝ) 2) :
    ∃ P₀ D : ℝ, 2 ≤ P₀ ∧ 0 ≤ D ∧
      ∀ {α : Type*} [Countable α] (β δ M degreeBound H B : ℝ)
        (data : SlotData α β degreeBound),
      WindowBound W M → (heightConstant data.analytic + 3 * (data.analytic.k : ℝ) ≤ H) →
      ∀ (P : ℝ) (pool : Finset α) (keep : α → Bool),
      1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 → 1 ≤ P →
      (∀ p : α, W (data.norm p / P) ≠ 0 → p ∈ pool) →
      ((pool.filter (fun p => keep p = false)).card : ℝ) ≤ B →
        ‖maskedPrimeSum data W P pool keep‖ ≤
          maskedPrimeConstant δ D M degreeBound P₀ H B * P ^ (β + δ) := by
  obtain ⟨P₀, D, hP₀, hD, hprime⟩ := exists_uniform_fixed_window_prime_bound W hW hWs
  refine ⟨P₀, D, hP₀, hD, ?_⟩
  intro α _ β δ M degreeBound H B data hWin hH P pool keep hβ hβ' hδ hδ' hP
    hcover hdeleted
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hB : 0 ≤ B := (Nat.cast_nonneg _).trans hdeleted
  have hnorm (p : α) : ‖data.coefficient p * W (data.norm p / P)‖ ≤ M := by
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (data.arithmetic.coeff_bound p)
      (hWin.bound (data.norm p / P)) (norm_nonneg _) zero_le_one
  have hraw := hprime data.norm data.coefficient degreeBound M data.arithmetic hWin
    β data.function data.analytic data.absolute data.euler δ P hβ hβ' hδ hδ' hP
  have hbase : ‖primeSum data.norm data.coefficient W P‖ ≤
      uniformPrimeConstant δ D M degreeBound P₀ H * P ^ (β + δ) :=
    hraw.trans (mul_le_mul_of_nonneg_right
      (primeBoundConstant_le_uniform data.analytic δ D M degreeBound P₀ H hD hH)
      (Real.rpow_nonneg hPpos.le _))
  have hmask := PrimeCancellationAux.norm_maskedSum_le_of_card pool
    (fun p => data.coefficient p * W (data.norm p / P)) keep M B hWin.nonneg
    (fun p _ _ => hnorm p) hdeleted
  rw [finite_sum_eq_primeSum data W P pool hcover] at hmask
  have hone : 1 ≤ P ^ (β + δ) := Real.one_le_rpow hP (by linarith)
  have hcost : B * M ≤ (M * B) * P ^ (β + δ) := by
    have h := mul_le_mul_of_nonneg_left hone (mul_nonneg hWin.nonneg hB)
    simpa only [mul_one, mul_comm B M] using h
  calc
    ‖maskedPrimeSum data W P pool keep‖ ≤
        ‖primeSum data.norm data.coefficient W P‖ + B * M := hmask
    _ ≤ uniformPrimeConstant δ D M degreeBound P₀ H * P ^ (β + δ) + B * M :=
      add_le_add hbase (le_refl _)
    _ ≤ uniformPrimeConstant δ D M degreeBound P₀ H * P ^ (β + δ) +
        (M * B) * P ^ (β + δ) := add_le_add (le_refl _) hcost
    _ = maskedPrimeConstant δ D M degreeBound P₀ H B * P ^ (β + δ) := by
      unfold maskedPrimeConstant
      ring

/-- General paired energy, derived from zero-free analytic input slot by
slot. Constants P₀ and D depend only on the fixed windows W. The row count
and the total buffer loss are the only subsequent exponent losses. -/
theorem exists_uniform_paired_prime_bound (W : ι → ℝ → ℂ)
    (hW : ∀ i, ContDiff ℝ ∞ (W i))
    (hWs : ∀ i, Function.support (W i) ⊆ Set.Icc (1 : ℝ) 2) :
    ∃ P₀ D : ι → ℝ, (∀ i, 2 ≤ P₀ i ∧ 0 ≤ D i) ∧
      ∀ {ρ α : Type*} [Countable α] (rows : Finset ρ) (slots : Finset ι)
        (β δ X ε Crows e : ℝ) (ell M degreeBound H B : ι → ℝ)
        (data : ρ → (i : ι) → SlotData α β (degreeBound i))
        (pool : ι → Finset α) (keep : ρ → ι → α → Bool),
      1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 → 1 ≤ X →
      (∀ i ∈ slots, 1 ≤ X ^ ell i) →
      (∀ i ∈ slots, WindowBound (W i) (M i)) →
      (∀ u ∈ rows, ∀ i ∈ slots,
        heightConstant (data u i).analytic + 3 * ((data u i).analytic.k : ℝ) ≤ H i) →
      (∀ u ∈ rows, ∀ i ∈ slots, ∀ p : α,
        W i ((data u i).norm p / X ^ ell i) ≠ 0 → p ∈ pool i) →
      (∀ u ∈ rows, ∀ i ∈ slots,
        (((pool i).filter (fun p => keep u i p = false)).card : ℝ) ≤ B i) →
      (rows.card : ℝ) ≤ Crows * X ^ e → 2 * δ * (∑ i ∈ slots, ell i) ≤ ε →
        (∑ u ∈ rows, ‖∏ i ∈ slots,
          normalizedMaskedPrimeSum (data u i) (W i) (X ^ ell i) (pool i) (keep u i)‖ ^ 2) ≤
          (Crows * ∏ i ∈ slots,
            (maskedPrimeConstant δ (D i) (M i) (degreeBound i) (P₀ i) (H i) (B i)) ^ 2) *
              X ^ (e + ((2 * β - 1) * (∑ i ∈ slots, ell i) + ε)) := by
  classical
  choose P₀ D hP₀ hD hbound using
    (fun i => exists_uniform_masked_prime_bound (W i) (hW i) (hWs i))
  refine ⟨P₀, D, fun i => ⟨hP₀ i, hD i⟩, ?_⟩
  intro ρ α _ rows slots β δ X ε Crows e ell M degreeBound H B data pool keep
    hβ hβ' hδ hδ' hX hP hWin hH hcover hdeleted hrows hloss
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  let C : ι → ℝ := fun i =>
    maskedPrimeConstant δ (D i) (M i) (degreeBound i) (P₀ i) (H i) (B i)
  have hslot (u : ρ) (hu : u ∈ rows) (i : ι) (hi : i ∈ slots) :
      ‖normalizedMaskedPrimeSum (data u i) (W i) (X ^ ell i) (pool i) (keep u i)‖ ^ 2 ≤
        (C i) ^ 2 * X ^ ((2 * β - 1) * ell i + (2 * δ) * ell i) := by
    have hHnon : 0 ≤ H i :=
      (add_nonneg (heightConstant_nonneg (data u i).analytic) (by positivity)).trans
        (hH u hu i hi)
    have hBnon : 0 ≤ B i := (Nat.cast_nonneg _).trans (hdeleted u hu i hi)
    have hC : 0 ≤ C i := maskedPrimeConstant_nonneg δ (D i) (M i) (degreeBound i)
      (P₀ i) (H i) (B i) (hD i) (hWin i hi).nonneg (data u i).arithmetic.d_nonneg
      (by linarith [hP₀ i]) hHnon hBnon
    have hb := hbound i β δ (M i) (degreeBound i) (H i) (B i) (data u i)
      (hWin i hi) (hH u hu i hi) (X ^ ell i) (pool i) (keep u i)
      hβ hβ' hδ hδ' (hP i hi) (hcover u hu i hi) (hdeleted u hu i hi)
    have hn := PrimeCancellationAux.norm_normalized_sq_le_rpow
      (X ^ ell i) (β + δ) (C i) (Real.rpow_pos_of_pos hXpos _) hC
      (maskedPrimeSum (data u i) (W i) (X ^ ell i) (pool i) (keep u i)) hb
    change ‖normalizedMaskedPrimeSum (data u i) (W i) (X ^ ell i)
      (pool i) (keep u i)‖ ^ 2 ≤ (C i) ^ 2 * (X ^ ell i) ^ (2 * (β + δ) - 1) at hn
    rw [← Real.rpow_mul hXpos.le] at hn
    have hexp : ell i * (2 * (β + δ) - 1) =
        (2 * β - 1) * ell i + (2 * δ) * ell i := by ring
    rw [hexp] at hn
    exact hn
  apply PrimeCancellationAux.paired_sum_le_of_slot_bounds rows slots
    (fun u i => normalizedMaskedPrimeSum (data u i) (W i) (X ^ ell i) (pool i) (keep u i))
    (fun i => (C i) ^ 2) ell (fun i => (2 * δ) * ell i) X (2 * β - 1) ε Crows e
    hX (fun i _ => sq_nonneg (C i)) hrows
  · simpa only [← Finset.mul_sum] using hloss
  · exact hslot

/-- Member-indexed form for an ambient row type containing exceptional or
principal rows. Analytic data are supplied only on `rows.attach` and
`slots.attach`; no assertion is made about the omitted rows or slots. -/
theorem exists_uniform_paired_prime_bound_on_members (slots : Finset ι)
    (W : ι → ℝ → ℂ) (hW : ∀ i ∈ slots, ContDiff ℝ ∞ (W i))
    (hWs : ∀ i ∈ slots, Function.support (W i) ⊆ Set.Icc (1 : ℝ) 2) :
    ∃ P₀ D : {i // i ∈ slots} → ℝ, (∀ i, 2 ≤ P₀ i ∧ 0 ≤ D i) ∧
      ∀ {ρ α : Type*} [Countable α] (rows : Finset ρ)
        (β δ X ε Crows e : ℝ) (ell M degreeBound H B : ι → ℝ)
        (data : {u // u ∈ rows} → (i : {i // i ∈ slots}) →
          SlotData α β (degreeBound i.val))
        (pool : ι → Finset α) (keep : ρ → ι → α → Bool),
      1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 → 1 ≤ X →
      (∀ i ∈ slots, 1 ≤ X ^ ell i) →
      (∀ i ∈ slots, WindowBound (W i) (M i)) →
      (∀ u i, heightConstant (data u i).analytic + 3 * ((data u i).analytic.k : ℝ) ≤ H i.val) →
      (∀ u i, ∀ p : α,
        W i.val ((data u i).norm p / X ^ ell i.val) ≠ 0 → p ∈ pool i.val) →
      (∀ (u : {u // u ∈ rows}) (i : {i // i ∈ slots}),
        (((pool i.val).filter (fun p => keep u.val i.val p = false)).card : ℝ) ≤ B i.val) →
      (rows.card : ℝ) ≤ Crows * X ^ e → 2 * δ * (∑ i ∈ slots, ell i) ≤ ε →
        (∑ u ∈ rows.attach, ‖∏ i ∈ slots.attach,
          normalizedMaskedPrimeSum (data u i) (W i.val) (X ^ ell i.val)
            (pool i.val) (keep u.val i.val)‖ ^ 2) ≤
          (Crows * ∏ i ∈ slots.attach,
            (maskedPrimeConstant δ (D i) (M i.val) (degreeBound i.val)
              (P₀ i) (H i.val) (B i.val)) ^ 2) *
              X ^ (e + ((2 * β - 1) * (∑ i ∈ slots, ell i) + ε)) := by
  obtain ⟨P₀, D, hconstants, hbound⟩ := exists_uniform_paired_prime_bound
    (fun i : {i // i ∈ slots} => W i.val)
    (fun i => hW i.val i.property) (fun i => hWs i.val i.property)
  refine ⟨P₀, D, hconstants, ?_⟩
  intro ρ α _ rows β δ X ε Crows e ell M degreeBound H B data pool keep
    hβ hβ' hδ hδ' hX hP hWin hH hcover hdeleted hrows hloss
  have hb := hbound rows.attach slots.attach β δ X ε Crows e
    (fun i => ell i.val) (fun i => M i.val) (fun i => degreeBound i.val)
    (fun i => H i.val) (fun i => B i.val) data (fun i => pool i.val)
    (fun u i => keep u.val i.val) hβ hβ' hδ hδ' hX
    (fun i _ => hP i.val i.property) (fun i _ => hWin i.val i.property)
    (fun u _ i _ => hH u i) (fun u _ i _ => hcover u i)
    (fun u _ i _ => hdeleted u i)
    (by simpa only [Finset.card_attach] using hrows)
    (by simpa only [Finset.sum_attach] using hloss)
  simpa only [Finset.sum_attach] using hb

#print axioms maskedPrimeConstant_nonneg
#print axioms primeBoundConstant_le_uniform
#print axioms finite_sum_eq_primeSum
#print axioms exists_uniform_masked_prime_bound
#print axioms exists_uniform_paired_prime_bound
#print axioms exists_uniform_paired_prime_bound_on_members

end PrimeCancellation.Paired
