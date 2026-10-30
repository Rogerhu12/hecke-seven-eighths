/-
Copyright (c) 2026 OpenAI. Released under the Apache 2.0 license.
-/
import PrimeCancellationPaired
import PrimeCancellationUniformProfiles

/-!
# A paired prime bound uniform in the source profiles

A single finite family of standard Schwartz seminorms, chosen before all
windows and models, controls the energy. The arithmetic data are supplied
only for members of the actual row and slot sets. Boolean masks require
explicit deletion bounds, available from `PrimeCancellationMaskCount`.
-/

noncomputable section
open MeasureTheory Set Complex
open scoped Topology BigOperators ContDiff SchwartzMap Classical

namespace PrimeCancellation.PairedProfiles

open Analytic Paired UniformProfiles PrimeCancellationPrimeSeries

def uniformConstant (δ C degreeBound H : ℝ) : ℝ :=
  24 * C * H / δ ^ 2 + degreeBound * (1 + Real.sqrt 2) +
    2 * degreeBound * Real.exp 4

theorem uniformConstant_nonneg (δ C degreeBound H : ℝ)
    (hC : 0 ≤ C) (hd : 0 ≤ degreeBound) (hH : 0 ≤ H) :
    0 ≤ uniformConstant δ C degreeBound H := by
  unfold uniformConstant
  positivity

theorem analyticConstant_le_uniform {F : ℂ → ℂ} {β : ℝ}
    (data : ZeroFreeData F β) (δ C degreeBound H : ℝ) (hC : 0 ≤ C)
    (hH : heightConstant data + 3 * (data.k : ℝ) ≤ H) :
    analyticConstant data δ C degreeBound ≤ uniformConstant δ C degreeBound H := by
  unfold analyticConstant uniformConstant
  gcongr

theorem windowBound_of_sourceSeminorm (s : Finset (ℕ × ℕ)) (hs : (0, 0) ∈ s)
    (W : SchwartzMap ℝ ℂ) (hW : Function.support (W : ℝ → ℂ) ⊆ Icc (1 : ℝ) 2) :
    WindowBound W (sourceSeminorm s W) := by
  refine ⟨sourceSeminorm_nonneg s W, hW, ?_⟩
  intro x
  have hle : schwartzSeminormFamily ℝ ℝ ℂ (0, 0) ≤
      s.sup (schwartzSeminormFamily ℝ ℝ ℂ) := Finset.le_sup hs
  exact (SchwartzMap.norm_le_seminorm ℝ W x).trans (Seminorm.le_def.mp hle W)

/-- The source-seminorm and constant are fixed before the window, the
arithmetic data and the mask. The mask cost is purely a deleted count. -/
theorem exists_uniform_masked_prime_seminorm_bound :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ (0, 0) ∈ s ∧
      ∀ {α : Type*} [Countable α] (W : SchwartzMap ℝ ℂ),
      Function.support (W : ℝ → ℂ) ⊆ Icc (1 : ℝ) 2 →
      ∀ (β δ degreeBound H B : ℝ) (data : SlotData α β degreeBound),
      heightConstant data.analytic + 3 * (data.analytic.k : ℝ) ≤ H →
      ∀ (P : ℝ) (pool : Finset α) (keep : α → Bool),
      1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 → 1 ≤ P →
      (∀ p : α, W (data.norm p / P) ≠ 0 → p ∈ pool) →
      ((pool.filter (fun p => keep p = false)).card : ℝ) ≤ B →
        ‖maskedPrimeSum data W P pool keep‖ ≤
          (uniformConstant δ C degreeBound H + B) * sourceSeminorm s W * P ^ (β + δ) := by
  obtain ⟨s, C, hC, hs, hprime⟩ := exists_uniform_prime_seminorm_bound
  refine ⟨s, C, hC, hs, ?_⟩
  intro α _ W hWs β δ degreeBound H B data hH P pool keep hβ hβ' hδ hδ' hP
    hcover hdeleted
  let M := sourceSeminorm s W
  have hWin := windowBound_of_sourceSeminorm s hs W hWs
  have hM : 0 ≤ M := hWin.nonneg
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hB : 0 ≤ B := (Nat.cast_nonneg _).trans hdeleted
  have hnorm (p : α) : ‖data.coefficient p * W (data.norm p / P)‖ ≤ M := by
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (data.arithmetic.coeff_bound p)
      (hWin.bound (data.norm p / P)) (norm_nonneg _) zero_le_one
  have hraw := hprime W hWs data.norm data.coefficient degreeBound data.arithmetic
    β data.function data.analytic data.absolute data.euler δ P hβ hβ' hδ hδ' hP
  have hbase : ‖primeSum data.norm data.coefficient W P‖ ≤
      uniformConstant δ C degreeBound H * M * P ^ (β + δ) :=
    hraw.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (analyticConstant_le_uniform data.analytic δ C degreeBound H hC.le hH) hM)
      (Real.rpow_nonneg hPpos.le _))
  have hmask := PrimeCancellationAux.norm_maskedSum_le_of_card pool
    (fun p => data.coefficient p * W (data.norm p / P)) keep M B hM
    (fun p _ _ => hnorm p) hdeleted
  rw [finite_sum_eq_primeSum data W P pool hcover] at hmask
  have hone : 1 ≤ P ^ (β + δ) := Real.one_le_rpow hP (by linarith)
  have hcost : B * M ≤ (B * M) * P ^ (β + δ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone (mul_nonneg hB hM)
  calc
    ‖maskedPrimeSum data W P pool keep‖ ≤
        ‖primeSum data.norm data.coefficient W P‖ + B * M := hmask
    _ ≤ uniformConstant δ C degreeBound H * M * P ^ (β + δ) + B * M :=
      add_le_add hbase le_rfl
    _ ≤ uniformConstant δ C degreeBound H * M * P ^ (β + δ) +
        (B * M) * P ^ (β + δ) := add_le_add le_rfl hcost
    _ = _ := by dsimp only [M]; ring

/-- General paired cancellation with a fixed finite source seminorm.

The structure `SlotData` is required only on the attached finite sets.
There is no analytic assumption about excluded or principal ambient rows.
-/
theorem exists_uniform_paired_seminorm_bound :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ (0, 0) ∈ s ∧
      ∀ {ρ ι α : Type*} [Countable α] (rows : Finset ρ) (slots : Finset ι)
        (W : ι → SchwartzMap ℝ ℂ)
        (β δ X ε Crows e : ℝ) (ell degreeBound H B : ι → ℝ)
        (data : {u // u ∈ rows} → (i : {i // i ∈ slots}) →
          SlotData α β (degreeBound i.val))
        (pool : ι → Finset α) (keep : ρ → ι → α → Bool),
      (∀ i ∈ slots, Function.support (W i : ℝ → ℂ) ⊆ Icc (1 : ℝ) 2) →
      1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 → 1 ≤ X →
      (∀ i ∈ slots, 1 ≤ X ^ ell i) →
      (∀ u i, heightConstant (data u i).analytic +
        3 * ((data u i).analytic.k : ℝ) ≤ H i.val) →
      (∀ u i p, W i.val ((data u i).norm p / X ^ ell i.val) ≠ 0 → p ∈ pool i.val) →
      (∀ (u : {u // u ∈ rows}) (i : {i // i ∈ slots}), (((pool i.val).filter
        (fun p => keep u.val i.val p = false)).card : ℝ) ≤ B i.val) →
      (rows.card : ℝ) ≤ Crows * X ^ e → 2 * δ * (∑ i ∈ slots, ell i) ≤ ε →
        (∑ u ∈ rows.attach, ‖∏ i ∈ slots.attach,
          normalizedMaskedPrimeSum (data u i) (W i.val) (X ^ ell i.val)
            (pool i.val) (keep u.val i.val)‖ ^ 2) ≤
          (Crows * ∏ i ∈ slots,
            ((uniformConstant δ C (degreeBound i) (H i) + B i) *
              sourceSeminorm s (W i)) ^ 2) *
                X ^ (e + ((2 * β - 1) * (∑ i ∈ slots, ell i) + ε)) := by
  obtain ⟨s, C, hC, hs, hbound⟩ := exists_uniform_masked_prime_seminorm_bound
  refine ⟨s, C, hC, hs, ?_⟩
  intro ρ ι α _ rows slots W β δ X ε Crows e ell degreeBound H B data pool keep
    hWs hβ hβ' hδ hδ' hX hP hH hcover hdeleted hrows hloss
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  let K : {i // i ∈ slots} → ℝ := fun i =>
    (uniformConstant δ C (degreeBound i.val) (H i.val) + B i.val) *
      sourceSeminorm s (W i.val)
  have hslot (u : {u // u ∈ rows}) (_hu : u ∈ rows.attach)
      (i : {i // i ∈ slots}) (_hi : i ∈ slots.attach) :
      ‖normalizedMaskedPrimeSum (data u i) (W i.val) (X ^ ell i.val)
        (pool i.val) (keep u.val i.val)‖ ^ 2 ≤
        (K i) ^ 2 * X ^ ((2 * β - 1) * ell i.val + (2 * δ) * ell i.val) := by
    have hHnon : 0 ≤ H i.val :=
      (add_nonneg (heightConstant_nonneg (data u i).analytic) (by positivity)).trans (hH u i)
    have hBnon : 0 ≤ B i.val := (Nat.cast_nonneg _).trans (hdeleted u i)
    have hK : 0 ≤ K i := mul_nonneg
      (add_nonneg (uniformConstant_nonneg δ C (degreeBound i.val) (H i.val)
        hC.le (data u i).arithmetic.d_nonneg hHnon) hBnon)
      (sourceSeminorm_nonneg s (W i.val))
    have hb := hbound (W i.val) (hWs i.val i.property)
      β δ (degreeBound i.val) (H i.val) (B i.val) (data u i) (hH u i)
      (X ^ ell i.val) (pool i.val) (keep u.val i.val)
      hβ hβ' hδ hδ' (hP i.val i.property) (hcover u i) (hdeleted u i)
    have hn := PrimeCancellationAux.norm_normalized_sq_le_rpow
      (X ^ ell i.val) (β + δ) (K i) (Real.rpow_pos_of_pos hXpos _) hK
      (maskedPrimeSum (data u i) (W i.val) (X ^ ell i.val)
        (pool i.val) (keep u.val i.val)) hb
    change ‖normalizedMaskedPrimeSum (data u i) (W i.val) (X ^ ell i.val)
      (pool i.val) (keep u.val i.val)‖ ^ 2 ≤
        (K i) ^ 2 * (X ^ ell i.val) ^ (2 * (β + δ) - 1) at hn
    rw [← Real.rpow_mul hXpos.le] at hn
    have hexp : ell i.val * (2 * (β + δ) - 1) =
        (2 * β - 1) * ell i.val + (2 * δ) * ell i.val := by ring
    rw [hexp] at hn
    exact hn
  have hrows' : (rows.attach.card : ℝ) ≤ Crows * X ^ e := by simpa using hrows
  have hloss' : (∑ i ∈ slots.attach, (2 * δ) * ell i.val) ≤ ε := by
    simpa only [← Finset.mul_sum, Finset.sum_attach] using hloss
  have henergy := PrimeCancellationAux.paired_sum_le_of_slot_bounds rows.attach slots.attach
    (fun u i => normalizedMaskedPrimeSum (data u i) (W i.val) (X ^ ell i.val)
      (pool i.val) (keep u.val i.val))
    (fun i => (K i) ^ 2) (fun i => ell i.val) (fun i => (2 * δ) * ell i.val)
    X (2 * β - 1) ε Crows e hX (fun i _ => sq_nonneg (K i)) hrows' hloss' hslot
  have hprod : (∏ i ∈ slots.attach, (K i) ^ 2) =
      ∏ i ∈ slots,
        ((uniformConstant δ C (degreeBound i) (H i) + B i) *
          sourceSeminorm s (W i)) ^ 2 := by
    dsimp only [K]
    exact Finset.prod_attach slots (fun i =>
      ((uniformConstant δ C (degreeBound i) (H i) + B i) *
        sourceSeminorm s (W i)) ^ 2)
  rw [hprod] at henergy
  simpa only [Finset.sum_attach] using henergy

end PrimeCancellation.PairedProfiles

#print axioms PrimeCancellation.PairedProfiles.uniformConstant_nonneg
#print axioms PrimeCancellation.PairedProfiles.analyticConstant_le_uniform
#print axioms PrimeCancellation.PairedProfiles.windowBound_of_sourceSeminorm
#print axioms PrimeCancellation.PairedProfiles.exists_uniform_masked_prime_seminorm_bound
#print axioms PrimeCancellation.PairedProfiles.exists_uniform_paired_seminorm_bound
