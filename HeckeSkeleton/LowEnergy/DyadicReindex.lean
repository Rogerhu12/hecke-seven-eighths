import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Order.Interval.Finset.Nat
import HeckeSkeleton.LowEnergy.InactiveCore
import Lean.Elab.Tactic.Omega

/-!
# Exact dyadic decomposition of positive integral norms

The index is the actual integer logarithm of the norm.  Every positive norm
belongs to exactly one half-open shell, including norms that are powers of
two.  Finite norm balls give actual finite column blocks.  The double dyadic
sum is obtained from the original summable series by its fibre equivalence;
no independent block-convergence or block-energy assumption is introduced.

For a finite original row set with norm at most X, the number of residual
row shells is at most log(X)/log(2)+1.  These shells partition row energy.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.DyadicReindex
open scoped BigOperators Classical

variable {ι : Type*}

def index (normI : ι → ℕ) (i : ι) : ℕ := Nat.log 2 (normI i)

theorem index_bounds (normI : ι → ℕ) {i : ι} (hi : 0 < normI i) :
    2 ^ index normI i ≤ normI i ∧ normI i < 2 ^ (index normI i + 1) := by
  exact ⟨Nat.pow_log_le_self 2 hi.ne',
    Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) (normI i)⟩

theorem index_eq_iff (normI : ι → ℕ) {i : ι} (hi : 0 < normI i) (j : ℕ) :
    index normI i = j ↔ 2 ^ j ≤ normI i ∧ normI i < 2 ^ (j + 1) :=
  Nat.log_eq_iff (Or.inr ⟨by decide, hi.ne'⟩)

theorem index_bounds_real (normI : ι → ℕ) {i : ι} (hi : 0 < normI i) :
    (2 : ℝ) ^ index normI i ≤ (normI i : ℝ) ∧
      (normI i : ℝ) < (2 : ℝ) ^ (index normI i + 1) := by
  obtain ⟨hl, hu⟩ := index_bounds normI hi
  exact ⟨by exact_mod_cast hl, by exact_mod_cast hu⟩

/-- Finiteness of actual norm balls suffices for the shell construction. -/
theorem finite_index_fiber (normI : ι → ℕ)
    (hballs : ∀ N : ℕ, Set.Finite {i | normI i ≤ N}) (j : ℕ) :
    Set.Finite {i | index normI i = j} := by
  apply (hballs (2 ^ (j + 1))).subset
  intro i hi
  have hu : normI i < 2 ^ (index normI i + 1) :=
    Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) (normI i)
  rw [show index normI i = j from hi] at hu
  exact hu.le

def shell (normI : ι → ℕ)
    (hballs : ∀ N : ℕ, Set.Finite {i | normI i ≤ N}) (j : ℕ) : Finset ι :=
  (finite_index_fiber normI hballs j).toFinset

@[simp] theorem mem_shell (normI : ι → ℕ)
    (hballs : ∀ N : ℕ, Set.Finite {i | normI i ≤ N}) (j : ℕ) (i : ι) :
    i ∈ shell normI hballs j ↔ index normI i = j := by
  simp only [shell, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

theorem shell_disjoint (normI : ι → ℕ)
    (hballs : ∀ N : ℕ, Set.Finite {i | normI i ≤ N}) {j l : ℕ} (hjl : j ≠ l) :
    Disjoint (shell normI hballs j) (shell normI hballs l) := by
  apply Finset.disjoint_left.mpr
  intro i hj hl
  exact hjl ((mem_shell normI hballs j i).mp hj |>.symm.trans
    ((mem_shell normI hballs l i).mp hl))

theorem fiber_tsum_eq_shell_sum (normI : ι → ℕ)
    (hballs : ∀ N : ℕ, Set.Finite {i | normI i ≤ N}) (f : ι → ℂ) (j : ℕ) :
    (∑' i : {i // index normI i = j}, f i) = ∑ i ∈ shell normI hballs j, f i := by
  have hs : {i | index normI i = j} = (shell normI hballs j : Set ι) := by
    ext i
    exact (mem_shell normI hballs j i).symm
  change (∑' i : ({i | index normI i = j} : Set ι), f i) = _
  rw [hs]
  exact Finset.tsum_subtype _ f

/-- Every finite dyadic block is obtained from the original summable
series.  The block series is therefore summable as well. -/
theorem summable_shell_sums (normI : ι → ℕ)
    (hballs : ∀ N : ℕ, Set.Finite {i | normI i ≤ N})
    (f : ι → ℂ) (hf : Summable f) :
    Summable (fun j => ∑ i ∈ shell normI hballs j, f i) := by
  have h := (hf.hasSum.tsum_fiberwise (index normI)).summable
  exact h.congr (fun j => fiber_tsum_eq_shell_sum normI hballs f j)

theorem tsum_eq_shell_sums (normI : ι → ℕ)
    (hballs : ∀ N : ℕ, Set.Finite {i | normI i ≤ N})
    (f : ι → ℂ) (hf : Summable f) :
    (∑' i, f i) = ∑' j : ℕ, ∑ i ∈ shell normI hballs j, f i := by
  calc
    (∑' i, f i) = ∑' j : ℕ, ∑' i : {i // index normI i = j}, f i :=
      (hf.hasSum.tsum_fiberwise (index normI)).tsum_eq.symm
    _ = ∑' j : ℕ, ∑ i ∈ shell normI hballs j, f i :=
      tsum_congr (fiber_tsum_eq_shell_sum normI hballs f)

def pairIndex (normN normB : ι → ℕ) (i : ι) : ℕ × ℕ :=
  (index normN i, index normB i)

theorem finite_pair_fiber (normN normB : ι → ℕ)
    (hballs : ∀ M N : ℕ, Set.Finite {i | normN i ≤ M ∧ normB i ≤ N})
    (j l : ℕ) : Set.Finite {i | index normN i = j ∧ index normB i = l} := by
  apply (hballs (2 ^ (j + 1)) (2 ^ (l + 1))).subset
  intro i hi
  have hn : normN i < 2 ^ (index normN i + 1) :=
    Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) (normN i)
  have hb : normB i < 2 ^ (index normB i + 1) :=
    Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) (normB i)
  rw [hi.1] at hn
  rw [hi.2] at hb
  exact ⟨hn.le, hb.le⟩

def pairShell (normN normB : ι → ℕ)
    (hballs : ∀ M N : ℕ, Set.Finite {i | normN i ≤ M ∧ normB i ≤ N})
    (j l : ℕ) : Finset ι :=
  (finite_pair_fiber normN normB hballs j l).toFinset

@[simp] theorem mem_pairShell (normN normB : ι → ℕ)
    (hballs : ∀ M N : ℕ, Set.Finite {i | normN i ≤ M ∧ normB i ≤ N})
    (j l : ℕ) (i : ι) :
    i ∈ pairShell normN normB hballs j l ↔ index normN i = j ∧ index normB i = l := by
  simp only [pairShell, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

theorem pair_fiber_tsum_eq_sum (normN normB : ι → ℕ)
    (hballs : ∀ M N : ℕ, Set.Finite {i | normN i ≤ M ∧ normB i ≤ N})
    (f : ι → ℂ) (p : ℕ × ℕ) :
    (∑' i : {i // pairIndex normN normB i = p}, f i) =
      ∑ i ∈ pairShell normN normB hballs p.1 p.2, f i := by
  have hs : {i | pairIndex normN normB i = p} =
      (pairShell normN normB hballs p.1 p.2 : Set ι) := by
    ext i
    simp only [Set.mem_setOf_eq, pairIndex, Prod.ext_iff, Finset.mem_coe, mem_pairShell]
  change (∑' i : ({i | pairIndex normN normB i = p} : Set ι), f i) = _
  rw [hs]
  exact Finset.tsum_subtype _ f

theorem summable_pair_shell_sums (normN normB : ι → ℕ)
    (hballs : ∀ M N : ℕ, Set.Finite {i | normN i ≤ M ∧ normB i ≤ N})
    (f : ι → ℂ) (hf : Summable f) :
    Summable (fun p : ℕ × ℕ => ∑ i ∈ pairShell normN normB hballs p.1 p.2, f i) := by
  have h := (hf.hasSum.tsum_fiberwise (pairIndex normN normB)).summable
  exact h.congr (pair_fiber_tsum_eq_sum normN normB hballs f)

/-- The two column dyads are reindexed from the original summable series,
including every original support condition in the finite pair shell. -/
theorem tsum_eq_double_shell_sums (normN normB : ι → ℕ)
    (hballs : ∀ M N : ℕ, Set.Finite {i | normN i ≤ M ∧ normB i ≤ N})
    (f : ι → ℂ) (hf : Summable f) :
    (∑' i, f i) = ∑' j : ℕ, ∑' l : ℕ, ∑ i ∈ pairShell normN normB hballs j l, f i := by
  calc
    (∑' i, f i) = ∑' p : ℕ × ℕ, ∑' i : {i // pairIndex normN normB i = p}, f i :=
      (hf.hasSum.tsum_fiberwise (pairIndex normN normB)).tsum_eq.symm
    _ = ∑' p : ℕ × ℕ, ∑ i ∈ pairShell normN normB hballs p.1 p.2, f i :=
      tsum_congr (pair_fiber_tsum_eq_sum normN normB hballs f)
    _ = ∑' j : ℕ, ∑' l : ℕ, ∑ i ∈ pairShell normN normB hballs j l, f i :=
      (summable_pair_shell_sums normN normB hballs f hf).tsum_prod

theorem summable_double_shell_sums (normN normB : ι → ℕ)
    (hballs : ∀ M N : ℕ, Set.Finite {i | normN i ≤ M ∧ normB i ≤ N})
    (f : ι → ℂ) (hf : Summable f) :
    (∀ j : ℕ, Summable (fun l : ℕ => ∑ i ∈ pairShell normN normB hballs j l, f i)) ∧
      Summable (fun j : ℕ => ∑' l : ℕ, ∑ i ∈ pairShell normN normB hballs j l, f i) := by
  have h := summable_pair_shell_sums normN normB hballs f hf
  exact ⟨h.prod_factor, h.prod⟩

/-- Actual support bounds for the two coefficient arrays of one block. -/
theorem pairShell_norm_bounds (normN normB : ι → ℕ)
    (hballs : ∀ M N : ℕ, Set.Finite {i | normN i ≤ M ∧ normB i ≤ N})
    (j l : ℕ) {i : ι} (hi : i ∈ pairShell normN normB hballs j l)
    (hn : 0 < normN i) (hb : 0 < normB i) :
    ((2 : ℝ) ^ j ≤ (normN i : ℝ) ∧ (normN i : ℝ) < 2 * (2 : ℝ) ^ j) ∧
      ((2 : ℝ) ^ l ≤ (normB i : ℝ) ∧ (normB i : ℝ) < 2 * (2 : ℝ) ^ l) := by
  have hindex := (mem_pairShell normN normB hballs j l i).mp hi
  constructor
  · simpa only [hindex.1, pow_succ, mul_comm] using index_bounds_real normN hn
  · simpa only [hindex.2, pow_succ, mul_comm] using index_bounds_real normB hb

/-- For independent column ideals, the finite pair shell is exactly the
product of its two actual finite ideal shells. -/
theorem pairShell_product {α β : Type*} (normN : α → ℕ) (normB : β → ℕ)
    (hN : ∀ M : ℕ, Set.Finite {n | normN n ≤ M})
    (hB : ∀ N : ℕ, Set.Finite {b | normB b ≤ N}) (j l : ℕ) :
    pairShell (fun p : α × β => normN p.1) (fun p : α × β => normB p.2)
      (fun M N => (hN M).prod (hB N)) j l =
      shell normN hN j ×ˢ shell normB hB l := by
  ext p
  simp only [pairShell, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
    Finset.mem_product, mem_shell, index]

/-- Literal two-column form for use by the raw ideal hybrid theorem. -/
theorem tsum_eq_double_product_shell_sums {α β : Type*}
    (normN : α → ℕ) (normB : β → ℕ)
    (hN : ∀ M : ℕ, Set.Finite {n | normN n ≤ M})
    (hB : ∀ N : ℕ, Set.Finite {b | normB b ≤ N})
    (f : α × β → ℂ) (hf : Summable f) :
    (∑' p, f p) = ∑' j : ℕ, ∑' l : ℕ,
      ∑ n ∈ shell normN hN j, ∑ b ∈ shell normB hB l, f (n, b) := by
  have h := tsum_eq_double_shell_sums
    (fun p : α × β => normN p.1) (fun p : α × β => normB p.2)
    (fun M N => (hN M).prod (hB N)) f hf
  refine h.trans ?_
  apply tsum_congr
  intro j
  apply tsum_congr
  intro l
  rw [pairShell_product normN normB hN hB j l, Finset.sum_product]

def shellCount (X : ℝ) : ℕ := Nat.log 2 ⌊X⌋₊ + 1

theorem index_lt_shellCount (normI : ι → ℕ) (X : ℝ) {i : ι}
    (hi : (normI i : ℝ) ≤ X) : index normI i < shellCount X :=
  Nat.lt_succ_of_le (Nat.log_mono_right (Nat.le_floor hi))

/-- The bound is uniform down to X=1 and has only a logarithmic shell cost. -/
theorem shellCount_le_log {X : ℝ} (hX : 1 ≤ X) :
    (shellCount X : ℝ) ≤ Real.log X / Real.log 2 + 1 := by
  have hfloor : 1 ≤ ⌊X⌋₊ := (Nat.one_le_floor_iff X).mpr hX
  have hfloorpos : (0 : ℝ) < (⌊X⌋₊ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hfloor)
  have hnat : (Nat.log 2 ⌊X⌋₊ : ℝ) ≤ Real.log (⌊X⌋₊ : ℝ) / Real.log 2 := by
    simpa only [Real.logb, Nat.cast_ofNat] using Real.natLog_le_logb ⌊X⌋₊ 2
  have hmono : Real.log (⌊X⌋₊ : ℝ) ≤ Real.log X :=
    Real.log_le_log hfloorpos (Nat.floor_le (zero_le_one.trans hX))
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hidx := hnat.trans (div_le_div_of_nonneg_right hmono htwo.le)
  simpa only [shellCount, Nat.cast_add, Nat.cast_one, add_comm] using add_le_add_right hidx 1

theorem shellCount_le_log_add_two {X : ℝ} (hX : 1 ≤ X) :
    (shellCount X : ℝ) ≤ Real.log X / Real.log 2 + 2 := by
  linarith [shellCount_le_log hX]

theorem finite_shell_image_card_le (normI : ι → ℕ) (rows : Finset ι)
    (X : ℝ) (hcut : ∀ i ∈ rows, (normI i : ℝ) ≤ X) :
    (rows.image (index normI)).card ≤ shellCount X := by
  have hs : rows.image (index normI) ⊆ Finset.range (shellCount X) := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (index_lt_shellCount normI X (hcut i hi))
  simpa only [Finset.card_range] using Finset.card_le_card hs

theorem finite_shell_image_card_le_log (normI : ι → ℕ) (rows : Finset ι)
    {X : ℝ} (hX : 1 ≤ X) (hcut : ∀ i ∈ rows, (normI i : ℝ) ≤ X) :
    ((rows.image (index normI)).card : ℝ) ≤ Real.log X / Real.log 2 + 1 := by
  exact (Nat.cast_le.mpr (finite_shell_image_card_le normI rows X hcut)).trans
    (shellCount_le_log hX)

/-- Residual row shells partition original row energy; they are not an
outer amplitude index and incur no Cauchy cardinality loss. -/
theorem finite_sum_eq_shell_sums (normI : ι → ℕ) (rows : Finset ι)
    (X : ℝ) (hcut : ∀ i ∈ rows, (normI i : ℝ) ≤ X) (E : ι → ℝ) :
    (∑ i ∈ rows, E i) =
      ∑ j ∈ Finset.range (shellCount X),
        ∑ i ∈ rows.filter (fun i => index normI i = j), E i := by
  exact (Finset.sum_fiberwise_of_maps_to
    (fun i hi => Finset.mem_range.mpr (index_lt_shellCount normI X (hcut i hi))) E).symm

/-- A physical product window of multiplicative width `2^r` meets at most
`r+1` dyadic shells, uniformly in its location.  This is the fixed cost
needed to put the active marked ideal into a single ratio-two dyad. -/
theorem index_mem_window_interval (normI : ι → ℕ) {i : ι} {X : ℝ}
    (hX : 1 ≤ X) (r : ℕ)
    (hl : X ≤ (normI i : ℝ)) (hu : (normI i : ℝ) ≤ (2 : ℝ) ^ r * X) :
    index normI i ∈ Finset.Ico (Nat.log 2 ⌊X⌋₊) (Nat.log 2 ⌊X⌋₊ + r + 1) := by
  have hi : 0 < normI i := by
    have hi' : (0 : ℝ) < (normI i : ℝ) := zero_lt_one.trans_le (hX.trans hl)
    exact_mod_cast hi'
  have hlog : Nat.log 2 ⌊X⌋₊ ≤ index normI i :=
    Nat.log_mono_right (Nat.floor_le_of_le hl)
  have hXpow : X < (2 : ℝ) ^ (Nat.log 2 ⌊X⌋₊ + 1) := by
    apply (Nat.lt_floor_add_one X).trans_le
    exact_mod_cast Nat.succ_le_of_lt
      (Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) ⌊X⌋₊)
  have hu' : (normI i : ℝ) < (2 : ℝ) ^ (Nat.log 2 ⌊X⌋₊ + r + 1) := by
    calc
      _ ≤ (2 : ℝ) ^ r * X := hu
      _ < (2 : ℝ) ^ r * (2 : ℝ) ^ (Nat.log 2 ⌊X⌋₊ + 1) :=
        mul_lt_mul_of_pos_left hXpow (pow_pos (by norm_num) _)
      _ = (2 : ℝ) ^ (Nat.log 2 ⌊X⌋₊ + r + 1) := by
        rw [← pow_add]
        congr 1
        omega
  have huN : normI i < 2 ^ (Nat.log 2 ⌊X⌋₊ + r + 1) := by exact_mod_cast hu'
  exact Finset.mem_Ico.mpr ⟨hlog, Nat.log_lt_of_lt_pow hi.ne' huN⟩

theorem window_shell_image_card_le (normI : ι → ℕ) (columns : Finset ι)
    {X : ℝ} (hX : 1 ≤ X) (r : ℕ)
    (hwindow : ∀ i ∈ columns,
      X ≤ (normI i : ℝ) ∧ (normI i : ℝ) ≤ (2 : ℝ) ^ r * X) :
    (columns.image (index normI)).card ≤ r + 1 := by
  have hs : columns.image (index normI) ⊆
      Finset.Ico (Nat.log 2 ⌊X⌋₊) (Nat.log 2 ⌊X⌋₊ + r + 1) := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact index_mem_window_interval normI hX r (hwindow i hi).1 (hwindow i hi).2
  simpa only [Nat.card_Ico, Nat.add_sub_cancel_left, Nat.add_assoc] using
    Finset.card_le_card hs

/-- Active mark dyads are split before taking the row norm. -/
theorem finite_sum_eq_window_shells (normI : ι → ℕ) (columns : Finset ι)
    {X : ℝ} (hX : 1 ≤ X) (r : ℕ)
    (hwindow : ∀ i ∈ columns,
      X ≤ (normI i : ℝ) ∧ (normI i : ℝ) ≤ (2 : ℝ) ^ r * X)
    (f : ι → ℂ) :
    (∑ i ∈ columns, f i) =
      ∑ j ∈ Finset.Ico (Nat.log 2 ⌊X⌋₊) (Nat.log 2 ⌊X⌋₊ + r + 1),
        ∑ i ∈ columns.filter (fun i => index normI i = j), f i := by
  exact (Finset.sum_fiberwise_of_maps_to
    (fun i hi => index_mem_window_interval normI hX r
      (hwindow i hi).1 (hwindow i hi).2) f).symm

/-- Only a fixed geometry cost is paid when recombining the finitely many
active mark dyads.  The row itself is never reindexed by its mask divisor. -/
theorem finite_window_shell_energy {κ : Type*}
    (normI : ι → ℕ) (columns : Finset ι) (rows : Finset κ)
    {X : ℝ} (hX : 1 ≤ X) (r : ℕ)
    (hwindow : ∀ i ∈ columns,
      X ≤ (normI i : ℝ) ∧ (normI i : ℝ) ≤ (2 : ℝ) ^ r * X)
    (v : κ → ι → ℂ) {E : ℝ} (hE : 0 ≤ E)
    (hblock : ∀ j ∈ Finset.Ico (Nat.log 2 ⌊X⌋₊) (Nat.log 2 ⌊X⌋₊ + r + 1),
      (∑ k ∈ rows, ‖∑ i ∈ columns.filter (fun i => index normI i = j), v k i‖ ^ 2) ≤ E) :
    (∑ k ∈ rows, ‖∑ i ∈ columns, v k i‖ ^ 2) ≤ (r + 1 : ℝ) ^ 2 * E := by
  let js := Finset.Ico (Nat.log 2 ⌊X⌋₊) (Nat.log 2 ⌊X⌋₊ + r + 1)
  have h := InactiveCore.finite_weighted_energy_le js rows (fun _ => (1 : ℂ))
    (fun j k => ∑ i ∈ columns.filter (fun i => index normI i = j), v k i) hblock
  have hcard : js.card = r + 1 := by
    simp only [js, Nat.card_Ico, Nat.add_assoc, Nat.add_sub_cancel_left]
  simp only [one_mul, norm_one, Finset.sum_const, nsmul_eq_mul, mul_one, hcard,
    Nat.cast_add, Nat.cast_one] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro k _
  rw [finite_sum_eq_window_shells normI columns hX r hwindow]

#print axioms index_eq_iff
#print axioms tsum_eq_double_shell_sums
#print axioms summable_double_shell_sums
#print axioms shellCount_le_log
#print axioms window_shell_image_card_le
#print axioms finite_window_shell_energy
#print axioms finite_sum_eq_shell_sums

end HeckeSkeleton.LowEnergy.DyadicReindex
