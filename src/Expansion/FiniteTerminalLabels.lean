import Expansion.DetectorProductBudget
import HeckeSkeleton.ExpansionModels.FixedSectorParameters
import Mathlib.Data.Fintype.Prod

/-!
# Finite labels for the actual terminal dyadic choices

The only discrete choices are one of the two canonical characters and the
actual two dyadic indices. Continuous zero and Fourier parameters remain
rowwise parameters in the fixed six-dimensional recipe. Every label has
admissible lengths: labels outside the genuine support geometry receive
lengths `(t, 0)` and have empty chosen-row fibers.

This is a finite assembly adapter. Its local relation is to be supplied by
the actual canonical row saturation theorem; no analytic detector or
polynomial estimate is asserted by a data field here.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Dyadic

open scoped Classical

abbrev TerminalLabel (U : ℝ) :=
  Fin 2 × (Fin (dyadicCap (3 * U ^ (21 : ℕ)) + 1) ×
    Fin (dyadicCap (3 * U ^ (21 : ℕ)) + 1))

def terminalLabelCount (U : ℝ) : ℕ := Fintype.card (TerminalLabel U)

theorem terminalLabelCount_eq (U : ℝ) :
    terminalLabelCount U = 2 * (dyadicCap (3 * U ^ (21 : ℕ)) + 1) ^ 2 := by
  simp [terminalLabelCount, TerminalLabel, pow_two]

theorem terminalLabelCount_pos (U : ℝ) : 0 < terminalLabelCount U := by
  rw [terminalLabelCount_eq]
  positivity

def encodeTerminalLabel (U : ℝ) : TerminalLabel U ≃ Fin (terminalLabelCount U) :=
  Fintype.equivFin (TerminalLabel U)

def defaultTerminalLabel (U : ℝ) : TerminalLabel U := (0, 0, 0)

/-- The predicate is exactly the four unconditional length requirements
in the repository's `WitnessCover`. -/
def terminalLabelValid (U t lam : ℝ) (l : TerminalLabel U) : Prop :=
  0 ≤ dyadicLength U l.2.1 ∧ 0 ≤ dyadicLength U l.2.2 ∧
    dyadicLength U l.2.1 ≤ t + lam ∧
    t - lam ≤ dyadicLength U l.2.1 + dyadicLength U l.2.2

def terminalLabelInverseLength (U t lam : ℝ) (l : TerminalLabel U) : ℝ :=
  if terminalLabelValid U t lam l then dyadicLength U l.2.1 else t

def terminalLabelPlainLength (U t lam : ℝ) (l : TerminalLabel U) : ℝ :=
  if terminalLabelValid U t lam l then dyadicLength U l.2.2 else 0

theorem terminalLabel_lengths (U t lam : ℝ) (ht : 0 ≤ t) (hlam : 0 ≤ lam)
    (l : TerminalLabel U) :
    0 ≤ terminalLabelInverseLength U t lam l ∧
    0 ≤ terminalLabelPlainLength U t lam l ∧
    terminalLabelInverseLength U t lam l ≤ t + lam ∧
    t - lam ≤ terminalLabelInverseLength U t lam l + terminalLabelPlainLength U t lam l := by
  by_cases hl : terminalLabelValid U t lam l
  · simp only [terminalLabelInverseLength, terminalLabelPlainLength, if_pos hl]
    exact hl
  · simp only [terminalLabelInverseLength, terminalLabelPlainLength, if_neg hl, add_zero]
    exact ⟨ht, le_rfl, by linarith, by linarith⟩

theorem terminalLabel_lengths_of_valid {U t lam : ℝ} {l : TerminalLabel U}
    (hl : terminalLabelValid U t lam l) :
    terminalLabelInverseLength U t lam l = dyadicLength U l.2.1 ∧
      terminalLabelPlainLength U t lam l = dyadicLength U l.2.2 := by
  simp only [terminalLabelInverseLength, terminalLabelPlainLength, if_pos hl, and_self]

/-- Every terminal label has a uniformly bounded nonnegative plain length.
This includes unused labels, whose plain length is zero.  The bound is
fixed before the source exponent, row, zero, and dyadic label are chosen. -/
theorem terminalLabel_plainLength_range {U : ℝ} (hU : 6 ≤ U)
    (t lam : ℝ) (l : TerminalLabel U) :
    0 ≤ terminalLabelPlainLength U t lam l ∧
      terminalLabelPlainLength U t lam l ≤ 22 := by
  by_cases hl : terminalLabelValid U t lam l
  · simp only [terminalLabelPlainLength, if_pos hl]
    exact ⟨hl.2.1, terminal_dyadicLength_le hU (Nat.le_of_lt_succ l.2.2.isLt)⟩
  · simp only [terminalLabelPlainLength, if_neg hl]
    norm_num

/-- The full retained shell range only guarantees `U ≥ 2`.  Its complete
terminal dyadic list still has the fixed length bound 24. -/
theorem terminal_dyadicLength_le_twenty_four {U : ℝ} (hU : 2 ≤ U) {j : ℕ}
    (hj : j ≤ dyadicCap (3 * U ^ (21 : ℕ))) : dyadicLength U j ≤ 24 := by
  have hUone : 1 < U := by linarith
  have hlogU : 0 < Real.log U := Real.log_pos hUone
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : Real.log 3 + Real.log 2 ≤ 3 * Real.log U := by
    calc
      _ = Real.log 6 := by
        rw [← Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
          (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num
      _ ≤ Real.log ((2 : ℝ) ^ (3 : ℕ)) :=
        Real.log_le_log (by norm_num) (by norm_num)
      _ = 3 * Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ 3 * Real.log U := mul_le_mul_of_nonneg_left
        (Real.log_le_log (by norm_num) hU) (by norm_num)
  have hcap := dyadicCap_terminal_le hUone.le
  rw [Real.rpow_ofNat] at hcap
  have hj' : (j : ℝ) ≤ (dyadicCap (3 * U ^ (21 : ℕ)) : ℝ) := by exact_mod_cast hj
  have hlen : (j : ℝ) * Real.log 2 ≤ 24 * Real.log U := by
    have hh := mul_le_mul_of_nonneg_right (hj'.trans hcap) hlog2.le
    have heq : ((21 / Real.log 2) * Real.log U +
        (Real.log 3 / Real.log 2 + 1)) * Real.log 2 =
          21 * Real.log U + Real.log 3 + Real.log 2 := by field_simp [hlog2.ne']; ring
    rw [heq] at hh
    linarith
  unfold dyadicLength
  rw [Real.log_pow]
  exact (div_le_iff₀ hlogU).mpr hlen

/-- A common plain-length range valid on every retained physical shell,
before any asymptotic threshold is imposed. -/
theorem terminalLabel_plainLength_range_two {U : ℝ} (hU : 2 ≤ U)
    (t lam : ℝ) (l : TerminalLabel U) :
    0 ≤ terminalLabelPlainLength U t lam l ∧
      terminalLabelPlainLength U t lam l ≤ 24 := by
  by_cases hl : terminalLabelValid U t lam l
  · simp only [terminalLabelPlainLength, if_pos hl]
    exact ⟨hl.2.1,
      terminal_dyadicLength_le_twenty_four hU (Nat.le_of_lt_succ l.2.2.isLt)⟩
  · simp only [terminalLabelPlainLength, if_neg hl]
    norm_num

/-- One threshold handles all source exponents and selected dyadic pairs.
The original cutoff stays `D = U^t`, exactly as in `RecipeWitnessData.model`. -/
theorem exists_terminal_label_support (lam : ℝ) (hlam : 0 < lam) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ t : ℝ, ∀ l : TerminalLabel U,
      (2 : ℝ) ^ (l.2.1 : ℕ) < 4 * U ^ t →
      U ^ t / 8 < (2 : ℝ) ^ (l.2.1 : ℕ) * (2 : ℝ) ^ (l.2.2 : ℕ) →
      terminalLabelValid U t lam l := by
  obtain ⟨U₀, hU₀, hsmall⟩ := exists_fixed_log_loss 8 lam hlam
  refine ⟨U₀, hU₀, ?_⟩
  intro U hU t l hleft hproduct
  have hUgt : 1 < U := by linarith [hU₀.trans hU]
  have h8 := hsmall U hU
  have h4 : Real.log 4 / Real.log U ≤ lam :=
    (div_le_div_of_nonneg_right
      (Real.log_le_log (by norm_num) (by norm_num : (4 : ℝ) ≤ 8))
      (Real.log_pos hUgt).le).trans h8
  have hleft' : U ^ dyadicLength U l.2.1 < 4 * U ^ t := by
    simpa only [rpow_dyadicLength hUgt] using hleft
  have hproduct' : U ^ t / 8 <
      U ^ dyadicLength U l.2.1 * U ^ dyadicLength U l.2.2 := by
    simpa only [rpow_dyadicLength hUgt] using hproduct
  obtain ⟨hr, hm⟩ := witness_length_bounds hUgt hleft' hproduct'
  exact ⟨dyadicLength_nonneg hUgt _, dyadicLength_nonneg hUgt _,
    by linarith, by linarith⟩

/-- A concrete subpower count for the two canonical presentations and both
dyadic labels. No row, zero, or frequency enters this constant. -/
theorem terminalLabelCount_subpower (lam : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U →
      (terminalLabelCount U : ℝ) ≤ C * U ^ lam := by
  let A := (21 / Real.log 2) / (lam / 2) + Real.log 3 / Real.log 2 + 2
  have hA : 0 < A := by
    have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hthree : 0 < Real.log 3 := Real.log_pos (by norm_num)
    unfold A
    positivity
  refine ⟨2 * A ^ 2, by positivity, ?_⟩
  intro U hU
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hcount := terminal_dyadic_count_subpower hU (show 0 < lam / 2 by positivity)
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount 2
  push_cast at hsq
  have hp : (U ^ (lam / 2)) ^ 2 = U ^ lam := by
    rw [← Real.rpow_mul_natCast hUpos.le]
    congr 1
    norm_num
  rw [terminalLabelCount_eq]
  push_cast
  calc
    _ ≤ 2 * (A * U ^ (lam / 2)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = _ := by simp only [mul_pow, hp, mul_assoc]

variable {Row : Type*}

/-- Select the finite label first. Continuous parameters can then be
assembled separately on each exact label fiber. -/
def chooseTerminalLabel (U : ℝ) (rows : Finset Row)
    (P : Row → TerminalLabel U → Prop)
    (hlocal : ∀ u ∈ rows, ∃ l, P u l) (u : Row) : TerminalLabel U :=
  if hu : u ∈ rows then Classical.choose (hlocal u hu) else defaultTerminalLabel U

theorem chooseTerminalLabel_spec (U : ℝ) (rows : Finset Row)
    (P : Row → TerminalLabel U → Prop)
    (hlocal : ∀ u ∈ rows, ∃ l, P u l) (u : Row) (hu : u ∈ rows) :
    P u (chooseTerminalLabel U rows P hlocal u) := by
  rw [chooseTerminalLabel, dif_pos hu]
  exact Classical.choose_spec (hlocal u hu)

def terminalLabelFiber (U : ℝ) (rows : Finset Row)
    (choice : Row → TerminalLabel U) (l : TerminalLabel U) : Finset Row :=
  rows.filter fun u => choice u = l

@[simp] theorem mem_terminalLabelFiber (U : ℝ) (rows : Finset Row)
    (choice : Row → TerminalLabel U) (l : TerminalLabel U) (u : Row) :
    u ∈ terminalLabelFiber U rows choice l ↔ u ∈ rows ∧ choice u = l := by
  simp only [terminalLabelFiber, Finset.mem_filter]

theorem terminalLabelFiber_cover (U : ℝ) (rows : Finset Row)
    (choice : Row → TerminalLabel U) :
    ∀ u ∈ rows, ∃ l, u ∈ terminalLabelFiber U rows choice l := by
  intro u hu
  exact ⟨choice u, (mem_terminalLabelFiber U rows choice _ u).mpr ⟨hu, rfl⟩⟩

theorem terminalLabelFiber_empty_of_invalid (U t lam : ℝ) (rows : Finset Row)
    (choice : Row → TerminalLabel U)
    (hchoice : ∀ u ∈ rows, terminalLabelValid U t lam (choice u))
    (l : TerminalLabel U) (hl : ¬terminalLabelValid U t lam l) :
    terminalLabelFiber U rows choice l = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨hu, heq⟩ := (mem_terminalLabelFiber U rows choice l u).mp hu
  exact hl (heq ▸ hchoice u hu)

/-- Raw ideal-indexed parameters for the concrete canonical recipe's
`scaledCanonicalRecipeWitness`. The default outside the sector is zero. -/
theorem assemble_terminal_raw_parameters_on_sector {Ideal Sector : Type*}
    (e : Row ↪ Ideal × Sector) (sector : Sector) (rows : Finset Row)
    (hsector : ∀ u ∈ rows, (e u).2 = sector) (C T : ℝ) (hC : 0 < C) (hT : 0 ≤ T)
    (P : Row → ℝ → ℝ → Prop)
    (hlocal : ∀ u ∈ rows, ∃ β ν : ℝ, |β| ≤ 1 ∧ |ν| ≤ C * T ∧ P u β ν) :
    ∃ β ν : Ideal → ℝ,
      (∀ I, |β I| ≤ 1) ∧ (∀ I, |ν I| ≤ C * T) ∧
      (∀ u ∈ rows, P u (β (e u).1) (ν (e u).1)) := by
  obtain ⟨p, hp, hexact⟩ := ExpansionRecipe.assemble_fixed_sector_parameters
    e sector rows hsector ((0, 0) : ℝ × ℝ)
    (fun q => |q.1| ≤ 1 ∧ |q.2| ≤ C * T)
    (by simp only [abs_zero]; exact ⟨by norm_num, mul_nonneg hC.le hT⟩)
    (fun u q => P u q.1 q.2) (by
      intro u hu
      obtain ⟨β, ν, hβ, hν, hP⟩ := hlocal u hu
      exact ⟨(β, ν), ⟨hβ, hν⟩, hP⟩)
  exact ⟨fun I => (p I).1, fun I => (p I).2,
    fun I => (hp I).1, fun I => (hp I).2, hexact⟩

/-- Fixed-sector assembly of the same real and imaginary parameters for
both factors. The local relation is left explicit, so the analytic source
must supply it before this purely finite adapter is applied. -/
theorem assemble_terminal_parameters_on_sector {Ideal Sector : Type*}
    (e : Row ↪ Ideal × Sector) (sector : Sector) (rows : Finset Row)
    (hsector : ∀ u ∈ rows, (e u).2 = sector) (C T : ℝ) (hC : 0 < C) (hT : 0 ≤ T)
    (P : Row → ℝ → ℝ → Prop)
    (hlocal : ∀ u ∈ rows, ∃ β ν : ℝ, |β| ≤ 1 ∧ |ν| ≤ C * T ∧ P u β ν) :
    ∃ σ τ : Ideal → Fin 6 → ℝ,
      (∀ I, ‖σ I‖ ≤ 1) ∧ (∀ I, ‖τ I‖ ≤ T) ∧
      (∀ u ∈ rows, P u (σ (e u).1 0) (C * τ (e u).1 0)) := by
  obtain ⟨p, hp, hexact⟩ := ExpansionRecipe.assemble_fixed_sector_parameters
    e sector rows hsector ((0, 0) : ℝ × ℝ)
    (fun q => |q.1| ≤ 1 ∧ |q.2| ≤ C * T)
    (by simp only [abs_zero]; exact ⟨by norm_num, mul_nonneg hC.le hT⟩)
    (fun u q => P u q.1 q.2) (by
      intro u hu
      obtain ⟨β, ν, hβ, hν, hP⟩ := hlocal u hu
      exact ⟨(β, ν), ⟨hβ, hν⟩, hP⟩)
  let σ : Ideal → Fin 6 → ℝ := fun I _ => (p I).1
  let τ : Ideal → Fin 6 → ℝ := fun I _ => (p I).2 / C
  refine ⟨σ, τ, ?_, ?_, ?_⟩
  · intro I
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro j
    simpa only [σ, Real.norm_eq_abs] using (hp I).1
  · intro I
    apply (pi_norm_le_iff_of_nonneg hT).mpr
    intro j
    change ‖(p I).2 / C‖ ≤ T
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hC]
    exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using (hp I).2)
  · intro u hu
    have heq : C * ((p (e u).1).2 / C) = (p (e u).1).2 := by
      field_simp [hC.ne']
    simpa only [σ, τ, heq] using hexact u hu

end Expansion.Dyadic

#print axioms Expansion.Dyadic.exists_terminal_label_support
#print axioms Expansion.Dyadic.terminalLabelCount_subpower
#print axioms Expansion.Dyadic.terminalLabel_lengths
#print axioms Expansion.Dyadic.terminalLabel_plainLength_range
#print axioms Expansion.Dyadic.terminalLabel_plainLength_range_two
#print axioms Expansion.Dyadic.assemble_terminal_raw_parameters_on_sector
#print axioms Expansion.Dyadic.assemble_terminal_parameters_on_sector
