import HeckeSkeleton.LowEnergy.IdealRankin
import HeckeSkeleton.LowEnergy.FiniteFiberEnergy
import HeckeSkeleton.LowEnergy.DyadicTail

/-!
# Outer aggregation over actual powerful ideal parts

The powerful half-norm mass is a theorem, obtained from the actual ideal
square--cube injection and Dedekind zeta convergence. The row fibres and
residual shells are disjoint subsets of the original row set. The only
analytic premise is the preceding per-fibre block estimate; it is neither
a powerful counting assumption nor the target completed marked energy.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.PowerfulRowAssembly

open NumberField
open HeckeSkeleton.LowEnergy.IdealRows HeckeSkeleton.LowEnergy.IdealRankin
open scoped Classical BigOperators nonZeroDivisors NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- No multiplicity factor is introduced when several physical rows share
one powerful part: the exact image-fibre sum retains those rows inside it. -/
theorem powerful_fibre_aggregation (eps rho : ℝ) (heps : 0 < eps) (hrho : 0 ≤ rho) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Row : Type*} (R : Finset Row)
      (I : Row → (Ideal (𝓞 K))⁰) (E : Row → ℝ) (X B : ℝ),
      1 ≤ X → 0 ≤ B → (∀ r ∈ R, idealNorm K (I r) ≤ X) →
      (∀ A ∈ R.image (fun r => powerfulPart (I r)),
        (∑ r ∈ R.filter (fun r => powerfulPart (I r) = A), E r) ≤
          B * idealNorm K A ^ (-(1 / 2 : ℝ) + rho)) →
      (∑ r ∈ R, E r) ≤ C * B * X ^ (eps + rho) := by
  obtain ⟨C, hC, hbound⟩ := powerful_weighted_half_mass K eps rho heps hrho
  refine ⟨C, hC, ?_⟩
  intro Row R I E X B hX hB hI hlocal
  let s : Finset (Ideal (𝓞 K))⁰ := R.image (fun r => powerfulPart (I r))
  have hs : ∀ A ∈ s, Powerful A ∧ idealNorm K A ≤ X := by
    intro A hA
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hA
    exact ⟨powerfulPart_powerful (I r), (idealNorm_powerfulPart_le K (I r)).trans (hI r hr)⟩
  calc
    _ ≤ ∑ A ∈ s, B * idealNorm K A ^ (-(1 / 2 : ℝ) + rho) :=
      FiniteFiberEnergy.sum_le_fibre_majorants R (fun r => powerfulPart (I r)) E
        (fun A => B * idealNorm K A ^ (-(1 / 2 : ℝ) + rho)) hlocal
    _ = B * ∑ A ∈ s, idealNorm K A ^ (-(1 / 2 : ℝ) + rho) :=
      (Finset.mul_sum ..).symm
    _ ≤ B * (C * X ^ (eps + rho)) := mul_le_mul_of_nonneg_left (hbound s X hX hs) hB
    _ = _ := by ring

/-- Both row partitions are exact. Only residual shells contribute the
finite factor `N`; powerful parts are paid by their proved half-norm mass. -/
theorem powerful_shell_aggregation (eps rho : ℝ) (heps : 0 < eps) (hrho : 0 ≤ rho) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Row : Type*} (R : Finset Row)
      (I : Row → (Ideal (𝓞 K))⁰) (shell : Row → ℕ) (E : Row → ℝ)
      (N : ℕ) (X B : ℝ),
      1 ≤ X → 0 ≤ B → (∀ r ∈ R, idealNorm K (I r) ≤ X) →
      (∀ r ∈ R, shell r < N) →
      (∀ A ∈ R.image (fun r => powerfulPart (I r)), ∀ j ∈ Finset.range N,
        (∑ r ∈ R.filter (fun r => powerfulPart (I r) = A ∧ shell r = j), E r) ≤
          B * idealNorm K A ^ (-(1 / 2 : ℝ) + rho)) →
      (∑ r ∈ R, E r) ≤ C * B * N * X ^ (eps + rho) := by
  obtain ⟨C, hC, hbound⟩ := powerful_fibre_aggregation K eps rho heps hrho
  refine ⟨C, hC, ?_⟩
  intro Row R I shell E N X B hX hB hI hshell hlocal
  have hf := FiniteFiberEnergy.fibre_bound_from_shells R
    (fun r => powerfulPart (I r)) shell E N hshell
    (fun A => B * idealNorm K A ^ (-(1 / 2 : ℝ) + rho)) hlocal
  have hb : ∀ A ∈ R.image (fun r => powerfulPart (I r)),
      (∑ r ∈ R.filter (fun r => powerfulPart (I r) = A), E r) ≤
        ((N : ℝ) * B) * idealNorm K A ^ (-(1 / 2 : ℝ) + rho) := by
    intro A hA
    simpa only [mul_assoc] using hf A hA
  have h := hbound R I E X ((N : ℝ) * B) hX (mul_nonneg (Nat.cast_nonneg _) hB) hI hb
  convert h using 1 <;> ring

/-- An explicit global allocation pays for state powers, the powerful
half-norm mass and the logarithmic number of residual row shells together.
The constant is chosen before the row set, its amplitude, and Z. -/
theorem powerful_shell_aggregation_at_scale (L eps C0 : ℝ)
    (hL : 0 ≤ L) (heps : 0 < eps) (hC0 : 0 < C0) :
    let delta := eps / (4 * (L + 1))
    ∃ C : ℝ, 0 < C ∧ ∀ {Row : Type*} (R : Finset Row)
      (I : Row → (Ideal (𝓞 K))⁰) (shell : Row → ℕ) (E : Row → ℝ)
      (N : ℕ) (Z B : ℝ),
      1 ≤ Z → 0 ≤ B → (∀ r ∈ R, idealNorm K (I r) ≤ Z ^ L) →
      (∀ r ∈ R, shell r < N) →
      ((N : ℝ) ≤ C0 * (1 + Real.log Z) ^ 2) →
      (∀ A ∈ R.image (fun r => powerfulPart (I r)), ∀ j ∈ Finset.range N,
        (∑ r ∈ R.filter (fun r => powerfulPart (I r) = A ∧ shell r = j), E r) ≤
          B * idealNorm K A ^ (-(1 / 2 : ℝ) + delta)) →
      (∑ r ∈ R, E r) ≤ C * B * Z ^ eps := by
  dsimp only
  let delta := eps / (4 * (L + 1))
  have hdelta : 0 < delta := div_pos heps (by positivity)
  obtain ⟨C1, hC1, hbound⟩ := powerful_shell_aggregation K delta delta hdelta hdelta.le
  let C := C1 * C0 * (1 + 2 / (eps / 2)) ^ 2
  have hc : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hc, ?_⟩
  intro Row R I shell E N Z B hZ hB hI hshell hN hlocal
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hpow : L * (delta + delta) ≤ eps / 2 := by
    have hd : delta * (4 * (L + 1)) = eps := by
      dsimp [delta]
      field_simp
    nlinarith
  have hx : (Z ^ L) ^ (delta + delta) ≤ Z ^ (eps / 2) := by
    rw [← Real.rpow_mul hZp.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ hpow
  have hn : (N : ℝ) ≤ C0 * ((1 + 2 / (eps / 2)) ^ 2 * Z ^ (eps / 2)) :=
    hN.trans (mul_le_mul_of_nonneg_left
      (DyadicTail.log_square_small_power hZ (show 0 < eps / 2 by linarith)) hC0.le)
  have h := hbound R I shell E N (Z ^ L) B (Real.one_le_rpow hZ hL) hB hI hshell hlocal
  calc
    _ ≤ C1 * B * N * (Z ^ L) ^ (delta + delta) := h
    _ ≤ C1 * B * (C0 * ((1 + 2 / (eps / 2)) ^ 2 * Z ^ (eps / 2))) * Z ^ (eps / 2) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hn (mul_nonneg hC1.le hB)
      · exact hx
      · exact Real.rpow_nonneg (Real.rpow_nonneg hZp.le _) _
      · positivity
    _ = C * B * Z ^ eps := by
      dsimp [C]
      have hp : Z ^ (eps / 2) * Z ^ (eps / 2) = Z ^ eps := by
        rw [← Real.rpow_add hZp]
        congr 1
        ring
      calc
        _ = (C1 * C0 * (1 + 2 / (eps / 2)) ^ 2) * B *
            (Z ^ (eps / 2) * Z ^ (eps / 2)) := by ring
        _ = _ := by rw [hp]

#print axioms powerful_fibre_aggregation
#print axioms powerful_shell_aggregation
#print axioms powerful_shell_aggregation_at_scale

end HeckeSkeleton.LowEnergy.PowerfulRowAssembly
