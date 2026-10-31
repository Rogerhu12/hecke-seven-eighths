import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CanonicalEnergy
import HeckePort.Moments.Inversion.TerminalWidths
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# From the general reflected-energy exponent to canonical terminals

The analytic input in this file is the block estimate of paper Lemma 4.8,
with exponent `E_ref`, before either canonical margin has been used.
The two conductor inequalities and the short cube-completion scale then
give the three terminal powers of Proposition 4.10. In particular, those
three powers are conclusions here, rather than assumptions on a terminal.

The final transport theorem preserves an exact finite decomposition of
the literal canonical column. Its coefficient mass is charged twice by
weighted Cauchy, before the separate squarefree-label normalization.
The block estimate may be supplied by the general LOW-REFLECTED-ENERGY
provider; it is not inferred from the narrower physical Gaussian bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open HeckePort.Moments
open scoped Classical BigOperators

/-- The geometry in Lemma 4.8 for one retained completed block.
`completion` is the short cube length removed before applying reflection;
`cube` is the dual cube length and remains a separate variable.
The optional ramified width is the existing terminal-width convention. -/
structure TerminalBlockGeometry (N V M Q z d eta tau : ℝ) where
  powerful : ℝ
  residual : ℝ
  small : ℝ
  cubeCharge : ℝ
  active : ℝ
  dual : ℝ
  cube : ℝ
  ramified : ℝ
  threshold : ℝ
  completion : ℝ
  powerful_nonneg : 0 ≤ powerful
  small_nonneg : 0 ≤ small
  cubeCharge_nonneg : 0 ≤ cubeCharge
  active_nonneg : 0 ≤ active
  active_le : active ≤ z
  dual_nonneg : 0 ≤ dual
  cube_nonneg : 0 ≤ cube
  ramified_lower : -eta ≤ ramified
  completion_nonneg : 0 ≤ completion
  completion_le : completion ≤ d + eta
  retained : dual + 3 * cube + ramified ≤ threshold + tau
  row_conductor : residual ≤ M - powerful + eta
  dual_conductor : threshold - small - cubeCharge ≤
    2 * M - powerful + Q + V - (N - 3 * completion) + 2 * active + eta

/-- The exact reflected-energy exponent, before canonical invariants. -/
def TerminalBlockGeometry.exponent {N V M Q z d eta tau : ℝ}
    (g : TerminalBlockGeometry N V M Q z d eta tau) : ℝ :=
  reflectedExponent g.powerful g.residual g.small g.cubeCharge g.active
    g.dual g.cube g.ramified g.threshold

/-- The three powers in the canonical terminal ledger, with the
subsidiary reflected loss displayed once. -/
def terminalLedger (Z F M c d eta tau pi : ℝ) : ℝ :=
  Z ^ (F - c + 5 * eta / 3 + pi) +
    Z ^ (F - 2 * c + 5 * d + 17 * eta / 3 + tau + pi) +
    Z ^ (F - M / 4 - 3 * c / 4 + 5 * d / 2 +
      19 * eta / 6 + tau / 2 + pi)

theorem terminalLedger_nonneg {Z F M c d eta tau pi : ℝ} (hZ : 0 ≤ Z) :
    0 ≤ terminalLedger Z F M c d eta tau pi := by
  unfold terminalLedger
  positivity

/-- The conductor bound and short completion imply the precise
three-way terminal classification. -/
theorem TerminalBlockGeometry.terminal_cases {N V M Q z d eta tau c : ℝ}
    (g : TerminalBlockGeometry N V M Q z d eta tau)
    (hinv : CanonicalMargins (N + V) M Q z c)
    (hQ : 0 ≤ Q) (hV : V ≤ d) :
    g.exponent ≤ N + V - c + 5 * eta / 3 ∨
    g.exponent ≤ N + V - 2 * c + 5 * d + 17 * eta / 3 + tau ∨
    g.exponent ≤ N + V - M / 4 - 3 * c / 4 + 5 * d / 2 +
      19 * eta / 6 + tau / 2 := by
  have hwidth := terminal_width_from_invariant
    (Nstar := N - 3 * g.completion) hinv rfl rfl hV
    g.completion_le g.dual_conductor
  obtain ⟨hrow, hfull, hpartial⟩ := reflected_terminal_cases
    hinv hQ g.powerful_nonneg g.small_nonneg g.cubeCharge_nonneg
    g.active_nonneg g.active_le g.dual_nonneg g.cube_nonneg
    g.ramified_lower g.retained g.row_conductor hwidth
  rcases le_total (g.dual + g.cube) g.residual with h | h
  · exact Or.inl (hrow h)
  · by_cases hu : hybridSaving g.dual g.active = g.active
    · exact Or.inr (Or.inl (hfull h hu))
    · exact Or.inr (Or.inr (hpartial h hu))

/-- Consume the general reflected exponent at the original terminal
node. Neither the final canonical exponent nor any terminal power is an
analytic premise. -/
theorem TerminalBlockGeometry.power_le_ledger {N V M Q z d eta tau c Z pi : ℝ}
    (g : TerminalBlockGeometry N V M Q z d eta tau)
    (hZ : 1 ≤ Z) (hinv : CanonicalMargins (N + V) M Q z c)
    (hQ : 0 ≤ Q) (hV : V ≤ d) :
    Z ^ (g.exponent + pi) ≤ terminalLedger Z (N + V) M c d eta tau pi := by
  have hz : 0 ≤ Z := zero_le_one.trans hZ
  have hp₁ := Real.rpow_nonneg hz (N + V - c + 5 * eta / 3 + pi)
  have hp₂ := Real.rpow_nonneg hz
    (N + V - 2 * c + 5 * d + 17 * eta / 3 + tau + pi)
  have hp₃ := Real.rpow_nonneg hz
    (N + V - M / 4 - 3 * c / 4 + 5 * d / 2 + 19 * eta / 6 + tau / 2 + pi)
  unfold terminalLedger
  rcases g.terminal_cases hinv hQ hV with h | h | h
  · have hb := Real.rpow_le_rpow_of_exponent_le hZ (add_le_add_right h pi)
    linarith
  · have hb := Real.rpow_le_rpow_of_exponent_le hZ (add_le_add_right h pi)
    linarith
  · have hb := Real.rpow_le_rpow_of_exponent_le hZ (add_le_add_right h pi)
    linarith

/-- Weighted finite Cauchy in the actual row Hilbert space. The
coefficient is independent of the row, and its mass is not hidden in a
new energy field. -/
theorem finite_reconstruction_energy {ι κ : Type*}
    (blocks : Finset ι) (rows : Finset κ)
    (coefficient : ι → ℂ) (piece : ι → κ → ℂ) (source : κ → ℂ)
    {B W : ℝ} (hB : 0 ≤ B) (hW : 0 ≤ W)
    (hsource : ∀ k ∈ rows, source k = ∑ i ∈ blocks, coefficient i * piece i k)
    (hmass : ∑ i ∈ blocks, ‖coefficient i‖ ≤ W)
    (henergy : ∀ i ∈ blocks, ∑ k ∈ rows, ‖piece i k‖ ^ 2 ≤ B) :
    ∑ k ∈ rows, ‖source k‖ ^ 2 ≤ W ^ 2 * B := by
  let mass := ∑ i ∈ blocks, ‖coefficient i‖
  have hmass0 : 0 ≤ mass := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hpoint (k : κ) (hk : k ∈ rows) :
      ‖source k‖ ^ 2 ≤ mass *
        ∑ i ∈ blocks, ‖coefficient i‖ * ‖piece i k‖ ^ 2 := by
    rw [hsource k hk]
    have hnorm : ‖∑ i ∈ blocks, coefficient i * piece i k‖ ≤
        ∑ i ∈ blocks, ‖coefficient i‖ * ‖piece i k‖ := by
      simpa only [norm_mul] using norm_sum_le blocks (fun i => coefficient i * piece i k)
    have hsq : ‖∑ i ∈ blocks, coefficient i * piece i k‖ ^ 2 ≤
        (∑ i ∈ blocks, ‖coefficient i‖ * ‖piece i k‖) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    apply hsq.trans
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul blocks
      (fun i _ => norm_nonneg (coefficient i))
      (fun i _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
      (fun i _ => le_of_eq (by ring))
  calc
    _ ≤ ∑ k ∈ rows, mass * ∑ i ∈ blocks, ‖coefficient i‖ * ‖piece i k‖ ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = mass * ∑ i ∈ blocks, ‖coefficient i‖ *
        ∑ k ∈ rows, ‖piece i k‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ mass * ∑ i ∈ blocks, ‖coefficient i‖ * B := by
      apply mul_le_mul_of_nonneg_left _ hmass0
      exact Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left (henergy i hi) (norm_nonneg _))
    _ = mass ^ 2 * B := by rw [← Finset.sum_mul]; dsimp only [mass]; ring
    _ ≤ W ^ 2 * B :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hmass0 hmass 2) hB

/-- The short cube completion has a row-dependent frozen character.
Only its independent positive majorant is extracted; its zeros remain
inside the exact reconstruction until the norm inequality is applied. -/
theorem finite_reconstruction_energy_bounded {ι κ : Type*}
    (blocks : Finset ι) (rows : Finset κ)
    (coefficient : ι → κ → ℂ) (weight : ι → ℝ)
    (piece : ι → κ → ℂ) (source : κ → ℂ)
    {B W : ℝ} (hB : 0 ≤ B)
    (hweight : ∀ i ∈ blocks, 0 ≤ weight i)
    (hcoefficient : ∀ i ∈ blocks, ∀ k ∈ rows, ‖coefficient i k‖ ≤ weight i)
    (hsource : ∀ k ∈ rows, source k = ∑ i ∈ blocks, coefficient i k * piece i k)
    (hmass : ∑ i ∈ blocks, weight i ≤ W)
    (henergy : ∀ i ∈ blocks, ∑ k ∈ rows, ‖piece i k‖ ^ 2 ≤ B) :
    ∑ k ∈ rows, ‖source k‖ ^ 2 ≤ W ^ 2 * B := by
  let mass := ∑ i ∈ blocks, weight i
  have hmass0 : 0 ≤ mass := Finset.sum_nonneg hweight
  have hpoint (k : κ) (hk : k ∈ rows) :
      ‖source k‖ ^ 2 ≤ mass * ∑ i ∈ blocks, weight i * ‖piece i k‖ ^ 2 := by
    rw [hsource k hk]
    have hnorm : ‖∑ i ∈ blocks, coefficient i k * piece i k‖ ≤
        ∑ i ∈ blocks, weight i * ‖piece i k‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hcoefficient i hi k hk) (norm_nonneg _)
    apply (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul blocks hweight
      (fun i hi => mul_nonneg (hweight i hi) (sq_nonneg _))
      (fun i _ => le_of_eq (by ring))
  calc
    _ ≤ ∑ k ∈ rows, mass * ∑ i ∈ blocks, weight i * ‖piece i k‖ ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = mass * ∑ i ∈ blocks, weight i * ∑ k ∈ rows, ‖piece i k‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ mass * ∑ i ∈ blocks, weight i * B := by
      apply mul_le_mul_of_nonneg_left _ hmass0
      exact Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left (henergy i hi) (hweight i hi))
    _ = mass ^ 2 * B := by rw [← Finset.sum_mul]; dsimp only [mass]; ring
    _ ≤ W ^ 2 * B :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hmass0 hmass 2) hB

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

/-- Exact finite completed-block realization of one label's canonical
column. The displayed block estimates are the general reflected energy
input; conductor geometry turns them into the required terminal ledger.
The original squarefree-label measure is untouched by this theorem. -/
theorem terminal_label_from_reflected_blocks {ι : Type*}
    (d : CanonicalDatum K) (f : NonzeroIdeal K)
    (blocks : Finset ι) (coefficient : ι → ℂ)
    (piece : ι → NonzeroIdeal K → ℂ)
    {Z c step eta tau pi C W : ℝ}
    (geometry : ι → TerminalBlockGeometry d.columnLength d.labelLength
      d.rowLength d.punctureLength d.markCap step eta tau)
    (hZ : 1 ≤ Z) (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hinv : CanonicalMargins d.totalLength d.rowLength d.punctureLength d.markCap c)
    (hV : d.labelLength ≤ step)
    (hsource : ∀ k ∈ d.rows,
      d.columnValue Z k f = ∑ i ∈ blocks, coefficient i * piece i k)
    (hmass : ∑ i ∈ blocks, ‖coefficient i‖ ≤ W)
    (hreflection : ∀ i ∈ blocks, ∑ k ∈ d.rows, ‖piece i k‖ ^ 2 ≤
      C * Z ^ ((geometry i).exponent + pi)) :
    d.labelEnergy Z f ≤ (W ^ 2 * C) *
      terminalLedger Z d.totalLength d.rowLength c step eta tau pi := by
  have hblocks : ∀ i ∈ blocks, ∑ k ∈ d.rows, ‖piece i k‖ ^ 2 ≤
      C * terminalLedger Z d.totalLength d.rowLength c step eta tau pi := by
    intro i hi
    exact (hreflection i hi).trans (mul_le_mul_of_nonneg_left
      ((geometry i).power_le_ledger hZ hinv d.punctureLength_nonneg hV) hC)
  have hb := finite_reconstruction_energy blocks d.rows coefficient piece
    (fun k => d.columnValue Z k f)
    (mul_nonneg hC (terminalLedger_nonneg (zero_le_one.trans hZ)))
    hW hsource hmass hblocks
  exact hb.trans_eq (by ring)

/-- The general block exponent yields a fixed terminal saving after
the prescribed loss allocation. This is the form independent of the
three-way presentation of the terminal ledger. -/
theorem TerminalBlockGeometry.exponent_saving {N V M Q z step eta tau c cstar pi : ℝ}
    (g : TerminalBlockGeometry N V M Q z step eta tau)
    (hinv : CanonicalMargins (N + V) M Q z c)
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hV : V ≤ step)
    (hcstar : 0 < cstar) (hmargin : cstar / 2 ≤ c)
    (hstep : step ≤ cstar / 200) (heta : eta ≤ cstar / 1000)
    (htau : tau ≤ cstar / 1000) (hpi : pi ≤ cstar / 1000) :
    g.exponent + pi ≤ N + V - cstar / 4 := by
  obtain ⟨h₁, h₂, h₃⟩ := terminal_ledger_saving
    (F := N + V) hcstar hM hmargin hstep heta htau hpi
  rcases g.terminal_cases hinv hQ hV with h | h | h <;> linarith

end HeckeSkeleton.Moments.MOM_INV_INDUCTION
