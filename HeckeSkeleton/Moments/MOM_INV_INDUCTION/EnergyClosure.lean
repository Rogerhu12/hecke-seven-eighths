import HeckeSkeleton.Moments.MOM_INV_INDUCTION.Interface
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.InductionClosure

/-!
# Finite closure of the canonical energy recursion

The single-step hypothesis is the explicit weighted energy reduction in
`Interface.lean`.  This file proves its consumption, including the exact
prefactor, a uniform constant, and a finite height exponent.  A terminal
estimate is a separate hypothesis; `Terminal.lean` proves its numerical
ledger from the reflected terminal exponents.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open scoped BigOperators

/-- Consume the child estimates in one literal weighted reduction.  The
child loss occurs once, and the normalized frozen-triple measure is used
once.  The child label measure stays inside `E y`. -/
theorem step_energy_bound {α : Type*} {E F M Q z : α → ℝ}
    {Z eta tau pi S d B e : ℝ} {x : α} {s : StepData α}
    (hZ : 1 ≤ Z) (heta : 0 ≤ eta) (htau : 0 ≤ tau) (hpi : 0 ≤ pi)
    (hS : 0 ≤ S) (hB : 1 ≤ B) (he : 0 ≤ e) (hMF : M x ≤ F x)
    (g : StepGeometry F M Q z eta d x s)
    (hstep : StepEnergy E F M Z eta tau pi S x s)
    (hchild : ∀ y ∈ s.children, E y ≤ B * Z ^ (F y + e)) :
    E x ≤ 3 * S * B * Z ^ (F x + stepLoss eta tau pi + e) := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hBpos : 0 ≤ B := zero_le_one.trans hB
  have hL : 0 ≤ stepLoss eta tau pi := stepLoss_nonneg heta htau hpi
  let T := B * Z ^ (F x + stepLoss eta tau pi + e)
  have hT : 0 ≤ T := mul_nonneg hBpos (Real.rpow_nonneg hZpos.le _)
  have hraise (a : ℝ) (ha : a ≤ F x + stepLoss eta tau pi + e) : Z ^ a ≤ T := by
    calc
      _ ≤ Z ^ (F x + stepLoss eta tau pi + e) :=
        Real.rpow_le_rpow_of_exponent_le hZ ha
      _ ≤ B * Z ^ (F x + stepLoss eta tau pi + e) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hZpos.le _)
  have hprincipal₀ : Z ^ M x ≤ T := hraise _ (by linarith)
  have hprincipal₁ : Z ^ (F x + 26 * eta + tau + pi) ≤ T := by
    apply hraise
    dsimp only [stepLoss]
    linarith
  have hterm (y : α) (hy : y ∈ s.children) :
      Z ^ (28 * eta + tau + pi) *
        (Z ^ (s.firstPrefactor y + s.secondPrefactor y + s.tripleCount y + F y) * E y)
        ≤ T := by
    calc
      _ ≤ Z ^ (28 * eta + tau + pi) *
          (Z ^ (s.firstPrefactor y + s.secondPrefactor y + s.tripleCount y + F y) *
            (B * Z ^ (F y + e))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hchild y hy) (Real.rpow_nonneg hZpos.le _))
          (Real.rpow_nonneg hZpos.le _)
      _ = B * Z ^ (28 * eta + tau + pi +
          (s.firstPrefactor y + s.secondPrefactor y + s.tripleCount y + F y) +
          (F y + e)) := by
        simp only [Real.rpow_add hZpos]
        ring
      _ ≤ T := by
        apply mul_le_mul_of_nonneg_left _ hBpos
        exact Real.rpow_le_rpow_of_exponent_le hZ (normalized_prefactor_le g y hy tau pi e)
  have hsum : Z ^ (28 * eta + tau + pi) *
      (∑ y ∈ s.children, s.weight y *
        (Z ^ (s.firstPrefactor y + s.secondPrefactor y + s.tripleCount y + F y) * E y)) ≤ T := by
    calc
      _ = ∑ y ∈ s.children, s.weight y *
          (Z ^ (28 * eta + tau + pi) *
            (Z ^ (s.firstPrefactor y + s.secondPrefactor y + s.tripleCount y + F y) * E y)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ ≤ ∑ y ∈ s.children, s.weight y * T :=
        Finset.sum_le_sum (fun y hy => mul_le_mul_of_nonneg_left (hterm y hy)
          (s.weight_nonneg y hy))
      _ = (∑ y ∈ s.children, s.weight y) * T := (Finset.sum_mul ..).symm
      _ ≤ 1 * T := mul_le_mul_of_nonneg_right s.weight_mass hT
      _ = T := one_mul _
  apply hstep.trans
  calc
    _ ≤ S * (3 * T) := mul_le_mul_of_nonneg_left (by linarith) hS
    _ = _ := by dsimp only [T]; ring

/-- The explicit constant and loss at a node with `n` remaining steps. -/
def energyEnvelope (n : ℕ) (S Z F L : ℝ) : ℝ :=
  (3 * S) ^ n * Z ^ (F + (n : ℝ) * L)

theorem terminal_le_envelope {S Z F L : ℝ}
    (hS : 1 ≤ S) (hZ : 1 ≤ Z) (hL : 0 ≤ L) (n : ℕ) :
    S * Z ^ F ≤ energyEnvelope (n + 1) S Z F L := by
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  have h3S : 1 ≤ 3 * S := by linarith
  have hpow : 1 ≤ (3 * S) ^ n := one_le_pow₀ h3S
  have hC : S ≤ (3 * S) ^ (n + 1) := by
    rw [pow_succ]
    nlinarith
  have hF : F ≤ F + ((n + 1 : ℕ) : ℝ) * L :=
    le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hL)
  exact mul_le_mul hC (Real.rpow_le_rpow_of_exponent_le hZ hF)
    (Real.rpow_nonneg (zero_le_one.trans hZ) _) (by positivity)

theorem step_le_envelope {α : Type*} {E F M Q z : α → ℝ}
    {Z eta tau pi S d : ℝ} {x : α} {s : StepData α}
    (hZ : 1 ≤ Z) (heta : 0 ≤ eta) (htau : 0 ≤ tau) (hpi : 0 ≤ pi)
    (hS : 1 ≤ S) (hMF : M x ≤ F x)
    (g : StepGeometry F M Q z eta d x s)
    (hstep : StepEnergy E F M Z eta tau pi S x s)
    (n : ℕ) (hchild : ∀ y ∈ s.children,
      E y ≤ energyEnvelope n S Z (F y) (stepLoss eta tau pi)) :
    E x ≤ energyEnvelope (n + 1) S Z (F x) (stepLoss eta tau pi) := by
  have h3S : 1 ≤ 3 * S := by linarith
  have hL := stepLoss_nonneg heta htau hpi
  have hb := step_energy_bound hZ heta htau hpi (zero_le_one.trans hS)
    (one_le_pow₀ h3S : 1 ≤ (3 * S) ^ n)
    (mul_nonneg (Nat.cast_nonneg n) hL) hMF g hstep hchild
  have hex : F x + stepLoss eta tau pi + (n : ℝ) * stepLoss eta tau pi =
      F x + ((n + 1 : ℕ) : ℝ) * stepLoss eta tau pi := by
    push_cast
    ring
  convert hb using 1 <;> dsimp only [energyEnvelope]
  rw [hex, pow_succ]
  ring

/-- Finite backward induction on the actual energy, with a uniform
constant.  Geometry and energy reduction are distinct hypotheses, and
the target estimate is not an assumption at any positive depth. -/
theorem canonical_energy_bound {α : Type*}
    (E F M Q z : α → ℝ) (s : α → StepData α)
    (Terminal : α → Prop) (Good : ℕ → α → Prop)
    (D : ℕ) (Z eta tau pi S d Mmax : ℝ)
    (hZ : 1 ≤ Z) (heta : 0 ≤ eta) (htau : 0 ≤ tau) (hpi : 0 ≤ pi)
    (hS : 1 ≤ S) (hdepth : Mmax < (D : ℝ) * d)
    (hnonneg : ∀ h x, Good h x → 0 ≤ M x)
    (hMF : ∀ h x, Good h x → M x ≤ F x)
    (hgeometry : ∀ h x, h < D → Good h x → ¬ Terminal x →
      StepGeometry F M Q z eta d x (s x))
    (hgood : ∀ h x y, h < D → Good h x → ¬ Terminal x →
      y ∈ (s x).children → Good (h + 1) y)
    (hterminal : ∀ h x, h < D → Good h x → Terminal x → E x ≤ S * Z ^ F x)
    (hstep : ∀ h x, h < D → Good h x → ¬ Terminal x →
      StepEnergy E F M Z eta tau pi S x (s x)) :
    ∀ x, Good 0 x → M x ≤ Mmax →
      E x ≤ energyEnvelope D S Z (F x) (stepLoss eta tau pi) := by
  apply finite_descent_with_terminal M (fun x y => y ∈ (s x).children) Terminal Good
    (fun h x => E x ≤ energyEnvelope (D - h) S Z (F x) (stepLoss eta tau pi))
    D d Mmax hdepth hnonneg
  · intro h x y hh hx ht hy
    exact ⟨hgood h x y hh hx ht hy, (hgeometry h x hh hx ht).row_decrease y hy⟩
  · intro h x hh hx ht
    have hn : D - h = (D - (h + 1)) + 1 := by omega
    rw [hn]
    exact (hterminal h x hh hx ht).trans
      (terminal_le_envelope hS hZ (stepLoss_nonneg heta htau hpi) _)
  · intro h x hh hx ht ih
    have hn : D - h = (D - (h + 1)) + 1 := by omega
    rw [hn]
    exact step_le_envelope hZ heta htau hpi hS (hMF h x hx)
      (hgeometry h x hh hx ht) (hstep h x hh hx ht) (D - (h + 1)) ih

/-- Finite propagation of a uniform polynomial height factor.  All
constants precede the root node.  Only the loss budget depends on ε. -/
theorem canonical_energy_polynomial_height {α : Type*}
    (E F M Q z : α → ℝ) (s : α → StepData α)
    (Terminal : α → Prop) (Good : ℕ → α → Prop)
    (D : ℕ) (Z eta tau pi C H A d Mmax eps : ℝ)
    (hZ : 1 ≤ Z) (heta : 0 ≤ eta) (htau : 0 ≤ tau) (hpi : 0 ≤ pi)
    (hC : 1 ≤ C) (hH : 1 ≤ H) (hA : 0 ≤ A)
    (hdepth : Mmax < (D : ℝ) * d)
    (hloss : (D : ℝ) * stepLoss eta tau pi ≤ eps)
    (hnonneg : ∀ h x, Good h x → 0 ≤ M x)
    (hMF : ∀ h x, Good h x → M x ≤ F x)
    (hgeometry : ∀ h x, h < D → Good h x → ¬ Terminal x →
      StepGeometry F M Q z eta d x (s x))
    (hgood : ∀ h x y, h < D → Good h x → ¬ Terminal x →
      y ∈ (s x).children → Good (h + 1) y)
    (hterminal : ∀ h x, h < D → Good h x → Terminal x → E x ≤ C * H ^ A * Z ^ F x)
    (hstep : ∀ h x, h < D → Good h x → ¬ Terminal x →
      StepEnergy E F M Z eta tau pi (C * H ^ A) x (s x)) :
    ∀ x, Good 0 x → M x ≤ Mmax →
      E x ≤ (3 * C) ^ D * Z ^ (F x + eps) * H ^ (A * (D : ℝ)) := by
  have hS : 1 ≤ C * H ^ A := one_le_mul_of_one_le_of_one_le hC (Real.one_le_rpow hH hA)
  intro x hx hM
  have hb := canonical_energy_bound E F M Q z s Terminal Good D Z eta tau pi (C * H ^ A)
    d Mmax hZ heta htau hpi hS hdepth hnonneg hMF hgeometry hgood hterminal hstep x hx hM
  apply hb.trans
  unfold energyEnvelope
  have hpow : (3 * (C * H ^ A)) ^ D = (3 * C) ^ D * H ^ (A * (D : ℝ)) := by
    rw [Real.rpow_mul (zero_le_one.trans hH), Real.rpow_natCast]
    rw [← mul_pow]
    congr 1
    ring
  rw [hpow]
  calc
    _ ≤ ((3 * C) ^ D * H ^ (A * (D : ℝ))) * Z ^ (F x + eps) := by
      apply mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
      positivity
    _ = _ := by ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION
