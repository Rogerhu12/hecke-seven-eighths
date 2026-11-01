import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CanonicalClosure
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CanonicalEnergy
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.InitialTransfer
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.InductionCapacity

/-!
# The inverse induction for literal ideal polynomials

The endpoint in this file is the repository's `inverseEnergy` for an
explicit `MomentData`, not an abstract energy supplied as a field of the
source.  Canonical energies are likewise the literal finite sums in
`CanonicalDatum.energy`.

The remaining analytic inputs are stated in full.  They are the
two-transform reduction, the initial masked Poisson reduction, and the
three reflected terminal branches for every squarefree label.  In
particular the existing fixed-Gaussian `CompletedMarkedEnergy` is not
silently promoted to the stronger terminal input below.  This is the
corrected relative theorem; the original skeleton declaration and its
admitted source data are assessed in `STATEMENT_AUDIT.md`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]

/-- The three explicit reflected terminal powers, at the remaining
margin after `h` steps. -/
def terminalPowers (d : CanonicalDatum K) {Mmax c eps : ℝ}
    (b : DescentBudget Mmax c eps) (Z : ℝ) (h : ℕ) : ℝ :=
  let margin := c - 7 * (h : ℝ) * b.eta
  Z ^ (d.totalLength - margin + 5 * b.eta / 3 + b.pi) +
    Z ^ (d.totalLength - 2 * margin + 5 * b.step + 17 * b.eta / 3 + b.tau + b.pi) +
    Z ^ (d.totalLength - d.rowLength / 4 - 3 * margin / 4 +
      5 * b.step / 2 + 19 * b.eta / 6 + b.tau / 2 + b.pi)

/-- The precise relative inputs for Proposition 4.10.  Arithmetic
admissibility records the coefficient/mask class and its scale/profile
conditions.  It contains no assumed final energy bound.  The two analytic
fields concern a short-label terminal and a genuine nonterminal step,
respectively; no endpoint bound is available on nonterminal nodes. -/
structure CanonicalInputs {α : Type*} (node : α → CanonicalDatum K)
    {Mmax c eps : ℝ} (b : DescentBudget Mmax c eps) (Z C L H A : ℝ) where
  admissible : α → Prop
  step : α → StepData α
  terminal : α → Prop
  terminalCubeLength : α → ℝ
  terminal_short_label : ∀ x, terminal x → (node x).labelLength < b.step
  terminal_short_cube : ∀ x, terminal x →
    0 ≤ terminalCubeLength x ∧ terminalCubeLength x ≤ b.step + b.eta
  geometry : ∀ h x, h < b.depth → admissible x →
    CanonicalAdmissible (fun y => (node y).rowLength) (fun y => (node y).totalLength)
      (fun y => (node y).punctureLength) (fun y => (node y).markCap) c b.eta h x →
    ¬ terminal x →
    StepGeometry (fun y => (node y).totalLength) (fun y => (node y).rowLength)
      (fun y => (node y).punctureLength) (fun y => (node y).markCap) b.eta b.step x (step x)
  arithmetic : ∀ h x y, h < b.depth → admissible x →
    CanonicalAdmissible (fun y => (node y).rowLength) (fun y => (node y).totalLength)
      (fun y => (node y).punctureLength) (fun y => (node y).markCap) c b.eta h x →
    ¬ terminal x → y ∈ (step x).children → admissible y
  label_mass : ∀ x, admissible x →
    ∑ f ∈ (node x).labels, (node x).labelWeight f ≤
      L * Z ^ ((node x).labelLength + c / 8)
  terminal_labels : ∀ h x, h < b.depth → admissible x →
    CanonicalAdmissible (fun y => (node y).rowLength) (fun y => (node y).totalLength)
      (fun y => (node y).punctureLength) (fun y => (node y).markCap) c b.eta h x →
    terminal x → ∀ f ∈ (node x).labels,
      (node x).labelEnergy Z f ≤ (C * H ^ A) * terminalPowers (node x) b Z h
  reduction : ∀ h x, h < b.depth → admissible x →
    CanonicalAdmissible (fun y => (node y).rowLength) (fun y => (node y).totalLength)
      (fun y => (node y).punctureLength) (fun y => (node y).markCap) c b.eta h x →
    ¬ terminal x →
    StepEnergy (fun y => (node y).energy Z) (fun y => (node y).totalLength)
      (fun y => (node y).rowLength) Z b.eta b.tau b.pi ((3 * C * L) * H ^ A) x (step x)

namespace CanonicalInputs

variable {α : Type*} {node : α → CanonicalDatum K} {Mmax c eps Z C L H A : ℝ}
    {b : DescentBudget Mmax c eps}

/-- Consume all labels in a genuine terminal block and retain a strict
`c / 8` saving after the label measure. -/
theorem terminal_bound (p : CanonicalInputs node b Z C L H A)
    (hZ : 1 ≤ Z) (hC : 1 ≤ C) (hL : 1 ≤ L) (hH : 1 ≤ H) (hc : 0 < c)
    (h : ℕ) (x : α) (hh : h < b.depth) (hx : p.admissible x)
    (hnum : CanonicalAdmissible (fun y => (node y).rowLength)
      (fun y => (node y).totalLength) (fun y => (node y).punctureLength)
      (fun y => (node y).markCap) c b.eta h x)
    (ht : p.terminal x) :
    (node x).energy Z ≤ ((3 * C * L) * H ^ A) * Z ^ (node x).totalLength := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hb := (node x).energy_le_of_terminal_labels hZ
    (mul_nonneg hC0 (Real.rpow_nonneg hH0 A)) (p.label_mass x hx) hc
    (budget_margin b (Nat.le_of_lt hh)) b.step_small b.eta_terminal b.tau_terminal b.pi_terminal
    (p.terminal_labels h x hh hx hnum ht)
  apply hb.trans
  calc
    _ ≤ (3 * (C * H ^ A) * L) * Z ^ (node x).totalLength := by
      apply mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
      positivity
    _ = _ := by ring

/-- The canonical energy bound is proved from the local inputs. -/
theorem energy_bound (p : CanonicalInputs node b Z C L H A)
    (hZ : 1 ≤ Z) (hC : 1 ≤ C) (hL : 1 ≤ L) (hH : 1 ≤ H)
    (hA : 0 ≤ A) (hc : 0 < c) :
    ∀ x, p.admissible x →
      CanonicalMargins (node x).totalLength (node x).rowLength
        (node x).punctureLength (node x).markCap c → (node x).rowLength ≤ Mmax →
      (node x).energy Z ≤ (3 * (3 * C * L)) ^ b.depth *
        Z ^ ((node x).totalLength + eps / 2) * H ^ (A * (b.depth : ℝ)) := by
  have hC0 : 1 ≤ 3 * C * L := by
    have hCL := one_le_mul_of_one_le_of_one_le hC hL
    nlinarith
  exact canonical_energy_from_ledger
    (fun x => (node x).energy Z) (fun x => (node x).totalLength)
    (fun x => (node x).rowLength) (fun x => (node x).punctureLength)
    (fun x => (node x).markCap)
    p.step p.terminal p.admissible b hc Z (3 * C * L) H A hZ hC0 hH hA
    (fun x _ => ⟨(node x).rowLength_nonneg, (node x).punctureLength_nonneg,
      (node x).markCap_nonneg⟩)
    p.geometry p.arithmetic
    (fun h x hh hx hnum ht => p.terminal_bound hZ hC hL hH hc h x hh hx hnum ht)
    p.reduction

end CanonicalInputs

/-- The initial reduction of the actual source energy to canonical
nodes.  The source scalar is supplied explicitly by the endpoint, not a
freely chosen field in this record. -/
structure InitialInputs {α : Type*} (node : α → CanonicalDatum K)
    {Mmax c eps : ℝ} {b : DescentBudget Mmax c eps} {Z C L H A : ℝ}
    (p : CanonicalInputs node b Z C L H A) (source m r z : ℝ) where
  data : InitialData α
  geometry : InitialGeometry (fun y => (node y).totalLength) (fun y => (node y).rowLength)
    (fun y => (node y).punctureLength) (fun y => (node y).markCap) m r z b.eta b.tau data
  admissible : ∀ y ∈ data.nodes, p.admissible y
  row_upper : ∀ y ∈ data.nodes, (node y).rowLength ≤ Mmax
  reduction : InitialEnergy (fun y => (node y).energy Z) (fun y => (node y).totalLength)
    source Z m r z b.eta b.pi ((3 * C * L) * H ^ A) data

/-- Construct the initial ledger from its actual source reduction.  The
row upper bound is derived from the source's marked margin and bounded
range; it need not be supplied as an additional analytic input. -/
def InitialInputs.of_initial_reduction {α : Type*} {node : α → CanonicalDatum K}
    {Mmax c eps Z C L H A source m r z : ℝ} {b : DescentBudget Mmax c eps}
    (p : CanonicalInputs node b Z C L H A) (data : InitialData α)
    (geometry : InitialGeometry (fun y => (node y).totalLength) (fun y => (node y).rowLength)
      (fun y => (node y).punctureLength) (fun y => (node y).markCap) m r z b.eta b.tau data)
    (admissible : ∀ y ∈ data.nodes, p.admissible y)
    (reduction : InitialEnergy (fun y => (node y).energy Z) (fun y => (node y).totalLength)
      source Z m r z b.eta b.pi ((3 * C * L) * H ^ A) data)
    (hc : 0 < c) (hz : 0 ≤ z) (hm : m ≤ Mmax)
    (hmargin : r + 2 * z ≤ m - 4 * c / 3) :
    InitialInputs node p source m r z where
  data := data
  geometry := geometry
  admissible := admissible
  row_upper := initial_children_row_upper geometry hz hm hmargin
    (by linarith [b.eta_terminal, b.tau_terminal])
  reduction := reduction

/-- Combine the initial masked Poisson reduction with the completed
canonical induction.  Initial margins are proved from the original
marked inequalities; they are not fields of `InitialInputs`. -/
theorem inverse_energy_of_reductions {α : Type*} {node : α → CanonicalDatum K}
    {Mmax c eps Z C L H A source m r z : ℝ}
    (b : DescentBudget Mmax c eps)
    (p : CanonicalInputs node b Z C L H A) (q : InitialInputs node p source m r z)
    (hMmax : 0 ≤ Mmax) (hc : 0 < c)
    (hZ : 1 ≤ Z) (hC : 1 ≤ C) (hL : 1 ≤ L) (hH : 1 ≤ H) (hA : 0 ≤ A)
    (h₁ : r + 2 * z ≤ m - 4 * c / 3)
    (h₂ : 2 * r + 8 * z ≤ 3 * m - 4 * c / 3) :
    source ≤ (3 * (3 * C * L)) ^ (b.depth + 1) *
      Z ^ (m + eps) * H ^ (A * ((b.depth + 1 : ℕ) : ℝ)) := by
  have hC0 : 1 ≤ 3 * C * L := by
    have hCL := one_le_mul_of_one_le_of_one_le hC hL
    nlinarith
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hconst : 1 ≤ 3 * (3 * C * L) := by linarith
  have hAdepth : 0 ≤ A * (b.depth : ℝ) := mul_nonneg hA (Nat.cast_nonneg _)
  let B := (3 * (3 * C * L)) ^ b.depth * H ^ (A * (b.depth : ℝ))
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ hconst) (Real.one_le_rpow hH hAdepth)
  have hmargin : ∀ y ∈ q.data.nodes,
      CanonicalMargins (node y).totalLength (node y).rowLength
        (node y).punctureLength (node y).markCap c := by
    have hm := initial_children_margins q.geometry h₁ h₂
      (by simp only [min_self]; positivity : 0 ≤ min (4 * c / 3) (4 * c / 3))
      (by simp only [min_self]; linarith [b.eta_terminal])
      (by simp only [min_self]; linarith [b.tau_terminal])
    have heq : 3 * min (4 * c / 3) (4 * c / 3) / 4 = c := by rw [min_self]; ring
    simpa only [heq] using hm
  have hchild : ∀ y ∈ q.data.nodes,
      (node y).energy Z ≤ B * Z ^ ((node y).totalLength + eps / 2) := by
    intro y hy
    have hb := p.energy_bound hZ hC hL hH hA hc y (q.admissible y hy)
      (hmargin y hy) (q.row_upper y hy)
    convert hb using 1 <;> dsimp only [B] <;> ring
  have hloss := budget_initial_loss b hMmax
  have heps : 0 ≤ eps / 2 := by
    have he := b.loss_budget
    have hn : 0 ≤ (b.depth : ℝ) * (40 * b.eta + b.tau + b.pi) := by
      have := b.eta_pos
      have := b.tau_pos
      have := b.pi_pos
      positivity
    linarith
  have hb := initial_energy_bound hZ b.eta_pos.le b.pi_pos.le
    (by have := zero_le_one.trans hC0; positivity : 0 ≤ (3 * C * L) * H ^ A)
    hB heps q.geometry q.reduction hchild
  have hheight : H ^ A * H ^ (A * (b.depth : ℝ)) =
      H ^ (A * ((b.depth + 1 : ℕ) : ℝ)) := by
    rw [← Real.rpow_add hH0]
    congr 1
    push_cast
    ring
  apply hb.trans
  calc
    _ ≤ 3 * ((3 * C * L) * H ^ A) * B * Z ^ (m + eps) := by
      apply mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
      have := zero_le_one.trans hB
      have := zero_le_one.trans hC0
      positivity
    _ = _ := by
      dsimp only [B]
      rw [pow_succ]
      calc
        _ = ((3 * (3 * C * L)) ^ b.depth * (3 * (3 * C * L))) *
            Z ^ (m + eps) * (H ^ A * H ^ (A * (b.depth : ℝ))) := by ring
        _ = _ := by rw [hheight]

/-- Corrected relative marked inverse theorem on the repository's
literal `inverseEnergy`.  The source data is explicit and the theorem
does not refer to the admitted `momentModels` or `highExpansion`. -/
theorem canonical_inverse_models {α : Type*} {node : α → CanonicalDatum K}
    {ω ψ : HeckeCharacter K} (source : MomentData K ω ψ) (a : RealParameters)
    {Mmax c eps Z C L H A : ℝ} (b : DescentBudget Mmax c eps)
    (p : CanonicalInputs node b Z C L H A)
    (q : InitialInputs node p (inverseEnergy source a Z 0) a.m a.r a.z)
    (hMmax : 0 ≤ Mmax) (hc : 0 < c)
    (hZ : 1 ≤ Z) (hC : 1 ≤ C) (hL : 1 ≤ L) (hH : 1 ≤ H) (hA : 0 ≤ A)
    (h₁ : a.r + 2 * a.z ≤ a.m - 4 * c / 3)
    (h₂ : 2 * a.r + 8 * a.z ≤ 3 * a.m - 4 * c / 3) :
    inverseEnergy source a Z 0 ≤ (3 * (3 * C * L)) ^ (b.depth + 1) *
      Z ^ (a.m + eps) * H ^ (A * ((b.depth + 1 : ℕ) : ℝ)) :=
  inverse_energy_of_reductions b p q hMmax hc hZ hC hL hH hA h₁ h₂

/-- The independent unmarked energy uses exactly the row ball, sixth-free
filter and inverse polynomial of the skeleton, with arbitrary explicit
`MomentData` in place of its admitted model choice. -/
def independentInverseEnergy {ω ψ : HeckeCharacter K}
    (source : MomentData K ω ψ) (U D : ℝ) : ℝ :=
  ∑ u ∈ (source.rows (2 * U)).filter (SixthPowerFreeIdeal (K := K)),
    ‖inversePolynomial source u D 0‖ ^ 2

/-- Independent scales enter the same actual source reduction after a
proved logarithmic reparameterization, including the case `U = D = 1`.
Any eventual-only construction still needs the separate bounded-scale
estimate recorded by `all_scales_of_bounded_and_eventual`. -/
theorem canonical_unmarked_inverse {α : Type*} {node : α → CanonicalDatum K}
    {ω ψ : HeckeCharacter K} (source : MomentData K ω ψ)
    {Mmax eps U D C L H A a : ℝ} (ha : 0 < a)
    (b : DescentBudget Mmax (3 * (a / (1 + a)) / 4) eps)
    (p : CanonicalInputs node b U C L H A)
    (q : InitialInputs node p (independentInverseEnergy source U D) 1 (Real.logb U D) 0)
    (hMmax : 0 ≤ Mmax) (hU : 1 ≤ U) (hD : 1 ≤ D)
    (hcap : D ≤ U ^ (1 / (1 + a)))
    (hC : 1 ≤ C) (hL : 1 ≤ L) (hH : 1 ≤ H) (hA : 0 ≤ A) :
    independentInverseEnergy source U D ≤ (3 * (3 * C * L)) ^ (b.depth + 1) *
      U ^ (1 + eps) * H ^ (A * ((b.depth + 1 : ℕ) : ℝ)) := by
  obtain ⟨_, _, _, hmargin⟩ := independent_scale_parameters ha hU hD hcap
  have hc : 0 < 3 * (a / (1 + a)) / 4 := by
    have := unmarked_margin_pos ha
    positivity
  apply inverse_energy_of_reductions b p q hMmax hc hU hC hL hH hA
  · have hm := hmargin.1
    dsimp only [MarkedMargins] at hmargin
    linarith
  · have hm := hmargin.2
    linarith

end HeckeSkeleton.Moments.MOM_INV_INDUCTION
