import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Literal finite-place shell coefficients

This file constructs coefficients by integration, then proves a common lower
valuation cutoff, all decay exponents below `1/3`, and absolute Mellin
convergence.  The hypotheses concern the pointwise local Whittaker function;
none of the conclusions about coefficient sequences is an input.

The local representation-theoretic input is exactly fixed-vector support at
large norm and fixed-vector power decay at small norm.  The `branch` parameter
may be infinite: all of its dependence is confined to multipliers of norm at
most one.  Uniformity therefore does not require counting the branch set.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.FiniteShell

open MeasureTheory Set Filter
open scoped BigOperators Topology

/-- A unit-shell parametrization of one fixed local Whittaker function.
For the application `X` is the multiplicative local field, `U` its units,
`radius` is the normalized local absolute value, and
`shell k u = π ^ k * u`.  The branch multiplier consists of a unitary
character and a power-class indicator. -/
structure LocalShellData (Branch X U : Type*) where
  q : ℕ
  q_gt_one : 1 < q
  radius : X → ℝ
  shell : ℤ → U → X
  shell_radius : ∀ k u, radius (shell k u) = (q : ℝ) ^ (-(k : ℝ))
  value : X → ℂ
  multiplier : Branch → ℤ → U → ℂ
  multiplier_norm : ∀ b k u, ‖multiplier b k u‖ ≤ 1

/-- Pointwise local fixed-vector estimates.  These are supplied by the
finite-place representation theory, before any shell integral is formed. -/
structure LocalWhittakerBounds {Branch X U : Type*}
    (d : LocalShellData Branch X U) : Prop where
  large_support : ∃ M : ℝ, 0 < M ∧ ∀ x, M < d.radius x → d.value x = 0
  small_power : ∀ δ : ℝ, 0 < δ → δ < 1 / 3 → ∃ B : ℝ, 0 ≤ B ∧
    ∀ x, 0 < d.radius x → d.radius x ≤ 1 →
      ‖d.value x‖ ≤ B * (d.radius x) ^ δ

variable {Branch X U : Type*} [MeasurableSpace U]

/-- The coefficient is the actual integral on one normalized valuation shell.
The measure is arbitrary finite Haar measure on the unit group; its mass is
retained in all estimates. -/
def coefficient (d : LocalShellData Branch X U) (μ : Measure U)
    (b : Branch) (k : ℤ) : ℂ :=
  ∫ u, d.multiplier b k u * d.value (d.shell k u) ∂μ

/-- This specification is definitional and is available to global unfolding.
A caller should additionally supply `ShellIntegrable` to certify that none
of these Bochner integrals is using the nonintegrable default value. -/
theorem coefficient_spec (d : LocalShellData Branch X U) (μ : Measure U)
    (b : Branch) (k : ℤ) :
    coefficient d μ b k =
      ∫ u, d.multiplier b k u * d.value (d.shell k u) ∂μ := rfl

/-- Local shell integrability, usually obtained from local constancy on the
compact unit group.  This does not assert any Mellin or orbit summability. -/
def ShellIntegrable (d : LocalShellData Branch X U) (μ : Measure U) : Prop :=
  ∀ b k, Integrable (fun u => d.multiplier b k u * d.value (d.shell k u)) μ

private theorem q_pos (d : LocalShellData Branch X U) : (0 : ℝ) < d.q := by
  exact_mod_cast lt_trans Nat.zero_lt_one d.q_gt_one

private theorem q_one_lt (d : LocalShellData Branch X U) : (1 : ℝ) < d.q := by
  exact_mod_cast d.q_gt_one

/-- Large local norm makes the literal shell integral vanish. -/
theorem coefficient_eq_zero_of_radius
    (d : LocalShellData Branch X U) (μ : Measure U)
    (M : ℝ) (hlarge : ∀ x, M < d.radius x → d.value x = 0)
    (b : Branch) (k : ℤ) (hk : M < (d.q : ℝ) ^ (-(k : ℝ))) :
    coefficient d μ b k = 0 := by
  unfold coefficient
  have hz : (fun u => d.multiplier b k u * d.value (d.shell k u)) =
      (fun _ : U => (0 : ℂ)) := by
    funext u
    rw [hlarge (d.shell k u) (by simpa only [d.shell_radius] using hk), mul_zero]
  rw [hz, integral_zero]

/-- One local pointwise support bound gives a valuation cutoff uniform in
all branch multipliers. -/
theorem coefficient_cutoff
    (d : LocalShellData Branch X U) (μ : Measure U)
    (hd : LocalWhittakerBounds d) :
    ∃ k₀ : ℤ, ∀ b k, k < k₀ → coefficient d μ b k = 0 := by
  obtain ⟨M, hM, hlarge⟩ := hd.large_support
  obtain ⟨k₀, hk₀⟩ := exists_int_lt (-(Real.log M / Real.log (d.q : ℝ)))
  refine ⟨k₀, fun b k hk => coefficient_eq_zero_of_radius d μ M hlarge b k ?_⟩
  apply (Real.lt_rpow_iff_log_lt hM (q_pos d)).2
  apply (div_lt_iff₀ (Real.log_pos (q_one_lt d))).mp
  have hcast : (k : ℝ) < (k₀ : ℝ) := by exact_mod_cast hk
  linarith

private theorem shell_radius_le_one
    (d : LocalShellData Branch X U) (k : ℤ) (hk : 0 ≤ k) :
    (d.q : ℝ) ^ (-(k : ℝ)) ≤ 1 := by
  have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
  simpa only [Real.rpow_zero] using
    Real.rpow_le_rpow_of_exponent_le (q_one_lt d).le (neg_nonpos.mpr hk')

/-- A small-norm power estimate survives integration on the unit shell,
with the correct Haar-volume factor. -/
theorem coefficient_bound_of_pointwise
    (d : LocalShellData Branch X U) (μ : Measure U) [IsFiniteMeasure μ]
    (δ B : ℝ)
    (hbound : ∀ x, 0 < d.radius x → d.radius x ≤ 1 →
      ‖d.value x‖ ≤ B * (d.radius x) ^ δ)
    (b : Branch) (k : ℤ) (hk : 0 ≤ k) :
    ‖coefficient d μ b k‖ ≤
      (B * μ.real Set.univ) * (d.q : ℝ) ^ (-(k : ℝ) * δ) := by
  have hi : ∀ u : U,
      ‖d.multiplier b k u * d.value (d.shell k u)‖ ≤
        B * (d.q : ℝ) ^ (-(k : ℝ) * δ) := by
    intro u
    calc
      ‖d.multiplier b k u * d.value (d.shell k u)‖ ≤
          ‖d.value (d.shell k u)‖ := by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (d.multiplier_norm b k u)
      _ ≤ B * (d.radius (d.shell k u)) ^ δ :=
        hbound _ (by rw [d.shell_radius]; exact Real.rpow_pos_of_pos (q_pos d) _)
          (by rw [d.shell_radius]; exact shell_radius_le_one d k hk)
      _ = B * (d.q : ℝ) ^ (-(k : ℝ) * δ) := by
        rw [d.shell_radius, ← Real.rpow_mul (q_pos d).le]
  unfold coefficient
  calc
    ‖∫ u, d.multiplier b k u * d.value (d.shell k u) ∂μ‖ ≤
        (B * (d.q : ℝ) ^ (-(k : ℝ) * δ)) * μ.real Set.univ :=
      norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hi)
    _ = (B * μ.real Set.univ) * (d.q : ℝ) ^ (-(k : ℝ) * δ) := by ring

/-- The hypotheses only require positive local decay exponents.  A larger
positive exponent gives every requested `δ < 1/3`, including negative δ. -/
theorem coefficient_decay
    (d : LocalShellData Branch X U) (μ : Measure U) [IsFiniteMeasure μ]
    (hd : LocalWhittakerBounds d)
    (δ : ℝ) (hδ : δ < 1 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b k, 0 ≤ k →
      ‖coefficient d μ b k‖ ≤ C * (d.q : ℝ) ^ (-(k : ℝ) * δ) := by
  let δ' : ℝ := max δ (1 / 6)
  have hδ'pos : 0 < δ' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hδ'third : δ' < 1 / 3 := max_lt hδ (by norm_num)
  obtain ⟨B, hB, hb⟩ := hd.small_power δ' hδ'pos hδ'third
  refine ⟨B * μ.real Set.univ, mul_nonneg hB (measureReal_nonneg), ?_⟩
  intro b k hk
  apply (coefficient_bound_of_pointwise d μ δ' B hb b k hk).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB (measureReal_nonneg))
  apply Real.rpow_le_rpow_of_exponent_le (q_one_lt d).le
  have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
  have hδle : δ ≤ δ' := le_max_left _ _
  nlinarith

/-- A measurable shell integrand with a nonnegative valuation is integrable
as a consequence of the pointwise local estimate; no Mellin assumption is
used.  Compactness/local constancy supplies measurability in the application. -/
theorem shell_integrable_nonnegative
    (d : LocalShellData Branch X U) (μ : Measure U) [IsFiniteMeasure μ]
    (hd : LocalWhittakerBounds d) (b : Branch) (k : ℤ) (hk : 0 ≤ k)
    (hm : AEStronglyMeasurable
      (fun u => d.multiplier b k u * d.value (d.shell k u)) μ) :
    Integrable (fun u => d.multiplier b k u * d.value (d.shell k u)) μ := by
  obtain ⟨B, hB, hb⟩ := hd.small_power (1 / 6) (by norm_num) (by norm_num)
  apply Integrable.of_bound hm (B * (d.q : ℝ) ^ (-(k : ℝ) * (1 / 6)))
  apply Filter.Eventually.of_forall
  intro u
  calc
    ‖d.multiplier b k u * d.value (d.shell k u)‖ ≤ ‖d.value (d.shell k u)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (d.multiplier_norm b k u)
    _ ≤ B * (d.radius (d.shell k u)) ^ (1 / 6 : ℝ) :=
      hb _ (by rw [d.shell_radius]; exact Real.rpow_pos_of_pos (q_pos d) _)
        (by rw [d.shell_radius]; exact shell_radius_le_one d k hk)
    _ = B * (d.q : ℝ) ^ (-(k : ℝ) * (1 / 6 : ℝ)) := by
      rw [d.shell_radius, ← Real.rpow_mul (q_pos d).le]

section FiniteFamily

variable {I : Type*} [Finite I]
variable {Point UnitSpace : I → Type*}
variable [∀ i, MeasurableSpace (UnitSpace i)]
variable (d : ∀ i, LocalShellData Branch (Point i) (UnitSpace i))
variable (μ : ∀ i, Measure (UnitSpace i))
variable (hd : ∀ i, LocalWhittakerBounds (d i))
include hd

/-- Uniform support is a finite-family consequence of local support.
The bound is chosen before the branch and the valuation. -/
theorem uniform_cutoff :
    ∃ k₀ : ℤ, ∀ i b k, k < k₀ → coefficient (d i) (μ i) b k = 0 := by
  choose cut hcut using fun i => coefficient_cutoff (d i) (μ i) (hd i)
  obtain ⟨k₀, hk₀⟩ := (Set.finite_range cut).bddBelow
  refine ⟨k₀, fun i b k hk => hcut i b k ?_⟩
  exact lt_of_lt_of_le hk (hk₀ (Set.mem_range_self i))

/-- Uniform decay is obtained by taking one bound for a finite family of
pointwise local Whittaker functions.  It is uniform in every branch. -/
theorem uniform_decay [∀ i, IsFiniteMeasure (μ i)]
    (δ : ℝ) (hδ : δ < 1 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i b k, 0 ≤ k →
      ‖coefficient (d i) (μ i) b k‖ ≤
        C * ((d i).q : ℝ) ^ (-(k : ℝ) * δ) := by
  choose bound hnonneg hbound using fun i => coefficient_decay (d i) (μ i) (hd i) δ hδ
  obtain ⟨C₀, hC₀⟩ := (Set.finite_range bound).bddAbove
  refine ⟨max 0 C₀, le_max_left _ _, ?_⟩
  intro i b k hk
  apply (hbound i b k hk).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (q_pos (d i)).le _)
  exact (hC₀ (Set.mem_range_self i)).trans (le_max_right _ _)

end FiniteFamily

/-- The analytic step from cutoff and power decay to an actual absolutely
convergent two-sided Mellin sum.  The negative side is finite and the
nonnegative side is dominated by a geometric series. -/
theorem summable_mellin_of_bounds
    (q : ℕ) (hq : 1 < q) (a : ℤ → ℂ)
    (hcutoff : ∃ k₀ : ℤ, ∀ k, k < k₀ → a k = 0)
    (hdecay : ∀ δ : ℝ, δ < 1 / 3 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℤ, 0 ≤ k → ‖a k‖ ≤ C * (q : ℝ) ^ (-(k : ℝ) * δ))
    (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re) :
    Summable (fun k : ℤ => a k * (q : ℂ) ^ (-(k : ℂ) * s)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast lt_trans Nat.zero_lt_one hq
  have hqone : (1 : ℝ) < q := by exact_mod_cast hq
  let δ : ℝ := (1 / 3 - s.re) / 2
  have hδ : δ < 1 / 3 := by dsimp [δ]; linarith
  have hδs : 0 < δ + s.re := by dsimp [δ]; linarith
  obtain ⟨C, hC, hbound⟩ := hdecay δ hδ
  have hgeom : Summable (fun n : ℕ => C * ((q : ℝ) ^ (-(δ + s.re))) ^ n) :=
    (summable_geometric_of_lt_one (Real.rpow_nonneg hqpos.le _)
      (Real.rpow_lt_one_of_one_lt_of_neg hqone (by linarith))).mul_left C
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · apply hgeom.of_norm_bounded
    intro n
    have hre : (-(n : ℂ) * s).re = -(n : ℝ) * s.re := by simp
    have hn : ‖a (n : ℤ)‖ ≤ C * (q : ℝ) ^ (-(n : ℝ) * δ) := by
      simpa only [Int.cast_natCast] using hbound (n : ℤ) (by omega)
    calc
      ‖a (n : ℤ) * (q : ℂ) ^ (-((n : ℤ) : ℂ) * s)‖ =
          ‖a (n : ℤ)‖ * (q : ℝ) ^ (-(n : ℝ) * s.re) := by
        rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
        simp only [Int.cast_natCast, hre]
      _ ≤ (C * (q : ℝ) ^ (-(n : ℝ) * δ)) *
          (q : ℝ) ^ (-(n : ℝ) * s.re) :=
        mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hqpos.le _)
      _ = C * ((q : ℝ) ^ (-(δ + s.re))) ^ n := by
        rw [mul_assoc, ← Real.rpow_add hqpos]
        rw [show -(n : ℝ) * δ + -(n : ℝ) * s.re =
          -(δ + s.re) * (n : ℝ) by ring]
        rw [Real.rpow_mul_natCast hqpos.le]
  · obtain ⟨k₀, hk₀⟩ := hcutoff
    obtain ⟨N, hN⟩ := exists_nat_gt (-k₀)
    apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
    intro n hn
    have hNn : N + 1 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
    have hncut : -(n : ℤ) < k₀ := by omega
    simp only [hk₀ _ hncut, zero_mul]

/-- Absolute Mellin convergence of the literal shell coefficients in the
optimal open half-plane supplied by local `δ < 1/3` decay. -/
theorem shell_mellin_summable
    (d : LocalShellData Branch X U) (μ : Measure U) [IsFiniteMeasure μ]
    (hd : LocalWhittakerBounds d) (b : Branch)
    (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re) :
    Summable (fun k : ℤ => coefficient d μ b k *
      (d.q : ℂ) ^ (-(k : ℂ) * s)) := by
  apply summable_mellin_of_bounds d.q d.q_gt_one (coefficient d μ b) ?_ ?_ s hs
  · obtain ⟨k₀, hk₀⟩ := coefficient_cutoff d μ hd
    exact ⟨k₀, fun k hk => hk₀ b k hk⟩
  · intro δ hδ
    obtain ⟨C, hC, hc⟩ := coefficient_decay d μ hd δ hδ
    exact ⟨C, hC, fun k hk => hc b k hk⟩

end ThetaGlobal.FiniteShell

#print axioms ThetaGlobal.FiniteShell.uniform_cutoff
#print axioms ThetaGlobal.FiniteShell.uniform_decay
#print axioms ThetaGlobal.FiniteShell.shell_mellin_summable
