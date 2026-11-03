module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.FieldTheory.Extension
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.Module.Multilinear.Topology

@[expose] public section
/-! Generated combined-body QA. See manifest.json for exact source hashes. -/

/- BEGIN SOURCE BODY: ThetaGlobal/FiniteShellCoefficients.lean -/
section Verification_FiniteShellCoefficients

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
end

end Verification_FiniteShellCoefficients
/- END SOURCE BODY: ThetaGlobal/FiniteShellCoefficients.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/FiniteClassExpansion.lean -/
section Verification_FiniteClassExpansion

/-!
# Explicit class-mask tensorization for finite-place shell integrals

The reflected sheet contains the literal multiplier
`1_B (κ * c⁻¹) * H(κ,c)^2`.
This file splits this multiplier into a finite sum of products of local
class indicators.  One fixed finite place carries the scalar coefficient.
The construction is exact, preserves every zero, and gives local factors
of norm at most one when the Hilbert/period factors have norm at most one.
It therefore feeds directly into `FiniteShellCoefficients`.
-/

set_option autoImplicit false
noncomputable section
namespace ThetaGlobal.FiniteClass

open MeasureTheory
open scoped Classical BigOperators

/-- The literal finite power-class multiplier from the reflected sheet.
For the theta application `V` is the local sixth-power quotient, `B` is
its allowed-unit image, and `H` is the sextic Hilbert pairing. -/
def powerClassMask {V : Type*} [Group V] (B : Set V)
    (H : V → V → ℂ) (κ c : V) : ℂ :=
  if κ * c⁻¹ ∈ B then H κ c ^ 2 else 0

theorem powerClassMask_norm_le_one {V : Type*} [Group V]
    (B : Set V) (H : V → V → ℂ) (hH : ∀ x y, ‖H x y‖ ≤ 1) (κ c : V) :
    ‖powerClassMask B H κ c‖ ≤ 1 := by
  classical
  unfold powerClassMask
  split_ifs
  · rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hH _ _)
  · simp

variable {P : Type*} [Fintype P]
variable {C : P → Type*} [∀ p, Fintype (C p)]

/-- A product of local equality indicators is the equality indicator of
the complete finite class tuple. -/
theorem prod_delta (x σ : ∀ p, C p) :
    (∏ p, (if x p = σ p then (1 : ℂ) else 0)) =
      if x = σ then 1 else 0 := by
  classical
  by_cases h : x = σ
  · subst σ
    simp
  · rw [if_neg h]
    have hp : ∃ p, x p ≠ σ p := by
      by_contra hn
      apply h
      funext p
      exact not_ne_iff.mp (fun hh => hn ⟨p, hh⟩)
    obtain ⟨p, hp⟩ := hp
    exact Finset.prod_eq_zero (Finset.mem_univ p) (if_neg hp)

/-- The scalar mask is stored at one fixed place.  The other factors are
local power-class indicators, so the result is a genuine finite tensor
presentation rather than an unspecified holomorphic multiplier. -/
def localMaskFactor (pivot : P) (mask : (∀ p, C p) → ℂ)
    (σ : ∀ p, C p) (p : P) (c : C p) : ℂ :=
  (if p = pivot then mask σ else 1) * (if c = σ p then 1 else 0)

theorem localMaskFactor_norm_le_one
    (pivot : P) (mask : (∀ p, C p) → ℂ) (hmask : ∀ σ, ‖mask σ‖ ≤ 1)
    (σ : ∀ p, C p) (p : P) (c : C p) :
    ‖localMaskFactor pivot mask σ p c‖ ≤ 1 := by
  classical
  unfold localMaskFactor
  split_ifs <;> simp_all

theorem prod_localMaskFactor
    (pivot : P) (mask : (∀ p, C p) → ℂ)
    (σ x : ∀ p, C p) :
    (∏ p, localMaskFactor pivot mask σ p (x p)) =
      mask σ * (if x = σ then 1 else 0) := by
  classical
  simp only [localMaskFactor, Finset.prod_mul_distrib]
  rw [prod_delta]
  simp

/-- Exact finite mask reconstruction, including multiplication by any
fixed local scalar values. -/
theorem tensor_expansion
    (pivot : P) (mask : (∀ p, C p) → ℂ)
    (x : ∀ p, C p) (value : P → ℂ) :
    (∑ σ : ∀ p, C p, ∏ p, localMaskFactor pivot mask σ p (x p) * value p) =
      mask x * ∏ p, value p := by
  classical
  simp_rw [Finset.prod_mul_distrib, prod_localMaskFactor]
  rw [← Finset.sum_mul]
  simp [mul_ite]

/-- The same reconstruction with the actual theta class indicator and
Hilbert factor, after assembling the local classes into the global class. -/
theorem theta_tensor_expansion {V : Type*} [Group V]
    (B : Set V) (H : V → V → ℂ) (κ : V)
    (assemble : (∀ p, C p) → V) (pivot : P)
    (x : ∀ p, C p) (value : P → ℂ) :
    (∑ σ : ∀ p, C p, ∏ p,
      localMaskFactor pivot (fun z => powerClassMask B H κ (assemble z)) σ p (x p) *
        value p) =
      powerClassMask B H κ (assemble x) * ∏ p, value p :=
  tensor_expansion pivot _ x value

section Integration

variable {U : P → Type*} [∀ p, MeasurableSpace (U p)]
variable (μ : ∀ p, Measure (U p)) [∀ p, SigmaFinite (μ p)]

/-- Local shell coefficient with its class indicator, actual local period
character, and actual Whittaker value all retained under the integral. -/
def localCoefficient (pivot : P) (mask : (∀ p, C p) → ℂ)
    (classOf : ∀ p, U p → C p) (period whittaker : ∀ p, U p → ℂ)
    (σ : ∀ p, C p) (p : P) : ℂ :=
  ∫ u, localMaskFactor pivot mask σ p (classOf p u) *
    (period p u * whittaker p u) ∂μ p

/-- Exact finite-product shell identity.  Its only analytic assumptions
are integrability of individual local tensor factors, before any global
Mellin or frequency summation occurs. -/
theorem tensor_shell_integral
    (pivot : P) (mask : (∀ p, C p) → ℂ)
    (classOf : ∀ p, U p → C p) (period whittaker : ∀ p, U p → ℂ)
    (hlocal : ∀ σ p, Integrable
      (fun u => localMaskFactor pivot mask σ p (classOf p u) *
        (period p u * whittaker p u)) (μ p)) :
    (∑ σ : ∀ p, C p, ∏ p, localCoefficient μ pivot mask classOf period whittaker σ p) =
      ∫ u : ∀ p, U p,
        mask (fun p => classOf p (u p)) * ∏ p, period p (u p) * whittaker p (u p)
        ∂Measure.pi μ := by
  classical
  calc
    (∑ σ : ∀ p, C p, ∏ p, localCoefficient μ pivot mask classOf period whittaker σ p) =
        ∑ σ : ∀ p, C p, ∫ u : ∀ p, U p,
          ∏ p, localMaskFactor pivot mask σ p (classOf p (u p)) *
            (period p (u p) * whittaker p (u p)) ∂Measure.pi μ := by
      apply Finset.sum_congr rfl
      intro σ _
      exact (integral_fintype_prod_eq_prod
        (fun p u => localMaskFactor pivot mask σ p (classOf p u) *
          (period p u * whittaker p u))).symm
    _ = ∫ u : ∀ p, U p, ∑ σ : ∀ p, C p,
          ∏ p, localMaskFactor pivot mask σ p (classOf p (u p)) *
            (period p (u p) * whittaker p (u p)) ∂Measure.pi μ := by
      symm
      exact integral_finsetSum _ (fun σ _ => Integrable.fintype_prod_dep (hlocal σ))
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      exact tensor_expansion pivot mask (fun p => classOf p (u p))
        (fun p => period p (u p) * whittaker p (u p))

/-- The tensor factors used above can be inserted in `LocalShellData`:
all dependence on κ and the class-sum index remains bounded by one. -/
theorem masked_period_norm_le_one
    (pivot : P) (mask : (∀ p, C p) → ℂ) (hmask : ∀ σ, ‖mask σ‖ ≤ 1)
    (classOf : ∀ p, U p → C p) (period : ∀ p, U p → ℂ)
    (hperiod : ∀ p u, ‖period p u‖ ≤ 1) (σ : ∀ p, C p) (p : P) (u : U p) :
    ‖localMaskFactor pivot mask σ p (classOf p u) * period p u‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (localMaskFactor_norm_le_one pivot mask hmask σ p _)
    (norm_nonneg _) (hperiod p u)

end Integration
end ThetaGlobal.FiniteClass

#print axioms ThetaGlobal.FiniteClass.theta_tensor_expansion
#print axioms ThetaGlobal.FiniteClass.tensor_shell_integral
end

end Verification_FiniteClassExpansion
/- END SOURCE BODY: ThetaGlobal/FiniteClassExpansion.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/FiniteTensorCoefficients.lean -/
section Verification_FiniteTensorCoefficients

/-!
# A literal finite tensor of reflected class-shell coefficients

This module joins the two separately checked operations:
* local Whittaker shell integration and power bounds;
* finite tensor expansion of the actual `1_B(κ c⁻¹) H(κ,c)^2` multiplier.

The local period is the `PUnit` multiplier in the base shell datum.  It is
kept inside the shell integral, including its uniformizer values.  In
particular no finite-order hypothesis on those uniformizer values is used.
-/

set_option autoImplicit false
noncomputable section
namespace ThetaGlobal.FiniteTensor

open MeasureTheory
open scoped Classical BigOperators
open FiniteShell FiniteClass

variable {P : Type*} [Fintype P]
variable {C : P → Type*} [∀ p, Fintype (C p)]
variable {V : Type*} [Group V]
variable {X U : P → Type*} [∀ p, MeasurableSpace (U p)]

/-- Add the full finite power-class multiplier to a local period-Whittaker
shell datum.  The class-sum index σ is a tensor index, whereas κ is the
reflected frequency class. -/
def withClassMask
    (B : Set V) (H : V → V → ℂ) (hH : ∀ x y, ‖H x y‖ ≤ 1)
    (assemble : (∀ p, C p) → V) (pivot : P)
    (classOf : ∀ p, X p → C p) (p : P)
    (d : LocalShellData PUnit (X p) (U p)) :
    LocalShellData (V × (∀ p, C p)) (X p) (U p) where
  q := d.q
  q_gt_one := d.q_gt_one
  radius := d.radius
  shell := d.shell
  shell_radius := d.shell_radius
  value := d.value
  multiplier b k u :=
    localMaskFactor pivot (fun c => powerClassMask B H b.1 (assemble c)) b.2 p
      (classOf p (d.shell k u)) * d.multiplier PUnit.unit k u
  multiplier_norm b k u := by
    rw [norm_mul]
    exact mul_le_one₀
      (localMaskFactor_norm_le_one pivot _
        (fun c => powerClassMask_norm_le_one B H hH b.1 (assemble c)) b.2 p _)
      (norm_nonneg _) (d.multiplier_norm PUnit.unit k u)

/-- The pointwise local Whittaker estimates are unchanged by adjoining
the finite class mask; their proof is not repeated or assumed anew. -/
theorem withClassMask_bounds
    (B : Set V) (H : V → V → ℂ) (hH : ∀ x y, ‖H x y‖ ≤ 1)
    (assemble : (∀ p, C p) → V) (pivot : P)
    (classOf : ∀ p, X p → C p) (p : P)
    (d : LocalShellData PUnit (X p) (U p)) (hd : LocalWhittakerBounds d) :
    LocalWhittakerBounds (withClassMask B H hH assemble pivot classOf p d) where
  large_support := hd.large_support
  small_power := hd.small_power

/-- Exact coefficient specification, with κ, the allowed-class indicator,
the Hilbert factor, local period, Whittaker vector, and valuation all visible. -/
theorem coefficient_spec
    (B : Set V) (H : V → V → ℂ) (hH : ∀ x y, ‖H x y‖ ≤ 1)
    (assemble : (∀ p, C p) → V) (pivot : P)
    (classOf : ∀ p, X p → C p) (p : P)
    (d : LocalShellData PUnit (X p) (U p)) (μ : Measure (U p))
    (κ : V) (σ : ∀ p, C p) (k : ℤ) :
    FiniteShell.coefficient (withClassMask B H hH assemble pivot classOf p d) μ (κ, σ) k =
      ∫ u, (if p = pivot then powerClassMask B H κ (assemble σ) else 1) *
        (if classOf p (d.shell k u) = σ p then 1 else 0) *
        d.multiplier PUnit.unit k u * d.value (d.shell k u) ∂μ := rfl

/-- Reassembling the local shell coefficients recovers precisely the
masked finite-place integral, before Mellin transformation. -/
theorem coefficient_tensor_sum
    (B : Set V) (H : V → V → ℂ) (hH : ∀ x y, ‖H x y‖ ≤ 1)
    (assemble : (∀ p, C p) → V) (pivot : P)
    (classOf : ∀ p, X p → C p)
    (d : ∀ p, LocalShellData PUnit (X p) (U p))
    (μ : ∀ p, Measure (U p)) [∀ p, SigmaFinite (μ p)]
    (κ : V) (k : P → ℤ)
    (hlocal : ∀ σ p, Integrable
      (fun u => localMaskFactor pivot (fun c => powerClassMask B H κ (assemble c)) σ p
        (classOf p ((d p).shell (k p) u)) *
        ((d p).multiplier PUnit.unit (k p) u * (d p).value ((d p).shell (k p) u))) (μ p)) :
    (∑ σ : ∀ p, C p, ∏ p,
      FiniteShell.coefficient (withClassMask B H hH assemble pivot classOf p (d p))
        (μ p) (κ, σ) (k p)) =
      ∫ u : ∀ p, U p,
        powerClassMask B H κ (assemble (fun p => classOf p ((d p).shell (k p) (u p)))) *
          ∏ p, (d p).multiplier PUnit.unit (k p) (u p) *
            (d p).value ((d p).shell (k p) (u p)) ∂Measure.pi μ := by
  classical
  have h := tensor_shell_integral μ pivot
    (fun c => powerClassMask B H κ (assemble c))
    (fun p u => classOf p ((d p).shell (k p) u))
    (fun p u => (d p).multiplier PUnit.unit (k p) u)
    (fun p u => (d p).value ((d p).shell (k p) u)) hlocal
  simpa only [FiniteShell.coefficient, withClassMask, localCoefficient, mul_assoc] using h

section FiniteVectors

variable {Sector Tensor : Type*} [Finite Sector] [Finite Tensor]
variable (B : Set V) (H : V → V → ℂ) (hH : ∀ x y, ‖H x y‖ ≤ 1)
variable (assemble : (∀ p, C p) → V) (pivot : P)
variable (classOf : ∀ p, X p → C p)
variable (d : Sector → Tensor → ∀ p, LocalShellData PUnit (X p) (U p))
variable (μ : ∀ p, Measure (U p)) [∀ p, IsFiniteMeasure (μ p)]
variable (hd : ∀ u t p, LocalWhittakerBounds (d u t p))
include hd

/-- One cutoff for all sectors, all tensor summands, all places, all
frequency classes and all class-separation indices. -/
theorem uniform_cutoff :
    ∃ k₀ : ℤ, ∀ u t p κ σ k, k < k₀ →
      FiniteShell.coefficient
        (withClassMask B H hH assemble pivot classOf p (d u t p)) (μ p) (κ, σ) k = 0 := by
  let D (i : Sector × Tensor × P) :=
    withClassMask B H hH assemble pivot classOf i.2.2 (d i.1 i.2.1 i.2.2)
  have hD : ∀ i, LocalWhittakerBounds (D i) := fun i =>
    withClassMask_bounds B H hH assemble pivot classOf i.2.2
      (d i.1 i.2.1 i.2.2) (hd i.1 i.2.1 i.2.2)
  obtain ⟨k₀, hk₀⟩ := FiniteShell.uniform_cutoff D (fun i => μ i.2.2) hD
  exact ⟨k₀, fun u t p κ σ k hk => hk₀ (u, t, p) (κ, σ) k hk⟩

/-- One decay constant, with the local norm `q_p` retained exactly, for
all finite vectors and all reflected power-class branches. -/
theorem uniform_decay (δ : ℝ) (hδ : δ < 1 / 3) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ u t p κ σ k, 0 ≤ k →
      ‖FiniteShell.coefficient
        (withClassMask B H hH assemble pivot classOf p (d u t p)) (μ p) (κ, σ) k‖ ≤
        C₀ * ((d u t p).q : ℝ) ^ (-(k : ℝ) * δ) := by
  let D (i : Sector × Tensor × P) :=
    withClassMask B H hH assemble pivot classOf i.2.2 (d i.1 i.2.1 i.2.2)
  have hD : ∀ i, LocalWhittakerBounds (D i) := fun i =>
    withClassMask_bounds B H hH assemble pivot classOf i.2.2
      (d i.1 i.2.1 i.2.2) (hd i.1 i.2.1 i.2.2)
  obtain ⟨C₀, hC₀, hc⟩ := FiniteShell.uniform_decay D (fun i => μ i.2.2) hD δ hδ
  exact ⟨C₀, hC₀, fun u t p κ σ k hk => hc (u, t, p) (κ, σ) k hk⟩

end FiniteVectors
end ThetaGlobal.FiniteTensor

#print axioms ThetaGlobal.FiniteTensor.coefficient_tensor_sum
#print axioms ThetaGlobal.FiniteTensor.uniform_cutoff
#print axioms ThetaGlobal.FiniteTensor.uniform_decay
end

end Verification_FiniteTensorCoefficients
/- END SOURCE BODY: ThetaGlobal/FiniteTensorCoefficients.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/FinitePowerQuotient.lean -/
section Verification_FinitePowerQuotient

/-!
# Power-class quotients after removing a power-divisible factor

Both project models of the S-local group have the same finite-place
coordinates and different presentations of the complex coordinates.
Since sixth powers are surjective on the latter, their sixth-power class
groups are canonically identified through the finite coordinates.  This
avoids an arbitrary equivalence of archimedean models.
-/

set_option autoImplicit false
noncomputable section
namespace ThetaGlobal.FinitePowerQuotient

open scoped Classical

variable {P : Type*} (G : Type*) [CommGroup G]
variable (H : P → Type*) [∀ p, CommGroup (H p)] (n : ℕ)

abbrev PowerClass (A : Type*) [CommGroup A] := A ⧸ (powMonoidHom n : A →* A).range

/-- Projection to the actual local power classes in every finite factor. -/
def finitePartHom : PowerClass n (G × (∀ p, H p)) →* (∀ p, PowerClass n (H p)) :=
  QuotientGroup.lift (powMonoidHom n : (G × (∀ p, H p)) →* _).range
    { toFun := fun x p => QuotientGroup.mk' (powMonoidHom n : H p →* H p).range (x.2 p)
      map_one' := by funext p; exact map_one _
      map_mul' := by intro x y; funext p; exact map_mul _ _ _ }
    (by
      rintro x ⟨y, rfl⟩
      funext p
      apply (QuotientGroup.eq_one_iff _).mpr
      exact ⟨y.2 p, rfl⟩)

@[simp] theorem finitePartHom_mk (x : G × (∀ p, H p)) :
    finitePartHom G H n (QuotientGroup.mk x) =
      fun p => (QuotientGroup.mk (x.2 p) : PowerClass n (H p)) := rfl

/-- Only surjectivity of the n-th-power map on the discarded factor is
needed for injectivity; no assumption on the local quotient is used. -/
theorem finitePartHom_injective (hG : ∀ g : G, ∃ x, x ^ n = g) :
    Function.Injective (finitePartHom G H n) := by
  intro c d hcd
  induction c using QuotientGroup.induction_on with | H a => ?_
  induction d using QuotientGroup.induction_on with | H b => ?_
  apply QuotientGroup.eq.mpr
  have hv : ∀ p, ∃ q : H p, q ^ n = (a.2 p)⁻¹ * b.2 p := by
    intro p
    have h := congrFun hcd p
    obtain ⟨q, hq⟩ := QuotientGroup.eq.mp h
    exact ⟨q, hq⟩
  let q : ∀ p, H p := fun p => Classical.choose (hv p)
  have hq : ∀ p, q p ^ n = (a.2 p)⁻¹ * b.2 p :=
    fun p => Classical.choose_spec (hv p)
  obtain ⟨x, hx⟩ := hG (a.1⁻¹ * b.1)
  exact ⟨(x, q), Prod.ext hx (funext hq)⟩

theorem finitePartHom_surjective : Function.Surjective (finitePartHom G H n) := by
  intro c
  refine ⟨QuotientGroup.mk ((1 : G), fun p => Quotient.out (c p)), ?_⟩
  funext p
  simp

/-- Canonical removal of a factor whose n-th-power map is surjective. -/
def finitePartEquiv (hG : ∀ g : G, ∃ x, x ^ n = g) :
    PowerClass n (G × (∀ p, H p)) ≃* (∀ p, PowerClass n (H p)) :=
  MulEquiv.ofBijective (finitePartHom G H n)
    ⟨finitePartHom_injective G H n hG, finitePartHom_surjective G H n⟩

@[simp] theorem finitePartEquiv_mk (hG : ∀ g : G, ∃ x, x ^ n = g)
    (x : G × (∀ p, H p)) :
    finitePartEquiv G H n hG (QuotientGroup.mk x) =
      fun p => (QuotientGroup.mk (x.2 p) : PowerClass n (H p)) := rfl

variable (G' : Type*) [CommGroup G']

/-- Exact comparison of two archimedean presentations sharing the same
finite local groups. -/
def changeDivisibleFactor
    (hG : ∀ g : G, ∃ x, x ^ n = g) (hG' : ∀ g : G', ∃ x, x ^ n = g) :
    PowerClass n (G × (∀ p, H p)) ≃* PowerClass n (G' × (∀ p, H p)) :=
  (finitePartEquiv G H n hG).trans (finitePartEquiv G' H n hG').symm

/-- The class of a genuine element is determined by its finite coordinates;
this formula supplies the dictionary on every actual rational diagonal. -/
theorem changeDivisibleFactor_mk
    (hG : ∀ g : G, ∃ x, x ^ n = g) (hG' : ∀ g : G', ∃ x, x ^ n = g)
    (a : G) (a' : G') (b : ∀ p, H p) :
    changeDivisibleFactor G H n G' hG hG' (QuotientGroup.mk (a, b)) =
      (QuotientGroup.mk (a', b) : PowerClass n (G' × (∀ p, H p))) := by
  apply (finitePartEquiv G' H n hG').injective
  simp [changeDivisibleFactor]

end ThetaGlobal.FinitePowerQuotient

#print axioms ThetaGlobal.FinitePowerQuotient.finitePartEquiv
#print axioms ThetaGlobal.FinitePowerQuotient.changeDivisibleFactor_mk
end

end Verification_FinitePowerQuotient
/- END SOURCE BODY: ThetaGlobal/FinitePowerQuotient.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/FiniteHaarShells.lean -/
section Verification_FiniteHaarShells

/-!
# Decomposing actual multiplicative Haar into valuation shells

This is a purely geometric measure theorem.  A uniformizer and the embedded
integral-unit group give all valuation shells.  Pulling the *given* Haar
measure back to the integral units, and then translating it by all integer
powers of the uniformizer, reconstructs that same Haar measure.  No unit
volume is set to one and no Mellin convergence statement is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.FiniteHaarShells

open MeasureTheory MeasureTheory.Measure Set
open scoped BigOperators

variable {G U : Type*} [CommGroup G] [MeasurableSpace G]
  [MeasurableMul G] [MeasurableInv G] [MeasurableSpace U]

/-- A valuation fiber, with additive indexing convention `ord(π) = 1`. -/
def valuationFiber (e : G →* Multiplicative ℤ) (k : ℤ) : Set G :=
  {x | e x = Multiplicative.ofAdd k}

/-- The unit-shell measure is induced by the fixed multiplicative Haar,
including its original normalization. -/
def unitMeasure (ν : Measure G) (ι : U → G) : Measure U := ν.comap ι

theorem unitMeasure_finite (ν : Measure G) (ι : U → G)
    (hι : MeasurableEmbedding ι) (hfinite : ν (Set.range ι) < ⊤) :
    IsFiniteMeasure (unitMeasure ν ι) := by
  constructor
  change ν.comap ι Set.univ < ⊤
  rw [hι.comap_apply, Set.image_univ]
  exact hfinite

private theorem order_uniformizer_zpow (e : G →* Multiplicative ℤ)
    (π : G) (hπ : e π = Multiplicative.ofAdd (1 : ℤ)) (k : ℤ) :
    e (π ^ k) = Multiplicative.ofAdd k := by
  rw [map_zpow, hπ, ← ofAdd_zsmul]
  simp

/-- A translated unit Haar measure is exactly Haar restricted to the
corresponding valuation fiber. -/
theorem map_unitMeasure_shell (ν : Measure G) [IsMulLeftInvariant ν]
    (e : G →* Multiplicative ℤ) (π : G)
    (hπ : e π = Multiplicative.ofAdd (1 : ℤ))
    (ι : U → G) (hι : MeasurableEmbedding ι)
    (hrange : Set.range ι = valuationFiber e 0) (k : ℤ) :
    Measure.map (fun u => π ^ k * ι u) (unitMeasure ν ι) =
      ν.restrict (valuationFiber e k) := by
  have hpre : (fun x : G => π ^ k * x) ⁻¹' valuationFiber e k =
      valuationFiber e 0 := by
    ext x
    change e (π ^ k * x) = Multiplicative.ofAdd k ↔ e x = 1
    simp only [map_mul, order_uniformizer_zpow e π hπ k, mul_eq_left]
  calc
    Measure.map (fun u => π ^ k * ι u) (unitMeasure ν ι) =
        (Measure.map ι (unitMeasure ν ι)).map (fun x => π ^ k * x) := by
      rw [Measure.map_map (measurable_const_mul _) hι.measurable]
      rfl
    _ = (ν.restrict (valuationFiber e 0)).map (fun x => π ^ k * x) := by
      rw [unitMeasure, hι.map_comap, hrange]
    _ = (ν.map (fun x => π ^ k * x)).restrict (valuationFiber e k) := by
      have he := (MeasurableEquiv.mulLeft (π ^ k)).restrict_map ν (valuationFiber e k)
      change (ν.map (fun x => π ^ k * x)).restrict (valuationFiber e k) =
        (ν.restrict ((fun x => π ^ k * x) ⁻¹' valuationFiber e k)).map
          (fun x => π ^ k * x) at he
      rw [hpre] at he
      exact he.symm
    _ = ν.restrict (valuationFiber e k) := by rw [map_mul_left_eq_self]

/-- Every point has exactly one integer valuation.  Summing Haar restricted
to those measurable fibers recovers the original measure. -/
theorem sum_restrict_valuationFiber (ν : Measure G)
    (e : G →* Multiplicative ℤ)
    (hmeas : ∀ k : ℤ, MeasurableSet (valuationFiber e k)) :
    Measure.sum (fun k : ℤ => ν.restrict (valuationFiber e k)) = ν := by
  have hdisjoint : Pairwise (fun k l => Disjoint (valuationFiber e k) (valuationFiber e l)) := by
    intro k l hkl
    rw [Set.disjoint_left]
    intro x hx hy
    apply hkl
    have h := hx.symm.trans hy
    exact Multiplicative.ofAdd.injective h
  have hcover : (⋃ k : ℤ, valuationFiber e k) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨Multiplicative.toAdd (e x), rfl⟩
  rw [← Measure.restrict_iUnion hdisjoint hmeas, hcover, Measure.restrict_univ]

/-- The Haar shell identity used by the Mellin integration theorem.  Its
inputs are valuation, uniformizer, unit embedding, and left invariance. -/
theorem haar_eq_sum_shells (ν : Measure G) [IsMulLeftInvariant ν]
    (e : G →* Multiplicative ℤ) (π : G)
    (hπ : e π = Multiplicative.ofAdd (1 : ℤ))
    (ι : U → G) (hι : MeasurableEmbedding ι)
    (hrange : Set.range ι = valuationFiber e 0)
    (hmeas : ∀ k : ℤ, MeasurableSet (valuationFiber e k)) :
    ν = Measure.sum (fun k : ℤ =>
      Measure.map (fun u => π ^ k * ι u) (unitMeasure ν ι)) := by
  simp_rw [map_unitMeasure_shell ν e π hπ ι hι hrange]
  exact (sum_restrict_valuationFiber ν e hmeas).symm

end ThetaGlobal.FiniteHaarShells

#print axioms ThetaGlobal.FiniteHaarShells.map_unitMeasure_shell
#print axioms ThetaGlobal.FiniteHaarShells.haar_eq_sum_shells
end

end Verification_FiniteHaarShells
/- END SOURCE BODY: ThetaGlobal/FiniteHaarShells.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/FiniteMellinIntegration.lean -/
section Verification_FiniteMellinIntegration

/-!
# Absolute shell integration and finite-place Mellin transforms

The coefficient estimates alone do not justify unfolding an integral: there
could be cancellation inside each shell.  This module applies the same raw
local Whittaker estimates to the absolute values *before* integrating.  It
therefore proves summability of the integrals of the norms, genuine
integrability for the sum of shell measures, and the literal Mellin identity.

The measure identity used by the final theorem is a geometric hypothesis,
independent of the test function and of the Mellin parameter.  A separate
valuation-shell module proves it from invariance of multiplicative Haar.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.FiniteMellinIntegration

open MeasureTheory
open scoped BigOperators
open ThetaGlobal.FiniteShell

variable {Branch X U : Type*} [MeasurableSpace U]

/-- Take absolute values of the local vector and of the unitary mask before
forming a coefficient.  This retains all pointwise support and decay input. -/
def absoluteData (d : LocalShellData Branch X U) : LocalShellData Branch X U where
  q := d.q
  q_gt_one := d.q_gt_one
  radius := d.radius
  shell := d.shell
  shell_radius := d.shell_radius
  value x := (‖d.value x‖ : ℂ)
  multiplier b k u := (‖d.multiplier b k u‖ : ℂ)
  multiplier_norm b k u := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_norm] using
      d.multiplier_norm b k u

theorem absoluteData_bounds (d : LocalShellData Branch X U)
    (hd : LocalWhittakerBounds d) : LocalWhittakerBounds (absoluteData d) := by
  constructor
  · obtain ⟨M, hM, hlarge⟩ := hd.large_support
    exact ⟨M, hM, fun x hx => by simpa [absoluteData, hlarge x hx]⟩
  · intro δ hδ hδ'
    obtain ⟨B, hB, hbound⟩ := hd.small_power δ hδ hδ'
    refine ⟨B, hB, fun x hx hx' => ?_⟩
    simpa only [absoluteData, Complex.norm_real, Real.norm_eq_abs, abs_norm] using
      hbound x hx hx'

/-- The new coefficient is precisely the integral of the norm, with no
norm-of-an-integral substitution. -/
theorem absolute_coefficient_spec (d : LocalShellData Branch X U)
    (μ : Measure U) (b : Branch) (k : ℤ) :
    coefficient (absoluteData d) μ b k =
      Complex.ofReal (∫ u, ‖d.multiplier b k u * d.value (d.shell k u)‖ ∂μ) := by
  change (∫ u, (‖d.multiplier b k u‖ : ℂ) *
    (‖d.value (d.shell k u)‖ : ℂ) ∂μ) = _
  simp_rw [← Complex.ofReal_mul, ← norm_mul]
  exact integral_complex_ofReal

/-- Absolute summability is established at the level required by Fubini:
the summands are the integrals of the norms of the shell integrands. -/
theorem summable_integral_norm (d : LocalShellData Branch X U)
    (μ : Measure U) [IsFiniteMeasure μ] (hd : LocalWhittakerBounds d)
    (b : Branch) (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re) :
    Summable (fun k : ℤ => ∫ u,
      ‖(d.multiplier b k u * d.value (d.shell k u)) *
        (d.q : ℂ) ^ (-(k : ℂ) * s)‖ ∂μ) := by
  have h := (shell_mellin_summable (absoluteData d) μ
    (absoluteData_bounds d hd) b s hs).norm
  apply h.congr
  intro k
  rw [norm_mul, absolute_coefficient_spec]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun u => norm_nonneg _)]
  simp_rw [norm_mul]
  rw [integral_mul_const]
  rfl

/-- The geometric sum of the pushforwards of unit measure on all valuation
shells.  The corresponding Haar identity has no analytic hypotheses. -/
def shellMeasure [MeasurableSpace X] (d : LocalShellData Branch X U)
    (μ : Measure U) : Measure X :=
  Measure.sum (fun k : ℤ => Measure.map (d.shell k) μ)

/-- Reassembly from genuine unit-shell integrability and raw local estimates.
The identity `hf_shell` just specifies the restriction of the function being
integrated; it asserts neither convergence nor an integral formula. -/
theorem integrable_and_integral_shellMeasure [MeasurableSpace X]
    (d : LocalShellData Branch X U) (μ : Measure U) [IsFiniteMeasure μ]
    (hd : LocalWhittakerBounds d) (hi : ShellIntegrable d μ)
    (hm : ∀ k, AEMeasurable (d.shell k) μ)
    (b : Branch) (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re)
    (f : X → ℂ)
    (hf : ∀ k, AEStronglyMeasurable f (Measure.map (d.shell k) μ))
    (hf_shell : ∀ k u, f (d.shell k u) =
      (d.multiplier b k u * d.value (d.shell k u)) *
        (d.q : ℂ) ^ (-(k : ℂ) * s)) :
    Integrable f (shellMeasure d μ) ∧
      (∫ x, f x ∂shellMeasure d μ) =
        ∑' k : ℤ, coefficient d μ b k * (d.q : ℂ) ^ (-(k : ℂ) * s) := by
  have hlocal (k : ℤ) : Integrable f (Measure.map (d.shell k) μ) := by
    apply (integrable_map_measure (hf k) (hm k)).2
    simpa only [Function.comp_def, hf_shell] using
      (hi b k).mul_const ((d.q : ℂ) ^ (-(k : ℂ) * s))
  have habs : Summable (fun k : ℤ =>
      ∫ x, ‖f x‖ ∂Measure.map (d.shell k) μ) := by
    have h := summable_integral_norm d μ hd b s hs
    apply h.congr
    intro k
    rw [integral_map (hm k) (hf k).norm]
    simp only [hf_shell]
  have hall : Integrable f (shellMeasure d μ) := integrable_sum_measure hlocal habs
  refine ⟨hall, ?_⟩
  rw [shellMeasure, integral_sum_measure hall]
  apply tsum_congr
  intro k
  rw [integral_map (hm k) (hf k)]
  simp only [hf_shell, integral_mul_const, coefficient]

/-- Once multiplicative Haar has been geometrically decomposed into its
unit shells, the local Mellin series is its actual integral. -/
theorem integrable_and_integral_of_haar_shells [MeasurableSpace X]
    (d : LocalShellData Branch X U) (μ : Measure U) [IsFiniteMeasure μ]
    (ν : Measure X) (hν : ν = shellMeasure d μ)
    (hd : LocalWhittakerBounds d) (hi : ShellIntegrable d μ)
    (hm : ∀ k, AEMeasurable (d.shell k) μ)
    (b : Branch) (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re)
    (f : X → ℂ)
    (hf : ∀ k, AEStronglyMeasurable f (Measure.map (d.shell k) μ))
    (hf_shell : ∀ k u, f (d.shell k u) =
      (d.multiplier b k u * d.value (d.shell k u)) *
        (d.q : ℂ) ^ (-(k : ℂ) * s)) :
    Integrable f ν ∧ (∫ x, f x ∂ν) =
      ∑' k : ℤ, coefficient d μ b k * (d.q : ℂ) ^ (-(k : ℂ) * s) := by
  rw [hν]
  exact integrable_and_integral_shellMeasure d μ hd hi hm b s hs f hf hf_shell

end ThetaGlobal.FiniteMellinIntegration

#print axioms ThetaGlobal.FiniteMellinIntegration.summable_integral_norm
#print axioms ThetaGlobal.FiniteMellinIntegration.integrable_and_integral_shellMeasure
end

end Verification_FiniteMellinIntegration
/- END SOURCE BODY: ThetaGlobal/FiniteMellinIntegration.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/FiniteTensorMellin.lean -/
section Verification_FiniteTensorMellin

/-!
# The finite tensor Mellin factor is its actual S-local Haar integral

Local shell reassembly is performed with absolute-integral convergence.
Finite-product Fubini and the proved class-mask tensor expansion then give
the exact finite S-local Mellin integral, with all valuations integrated.
-/

set_option autoImplicit false
noncomputable section
namespace ThetaGlobal.FiniteTensorMellin

open MeasureTheory
open ThetaGlobal.FiniteShell ThetaGlobal.FiniteClass ThetaGlobal.FiniteTensor
open ThetaGlobal.FiniteMellinIntegration
open scoped Classical BigOperators

variable {P : Type*} [Fintype P]
variable {C : P → Type*} [∀ p, Fintype (C p)]
variable {V : Type*} [Group V]
variable {X U : P → Type*} [∀ p, MeasurableSpace (X p)] [∀ p, MeasurableSpace (U p)]

theorem radius_cpow_on_shell {Branch Y Z : Type*}
    (d : LocalShellData Branch Y Z) (k : ℤ) (z : Z) (s : ℂ) :
    (d.radius (d.shell k z) : ℂ) ^ s = (d.q : ℂ) ^ (-(k : ℂ) * s) := by
  rw [d.shell_radius, ← Complex.cpow_mul_ofReal_nonneg (Nat.cast_nonneg _) (-(k : ℝ)) s]
  simp only [Complex.ofReal_neg, Complex.ofReal_intCast, Complex.ofReal_natCast]

variable (B : Set V) (H : V → V → ℂ) (hH : ∀ x y, ‖H x y‖ ≤ 1)
  (assemble : (∀ p, C p) → V) (pivot : P) (classOf : ∀ p, X p → C p)
  (d : ∀ p, LocalShellData PUnit (X p) (U p))
  (μ : ∀ p, Measure (U p)) [∀ p, IsFiniteMeasure (μ p)]
  (ν : ∀ p, Measure (X p)) [∀ p, SigmaFinite (ν p)]
  (L : ∀ p, X p → ℂ)

/-- A separated local factor of the *full* finite Mellin integrand. -/
def localIntegrand (κ : V) (σ : ∀ p, C p) (p : P) (s : ℂ) (x : X p) : ℂ :=
  localMaskFactor pivot (fun c => powerClassMask B H κ (assemble c)) σ p (classOf p x) *
    (L p x * ((d p).value x * ((d p).radius x : ℂ) ^ s))

/-- Fubini is justified by the absolute local shell-integral bounds.
The measure input is the geometric Haar-shell identity and the only
regularity inputs are local measurability and unit-shell integrability. -/
theorem finite_tensor_mellin_integral
    (hd : ∀ p, LocalWhittakerBounds (d p))
    (hν : ∀ p, ν p = shellMeasure (d p) (μ p))
    (hm : ∀ p k, AEMeasurable ((d p).shell k) (μ p))
    (hL : ∀ p k u, (d p).multiplier PUnit.unit k u = L p ((d p).shell k u))
    (hi : ∀ p, ShellIntegrable (withClassMask B H hH assemble pivot classOf p (d p)) (μ p))
    (κ : V) (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re)
    (hf : ∀ σ p k, AEStronglyMeasurable
      (localIntegrand B H assemble pivot classOf d L κ σ p s)
      (Measure.map ((d p).shell k) (μ p))) :
    Integrable (fun x : ∀ p, X p =>
      powerClassMask B H κ (assemble (fun p => classOf p (x p))) *
        ∏ p, L p (x p) * ((d p).value (x p) * ((d p).radius (x p) : ℂ) ^ s))
      (Measure.pi ν) ∧
    (∑ σ : ∀ p, C p, ∏ p, ∑' k : ℤ,
      FiniteShell.coefficient (withClassMask B H hH assemble pivot classOf p (d p))
        (μ p) (κ, σ) k * ((d p).q : ℂ) ^ (-(k : ℂ) * s)) =
      ∫ x : ∀ p, X p,
        powerClassMask B H κ (assemble (fun p => classOf p (x p))) *
          ∏ p, L p (x p) * ((d p).value (x p) * ((d p).radius (x p) : ℂ) ^ s)
        ∂Measure.pi ν := by
  have hlocal (σ : ∀ p, C p) (p : P) :
      Integrable (localIntegrand B H assemble pivot classOf d L κ σ p s) (ν p) ∧
      (∫ x, localIntegrand B H assemble pivot classOf d L κ σ p s x ∂ν p) =
        ∑' k : ℤ, FiniteShell.coefficient
          (withClassMask B H hH assemble pivot classOf p (d p)) (μ p) (κ, σ) k *
            ((d p).q : ℂ) ^ (-(k : ℂ) * s) := by
    apply integrable_and_integral_of_haar_shells
      (withClassMask B H hH assemble pivot classOf p (d p)) (μ p) (ν p) (hν p)
      (withClassMask_bounds B H hH assemble pivot classOf p (d p) (hd p))
      (hi p) (hm p) (κ, σ) s hs _ (hf σ p)
    intro k u
    simp only [localIntegrand, withClassMask, radius_cpow_on_shell, hL, mul_assoc]
  have hlocal' (σ : ∀ p, C p) (p : P) : Integrable
      (fun x => localMaskFactor pivot (fun c => powerClassMask B H κ (assemble c)) σ p
        (classOf p x) * (L p x * ((d p).value x * ((d p).radius x : ℂ) ^ s))) (ν p) :=
    (hlocal σ p).1
  constructor
  · have hint := integrable_finsetSum (Finset.univ : Finset (∀ p, C p))
      (fun σ _ => Integrable.fintype_prod_dep (hlocal' σ))
    apply hint.congr
    apply Filter.Eventually.of_forall
    intro x
    exact tensor_expansion pivot (fun c => powerClassMask B H κ (assemble c))
      (fun p => classOf p (x p))
      (fun p => L p (x p) * ((d p).value (x p) * ((d p).radius (x p) : ℂ) ^ s))
  · calc
      _ = ∑ σ : ∀ p, C p, ∏ p,
          localCoefficient ν pivot (fun c => powerClassMask B H κ (assemble c))
            classOf L (fun p x => (d p).value x * ((d p).radius x : ℂ) ^ s) σ p := by
        apply Finset.sum_congr rfl
        intro σ _
        apply Finset.prod_congr rfl
        intro p _
        exact (hlocal σ p).2.symm
      _ = _ := tensor_shell_integral ν pivot
        (fun c => powerClassMask B H κ (assemble c)) classOf L
        (fun p x => (d p).value x * ((d p).radius x : ℂ) ^ s) hlocal'

end ThetaGlobal.FiniteTensorMellin

#print axioms ThetaGlobal.FiniteTensorMellin.finite_tensor_mellin_integral
end

end Verification_FiniteTensorMellin
/- END SOURCE BODY: ThetaGlobal/FiniteTensorMellin.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/FiniteMellinRatio.lean -/
section Verification_FiniteMellinRatio

/-!
# The same-vector Mellin normalization

Both transforms below retain the actual Fourier coefficient of the same
pure tensor at one.  The direct finite factor is its actual cutoff volume.
The two archimedean constants may differ, including the phase from the
chosen Weyl convention.  The normalization constant is therefore their
explicit ratio, rather than an unrelated nonzero complex number.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.FiniteMellinRatio

open scoped BigOperators

variable {I : Type*} [Fintype I]

theorem ofReal_prod_cpow {J : Type*} (t : Finset J) (a : J → ℝ)
    (ha : ∀ i, 0 ≤ a i) (s : ℂ) :
    ((∏ i ∈ t, a i : ℝ) : ℂ) ^ s = ∏ i ∈ t, (a i : ℂ) ^ s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    rw [Finset.prod_insert hi, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (ha i) (Finset.prod_nonneg (fun j _ => ha j)),
      ih, Finset.prod_insert hi]

def normalization (finiteVolume directConstant reflectedConstant : ℂ) : ℂ :=
  finiteVolume * directConstant / reflectedConstant

theorem normalization_ne_zero
    {finiteVolume directConstant reflectedConstant : ℂ}
    (hv : finiteVolume ≠ 0) (hd : directConstant ≠ 0) (hr : reflectedConstant ≠ 0) :
    normalization finiteVolume directConstant reflectedConstant ≠ 0 :=
  div_ne_zero (mul_ne_zero hv hd) hr

/-- Cancellation of the same actual source scalar and the exact Haar and
local Mellin constants.  No nonvanishing of the gamma factors is needed
for this algebraic identity: division is the field's total division. -/
theorem same_vector_ratio
    (W finiteVolume directConstant reflectedConstant : ℂ)
    (hW : W ≠ 0) (hv : finiteVolume ≠ 0)
    (hd : directConstant ≠ 0) (hr : reflectedConstant ≠ 0)
    (A : ℝ) (hA : 0 < A) (s : ℂ) (finiteFactor : ℂ)
    (numerator denominator : I → ℂ) :
    (W * reflectedConstant * (A : ℂ) ^ s * finiteFactor * ∏ i, numerator i) /
      (W * finiteVolume * directConstant * (A : ℂ) ^ (-s) * ∏ i, denominator i) =
    (normalization finiteVolume directConstant reflectedConstant)⁻¹ *
      (A : ℂ) ^ (2 * s) * finiteFactor * ∏ i, numerator i / denominator i := by
  have hAc : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hAs : (A : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hAc]
    exact Complex.exp_ne_zero _
  rw [Finset.prod_div_distrib, Complex.cpow_neg, two_mul,
    Complex.cpow_add _ _ hAc]
  unfold normalization
  by_cases hg : (∏ i, denominator i) = 0
  · simp only [hg, mul_zero, div_zero, zero_mul]
  · field_simp [hW, hv, hd, hr, hAs, hg]
    <;> ring

/-- A form used when the local gamma pair is stored as two factors. -/
theorem product_pair_quotient
    (n₁ n₂ d₁ d₂ : I → ℂ) :
    (∏ i, (n₁ i * n₂ i) / (d₁ i * d₂ i)) =
      ∏ i, (n₁ i / d₁ i) * (n₂ i / d₂ i) := by
  apply Finset.prod_congr rfl
  intro i _
  exact mul_div_mul_comm _ _ _ _

end ThetaGlobal.FiniteMellinRatio

#print axioms ThetaGlobal.FiniteMellinRatio.same_vector_ratio
end

end Verification_FiniteMellinRatio
/- END SOURCE BODY: ThetaGlobal/FiniteMellinRatio.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/ReflectedAbsoluteCore.lean -/
section Verification_ReflectedAbsoluteCore

/-!
# A coarse absolute-convergence theorem for marked reflected theta sums

This module uses only Mathlib.  A fixed reflected row needs no sharp Euler
majorant: bounded arithmetic coefficients and a quadratic tail for the
kernel suffice, after enlarging the frozen numerator to all integral ideals.
The three ideal variables are kept distinct.  All hypotheses are elementary
local bounds, a kernel bound, or a positive Dirichlet-series majorant; the
conclusion is not among the hypotheses.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.ReflectedAbsolute

open scoped BigOperators

/-- Zero-extended unitary values remain bounded after taking inverse powers.
The assertion `‖z‖ ≤ 1` alone would not justify this step. -/
def ZeroOrUnitNorm (z : ℂ) : Prop := z = 0 ∨ ‖z‖ = 1

theorem ZeroOrUnitNorm.norm_le {z : ℂ} (hz : ZeroOrUnitNorm z) : ‖z‖ ≤ 1 := by
  rcases hz with rfl | hz
  · simp
  · exact hz.le

theorem ZeroOrUnitNorm.one : ZeroOrUnitNorm (1 : ℂ) := Or.inr (by simp)

theorem ZeroOrUnitNorm.zero : ZeroOrUnitNorm (0 : ℂ) := Or.inl rfl

theorem ZeroOrUnitNorm.mul {z w : ℂ} (hz : ZeroOrUnitNorm z)
    (hw : ZeroOrUnitNorm w) : ZeroOrUnitNorm (z * w) := by
  rcases hz with rfl | hz
  · simp [ZeroOrUnitNorm]
  rcases hw with rfl | hw
  · simp [ZeroOrUnitNorm]
  · exact Or.inr (by rw [norm_mul, hz, hw, one_mul])

theorem ZeroOrUnitNorm.inv {z : ℂ} (hz : ZeroOrUnitNorm z) :
    ZeroOrUnitNorm z⁻¹ := by
  rcases hz with rfl | hz
  · simp [ZeroOrUnitNorm]
  · exact Or.inr (by rw [norm_inv, hz, inv_one])

theorem ZeroOrUnitNorm.pow {z : ℂ} (hz : ZeroOrUnitNorm z) (n : ℕ) :
    ZeroOrUnitNorm (z ^ n) := by
  induction n with
  | zero => simpa using ZeroOrUnitNorm.one
  | succ n ih => simpa only [pow_succ] using ih.mul hz

theorem ZeroOrUnitNorm.zpow {z : ℂ} (hz : ZeroOrUnitNorm z) (n : ℤ) :
    ZeroOrUnitNorm (z ^ n) := by
  cases n with
  | ofNat n =>
      change ZeroOrUnitNorm (z ^ (n : ℤ))
      simpa only [zpow_natCast] using hz.pow n
  | negSucc n => simpa only [zpow_negSucc] using (hz.pow (n + 1)).inv

theorem ZeroOrUnitNorm.finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ s, ZeroOrUnitNorm (f i)) :
    ZeroOrUnitNorm (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ZeroOrUnitNorm.one
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem ZeroOrUnitNorm.multiset_prod (s : Multiset ℂ)
    (hs : ∀ z ∈ s, ZeroOrUnitNorm z) : ZeroOrUnitNorm s.prod := by
  induction s using Multiset.induction_on with
  | empty => simpa using ZeroOrUnitNorm.one
  | @cons z s ih =>
    rw [Multiset.prod_cons]
    exact (hs z (Multiset.mem_cons_self z s)).mul
      (ih (fun w hw => hs w (Multiset.mem_cons_of_mem hw)))

/-- The inverse-square ideal weight. -/
def inverseSquare (N : ℝ) : ℝ := (N ^ 2)⁻¹

theorem inverseSquare_nonneg (N : ℝ) : 0 ≤ inverseSquare N := by
  exact inv_nonneg.mpr (sq_nonneg N)

/-- Enlarging the cubic variable to a linear variable is valid since all
integral ideal norms are at least one. -/
theorem cubic_scale_inverse_square_le (a c n t : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hn : 1 ≤ n) (ht : 0 < t) :
    inverseSquare (t * a * c * n ^ 3) ≤
      t⁻¹ ^ 2 * inverseSquare a * inverseSquare c * inverseSquare n := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hn2 : 1 ≤ n ^ 2 := one_le_pow₀ hn
  have hn3 : n ≤ n ^ 3 := by
    calc
      n = n * 1 := by ring
      _ ≤ n * n ^ 2 := mul_le_mul_of_nonneg_left hn2 hn0.le
      _ = n ^ 3 := by ring
  have hlin : 0 < t * a * c * n := by positivity
  have hcub : t * a * c * n ≤ t * a * c * n ^ 3 :=
    mul_le_mul_of_nonneg_left hn3 (by positivity)
  have hsq : (t * a * c * n) ^ 2 ≤ (t * a * c * n ^ 3) ^ 2 :=
    pow_le_pow_left₀ hlin.le hcub 2
  calc
    inverseSquare (t * a * c * n ^ 3) ≤ inverseSquare (t * a * c * n) :=
      inv_le_inv₀ (sq_pos_of_pos (hlin.trans_le hcub)) (sq_pos_of_pos hlin) |>.mpr hsq
    _ = t⁻¹ ^ 2 * inverseSquare a * inverseSquare c * inverseSquare n := by
      simp only [inverseSquare, mul_pow, mul_inv_rev, inv_pow]
      ring

/-- Three independent convergent positive series give the ideal majorant.
No squarefree or coprimality restriction is required after positive extension. -/
theorem summable_triple_inverseSquare {I : Type*} (N : I → ℝ)
    (hN : Summable (fun a => inverseSquare (N a))) :
    Summable (fun x : I × I × I =>
      inverseSquare (N x.1) * inverseSquare (N x.2.1) * inverseSquare (N x.2.2)) := by
  have htwo := hN.mul_of_nonneg hN
    (fun a => inverseSquare_nonneg (N a)) (fun a => inverseSquare_nonneg (N a))
  have hthree := hN.mul_of_nonneg htwo
    (fun a => inverseSquare_nonneg (N a))
    (fun x => mul_nonneg (inverseSquare_nonneg (N x.1))
      (inverseSquare_nonneg (N x.2)))
  simpa only [mul_assoc] using hthree

/-- Generic fixed-row reflected sum.  The encoding retains all discrete
data and is injective; therefore no multiplicity is silently dropped. -/
theorem summable_reflected_of_quadratic_tail
    {B I J C : Type*} [Finite B]
    (N : I → ℝ) (hNpos : ∀ a, 1 ≤ N a)
    (hNsum : Summable (fun a => inverseSquare (N a)))
    (encode : J → B × I × I × I) (hencode : Function.Injective encode)
    (sector : J → C) (scale arithmeticBound : B → ℝ)
    (hscale : ∀ b, 0 < scale b) (hbound : ∀ b, 0 ≤ arithmeticBound b)
    (coefficient : J → ℂ)
    (hcoefficient : ∀ j, ‖coefficient j‖ ≤ arithmeticBound (encode j).1)
    (kernel : C → ℝ → ℂ) (kernelBound : ℝ) (hkernelBound : 0 ≤ kernelBound)
    (hkernel : ∀ c y, 0 < y → ‖kernel c y‖ ≤ kernelBound * inverseSquare y) :
    Summable (fun j => coefficient j * kernel (sector j)
      (scale (encode j).1 * N (encode j).2.1 * N (encode j).2.2.1 *
        N (encode j).2.2.2 ^ 3)) := by
  let branchBound : B → ℝ := fun b => arithmeticBound b * kernelBound * (scale b)⁻¹ ^ 2
  have hb : Summable branchBound := Summable.of_finite
  have hb0 : ∀ b, 0 ≤ branchBound b := by
    intro b
    exact mul_nonneg (mul_nonneg (hbound b) hkernelBound) (sq_nonneg _)
  have hthree := summable_triple_inverseSquare N hNsum
  have hprod := hb.mul_of_nonneg hthree hb0
    (fun x => mul_nonneg
      (mul_nonneg (inverseSquare_nonneg _) (inverseSquare_nonneg _))
      (inverseSquare_nonneg _))
  have hmajor := hprod.comp_injective hencode
  apply Summable.of_norm_bounded hmajor
  intro j
  have ha : 0 < N (encode j).2.1 := lt_of_lt_of_le zero_lt_one (hNpos _)
  have hc : 0 < N (encode j).2.2.1 := lt_of_lt_of_le zero_lt_one (hNpos _)
  have hn : 0 < N (encode j).2.2.2 := lt_of_lt_of_le zero_lt_one (hNpos _)
  have hy : 0 < scale (encode j).1 * N (encode j).2.1 * N (encode j).2.2.1 *
      N (encode j).2.2.2 ^ 3 := by
    exact mul_pos (mul_pos (mul_pos (hscale _) ha) hc) (pow_pos hn _)
  rw [norm_mul]
  calc
    _ ≤ arithmeticBound (encode j).1 *
        (kernelBound * inverseSquare
          (scale (encode j).1 * N (encode j).2.1 * N (encode j).2.2.1 *
            N (encode j).2.2.2 ^ 3)) :=
      mul_le_mul (hcoefficient j) (hkernel _ _ hy) (norm_nonneg _) (hbound _)
    _ ≤ arithmeticBound (encode j).1 * kernelBound *
        ((scale (encode j).1)⁻¹ ^ 2 * inverseSquare (N (encode j).2.1) *
          inverseSquare (N (encode j).2.2.1) * inverseSquare (N (encode j).2.2.2)) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (cubic_scale_inverse_square_le _ _ _ _ ha hc (hNpos _) (hscale _))
        (mul_nonneg (hbound _) hkernelBound)
    _ = _ := by dsimp [branchBound, Function.comp_def]; ring

end ThetaGlobal.ReflectedAbsolute
end

end Verification_ReflectedAbsoluteCore
/- END SOURCE BODY: ThetaGlobal/ReflectedAbsoluteCore.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/ReflectedLocalBounds.lean -/
section Verification_ReflectedLocalBounds

/-!
# Uniform bounds for finite-digit Weyl coefficients

This Mathlib-only module isolates the exact elementary algebra used at an
exterior prime.  Digit weights can be arbitrary fixed complex numbers; their
norms are summed explicitly.  No local Weyl identity is assumed or proved.
The result bounds the finite-sum expression that defines `localWeylScalar`
in the project, uniformly in its nonnegative valuation index.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.ReflectedLocalBounds

open ThetaGlobal.ReflectedAbsolute
open scoped BigOperators

theorem norm_real_inv_le_one {r : ℝ} (hr : 1 ≤ r) : ‖(r : ℂ)⁻¹‖ ≤ 1 := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hr0.le]
  exact (inv_le_one₀ hr0).mpr hr

theorem norm_real_sqrt_inv_le_one {r : ℝ} (hr : 1 ≤ r) :
    ‖(Real.sqrt r : ℂ)⁻¹‖ ≤ 1 := by
  apply norm_real_inv_le_one
  exact (Real.le_sqrt (by norm_num) (le_trans zero_le_one hr)).mpr (by simpa using hr)

def sphericalCoefficient (q : ℝ) (γ : ℂ) (e : ℕ) : ℂ :=
  if e % 3 = 0 then (q : ℂ)⁻¹ ^ (e / 3)
  else if e % 3 = 1 then (q : ℂ)⁻¹ ^ (e / 3) * (Real.sqrt q : ℂ)⁻¹ * γ
  else 0

theorem norm_sphericalCoefficient_le_one {q : ℝ} (hq : 1 ≤ q)
    {γ : ℂ} (hγ : ‖γ‖ = 1) (e : ℕ) : ‖sphericalCoefficient q γ e‖ ≤ 1 := by
  have hp := pow_le_one₀ (n := e / 3) (norm_nonneg ((q : ℂ)⁻¹))
    (norm_real_inv_le_one hq)
  have hs := norm_real_sqrt_inv_le_one hq
  unfold sphericalCoefficient
  split_ifs
  · simpa only [norm_pow] using hp
  · rw [norm_mul, norm_mul, norm_pow, hγ, mul_one]
    exact (mul_le_mul hp hs (norm_nonneg _) zero_le_one).trans (by norm_num)
  · simp

def finiteWeylCoefficient {Ω : Type*} [Fintype Ω]
    (q : ℝ) (γ : ℂ) (digit character phase : Ω → ℂ) (e : ℕ) : ℂ :=
  sphericalCoefficient q γ e *
    ∑ x, digit x * character x ^ 4 * (if e = 0 then phase x else 1)

def finiteWeylBound {Ω : Type*} [Fintype Ω] (digit phase : Ω → ℂ) : ℝ :=
  ∑ x, ‖digit x‖ * (1 + ‖phase x‖)

theorem finiteWeylBound_nonneg {Ω : Type*} [Fintype Ω] (digit phase : Ω → ℂ) :
    0 ≤ finiteWeylBound digit phase := by
  unfold finiteWeylBound
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (norm_nonneg _) (by positivity))

theorem norm_finiteWeylCoefficient_le {Ω : Type*} [Fintype Ω]
    {q : ℝ} (hq : 1 ≤ q) {γ : ℂ} (hγ : ‖γ‖ = 1)
    (digit character phase : Ω → ℂ) (hcharacter : ∀ x, ZeroOrUnitNorm (character x))
    (e : ℕ) :
    ‖finiteWeylCoefficient q γ digit character phase e‖ ≤ finiteWeylBound digit phase := by
  let g : Ω → ℂ := fun x => digit x * character x ^ 4 * (if e = 0 then phase x else 1)
  have hg (x : Ω) : ‖g x‖ ≤ ‖digit x‖ * (1 + ‖phase x‖) := by
    have hchar := ((hcharacter x).pow 4).norm_le
    have hphase : ‖(if e = 0 then phase x else 1)‖ ≤ 1 + ‖phase x‖ := by
      split_ifs
      · linarith [norm_nonneg (phase x)]
      · rw [norm_one]
        exact le_add_of_nonneg_right (norm_nonneg (phase x))
    dsimp only [g]
    rw [norm_mul, norm_mul]
    calc
      _ ≤ (‖digit x‖ * 1) * (1 + ‖phase x‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hchar (norm_nonneg _)) hphase
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  change ‖sphericalCoefficient q γ e * ∑ x, g x‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖∑ x, g x‖ := mul_le_mul_of_nonneg_right
      (norm_sphericalCoefficient_le_one hq hγ e) (norm_nonneg _)
    _ = ‖∑ x, g x‖ := one_mul _
    _ ≤ ∑ x, ‖g x‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun x _ => hg x)

theorem norm_one_sub_real_inverse_le_one {q : ℝ} (hq : 1 ≤ q) :
    ‖1 - (q : ℂ)⁻¹‖ ≤ 1 := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hi : q⁻¹ ≤ 1 := (inv_le_one₀ hq0).mpr hq
  have hid : 1 - (q : ℂ)⁻¹ = ((1 - q⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hid, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hi)]
  exact sub_le_self _ (inv_nonneg.mpr hq0.le)

end ThetaGlobal.ReflectedLocalBounds
end

end Verification_ReflectedLocalBounds
/- END SOURCE BODY: ThetaGlobal/ReflectedLocalBounds.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/ReflectedIdealMajorant.lean -/
section Verification_ReflectedIdealMajorant

/-!
# Actual ideal counting and the reflected triple majorant

The ideal-counting proof below is copied with namespace isolation from the
provided `HeckeGeneral.Analysis.IdealSummability`; the specialization at the
end is new.  This file uses only Mathlib and the newly verified generic core.

The counting asymptotic is Mathlib's proved number-field theorem. In particular,
the convergence majorant is not a supplied analytic hypothesis. The finite-fiber
counting argument follows the calculation in Mathlib's DedekindZeta file.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace ThetaGlobal.ReflectedIdealMajorant

open Filter Ideal NumberField Asymptotics
open scoped Topology nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

/-- The actual number of integral ideals of a given absolute norm. -/
def idealCount (n : ℕ) : ℕ := Nat.card {I : Ideal (𝓞 K) // absNorm I = n}

theorem idealCount_partial_sum_limit :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) / n)
      atTop (𝓝 (NumberField.dedekindZeta_residue K)) := by
  refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
    tendsto_natCast_atTop_atTop).congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  unfold idealCount
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

/-- The ordinary Dirichlet series of ideal counts converges for real part > 1. -/
theorem idealCount_lSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (idealCount K n : ℂ)) s := by
  apply LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n => (idealCount K n : ℝ)) ?_ (fun n => Nat.cast_nonneg _) zero_le_one hs
  exact isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
    (by simpa using idealCount_partial_sum_limit K)

theorem summable_idealCount_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (idealCount K n : ℝ) * (n : ℝ) ^ (-σ)) := by
  have h := (idealCount_lSeriesSummable K (s := (σ : ℂ)) (by simpa using hσ)).norm
  convert h using 1
  funext n
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (by linarith : -σ ≠ 0)]
  · simp [hn, Real.rpow_neg, div_eq_mul_inv]

/-- The Dedekind majorant over actual integral ideals is summable.
The zero ideal contributes zero because σ > 1. -/
theorem summable_ideal_norm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 K) => (absNorm I : ℝ) ^ (-σ)) := by
  classical
  have hfiber (n : ℕ) : Finite {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  have hsum (n : ℕ) :
      (∑' I : {I : Ideal (𝓞 K) // absNorm I = n}, (absNorm I.val : ℝ) ^ (-σ)) =
        (idealCount K n : ℝ) * (n : ℝ) ^ (-σ) := by
    have := hfiber n
    simp_rw [show ∀ I : {I : Ideal (𝓞 K) // absNorm I = n}, absNorm I.val = n
      from fun I => I.property]
    simp [idealCount, tsum_const, nsmul_eq_mul]
  rw [summable_partition (s := fun n : ℕ => {I : Ideal (𝓞 K) | absNorm I = n})
    (fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun I => ⟨absNorm I, rfl, fun _ h => h.symm⟩)]
  constructor
  · intro n
    have : Finite ↑{I : Ideal (𝓞 K) | absNorm I = n} :=
      (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
    exact Summable.of_finite
  · change Summable (fun n => ∑' I : {I : Ideal (𝓞 K) // absNorm I = n},
      (absNorm I.val : ℝ) ^ (-σ))
    simp_rw [hsum]
    exact summable_idealCount_rpow K hσ

/-- Removing the zero ideal gives the majorant used by Hecke ideal series. -/
theorem summable_nonzeroIdeal_norm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : (Ideal (𝓞 K))⁰ => (absNorm I.val : ℝ) ^ (-σ)) :=
  (summable_ideal_norm_rpow K hσ).subtype _


/-- The literal positive norm on nonzero integral ideals. -/
def positiveIdealNorm (I : (Ideal (𝓞 K))⁰) : ℝ := Ideal.absNorm I.val

theorem positiveIdealNorm_ge_one (I : (Ideal (𝓞 K))⁰) :
    1 ≤ positiveIdealNorm K I := by
  change (1 : ℝ) ≤ (Ideal.absNorm I.val : ℝ)
  exact_mod_cast Nat.succ_le_iff.mpr (Ideal.absNorm_pos_of_nonZeroDivisors I)

/-- The ζ_K(2) majorant, proved from Mathlib's number-field ideal counting. -/
theorem summable_positiveIdealNorm_inverseSquare :
    Summable (fun I : (Ideal (𝓞 K))⁰ =>
      ReflectedAbsolute.inverseSquare (positiveIdealNorm K I)) := by
  have hs := summable_nonzeroIdeal_norm_rpow K (σ := 2) (by norm_num)
  apply hs.congr
  intro I
  rw [Real.rpow_neg (Nat.cast_nonneg _) 2, Real.rpow_two]
  rfl

/-- A kernel with quadratic decay gives a convergent triple sum over actual
number-field ideals, with arbitrary finite branches, masks, and unit sectors
encoded injectively.  The only supplied analytic estimate is the kernel tail.
The norm series is proved here; it is not an extra premise. -/
theorem summable_numberField_reflected_of_quadratic_tail
    {B J C : Type*} [Finite B]
    (encode : J → B × (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰)
    (hencode : Function.Injective encode)
    (sector : J → C) (scale arithmeticBound : B → ℝ)
    (hscale : ∀ b, 0 < scale b) (hbound : ∀ b, 0 ≤ arithmeticBound b)
    (coefficient : J → ℂ)
    (hcoefficient : ∀ j, ‖coefficient j‖ ≤ arithmeticBound (encode j).1)
    (kernel : C → ℝ → ℂ) (kernelBound : ℝ) (hkernelBound : 0 ≤ kernelBound)
    (hkernel : ∀ c y, 0 < y →
      ‖kernel c y‖ ≤ kernelBound * ReflectedAbsolute.inverseSquare y) :
    Summable (fun j => coefficient j * kernel (sector j)
      (scale (encode j).1 * positiveIdealNorm K (encode j).2.1 *
        positiveIdealNorm K (encode j).2.2.1 * positiveIdealNorm K (encode j).2.2.2 ^ 3)) :=
  ReflectedAbsolute.summable_reflected_of_quadratic_tail
    (positiveIdealNorm K) (positiveIdealNorm_ge_one K)
    (summable_positiveIdealNorm_inverseSquare K) encode hencode sector scale arithmeticBound
    hscale hbound coefficient hcoefficient kernel kernelBound hkernelBound hkernel

end ThetaGlobal.ReflectedIdealMajorant
end

end Verification_ReflectedIdealMajorant
/- END SOURCE BODY: ThetaGlobal/ReflectedIdealMajorant.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/ReflectedCoefficientModel.lean -/
section Verification_ReflectedCoefficientModel

/-!
# The literal marked reflected scalar coefficient, independent of project vendors

This model retains every multiplication, inverse, zero extension, prime product,
valuation dependence, and normalization of the project's reflectedTerm.
Only the underlying ideal, residue and unit types are abstracted. Its hypotheses
are individual local facts: norm >= 1, zero-or-unit characters, and normalized
prime Gauss norm 1. The Weyl bound is proved from its finite sum, not supplied.

The actual project instantiation is given in ReflectedCoefficientProject.lean.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.ReflectedCoefficientModel

open ThetaGlobal.ReflectedAbsolute ThetaGlobal.ReflectedLocalBounds
open scoped Classical BigOperators

/-- Scalar data obtained from actual generators, residue characters and prime
Gauss sums. No reflected coefficient bound or summability is a field. -/
structure ScalarData (P I A U : Type) where
  normI : I → ℝ
  normI_ge_one : ∀ a, 1 ≤ normI a
  primeNorm : P → ℝ
  primeNorm_ge_one : ∀ p, 1 ≤ primeNorm p
  generator : I → A
  frequencyUnit : U → A
  removePrime : I → P → I
  exponent : I → P → ℕ
  support : I → Finset P
  primeSetIdeal : Finset P → I
  primeCharacter : P → A → ℂ
  primeCharacter_zeroOrUnit : ∀ p a, ZeroOrUnitNorm (primeCharacter p a)
  idealCharacter : I → A → ℂ
  idealCharacter_zeroOrUnit : ∀ a x, ZeroOrUnitNorm (idealCharacter a x)
  period : I → ℂ
  period_zeroOrUnit : ∀ a, ZeroOrUnitNorm (period a)
  gamma : P → ℂ
  gamma_norm : ∀ p, ‖gamma p‖ = 1
  residueUnits : P → Type
  residueFintype : ∀ p, Fintype (residueUnits p)
  residueCharacter : (p : P) → residueUnits p → ℂ
  residueCharacter_zeroOrUnit : ∀ p x, ZeroOrUnitNorm (residueCharacter p x)
  digit : (p : P) → Fin 6 → residueUnits p → ℂ
  inversePhase : (p : P) → residueUnits p → ℂ

variable {P I A U : Type} [CommMonoid A] (D : ScalarData P I A U)

/-- This is the literal nonzero-digit finite sum at the local unit 1. -/
def localWeyl (p : P) (j : Fin 6) (e : ℕ) : ℂ := by
  letI := D.residueFintype p
  exact finiteWeylCoefficient (D.primeNorm p) (D.gamma p)
    (D.digit p j) (D.residueCharacter p) (D.inversePhase p) e

def localWeylBound (p : P) (j : Fin 6) : ℝ := by
  letI := D.residueFintype p
  exact finiteWeylBound (D.digit p j) (D.inversePhase p)

theorem localWeylBound_nonneg (p : P) (j : Fin 6) :
    0 ≤ localWeylBound D p j := by
  letI := D.residueFintype p
  exact finiteWeylBound_nonneg _ _

theorem norm_localWeyl_le (p : P) (j : Fin 6) (e : ℕ) :
    ‖localWeyl D p j e‖ ≤ localWeylBound D p j := by
  letI := D.residueFintype p
  exact norm_finiteWeylCoefficient_le (D.primeNorm_ge_one p) (D.gamma_norm p)
    (D.digit p j) (D.residueCharacter p) (D.inversePhase p)
    (D.residueCharacter_zeroOrUnit p) e

/-- Exactly the project's exponent; in particular e=0 is a distinct case. -/
def localExponent (j : Fin 6) (e : ℕ) : ℕ :=
  if e = 0 then (8 - j.val) % 6 else (4 + 2 * e) % 6

structure Frame (P I : Type) where
  moving : I
  frozenPrimes : Finset P
  marks : Finset P
  rowDigit : P → Fin 6

/-- This unrestricted ambient index contains the actual index injectively.
Deleting restrictions is legitimate for a positive convergence majorant. -/
structure Index (P I U : Type) where
  activeMarks : Finset P
  activeFrozen : Finset P
  numeratorFrozen : I
  n : I
  c : I
  unitSector : U

variable (d : Frame P I) (i : Index P I U)

def activeFrozenIdeal : I := D.primeSetIdeal i.activeFrozen
def activeMarkedIdeal : I := D.primeSetIdeal i.activeMarks

def frozenOmega : ℂ :=
  (Finset.prod (d.frozenPrimes \ i.activeFrozen)
    (fun p => 1 - (D.primeNorm p : ℂ)⁻¹)) *
  (D.period i.numeratorFrozen)⁻¹ * D.period i.n ^ (-3 : ℤ) *
  D.period (activeFrozenIdeal D i) ^ 2 *
  ∏ p ∈ i.activeFrozen,
    let e := D.exponent i.numeratorFrozen p
    localWeyl D p (d.rowDigit p) e *
      (D.primeCharacter p (D.frequencyUnit i.unitSector) *
       D.primeCharacter p (D.generator (D.removePrime i.numeratorFrozen p)) *
       D.primeCharacter p (D.generator i.n) ^ 3 *
       D.primeCharacter p (D.generator (D.removePrime (activeFrozenIdeal D i) p)) ^
         (-2 : ℤ)) ^ localExponent (d.rowDigit p) e

def reflectedRowFactor : ℂ :=
  D.period d.moving ^ 2 *
  (∏ p ∈ D.support d.moving,
    localWeyl D p ⟨1, by decide⟩ 0 *
    (D.primeCharacter p (D.frequencyUnit i.unitSector) *
     D.primeCharacter p (D.generator i.numeratorFrozen) *
     D.primeCharacter p (D.generator (D.removePrime d.moving p)) ^ (-2 : ℤ) *
     D.primeCharacter p (D.generator (activeFrozenIdeal D i)) ^ (-2 : ℤ))) *
  ∏ p ∈ i.activeFrozen, D.primeCharacter p (D.generator d.moving) ^
    (-(2 * localExponent (d.rowDigit p) (D.exponent i.numeratorFrozen p) : ℤ))

def reflectedMarkFactor : ℂ :=
  D.period (activeMarkedIdeal D i) ^ 2 *
  (∏ p ∈ i.activeMarks,
    D.gamma p *
    (D.primeCharacter p (D.frequencyUnit i.unitSector) *
     D.primeCharacter p (D.generator i.numeratorFrozen) *
     D.primeCharacter p (D.generator (D.removePrime (activeMarkedIdeal D i) p)) ^ (-2 : ℤ) *
     D.primeCharacter p (D.generator (activeFrozenIdeal D i)) ^ (-2 : ℤ)) ^ 2) *
  ∏ p ∈ i.activeFrozen,
    D.primeCharacter p (D.generator (activeMarkedIdeal D i)) ^
      (-(2 * localExponent (d.rowDigit p) (D.exponent i.numeratorFrozen p) : ℤ))

def reflectedColumnFactor : ℂ :=
  (D.period i.c)⁻¹ *
  (∏ p ∈ i.activeFrozen, D.primeCharacter p (D.generator i.c) ^
    localExponent (d.rowDigit p) (D.exponent i.numeratorFrozen p)) *
  ∏ p ∈ D.support i.c,
    D.gamma p *
    (D.primeCharacter p (D.frequencyUnit i.unitSector) *
     D.primeCharacter p (D.generator i.numeratorFrozen) *
     D.primeCharacter p (D.generator (D.removePrime i.c p)) *
     D.primeCharacter p (D.generator (activeFrozenIdeal D i)) ^ (-2 : ℤ)) ^ 2

/-- Exactly the scalar prefactor preceding the Mellin kernel in reflectedTerm. -/
def reflectedCoefficient : ℂ :=
  (∏ p ∈ d.marks \ i.activeMarks, (D.primeNorm p : ℂ)⁻¹) *
  (Real.sqrt (D.normI (activeMarkedIdeal D i)) : ℂ)⁻¹ *
  frozenOmega D d i / (D.normI i.n : ℂ) *
  reflectedMarkFactor D d i * reflectedRowFactor D d i *
  reflectedColumnFactor D d i / (Real.sqrt (D.normI i.c) : ℂ) *
  D.idealCharacter d.moving (D.generator i.c * D.generator i.n) ^ 3 *
  D.idealCharacter (activeMarkedIdeal D i) (D.generator i.c) ^ (-2 : ℤ)

def frozenBound (f : Finset P) : ℝ :=
  ∏ p ∈ f, localWeylBound D p (d.rowDigit p)

def rowBound : ℝ :=
  ∏ p ∈ D.support d.moving, localWeylBound D p ⟨1, by decide⟩

theorem frozenBound_nonneg (f : Finset P) : 0 ≤ frozenBound D d f :=
  Finset.prod_nonneg (fun p _ => localWeylBound_nonneg D p _)

theorem rowBound_nonneg : 0 ≤ rowBound D d :=
  Finset.prod_nonneg (fun p _ => localWeylBound_nonneg D p _)

private theorem norm_mul_bound {z w : ℂ} {a b : ℝ}
    (hz : ‖z‖ ≤ a) (hw : ‖w‖ ≤ b) : ‖z * w‖ ≤ a * b := by
  rw [norm_mul]
  exact mul_le_mul hz hw (norm_nonneg _) ((norm_nonneg _).trans hz)

private theorem norm_prod_bound {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (b : ι → ℝ) (h : ∀ j ∈ s, ‖f j‖ ≤ b j) :
    ‖∏ j ∈ s, f j‖ ≤ ∏ j ∈ s, b j := by
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) h

private theorem norm_prod_le_one {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ j ∈ s, ‖f j‖ ≤ 1) : ‖∏ j ∈ s, f j‖ ≤ 1 := by
  simpa using norm_prod_bound s f (fun _ => 1) h

theorem frozenUnitFactor_zeroOrUnit (p : P) :
    ZeroOrUnitNorm
      ((D.primeCharacter p (D.frequencyUnit i.unitSector) *
        D.primeCharacter p (D.generator (D.removePrime i.numeratorFrozen p)) *
        D.primeCharacter p (D.generator i.n) ^ 3 *
        D.primeCharacter p (D.generator (D.removePrime (activeFrozenIdeal D i) p)) ^
          (-2 : ℤ)) ^ localExponent (d.rowDigit p) (D.exponent i.numeratorFrozen p)) :=
  ((((D.primeCharacter_zeroOrUnit p _).mul (D.primeCharacter_zeroOrUnit p _)).mul
    ((D.primeCharacter_zeroOrUnit p _).pow 3)).mul
    ((D.primeCharacter_zeroOrUnit p _).zpow (-2))).pow _

theorem norm_frozenOmega_le :
    ‖frozenOmega D d i‖ ≤ frozenBound D d i.activeFrozen := by
  have hI := norm_prod_le_one (d.frozenPrimes \ i.activeFrozen)
    (fun p => (1 : ℂ) - (D.primeNorm p : ℂ)⁻¹)
    (fun p _ => norm_one_sub_real_inverse_le_one (D.primeNorm_ge_one p))
  have hunit := norm_mul_bound (norm_mul_bound (norm_mul_bound hI
    (D.period_zeroOrUnit i.numeratorFrozen).inv.norm_le)
    ((D.period_zeroOrUnit i.n).zpow (-3)).norm_le)
    ((D.period_zeroOrUnit (activeFrozenIdeal D i)).pow 2).norm_le
  have hprod : ‖∏ p ∈ i.activeFrozen,
      let e := D.exponent i.numeratorFrozen p
      localWeyl D p (d.rowDigit p) e *
        (D.primeCharacter p (D.frequencyUnit i.unitSector) *
         D.primeCharacter p (D.generator (D.removePrime i.numeratorFrozen p)) *
         D.primeCharacter p (D.generator i.n) ^ 3 *
         D.primeCharacter p (D.generator (D.removePrime (activeFrozenIdeal D i) p)) ^
           (-2 : ℤ)) ^ localExponent (d.rowDigit p) e‖ ≤
      frozenBound D d i.activeFrozen := by
    apply norm_prod_bound
    intro p _
    dsimp only
    simpa only [mul_one] using norm_mul_bound (norm_localWeyl_le D p (d.rowDigit p) _)
      (frozenUnitFactor_zeroOrUnit D d i p).norm_le
  simpa only [frozenOmega, one_mul, mul_one] using norm_mul_bound hunit hprod

theorem rowUnitFactor_zeroOrUnit (p : P) :
    ZeroOrUnitNorm
      (D.primeCharacter p (D.frequencyUnit i.unitSector) *
       D.primeCharacter p (D.generator i.numeratorFrozen) *
       D.primeCharacter p (D.generator (D.removePrime d.moving p)) ^ (-2 : ℤ) *
       D.primeCharacter p (D.generator (activeFrozenIdeal D i)) ^ (-2 : ℤ)) :=
  (((D.primeCharacter_zeroOrUnit p _).mul (D.primeCharacter_zeroOrUnit p _)).mul
    ((D.primeCharacter_zeroOrUnit p _).zpow (-2))).mul
    ((D.primeCharacter_zeroOrUnit p _).zpow (-2))

theorem norm_reflectedRowFactor_le :
    ‖reflectedRowFactor D d i‖ ≤ rowBound D d := by
  have hfirst := ((D.period_zeroOrUnit d.moving).pow 2).norm_le
  have hprod : ‖∏ p ∈ D.support d.moving,
      localWeyl D p ⟨1, by decide⟩ 0 *
      (D.primeCharacter p (D.frequencyUnit i.unitSector) *
       D.primeCharacter p (D.generator i.numeratorFrozen) *
       D.primeCharacter p (D.generator (D.removePrime d.moving p)) ^ (-2 : ℤ) *
       D.primeCharacter p (D.generator (activeFrozenIdeal D i)) ^ (-2 : ℤ))‖ ≤
      rowBound D d := by
    apply norm_prod_bound
    intro p _
    simpa only [mul_one] using norm_mul_bound (norm_localWeyl_le D p ⟨1, by decide⟩ 0)
      (rowUnitFactor_zeroOrUnit D d i p).norm_le
  have hlast : ‖∏ p ∈ i.activeFrozen,
      D.primeCharacter p (D.generator d.moving) ^
        (-(2 * localExponent (d.rowDigit p) (D.exponent i.numeratorFrozen p) : ℤ))‖ ≤ 1 := by
    apply norm_prod_le_one
    intro p _
    exact ((D.primeCharacter_zeroOrUnit p _).zpow _).norm_le
  simpa only [reflectedRowFactor, one_mul, mul_one] using
    norm_mul_bound (norm_mul_bound hfirst hprod) hlast

theorem reflectedMarkFactor_zeroOrUnit :
    ZeroOrUnitNorm (reflectedMarkFactor D d i) := by
  unfold reflectedMarkFactor
  apply ZeroOrUnitNorm.mul
  · apply ZeroOrUnitNorm.mul
    · exact (D.period_zeroOrUnit _).pow 2
    · apply ZeroOrUnitNorm.finset_prod
      intro p _
      apply ZeroOrUnitNorm.mul
      · exact Or.inr (D.gamma_norm p)
      · apply ZeroOrUnitNorm.pow
        exact (((D.primeCharacter_zeroOrUnit p _).mul
          (D.primeCharacter_zeroOrUnit p _)).mul
          ((D.primeCharacter_zeroOrUnit p _).zpow (-2))).mul
          ((D.primeCharacter_zeroOrUnit p _).zpow (-2))
  · apply ZeroOrUnitNorm.finset_prod
    intro p _
    exact (D.primeCharacter_zeroOrUnit p _).zpow _

theorem reflectedColumnFactor_zeroOrUnit :
    ZeroOrUnitNorm (reflectedColumnFactor D d i) := by
  unfold reflectedColumnFactor
  apply ZeroOrUnitNorm.mul
  · apply ZeroOrUnitNorm.mul
    · exact (D.period_zeroOrUnit i.c).inv
    · apply ZeroOrUnitNorm.finset_prod
      intro p _
      exact (D.primeCharacter_zeroOrUnit p _).pow _
  · apply ZeroOrUnitNorm.finset_prod
    intro p _
    apply ZeroOrUnitNorm.mul
    · exact Or.inr (D.gamma_norm p)
    · apply ZeroOrUnitNorm.pow
      exact (((D.primeCharacter_zeroOrUnit p _).mul
        (D.primeCharacter_zeroOrUnit p _)).mul
        (D.primeCharacter_zeroOrUnit p _)).mul
        ((D.primeCharacter_zeroOrUnit p _).zpow (-2))

/-- The complete literal arithmetic prefactor is bounded independently of
all three moving ideal variables and the frequency unit. -/
theorem norm_reflectedCoefficient_le :
    ‖reflectedCoefficient D d i‖ ≤ frozenBound D d i.activeFrozen * rowBound D d := by
  have hmark := norm_prod_le_one (d.marks \ i.activeMarks)
    (fun p => (D.primeNorm p : ℂ)⁻¹)
    (fun p _ => norm_real_inv_le_one (D.primeNorm_ge_one p))
  have hsP := norm_real_sqrt_inv_le_one (D.normI_ge_one (activeMarkedIdeal D i))
  have hn := norm_real_inv_le_one (D.normI_ge_one i.n)
  have hc := norm_real_sqrt_inv_le_one (D.normI_ge_one i.c)
  have hmove := ((D.idealCharacter_zeroOrUnit d.moving
    (D.generator i.c * D.generator i.n)).pow 3).norm_le
  have hactive := ((D.idealCharacter_zeroOrUnit (activeMarkedIdeal D i)
    (D.generator i.c)).zpow (-2)).norm_le
  have h := norm_mul_bound (norm_mul_bound (norm_mul_bound (norm_mul_bound
    (norm_mul_bound (norm_mul_bound (norm_mul_bound (norm_mul_bound
      (norm_mul_bound hmark hsP) (norm_frozenOmega_le D d i)) hn)
      (reflectedMarkFactor_zeroOrUnit D d i).norm_le)
      (norm_reflectedRowFactor_le D d i))
      (reflectedColumnFactor_zeroOrUnit D d i).norm_le) hc) hmove) hactive
  simpa only [reflectedCoefficient, div_eq_mul_inv, mul_one, one_mul] using h

end ThetaGlobal.ReflectedCoefficientModel

end

end Verification_ReflectedCoefficientModel
/- END SOURCE BODY: ThetaGlobal/ReflectedCoefficientModel.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/ReflectedCoefficientSummability.lean -/
section Verification_ReflectedCoefficientSummability

/-!
# Marked reflected summability with the full scalar coefficient proved

This closes the standalone convergence theorem. The infinite arithmetic index
retains three independent ideals and all finite mark/frozen/unit choices.
The full scalar coefficient is the literal formula in ReflectedCoefficientModel.
The specialization to nonzero number-field ideals proves its counting input from
Mathlib; neither a global coefficient bound nor summability is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.ReflectedCoefficientSummability

open ThetaGlobal.ReflectedAbsolute ThetaGlobal.ReflectedCoefficientModel
open scoped Classical BigOperators nonZeroDivisors

variable {P I A U : Type} [CommMonoid A] [Finite U]

/-- Keep only the restrictions needed to make the two prime-set choices finite.
Every actual project's reflection index maps into this larger space. -/
abbrev AdmissibleIndex (d : Frame P I) :=
  {i : Index P I U // i.activeMarks ⊆ d.marks ∧ i.activeFrozen ⊆ d.frozenPrimes}

abbrev Branch (d : Frame P I) :=
  {a : Finset P // a ∈ d.marks.powerset} ×
  {f : Finset P // f ∈ d.frozenPrimes.powerset} × U

instance branch_finite (d : Frame P I) : Finite (Branch (U := U) d) := by
  dsimp only [Branch]
  infer_instance

def encode (d : Frame P I) (i : AdmissibleIndex (U := U) d) :
    Branch (U := U) d × I × I × I :=
  ((⟨i.val.activeMarks, Finset.mem_powerset.mpr i.property.1⟩,
    ⟨i.val.activeFrozen, Finset.mem_powerset.mpr i.property.2⟩,
    i.val.unitSector), i.val.numeratorFrozen, i.val.c, i.val.n)

theorem encode_injective (d : Frame P I) :
    Function.Injective (encode (U := U) d) := by
  intro i j h
  apply Subtype.ext
  have hmarks : i.val.activeMarks = j.val.activeMarks := congrArg (fun x => x.1.1.val) h
  have hfrozen : i.val.activeFrozen = j.val.activeFrozen := congrArg (fun x => x.1.2.1.val) h
  have hunit : i.val.unitSector = j.val.unitSector := congrArg (fun x => x.1.2.2) h
  have ha : i.val.numeratorFrozen = j.val.numeratorFrozen := congrArg (fun x => x.2.1) h
  have hc : i.val.c = j.val.c := congrArg (fun x => x.2.2.1) h
  have hn : i.val.n = j.val.n := congrArg (fun x => x.2.2.2) h
  cases i with
  | mk i hi =>
    cases j with
    | mk j hj =>
      cases i
      cases j
      cases hmarks
      cases hfrozen
      cases hunit
      cases ha
      cases hc
      cases hn
      rfl

variable (D : ScalarData P I A U) (d : Frame P I)

def scale (X : ℝ) (b : Branch (U := U) d) : ℝ :=
  X / (D.normI d.moving * D.normI (D.primeSetIdeal b.2.1.val) *
    D.normI (D.primeSetIdeal b.1.val)) ^ 2

theorem scale_pos {X : ℝ} (hX : 0 < X) (b : Branch (U := U) d) :
    0 < scale D d X b := by
  apply div_pos hX
  apply sq_pos_of_pos
  exact mul_pos
    (mul_pos (lt_of_lt_of_le zero_lt_one (D.normI_ge_one _))
      (lt_of_lt_of_le zero_lt_one (D.normI_ge_one _)))
    (lt_of_lt_of_le zero_lt_one (D.normI_ge_one _))

def arithmeticBound (b : Branch (U := U) d) : ℝ :=
  frozenBound D d b.2.1.val * rowBound D d

theorem arithmeticBound_nonneg (b : Branch (U := U) d) :
    0 ≤ arithmeticBound D d b :=
  mul_nonneg (frozenBound_nonneg D d _) (rowBound_nonneg D d)

/-- Exact literal coefficient and the project's three-ideal positive argument. -/
def reflectedTerm {C : Type*} (sector : AdmissibleIndex (U := U) d → C)
    (kernel : C → ℝ → ℂ) (X : ℝ) (i : AdmissibleIndex (U := U) d) : ℂ :=
  reflectedCoefficient D d i.val * kernel (sector i)
    (X * D.normI i.val.numeratorFrozen * D.normI i.val.c * D.normI i.val.n ^ 3 /
      (D.normI d.moving * D.normI (activeFrozenIdeal D i.val) *
        D.normI (activeMarkedIdeal D i.val)) ^ 2)

/-- Generic norm series version. The arithmetic bound is proved from the exact
finite-sum formula and local unit-norm facts, not an extra premise. -/
theorem summable_reflectedTerm {C : Type*}
    (hcount : Summable (fun a => inverseSquare (D.normI a)))
    (sector : AdmissibleIndex (U := U) d → C)
    (kernel : C → ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (htail : ∀ c y, 0 < y → ‖kernel c y‖ ≤ B * inverseSquare y)
    {X : ℝ} (hX : 0 < X) :
    Summable (reflectedTerm D d sector kernel X) := by
  have h := summable_reflected_of_quadratic_tail D.normI D.normI_ge_one hcount
    (encode d) (encode_injective d) sector (scale D d X) (arithmeticBound D d)
    (scale_pos D d hX) (arithmeticBound_nonneg D d)
    (fun i => reflectedCoefficient D d i.val)
    (fun i => norm_reflectedCoefficient_le D d i.val)
    kernel B hB htail
  apply h.congr
  intro i
  unfold reflectedTerm
  congr 1
  congr 1
  simp only [scale, encode, activeFrozenIdeal, activeMarkedIdeal, div_eq_mul_inv]
  ring

/-- Subsets of the ambient index can impose all actual arithmetic masks and
support restrictions without any additional convergence assumption. -/
theorem summable_reflectedTerm_on {C J : Type*}
    (hcount : Summable (fun a => inverseSquare (D.normI a)))
    (embed : J → AdmissibleIndex (U := U) d) (hembed : Function.Injective embed)
    (sector : AdmissibleIndex (U := U) d → C)
    (kernel : C → ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (htail : ∀ c y, 0 < y → ‖kernel c y‖ ≤ B * inverseSquare y)
    {X : ℝ} (hX : 0 < X) :
    Summable (fun j => reflectedTerm D d sector kernel X (embed j)) :=
  (summable_reflectedTerm D d hcount sector kernel B hB htail hX).comp_injective hembed

section NumberField

open NumberField
variable (K : Type) [Field K] [NumberField K]
variable (DK : ScalarData P ((Ideal (𝓞 K))⁰) A U)
variable (dK : Frame P ((Ideal (𝓞 K))⁰))

/-- Actual number-field ideal specialization. The only norm identification is
with the literal absolute ideal norm; Mathlib proves the required ideal sum. -/
theorem summable_numberField_reflectedTerm {C : Type*}
    (hNorm : ∀ a, DK.normI a = ReflectedIdealMajorant.positiveIdealNorm K a)
    (sector : AdmissibleIndex (U := U) dK → C)
    (kernel : C → ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (htail : ∀ c y, 0 < y → ‖kernel c y‖ ≤ B * inverseSquare y)
    {X : ℝ} (hX : 0 < X) :
    Summable (reflectedTerm DK dK sector kernel X) := by
  apply summable_reflectedTerm DK dK _ sector kernel B hB htail hX
  simpa only [hNorm] using ReflectedIdealMajorant.summable_positiveIdealNorm_inverseSquare K

/-- The same fully counted theorem for any subtype of nonzero integral ideals,
in particular ideals prime to the actual finite set S. No extension of residue
characters to ideals meeting S is necessary. -/
theorem summable_numberField_subtype_reflectedTerm
    (Q : (Ideal (𝓞 K))⁰ → Prop)
    (DS : ScalarData P {a : (Ideal (𝓞 K))⁰ // Q a} A U)
    (dS : Frame P {a : (Ideal (𝓞 K))⁰ // Q a}) {C : Type*}
    (hNorm : ∀ a, DS.normI a = ReflectedIdealMajorant.positiveIdealNorm K a.val)
    (sector : AdmissibleIndex (U := U) dS → C)
    (kernel : C → ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (htail : ∀ c y, 0 < y → ‖kernel c y‖ ≤ B * inverseSquare y)
    {X : ℝ} (hX : 0 < X) :
    Summable (reflectedTerm DS dS sector kernel X) := by
  apply summable_reflectedTerm DS dS _ sector kernel B hB htail hX
  simpa only [Function.comp_def, hNorm] using
    (ReflectedIdealMajorant.summable_positiveIdealNorm_inverseSquare K).subtype Q

end NumberField
end ThetaGlobal.ReflectedCoefficientSummability

end

end Verification_ReflectedCoefficientSummability
/- END SOURCE BODY: ThetaGlobal/ReflectedCoefficientSummability.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/ReflectedDominatedLimit.lean -/
section Verification_ReflectedDominatedLimit

/-!
# Uniform domination and regularizer removal for the literal reflected series

The coefficient is proved bounded in ReflectedCoefficientModel and ideal
counting is supplied by Mathlib. A common quadratic kernel tail automatically
produces the summable majorant required by Tannery's theorem. The index keeps
all three ideal variables, every finite branch, and all unit sectors.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.ReflectedDominatedLimit

open Filter
open ThetaGlobal.ReflectedAbsolute ThetaGlobal.ReflectedCoefficientModel
open ThetaGlobal.ReflectedCoefficientSummability
open scoped Classical BigOperators Topology nonZeroDivisors

variable {P I A U : Type} [CommMonoid A] [Finite U]
variable (D : ScalarData P I A U) (d : Frame P I)

def argument (X : ℝ) (i : AdmissibleIndex (U := U) d) : ℝ :=
  X * D.normI i.val.numeratorFrozen * D.normI i.val.c * D.normI i.val.n ^ 3 /
    (D.normI d.moving * D.normI (activeFrozenIdeal D i.val) *
      D.normI (activeMarkedIdeal D i.val)) ^ 2

theorem argument_pos {X : ℝ} (hX : 0 < X) (i : AdmissibleIndex (U := U) d) :
    0 < argument D d X i := by
  have hnorm (a : I) : 0 < D.normI a :=
    lt_of_lt_of_le zero_lt_one (D.normI_ge_one a)
  exact div_pos
    (mul_pos (mul_pos (mul_pos hX (hnorm _)) (hnorm _)) (pow_pos (hnorm _) _))
    (sq_pos_of_pos (mul_pos (mul_pos (hnorm _) (hnorm _)) (hnorm _)))

/-- A summable envelope independent of the regularizer and the sector. -/
def majorant (B X : ℝ) (i : AdmissibleIndex (U := U) d) : ℝ :=
  ‖reflectedCoefficient D d i.val‖ * B * inverseSquare (argument D d X i)

theorem summable_majorant
    (hcount : Summable (fun a => inverseSquare (D.normI a)))
    {B X : ℝ} (hB : 0 ≤ B) (hX : 0 < X) :
    Summable (majorant D d B X) := by
  let k : Unit → ℝ → ℂ := fun _ y => ((B * inverseSquare y : ℝ) : ℂ)
  have hk : ∀ (c : Unit) y, 0 < y → ‖k c y‖ ≤ B * inverseSquare y := by
    intro c y _
    change ‖((B * inverseSquare y : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hB (inverseSquare_nonneg y))]
  have hs := summable_reflectedTerm D d hcount (fun _ => ()) k B hB hk hX
  apply hs.norm.congr
  intro i
  change ‖reflectedCoefficient D d i.val *
      ((B * inverseSquare (argument D d X i) : ℝ) : ℂ)‖ =
    ‖reflectedCoefficient D d i.val‖ * B * inverseSquare (argument D d X i)
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg hB (inverseSquare_nonneg _))]
  ring

theorem norm_reflectedTerm_le_majorant {C : Type*}
    (sector : AdmissibleIndex (U := U) d → C)
    (kernel : C → ℝ → ℂ) {B X : ℝ}
    (htail : ∀ c y, 0 < y → ‖kernel c y‖ ≤ B * inverseSquare y)
    (hX : 0 < X) (i : AdmissibleIndex (U := U) d) :
    ‖reflectedTerm D d sector kernel X i‖ ≤ majorant D d B X i := by
  change ‖reflectedCoefficient D d i.val * kernel (sector i) (argument D d X i)‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ ‖reflectedCoefficient D d i.val‖ *
        (B * inverseSquare (argument D d X i)) :=
      mul_le_mul_of_nonneg_left (htail _ _ (argument_pos D d hX i)) (norm_nonneg _)
    _ = _ := by dsimp only [majorant]; ring

/-- An eventual common quadratic tail suffices for exchanging a regularizer
limit with the full literal reflected series. The limit series is proved
summable as part of the conclusion; its convergence is not a premise. -/
theorem tendsto_tsum_reflectedTerm {T C : Type*} {l : Filter T} [l.NeBot]
    (hcount : Summable (fun a => inverseSquare (D.normI a)))
    (sector : AdmissibleIndex (U := U) d → C)
    (kernel : T → C → ℝ → ℂ) (kernel₀ : C → ℝ → ℂ)
    {B X : ℝ} (hB : 0 ≤ B) (hX : 0 < X)
    (htail : ∀ᶠ n in l, ∀ c y, 0 < y →
      ‖kernel n c y‖ ≤ B * inverseSquare y)
    (hlim : ∀ c y, 0 < y → Tendsto (fun n => kernel n c y) l (𝓝 (kernel₀ c y))) :
    Summable (reflectedTerm D d sector kernel₀ X) ∧
      Tendsto (fun n => ∑' i, reflectedTerm D d sector (kernel n) X i)
        l (𝓝 (∑' i, reflectedTerm D d sector kernel₀ X i)) := by
  have hmajor := summable_majorant D d hcount hB hX
  have hpoint (i : AdmissibleIndex (U := U) d) :
      Tendsto (fun n => reflectedTerm D d sector (kernel n) X i)
        l (𝓝 (reflectedTerm D d sector kernel₀ X i)) := by
    exact tendsto_const_nhds.mul (hlim (sector i) _ (argument_pos D d hX i))
  have hbound : ∀ᶠ n in l, ∀ i,
      ‖reflectedTerm D d sector (kernel n) X i‖ ≤ majorant D d B X i :=
    htail.mono (fun n hn i => norm_reflectedTerm_le_majorant D d sector (kernel n) hn hX i)
  refine ⟨hmajor.of_norm_bounded (fun i => ?_),
    tendsto_tsum_of_dominated_convergence hmajor hpoint hbound⟩
  exact le_of_tendsto (hpoint i).norm (hbound.mono (fun n hn => hn i))

/-- If scalar convolution and fixed-profile unfolding have supplied the
regularized equalities, the only remaining limit step is uniqueness of limits.
This theorem neither assumes nor constructs the automorphic seed identity. -/
theorem equality_of_regularized_equalities {T C : Type*} {l : Filter T} [l.NeBot]
    (hcount : Summable (fun a => inverseSquare (D.normI a)))
    (sector : AdmissibleIndex (U := U) d → C)
    (kernel : T → C → ℝ → ℂ) (kernel₀ : C → ℝ → ℂ)
    {B X : ℝ} (hB : 0 ≤ B) (hX : 0 < X)
    (htail : ∀ᶠ n in l, ∀ c y, 0 < y →
      ‖kernel n c y‖ ≤ B * inverseSquare y)
    (hlim : ∀ c y, 0 < y → Tendsto (fun n => kernel n c y) l (𝓝 (kernel₀ c y)))
    (forward : T → ℂ) (forward₀ : ℂ)
    (hforward : Tendsto forward l (𝓝 forward₀))
    (heq : ∀ᶠ n in l, forward n = ∑' i, reflectedTerm D d sector (kernel n) X i) :
    forward₀ = ∑' i, reflectedTerm D d sector kernel₀ X i := by
  have href := (tendsto_tsum_reflectedTerm D d hcount sector kernel kernel₀
    hB hX htail hlim).2
  exact tendsto_nhds_unique (hforward.congr' heq) href

section NumberField

open NumberField
variable (K : Type) [Field K] [NumberField K]

/-- Actual ideal counting, including any exterior-ideal subtype, discharges
the majorant's last counting premise automatically. -/
theorem tendsto_tsum_numberField_subtype_reflectedTerm
    (Q : (Ideal (𝓞 K))⁰ → Prop)
    (DS : ScalarData P {a : (Ideal (𝓞 K))⁰ // Q a} A U)
    (dS : Frame P {a : (Ideal (𝓞 K))⁰ // Q a})
    (hNorm : ∀ a, DS.normI a = ReflectedIdealMajorant.positiveIdealNorm K a.val)
    {T C : Type*} {l : Filter T} [l.NeBot]
    (sector : AdmissibleIndex (U := U) dS → C)
    (kernel : T → C → ℝ → ℂ) (kernel₀ : C → ℝ → ℂ)
    {B X : ℝ} (hB : 0 ≤ B) (hX : 0 < X)
    (htail : ∀ᶠ n in l, ∀ c y, 0 < y →
      ‖kernel n c y‖ ≤ B * inverseSquare y)
    (hlim : ∀ c y, 0 < y → Tendsto (fun n => kernel n c y) l (𝓝 (kernel₀ c y))) :
    Summable (reflectedTerm DS dS sector kernel₀ X) ∧
      Tendsto (fun n => ∑' i, reflectedTerm DS dS sector (kernel n) X i)
        l (𝓝 (∑' i, reflectedTerm DS dS sector kernel₀ X i)) := by
  apply tendsto_tsum_reflectedTerm DS dS _ sector kernel kernel₀ hB hX htail hlim
  simpa only [Function.comp_def, hNorm] using
    (ReflectedIdealMajorant.summable_positiveIdealNorm_inverseSquare K).subtype Q

end NumberField
end ThetaGlobal.ReflectedDominatedLimit

end

end Verification_ReflectedDominatedLimit
/- END SOURCE BODY: ThetaGlobal/ReflectedDominatedLimit.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/GlobalMarks.lean -/
section Verification_GlobalMarks

/-!
# Finite mark insertion and the global invariance step

This file proves the algebraic and measure-theoretic parts of inserting
whole-index marks.  It does not assume a theta reflection identity.

The hypotheses of `weighted_weyl_average` are rational Weyl invariance
of a function on the group.  The hypotheses of
`angular_constant_term_vanishes` are a measure-preserving rotation,
radial invariance of the constant term, and a nontrivial angular
eigencharacter.  Constructing the required theta function and its
Whittaker expansion is deliberately outside these lemmas.

All powers and masks retain their literal zero values.  In particular,
the zeroth ordinary digit is the unit mask, not a constant character.
-/

noncomputable section
open scoped BigOperators

namespace ThetaGlobal.GlobalMarks

section FiniteAlgebra

variable {P I R : Type*} [CommRing R]

/-- Multiplying finitely many Boolean masks is the mask of their conjunction. -/
theorem prod_boolean_mask (s : Finset P) (p : P → Prop) [DecidablePred p] :
    (∏ q ∈ s, (if p q then (1 : R) else 0)) =
      if ∀ q ∈ s, p q then 1 else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert q s hq ih =>
    by_cases hp : p q
    · simp [Finset.prod_insert hq, ih, hp]
    · simp [Finset.prod_insert hq, hp]

/-- Whole-index divisibility marks are a finite alternating sum of
whole-index nondivisibility masks.  The predicate can literally be
`q.asIdeal ∣ A`, so no squarefree assumption is used here. -/
theorem marks_inclusion_exclusion (s : Finset P) (p : P → Prop)
    [DecidablePred p] :
    (if ∀ q ∈ s, p q then (1 : R) else 0) =
      ∑ t ∈ s.powerset, (-1 : R) ^ t.card *
        (if ∀ q ∈ t, ¬p q then 1 else 0) := by
  classical
  calc
    (if ∀ q ∈ s, p q then (1 : R) else 0) =
        ∏ q ∈ s, (1 - (if ¬p q then (1 : R) else 0)) := by
      rw [← prod_boolean_mask]
      apply Finset.prod_congr rfl
      intro q hq
      by_cases h : p q <;> simp [h]
    _ = ∑ t ∈ s.powerset, (-1 : R) ^ t.card *
        (if ∀ q ∈ t, ¬p q then 1 else 0) := by
      rw [Finset.prod_sub]
      simp only [Finset.prod_const_one, mul_one, prod_boolean_mask]

/-- Pointwise insertion of marks commutes with every other coefficient,
including a whole-index puncture mask. -/
theorem weighted_marks_inclusion_exclusion (s : Finset P) (p : P → Prop)
    [DecidablePred p] (a : R) :
    a * (if ∀ q ∈ s, p q then (1 : R) else 0) =
      ∑ t ∈ s.powerset, (-1 : R) ^ t.card *
        (a * (if ∀ q ∈ t, ¬p q then 1 else 0)) := by
  rw [marks_inclusion_exclusion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  ring

/-- The same formula for any finite collection of arithmetic indices. -/
theorem sum_marked_eq_alternating_unmarked (indices : Finset I)
    (marks : Finset P) (divides : P → I → Prop)
    [∀ q, DecidablePred (divides q)] (a : I → R) :
    (∑ i ∈ indices, a i * (if ∀ q ∈ marks, divides q i then (1 : R) else 0)) =
      ∑ t ∈ marks.powerset, (-1 : R) ^ t.card *
        ∑ i ∈ indices, a i * (if ∀ q ∈ t, ¬divides q i then 1 else 0) := by
  classical
  calc
    _ = ∑ i ∈ indices, ∑ t ∈ marks.powerset, (-1 : R) ^ t.card *
        (a i * (if ∀ q ∈ t, ¬divides q i then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact weighted_marks_inclusion_exclusion marks (fun q => divides q i) (a i)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mul_sum]

/-- The ordinary zeroth digit, written independently of any residue field. -/
def ordinaryZeroDigit (Q : R) (x : I) [Zero I] [DecidableEq I] : R :=
  if x = 0 then 1 - Q else -Q

/-- Uniform marking is delta at zero minus the ordinary zeroth digit.
Here `Q` is the reciprocal residue cardinality. -/
theorem uniformDigit_eq_delta_sub_ordinary (Q : R) (x : I)
    [Zero I] [DecidableEq I] :
    Q = (if x = 0 then (1 : R) else 0) - ordinaryZeroDigit Q x := by
  by_cases hx : x = 0 <;> simp [ordinaryZeroDigit, hx]

/-- Expanding a tensor of digit differences gives exactly one branch for
each active/inactive subset.  This identity is independent of the
choice of the vector on which the digit functional acts. -/
theorem digit_tensor_expansion [DecidableEq P]
    (s : Finset P) (delta ordinary : P → R) :
    (∏ q ∈ s, (delta q - ordinary q)) =
      ∑ t ∈ s.powerset, (-1 : R) ^ t.card *
        (∏ q ∈ s \ t, delta q) * ∏ q ∈ t, ordinary q :=
  Finset.prod_sub delta ordinary s

end FiniteAlgebra

section InfiniteMarks

variable {P I : Type*}

/-- A Boolean restriction of an absolutely summable complex family remains
summable.  This is the convergence justification for all puncture masks. -/
theorem summable_mul_boolean_mask (f : I → ℂ) (hf : Summable f)
    (p : I → Prop) [DecidablePred p] :
    Summable (fun i => f i * (if p i then (1 : ℂ) else 0)) := by
  classical
  convert hf.indicator {i | p i} using 1
  funext i
  by_cases hi : p i <;> simp [Set.indicator, hi]

/-- Inclusion-exclusion for an actual infinite arithmetic sum.  Only the
unmarked coefficient's summability is required, and all new restricted
series are automatically summable by `summable_mul_boolean_mask`. -/
theorem tsum_marked_eq_alternating_unmarked (marks : Finset P)
    (divides : P → I → Prop) [∀ q, DecidablePred (divides q)]
    (a : I → ℂ) (ha : Summable a) :
    (∑' i, a i * (if ∀ q ∈ marks, divides q i then (1 : ℂ) else 0)) =
      ∑ t ∈ marks.powerset, (-1 : ℂ) ^ t.card *
        ∑' i, a i * (if ∀ q ∈ t, ¬divides q i then 1 else 0) := by
  classical
  have hs (t : Finset P) : Summable (fun i => (-1 : ℂ) ^ t.card *
      (a i * (if ∀ q ∈ t, ¬divides q i then 1 else 0))) :=
    (summable_mul_boolean_mask a ha (fun i => ∀ q ∈ t, ¬divides q i)).mul_left _
  calc
    _ = ∑' i, ∑ t ∈ marks.powerset, (-1 : ℂ) ^ t.card *
        (a i * (if ∀ q ∈ t, ¬divides q i then 1 else 0)) := by
      apply tsum_congr
      intro i
      exact weighted_marks_inclusion_exclusion marks (fun q => divides q i) (a i)
    _ = ∑ t ∈ marks.powerset, ∑' i, (-1 : ℂ) ^ t.card *
        (a i * (if ∀ q ∈ t, ¬divides q i then 1 else 0)) :=
      Summable.tsum_finsetSum (fun t ht => hs t)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      exact tsum_mul_left

end InfiniteMarks

section WeylAveraging

variable {G I R : Type*} [Mul G] [CommSemiring R]

/-- A finite digit average inherits rational Weyl invariance term by term.
No Whittaker expansion or reflection conclusion is a hypothesis. -/
theorem weighted_weyl_average (s : Finset I) (theta : G → R) (w : G)
    (hw : ∀ g, theta (w * g) = theta g) (weight : I → R) (arg : I → G) :
    (∑ d ∈ s, weight d * theta (w * arg d)) =
      ∑ d ∈ s, weight d * theta (arg d) := by
  apply Finset.sum_congr rfl
  intro d hd
  rw [hw]

end WeylAveraging

section AngularCancellation

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Integration of a nontrivial angular eigenfunction is zero.  The
integrability hypothesis ensures this is not merely the zero default of
the Bochner integral. -/
theorem integral_eq_zero_of_rotation (e : X ≃ᵐ X)
    (hμ : MeasurePreserving e μ μ) (f : X → ℂ) (_hf : Integrable f μ)
    (ζ : ℂ) (hζ : ζ ≠ 1) (hrot : ∀ x, f (e x) = ζ * f x) :
    ∫ x, f x ∂μ = 0 := by
  have heq : (∫ x, f x ∂μ) = ζ * ∫ x, f x ∂μ := by
    calc
      (∫ x, f x ∂μ) = ∫ x, f (e x) ∂μ := (hμ.integral_comp' f).symm
      _ = ∫ x, ζ * f x ∂μ := by congr 1; funext x; exact hrot x
      _ = ζ * ∫ x, f x ∂μ := integral_const_mul ζ f
  have hz : (1 - ζ) * (∫ x, f x ∂μ) = 0 := by
    calc
      (1 - ζ) * (∫ x, f x ∂μ) = (∫ x, f x ∂μ) - ζ * ∫ x, f x ∂μ := by ring
      _ = 0 := sub_eq_zero.mpr heq
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hζ))

/-- The angular character kills a radial constant term, including any
fixed finite-place or relative-radial weight. -/
theorem angular_constant_term_vanishes (e : X ≃ᵐ X)
    (hμ : MeasurePreserving e μ μ) (weight constantTerm : X → ℂ)
    (hint : Integrable (fun x => weight x * constantTerm x) μ)
    (ζ : ℂ) (hζ : ζ ≠ 1)
    (hweight : ∀ x, weight (e x) = ζ * weight x)
    (hradial : ∀ x, constantTerm (e x) = constantTerm x) :
    ∫ x, weight x * constantTerm x ∂μ = 0 := by
  apply integral_eq_zero_of_rotation μ e hμ _ hint ζ hζ
  intro x
  rw [hweight, hradial, mul_assoc]

end AngularCancellation

end ThetaGlobal.GlobalMarks
end

end Verification_GlobalMarks
/- END SOURCE BODY: ThetaGlobal/GlobalMarks.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/GlobalPhases.lean -/
section Verification_GlobalPhases

/-!
# Zero-extended sextic phase separation

These identities are the five cross-couplings in the proof of the
separated marked expansion.  They explicitly include the zero case;
nonzero character values are sixth roots of unity.  In particular the
row--mark and mark--cube interactions give coprimality masks, rather
than being cancelled to `1` at a zero of the residue symbol.

The file uses only Mathlib.  Instantiation with the project's actual
sextic residue evaluations requires their sixth-root/zero theorem and
the allowed-generator reciprocity theorem.
-/

noncomputable section
open scoped BigOperators Classical

namespace ThetaGlobal.GlobalPhases

variable {R : Type*} [Field R]

/-- The precise range condition of a sextic character extended by zero. -/
def SexticValue (z : R) : Prop := z = 0 ∨ z ^ 6 = 1

/-- The unit/coprimality mask represented by a zero-extended character. -/
def nonzeroMask (z : R) : R := if z = 0 then 0 else 1

theorem sextic_nonzero {z : R} (h : z ^ 6 = 1) : z ≠ 0 := by
  intro hz
  simpa [hz] using h

theorem sextic_zpow_six_periodic {z : R} (h : z ^ 6 = 1) (n : ℤ) :
    z ^ (n + 6) = z ^ n := by
  rw [zpow_add₀ (sextic_nonzero h), show z ^ (6 : ℤ) = 1 by simpa using h,
    mul_one]

theorem sextic_neg_four_eq_two {z : R} (h : z ^ 6 = 1) :
    z ^ (-4 : ℤ) = z ^ 2 := by
  have hp := sextic_zpow_six_periodic h (-4)
  norm_num at hp ⊢
  exact hp.symm

theorem sextic_neg_two_eq_four {z : R} (h : z ^ 6 = 1) :
    z ^ (-2 : ℤ) = z ^ 4 := by
  have hp := sextic_zpow_six_periodic h (-2)
  norm_num at hp ⊢
  exact hp.symm

/-- Row--squarefree-column interaction. -/
theorem row_column_coupling {z : R} (hz : SexticValue z) :
    z * z ^ (-4 : ℤ) = z ^ 3 := by
  rcases hz with rfl | h6
  · simp
  · rw [sextic_neg_four_eq_two h6]
    ring

/-- Row--active-mark interaction, with its zero extension retained. -/
theorem row_mark_coupling {z : R} (hz : SexticValue z) :
    z ^ (-2 : ℤ) * z ^ (-4 : ℤ) = nonzeroMask z := by
  rcases hz with rfl | h6
  · simp [nonzeroMask]
  · rw [sextic_neg_two_eq_four h6, sextic_neg_four_eq_two h6]
    rw [nonzeroMask, if_neg (sextic_nonzero h6)]
    calc
      z ^ 4 * z ^ 2 = z ^ 6 := by ring
      _ = 1 := h6

/-- Active-mark--squarefree-column interaction. -/
theorem mark_column_coupling {z : R} (hz : SexticValue z) :
    z ^ 2 * z ^ (-4 : ℤ) = z ^ (-2 : ℤ) := by
  rcases hz with rfl | h6
  · simp
  · rw [sextic_neg_four_eq_two h6, sextic_neg_two_eq_four h6]
    ring

/-- The cube variable meets an active mark only through this mask. -/
theorem mark_cube_coupling {z : R} (hz : SexticValue z) :
    z ^ 6 = nonzeroMask z := by
  rcases hz with rfl | h6
  · simp [nonzeroMask]
  · simp [nonzeroMask, sextic_nonzero h6, h6]

/-- Reciprocity can be substituted before the row--column simplification. -/
theorem reciprocal_row_column_coupling {x y : R}
    (hx : SexticValue x) (hreciprocity : x = y) :
    x * y ^ (-4 : ℤ) = x ^ 3 := by
  rw [← hreciprocity]
  exact row_column_coupling hx

/-- Simultaneous separation of all the moving kinds.  The variables are
the reciprocal pairings `(d,c)`, `(d,P)`, `(P,c)`, `(d,n)`, `(P,n)`.
There is no cancellation by a possibly zero residue symbol. -/
theorem separated_moving_couplings (dc dP Pc dn Pn : R)
    (hdc : SexticValue dc) (hdP : SexticValue dP)
    (hPc : SexticValue Pc) (hPn : SexticValue Pn) :
    (dc * dc ^ (-4 : ℤ)) * (dP ^ (-2 : ℤ) * dP ^ (-4 : ℤ)) *
        (Pc ^ 2 * Pc ^ (-4 : ℤ)) * dn ^ 3 * Pn ^ 6 =
      (dc * dn) ^ 3 * Pc ^ (-2 : ℤ) * nonzeroMask dP * nonzeroMask Pn := by
  rw [row_column_coupling hdc, row_mark_coupling hdP,
    mark_column_coupling hPc, mark_cube_coupling hPn]
  ring

/-- The same phase reduction after multiplying over any finite prime set. -/
theorem prod_row_column_coupling {P : Type*} (s : Finset P)
    (z : P → R) (hz : ∀ p ∈ s, SexticValue (z p)) :
    (∏ p ∈ s, z p * z p ^ (-4 : ℤ)) = (∏ p ∈ s, z p) ^ 3 := by
  calc
    _ = ∏ p ∈ s, z p ^ 3 := by
      apply Finset.prod_congr rfl
      intro p hp
      exact row_column_coupling (hz p hp)
    _ = _ := Finset.prod_pow s 3 z

end ThetaGlobal.GlobalPhases
end

end Verification_GlobalPhases
/- END SOURCE BODY: ThetaGlobal/GlobalPhases.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/GlobalFrequency.lean -/
section Verification_GlobalFrequency

/-!
# Reflected frequency reconstruction on nonzero support

The full project index deliberately retains coefficients that vanish
locally.  Its map to frequency valuations is therefore not injective.
The explicit one-prime example below has exponent `1` in an inactive
branch and exponent `3 - 2 = 1` in an active branch.  In the latter
branch the ordinary `j = 0, e = 3` local Weyl coefficient vanishes.

On nonzero support, a newly active ordinary `j = 0` prime has numerator
exponent zero, and an active mark also has numerator exponent zero.
These facts make the optional active set exactly the set of negative
valuations.  The mandatory active primes are those of nonzero ordinary
digit.  Once that set is recovered, the squarefree/cube decomposition is
unique.  `supported_valuation_injective` proves this reconstruction.

The model records exterior valuation data only; the separate unit-sector
dictionary with actual rational frequencies remains an arithmetic step.
-/

noncomputable section
open scoped Classical

namespace ThetaGlobal.GlobalFrequency

variable {P : Type*}

structure Branch (P : Type*) where
  active : Set P
  a : P → ℕ
  c : P → ℕ
  n : P → ℕ

theorem Branch.ext {b b' : Branch P} (hactive : b.active = b'.active)
    (ha : b.a = b'.a) (hc : b.c = b'.c) (hn : b.n = b'.n) : b = b' := by
  cases b
  cases b'
  cases hactive
  cases ha
  cases hc
  cases hn
  rfl

/-- The fixed moving-row denominator has been subtracted from both
sides, leaving precisely the active frozen/mark denominator. -/
def valuation (b : Branch P) (p : P) : ℤ :=
  (b.a p : ℤ) + (b.c p : ℤ) + 3 * (b.n p : ℤ) -
    if p ∈ b.active then 2 else 0

/-- The valuation restrictions in the enlarged index before removing
locally zero coefficients. -/
structure RawAdmissible (b : Branch P) : Prop where
  a_outside : ∀ p, p ∉ b.active → b.a p = 0
  c_active : ∀ p, p ∈ b.active → b.c p = 0
  n_active : ∀ p, p ∈ b.active → b.n p = 0
  c_squarefree : ∀ p, b.c p ≤ 1
  a_digits : ∀ p, b.a p % 3 ≠ 2

/-- The extra local zero information required for an injective global
parametrization.  The hypothesis `optional_zero` is a support statement
from the exterior local table, not a global reflection conclusion. -/
structure Supported (mandatory : Set P) (b : Branch P) : Prop
    extends RawAdmissible b where
  mandatory_active : mandatory ⊆ b.active
  optional_zero : ∀ p, p ∈ b.active → p ∉ mandatory → b.a p = 0

theorem active_iff_mandatory_or_negative (mandatory : Set P) (b : Branch P)
    (hb : Supported mandatory b) (p : P) :
    p ∈ b.active ↔ p ∈ mandatory ∨ valuation b p < 0 := by
  constructor
  · intro hp
    by_cases hm : p ∈ mandatory
    · exact Or.inl hm
    · right
      have ha := hb.optional_zero p hp hm
      have hc := hb.c_active p hp
      have hn := hb.n_active p hp
      simp [valuation, hp, ha, hc, hn]
  · rintro (hm | hv)
    · exact hb.mandatory_active hm
    · by_contra hp
      have ha := hb.a_outside p hp
      simp only [valuation, hp, if_false, ha, Nat.cast_zero, zero_add, sub_zero] at hv
      omega

/-- For a fixed active branch, the frozen exponent and the
squarefree/cube exponents are determined by the frequency valuations. -/
theorem fixed_active_coordinates_unique (b b' : Branch P)
    (hb : RawAdmissible b) (hb' : RawAdmissible b')
    (hactive : b.active = b'.active) (hv : valuation b = valuation b') :
    b.a = b'.a ∧ b.c = b'.c ∧ b.n = b'.n := by
  have hpoint (p : P) : b.a p = b'.a p ∧ b.c p = b'.c p ∧ b.n p = b'.n p := by
    have he := congrFun hv p
    by_cases hp : p ∈ b.active
    · have hp' : p ∈ b'.active := hactive ▸ hp
      have hc := hb.c_active p hp
      have hc' := hb'.c_active p hp'
      have hn := hb.n_active p hp
      have hn' := hb'.n_active p hp'
      simp only [valuation, hp, hp', if_true, hc, hc', hn, hn', Nat.cast_zero,
        add_zero, mul_zero] at he
      omega
    · have hp' : p ∉ b'.active := hactive ▸ hp
      have ha := hb.a_outside p hp
      have ha' := hb'.a_outside p hp'
      have hc := hb.c_squarefree p
      have hc' := hb'.c_squarefree p
      simp only [valuation, hp, hp', if_false, ha, ha', Nat.cast_zero,
        zero_add, sub_zero] at he
      omega
  exact ⟨funext (fun p => (hpoint p).1), funext (fun p => (hpoint p).2.1),
    funext (fun p => (hpoint p).2.2)⟩

/-- The whole exterior numerical index is injective after deleting the
local zero branches. -/
theorem supported_valuation_injective (mandatory : Set P)
    (b b' : Branch P) (hb : Supported mandatory b) (hb' : Supported mandatory b')
    (hv : valuation b = valuation b') : b = b' := by
  have hactive : b.active = b'.active := by
    apply Set.ext
    intro p
    rw [active_iff_mandatory_or_negative mandatory b hb,
      active_iff_mandatory_or_negative mandatory b' hb', congrFun hv p]
  obtain ⟨ha, hc, hn⟩ := fixed_active_coordinates_unique b b'
    hb.toRawAdmissible hb'.toRawAdmissible hactive hv
  exact Branch.ext hactive ha hc hn

def inactiveDuplicate : Branch Unit where
  active := ∅
  a := fun _ => 0
  c := fun _ => 1
  n := fun _ => 0

def activeDuplicate : Branch Unit where
  active := Set.univ
  a := fun _ => 3
  c := fun _ => 0
  n := fun _ => 0

theorem inactiveDuplicate_admissible : RawAdmissible inactiveDuplicate where
  a_outside := by intros; rfl
  c_active := by intro p hp; exact False.elim hp
  n_active := by intros; rfl
  c_squarefree := by intro p; change 1 ≤ 1; decide
  a_digits := by intro p; change (0 : ℕ) % 3 ≠ 2; decide

theorem activeDuplicate_admissible : RawAdmissible activeDuplicate where
  a_outside := by intro p hp; exact False.elim (hp (Set.mem_univ p))
  c_active := by intros; rfl
  n_active := by intros; rfl
  c_squarefree := by intro p; change (0 : ℕ) ≤ 1; decide
  a_digits := by intro p; change (3 : ℕ) % 3 ≠ 2; decide

/-- Two distinct raw indices have the same actual integer valuation. -/
theorem duplicate_same_valuation : valuation inactiveDuplicate = valuation activeDuplicate := by
  funext p
  norm_num [valuation, inactiveDuplicate, activeDuplicate]

theorem duplicate_indices_distinct : inactiveDuplicate ≠ activeDuplicate := by
  intro h
  have hs := congrArg Branch.active h
  have he : (Set.univ : Set Unit) = ∅ := hs.symm
  have : (Unit.unit : Unit) ∈ (∅ : Set Unit) := he ▸ Set.mem_univ Unit.unit
  exact this

theorem activeDuplicate_excluded_from_nonzero_support :
    ¬ Supported (∅ : Set Unit) activeDuplicate := by
  intro h
  have he := h.optional_zero Unit.unit (Set.mem_univ _) (by simp)
  norm_num [activeDuplicate] at he

end ThetaGlobal.GlobalFrequency
end

end Verification_GlobalFrequency
/- END SOURCE BODY: ThetaGlobal/GlobalFrequency.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/GlobalFrequencyReconstruction.lean -/
section Verification_GlobalFrequencyReconstruction

/-!
# Surjectivity of the nonzero-support valuation parametrization

This is the converse to `GlobalFrequency.supported_valuation_injective`.
The active set is reconstructed from the mandatory ordinary digits and
the negative valuations.  Outside that set, Euclidean division by three
recovers the squarefree and cube coordinates.  All three supports are
proved finite, so the existing number-field ideal-construction theorem
can be applied to these exponents.

The fixed moving-row denominator is removed before using this model.
The conditions below are precisely local valuation support conditions;
they contain neither a theta identity nor a frequency bijection.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalFrequencyReconstruction

open ThetaGlobal.GlobalFrequency
open scoped Classical

variable {P : Type*}

/-- Local nonzero-support restrictions after removing the fixed row
denominator.  `allowed` is the union of frozen and marked primes. -/
structure LocalSupport (mandatory allowed : Set P) (v : P → ℤ) : Prop where
  mandatory_allowed : mandatory ⊆ allowed
  negative_allowed : ∀ p, v p < 0 → p ∈ allowed
  lower_bound : ∀ p, -2 ≤ v p
  mandatory_digits : ∀ p, p ∈ mandatory → (v p + 2).toNat % 3 ≠ 2
  optional_negative : ∀ p, p ∉ mandatory → v p < 0 → v p = -2
  nonnegative_digits : ∀ p, p ∉ mandatory → 0 ≤ v p → (v p).toNat % 3 ≠ 2

def active (mandatory : Set P) (v : P → ℤ) : Set P :=
  mandatory ∪ {p | v p < 0}

def reconstruct (mandatory : Set P) (v : P → ℤ) : Branch P where
  active := active mandatory v
  a := fun p => if p ∈ active mandatory v then (v p + 2).toNat else 0
  c := fun p => if p ∈ active mandatory v then 0 else (v p).toNat % 3
  n := fun p => if p ∈ active mandatory v then 0 else (v p).toNat / 3

theorem reconstructed_supported (mandatory allowed : Set P) (v : P → ℤ)
    (hv : LocalSupport mandatory allowed v) :
    Supported mandatory (reconstruct mandatory v) := by
  refine {
    a_outside := ?_
    c_active := ?_
    n_active := ?_
    c_squarefree := ?_
    a_digits := ?_
    mandatory_active := ?_
    optional_zero := ?_ }
  · intro p hp
    exact if_neg hp
  · intro p hp
    exact if_pos hp
  · intro p hp
    exact if_pos hp
  · intro p
    by_cases hp : p ∈ active mandatory v
    · simp only [reconstruct, if_pos hp]
      omega
    · have hm : p ∉ mandatory := fun h => hp (Or.inl h)
      have hn : 0 ≤ v p := by
        by_contra h
        exact hp (Or.inr (lt_of_not_ge h))
      have hd := hv.nonnegative_digits p hm hn
      have hr := Nat.mod_lt (v p).toNat (by decide : 0 < 3)
      simp only [reconstruct, if_neg hp]
      omega
  · intro p
    by_cases hp : p ∈ active mandatory v
    · simp only [reconstruct, if_pos hp]
      by_cases hm : p ∈ mandatory
      · exact hv.mandatory_digits p hm
      · have hn : v p < 0 := hp.resolve_left hm
        rw [hv.optional_negative p hm hn]
        decide
    · simp only [reconstruct, if_neg hp]
      decide
  · intro p hp
    exact Or.inl hp
  · intro p hp hm
    change p ∈ active mandatory v at hp
    have hn : v p < 0 := hp.resolve_left hm
    change (if p ∈ active mandatory v then (v p + 2).toNat else 0) = 0
    rw [if_pos hp, hv.optional_negative p hm hn]
    rfl

theorem reconstructed_valuation (mandatory allowed : Set P) (v : P → ℤ)
    (hv : LocalSupport mandatory allowed v) :
    valuation (reconstruct mandatory v) = v := by
  funext p
  change ((if p ∈ active mandatory v then (v p + 2).toNat else 0 : ℕ) : ℤ) +
      ((if p ∈ active mandatory v then 0 else (v p).toNat % 3 : ℕ) : ℤ) +
      3 * ((if p ∈ active mandatory v then 0 else (v p).toNat / 3 : ℕ) : ℤ) -
      (if p ∈ active mandatory v then 2 else 0) = v p
  by_cases hp : p ∈ active mandatory v
  · have hn : 0 ≤ v p + 2 := by have := hv.lower_bound p; omega
    simp only [if_pos hp, Nat.cast_zero, add_zero,
      mul_zero, Int.toNat_of_nonneg hn]
    omega
  · have hn : 0 ≤ v p := by
      by_contra h
      exact hp (Or.inr (lt_of_not_ge h))
    have hc := Int.toNat_of_nonneg hn
    have hdiv := Nat.mod_add_div (v p).toNat 3
    simp only [if_neg hp, Nat.cast_zero, zero_add, sub_zero]
    omega

theorem reconstructed_active_subset (mandatory allowed : Set P) (v : P → ℤ)
    (hv : LocalSupport mandatory allowed v) :
    (reconstruct mandatory v).active ⊆ allowed := by
  intro p hp
  rcases hp with hm | hn
  · exact hv.mandatory_allowed hm
  · exact hv.negative_allowed p hn

/-- The exact finite exponent data needed by
`exterior_ideal_of_exponents`; there is no hidden choice of an ideal. -/
theorem reconstructed_supports_finite (mandatory allowed : Set P) (v : P → ℤ)
    (hv : LocalSupport mandatory allowed v) (hallowed : allowed.Finite)
    (hsupport : (Function.support v).Finite) :
    (reconstruct mandatory v).active.Finite ∧
      {p | (reconstruct mandatory v).a p ≠ 0}.Finite ∧
      {p | (reconstruct mandatory v).c p ≠ 0}.Finite ∧
      {p | (reconstruct mandatory v).n p ≠ 0}.Finite := by
  have ha := hallowed.subset (reconstructed_active_subset mandatory allowed v hv)
  refine ⟨ha, ha.subset ?_, hsupport.subset ?_, hsupport.subset ?_⟩
  · intro p hp
    by_contra hn
    exact hp ((reconstructed_supported mandatory allowed v hv).a_outside p hn)
  · intro p hp
    change v p ≠ 0
    intro hz
    apply hp
    simp [reconstruct, hz]
  · intro p hp
    change v p ≠ 0
    intro hz
    apply hp
    simp [reconstruct, hz]

/-- Existence and uniqueness together: this repairs the overlarge raw
parametrization without discarding legitimate nonzero frequencies. -/
theorem existsUnique_supported_coordinates (mandatory allowed : Set P) (v : P → ℤ)
    (hv : LocalSupport mandatory allowed v) :
    ∃! b : Branch P, Supported mandatory b ∧ valuation b = v := by
  refine ⟨reconstruct mandatory v,
    ⟨reconstructed_supported mandatory allowed v hv,
      reconstructed_valuation mandatory allowed v hv⟩, ?_⟩
  intro b hb
  exact supported_valuation_injective mandatory b (reconstruct mandatory v)
    hb.1 (reconstructed_supported mandatory allowed v hv)
    (hb.2.trans (reconstructed_valuation mandatory allowed v hv).symm)

end ThetaGlobal.GlobalFrequencyReconstruction

#print axioms ThetaGlobal.GlobalFrequencyReconstruction.reconstructed_supports_finite
#print axioms ThetaGlobal.GlobalFrequencyReconstruction.existsUnique_supported_coordinates
end

end Verification_GlobalFrequencyReconstruction
/- END SOURCE BODY: ThetaGlobal/GlobalFrequencyReconstruction.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/GlobalSupportReindex.lean -/
section Verification_GlobalSupportReindex

/-!
# Reindexing with retained zero coefficients

The paper's full index deliberately retains local zero coefficients.
Only the nonzero support must be injective.  This theorem restores all
zero terms after the arithmetic frequency correspondence is proved,
without silently requiring injectivity on the larger raw index.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalSupportReindex

open Function

variable {I J : Type*}

theorem hasSum_iff_of_supported_coordinates (f : I → ℂ) (g : J → ℂ) (ν : J → I)
    (hinj : Set.InjOn ν (support g))
    (hcover : ∀ i, f i ≠ 0 → ∃ j, g j ≠ 0 ∧ ν j = i)
    (hterm : ∀ j, g j ≠ 0 → f (ν j) = g j) (z : ℂ) :
    HasSum f z ↔ HasSum g z := by
  apply hasSum_iff_hasSum_of_ne_zero_bij (fun j : support g => ν j.val)
  · intro j k h
    exact Subtype.ext (hinj j.property k.property h)
  · intro i hi
    obtain ⟨j, hj, he⟩ := hcover i hi
    exact ⟨⟨j, hj⟩, he⟩
  · intro j
    exact hterm j.val j.property

theorem summable_iff_of_supported_coordinates (f : I → ℂ) (g : J → ℂ) (ν : J → I)
    (hinj : Set.InjOn ν (support g))
    (hcover : ∀ i, f i ≠ 0 → ∃ j, g j ≠ 0 ∧ ν j = i)
    (hterm : ∀ j, g j ≠ 0 → f (ν j) = g j) :
    Summable f ↔ Summable g :=
  exists_congr (hasSum_iff_of_supported_coordinates f g ν hinj hcover hterm)

/-- The hypotheses are the pointwise coefficient dictionary and the
arithmetic correspondence on its support, not an equality of sums. -/
theorem tsum_eq_of_supported_coordinates (f : I → ℂ) (g : J → ℂ) (ν : J → I)
    (hinj : Set.InjOn ν (support g))
    (hcover : ∀ i, f i ≠ 0 → ∃ j, g j ≠ 0 ∧ ν j = i)
    (hterm : ∀ j, g j ≠ 0 → f (ν j) = g j) :
    (∑' i, f i) = ∑' j, g j := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun j : support g => ν j.val)
  · intro j k h
    apply Subtype.ext
    exact hinj j.property k.property h
  · intro i hi
    obtain ⟨j, hj, he⟩ := hcover i hi
    exact ⟨⟨j, hj⟩, he⟩
  · intro j
    exact hterm j.val j.property

theorem tsum_norm_eq_of_supported_coordinates (f : I → ℂ) (g : J → ℂ) (ν : J → I)
    (hinj : Set.InjOn ν (support g))
    (hcover : ∀ i, f i ≠ 0 → ∃ j, g j ≠ 0 ∧ ν j = i)
    (hterm : ∀ j, g j ≠ 0 → f (ν j) = g j) :
    (∑' i, ‖f i‖) = ∑' j, ‖g j‖ := by
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun j : support (fun j => ‖g j‖) => ν j.val)
  · intro j k h
    apply Subtype.ext
    exact hinj (by simpa only [mem_support, norm_ne_zero_iff] using j.property)
      (by simpa only [mem_support, norm_ne_zero_iff] using k.property) h
  · intro i hi
    obtain ⟨j, hj, he⟩ := hcover i (by simpa only [mem_support, norm_ne_zero_iff] using hi)
    exact ⟨⟨j, by simpa only [mem_support, norm_ne_zero_iff] using hj⟩, he⟩
  · intro j
    rw [hterm j.val (by simpa only [mem_support, norm_ne_zero_iff] using j.property)]

end ThetaGlobal.GlobalSupportReindex

#print axioms ThetaGlobal.GlobalSupportReindex.tsum_eq_of_supported_coordinates
#print axioms ThetaGlobal.GlobalSupportReindex.tsum_norm_eq_of_supported_coordinates
#print axioms ThetaGlobal.GlobalSupportReindex.summable_iff_of_supported_coordinates
end

end Verification_GlobalSupportReindex
/- END SOURCE BODY: ThetaGlobal/GlobalSupportReindex.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/GlobalEmbedding.lean -/
section Verification_GlobalEmbedding

/-!
# Choosing the complex embedding before the arithmetic context

The KP coefficient embedding sends the chosen sixth root to
`exp (2 * pi * I / 6)`.  An arbitrary complex embedding need not have
this property.  Here the primitive twelfth root is prescribed first,
and the field embedding is chosen to send it to the standard twelfth
root.  Squaring gives exactly the sixth-root convention used by KP.

The existence proof extends a rational embedding through the minimal
polynomial of the prescribed primitive root.  It uses no theta input.
The project adapter makes its one arithmetic choice only after fixing
this embedding, so the same finite set and the same generator context
can subsequently be used by the global source.
-/

noncomputable section

open Polynomial

namespace ThetaGlobal.GlobalEmbedding

def canonicalTwelfthRoot : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 12)

def canonicalSixthRoot : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 6)

theorem canonicalTwelfthRoot_primitive : IsPrimitiveRoot canonicalTwelfthRoot 12 :=
  Complex.isPrimitiveRoot_exp 12 (by norm_num)

theorem canonicalSixthRoot_primitive : IsPrimitiveRoot canonicalSixthRoot 6 :=
  Complex.isPrimitiveRoot_exp 6 (by norm_num)

theorem canonicalTwelfthRoot_sq : canonicalTwelfthRoot ^ 2 = canonicalSixthRoot := by
  unfold canonicalTwelfthRoot canonicalSixthRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

variable {F : Type*} [Field F] [NumberField F]

/-- A prescribed primitive twelfth root can be sent to the canonical
complex root by an embedding of the whole number field. -/
theorem exists_alignedEmbedding (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    ∃ σ : F →+* ℂ, σ ζ = canonicalTwelfthRoot := by
  have hmin : minpoly ℚ ζ = cyclotomic 12 ℚ :=
    (cyclotomic_eq_minpoly_rat hζ (by norm_num)).symm
  have hroot : aeval canonicalTwelfthRoot (minpoly ℚ ζ) = 0 := by
    rw [hmin, aeval_def, eval₂_eq_eval_map, map_cyclotomic,
      ← IsRoot.def, isRoot_cyclotomic_iff]
    exact canonicalTwelfthRoot_primitive
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_adjoin_splits_of_aeval
    (F := ℚ) (E := F) (K := ℂ) (S := Set.univ) (x := ζ)
    (y := canonicalTwelfthRoot)
    (fun s _ => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩)
    (IntermediateField.adjoin_univ ℚ F) hroot
  exact ⟨φ.toRingHom, hφ⟩

/-- Fix this embedding before making the final arithmetic choice. -/
def alignedEmbedding (ζ : F) (hζ : IsPrimitiveRoot ζ 12) : F →+* ℂ :=
  Classical.choose (exists_alignedEmbedding ζ hζ)

@[simp] theorem alignedEmbedding_root12 (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    alignedEmbedding ζ hζ ζ = canonicalTwelfthRoot :=
  Classical.choose_spec (exists_alignedEmbedding ζ hζ)

@[simp] theorem alignedEmbedding_root6 (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    alignedEmbedding ζ hζ (ζ ^ 2) = canonicalSixthRoot := by
  rw [map_pow, alignedEmbedding_root12, canonicalTwelfthRoot_sq]

@[simp] theorem alignedEmbedding_root6_pow (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (i : ℕ) :
    alignedEmbedding ζ hζ ((ζ ^ 2) ^ i) = canonicalSixthRoot ^ i := by
  rw [map_pow, alignedEmbedding_root6]

/-- The compatibility statement is independent of the choice of an
exponent representing the sixth root. -/
theorem alignedEmbedding_of_sixth_power (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (z : F) (i : ℕ) (hi : (ζ ^ 2) ^ i = z) :
    alignedEmbedding ζ hζ z = canonicalSixthRoot ^ i := by
  rw [← hi, alignedEmbedding_root6_pow]

/-- Every sixth root has the exponent required to compare with the KP
coefficient convention. -/
theorem sixthRoot_exponent (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (z : rootsOfUnity 6 F) :
    ∃ i : ℕ, i < 6 ∧ (ζ ^ 2) ^ i = ((z : Fˣ) : F) := by
  have h6 : IsPrimitiveRoot (ζ ^ 2) 6 := hζ.pow (by norm_num) (by norm_num)
  apply h6.eq_pow_of_pow_eq_one
  exact congrArg (fun a : Fˣ => (a : F)) z.property

theorem alignedEmbedding_sixthRoot (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (z : rootsOfUnity 6 F) :
    ∃ i : ℕ, i < 6 ∧
      alignedEmbedding ζ hζ ((z : Fˣ) : F) = canonicalSixthRoot ^ i := by
  obtain ⟨i, hi, hz⟩ := sixthRoot_exponent ζ hζ z
  exact ⟨i, hi, alignedEmbedding_of_sixth_power ζ hζ _ i hz⟩

end ThetaGlobal.GlobalEmbedding
end

end Verification_GlobalEmbedding
/- END SOURCE BODY: ThetaGlobal/GlobalEmbedding.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/GlobalCharacterSums.lean -/
section Verification_GlobalCharacterSums

/-!
# Orthogonality for the optional positive-valuation branch

The ordinary zeroth digit is constant on residue units.  At positive
valuation its additive phase is one.  The remaining character is the
fourth power of an exact-order-six character, whose sum is zero.

These lemmas use only finite character algebra.  The project adapter
derives the exact order from the actual specified-root residue character.
-/

noncomputable section
open scoped BigOperators

namespace ThetaGlobal.GlobalCharacterSums

variable {R C : Type*} [CommMonoid R] [CommRing C] [IsDomain C]

/-- Orthogonality over the unit group, with no zero-extension convention
hidden in the index of summation. -/
theorem sum_units_eq_zero_of_ne_one [Fintype Rˣ]
    (χ : MulChar R C) (hχ : χ ≠ 1) :
    (∑ x : Rˣ, χ (x : R)) = 0 := by
  obtain ⟨b, hb⟩ := MulChar.ne_one_iff.mp hχ
  apply eq_zero_of_mul_eq_self_left hb
  calc
    χ (b : R) * ∑ x : Rˣ, χ (x : R) =
        ∑ x : Rˣ, χ ((b * x : Rˣ) : R) := by
      simp only [Finset.mul_sum, Units.val_mul, map_mul]
    _ = ∑ x : Rˣ, χ (x : R) :=
      Equiv.sum_comp (Equiv.mulLeft b) (fun x : Rˣ => χ (x : R))

theorem fourth_power_ne_one_of_order_six (χ : MulChar R C)
    (hχ : orderOf χ = 6) : χ ^ 4 ≠ 1 := by
  intro h
  have hd := orderOf_dvd_of_pow_eq_one h
  rw [hχ] at hd
  norm_num at hd

theorem sum_fourth_power_units_eq_zero [Fintype Rˣ]
    (χ : MulChar R C) (hχ : orderOf χ = 6) :
    (∑ x : Rˣ, χ (x : R) ^ 4) = 0 := by
  simpa only [MulChar.pow_apply_coe] using
    sum_units_eq_zero_of_ne_one (χ ^ 4) (fourth_power_ne_one_of_order_six χ hχ)

/-- This is the literal positive-valuation zeroth-row exterior sum. -/
theorem ordinary_zero_digit_positive_sum [Fintype Rˣ]
    (χ : MulChar R C) (hχ : orderOf χ = 6) (qinv spherical : C) :
    spherical * (∑ x : Rˣ, (-qinv) * χ (x : R) ^ 4) = 0 := by
  rw [← Finset.mul_sum, sum_fourth_power_units_eq_zero χ hχ, mul_zero, mul_zero]

end ThetaGlobal.GlobalCharacterSums
end

end Verification_GlobalCharacterSums
/- END SOURCE BODY: ThetaGlobal/GlobalCharacterSums.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/GlobalDigitSupport.lean -/
section Verification_GlobalDigitSupport

/-!
# The actual nonzero support of the ordinary positive-valuation digit

At positive valuation the additive phase is one.  The remaining
character sum vanishes for every nonzero ordinary digit except j=4.
In particular a moving-row digit j=1 has only valuation e=0.
This is finite character algebra, independent of theta reflection.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalDigitSupport

open scoped BigOperators

variable {k : Type*} [Field k] [Fintype k] [Fintype kˣ]

theorem character_sixth_power (χ : MulChar k ℂ) (hχ : orderOf χ = 6) (x : kˣ) :
    χ (x : k) ^ 6 = 1 := by
  have h := congrArg (fun c : MulChar k ℂ => c (x : k)) (pow_orderOf_eq_one χ)
  simpa only [hχ, MulChar.pow_apply_coe, MulChar.one_apply_coe] using h

theorem inverse_digit_times_fourth (χ : MulChar k ℂ) (hχ : orderOf χ = 6)
    (j : Fin 6) (x : kˣ) :
    χ (x : k) ^ (-(j.val : ℤ)) * χ (x : k) ^ 4 = χ (x : k) ^ (10 - j.val) := by
  have h6 := character_sixth_power χ hχ x
  have hx : χ (x : k) ≠ 0 := by
    intro hz
    exact zero_ne_one (by
      simpa only [hz, zero_pow (by decide : (6 : ℕ) ≠ 0)] using h6)
  rw [zpow_neg, zpow_natCast, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero j.val hx)]
  rw [← pow_add, Nat.add_sub_of_le (by omega : j.val ≤ 10)]
  calc
    χ (x : k) ^ 4 = χ (x : k) ^ 6 * χ (x : k) ^ 4 := by rw [h6, one_mul]
    _ = χ (x : k) ^ 10 := by rw [← pow_add]

theorem positive_digit_character_ne_one (χ : MulChar k ℂ) (hχ : orderOf χ = 6)
    (j : Fin 6) (hj : j.val ≠ 4) : χ ^ (10 - j.val) ≠ 1 := by
  intro h
  have hd := orderOf_dvd_of_pow_eq_one h
  rw [hχ] at hd
  have hjlt := j.isLt
  omega

theorem ordinary_positive_digit_sum_zero (χ : MulChar k ℂ) (hχ : orderOf χ = 6)
    (j : Fin 6) (hj : j.val ≠ 4) (tauInv spherical : ℂ) :
    spherical * (∑ x : kˣ,
      tauInv * χ (x : k) ^ (-(j.val : ℤ)) * χ (x : k) ^ 4) = 0 := by
  have hs : (∑ x : kˣ, χ (x : k) ^ (10 - j.val)) = 0 := by
    simpa only [MulChar.pow_apply_coe] using
      GlobalCharacterSums.sum_units_eq_zero_of_ne_one (χ ^ (10 - j.val))
        (positive_digit_character_ne_one χ hχ j hj)
  calc
    _ = spherical * (tauInv * ∑ x : kˣ, χ (x : k) ^ (10 - j.val)) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [mul_assoc, inverse_digit_times_fourth χ hχ]
    _ = 0 := by rw [hs, mul_zero, mul_zero]

end ThetaGlobal.GlobalDigitSupport

#print axioms ThetaGlobal.GlobalDigitSupport.ordinary_positive_digit_sum_zero
end

end Verification_GlobalDigitSupport
/- END SOURCE BODY: ThetaGlobal/GlobalDigitSupport.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/GlobalFourierDescent.lean -/
section Verification_GlobalFourierDescent

/-!
# Integrated rational Fourier descent from automorphy

This file proves the global analytic identity before identifying its
Fourier coefficients with the separated ideal coefficients.  The inputs
are a rational Weyl-invariant function, its absolutely convergent
nonzero-frequency Fourier expansions, integrable majorants for exchanging
series and integral, and vanishing integrals of the constant terms.

No seed identity, marked reflection, functional equation, or separated
ideal coefficient formula is an assumption.  For the actual residual
vector, `GlobalCoreSource.lean` supplies automorphy and pointwise Fourier
reconstruction.  Angular cancellation supplies constant-term vanishing.
The remaining local evaluations and frequency reindexing are explicit
separate obligations.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace ThetaGlobal.GlobalFourierDescent

variable {X I J G E : Type*} [MeasurableSpace X]

/-- Termwise integration of a nonzero-frequency Fourier expansion whose
weighted constant term has integral zero.  The absolute integral-norm
sum, not an assertion about the desired theta identity, justifies Fubini. -/
theorem integrated_fourier_of_vanishing_constant [Countable I]
    (μ : Measure X) (weight f constantTerm : X → ℂ) (a : I → X → ℂ)
    (hfourier : ∀ x, HasSum (fun i => a i x) (f x - constantTerm x))
    (ha : ∀ i, Integrable (fun x => weight x * a i x) μ)
    (ha_norm : Summable (fun i => ∫ x, ‖weight x * a i x‖ ∂μ))
    (hf : Integrable (fun x => weight x * f x) μ)
    (hc : Integrable (fun x => weight x * constantTerm x) μ)
    (hc_zero : (∫ x, weight x * constantTerm x ∂μ) = 0) :
    HasSum (fun i => ∫ x, weight x * a i x ∂μ)
      (∫ x, weight x * f x ∂μ) := by
  have hs := hasSum_integral_of_summable_integral_norm ha ha_norm
  have he : (∫ x, (∑' i, weight x * a i x) ∂μ) =
      ∫ x, weight x * f x ∂μ := by
    calc
      _ = ∫ x, (weight x * f x - weight x * constantTerm x) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change (∑' i, weight x * a i x) =
            weight x * f x - weight x * constantTerm x
          rw [((hfourier x).mul_left (weight x)).tsum_eq, mul_sub]
      _ = (∫ x, weight x * f x ∂μ) -
          ∫ x, weight x * constantTerm x ∂μ := integral_sub hf hc
      _ = ∫ x, weight x * f x ∂μ := by rw [hc_zero, sub_zero]
  exact he ▸ hs

/-- Weyl invariance and the two actual Fourier expansions yield an
equality of integrated rational-frequency series. -/
theorem integrated_fourier_weyl [Countable I] [Countable J] [Mul G]
    (μ : Measure X) (weight : X → ℂ) (theta : G → ℂ) (w : G) (g : X → G)
    (hweyl : ∀ z, theta (w * z) = theta z)
    (constant₀ constant₁ : X → ℂ) (a : I → X → ℂ) (b : J → X → ℂ)
    (hfourier₀ : ∀ x, HasSum (fun i => a i x) (theta (g x) - constant₀ x))
    (hfourier₁ : ∀ x, HasSum (fun j => b j x) (theta (w * g x) - constant₁ x))
    (ha : ∀ i, Integrable (fun x => weight x * a i x) μ)
    (ha_norm : Summable (fun i => ∫ x, ‖weight x * a i x‖ ∂μ))
    (hb : ∀ j, Integrable (fun x => weight x * b j x) μ)
    (hb_norm : Summable (fun j => ∫ x, ‖weight x * b j x‖ ∂μ))
    (hθ : Integrable (fun x => weight x * theta (g x)) μ)
    (hc₀ : Integrable (fun x => weight x * constant₀ x) μ)
    (hc₁ : Integrable (fun x => weight x * constant₁ x) μ)
    (hc₀_zero : (∫ x, weight x * constant₀ x ∂μ) = 0)
    (hc₁_zero : (∫ x, weight x * constant₁ x ∂μ) = 0) :
    (∑' i, ∫ x, weight x * a i x ∂μ) =
      ∑' j, ∫ x, weight x * b j x ∂μ := by
  have hfourier₁' : ∀ x,
      HasSum (fun j => b j x) (theta (g x) - constant₁ x) := by
    intro x
    simpa only [hweyl] using hfourier₁ x
  exact
    (integrated_fourier_of_vanishing_constant μ weight (fun x => theta (g x))
      constant₀ a hfourier₀ ha ha_norm hθ hc₀ hc₀_zero).tsum_eq.trans
    (integrated_fourier_of_vanishing_constant μ weight (fun x => theta (g x))
      constant₁ b hfourier₁' hb hb_norm hθ hc₁ hc₁_zero).tsum_eq.symm

/-- Finite digit averages preserve the pointwise nonzero-frequency
Fourier expansion, with their exact averaged constant term. -/
theorem finite_average_fourier_hasSum [Fintype E]
    (coefficient : E → ℂ) (value constantTerm : E → ℂ) (a : E → I → ℂ)
    (hfourier : ∀ d, HasSum (a d) (value d - constantTerm d)) :
    HasSum (fun i => ∑ d, coefficient d * a d i)
      ((∑ d, coefficient d * value d) - ∑ d, coefficient d * constantTerm d) := by
  have hs := hasSum_sum (s := Finset.univ) fun d _ =>
    (hfourier d).mul_left (coefficient d)
  simpa only [mul_sub, Finset.sum_sub_distrib] using hs

/-- The finite digit average can be taken before the rational Fourier
descent.  The hypotheses on integrals concern the actual averaged
coefficient functions, allowing cancellation in the finite average. -/
theorem integrated_finite_average_weyl
    [Countable I] [Countable J] [Fintype E] [Mul G]
    (μ : Measure X) (weight : X → ℂ) (theta : G → ℂ) (w : G)
    (coefficient : E → ℂ) (g : E → X → G)
    (hweyl : ∀ z, theta (w * z) = theta z)
    (constant₀ constant₁ : E → X → ℂ)
    (a : E → I → X → ℂ) (b : E → J → X → ℂ)
    (hfourier₀ : ∀ d x,
      HasSum (fun i => a d i x) (theta (g d x) - constant₀ d x))
    (hfourier₁ : ∀ d x,
      HasSum (fun j => b d j x) (theta (w * g d x) - constant₁ d x))
    (ha : ∀ i, Integrable (fun x => weight x * ∑ d, coefficient d * a d i x) μ)
    (ha_norm : Summable
      (fun i => ∫ x, ‖weight x * ∑ d, coefficient d * a d i x‖ ∂μ))
    (hb : ∀ j, Integrable (fun x => weight x * ∑ d, coefficient d * b d j x) μ)
    (hb_norm : Summable
      (fun j => ∫ x, ‖weight x * ∑ d, coefficient d * b d j x‖ ∂μ))
    (hθ : Integrable (fun x => weight x * ∑ d, coefficient d * theta (g d x)) μ)
    (hc₀ : Integrable (fun x => weight x * ∑ d, coefficient d * constant₀ d x) μ)
    (hc₁ : Integrable (fun x => weight x * ∑ d, coefficient d * constant₁ d x) μ)
    (hc₀_zero : (∫ x, weight x * ∑ d, coefficient d * constant₀ d x ∂μ) = 0)
    (hc₁_zero : (∫ x, weight x * ∑ d, coefficient d * constant₁ d x ∂μ) = 0) :
    (∑' i, ∫ x, weight x * ∑ d, coefficient d * a d i x ∂μ) =
      ∑' j, ∫ x, weight x * ∑ d, coefficient d * b d j x ∂μ := by
  have h₀ (x : X) :
      HasSum (fun i => ∑ d, coefficient d * a d i x)
        ((∑ d, coefficient d * theta (g d x)) -
          ∑ d, coefficient d * constant₀ d x) :=
    finite_average_fourier_hasSum coefficient (fun d => theta (g d x))
      (fun d => constant₀ d x) (fun d i => a d i x) (fun d => hfourier₀ d x)
  have h₁ (x : X) :
      HasSum (fun j => ∑ d, coefficient d * b d j x)
        ((∑ d, coefficient d * theta (g d x)) -
          ∑ d, coefficient d * constant₁ d x) := by
    apply finite_average_fourier_hasSum coefficient (fun d => theta (g d x))
      (fun d => constant₁ d x) (fun d j => b d j x)
    intro d
    simpa only [hweyl] using hfourier₁ d x
  exact
    (integrated_fourier_of_vanishing_constant μ weight
      (fun x => ∑ d, coefficient d * theta (g d x))
      (fun x => ∑ d, coefficient d * constant₀ d x)
      (fun i x => ∑ d, coefficient d * a d i x)
      h₀ ha ha_norm hθ hc₀ hc₀_zero).tsum_eq.trans
    (integrated_fourier_of_vanishing_constant μ weight
      (fun x => ∑ d, coefficient d * theta (g d x))
      (fun x => ∑ d, coefficient d * constant₁ d x)
      (fun j x => ∑ d, coefficient d * b d j x)
      h₁ hb hb_norm hθ hc₁ hc₁_zero).tsum_eq.symm

end ThetaGlobal.GlobalFourierDescent
end

end Verification_GlobalFourierDescent
/- END SOURCE BODY: ThetaGlobal/GlobalFourierDescent.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/GlobalAngular.lean -/
section Verification_GlobalAngular

/-!
# Angular cancellation for every nonzero integer weight

The rotation `exp (pi / k)` detects every nonzero integer weight `k`;
rotation by `-1` alone would only detect odd weights.  Every complex
rotation is a sixth power, so the insertion preserves the finite
sixth-power class and every class mask.

The second section records why a radial constant-term law extends under
right translation and right Lie differentiation.  Applying it to the
actual residual module additionally uses the analytic commutation of
the compact upper-period integral with right differentiation.
-/

noncomputable section

open MeasureTheory

namespace ThetaGlobal.GlobalAngular

def angularRotation (k : ℤ) : Circle := Circle.exp (Real.pi / (k : ℝ))

theorem angularRotation_zpow_ne_one (k : ℤ) (hk : k ≠ 0) :
    angularRotation k ^ k ≠ 1 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have he : (k : ℝ) * (Real.pi / (k : ℝ)) = Real.pi := by
    rw [mul_comm, div_mul_cancel₀ _ hk']
  rw [angularRotation, ← Circle.exp_intCast_mul, he]
  exact Circle.exp_pi_ne_one

theorem angularRotation_coe_zpow_ne_one (k : ℤ) (hk : k ≠ 0) :
    (angularRotation k : ℂ) ^ k ≠ 1 := by
  intro h
  apply angularRotation_zpow_ne_one k hk
  apply Circle.ext
  simpa only [Circle.coe_zpow, Circle.coe_one] using h

theorem exists_circle_sixth_root (z : Circle) : ∃ r : Circle, r ^ 6 = z := by
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  refine ⟨Circle.exp (t / 6), ?_⟩
  rw [← Circle.exp_natCast_mul]
  congr 1
  ring

/-- Any homomorphic insertion of a complex rotation has trivial class
in the quotient by sixth powers. -/
theorem rotation_sixth_class {G : Type*} [CommGroup G]
    (insert : Circle →* G) (z : Circle) :
    (QuotientGroup.mk (insert z) : G ⧸ (powMonoidHom 6 : G →* G).range) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  obtain ⟨r, hr⟩ := exists_circle_sixth_root z
  refine ⟨insert r, ?_⟩
  change (insert r) ^ 6 = insert z
  rw [← map_pow, hr]

/-- An invariant constant term paired with a nontrivial angular weight
has zero integral, for arbitrary positive or negative integer weight. -/
theorem integral_angular_weight_eq_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (rotate : Circle → X ≃ᵐ X)
    (hμ : ∀ z, MeasurePreserving (rotate z) μ μ)
    (weight constantTerm : X → ℂ) (k : ℤ) (hk : k ≠ 0)
    (hint : Integrable (fun x => weight x * constantTerm x) μ)
    (hweight : ∀ z x, weight (rotate z x) = (z : ℂ) ^ k * weight x)
    (hconstant : ∀ z x, constantTerm (rotate z x) = constantTerm x) :
    (∫ x, weight x * constantTerm x ∂μ) = 0 := by
  exact GlobalMarks.angular_constant_term_vanishes μ (rotate (angularRotation k))
    (hμ _) weight constantTerm hint ((angularRotation k : ℂ) ^ k)
    (angularRotation_coe_zpow_ne_one k hk) (hweight _) (hconstant _)

section Covariance

variable {G D : Type*} [Semigroup G]

/-- A left radial/rotation covariance law, viewed as a linear subspace
of all complex-valued functions on the group. -/
def covariantFunctions (a : G) (ρ : ℂ) : Submodule ℂ (G → ℂ) where
  carrier := {f | ∀ g, f (a * g) = ρ * f g}
  zero_mem' := by intro g; simp
  add_mem' := by
    intro f h hf hh g
    change f (a * g) + h (a * g) = ρ * (f g + h g)
    rw [hf, hh, mul_add]
  smul_mem' := by
    intro c f hf g
    change c * f (a * g) = ρ * (c * f g)
    rw [hf]
    ring

theorem rightTranslate_covariant (a r : G) (ρ : ℂ) (f : G → ℂ)
    (hf : f ∈ covariantFunctions a ρ) :
    (fun g => f (g * r)) ∈ covariantFunctions a ρ := by
  intro g
  change f ((a * g) * r) = ρ * f (g * r)
  rw [mul_assoc]
  exact hf _

def rightDerivative (flow : ℝ → G) (f : G → ℂ) (g : G) : ℂ :=
  deriv (fun t => f (g * flow t)) 0

/-- Left covariance commutes with right differentiation.  The theorem
uses Mathlib's derivative convention even when a derivative is zero by
default; its intended application has smooth vectors. -/
theorem rightDerivative_covariant (a : G) (ρ : ℂ) (flow : ℝ → G) (f : G → ℂ)
    (hf : f ∈ covariantFunctions a ρ) :
    rightDerivative flow f ∈ covariantFunctions a ρ := by
  intro g
  have he : (fun t => f ((a * g) * flow t)) =
      (fun t => ρ * f (g * flow t)) := by
    funext t
    rw [mul_assoc]
    exact hf _
  change deriv (fun t => f ((a * g) * flow t)) 0 =
    ρ * deriv (fun t => f (g * flow t)) 0
  rw [he, deriv_const_mul_field]

def rightWord (flow : D → ℝ → G) : List D → (G → ℂ) → G → ℂ
  | [], f => f
  | b :: word, f => rightDerivative (flow b) (rightWord flow word f)

theorem rightWord_covariant (a : G) (ρ : ℂ) (flow : D → ℝ → G) (f : G → ℂ)
    (hf : f ∈ covariantFunctions a ρ) (word : List D) :
    rightWord flow word f ∈ covariantFunctions a ρ := by
  induction word with
  | nil => exact hf
  | cons b word ih => exact rightDerivative_covariant a ρ (flow b) _ ih

/-- Once the upper-period functional is known to commute with the
right-word operations, covariance extends to the whole algebraic span
defining the same residual module. -/
theorem period_covariance_of_mem_span
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (period : V →ₗ[ℂ] (G → ℂ)) (seeds : Set V) (a : G) (ρ : ℂ)
    (hseeds : ∀ v ∈ seeds, period v ∈ covariantFunctions a ρ)
    {v : V} (hv : v ∈ Submodule.span ℂ seeds) :
    period v ∈ covariantFunctions a ρ := by
  have h : Submodule.span ℂ seeds ≤ (covariantFunctions a ρ).comap period :=
    Submodule.span_le.mpr hseeds
  exact h hv

end Covariance

end ThetaGlobal.GlobalAngular
end

end Verification_GlobalAngular
/- END SOURCE BODY: ThetaGlobal/GlobalAngular.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/GlobalCompactPeriod.lean -/
section Verification_GlobalCompactPeriod

/-!
# Differentiating a compact period

For a compact measured quotient, joint continuity of an integrand and
its pointwise derivative supplies the domination required to exchange
one real derivative with the period integral.  No unproved interchange
principle is packaged into the hypotheses: the common bound is obtained
from compactness on a closed interval times the quotient.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace ThetaGlobal.GlobalCompactPeriod

theorem hasDerivAt_integral_of_joint_continuous
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (P P' : ℝ → X → ℂ)
    (hP : Continuous (Function.uncurry P))
    (hP' : Continuous (Function.uncurry P'))
    (hderiv : ∀ t q, HasDerivAt (fun s => P s q) (P' t q) t)
    (t : ℝ) :
    HasDerivAt (fun s => ∫ q, P s q ∂μ) (∫ q, P' t q ∂μ) t := by
  obtain ⟨C, hC⟩ :=
    ((isCompact_Icc : IsCompact (Set.Icc (t - 1) (t + 1))).prod
      (isCompact_univ : IsCompact (Set.univ : Set X))).exists_bound_of_continuousOn
        hP'.continuousOn
  have hi (s : ℝ) : Integrable (P s) μ :=
    (hP.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi' (s : ℝ) : Integrable (P' s) μ :=
    (hP'.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := P) (F' := P')
    (x₀ := t) (s := Set.Icc (t - 1) (t + 1)) (bound := fun _ => C)
    (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun s => (hi s).aestronglyMeasurable)
    (hi t) (hi' t).aestronglyMeasurable
    (Eventually.of_forall fun q s hs => hC (s, q) ⟨hs, Set.mem_univ q⟩)
    (integrable_const C)
    (Eventually.of_forall fun q s _ => hderiv s q)).2

end ThetaGlobal.GlobalCompactPeriod
end

end Verification_GlobalCompactPeriod
/- END SOURCE BODY: ThetaGlobal/GlobalCompactPeriod.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/GlobalAffineJets.lean -/
section Verification_GlobalAffineJets

/-! A local smooth chart may be restricted to an affine linear family
without requiring a globally smooth extension of that chart. -/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalAffineJets

open Set
open scoped ContDiff

variable {E G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem iteratedFDeriv_comp_affine
    (L : E →L[ℝ] G) (a : G) (f : G → H) (s : Set G)
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s)
    (x : E) (hx : a + L x ∈ s) (n : ℕ) :
    iteratedFDeriv ℝ n (fun y => f (a + L y)) x =
      (iteratedFDeriv ℝ n f (a + L x)).compContinuousLinearMap (fun _ => L) := by
  let t : Set G := (fun y : G => a + y) ⁻¹' s
  have ht : IsOpen t := hs.preimage (continuous_const.add continuous_id)
  have hg : ContDiffOn ℝ ∞ (fun y : G => f (a + y)) t :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ h => h)
  have htx : L x ∈ t := hx
  have h := L.iteratedFDerivWithin_comp_right hg ht.uniqueDiffOn
    (ht.preimage L.continuous).uniqueDiffOn htx (i := n) (by simp)
  rw [iteratedFDerivWithin_of_isOpen n (ht.preimage L.continuous) htx,
    iteratedFDerivWithin_of_isOpen n ht htx,
    iteratedFDeriv_comp_add_left] at h
  exact h

end ThetaGlobal.GlobalAffineJets
end

end Verification_GlobalAffineJets
/- END SOURCE BODY: ThetaGlobal/GlobalAffineJets.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/WeightedUnfolding.lean -/
section Verification_WeightedUnfolding

/-!
# Weighted orbit unfolding with the actual change of sheet

The character and class mask are retained inside the integrand.  The
measure-preserving map may be multiplication by a frequency (direct
unfolding) or frequency divided by the sheet variable (reflected unfolding).
The hypotheses concern only the group action, sheet measures, and one
integrable local Whittaker profile.  No theta reflection identity is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.WeightedUnfolding

open MeasureTheory Set
open scoped BigOperators Pointwise

variable {Γ X Y : Type*} [Group Γ] [Countable Γ]
  [MeasurableSpace X] [MeasurableSpace Y] [MulAction Γ X]
  [MeasurableConstSMul Γ X] {μ : Measure X} {ν : Measure Y}
  [SMulInvariantMeasure Γ X μ]

/-- Integral norms of the orbit pieces form a convergent series. -/
theorem orbit_integrals_norm_summable {Ω : Set X}
    (hΩ : IsFundamentalDomain Γ Ω μ) (g : X → ℂ)
    (hg : Integrable g μ) :
    Summable (fun γ : Γ => ∫ x in Ω, ‖g (γ • x)‖ ∂μ) := by
  have hsum : Integrable g (Measure.sum fun γ : Γ => μ.restrict (γ • Ω)) := by
    rw [hΩ.sum_restrict]
    exact hg
  have hs := hsum.summable_integral
  apply hs.congr
  intro γ
  exact (measurePreserving_smul γ μ).setIntegral_image_emb
    (measurableEmbedding_const_smul γ) (fun x => ‖g x‖) Ω

/-- Absolute convergence of the complex orbit-integral series. -/
theorem orbit_integrals_summable {Ω : Set X}
    (hΩ : IsFundamentalDomain Γ Ω μ) (g : X → ℂ)
    (hg : Integrable g μ) :
    Summable (fun γ : Γ => ∫ x in Ω, g (γ • x) ∂μ) := by
  apply Summable.of_norm_bounded (orbit_integrals_norm_summable hΩ g hg)
  intro γ
  exact norm_integral_le_integral_norm _

/-- The exact weighted formula, including absolute convergence.  A finite
power-class indicator can be multiplied into `weight` without any change. -/
theorem weighted_orbit_unfolding {Ω : Set X}
    (hΩ : IsFundamentalDomain Γ Ω μ)
    (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (weight : X → ℂ) (targetWeight : Y → ℂ) (f : Y → ℂ) (c : ℂ)
    (hΓ : ∀ (γ : Γ) (x : X), weight (γ • x) = weight x)
    (htransport : ∀ x, weight x = c * targetWeight (e x))
    (hf : Integrable (fun y => targetWeight y * f y) ν) :
    Summable (fun γ : Γ => ∫ x in Ω, weight x * f (e (γ • x)) ∂μ) ∧
      (∑' γ : Γ, ∫ x in Ω, weight x * f (e (γ • x)) ∂μ) =
        c * ∫ y, targetWeight y * f y ∂ν := by
  let g : X → ℂ := fun x => weight x * f (e x)
  have hg : Integrable g μ := by
    have hi := he.integrable_comp_of_integrable (hf.const_mul c)
    apply hi.congr
    filter_upwards [] with x
    simp only [g, Function.comp_apply, htransport x, mul_assoc]
  have hpiece (γ : Γ) :
      (∫ x in Ω, g (γ • x) ∂μ) =
        ∫ x in Ω, weight x * f (e (γ • x)) ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [g, hΓ]
  constructor
  · exact (orbit_integrals_summable hΩ g hg).congr hpiece
  · calc
      _ = ∑' γ : Γ, ∫ x in Ω, g (γ • x) ∂μ :=
        tsum_congr fun γ => (hpiece γ).symm
      _ = ∫ x, g x ∂μ := (hΩ.integral_eq_tsum'' g hg).symm
      _ = ∫ x, c * (targetWeight (e x) * f (e x)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [g, htransport x, mul_assoc]
      _ = c * ∫ x, targetWeight (e x) * f (e x) ∂μ := integral_const_mul _ _
      _ = c * ∫ y, targetWeight y * f y ∂ν := by
        rw [he.integral_comp' (fun y => targetWeight y * f y)]

/-- Absolute orbit unfolding remains valid after multiplication by a bounded
unitary weight.  This is the estimate needed before signed rearrangement. -/
theorem integrable_weight_mul (w f : Y → ℂ)
    (hw : AEStronglyMeasurable w ν) (hf : Integrable f ν)
    (hw_bound : ∀ᵐ y ∂ν, ‖w y‖ ≤ 1) :
    Integrable (fun y => w y * f y) ν := by
  apply Integrable.mono' hf.norm (hw.mul hf.aestronglyMeasurable)
  filter_upwards [hw_bound] with y hy
  change ‖w y * f y‖ ≤ ‖f y‖
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right hy (norm_nonneg _)).trans_eq (one_mul _)

end ThetaGlobal.WeightedUnfolding

#print axioms ThetaGlobal.WeightedUnfolding.weighted_orbit_unfolding
end

end Verification_WeightedUnfolding
/- END SOURCE BODY: ThetaGlobal/WeightedUnfolding.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/SheetMellin.lean -/
section Verification_SheetMellin

/-!
# Mellin factorization after norm-sheet disintegration

There are two concrete measure changes: the norm-sheet splitting and the
product of local factors. Their measure-preserving assertions are exactly
the Haar/disintegration data already carried by the actual source. The
only function identity assumed is a pointwise finite tensor expansion;
the Mellin integral identity is proved by absolute Fubini.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.SheetMellin

open MeasureTheory
open scoped BigOperators

variable {T X G : Type*} [MeasurableSpace T] [MeasurableSpace X] [MeasurableSpace G]
  {ν : Measure T} {μ : Measure X} {ξ : Measure G} [SigmaFinite ν] [SigmaFinite μ]

def sheetProfile (e : T × X ≃ᵐ G) (W : G → ℂ) (t : T) : ℂ :=
  ∫ x, W (e (t, x)) ∂μ

/-- Integrating a sheet profile against the norm weight is exactly the
weighted group integral. All Fubini steps follow from the displayed L1
condition on the original group, before any factorization is used. -/
theorem sheet_transform_eq_global
    (e : T × X ≃ᵐ G) (he : MeasurePreserving e (ν.prod μ) ξ)
    (normCoordinate : G → T) (hnorm : ∀ z, normCoordinate (e z) = z.1)
    (weight : T → ℂ) (W : G → ℂ)
    (hW : Integrable (fun g => weight (normCoordinate g) * W g) ξ) :
    (∫ t, weight t * sheetProfile (μ := μ) e W t ∂ν) =
      ∫ g, weight (normCoordinate g) * W g ∂ξ := by
  have hi : Integrable (fun z : T × X => weight z.1 * W (e z)) (ν.prod μ) := by
    have h := he.integrable_comp_of_integrable hW
    apply h.congr
    exact Filter.Eventually.of_forall fun z => by simp only [Function.comp_apply, hnorm]
  calc
    _ = ∫ t, ∫ x, weight t * W (e (t, x)) ∂μ ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => (integral_const_mul (weight t) _).symm
    _ = ∫ z : T × X, weight z.1 * W (e z) ∂(ν.prod μ) :=
      (integral_prod _ hi).symm
    _ = ∫ z : T × X, weight (normCoordinate (e z)) * W (e z) ∂(ν.prod μ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change weight z.1 * W (e z) = weight (normCoordinate (e z)) * W (e z)
        rw [hnorm]
    _ = ∫ g, weight (normCoordinate g) * W g ∂ξ :=
      he.integral_comp' (fun g : G => weight (normCoordinate g) * W g)

variable {P J : Type*} [Fintype P] [Fintype J]
  {Y : P → Type*} [∀ p, MeasurableSpace (Y p)]
  (localMeasure : ∀ p, Measure (Y p)) [∀ p, SigmaFinite (localMeasure p)]

/-- A finite sum of local tensor products is globally integrable as soon
as its individual local factors are integrable. -/
theorem finite_tensor_integrable
    (φ : G ≃ᵐ (∀ p, Y p)) (hφ : MeasurePreserving φ ξ (Measure.pi localMeasure))
    (f : J → ∀ p, Y p → ℂ) (hf : ∀ j p, Integrable (f j p) (localMeasure p))
    (W : G → ℂ) (hW : ∀ g, W g = ∑ j, ∏ p, f j p (φ g p)) :
    Integrable W ξ := by
  have hi : Integrable (fun y : ∀ p, Y p => ∑ j, ∏ p, f j p (y p)) (Measure.pi localMeasure) :=
    integrable_finsetSum Finset.univ (fun j _ => Integrable.fintype_prod_dep (hf j))
  apply (hφ.integrable_comp_of_integrable hi).congr
  exact Filter.Eventually.of_forall fun g => (hW g).symm

theorem finite_tensor_integral
    (φ : G ≃ᵐ (∀ p, Y p)) (hφ : MeasurePreserving φ ξ (Measure.pi localMeasure))
    (f : J → ∀ p, Y p → ℂ) (hf : ∀ j p, Integrable (f j p) (localMeasure p))
    (W : G → ℂ) (hW : ∀ g, W g = ∑ j, ∏ p, f j p (φ g p)) :
    (∫ g, W g ∂ξ) = ∑ j, ∏ p, ∫ y, f j p y ∂localMeasure p := by
  calc
    _ = ∫ g, ∑ j, ∏ p, f j p (φ g p) ∂ξ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hW
    _ = ∫ y : ∀ p, Y p, ∑ j, ∏ p, f j p (y p) ∂Measure.pi localMeasure :=
      hφ.integral_comp' (fun y : ∀ p, Y p => ∑ j, ∏ p, f j p (y p))
    _ = ∑ j, ∫ y : ∀ p, Y p, ∏ p, f j p (y p) ∂Measure.pi localMeasure :=
      integral_finsetSum _ (fun j _ => Integrable.fintype_prod_dep (hf j))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact integral_fintype_prod_eq_prod (f j)

/-- The full sheet Mellin factorization. In the intended application
`weight t = t^s`, `f` contains the local period, norm power, class indicator
and Whittaker value, and the tensor index includes the finite class split. -/
theorem sheet_mellin_factorization
    (e : T × X ≃ᵐ G) (he : MeasurePreserving e (ν.prod μ) ξ)
    (normCoordinate : G → T) (hnorm : ∀ z, normCoordinate (e z) = z.1)
    (φ : G ≃ᵐ (∀ p, Y p)) (hφ : MeasurePreserving φ ξ (Measure.pi localMeasure))
    (weight : T → ℂ) (W : G → ℂ)
    (f : J → ∀ p, Y p → ℂ) (hf : ∀ j p, Integrable (f j p) (localMeasure p))
    (hpoint : ∀ g, weight (normCoordinate g) * W g =
      ∑ j, ∏ p, f j p (φ g p)) :
    (∫ t, weight t * sheetProfile (μ := μ) e W t ∂ν) =
      ∑ j, ∏ p, ∫ y, f j p y ∂localMeasure p := by
  have hi := finite_tensor_integrable localMeasure φ hφ f hf
    (fun g => weight (normCoordinate g) * W g) hpoint
  rw [sheet_transform_eq_global e he normCoordinate hnorm weight W hi]
  exact finite_tensor_integral localMeasure φ hφ f hf _ hpoint

end ThetaGlobal.SheetMellin

#print axioms ThetaGlobal.SheetMellin.sheet_mellin_factorization
end

end Verification_SheetMellin
/- END SOURCE BODY: ThetaGlobal/SheetMellin.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/GaussianRegularization.lean -/
section Verification_GaussianRegularization

/-!
# Gaussian regularization on a vertical Mellin line

The literal multiplier is `exp (ε * (σ + i t)^2)`.  Its uniform bound is
`exp (σ^2)` for `0 ≤ ε ≤ 1`, and it tends to one as `ε → 0`.  Hence every
absolutely integrable vertical Mellin kernel passes to the unregularized
limit by dominated convergence.  This is independent of any theta identity.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GaussianRegularization

open MeasureTheory Filter
open scoped Topology

def verticalGaussian (ε σ t : ℝ) : ℂ :=
  Complex.exp ((ε : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ 2)

theorem verticalGaussian_norm (ε σ t : ℝ) :
    ‖verticalGaussian ε σ t‖ = Real.exp (ε * (σ ^ 2 - t ^ 2)) := by
  rw [verticalGaussian, Complex.norm_exp]
  congr 1
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

theorem verticalGaussian_norm_le {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (σ t : ℝ) :
    ‖verticalGaussian ε σ t‖ ≤ Real.exp (σ ^ 2) := by
  rw [verticalGaussian_norm]
  apply Real.exp_le_exp.mpr
  calc
    ε * (σ ^ 2 - t ^ 2) ≤ ε * σ ^ 2 :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) hε₀
    _ ≤ 1 * σ ^ 2 := mul_le_mul_of_nonneg_right hε₁ (sq_nonneg _)
    _ = σ ^ 2 := one_mul _

theorem verticalGaussian_continuous (ε σ : ℝ) :
    Continuous (verticalGaussian ε σ) := by
  unfold verticalGaussian
  fun_prop

theorem verticalGaussian_tendsto {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (σ t : ℝ) :
    Tendsto (fun n => verticalGaussian (ε n) σ t) atTop (𝓝 1) := by
  have hr := ((Complex.continuous_ofReal.tendsto 0).comp hε).mul_const
    (((σ : ℂ) + (t : ℂ) * Complex.I) ^ 2)
  have he := Complex.continuous_exp.continuousAt.tendsto.comp hr
  simpa only [Function.comp_def, verticalGaussian, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero] using he

theorem regularized_integrable (g : ℝ → ℂ) (hg : Integrable g)
    {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (σ : ℝ) :
    Integrable (fun t => g t * verticalGaussian ε σ t) := by
  apply Integrable.mono' (hg.norm.const_mul (Real.exp (σ ^ 2)))
    (hg.aestronglyMeasurable.mul (verticalGaussian_continuous ε σ).aestronglyMeasurable)
  filter_upwards [] with t
  change ‖g t * verticalGaussian ε σ t‖ ≤ Real.exp (σ ^ 2) * ‖g t‖
  rw [norm_mul]
  calc
    ‖g t‖ * ‖verticalGaussian ε σ t‖ ≤ ‖g t‖ * Real.exp (σ ^ 2) :=
      mul_le_mul_of_nonneg_left (verticalGaussian_norm_le hε₀ hε₁ σ t) (norm_nonneg _)
    _ = Real.exp (σ ^ 2) * ‖g t‖ := mul_comm _ _

theorem regularized_integral_tendsto (g : ℝ → ℂ) (hg : Integrable g)
    (ε : ℕ → ℝ) (hε₀ : ∀ n, 0 ≤ ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0)) (σ : ℝ) :
    Tendsto (fun n => ∫ t, g t * verticalGaussian (ε n) σ t)
      atTop (𝓝 (∫ t, g t)) := by
  apply tendsto_integral_of_dominated_convergence (fun t => Real.exp (σ ^ 2) * ‖g t‖)
  · intro n
    exact (regularized_integrable g hg (hε₀ n) (hε₁ n) σ).aestronglyMeasurable
  · exact hg.norm.const_mul _
  · intro n
    filter_upwards [] with t
    rw [norm_mul]
    calc
      ‖g t‖ * ‖verticalGaussian (ε n) σ t‖ ≤ ‖g t‖ * Real.exp (σ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (verticalGaussian_norm_le (hε₀ n) (hε₁ n) σ t) (norm_nonneg _)
      _ = Real.exp (σ ^ 2) * ‖g t‖ := mul_comm _ _
  · filter_upwards [] with t
    simpa only [mul_one] using
      (tendsto_const_nhds.mul (verticalGaussian_tendsto hε σ t) :
        Tendsto (fun n => g t * verticalGaussian (ε n) σ t) atTop (𝓝 (g t * 1)))

end ThetaGlobal.GaussianRegularization

#print axioms ThetaGlobal.GaussianRegularization.regularized_integral_tendsto
end

end Verification_GaussianRegularization
/- END SOURCE BODY: ThetaGlobal/GaussianRegularization.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/GaussianTransfer.lean -/
section Verification_GaussianTransfer

/-!
# Passing from a fixed profile to arbitrary tests by regularized convolution

This module is the global sum/integral and limit part of the Gaussian Mellin
deconvolution argument.  `forward` and `reverse` are fixed-profile expansions;
their identity is obtained from automorphy and weighted orbit unfolding in
the intended application.  The hypotheses below expose that prerequisite
explicitly.  In particular the final test-function reflection is never an
assumption.  Every exchange has a summable integral-norm hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GaussianTransfer

open MeasureTheory Filter
open scoped BigOperators Topology

variable {T I J : Type*} [MeasurableSpace T] [Countable I] [Countable J]
  {μ : Measure T}

/-- Integrating two equal fixed-profile expansions against a deconvolver
preserves equality, with all exchanges certified by absolute mass. -/
theorem convolve_fixed_profile
    (forward : I → T → ℂ) (reverse : J → T → ℂ) (kernel : T → ℂ)
    (hseed : ∀ᵐ t ∂μ, (∑' i, forward i t) = ∑' j, reverse j t)
    (hforward : ∀ i, Integrable (fun t => kernel t * forward i t) μ)
    (hreverse : ∀ j, Integrable (fun t => kernel t * reverse j t) μ)
    (hfmass : Summable (fun i => ∫ t, ‖kernel t * forward i t‖ ∂μ))
    (hrmass : Summable (fun j => ∫ t, ‖kernel t * reverse j t‖ ∂μ)) :
    (∑' i, ∫ t, kernel t * forward i t ∂μ) =
      ∑' j, ∫ t, kernel t * reverse j t ∂μ := by
  rw [integral_tsum_of_summable_integral_norm hforward hfmass,
    integral_tsum_of_summable_integral_norm hreverse hrmass]
  apply integral_congr_ae
  filter_upwards [hseed] with t ht
  simp only [tsum_mul_left, ht]

/-- The same result after identifying each scalar local convolution. -/
theorem regularized_identity
    (forward : I → T → ℂ) (reverse : J → T → ℂ) (kernel : T → ℂ)
    (a : I → ℂ) (b : J → ℂ)
    (hseed : ∀ᵐ t ∂μ, (∑' i, forward i t) = ∑' j, reverse j t)
    (hforward : ∀ i, Integrable (fun t => kernel t * forward i t) μ)
    (hreverse : ∀ j, Integrable (fun t => kernel t * reverse j t) μ)
    (hfmass : Summable (fun i => ∫ t, ‖kernel t * forward i t‖ ∂μ))
    (hrmass : Summable (fun j => ∫ t, ‖kernel t * reverse j t‖ ∂μ))
    (hfirst : ∀ i, (∫ t, kernel t * forward i t ∂μ) = a i)
    (hsecond : ∀ j, (∫ t, kernel t * reverse j t ∂μ) = b j) :
    (∑' i, a i) = ∑' j, b j := by
  simpa only [hfirst, hsecond] using
    convolve_fixed_profile forward reverse kernel hseed hforward hreverse hfmass hrmass

/-- Removing a regularizer requires only two explicit summable majorants.
No analytic continuation or growth assertion about a global Dirichlet
series enters this theorem. -/
theorem remove_regularizer
    (a : ℕ → I → ℂ) (b : ℕ → J → ℂ) (a₀ : I → ℂ) (b₀ : J → ℂ)
    (A : I → ℝ) (B : J → ℝ)
    (hA : Summable A) (hB : Summable B)
    (ha : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (a₀ i)))
    (hb : ∀ j, Tendsto (fun n => b n j) atTop (𝓝 (b₀ j)))
    (ha_bound : ∀ n i, ‖a n i‖ ≤ A i)
    (hb_bound : ∀ n j, ‖b n j‖ ≤ B j)
    (heq : ∀ n, (∑' i, a n i) = ∑' j, b n j) :
    Summable a₀ ∧ Summable b₀ ∧ (∑' i, a₀ i) = ∑' j, b₀ j := by
  have hta := tendsto_tsum_of_dominated_convergence hA ha (Eventually.of_forall ha_bound)
  have htb := tendsto_tsum_of_dominated_convergence hB hb (Eventually.of_forall hb_bound)
  have hsa : Summable a₀ := hA.of_norm_bounded fun i =>
    le_of_tendsto ((ha i).norm) (Eventually.of_forall fun n => ha_bound n i)
  have hsb : Summable b₀ := hB.of_norm_bounded fun j =>
    le_of_tendsto ((hb j).norm) (Eventually.of_forall fun n => hb_bound n j)
  refine ⟨hsa, hsb, ?_⟩
  exact tendsto_nhds_unique (hta.congr heq) htb

/-- Full global transfer once the scalar Mellin convolution formulas have
been established.  The fixed-profile identity is independent of `a₀,b₀`.
All assumptions are included here so that the unresolved automorphic
realization cannot be hidden in a packaged final-reflection field. -/
theorem reflection_from_regularized_convolution
    (forward : I → T → ℂ) (reverse : J → T → ℂ)
    (kernel : ℕ → T → ℂ)
    (a : ℕ → I → ℂ) (b : ℕ → J → ℂ) (a₀ : I → ℂ) (b₀ : J → ℂ)
    (hseed : ∀ᵐ t ∂μ, (∑' i, forward i t) = ∑' j, reverse j t)
    (hforward : ∀ n i, Integrable (fun t => kernel n t * forward i t) μ)
    (hreverse : ∀ n j, Integrable (fun t => kernel n t * reverse j t) μ)
    (hfmass : ∀ n, Summable (fun i => ∫ t, ‖kernel n t * forward i t‖ ∂μ))
    (hrmass : ∀ n, Summable (fun j => ∫ t, ‖kernel n t * reverse j t‖ ∂μ))
    (hfirst : ∀ n i, (∫ t, kernel n t * forward i t ∂μ) = a n i)
    (hsecond : ∀ n j, (∫ t, kernel n t * reverse j t ∂μ) = b n j)
    (A : I → ℝ) (B : J → ℝ) (hA : Summable A) (hB : Summable B)
    (ha : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (a₀ i)))
    (hb : ∀ j, Tendsto (fun n => b n j) atTop (𝓝 (b₀ j)))
    (ha_bound : ∀ n i, ‖a n i‖ ≤ A i)
    (hb_bound : ∀ n j, ‖b n j‖ ≤ B j) :
    Summable a₀ ∧ Summable b₀ ∧ (∑' i, a₀ i) = ∑' j, b₀ j := by
  apply remove_regularizer a b a₀ b₀ A B hA hB ha hb ha_bound hb_bound
  intro n
  exact regularized_identity forward reverse (kernel n) (a n) (b n) hseed
    (hforward n) (hreverse n) (hfmass n) (hrmass n) (hfirst n) (hsecond n)

end ThetaGlobal.GaussianTransfer

#print axioms ThetaGlobal.GaussianTransfer.reflection_from_regularized_convolution
end

end Verification_GaussianTransfer
/- END SOURCE BODY: ThetaGlobal/GaussianTransfer.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/ConvolutionMass.lean -/
section Verification_ConvolutionMass

/-!
# Absolute convolution mass from one weighted moment

The fixed-profile transfer does not need an analytic continuation of the
global Dirichlet series. A single absolutely convergent coefficient majorant
and the corresponding positive/negative power moment of the deconvolver
justify all exchanges. In logarithmic coordinates these are exponential
moments. The estimates retain the sign change on the reflected side.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.ConvolutionMass

open MeasureTheory
open scoped BigOperators

variable {I T : Type*} [MeasurableSpace T] {μ : Measure T}

/-- A separable majorant proves both individual integrability and summable
integral norms, the precise hypotheses of absolute integral/series Fubini. -/
theorem absolute_mass_of_separable_majorant
    (f : I → T → ℂ) (b : I → ℝ) (g : T → ℝ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hb : Summable b) (hg : Integrable g μ)
    (hbound : ∀ i, ∀ᵐ t ∂μ, ‖f i t‖ ≤ b i * g t) :
    (∀ i, Integrable (f i) μ) ∧
      Summable (fun i => ∫ t, ‖f i t‖ ∂μ) := by
  have hi (i : I) : Integrable (f i) μ :=
    Integrable.mono' (hg.const_mul (b i)) (hf i) (hbound i)
  refine ⟨hi, ?_⟩
  apply (hb.mul_right (∫ t, g t ∂μ)).of_nonneg_of_le
    (fun i => integral_nonneg fun t => norm_nonneg (f i t))
  intro i
  calc
    (∫ t, ‖f i t‖ ∂μ) ≤ ∫ t, b i * g t ∂μ :=
      integral_mono_ae (hi i).norm (hg.const_mul (b i)) (hbound i)
    _ = b i * ∫ t, g t ∂μ := integral_const_mul _ _

/-- Translating the direct profile requires the negative exponential
moment of the deconvolver. -/
theorem direct_log_bound (P J : ℝ → ℂ) (a : ℂ) (x t σ C : ℝ)
    (hP : ‖P (t + x)‖ ≤ C * Real.exp (-σ * (t + x))) :
    ‖J t * (a * P (t + x))‖ ≤
      (‖a‖ * Real.exp (-σ * x)) * (C * (‖J t‖ * Real.exp (-σ * t))) := by
  rw [norm_mul, norm_mul]
  calc
    ‖J t‖ * (‖a‖ * ‖P (t + x)‖) ≤
        ‖J t‖ * (‖a‖ * (C * Real.exp (-σ * (t + x)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hP (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by
      rw [show -σ * (t + x) = -σ * t + -σ * x by ring, Real.exp_add]
      ring

/-- Reflecting the log variable reverses that sign, so the positive
exponential moment is needed on the reflected side. -/
theorem reflected_log_bound (H J : ℝ → ℂ) (a : ℂ) (x t σ C : ℝ)
    (hH : ‖H (x - t)‖ ≤ C * Real.exp (-σ * (x - t))) :
    ‖J t * (a * H (x - t))‖ ≤
      (‖a‖ * Real.exp (-σ * x)) * (C * (‖J t‖ * Real.exp (σ * t))) := by
  rw [norm_mul, norm_mul]
  calc
    ‖J t‖ * (‖a‖ * ‖H (x - t)‖) ≤
        ‖J t‖ * (‖a‖ * (C * Real.exp (-σ * (x - t)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hH (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by
      rw [show -σ * (x - t) = -σ * x + σ * t by ring, Real.exp_add]
      ring

theorem direct_convolution_absolute_mass
    (P J : ℝ → ℂ) (a : I → ℂ) (x : I → ℝ) (σ C : ℝ)
    (hP : ∀ y, ‖P y‖ ≤ C * Real.exp (-σ * y))
    (hcoeff : Summable (fun i => ‖a i‖ * Real.exp (-σ * x i)))
    (hmoment : Integrable (fun t => ‖J t‖ * Real.exp (-σ * t)))
    (hmeas : ∀ i, AEStronglyMeasurable (fun t => J t * (a i * P (t + x i)))) :
    (∀ i, Integrable (fun t => J t * (a i * P (t + x i)))) ∧
      Summable (fun i => ∫ t, ‖J t * (a i * P (t + x i))‖) := by
  apply absolute_mass_of_separable_majorant _
    (fun i => ‖a i‖ * Real.exp (-σ * x i))
    (fun t => C * (‖J t‖ * Real.exp (-σ * t))) hmeas hcoeff
    (hmoment.const_mul C)
  intro i
  exact Filter.Eventually.of_forall fun t => direct_log_bound P J (a i) (x i) t σ C (hP _)

theorem reflected_convolution_absolute_mass
    (H : I → ℝ → ℂ) (J : ℝ → ℂ) (a : I → ℂ) (x : I → ℝ) (σ C : ℝ)
    (hH : ∀ i y, ‖H i y‖ ≤ C * Real.exp (-σ * y))
    (hcoeff : Summable (fun i => ‖a i‖ * Real.exp (-σ * x i)))
    (hmoment : Integrable (fun t => ‖J t‖ * Real.exp (σ * t)))
    (hmeas : ∀ i, AEStronglyMeasurable (fun t => J t * (a i * H i (x i - t)))) :
    (∀ i, Integrable (fun t => J t * (a i * H i (x i - t)))) ∧
      Summable (fun i => ∫ t, ‖J t * (a i * H i (x i - t))‖) := by
  apply absolute_mass_of_separable_majorant _
    (fun i => ‖a i‖ * Real.exp (-σ * x i))
    (fun t => C * (‖J t‖ * Real.exp (σ * t))) hmeas hcoeff
    (hmoment.const_mul C)
  intro i
  exact Filter.Eventually.of_forall fun t => reflected_log_bound (H i) J (a i) (x i) t σ C (hH i _)

end ThetaGlobal.ConvolutionMass

#print axioms ThetaGlobal.ConvolutionMass.absolute_mass_of_separable_majorant
#print axioms ThetaGlobal.ConvolutionMass.reflected_convolution_absolute_mass
end

end Verification_ConvolutionMass
/- END SOURCE BODY: ThetaGlobal/ConvolutionMass.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/ScalarMellinConvolution.lean -/
section Verification_ScalarMellinConvolution

/-!
# The two scalar Mellin deconvolution identities, with their signs

We work in logarithmic coordinates `u = log t`, so Lebesgue measure here
is exactly the multiplicative measure `dt/t`.  `positiveSpectrum f τ`
is the Mellin transform at `iτ` of `x ↦ f (log x)`.

The direct profile is translated as `f(u+z)` and the reflected profile as
`h(z-u)`.  They consequently consume the seed Mellin factors at `-iτ` and
`+iτ`, respectively.  All sum/integral interchange in this scalar result is
derived from two ordinary L1 assumptions, with no theta identity premise.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.ScalarMellinConvolution

open MeasureTheory
open scoped Topology

def phase (τ u : ℝ) : ℂ := Complex.exp ((τ : ℂ) * Complex.I * (u : ℂ))

theorem norm_phase (τ u : ℝ) : ‖phase τ u‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp

theorem continuous_phase : Continuous (fun p : ℝ × ℝ => phase (-p.1) p.2) := by
  unfold phase
  fun_prop

theorem phase_shift (τ z v : ℝ) :
    phase (-τ) (v - z) = phase τ z * phase (-τ) v := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_reverse (τ z v : ℝ) :
    phase (-τ) (z - v) = phase (-τ) z * phase τ v := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

def positiveSpectrum (f : ℝ → ℂ) (τ : ℝ) : ℂ :=
  ∫ u, f u * phase τ u

def inverseLine (G : ℝ → ℂ) (u : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ τ, G τ * phase (-τ) u

theorem integrable_spectral_product {G f : ℝ → ℂ}
    (hG : Integrable G) (hf : Integrable f) :
    Integrable (fun p : ℝ × ℝ => G p.1 * phase (-p.1) p.2 * f p.2)
      (volume.prod volume) := by
  have hprod := hG.mul_prod hf
  apply hprod.mono
  · have hm := hprod.aestronglyMeasurable.mul continuous_phase.aestronglyMeasurable
    convert hm using 1
    funext p
    change G p.1 * phase (-p.1) p.2 * f p.2 = (G p.1 * f p.2) * phase (-p.1) p.2
    ring
  · filter_upwards [] with p
    simp only [norm_mul, norm_phase, mul_one]
    exact le_rfl

/-- The scalar inverse-transform/product interchange; absolute Fubini follows
from `G ∈ L1` and `f ∈ L1` because the phase has norm one. -/
theorem integral_inverse_mul {G f : ℝ → ℂ}
    (hG : Integrable G) (hf : Integrable f) :
    (∫ u, inverseLine G u * f u) =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ τ, G τ * positiveSpectrum f (-τ) := by
  have hi (u : ℝ) : inverseLine G u * f u =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ τ, G τ * phase (-τ) u * f u := by
    rw [inverseLine, integral_mul_const]
    ring
  simp_rw [hi]
  rw [integral_const_mul]
  congr 1
  calc
    (∫ u, ∫ τ, G τ * phase (-τ) u * f u) =
        ∫ τ, ∫ u, G τ * phase (-τ) u * f u :=
      integral_integral_swap (integrable_spectral_product hG hf).swap
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with τ
      rw [positiveSpectrum, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      ring

theorem positiveSpectrum_translate (f : ℝ → ℂ) (τ z : ℝ) :
    positiveSpectrum (fun u => f (u + z)) (-τ) =
      phase τ z * positiveSpectrum f (-τ) := by
  have hshift := integral_add_right_eq_self
    (fun v : ℝ => f v * phase (-τ) (v - z)) z (μ := volume)
  simp only [add_sub_cancel_right] at hshift
  unfold positiveSpectrum
  rw [hshift, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [phase_shift]
  ring

theorem positiveSpectrum_reverse (f : ℝ → ℂ) (τ z : ℝ) :
    positiveSpectrum (fun u => f (z - u)) (-τ) =
      phase (-τ) z * positiveSpectrum f τ := by
  have hshift := integral_sub_left_eq_self
    (fun v : ℝ => f v * phase (-τ) (z - v)) volume z
  have hcancel (u : ℝ) : z - (z - u) = u := by ring
  simp only [hcancel] at hshift
  unfold positiveSpectrum
  rw [hshift, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [phase_reverse]
  ring

theorem direct_profile_convolution {G f : ℝ → ℂ}
    (hG : Integrable G) (hf : Integrable f) (z : ℝ) :
    (∫ u, inverseLine G u * f (u + z)) =
      (2 * (Real.pi : ℂ))⁻¹ *
        ∫ τ, G τ * phase τ z * positiveSpectrum f (-τ) := by
  rw [integral_inverse_mul hG (hf.comp_add_right z)]
  simp_rw [positiveSpectrum_translate, mul_assoc]

theorem reverse_profile_convolution {G f : ℝ → ℂ}
    (hG : Integrable G) (hf : Integrable f) (z : ℝ) :
    (∫ u, inverseLine G u * f (z - u)) =
      (2 * (Real.pi : ℂ))⁻¹ *
        ∫ τ, G τ * phase (-τ) z * positiveSpectrum f τ := by
  rw [integral_inverse_mul hG (hf.comp_sub_left z)]
  simp_rw [positiveSpectrum_reverse, mul_assoc]

def gaussian (ε τ : ℝ) : ℂ := Complex.exp (-(ε : ℂ) * (τ : ℂ) ^ 2)

theorem gaussian_even (ε τ : ℝ) : gaussian ε (-τ) = gaussian ε τ := by
  simp [gaussian]

/-- `M τ` is the direct seed Mellin transform at `iτ`.  Thus the
denominator here is `M(-τ)`, exactly as required by Mellin correlation. -/
def deconvolutionSpectrum (M Vhat : ℝ → ℂ) (ε τ : ℝ) : ℂ :=
  Vhat (-τ) * gaussian ε τ / M (-τ)

def regularizedTest (Vhat : ℝ → ℂ) (ε z : ℝ) : ℂ :=
  inverseLine (fun τ => Vhat τ * gaussian ε τ) z

def regularizedReflected (Vhat R : ℝ → ℂ) (ε z : ℝ) : ℂ :=
  inverseLine (fun τ => Vhat (-τ) * gaussian ε τ * R τ) z

/-- The direct scalar deconvolution formula.  `hM` is a local Mellin pair,
and `hMne` follows from the explicit gamma product on the imaginary axis.
There is no fixed-profile global theta identity among the assumptions. -/
theorem deconvolver_direct (f : ℝ → ℂ) (hf : Integrable f)
    (M Vhat : ℝ → ℂ) (ε : ℝ)
    (hM : ∀ τ, positiveSpectrum f τ = M τ) (hMne : ∀ τ, M τ ≠ 0)
    (hG : Integrable (deconvolutionSpectrum M Vhat ε)) (z : ℝ) :
    (∫ u, inverseLine (deconvolutionSpectrum M Vhat ε) u * f (u + z)) =
      regularizedTest Vhat ε z := by
  rw [direct_profile_convolution hG hf]
  have heq (τ : ℝ) :
      deconvolutionSpectrum M Vhat ε τ * phase τ z * positiveSpectrum f (-τ) =
        Vhat (-τ) * gaussian ε τ * phase τ z := by
    rw [hM]
    unfold deconvolutionSpectrum
    field_simp [hMne (-τ)]
  simp_rw [heq]
  unfold regularizedTest inverseLine
  congr 1
  have hneg := integral_neg_eq_self
    (fun τ : ℝ => Vhat τ * gaussian ε τ * phase (-τ) z) volume
  simpa only [gaussian_even, neg_neg] using hneg

/-- The reflected scalar formula.  `hH` is the explicit local quotient
identity `Hhat(iτ) = M(-iτ) R(iτ)`; it is not a theta reflection identity. -/
theorem deconvolver_reflected (h : ℝ → ℂ) (hh : Integrable h)
    (M Vhat R : ℝ → ℂ) (ε : ℝ)
    (hH : ∀ τ, positiveSpectrum h τ = M (-τ) * R τ)
    (hMne : ∀ τ, M τ ≠ 0)
    (hG : Integrable (deconvolutionSpectrum M Vhat ε)) (z : ℝ) :
    (∫ u, inverseLine (deconvolutionSpectrum M Vhat ε) u * h (z - u)) =
      regularizedReflected Vhat R ε z := by
  rw [reverse_profile_convolution hG hh]
  unfold regularizedReflected inverseLine
  congr 1
  apply integral_congr_ae
  filter_upwards [] with τ
  rw [hH]
  unfold deconvolutionSpectrum
  field_simp [hMne (-τ)]

end ThetaGlobal.ScalarMellinConvolution
end

end Verification_ScalarMellinConvolution
/- END SOURCE BODY: ThetaGlobal/ScalarMellinConvolution.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/VerticalContour.lean -/
section Verification_VerticalContour

/-!
# Polynomial contour shifts and their Gaussian regularization

The unregularized contour lemma is extracted without mathematical changes
from the supplied `HeckeSkeleton.ThetaKernel.Shift` into a Mathlib-only
module. The additional theorem keeps an entire Gaussian regularizer in the
integrand. It applies to the existing multiplier bound and therefore
justifies uniform tail bounds without treating a smoothed test as annular.
-/

noncomputable section
namespace ThetaGlobal.VerticalContour

open MeasureTheory Set Filter
open scoped Topology

theorem integrable_one_add_abs_rpow_neg {e : ℝ} (he : 1 < e) :
    Integrable (fun t : ℝ => (1 + |t|) ^ (-e)) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := e) (by simpa using he)
  simpa [Real.norm_eq_abs] using this

theorem tendsto_one_add_abs_rpow_neg {e : ℝ} (he : 0 < e) :
    Tendsto (fun T : ℝ => (1 + T) ^ (-e)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun T : ℝ => 1 + T) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_id
  exact (tendsto_rpow_neg_atTop he).comp h1

theorem verticalIntegral_eq_of_poly_strip
    {f : ℂ → ℂ} {a b C e : ℝ} (hab : a ≤ b) (he : 1 < e)
    (hf : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ f z)
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + |t|) ^ (-e)) :
    (∫ t : ℝ, f ((a : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t : ℝ, f ((b : ℂ) + (t : ℂ) * Complex.I) := by
  have hint (σ : ℝ) (hσ : σ ∈ Icc a b) :
      Integrable (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    have hc : Continuous (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      have hr : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
      exact (hf _ (hr.symm ▸ hσ.1) (hr.symm ▸ hσ.2)).continuousAt.comp
        (by fun_prop : ContinuousAt (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) t)
    apply ((integrable_one_add_abs_rpow_neg he).const_mul C).mono'
      hc.aestronglyMeasurable
    exact ae_of_all _ (fun t => hbound σ hσ t)
  let horizontal : ℝ → ℂ := fun T => ∫ x : ℝ in a..b,
    f ((x : ℂ) + (T : ℂ) * Complex.I)
  have hg : Tendsto (fun T : ℝ => C * (1 + T) ^ (-e) * |b - a|) atTop (𝓝 0) := by
    have := ((tendsto_one_add_abs_rpow_neg (by linarith : 0 < e)).const_mul C).mul_const |b - a|
    simpa using this
  have hh : Tendsto horizontal atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
      (Eventually.of_forall (fun _ => norm_nonneg _))
    filter_upwards [eventually_ge_atTop 0] with T hT
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    have := hbound x (by simpa [uIcc_of_le hab] using uIoc_subset_uIcc hx) T
    simpa [abs_of_nonneg hT] using this
  have hhn : Tendsto (fun T => horizontal (-T)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
      (Eventually.of_forall (fun _ => norm_nonneg _))
    filter_upwards [eventually_ge_atTop 0] with T hT
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    have := hbound x (by simpa [uIcc_of_le hab] using uIoc_subset_uIcc hx) (-T)
    simpa [abs_neg, abs_of_nonneg hT] using this
  let left : ℝ → ℂ := fun T => ∫ t : ℝ in -T..T, f ((a : ℂ) + (t : ℂ) * Complex.I)
  let right : ℝ → ℂ := fun T => ∫ t : ℝ in -T..T, f ((b : ℂ) + (t : ℂ) * Complex.I)
  have hrect (T : ℝ) : horizontal (-T) - horizontal T +
      Complex.I * right T - Complex.I * left T = 0 := by
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) - (T : ℂ) * Complex.I) ((b : ℂ) + (T : ℂ) * Complex.I) (by
        intro z hz
        have hre : z.re ∈ Icc a b := by
          simpa [uIcc_of_le hab] using hz.1
        exact (hf z hre.1 hre.2).differentiableWithinAt)
    simpa only [horizontal, left, right, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      sub_zero, zero_sub, Complex.ofReal_neg, smul_eq_mul] using h
  have hl := intervalIntegral_tendsto_integral (hint a ⟨le_rfl, hab⟩)
    tendsto_neg_atTop_atBot tendsto_id
  have hr := intervalIntegral_tendsto_integral (hint b ⟨hab, le_rfl⟩)
    tendsto_neg_atTop_atBot tendsto_id
  have heq := tendsto_nhds_unique
    (((hhn.sub hh).add (hr.const_mul Complex.I)).sub (hl.const_mul Complex.I))
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun T => (hrect T).symm)))
  simp only [sub_self, zero_add] at heq
  exact (mul_left_cancel₀ Complex.I_ne_zero (sub_eq_zero.mp heq)).symm

theorem square_le_endpoints {a b σ : ℝ} (ha : a ≤ σ) (hb : σ ≤ b) :
    σ ^ 2 ≤ a ^ 2 + b ^ 2 := by
  rcases le_or_gt 0 σ with hσ | hσ
  · have hb0 : 0 ≤ b := hσ.trans hb
    nlinarith [sq_nonneg a]
  · have ha0 : a ≤ 0 := ha.trans hσ.le
    nlinarith [sq_nonneg b]

theorem gaussian_norm_le_strip {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    {a b σ : ℝ} (ha : a ≤ σ) (hb : σ ≤ b) (t : ℝ) :
    ‖GaussianRegularization.verticalGaussian ε σ t‖ ≤ Real.exp (a ^ 2 + b ^ 2) :=
  (GaussianRegularization.verticalGaussian_norm_le hε₀ hε₁ σ t).trans
    (Real.exp_le_exp.mpr (square_le_endpoints ha hb))

/-- A Gaussian regularizer preserves the contour shift. On a fixed strip
its norm is uniformly bounded for `0 ≤ ε ≤ 1`, so the original polynomial
majorant still applies with a fixed larger constant. -/
theorem verticalIntegral_regularized_eq_of_poly_strip
    {f : ℂ → ℂ} {a b C e ε : ℝ} (hab : a ≤ b) (he : 1 < e) (hC : 0 ≤ C)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hf : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ f z)
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + |t|) ^ (-e)) :
    (∫ t : ℝ, f ((a : ℂ) + (t : ℂ) * Complex.I) *
      GaussianRegularization.verticalGaussian ε a t) =
      ∫ t : ℝ, f ((b : ℂ) + (t : ℂ) * Complex.I) *
        GaussianRegularization.verticalGaussian ε b t := by
  apply verticalIntegral_eq_of_poly_strip
    (f := fun z => f z * Complex.exp ((ε : ℂ) * z ^ 2))
    (C := C * Real.exp (a ^ 2 + b ^ 2)) hab he
  · intro z hz₀ hz₁
    exact (hf z hz₀ hz₁).mul (by fun_prop)
  · intro σ hσ t
    change ‖f ((σ : ℂ) + (t : ℂ) * Complex.I) *
      GaussianRegularization.verticalGaussian ε σ t‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ (C * (1 + |t|) ^ (-e)) * Real.exp (a ^ 2 + b ^ 2) :=
        mul_le_mul (hbound σ hσ t)
          (gaussian_norm_le_strip hε₀ hε₁ hσ.1 hσ.2 t)
          (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
      _ = _ := by ring

end ThetaGlobal.VerticalContour

#print axioms ThetaGlobal.VerticalContour.verticalIntegral_regularized_eq_of_poly_strip
end

end Verification_VerticalContour
/- END SOURCE BODY: ThetaGlobal/VerticalContour.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/VerticalInverseBounds.lean -/
section Verification_VerticalInverseBounds

/-!
# Uniform bounds and removal of the regularizer on a Mellin line

The spectral function below is the ORIGINAL annular-test Mellin transform
times its local multiplier. The estimate never invokes an annular-test
theorem on a Gaussian-smoothed, noncompactly supported test.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.VerticalInverseBounds

open MeasureTheory Filter
open scoped Topology

def powerPhase (σ y t : ℝ) : ℂ :=
  (y : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))

theorem powerPhase_norm (σ t : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖powerPhase σ y t‖ = y ^ (-σ) := by
  rw [powerPhase, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp

theorem powerPhase_continuous (σ : ℝ) {y : ℝ} (hy : 0 < y) :
    Continuous (powerPhase σ y) := by
  have h : Continuous (fun t : ℝ => -((σ : ℂ) + (t : ℂ) * Complex.I)) := by fun_prop
  apply h.const_cpow
  exact Or.inl (by exact_mod_cast hy.ne')

theorem integrable_line (F : ℝ → ℂ) (hF : Integrable F) (σ : ℝ)
    {y : ℝ} (hy : 0 < y) :
    Integrable (fun t => F t * powerPhase σ y t) := by
  apply Integrable.mono' (hF.norm.mul_const (y ^ (-σ)))
    (hF.aestronglyMeasurable.mul (powerPhase_continuous σ hy).aestronglyMeasurable)
  filter_upwards [] with t
  change ‖F t * powerPhase σ y t‖ ≤ ‖F t‖ * y ^ (-σ)
  rw [norm_mul, powerPhase_norm σ t hy]

def inverseLine (F : ℝ → ℂ) (σ y : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ t, F t * powerPhase σ y t

def regularizedInverseLine (F : ℝ → ℂ) (ε σ y : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ *
    ∫ t, (F t * powerPhase σ y t) * GaussianRegularization.verticalGaussian ε σ t

theorem regularized_line_integrable (F : ℝ → ℂ) (hF : Integrable F)
    {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (σ : ℝ)
    {y : ℝ} (hy : 0 < y) :
    Integrable (fun t => (F t * powerPhase σ y t) *
      GaussianRegularization.verticalGaussian ε σ t) :=
  GaussianRegularization.regularized_integrable _ (integrable_line F hF σ hy) hε₀ hε₁ σ

/-- One `y^(-σ)` bound is uniform over all `0 ≤ ε ≤ 1`.  Setting `σ=2`
gives the arithmetic summable majorant used to remove the regularizer. -/
theorem regularizedInverseLine_bound (F : ℝ → ℂ) (hF : Integrable F)
    {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (σ : ℝ)
    {y : ℝ} (hy : 0 < y) :
    ‖regularizedInverseLine F ε σ y‖ ≤
      (‖(2 * (Real.pi : ℂ))⁻¹‖ * Real.exp (σ ^ 2) * (∫ t, ‖F t‖)) * y ^ (-σ) := by
  have hi := regularized_line_integrable F hF hε₀ hε₁ σ hy
  have hp (t : ℝ) :
      ‖(F t * powerPhase σ y t) * GaussianRegularization.verticalGaussian ε σ t‖ ≤
        (‖F t‖ * y ^ (-σ)) * Real.exp (σ ^ 2) := by
    rw [norm_mul, norm_mul, powerPhase_norm σ t hy]
    exact mul_le_mul_of_nonneg_left
      (GaussianRegularization.verticalGaussian_norm_le hε₀ hε₁ σ t)
      (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hy.le _))
  unfold regularizedInverseLine
  rw [norm_mul]
  calc
    _ ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ *
        ∫ t, ‖(F t * powerPhase σ y t) * GaussianRegularization.verticalGaussian ε σ t‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ *
        ∫ t, (‖F t‖ * y ^ (-σ)) * Real.exp (σ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (integral_mono_ae hi.norm
          ((hF.norm.mul_const (y ^ (-σ))).mul_const (Real.exp (σ ^ 2)))
          (Filter.Eventually.of_forall hp)) (norm_nonneg _)
    _ = _ := by
      rw [integral_mul_const, integral_mul_const]
      ring

theorem uniform_tail (F : ℝ → ℂ) (hF : Integrable F) (σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε, 0 ≤ ε → ε ≤ 1 →
      ∀ y, 0 < y → ‖regularizedInverseLine F ε σ y‖ ≤ C * y ^ (-σ) := by
  refine ⟨‖(2 * (Real.pi : ℂ))⁻¹‖ * Real.exp (σ ^ 2) * (∫ t, ‖F t‖), ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
      (integral_nonneg fun t => norm_nonneg (F t))
  · intro ε hε₀ hε₁ y hy
    exact regularizedInverseLine_bound F hF hε₀ hε₁ σ hy

theorem regularizedInverseLine_tendsto (F : ℝ → ℂ) (hF : Integrable F)
    (ε : ℕ → ℝ) (hε₀ : ∀ n, 0 ≤ ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0)) (σ : ℝ) {y : ℝ} (hy : 0 < y) :
    Tendsto (fun n => regularizedInverseLine F (ε n) σ y)
      atTop (𝓝 (inverseLine F σ y)) :=
  (GaussianRegularization.regularized_integral_tendsto _
    (integrable_line F hF σ hy) ε hε₀ hε₁ hε σ).const_mul _

end ThetaGlobal.VerticalInverseBounds

#print axioms ThetaGlobal.VerticalInverseBounds.uniform_tail
#print axioms ThetaGlobal.VerticalInverseBounds.regularizedInverseLine_tendsto
end

end Verification_VerticalInverseBounds
/- END SOURCE BODY: ThetaGlobal/VerticalInverseBounds.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/TestMellinLimit.lean -/
section Verification_TestMellinLimit

/-!
# Pointwise recovery of the original test after Gaussian regularization

The inverse integral is identified with Mathlib's Mellin inverse, including
its `1/(2π)` normalization and the sign of the imaginary coordinate.
Mellin inversion and dominated convergence then prove convergence to the
original test at every positive continuity point.  In particular no
almost-everywhere representative is substituted in an ideal sum.

The two integrability assumptions are the ordinary Mellin and vertical
Mellin convergence conditions.  For smooth annular tests they follow from
the existing `ThetaKernel.TestMellin` estimates.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.TestMellinLimit

open MeasureTheory Filter
open scoped Topology

theorem powerPhase_zero_eq_phase (t : ℝ) {y : ℝ} (hy : 0 < y) :
    VerticalInverseBounds.powerPhase 0 y t =
      ScalarMellinConvolution.phase (-t) (Real.log y) := by
  unfold VerticalInverseBounds.powerPhase ScalarMellinConvolution.phase
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'),
    ← Complex.ofReal_log hy.le]
  congr 1
  push_cast
  ring

theorem verticalGaussian_zero_eq (ε t : ℝ) :
    GaussianRegularization.verticalGaussian ε 0 t =
      ScalarMellinConvolution.gaussian ε t := by
  unfold GaussianRegularization.verticalGaussian ScalarMellinConvolution.gaussian
  congr 1
  simp only [Complex.ofReal_zero, zero_add, mul_pow, Complex.I_sq]
  ring

theorem inverseLine_eq_mellinInv (F : ℂ → ℂ) (σ y : ℝ) :
    VerticalInverseBounds.inverseLine
      (fun t => F ((σ : ℂ) + (t : ℂ) * Complex.I)) σ y = mellinInv σ F y := by
  unfold VerticalInverseBounds.inverseLine VerticalInverseBounds.powerPhase mellinInv
  simp only [one_div, Complex.real_smul, smul_eq_mul, Complex.ofReal_inv,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun t => mul_comm _ _

theorem scalar_regularizedTest_eq (F : ℂ → ℂ) (ε : ℝ)
    {y : ℝ} (hy : 0 < y) :
    ScalarMellinConvolution.regularizedTest
      (fun t => F ((t : ℂ) * Complex.I)) ε (Real.log y) =
      VerticalInverseBounds.regularizedInverseLine
        (fun t => F ((t : ℂ) * Complex.I)) ε 0 y := by
  unfold ScalarMellinConvolution.regularizedTest ScalarMellinConvolution.inverseLine
    VerticalInverseBounds.regularizedInverseLine
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [powerPhase_zero_eq_phase t hy, verticalGaussian_zero_eq]
  ring

/-- Actual pointwise Mellin inversion, before taking the regularized limit. -/
theorem inverseLine_mellin_eq (f : ℝ → ℂ) (σ : ℝ)
    (hf : MellinConvergent f σ) (hF : Complex.VerticalIntegrable (mellin f) σ)
    {y : ℝ} (hy : 0 < y) (hc : ContinuousAt f y) :
    VerticalInverseBounds.inverseLine
      (fun t => mellin f ((σ : ℂ) + (t : ℂ) * Complex.I)) σ y = f y := by
  rw [inverseLine_eq_mellinInv]
  exact mellinInv_mellin_eq σ f hy hf hF hc

/-- The Gaussian-smoothed test converges at every positive point, not
merely almost everywhere.  This is the limit required by discrete theta
and ideal sums. -/
theorem regularized_test_tendsto (f : ℝ → ℂ)
    (hf : MellinConvergent f 0) (hF : Complex.VerticalIntegrable (mellin f) 0)
    (ε : ℕ → ℝ) (hε₀ : ∀ n, 0 ≤ ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0))
    {y : ℝ} (hy : 0 < y) (hc : ContinuousAt f y) :
    Tendsto (fun n => ScalarMellinConvolution.regularizedTest
      (fun t => mellin f ((t : ℂ) * Complex.I)) (ε n) (Real.log y))
      atTop (𝓝 (f y)) := by
  have hi : Integrable (fun t : ℝ => mellin f ((t : ℂ) * Complex.I)) := by
    simpa only [Complex.VerticalIntegrable, Complex.ofReal_zero, zero_add] using hF
  have h := VerticalInverseBounds.regularizedInverseLine_tendsto
    (fun t => mellin f ((t : ℂ) * Complex.I)) hi ε hε₀ hε₁ hε 0 hy
  have hinv : VerticalInverseBounds.inverseLine
      (fun t => mellin f ((t : ℂ) * Complex.I)) 0 y = f y := by
    simpa only [Complex.ofReal_zero, zero_add] using inverseLine_mellin_eq f 0 hf hF hy hc
  rw [hinv] at h
  exact h.congr (fun n => (scalar_regularizedTest_eq (mellin f) (ε n) hy).symm)

end ThetaGlobal.TestMellinLimit

#print axioms ThetaGlobal.TestMellinLimit.inverseLine_mellin_eq
#print axioms ThetaGlobal.TestMellinLimit.regularized_test_tendsto
end

end Verification_TestMellinLimit
/- END SOURCE BODY: ThetaGlobal/TestMellinLimit.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/DeconvolverMoments.lean -/
section Verification_DeconvolverMoments

/-!
# All absolute power moments of a scalar Mellin deconvolver

For an entire spectral function G, quadratic decay on every fixed vertical
strip implies that its inverse Mellin transform has every absolute power
moment. This is the exact local condition supplied by the annular Mellin
transform times a Gaussian times the entire reciprocal gamma product.
No theta identity or final reflection statement is a hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.DeconvolverMoments

open MeasureTheory Set Filter
open scoped Topology

def verticalSpectrum (G : ℂ → ℂ) (c t : ℝ) : ℂ :=
  G ((c : ℂ) + (t : ℂ) * Complex.I)

def exponentialPhase (c t u : ℝ) : ℂ :=
  Complex.exp (-((c : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))

def logInverse (G : ℂ → ℂ) (c u : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ t, verticalSpectrum G c t * exponentialPhase c t u

/-- Local scalar spectral decay, proved in the application from the Gaussian
and the fixed-strip growth of reciprocal gamma. -/
def QuadraticStripDecay (G : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, a ≤ b → ∃ C : ℝ, 0 ≤ C ∧
    ∀ c ∈ Icc a b, ∀ t : ℝ,
      ‖verticalSpectrum G c t‖ ≤ C * (1 + |t|) ^ (-2 : ℝ)

theorem norm_exponentialPhase (c t u : ℝ) :
    ‖exponentialPhase c t u‖ = Real.exp (-c * u) := by
  rw [exponentialPhase, Complex.norm_exp]
  simp

theorem integrable_verticalSpectrum {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hstrip : QuadraticStripDecay G) (c : ℝ) :
    Integrable (verticalSpectrum G c) := by
  obtain ⟨C, _, hC⟩ := hstrip c c le_rfl
  have hc : Continuous (verticalSpectrum G c) := by
    exact hG.continuous.comp (by fun_prop)
  apply ((VerticalContour.integrable_one_add_abs_rpow_neg (e := 2) (by norm_num)).const_mul C).mono'
    hc.aestronglyMeasurable
  exact Eventually.of_forall (fun t => hC c ⟨le_rfl, le_rfl⟩ t)

private theorem strip_exponent_le {a b c : ℝ}
    (ha : a ≤ c) (hb : c ≤ b) (u : ℝ) :
    -c * u ≤ |a * u| + |b * u| := by
  rcases le_total 0 u with hu | hu
  · calc
      -c * u = -(c * u) := by ring
      _ ≤ -(a * u) := neg_le_neg (mul_le_mul_of_nonneg_right ha hu)
      _ ≤ |a * u| := neg_le_abs _
      _ ≤ _ := le_add_of_nonneg_right (abs_nonneg _)
  · calc
      -c * u = -(c * u) := by ring
      _ ≤ -(b * u) := neg_le_neg (mul_le_mul_of_nonpos_right hb hu)
      _ ≤ |b * u| := neg_le_abs _
      _ ≤ _ := le_add_of_nonneg_left (abs_nonneg _)

/-- The two inverse lines agree pointwise in the logarithmic argument. -/
theorem logInverse_line_independent {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hstrip : QuadraticStripDecay G)
    (a b u : ℝ) : logInverse G a u = logInverse G b u := by
  have shift (a b : ℝ) (hab : a ≤ b) :
      logInverse G a u = logInverse G b u := by
    obtain ⟨C, hC, hbound⟩ := hstrip a b hab
    unfold logInverse
    congr 1
    apply VerticalContour.verticalIntegral_eq_of_poly_strip
      (f := fun z => G z * Complex.exp (-z * (u : ℂ)))
      (C := C * Real.exp (|a * u| + |b * u|)) (e := 2) hab (by norm_num)
    · intro z _ _
      exact (hG z).mul (by fun_prop)
    · intro c hc t
      change ‖verticalSpectrum G c t * exponentialPhase c t u‖ ≤ _
      rw [norm_mul, norm_exponentialPhase]
      calc
        _ ≤ (C * (1 + |t|) ^ (-2 : ℝ)) *
            Real.exp (|a * u| + |b * u|) :=
          mul_le_mul (hbound c hc t)
            (Real.exp_le_exp.mpr (strip_exponent_le hc.1 hc.2 u))
            (Real.exp_pos _).le
            (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
        _ = _ := by ring
  rcases le_total a b with hab | hba
  · exact shift a b hab
  · exact (shift b a hba).symm

theorem logInverse_bound (G : ℂ → ℂ) (c u : ℝ) :
    ‖logInverse G c u‖ ≤
      (‖(2 * (Real.pi : ℂ))⁻¹‖ * ∫ t, ‖verticalSpectrum G c t‖) *
        Real.exp (-c * u) := by
  unfold logInverse
  rw [norm_mul]
  calc
    _ ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ *
        ∫ t, ‖verticalSpectrum G c t * exponentialPhase c t u‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ = _ := by
      simp_rw [norm_mul, norm_exponentialPhase]
      rw [integral_mul_const]
      ring

/-- Continuity is pointwise, so scalar inversion identities never have to
remain merely almost everywhere statements. -/
theorem continuous_logInverse {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hstrip : QuadraticStripDecay G) :
    Continuous (logInverse G 0) := by
  have hspec := integrable_verticalSpectrum hG hstrip 0
  have hspec_cont : Continuous (verticalSpectrum G 0) :=
    hG.continuous.comp (by fun_prop)
  have hi : Continuous (fun u : ℝ =>
      ∫ t, verticalSpectrum G 0 t * exponentialPhase 0 t u) := by
    apply continuous_of_dominated (bound := fun t => ‖verticalSpectrum G 0 t‖)
    · intro u
      exact (hspec_cont.mul (by unfold exponentialPhase; fun_prop)).aestronglyMeasurable
    · intro u
      filter_upwards [] with t
      rw [norm_mul, norm_exponentialPhase]
      simp
    · exact hspec.norm
    · filter_upwards [] with t
      unfold exponentialPhase
      fun_prop
  exact continuous_const.mul hi

theorem zeroLine_eq_scalarInverse (G : ℂ → ℂ) (u : ℝ) :
    logInverse G 0 u =
      ScalarMellinConvolution.inverseLine (verticalSpectrum G 0) u := by
  unfold logInverse ScalarMellinConvolution.inverseLine
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  unfold exponentialPhase ScalarMellinConvolution.phase
  congr 1
  push_cast
  ring

/-- A pair of opposite log-exponential envelopes gives the required L1
moment. This is the rigorous split into t <= 1 and t >= 1. -/
theorem integrable_log_weight_of_two_bounds (J : ℝ → ℂ)
    (hJ : Continuous J) (q Cminus Cplus : ℝ)
    (hminus : ∀ u, ‖J u‖ ≤ Cminus * Real.exp (-(q - 1) * u))
    (hplus : ∀ u, ‖J u‖ ≤ Cplus * Real.exp (-(q + 1) * u)) :
    Integrable (fun u => ‖J u‖ * Real.exp (q * u)) := by
  let f : ℝ → ℝ := fun u => ‖J u‖ * Real.exp (q * u)
  have hf : Continuous f := hJ.norm.mul (by fun_prop)
  have hleft : IntegrableOn f (Iic 0) := by
    apply ((integrableOn_exp_Iic 0).const_mul Cminus).mono' hf.aestronglyMeasurable
    filter_upwards [] with u
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
    calc
      f u ≤ (Cminus * Real.exp (-(q - 1) * u)) * Real.exp (q * u) :=
        mul_le_mul_of_nonneg_right (hminus u) (Real.exp_pos _).le
      _ = Cminus * Real.exp u := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        congr 1
        ring
  have hright : IntegrableOn f (Ioi 0) := by
    apply ((integrableOn_exp_neg_Ioi 0).const_mul Cplus).mono' hf.aestronglyMeasurable
    filter_upwards [] with u
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
    calc
      f u ≤ (Cplus * Real.exp (-(q + 1) * u)) * Real.exp (q * u) :=
        mul_le_mul_of_nonneg_right (hplus u) (Real.exp_pos _).le
      _ = Cplus * Real.exp (-u) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        congr 1
        ring
  simpa only [Iic_union_Ioi, integrableOn_univ] using hleft.union hright

/-- Every absolute power moment of the Mellin deconvolver is finite in
logarithmic coordinates. The constants are allowed to depend on the line. -/
theorem integrable_log_power_moment {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hstrip : QuadraticStripDecay G) (q : ℝ) :
    Integrable (fun u => ‖logInverse G 0 u‖ * Real.exp (q * u)) := by
  apply integrable_log_weight_of_two_bounds (logInverse G 0)
    (continuous_logInverse hG hstrip) q
    (‖(2 * (Real.pi : ℂ))⁻¹‖ * ∫ t, ‖verticalSpectrum G (q - 1) t‖)
    (‖(2 * (Real.pi : ℂ))⁻¹‖ * ∫ t, ‖verticalSpectrum G (q + 1) t‖)
  · intro u
    rw [logInverse_line_independent hG hstrip 0 (q - 1) u]
    exact logInverse_bound G (q - 1) u
  · intro u
    rw [logInverse_line_independent hG hstrip 0 (q + 1) u]
    exact logInverse_bound G (q + 1) u

def multiplicativeInverse (G : ℂ → ℂ) (t : ℝ) : ℂ :=
  logInverse G 0 (Real.log t)

/-- The exact dt/t form, including any real positive or negative moment. -/
theorem integrable_multiplicative_power_moment {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hstrip : QuadraticStripDecay G) (q : ℝ) :
    IntegrableOn (fun t => ‖multiplicativeInverse G t‖ * t ^ q / t) (Ioi 0) := by
  have h := (integrableOn_comp_log_Ioi_zero
    (fun u => ‖logInverse G 0 u‖ * Real.exp (q * u))).mpr
      (integrable_log_power_moment hG hstrip q)
  apply h.congr_fun _ measurableSet_Ioi
  intro t ht
  change t⁻¹ * (‖logInverse G 0 (Real.log t)‖ * Real.exp (q * Real.log t)) =
    ‖logInverse G 0 (Real.log t)‖ * t ^ q / t
  rw [Real.rpow_def_of_pos ht, mul_comm (Real.log t) q]
  ring

end ThetaGlobal.DeconvolverMoments

end

end Verification_DeconvolverMoments
/- END SOURCE BODY: ThetaGlobal/DeconvolverMoments.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/AnnularTransfer.lean -/
section Verification_AnnularTransfer

/-!
# Explicit arbitrary-test transfer from local Mellin pairs and a global seed

All scalar convolution, weighted-moment, absolute Fubini, and limit steps are
proved here. The one remaining global prerequisite is displayed as hseed:
equality of the two ACTUAL fixed-profile theta expansions at every log scale.
That prerequisite must be independently proved from the automorphic source.
This theorem is a conditional transfer theorem, not a claim to have supplied
the missing global automorphic identity.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.AnnularTransfer

open MeasureTheory Filter
open ScalarMellinConvolution DeconvolverMoments
open scoped Topology BigOperators

/-- Only local profile statements. In the application these are the actual
V0 and Hκ log profiles, their gamma Mellin pairs, and two-ended local bounds.
There is deliberately no global theta identity in this structure. -/
structure LocalProfiles (C : Type*) where
  direct : ℝ → ℂ
  reflected : C → ℝ → ℂ
  M : ℝ → ℂ
  R : C → ℝ → ℂ
  direct_continuous : Continuous direct
  reflected_continuous : ∀ c, Continuous (reflected c)
  direct_integrable : Integrable direct
  reflected_integrable : ∀ c, Integrable (reflected c)
  direct_mellin : ∀ t, positiveSpectrum direct t = M t
  reflected_mellin : ∀ c t, positiveSpectrum (reflected c) t = M (-t) * R c t
  M_ne_zero : ∀ t, M t ≠ 0
  exponent : ℝ
  directBound : ℝ
  reflectedBound : ℝ
  direct_tail : ∀ u, ‖direct u‖ ≤ directBound * Real.exp (-exponent * u)
  reflected_tail : ∀ c u, ‖reflected c u‖ ≤ reflectedBound * Real.exp (-exponent * u)

/-- A local scalar spectrum, not a theta seed. The intended spectrum is
Vhat(-w) exp(ε w²) times the actual entire reciprocal gamma product. -/
structure DeconvolverData (M Vhat : ℝ → ℂ) (ε : ℝ) where
  spectrum : ℂ → ℂ
  entire : Differentiable ℂ spectrum
  strip_decay : QuadraticStripDecay spectrum
  imaginary_line : ∀ t,
    verticalSpectrum spectrum 0 t = deconvolutionSpectrum M Vhat ε t

variable {C : Type*} (L : LocalProfiles C) (Vhat : ℝ → ℂ)

def kernel (ε : ℝ) (J : DeconvolverData L.M Vhat ε) : ℝ → ℂ :=
  logInverse J.spectrum 0

theorem kernel_continuous (ε : ℝ) (J : DeconvolverData L.M Vhat ε) :
    Continuous (kernel L Vhat ε J) :=
  continuous_logInverse J.entire J.strip_decay

theorem kernel_moment (ε : ℝ) (J : DeconvolverData L.M Vhat ε) (q : ℝ) :
    Integrable (fun u => ‖kernel L Vhat ε J u‖ * Real.exp (q * u)) :=
  integrable_log_power_moment J.entire J.strip_decay q

theorem deconvolution_spectrum_integrable (ε : ℝ)
    (J : DeconvolverData L.M Vhat ε) :
    Integrable (deconvolutionSpectrum L.M Vhat ε) := by
  have heq : verticalSpectrum J.spectrum 0 = deconvolutionSpectrum L.M Vhat ε :=
    funext J.imaginary_line
  rw [← heq]
  exact integrable_verticalSpectrum J.entire J.strip_decay 0

theorem kernel_eq_scalar (ε : ℝ) (J : DeconvolverData L.M Vhat ε) (u : ℝ) :
    kernel L Vhat ε J u =
      ScalarMellinConvolution.inverseLine (deconvolutionSpectrum L.M Vhat ε) u := by
  unfold kernel
  rw [zeroLine_eq_scalarInverse]
  congr 1
  exact funext J.imaginary_line

theorem direct_scalar_convolution (ε : ℝ) (J : DeconvolverData L.M Vhat ε)
    (a : ℂ) (x : ℝ) :
    (∫ u, kernel L Vhat ε J u * (a * L.direct (u + x))) =
      a * regularizedTest Vhat ε x := by
  calc
    _ = a * ∫ u, kernel L Vhat ε J u * L.direct (u + x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      ring
    _ = _ := by
      simp_rw [kernel_eq_scalar]
      rw [deconvolver_direct L.direct L.direct_integrable L.M Vhat ε
        L.direct_mellin L.M_ne_zero (deconvolution_spectrum_integrable L Vhat ε J)]

theorem reflected_scalar_convolution (ε : ℝ) (J : DeconvolverData L.M Vhat ε)
    (b : ℂ) (c : C) (x : ℝ) :
    (∫ u, kernel L Vhat ε J u * (b * L.reflected c (x - u))) =
      b * regularizedReflected Vhat (L.R c) ε x := by
  calc
    _ = b * ∫ u, kernel L Vhat ε J u * L.reflected c (x - u) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      ring
    _ = _ := by
      simp_rw [kernel_eq_scalar]
      rw [deconvolver_reflected (L.reflected c) (L.reflected_integrable c)
        L.M Vhat (L.R c) ε (L.reflected_mellin c) L.M_ne_zero
        (deconvolution_spectrum_integrable L Vhat ε J)]

variable {I J : Type*} [Countable I] [Countable J]

/-- Every integral/sum interchange is proved from the local spectral moments,
local profile tails, and independently proved arithmetic norm majorants.
hseed is precisely the independent global automorphic prerequisite. -/
theorem regularized_reflection
    (a : I → ℂ) (b : J → ℂ) (x : I → ℝ) (y : J → ℝ) (sector : J → C)
    (ha : Summable (fun i => ‖a i‖ * Real.exp (-L.exponent * x i)))
    (hb : Summable (fun j => ‖b j‖ * Real.exp (-L.exponent * y j)))
    (hseed : ∀ u : ℝ, (∑' i, a i * L.direct (u + x i)) =
      ∑' j, b j * L.reflected (sector j) (y j - u))
    (ε : ℝ) (D : DeconvolverData L.M Vhat ε) :
    (∑' i, a i * regularizedTest Vhat ε (x i)) =
      ∑' j, b j * regularizedReflected Vhat (L.R (sector j)) ε (y j) := by
  have hd := ConvolutionMass.direct_convolution_absolute_mass
    L.direct (kernel L Vhat ε D) a x L.exponent L.directBound L.direct_tail ha
    (kernel_moment L Vhat ε D (-L.exponent)) (by
      intro i
      exact ((kernel_continuous L Vhat ε D).mul
        (continuous_const.mul (L.direct_continuous.comp (by fun_prop)))).aestronglyMeasurable)
  have hr := ConvolutionMass.reflected_convolution_absolute_mass
    (fun j => L.reflected (sector j)) (kernel L Vhat ε D) b y
    L.exponent L.reflectedBound (fun j => L.reflected_tail (sector j)) hb
    (kernel_moment L Vhat ε D L.exponent) (by
      intro j
      exact ((kernel_continuous L Vhat ε D).mul
        (continuous_const.mul ((L.reflected_continuous (sector j)).comp
          (by fun_prop)))).aestronglyMeasurable)
  exact GaussianTransfer.regularized_identity
    (fun i u => a i * L.direct (u + x i))
    (fun j u => b j * L.reflected (sector j) (y j - u))
    (kernel L Vhat ε D)
    (fun i => a i * regularizedTest Vhat ε (x i))
    (fun j => b j * regularizedReflected Vhat (L.R (sector j)) ε (y j))
    (Eventually.of_forall hseed) hd.1 hr.1 hd.2 hr.2
    (fun i => direct_scalar_convolution L Vhat ε D (a i) (x i))
    (fun j => reflected_scalar_convolution L Vhat ε D (b j) (sector j) (y j))

/-- Arbitrary-test transfer with no assumed scalar convolution or summed
regularized identity. The remaining assumptions are local scalar limits and
uniform tails, arithmetic majorants, and the explicit fixed-profile seed. -/
theorem arbitrary_test_reflection
    (a : I → ℂ) (b : J → ℂ) (x : I → ℝ) (y : J → ℝ) (sector : J → C)
    (ha : Summable (fun i => ‖a i‖ * Real.exp (-L.exponent * x i)))
    (hb : Summable (fun j => ‖b j‖ * Real.exp (-L.exponent * y j)))
    (hseed : ∀ u : ℝ, (∑' i, a i * L.direct (u + x i)) =
      ∑' j, b j * L.reflected (sector j) (y j - u))
    (ε : ℕ → ℝ) (D : ∀ n, DeconvolverData L.M Vhat (ε n))
    (V : ℝ → ℂ) (Phi : C → ℝ → ℂ)
    (hV : ∀ z, Tendsto (fun n => regularizedTest Vhat (ε n) z) atTop (𝓝 (V z)))
    (hPhi : ∀ c z, Tendsto (fun n => regularizedReflected Vhat (L.R c) (ε n) z)
      atTop (𝓝 (Phi c z)))
    (CV CPhi : ℝ)
    (hVtail : ∀ n z, ‖regularizedTest Vhat (ε n) z‖ ≤
      CV * Real.exp (-L.exponent * z))
    (hPhitail : ∀ n c z, ‖regularizedReflected Vhat (L.R c) (ε n) z‖ ≤
      CPhi * Real.exp (-L.exponent * z)) :
    Summable (fun i => a i * V (x i)) ∧
      Summable (fun j => b j * Phi (sector j) (y j)) ∧
      (∑' i, a i * V (x i)) = ∑' j, b j * Phi (sector j) (y j) := by
  apply GaussianTransfer.remove_regularizer
    (fun n i => a i * regularizedTest Vhat (ε n) (x i))
    (fun n j => b j * regularizedReflected Vhat (L.R (sector j)) (ε n) (y j))
    (fun i => a i * V (x i)) (fun j => b j * Phi (sector j) (y j))
    (fun i => (‖a i‖ * Real.exp (-L.exponent * x i)) * CV)
    (fun j => (‖b j‖ * Real.exp (-L.exponent * y j)) * CPhi)
    (ha.mul_right CV) (hb.mul_right CPhi)
  · intro i
    exact tendsto_const_nhds.mul (hV (x i))
  · intro j
    exact tendsto_const_nhds.mul (hPhi (sector j) (y j))
  · intro n i
    rw [norm_mul]
    calc
      _ ≤ ‖a i‖ * (CV * Real.exp (-L.exponent * x i)) :=
        mul_le_mul_of_nonneg_left (hVtail n (x i)) (norm_nonneg _)
      _ = _ := by ring
  · intro n j
    rw [norm_mul]
    calc
      _ ≤ ‖b j‖ * (CPhi * Real.exp (-L.exponent * y j)) :=
        mul_le_mul_of_nonneg_left (hPhitail n (sector j) (y j)) (norm_nonneg _)
      _ = _ := by ring
  · intro n
    exact regularized_reflection L Vhat a b x y sector ha hb hseed (ε n) (D n)

end ThetaGlobal.AnnularTransfer

end

end Verification_AnnularTransfer
/- END SOURCE BODY: ThetaGlobal/AnnularTransfer.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/ScalarGaussianLimits.lean -/
section Verification_ScalarGaussianLimits

/-!
# Pointwise scalar Gaussian limits, including actual Mellin inversion

These are the scalar limit hypotheses needed by AnnularTransfer. They follow
from ordinary L1 vertical spectra and Mathlib's Mellin inversion theorem.
The final direct theorem converges to the actual test value V(exp z), not an
unspecified inverse transform and not merely an almost-everywhere value.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.ScalarGaussianLimits

open MeasureTheory Filter
open ThetaGlobal.ScalarMellinConvolution
open scoped Topology

theorem gaussian_eq_vertical (ε t : ℝ) :
    gaussian ε t = GaussianRegularization.verticalGaussian ε 0 t := by
  unfold gaussian GaussianRegularization.verticalGaussian
  congr 1
  simp only [Complex.ofReal_zero, zero_add, mul_pow, Complex.I_sq]
  ring

theorem integrable_phase_product {G : ℝ → ℂ} (hG : Integrable G) (z : ℝ) :
    Integrable (fun t => G t * phase (-t) z) := by
  have hp : Continuous (fun t : ℝ => phase (-t) z) := by
    unfold phase
    fun_prop
  apply hG.norm.mono' (hG.aestronglyMeasurable.mul hp.aestronglyMeasurable)
  filter_upwards [] with t
  change ‖G t * phase (-t) z‖ ≤ ‖G t‖
  rw [norm_mul, norm_phase, mul_one]

theorem regularizedTest_tendsto_inverseLine (Vhat : ℝ → ℂ) (hVhat : Integrable Vhat)
    (ε : ℕ → ℝ) (hε₀ : ∀ n, 0 ≤ ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0)) (z : ℝ) :
    Tendsto (fun n => regularizedTest Vhat (ε n) z)
      atTop (𝓝 (inverseLine Vhat z)) := by
  have h := (GaussianRegularization.regularized_integral_tendsto
    (fun t => Vhat t * phase (-t) z) (integrable_phase_product hVhat z)
    ε hε₀ hε₁ hε 0).const_mul (2 * (Real.pi : ℂ))⁻¹
  have heq (n : ℕ) : regularizedTest Vhat (ε n) z =
      (2 * (Real.pi : ℂ))⁻¹ *
        ∫ t, (Vhat t * phase (-t) z) * GaussianRegularization.verticalGaussian (ε n) 0 t := by
    unfold regularizedTest inverseLine
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    rw [gaussian_eq_vertical]
    ring
  simpa only [heq, inverseLine] using h

theorem regularizedReflected_eq_regularizedTest (Vhat R : ℝ → ℂ) (ε z : ℝ) :
    regularizedReflected Vhat R ε z =
      regularizedTest (fun t => Vhat (-t) * R t) ε z := by
  unfold regularizedReflected regularizedTest inverseLine
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  ring

theorem regularizedReflected_tendsto (Vhat R : ℝ → ℂ)
    (hF : Integrable (fun t => Vhat (-t) * R t))
    (ε : ℕ → ℝ) (hε₀ : ∀ n, 0 ≤ ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0)) (z : ℝ) :
    Tendsto (fun n => regularizedReflected Vhat R (ε n) z)
      atTop (𝓝 (inverseLine (fun t => Vhat (-t) * R t) z)) := by
  simpa only [regularizedReflected_eq_regularizedTest] using
    regularizedTest_tendsto_inverseLine (fun t => Vhat (-t) * R t) hF ε hε₀ hε₁ hε z

/-- Exact compatibility of the log-coordinate inverse line with Mathlib's
Mellin inverse and its normalization 1/(2π). -/
theorem inverseLine_mellin_eq (V : ℝ → ℂ) (z : ℝ) :
    inverseLine (fun t => mellin V ((t : ℂ) * Complex.I)) z =
      mellinInv 0 (mellin V) (Real.exp z) := by
  have hpow (t : ℝ) :
      ((Real.exp z : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) = phase (-t) z := by
    rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.exp_pos z).ne'),
      ← Complex.ofReal_log (Real.exp_pos z).le, Real.log_exp]
    unfold phase
    congr 1
    push_cast
    ring
  unfold inverseLine mellinInv
  simp only [Complex.ofReal_zero, zero_add, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_inv,
    Complex.ofReal_mul, Complex.ofReal_ofNat, one_div]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [hpow]
  ring

/-- The actual test is recovered at every positive point whenever its Mellin
integral and vertical transform are L1 and it is continuous at that point.
Smooth annular tests satisfy these scalar analytic hypotheses. -/
theorem regularizedTest_tendsto_actual_test (V : ℝ → ℂ)
    (hV : MellinConvergent V 0)
    (hF : Complex.VerticalIntegrable (mellin V) 0)
    (ε : ℕ → ℝ) (hε₀ : ∀ n, 0 ≤ ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0)) (z : ℝ)
    (hcont : ContinuousAt V (Real.exp z)) :
    Tendsto (fun n =>
      regularizedTest (fun t => mellin V ((t : ℂ) * Complex.I)) (ε n) z)
      atTop (𝓝 (V (Real.exp z))) := by
  have hspec : Integrable (fun t : ℝ => mellin V ((t : ℂ) * Complex.I)) := by
    simpa only [Complex.VerticalIntegrable, Complex.ofReal_zero, zero_add] using hF
  have h := regularizedTest_tendsto_inverseLine
    (fun t => mellin V ((t : ℂ) * Complex.I)) hspec ε hε₀ hε₁ hε z
  rw [inverseLine_mellin_eq,
    mellinInv_mellin_eq 0 V (Real.exp_pos z) hV hF hcont] at h
  exact h

end ThetaGlobal.ScalarGaussianLimits

end

end Verification_ScalarGaussianLimits
/- END SOURCE BODY: ThetaGlobal/ScalarGaussianLimits.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/GaussianStripDecay.lean -/
section Verification_GaussianStripDecay

/-!
# A Gaussian converts explicit exponential strip growth into quadratic decay

The fixed-strip input is the ordinary polynomial-times-exponential bound
provided by reciprocal-gamma Stirling estimates. The proof is elementary:
(1+x)^m <= exp(mx), followed by completion of the square. No decay or
integrability of the resulting deconvolver is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GaussianStripDecay

open Set
open DeconvolverMoments

/-- Explicit local strip growth, with natural polynomial degree. -/
def ExponentialStripGrowth (F : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, a ≤ b → ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℝ, ∃ N : ℕ,
    ∀ c ∈ Icc a b, ∀ t : ℝ,
      ‖F ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (1 + |t|) ^ N * Real.exp (A * |t|)

/-- Annular-test Mellin transforms are bounded on each fixed strip. -/
def BoundedOnVerticalStrips (F : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, a ≤ b → ∃ C : ℝ, 0 ≤ C ∧
    ∀ c ∈ Icc a b, ∀ t : ℝ,
      ‖F ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C

theorem BoundedOnVerticalStrips.exponentialGrowth {F : ℂ → ℂ}
    (hF : BoundedOnVerticalStrips F) : ExponentialStripGrowth F := by
  intro a b hab
  obtain ⟨C, hC, hbound⟩ := hF a b hab
  refine ⟨C, hC, 0, 0, ?_⟩
  simpa only [pow_zero, zero_mul, Real.exp_zero, mul_one] using hbound

theorem ExponentialStripGrowth.comp_neg {F : ℂ → ℂ}
    (hF : ExponentialStripGrowth F) :
    ExponentialStripGrowth (fun s => F (-s)) := by
  intro a b hab
  obtain ⟨C, hC, A, N, hbound⟩ := hF (-b) (-a) (neg_le_neg hab)
  refine ⟨C, hC, A, N, ?_⟩
  intro c hc t
  have h := hbound (-c) ⟨neg_le_neg hc.2, neg_le_neg hc.1⟩ (-t)
  have he : ((-c : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I =
      -((c : ℂ) + (t : ℂ) * Complex.I) := by push_cast; ring
  rw [he] at h
  simpa only [abs_neg] using h

theorem ExponentialStripGrowth.mul {F G : ℂ → ℂ}
    (hF : ExponentialStripGrowth F) (hG : ExponentialStripGrowth G) :
    ExponentialStripGrowth (fun s => F s * G s) := by
  intro a b hab
  obtain ⟨C₁, hC₁, A₁, N₁, h₁⟩ := hF a b hab
  obtain ⟨C₂, hC₂, A₂, N₂, h₂⟩ := hG a b hab
  refine ⟨C₁ * C₂, mul_nonneg hC₁ hC₂, A₁ + A₂, N₁ + N₂, ?_⟩
  intro c hc t
  rw [norm_mul]
  calc
    _ ≤ (C₁ * (1 + |t|) ^ N₁ * Real.exp (A₁ * |t|)) *
        (C₂ * (1 + |t|) ^ N₂ * Real.exp (A₂ * |t|)) :=
      mul_le_mul (h₁ c hc t) (h₂ c hc t) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [pow_add, add_mul, Real.exp_add]
      ring

theorem one_add_pow_le_exp {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (1 + x) ^ n ≤ Real.exp ((n : ℝ) * x) := by
  rw [Real.exp_nat_mul]
  apply pow_le_pow_left₀ (by linarith)
  linarith [Real.add_one_le_exp x]

theorem linear_sub_quadratic_le {ε : ℝ} (hε : 0 < ε) (A x : ℝ) :
    A * x - ε * x ^ 2 ≤ A ^ 2 / (4 * ε) := by
  apply (le_div_iff₀ (by positivity : 0 < 4 * ε)).mpr
  nlinarith [sq_nonneg (2 * ε * x - A)]

def regularized (F : ℂ → ℂ) (ε : ℝ) (s : ℂ) : ℂ :=
  F s * Complex.exp ((ε : ℂ) * s ^ 2)

/-- The explicit quadratic strip constant. No uniformity as ε -> 0 is claimed
or needed for the fixed-ε moment and Fubini arguments. -/
def stripConstant (C A a b ε : ℝ) (N : ℕ) : ℝ :=
  C * Real.exp (ε * (a ^ 2 + b ^ 2) + (A + ((N + 2 : ℕ) : ℝ)) ^ 2 / (4 * ε))

theorem regularized_strip_bound
    (F : ℂ → ℂ) {a b C A ε : ℝ} (N : ℕ)
    (hC : 0 ≤ C) (hε : 0 < ε)
    (hbound : ∀ c ∈ Icc a b, ∀ t : ℝ,
      ‖F ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (1 + |t|) ^ N * Real.exp (A * |t|)) :
    ∀ c ∈ Icc a b, ∀ t : ℝ,
      ‖regularized F ε ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        stripConstant C A a b ε N * (1 + |t|) ^ (-2 : ℝ) := by
  intro c hc t
  have hpoly := one_add_pow_le_exp (abs_nonneg t) (N + 2)
  have hsquare := VerticalContour.square_le_endpoints hc.1 hc.2
  have hcomplete := linear_sub_quadratic_le hε (A + ((N + 2 : ℕ) : ℝ)) |t|
  rw [sq_abs] at hcomplete
  have hexp : ((N + 2 : ℕ) : ℝ) * |t| + (A * |t| + ε * (c ^ 2 - t ^ 2)) ≤
      ε * (a ^ 2 + b ^ 2) + (A + ((N + 2 : ℕ) : ℝ)) ^ 2 / (4 * ε) := by
    have hc' := mul_le_mul_of_nonneg_left hsquare hε.le
    nlinarith
  have hweighted :
      ‖regularized F ε ((c : ℂ) + (t : ℂ) * Complex.I)‖ * (1 + |t|) ^ 2 ≤
        stripConstant C A a b ε N := by
    unfold regularized
    rw [norm_mul]
    change (‖F ((c : ℂ) + (t : ℂ) * Complex.I)‖ *
      ‖GaussianRegularization.verticalGaussian ε c t‖) * (1 + |t|) ^ 2 ≤ _
    rw [GaussianRegularization.verticalGaussian_norm]
    calc
      _ ≤ (C * (1 + |t|) ^ N * Real.exp (A * |t|) *
          Real.exp (ε * (c ^ 2 - t ^ 2))) * (1 + |t|) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hbound c hc t) (Real.exp_pos _).le)
          (sq_nonneg _)
      _ = C * (1 + |t|) ^ (N + 2) *
          Real.exp (A * |t| + ε * (c ^ 2 - t ^ 2)) := by
        rw [pow_add, Real.exp_add]
        ring
      _ ≤ C * Real.exp (((N + 2 : ℕ) : ℝ) * |t|) *
          Real.exp (A * |t| + ε * (c ^ 2 - t ^ 2)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpoly hC) (Real.exp_pos _).le
      _ = C * Real.exp (((N + 2 : ℕ) : ℝ) * |t| +
          (A * |t| + ε * (c ^ 2 - t ^ 2))) := by
        simp_rw [Real.exp_add]
        ring
      _ ≤ stripConstant C A a b ε N :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC
  have hpos : 0 < (1 + |t|) ^ 2 := by positivity
  have hdiv := (le_div_iff₀ hpos).mpr hweighted
  rw [Real.rpow_neg (by positivity : 0 ≤ 1 + |t|) 2, Real.rpow_two]
  simpa only [div_eq_mul_inv] using hdiv

theorem quadraticStripDecay_regularized {F : ℂ → ℂ}
    (hF : ExponentialStripGrowth F) {ε : ℝ} (hε : 0 < ε) :
    QuadraticStripDecay (regularized F ε) := by
  intro a b hab
  obtain ⟨C, hC, A, N, hbound⟩ := hF a b hab
  refine ⟨stripConstant C A a b ε N, ?_, ?_⟩
  · exact mul_nonneg hC (Real.exp_pos _).le
  · exact regularized_strip_bound F N hC hε hbound

theorem differentiable_regularized {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (ε : ℝ) :
    Differentiable ℂ (regularized F ε) := by
  exact hF.mul (by fun_prop)

end ThetaGlobal.GaussianStripDecay

end

end Verification_GaussianStripDecay
/- END SOURCE BODY: ThetaGlobal/GaussianStripDecay.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/GammaDeconvolver.lean -/
section Verification_GammaDeconvolver

/-!
# The actual finite gamma product supplies the scalar deconvolver

The direct profile has C0 A0^s times a finite product of shifted gamma factors.
This file proves its imaginary-line nonvanishing and the entire reciprocal
using Mathlib's actual reciprocal-Gamma theorem. The only remaining local
growth input is explicitly a polynomial-times-exponential strip bound for
that concrete reciprocal product (the usual reciprocal-Gamma Stirling bound).
GaussianStripDecay proves the resulting deconvolver's strip decay, after
which DeconvolverMoments proves all absolute power moments.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GammaDeconvolver

open MeasureTheory
open DeconvolverMoments GaussianStripDecay
open scoped Classical BigOperators

/-- For the theta profile the index is the complex place times the two sixth
offsets; shift = (|m_v|+1)/2 ± 1/6 and radial = -τ_v. -/
structure GammaProfile (ι : Type*) where
  C₀ : ℂ
  C₀_ne_zero : C₀ ≠ 0
  A₀ : ℝ
  A₀_pos : 0 < A₀
  shift : ι → ℝ
  shift_pos : ∀ j, 0 < shift j
  radial : ι → ℝ

variable {ι : Type*} [Fintype ι] (p : GammaProfile ι)

def directGamma (s : ℂ) : ℂ :=
  p.C₀ * Complex.exp ((Real.log p.A₀ : ℂ) * s) *
    ∏ j, Complex.Gamma ((p.shift j : ℂ) + s + Complex.I * (p.radial j : ℂ))

/-- Define the entire reciprocal through reciprocal Gamma, never through an
unconverged totalized Mellin integral. -/
def reciprocalGamma (s : ℂ) : ℂ :=
  p.C₀⁻¹ * Complex.exp (-((Real.log p.A₀ : ℂ) * s)) *
    ∏ j, (Complex.Gamma ((p.shift j : ℂ) + s + Complex.I * (p.radial j : ℂ)))⁻¹

theorem directGamma_eq_positive_cpow (s : ℂ) :
    directGamma p s = p.C₀ * (p.A₀ : ℂ) ^ s *
      ∏ j, Complex.Gamma ((p.shift j : ℂ) + s + Complex.I * (p.radial j : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr p.A₀_pos.ne'),
    ← Complex.ofReal_log p.A₀_pos.le]
  rfl

theorem reciprocalGamma_eq_inverse (s : ℂ) :
    reciprocalGamma p s = (directGamma p s)⁻¹ := by
  unfold reciprocalGamma directGamma
  simp only [mul_inv_rev, Finset.prod_inv_distrib, Complex.exp_neg]
  ring

/-- This is proved even at the gamma poles, using the entire reciprocal. -/
theorem reciprocalGamma_entire : Differentiable ℂ (reciprocalGamma p) := by
  apply Differentiable.mul
  · exact (differentiable_const (p.C₀⁻¹)).mul (by fun_prop)
  · apply Differentiable.fun_finsetProd
    intro j _
    exact Complex.differentiable_one_div_Gamma.comp (by fun_prop)

theorem directGamma_imaginary_ne_zero (t : ℝ) :
    directGamma p ((t : ℂ) * Complex.I) ≠ 0 := by
  apply mul_ne_zero (mul_ne_zero p.C₀_ne_zero (Complex.exp_ne_zero _))
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply Complex.Gamma_ne_zero_of_re_pos
  simpa using p.shift_pos j

/-- Concrete scalar deconvolution data for every positive regularizer.
The only Gamma estimate assumed is hStirling for the explicit reciprocal
product above. Its entire nature and imaginary nonvanishing are proved. -/
def gammaDeconvolver (Vhat : ℂ → ℂ)
    (hV : Differentiable ℂ Vhat) (hVstrip : BoundedOnVerticalStrips Vhat)
    (hStirling : ExponentialStripGrowth (reciprocalGamma p))
    (ε : ℝ) (hε : 0 < ε) :
    AnnularTransfer.DeconvolverData
      (fun t => directGamma p ((t : ℂ) * Complex.I))
      (fun t => Vhat ((t : ℂ) * Complex.I)) ε where
  spectrum := regularized (fun s => Vhat (-s) * reciprocalGamma p (-s)) ε
  entire := differentiable_regularized
    ((hV.comp differentiable_neg).mul ((reciprocalGamma_entire p).comp differentiable_neg)) ε
  strip_decay := quadraticStripDecay_regularized
    (hVstrip.exponentialGrowth.comp_neg.mul hStirling.comp_neg) hε
  imaginary_line := by
    intro t
    unfold verticalSpectrum regularized
    simp only [Complex.ofReal_zero, zero_add]
    have hneg : -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hneg, reciprocalGamma_eq_inverse]
    have hg := ScalarGaussianLimits.gaussian_eq_vertical ε t
    simp only [GaussianRegularization.verticalGaussian, Complex.ofReal_zero, zero_add] at hg
    rw [← hg]
    unfold ScalarMellinConvolution.deconvolutionSpectrum
    rw [div_eq_mul_inv]
    ring

/-- Every dt/t absolute power moment follows from the explicit Gamma profile,
annular Mellin strip bounds, and the local Stirling bound; it is not assumed. -/
theorem gammaDeconvolver_all_power_moments (Vhat : ℂ → ℂ)
    (hV : Differentiable ℂ Vhat) (hVstrip : BoundedOnVerticalStrips Vhat)
    (hStirling : ExponentialStripGrowth (reciprocalGamma p))
    (ε : ℝ) (hε : 0 < ε) (q : ℝ) :
    IntegrableOn
      (fun t => ‖multiplicativeInverse
        (gammaDeconvolver p Vhat hV hVstrip hStirling ε hε).spectrum t‖ * t ^ q / t)
      (Set.Ioi 0) :=
  integrable_multiplicative_power_moment
    (gammaDeconvolver p Vhat hV hVstrip hStirling ε hε).entire
    (gammaDeconvolver p Vhat hV hVstrip hStirling ε hε).strip_decay q

end ThetaGlobal.GammaDeconvolver

end

end Verification_GammaDeconvolver
/- END SOURCE BODY: ThetaGlobal/GammaDeconvolver.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/GammaAnnularTransfer.lean -/
section Verification_GammaAnnularTransfer

/-!
# Arbitrary-test transfer with the Gamma deconvolver actually constructed

This is the complete conditional analytic transfer interface. It assumes no
deconvolution kernel, power moments, scalar convolution identity, scalar
regularizer limit, or regularized theta identity. Those are all derived.
The independently required fixed-profile global identity is named hseed.
Consequently this theorem does not claim to prove that global prerequisite.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GammaAnnularTransfer

open MeasureTheory Filter
open AnnularTransfer GammaDeconvolver GaussianStripDecay ScalarMellinConvolution
open scoped Topology BigOperators

variable {ι C I J : Type*} [Fintype ι] [Countable I] [Countable J]

/-- The actual gamma Mellin formula supplies DeconvolverData, rather than
leaving the existence of such data as an analytic premise. -/
def profileDeconvolver (p : GammaProfile ι) (L : LocalProfiles C)
    (hM : L.M = fun t : ℝ => directGamma p ((t : ℂ) * Complex.I))
    (Vhat : ℂ → ℂ) (hV : Differentiable ℂ Vhat)
    (hVstrip : BoundedOnVerticalStrips Vhat)
    (hGamma : ExponentialStripGrowth (reciprocalGamma p))
    (ε : ℝ) (hε : 0 < ε) :
    DeconvolverData L.M (fun t => Vhat ((t : ℂ) * Complex.I)) ε := by
  rw [hM]
  exact gammaDeconvolver p Vhat hV hVstrip hGamma ε hε

/-- For an actual test V, the completed analytic transfer reduces to the
named fixed-profile global seed and ordinary local Mellin/profile estimates.
Both final series are proved summable. The direct limit is the pointwise
value V(exp x), and the reflected limit is the prescribed scalar inverse.

The two uniform-tail inputs concern the scalar transforms of the original
test. In the project they are proved on Re(s)=2 by RegularizedTestProject
and RegularizedKernelProject, without assuming the smoothed test is annular.
-/
theorem arbitrary_test_from_seed
    (p : GammaProfile ι) (L : LocalProfiles C)
    (hM : L.M = fun t : ℝ => directGamma p ((t : ℂ) * Complex.I))
    (V : ℝ → ℂ)
    (hVentire : Differentiable ℂ (mellin V))
    (hVstrip : BoundedOnVerticalStrips (mellin V))
    (hGamma : ExponentialStripGrowth (reciprocalGamma p))
    (hVconvergent : MellinConvergent V 0)
    (hVvertical : Complex.VerticalIntegrable (mellin V) 0)
    (hVcontinuous : ∀ x, 0 < x → ContinuousAt V x)
    (hRintegrable : ∀ c, Integrable (fun t : ℝ =>
      mellin V (((-t : ℝ) : ℂ) * Complex.I) * L.R c t))
    (a : I → ℂ) (b : J → ℂ) (x : I → ℝ) (y : J → ℝ) (sector : J → C)
    (ha : Summable (fun i => ‖a i‖ * Real.exp (-L.exponent * x i)))
    (hb : Summable (fun j => ‖b j‖ * Real.exp (-L.exponent * y j)))
    (hseed : ∀ u : ℝ, (∑' i, a i * L.direct (u + x i)) =
      ∑' j, b j * L.reflected (sector j) (y j - u))
    (ε : ℕ → ℝ) (hε₀ : ∀ n, 0 < ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0))
    (CV CPhi : ℝ)
    (hVtail : ∀ n z,
      ‖regularizedTest (fun t => mellin V ((t : ℂ) * Complex.I)) (ε n) z‖ ≤
        CV * Real.exp (-L.exponent * z))
    (hPhitail : ∀ n c z,
      ‖regularizedReflected (fun t => mellin V ((t : ℂ) * Complex.I))
        (L.R c) (ε n) z‖ ≤ CPhi * Real.exp (-L.exponent * z)) :
    Summable (fun i => a i * V (Real.exp (x i))) ∧
      Summable (fun j => b j * inverseLine
        (fun t : ℝ => mellin V (((-t : ℝ) : ℂ) * Complex.I) * L.R (sector j) t)
        (y j)) ∧
      (∑' i, a i * V (Real.exp (x i))) =
        ∑' j, b j * inverseLine
          (fun t : ℝ => mellin V (((-t : ℝ) : ℂ) * Complex.I) * L.R (sector j) t)
          (y j) := by
  apply AnnularTransfer.arbitrary_test_reflection L
    (fun t => mellin V ((t : ℂ) * Complex.I))
    a b x y sector ha hb hseed ε
    (fun n => profileDeconvolver p L hM (mellin V) hVentire hVstrip hGamma (ε n) (hε₀ n))
    (fun z => V (Real.exp z))
    (fun c z => inverseLine
      (fun t : ℝ => mellin V (((-t : ℝ) : ℂ) * Complex.I) * L.R c t) z)
    ?_ ?_ CV CPhi hVtail hPhitail
  · intro z
    exact ScalarGaussianLimits.regularizedTest_tendsto_actual_test V
      hVconvergent hVvertical ε (fun n => (hε₀ n).le) hε₁ hε z
      (hVcontinuous _ (Real.exp_pos z))
  · intro c z
    exact ScalarGaussianLimits.regularizedReflected_tendsto
      (fun t => mellin V ((t : ℂ) * Complex.I)) (L.R c) (hRintegrable c)
      ε (fun n => (hε₀ n).le) hε₁ hε z

end ThetaGlobal.GammaAnnularTransfer

end

end Verification_GammaAnnularTransfer
/- END SOURCE BODY: ThetaGlobal/GammaAnnularTransfer.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/GammaReciprocalGrowth.lean -/
section Verification_GammaReciprocalGrowth


/-!
# Reciprocal Gamma has exponential growth on every vertical strip

Euler reflection and the convergent Gamma integral suffice here.  Shift a
fixed strip left by an integer, bound each recurrence denominator by the
imaginary part when its absolute value is at least one, and use compactness
for the remaining rectangle.  No Stirling estimate is an input.
-/


set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GammaReciprocalGrowth

open Complex MeasureTheory Set
open scoped Topology

theorem norm_Gamma_le_real {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral, Real.Gamma_eq_integral hz]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [sub_re, one_re]

theorem norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  have h₁ : ‖Complex.exp (-z * Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using le_abs_self z.im
  have h₂ : ‖Complex.exp (z * Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using neg_le_abs z.im
  have h := (norm_sub_le (Complex.exp (-z * Complex.I))
    (Complex.exp (z * Complex.I))).trans (add_le_add h₁ h₂)
  norm_num only [norm_ofNat]
  linarith

theorem gamma_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    Complex.Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n hn
  apply hz
  simpa only [hn, neg_im, natCast_im, neg_zero]

theorem inverse_reflection {z : ℂ} (hz : z.im ≠ 0) :
    (Complex.Gamma z)⁻¹ =
      Complex.Gamma (1 - z) * Complex.sin (Real.pi * z) / Real.pi := by
  have hG := gamma_ne_zero_of_im_ne_zero hz
  have hG' : Complex.Gamma (1 - z) ≠ 0 :=
    gamma_ne_zero_of_im_ne_zero (by simpa using hz)
  have h := Complex.Gamma_mul_Gamma_one_sub z
  have hs : Complex.sin (Real.pi * z) ≠ 0 := by
    intro hs
    rw [hs, div_zero] at h
    exact mul_ne_zero hG hG' h
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have he := (eq_div_iff hs).mp h
  apply (eq_div_iff hp).mpr
  apply mul_left_cancel₀ hG
  rw [← mul_assoc, mul_inv_cancel₀ hG, one_mul]
  simpa only [mul_assoc] using he.symm

/-- Moving right by an integer cannot increase the reciprocal Gamma norm
at heights whose absolute value is at least one. -/
theorem inverse_Gamma_add_nat_le (z : ℂ) (n : ℕ) (ht : 1 ≤ |z.im|) :
    ‖(Complex.Gamma (z + n))⁻¹‖ ≤ ‖(Complex.Gamma z)⁻¹‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (1 : ℝ) ≤ ‖z + (n : ℂ)‖ := by
      exact ht.trans (by simpa using Complex.abs_im_le_norm (z + (n : ℂ)))
    calc
      ‖(Complex.Gamma (z + (n + 1 : ℕ)))⁻¹‖ =
          ‖(Complex.Gamma (z + n + 1))⁻¹‖ := by
        rw [Nat.cast_add, Nat.cast_one, add_assoc]
      _ ≤ ‖z + (n : ℂ)‖ * ‖(Complex.Gamma (z + n + 1))⁻¹‖ :=
        le_mul_of_one_le_left (norm_nonneg _) hn
      _ = ‖(Complex.Gamma (z + n))⁻¹‖ := by
        conv_rhs =>
          rw [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one, norm_mul]
      _ ≤ _ := ih

theorem real_Gamma_bounded {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ Icc a b, Real.Gamma c ≤ C := by
  have hcont : ContinuousOn Real.Gamma (Icc a b) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (fun c hc => ha.trans_le hc.1)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro c hc
  exact (le_abs_self _).trans ((hC c hc).trans (le_max_left _ _))

/-- Uniform exponential growth on an arbitrary fixed vertical strip. -/
theorem inverse_Gamma_strip_bound (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ Icc a b, ∀ t : ℝ,
      ‖(Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I))⁻¹‖ ≤
        C * Real.exp (Real.pi * |t|) := by
  obtain ⟨n, hn⟩ := exists_nat_gt b
  obtain ⟨M, hM, hMG⟩ := real_Gamma_bounded
    (a := 1 - b + n) (b := 1 - a + n) (by linarith)
  let rect : Set (ℝ × ℝ) := Icc a b ×ˢ Icc (-1 : ℝ) 1
  have hcompact : IsCompact rect := isCompact_Icc.prod isCompact_Icc
  have hcont : Continuous (fun x : ℝ × ℝ =>
      (Complex.Gamma ((x.1 : ℂ) + (x.2 : ℂ) * Complex.I))⁻¹) :=
    Complex.differentiable_one_div_Gamma.continuous.comp (by fun_prop)
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hcont.continuousOn
  let C := max (max B 0) (M / Real.pi)
  refine ⟨C, (le_max_right B 0).trans (le_max_left _ _), ?_⟩
  intro c hc t
  by_cases ht : 1 ≤ |t|
  · let z : ℂ := (c : ℂ) + (t : ℂ) * Complex.I - n
    have him : z.im = t := by simp [z]
    have himne : z.im ≠ 0 := by
      rw [him]
      intro hz
      have h : (1 : ℝ) ≤ 0 := by simpa only [hz, abs_zero] using ht
      exact (not_le_of_gt zero_lt_one) h
    have hre : 0 < (1 - z).re := by simp [z]; linarith [hc.2]
    have hreal : (1 - z).re ∈ Icc (1 - b + n) (1 - a + n) := by
      simp only [z, sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, zero_sub, sub_zero, natCast_re, one_re]
      constructor <;> linarith [hc.1, hc.2]
    have hshift := inverse_Gamma_add_nat_le z n (by simpa [him] using ht)
    have hsin : ‖Complex.sin (Real.pi * z)‖ ≤ Real.exp (Real.pi * |t|) := by
      have h := norm_sin_le_exp (Real.pi * z)
      simpa only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, him,
        abs_mul, abs_of_nonneg Real.pi_pos.le] using h
    have hbound : ‖(Complex.Gamma z)⁻¹‖ ≤
        (M / Real.pi) * Real.exp (Real.pi * |t|) := by
      rw [inverse_reflection himne, norm_div, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      have hnum := mul_le_mul ((norm_Gamma_le_real hre).trans (hMG _ hreal)) hsin
        (norm_nonneg _) hM
      have hd := div_le_div_of_nonneg_right hnum Real.pi_pos.le
      convert hd using 1 <;> ring
    calc
      _ ≤ ‖(Complex.Gamma z)⁻¹‖ := by simpa [z] using hshift
      _ ≤ (M / Real.pi) * Real.exp (Real.pi * |t|) := hbound
      _ ≤ C * Real.exp (Real.pi * |t|) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · have htr : t ∈ Icc (-1 : ℝ) 1 := by
      have h := abs_lt.mp (lt_of_not_ge ht)
      exact ⟨h.1.le, h.2.le⟩
    have hb := hB (c, t) ⟨hc, htr⟩
    have hC : B ≤ C := (le_max_left B 0).trans (le_max_left _ _)
    exact hb.trans (hC.trans (le_mul_of_one_le_right
      ((le_max_right B 0).trans (le_max_left _ _))
      (Real.one_le_exp (mul_nonneg Real.pi_pos.le (abs_nonneg t)))))

end ThetaGlobal.GammaReciprocalGrowth

#print axioms ThetaGlobal.GammaReciprocalGrowth.inverse_Gamma_strip_bound
end

end Verification_GammaReciprocalGrowth
/- END SOURCE BODY: ThetaGlobal/GammaReciprocalGrowth.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/GammaProfileGrowth.lean -/
section Verification_GammaProfileGrowth


/-!
# The finite Gamma profile has the required strip growth

This discharges the reciprocal-Gamma growth hypothesis of the scalar
deconvolver from the actual Gamma function.  The proof uses Euler reflection
and finite products; no separate Stirling assumption remains.
-/


set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GammaProfileGrowth

open Set MeasureTheory
open GaussianStripDecay GammaDeconvolver GammaReciprocalGrowth
open scoped BigOperators Classical

theorem growth_one : ExponentialStripGrowth (fun _ : ℂ => (1 : ℂ)) := by
  intro a b _
  refine ⟨1, zero_le_one, 0, 0, ?_⟩
  intro c hc t
  simp

theorem growth_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ j ∈ s, ExponentialStripGrowth (f j)) :
    ExponentialStripGrowth (fun z => ∏ j ∈ s, f j z) := by
  induction s using Finset.induction_on with
  | empty => simpa using growth_one
  | @insert j s hj ih =>
    simp only [Finset.prod_insert hj]
    apply (hf j (Finset.mem_insert_self _ _)).mul
    exact ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))

theorem shifted_reciprocal_growth (shift radial : ℝ) :
    ExponentialStripGrowth (fun z : ℂ =>
      (Complex.Gamma ((shift : ℂ) + z + Complex.I * (radial : ℂ)))⁻¹) := by
  intro a b _
  obtain ⟨C, hC, hbound⟩ := inverse_Gamma_strip_bound (shift + a) (shift + b)
  refine ⟨C * Real.exp (Real.pi * |radial|), by positivity, Real.pi, 0, ?_⟩
  intro c hc t
  have he : (shift : ℂ) + ((c : ℂ) + (t : ℂ) * Complex.I) +
      Complex.I * (radial : ℂ) =
        ((shift + c : ℝ) : ℂ) + ((t + radial : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  dsimp only
  rw [he, pow_zero, mul_one]
  have h := hbound (shift + c) ⟨by linarith [hc.1], by linarith [hc.2]⟩ (t + radial)
  have hexp : Real.exp (Real.pi * |t + radial|) ≤
      Real.exp (Real.pi * |radial|) * Real.exp (Real.pi * |t|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (abs_add_le t radial) Real.pi_pos.le
    nlinarith
  exact h.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hexp hC)

theorem scalar_exp_growth (C : ℂ) (L : ℝ) :
    ExponentialStripGrowth (fun z : ℂ => C * Complex.exp (-((L : ℂ) * z))) := by
  intro a b _
  refine ⟨‖C‖ * Real.exp (|L| * (|a| + |b|)), by positivity, 0, 0, ?_⟩
  intro c hc t
  have hcabs : |c| ≤ |a| + |b| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le a, abs_nonneg b, hc.1]
    · linarith [le_abs_self b, abs_nonneg a, hc.2]
  have hLc : -(L * c) ≤ |L| * (|a| + |b|) := by
    calc
      -(L * c) ≤ |L * c| := neg_le_abs _
      _ = |L| * |c| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hcabs (abs_nonneg L)
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, zero_sub, add_zero, pow_zero,
    zero_mul, Real.exp_zero, mul_one]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hLc) (norm_nonneg C)

variable {ι : Type*} [Fintype ι] (p : GammaProfile ι)

theorem reciprocalGamma_growth : ExponentialStripGrowth (reciprocalGamma p) := by
  unfold reciprocalGamma
  apply (scalar_exp_growth p.C₀⁻¹ (Real.log p.A₀)).mul
  exact growth_prod Finset.univ _ (fun j _ => shifted_reciprocal_growth (p.shift j) (p.radial j))

/-- The deconvolver is now constructed from the Gamma profile and the
annular transform alone; reciprocal-Gamma growth is a theorem. -/
def canonicalDeconvolver (Vhat : ℂ → ℂ)
    (hV : Differentiable ℂ Vhat) (hVstrip : BoundedOnVerticalStrips Vhat)
    (ε : ℝ) (hε : 0 < ε) :
    AnnularTransfer.DeconvolverData
      (fun t : ℝ => directGamma p ((t : ℂ) * Complex.I))
      (fun t : ℝ => Vhat ((t : ℂ) * Complex.I)) ε :=
  gammaDeconvolver p Vhat hV hVstrip (reciprocalGamma_growth p) ε hε

theorem canonicalDeconvolver_all_power_moments (Vhat : ℂ → ℂ)
    (hV : Differentiable ℂ Vhat) (hVstrip : BoundedOnVerticalStrips Vhat)
    (ε : ℝ) (hε : 0 < ε) (q : ℝ) :
    IntegrableOn
      (fun t => ‖DeconvolverMoments.multiplicativeInverse
        (canonicalDeconvolver p Vhat hV hVstrip ε hε).spectrum t‖ * t ^ q / t)
      (Ioi 0) :=
  gammaDeconvolver_all_power_moments p Vhat hV hVstrip (reciprocalGamma_growth p) ε hε q

end ThetaGlobal.GammaProfileGrowth

#print axioms ThetaGlobal.GammaProfileGrowth.reciprocalGamma_growth
#print axioms ThetaGlobal.GammaProfileGrowth.canonicalDeconvolver_all_power_moments
end

end Verification_GammaProfileGrowth
/- END SOURCE BODY: ThetaGlobal/GammaProfileGrowth.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/GlobalProjectOrbitAbsolute.lean -/
section Verification_GlobalProjectOrbitAbsolute

/-!
# Full-sheet unfolding from absolute fundamental-domain pieces

An integrability hypothesis for the full noncompact sheet is unnecessary
once the actual Fourier coefficients already give an absolutely summable
family of integrable orbit pieces.  The fundamental-domain partition
turns precisely those estimates into full-sheet integrability.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalProjectOrbitAbsolute

open MeasureTheory Set
open scoped BigOperators Pointwise

variable {Γ X Y : Type*} [Group Γ] [Countable Γ]
  [MeasurableSpace X] [MeasurableSpace Y] [MulAction Γ X]
  [MeasurableConstSMul Γ X] {μ : Measure X} {ν : Measure Y}
  [SMulInvariantMeasure Γ X μ]

theorem integrable_of_orbit_pieces {Ω : Set X}
    (hΩ : IsFundamentalDomain Γ Ω μ) (g : X → ℂ)
    (hi : ∀ γ : Γ, IntegrableOn (fun x => g (γ • x)) Ω μ)
    (hs : Summable (fun γ : Γ => ∫ x in Ω, ‖g (γ • x)‖ ∂μ)) :
    Integrable g μ := by
  rw [← hΩ.sum_restrict]
  apply integrable_sum_measure
  · intro γ
    exact ((measurePreserving_smul γ μ).integrableOn_image
      (measurableEmbedding_const_smul γ)).mpr (hi γ)
  · apply hs.congr
    intro γ
    exact ((measurePreserving_smul γ μ).setIntegral_image_emb
      (measurableEmbedding_const_smul γ) (fun x => ‖g x‖) Ω).symm

/-- The exact weighted unfolding from the already proved Fourier mass
estimates.  The scalar may vanish: the coefficient is kept inside the
profile, so no division by a possibly zero exterior coefficient occurs. -/
theorem weighted_unfold_of_pieces {Ω : Set X}
    (hΩ : IsFundamentalDomain Γ Ω μ)
    (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (weight : X → ℂ) (targetWeight : Y → ℂ) (f : Y → ℂ) (c : ℂ)
    (hΓ : ∀ (γ : Γ) (x : X), weight (γ • x) = weight x)
    (htransport : ∀ x, weight x = c * targetWeight (e x))
    (hi : ∀ γ : Γ,
      IntegrableOn (fun x => weight x * f (e (γ • x))) Ω μ)
    (hs : Summable (fun γ : Γ =>
      ∫ x in Ω, ‖weight x * f (e (γ • x))‖ ∂μ)) :
    Summable (fun γ : Γ => ∫ x in Ω, weight x * f (e (γ • x)) ∂μ) ∧
      (∑' γ : Γ, ∫ x in Ω, weight x * f (e (γ • x)) ∂μ) =
        c * ∫ y, targetWeight y * f y ∂ν := by
  let g : X → ℂ := fun x => weight x * f (e x)
  have hp (γ : Γ) (x : X) : g (γ • x) = weight x * f (e (γ • x)) := by
    simp only [g, hΓ]
  have hg : Integrable g μ := integrable_of_orbit_pieces hΩ g
    (fun γ => (hi γ).congr (Filter.Eventually.of_forall fun x => (hp γ x).symm))
    (hs.congr fun γ => by simp only [hp])
  refine ⟨?_, ?_⟩
  · apply Summable.of_norm_bounded hs
    intro γ
    exact norm_integral_le_integral_norm _
  · calc
      _ = ∑' γ : Γ, ∫ x in Ω, g (γ • x) ∂μ := by
        apply tsum_congr
        intro γ
        apply integral_congr_ae
        filter_upwards [] with x
        exact (hp γ x).symm
      _ = ∫ x, g x ∂μ := (hΩ.integral_eq_tsum'' g hg).symm
      _ = ∫ x, c * (targetWeight (e x) * f (e x)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [g, htransport x, mul_assoc]
      _ = c * ∫ x, targetWeight (e x) * f (e x) ∂μ := integral_const_mul _ _
      _ = c * ∫ y, targetWeight y * f y ∂ν := by
        rw [he.integral_comp' (fun y => targetWeight y * f y)]

end ThetaGlobal.GlobalProjectOrbitAbsolute

#print axioms ThetaGlobal.GlobalProjectOrbitAbsolute.weighted_unfold_of_pieces
end

end Verification_GlobalProjectOrbitAbsolute
/- END SOURCE BODY: ThetaGlobal/GlobalProjectOrbitAbsolute.lean -/

/- BEGIN SOURCE BODY: ThetaGlobal/ReflectedAudit.lean -/
section Verification_ReflectedAudit

#print axioms ThetaGlobal.ReflectedAbsolute.ZeroOrUnitNorm.zpow
#print axioms ThetaGlobal.ReflectedAbsolute.cubic_scale_inverse_square_le
#print axioms ThetaGlobal.ReflectedAbsolute.summable_reflected_of_quadratic_tail
#print axioms ThetaGlobal.ReflectedLocalBounds.norm_finiteWeylCoefficient_le
#print axioms ThetaGlobal.ReflectedIdealMajorant.summable_positiveIdealNorm_inverseSquare
#print axioms ThetaGlobal.ReflectedIdealMajorant.summable_numberField_reflected_of_quadratic_tail
#print axioms ThetaGlobal.ReflectedCoefficientModel.norm_reflectedCoefficient_le
#print axioms ThetaGlobal.ReflectedCoefficientSummability.summable_numberField_subtype_reflectedTerm
#print axioms ThetaGlobal.ReflectedDominatedLimit.tendsto_tsum_numberField_subtype_reflectedTerm
#print axioms ThetaGlobal.ScalarMellinConvolution.deconvolver_direct
#print axioms ThetaGlobal.ScalarMellinConvolution.deconvolver_reflected
#print axioms ThetaGlobal.DeconvolverMoments.integrable_multiplicative_power_moment
#print axioms ThetaGlobal.AnnularTransfer.arbitrary_test_reflection
#print axioms ThetaGlobal.ScalarGaussianLimits.regularizedTest_tendsto_actual_test
#print axioms ThetaGlobal.GaussianStripDecay.quadraticStripDecay_regularized
#print axioms ThetaGlobal.GammaDeconvolver.reciprocalGamma_entire
#print axioms ThetaGlobal.GammaDeconvolver.directGamma_imaginary_ne_zero
#print axioms ThetaGlobal.GammaDeconvolver.gammaDeconvolver_all_power_moments
#print axioms ThetaGlobal.GammaAnnularTransfer.arbitrary_test_from_seed
end Verification_ReflectedAudit
/- END SOURCE BODY: ThetaGlobal/ReflectedAudit.lean -/
