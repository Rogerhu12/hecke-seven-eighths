import ThetaGlobal.GlobalFrequency
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import Mathlib.FieldTheory.Extension
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Module.Multilinear.Topology

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
