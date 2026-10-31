import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

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
