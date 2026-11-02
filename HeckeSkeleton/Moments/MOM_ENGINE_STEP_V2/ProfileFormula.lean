import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.EstimateData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLogProfiles

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# One global formula for the original transformed profiles

An equality only at the finite ideal norms does not determine a smooth
profile. This formula fixes its value on every real argument. It uses
one original Schwartz representative, one positive dilation, one real
power and one linear Fourier log phase. Conjugation handles both sides.
The phase translation is unrestricted: it is constant in the profile
argument and has unit norm, so it does not affect a Schwartz seminorm.
-/

noncomputable section
open scoped Classical SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open HeckeGeneral.Analysis

structure ProfileShape where
  dilationLower : ℝ
  dilationUpper : ℝ
  dilationLower_pos : 0 < dilationLower
  dilation_interval : dilationLower ≤ dilationUpper
  powerBound : ℝ
  powerBound_nonneg : 0 ≤ powerBound
  phaseBound : ℝ
  phaseBound_nonneg : 0 ≤ phaseBound

/-- All coefficients are finite-dimensional original data. In the
arithmetic dictionary `original` is a specified parent representative,
not a freely chosen function agreeing only on a finite set. -/
structure ProfileFormula where
  original : SchwartzMap ℝ ℂ
  conjugate : Bool
  dilation : ℝ
  dilation_pos : 0 < dilation
  scalar : ℂ
  power : ℝ
  phase : ℝ × ℝ
  translation : ℝ × ℝ

namespace ProfileFormula

def linear (a : ℝ × ℝ) (ξ : EngineParameter) : ℝ :=
  a.1 * (WithLp.ofLp ξ).1 + a.2 * (WithLp.ofLp ξ).2

def value (f : ProfileFormula) (ξ : EngineParameter) (x : ℝ) : ℂ :=
  if 0 < x then
    f.scalar *
      (if f.conjugate then star (f.original (f.dilation * x))
       else f.original (f.dilation * x)) *
      (x ^ f.power : ℝ) *
      Complex.exp (((2 * Real.pi *
        (linear f.phase ξ * Real.log x + linear f.translation ξ) : ℝ) : ℂ) * Complex.I)
  else 0

/-- These are uniform bounds on the actual dilation, real power and
log-frequency coefficients. The original scalar is paid separately. -/
structure Bounded (f : ProfileFormula) (shape : ProfileShape) : Prop where
  dilation_lower : shape.dilationLower ≤ f.dilation
  dilation_upper : f.dilation ≤ shape.dilationUpper
  power : |f.power| ≤ shape.powerBound
  phase_first : |f.phase.1| ≤ shape.phaseBound
  phase_second : |f.phase.2| ≤ shape.phaseBound

def window (f : ProfileFormula) (lower upper : ℝ) : Set ℝ :=
  Set.Icc (lower / f.dilation) (upper / f.dilation)

/-- The representatives are global functions and retain the exact
transformed support. No finite ideal-value interpolation is permitted. -/
structure SchwartzControl (f : ProfileFormula) (lower upper : ℝ)
    (orders : Finset (ℕ × ℕ)) (coefficient : ℝ) (degree : ℕ) where
  representative : EngineParameter → SchwartzMap ℝ ℂ
  value_eq : ∀ ξ x, representative ξ x = f.value ξ x
  support : ∀ ξ, Function.support (representative ξ) ⊆ f.window lower upper
  bound : ∀ ξ,
    orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (representative ξ) ≤
      EngineStep.polynomialProfileRadius coefficient degree degree (WithLp.ofLp ξ)

end ProfileFormula

/-- The degree and required input orders precede every original moving
profile. The later common-kernel estimate consumes this very witness. -/
structure ProfileFormulaCertificate (shape : ProfileShape) (lower upper : ℝ)
    (orders : Finset (ℕ × ℕ)) where
  inputOrders : Finset (ℕ × ℕ)
  degree : ℕ
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  control : ∀ (f : ProfileFormula), f.Bounded shape →
    Function.support f.original ⊆ Set.Icc lower upper →
    ∀ (amplitude scalarBound : ℝ), 0 ≤ amplitude → 0 ≤ scalarBound →
    inputOrders.sup (schwartzSeminormFamily ℂ ℝ ℂ) f.original ≤ amplitude →
    ‖f.scalar‖ ≤ scalarBound →
    Nonempty (f.SchwartzControl lower upper orders
      (coefficient * amplitude * scalarBound) degree)

/-- The analytic blueprint obligation, with every uniform choice made
before the individual original profile. -/
def ProfileFormulaTask : Prop :=
  ∀ (shape : ProfileShape) (lower upper : ℝ),
    0 < lower → lower ≤ upper → ∀ orders : Finset (ℕ × ℕ),
      Nonempty (ProfileFormulaCertificate shape lower upper orders)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
