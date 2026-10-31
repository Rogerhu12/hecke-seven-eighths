import ThetaGlobal.GlobalMarks
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.GroupTheory.QuotientGroup.Basic

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
