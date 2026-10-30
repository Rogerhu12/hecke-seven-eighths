import Mathlib.NumberTheory.GaussSum
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The actual finite Fourier algebra for periodic orbital Poisson

The positive-sign unnormalized transform is the finite transform in the
extension manuscript, lines 619–660, and `docs/NEXT_POISSON.md`:
`hat(f)_d(h) = sum_a f(d*a) e(h*a/c)`.
Here the finite ring is an actual ring (eventually R/cR), and its additive
character is an actual `AddChar`. No arithmetic or analytic estimate is
recorded as a field of an input structure.

Dilation of an arbitrary function is retained inside the transform. Only
the multiplicative-character specialization factors it as χ(d)χ(a).
Unit invariance is transported by an actual bijective change of residue
variables. Inversion uses the algebraic nondegeneracy property
`AddChar.IsPrimitive`, and derives finite character orthogonality.

This file does not construct the trace pairing on an S-integer quotient,
prove its primitivity, or establish lattice/orbital Poisson.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic.PeriodicFourier

open scoped BigOperators

variable {R : Type*} [CommRing R] [Fintype R]

/-- Positive-sign, unnormalized finite Fourier transform. -/
def fourier (ψ : AddChar R ℂ) (f : R → ℂ) (h : R) : ℂ :=
  ∑ a : R, f a * ψ (h * a)

/-- Dilation keeps the full periodic coefficient, including its zero extensions. -/
def dilate (d : R) (f : R → ℂ) (a : R) : ℂ := f (d * a)

/-- The finite transform that occurs after expanding a moving mask divisor. -/
def divisorTransform (ψ : AddChar R ℂ) (f : R → ℂ) (d h : R) : ℂ :=
  fourier ψ (dilate d f) h

@[simp] theorem divisorTransform_apply (ψ : AddChar R ℂ) (f : R → ℂ) (d h : R) :
    divisorTransform ψ f d h = ∑ a : R, f (d * a) * ψ (h * a) := rfl

/-- The zero-frequency coefficient is the actual finite sum, not a discarded term. -/
@[simp] theorem fourier_zero (ψ : AddChar R ℂ) (f : R → ℂ) :
    fourier ψ f 0 = ∑ a : R, f a := by
  simp [fourier]

@[simp] theorem divisorTransform_zero (ψ : AddChar R ℂ) (f : R → ℂ) (d : R) :
    divisorTransform ψ f d 0 = ∑ a : R, f (d * a) := by
  simp [divisorTransform, dilate]

theorem fourier_add (ψ : AddChar R ℂ) (f g : R → ℂ) (h : R) :
    fourier ψ (fun a => f a + g a) h = fourier ψ f h + fourier ψ g h := by
  simp [fourier, add_mul, Finset.sum_add_distrib]

theorem fourier_const_mul (ψ : AddChar R ℂ) (f : R → ℂ) (c : ℂ) (h : R) :
    fourier ψ (fun a => c * f a) h = c * fourier ψ f h := by
  simp [fourier, Finset.mul_sum, mul_assoc]

/-- Finite linear mask expansions are transformed term by term before any specialization. -/
theorem fourier_sum {ι : Type*} (s : Finset ι) (ψ : AddChar R ℂ)
    (f : ι → R → ℂ) (h : R) :
    fourier ψ (fun a => ∑ i ∈ s, f i a) h = ∑ i ∈ s, fourier ψ (f i) h := by
  classical
  simp only [fourier, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Dilation by a unit transports frequency by the inverse unit. -/
theorem fourier_dilate_unit (ψ : AddChar R ℂ) (f : R → ℂ) (u : Rˣ) (h : R) :
    fourier ψ (dilate (u : R) f) h = fourier ψ f ((u⁻¹ : Rˣ) * h) := by
  unfold fourier dilate
  refine Fintype.sum_bijective _ u.mulLeft_bijective _ _ (fun a => ?_)
  congr 1
  congr 1
  simp [mul_comm, mul_left_comm, mul_assoc]

/-- A periodic function invariant under unit multiplication has an invariant dual transform. -/
theorem fourier_unit_invariant (ψ : AddChar R ℂ) (f : R → ℂ) (u : Rˣ)
    (hf : ∀ a : R, f ((u : R) * a) = f a) (h : R) :
    fourier ψ f ((u : R) * h) = fourier ψ f h := by
  unfold fourier
  refine Fintype.sum_bijective _ u.mulLeft_bijective _ _ (fun a => ?_)
  rw [hf]
  congr 1
  congr 1
  ring

/-- Invariance under a subgroup of units is a property of the actual finite function. -/
def UnitInvariant (Γ : Subgroup Rˣ) (f : R → ℂ) : Prop :=
  ∀ u ∈ Γ, ∀ a : R, f ((u : R) * a) = f a

omit [Fintype R] in
theorem dilate_unitInvariant (Γ : Subgroup Rˣ) (f : R → ℂ)
    (hf : UnitInvariant Γ f) (d : R) : UnitInvariant Γ (dilate d f) := by
  intro u hu a
  unfold dilate
  rw [show d * ((u : R) * a) = (u : R) * (d * a) by ring]
  exact hf u hu (d * a)

/-- Gamma invariance survives the divisor pullback and the full finite transform. -/
theorem divisorTransform_unitInvariant (Γ : Subgroup Rˣ) (ψ : AddChar R ℂ)
    (f : R → ℂ) (hf : UnitInvariant Γ f) (d : R) :
    UnitInvariant Γ (divisorTransform ψ f d) := by
  intro u hu h
  exact fourier_unit_invariant ψ (dilate d f) u (dilate_unitInvariant Γ f hf d u hu) h

/-- Only genuine multiplicativity allows extracting a divisor coefficient. -/
theorem divisorTransform_mulChar (ψ : AddChar R ℂ) (χ : MulChar R ℂ) (d h : R) :
    divisorTransform ψ χ d h = χ d * fourier ψ χ h := by
  simp [divisorTransform, dilate, fourier, map_mul, Finset.mul_sum, mul_assoc]

/-- Nonunit divisor values retain the original multiplicative zero extension. -/
theorem divisorTransform_mulChar_nonunit (ψ : AddChar R ℂ) (χ : MulChar R ℂ)
    (d h : R) (hd : ¬ IsUnit d) : divisorTransform ψ χ d h = 0 := by
  rw [divisorTransform_mulChar, MulChar.map_nonunit χ hd, zero_mul]

/-- The transform of a multiplicative character is its actual shifted Gauss sum. -/
theorem fourier_mulChar (ψ : AddChar R ℂ) (χ : MulChar R ℂ) (h : R) :
    fourier ψ χ h = gaussSum χ (ψ.mulShift h) := rfl

/-- Unit frequencies specialize through a genuine finite Gauss-sum change of variables.

This does not claim vanishing at nonunit frequencies for an arbitrary χ.
-/
theorem fourier_mulChar_unit (ψ : AddChar R ℂ) (χ : MulChar R ℂ) (u : Rˣ) :
    fourier ψ χ u = χ⁻¹ u * gaussSum χ ψ := by
  rw [fourier_mulChar]
  exact gaussSum_mulShift_eq χ ψ u

/-- Primitive additive pairing gives actual finite orthogonality. -/
theorem pairing_orthogonality [DecidableEq R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (b : R) :
    ∑ h : R, ψ (h * b) = if b = 0 then (Fintype.card R : ℂ) else 0 := by
  classical
  simpa only [Nat.cast_ite, Nat.cast_zero] using AddChar.sum_mulShift (R' := ℂ) b hψ

/-- The opposite-sign Fourier sum recovers cardinality times the original function. -/
theorem inversion_sum (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (f : R → ℂ) (x : R) :
    ∑ h : R, fourier ψ f h * ψ (-(h * x)) = (Fintype.card R : ℂ) * f x := by
  classical
  unfold fourier
  simp_rw [Finset.sum_mul, mul_assoc, ← ψ.map_add_eq_mul,
    show ∀ h a : R, h * a + -(h * x) = h * (a - x) by intros; ring]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, pairing_orthogonality ψ hψ, sub_eq_zero,
    mul_ite, mul_zero]
  simp [mul_comm]

/-- Opposite-sign normalized inverse, defined from the actual finite sum. -/
def inverse (ψ : AddChar R ℂ) (g : R → ℂ) (x : R) : ℂ :=
  (Fintype.card R : ℂ)⁻¹ * ∑ h : R, g h * ψ (-(h * x))

theorem inverse_fourier (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (f : R → ℂ) (x : R) :
    inverse ψ (fourier ψ f) x = f x := by
  have hcard : (Fintype.card R : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold inverse
  rw [inversion_sum ψ hψ f x, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- The correct Fourier rule for an arbitrary divisor, even when multiplication is not bijective.

All solutions of d*k = h are retained. This is not the invalid extraction
of a factor f(d) from f(d*a) for a general periodic function.
-/
theorem fourier_dilate_fibers [DecidableEq R] (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (f : R → ℂ) (d h : R) :
    fourier ψ (dilate d f) h =
      ∑ k : R, if d * k = h then fourier ψ f k else 0 := by
  classical
  have hcard : (Fintype.card R : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hfexp : dilate d f = fun a =>
      (Fintype.card R : ℂ)⁻¹ * ∑ k : R, fourier ψ f k * ψ (-(k * (d * a))) := by
    funext a
    exact (inverse_fourier ψ hψ f (d * a)).symm
  have hk (k : R) :
      fourier ψ (fun a => fourier ψ f k * ψ (-(k * (d * a)))) h =
        fourier ψ f k * (if d * k = h then (Fintype.card R : ℂ) else 0) := by
    unfold fourier
    simp_rw [mul_assoc, ← ψ.map_add_eq_mul,
      show ∀ a : R, -(k * (d * a)) + h * a = a * (h - d * k) by intros; ring]
    rw [← Finset.mul_sum, pairing_orthogonality ψ hψ (h - d * k)]
    simp [sub_eq_zero, eq_comm]
  rw [hfexp, fourier_const_mul]
  rw [fourier_sum Finset.univ ψ (fun k a => fourier ψ f k * ψ (-(k * (d * a)))) h]
  simp_rw [hk, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp [mul_comm, hcard]

/-- Finite Poisson pairing, with signs and the unnormalized transform made explicit. -/
theorem finite_poisson (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (f g : R → ℂ) :
    (Fintype.card R : ℂ) * (∑ a : R, f a * g a) =
      ∑ h : R, fourier ψ f h * fourier ψ g (-h) := by
  classical
  symm
  calc
    (∑ h : R, fourier ψ f h * fourier ψ g (-h)) =
        ∑ h : R, ∑ a : R, (fourier ψ f h * ψ (-(h * a))) * g a := by
      apply Finset.sum_congr rfl
      intro h _
      change fourier ψ f h * (∑ a : R, g a * ψ ((-h) * a)) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [neg_mul]
      ring
    _ = ∑ a : R, (∑ h : R, fourier ψ f h * ψ (-(h * a))) * g a := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ = ∑ a : R, ((Fintype.card R : ℂ) * f a) * g a := by
      simp_rw [inversion_sum ψ hψ f]
    _ = (Fintype.card R : ℂ) * (∑ a : R, f a * g a) := by
      simp [Finset.mul_sum, mul_assoc]

end HeckeGeneral.Arithmetic.PeriodicFourier
