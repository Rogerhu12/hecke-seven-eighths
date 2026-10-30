import HeckeSkeleton.LowFrozenCube.Phases
import HeckeSkeleton.LowFrozenCube.LocalCoefficients

/-!
# Explicit frozen coefficient separation

This module isolates exactly the varying parts of the paper's `π`, `ρ`, and
`λ`: evaluation at `a_min*x^3` and the ordinary-prime interaction product.
All self-interactions, original slot weights, and fixed norm phases are
collected in the functions `a₀`, `ρ₀`, and `lam`.

The conclusions prove that the active-mark coefficient loses its cube
dependence, while the row coefficient contributes precisely `χ_d(x)^3`.
-/

namespace HeckeSkeleton.LowFrozenCube

open scoped BigOperators Classical

noncomputable section

variable {ι A : Type*} [CommMonoid A]

/-- Ordinary-prime factor occurring in the row and active-mark coefficients. -/
def negativeOrdinaryInteraction (F : Finset ι) (ψ : ι → A → ℂ)
    (j v : ι → ℕ) (a : A) : ℂ :=
  ∏ p ∈ F, ψ p a ^ (-2 * (localPhaseDigit (j p) (v p) : ℤ))

/-- Ordinary-prime factor occurring in the dual squarefree-column coefficient. -/
def positiveOrdinaryInteraction (F : Finset ι) (ψ : ι → A → ℂ)
    (j v : ι → ℕ) (a : A) : ℂ :=
  ∏ p ∈ F, ψ p a ^ localPhaseDigit (j p) (v p)

theorem negativeOrdinaryInteraction_frozen (F : Finset ι) (ψ : ι → A → ℂ)
    (j v : ι → ℕ) (hv : ∀ p, AdmissibleExponent (v p)) (a : A) :
    negativeOrdinaryInteraction F ψ j v a =
      negativeOrdinaryInteraction F ψ j (frozenBase v) a := by
  unfold negativeOrdinaryInteraction
  apply Finset.prod_congr rfl
  intro p hp
  rw [localPhaseDigit_frozen (j p) (v p) (hv p)]
  rfl

theorem positiveOrdinaryInteraction_frozen (F : Finset ι) (ψ : ι → A → ℂ)
    (j v : ι → ℕ) (hv : ∀ p, AdmissibleExponent (v p)) (a : A) :
    positiveOrdinaryInteraction F ψ j v a =
      positiveOrdinaryInteraction F ψ j (frozenBase v) a := by
  unfold positiveOrdinaryInteraction
  apply Finset.prod_congr rfl
  intro p hp
  rw [localPhaseDigit_frozen (j p) (v p) (hv p)]
  rfl

variable (χ : A → A →* ℂ) (Cop : A → A → Prop)

/-- The varying factors in `π_t(P)`, after product aggregation of its primes. -/
def markCoefficient (F : Finset ι) (ψ : ι → A → ℂ) (j v : ι → ℕ)
    (a₀ : A → ℂ) (a' P : A) : ℂ :=
  a₀ P * (χ P a') ^ 2 * negativeOrdinaryInteraction F ψ j v P

/-- The varying factors in `ρ_t(d)`. -/
def rowCoefficient (F : Finset ι) (ψ : ι → A → ℂ) (j v : ι → ℕ)
    (ρ₀ : A → ℂ) (a' d : A) : ℂ :=
  ρ₀ d * χ d a' * negativeOrdinaryInteraction F ψ j v d

/-- The varying factors in `λ_t(c')`. -/
def columnCoefficient (F : Finset ι) (ψ : ι → A → ℂ) (j v : ι → ℕ)
    (lam : A → ℂ) (a' c : A) : ℂ :=
  lam c * (χ c a') ^ 2 * positiveOrdinaryInteraction F ψ j v c

/-- The active-mark coefficient depends on the frozen minimum, not on `x`.
Its fixed-prime disjointness is used exactly in the sixth-power cancellation. -/
theorem markCoefficient_frozen
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0)
    (F : Finset ι) (ψ : ι → A → ℂ) (j v : ι → ℕ)
    (hv : ∀ p, AdmissibleExponent (v p)) (a₀ : A → ℂ)
    (amin x P : A) (hPx : Cop P x) :
    markCoefficient χ F ψ j v a₀ (amin * x ^ 3) P =
      markCoefficient χ F ψ j (frozenBase v) a₀ amin P := by
  unfold markCoefficient
  rw [map_mul, mul_pow, frozen_cube_square_phase χ Cop h6 P x hPx,
    negativeOrdinaryInteraction_frozen F ψ j v hv P]
  simp

/-- The column coefficient has the same frozen-cube independence. -/
theorem columnCoefficient_frozen
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0)
    (F : Finset ι) (ψ : ι → A → ℂ) (j v : ι → ℕ)
    (hv : ∀ p, AdmissibleExponent (v p)) (lam : A → ℂ)
    (amin x c : A) (hcx : Cop c x) :
    columnCoefficient χ F ψ j v lam (amin * x ^ 3) c =
      columnCoefficient χ F ψ j (frozenBase v) lam amin c := by
  unfold columnCoefficient
  rw [map_mul, mul_pow, frozen_cube_square_phase χ Cop h6 c x hcx,
    positiveOrdinaryInteraction_frozen F ψ j v hv c]
  simp

/-- The row coefficient retains exactly the cubic row phase which must stay
inside the hybrid sum.  No coprimality hypothesis is needed for this identity. -/
theorem rowCoefficient_frozen (F : Finset ι) (ψ : ι → A → ℂ)
    (j v : ι → ℕ) (hv : ∀ p, AdmissibleExponent (v p)) (ρ₀ : A → ℂ)
    (amin x d : A) :
    rowCoefficient χ F ψ j v ρ₀ (amin * x ^ 3) d =
      rowCoefficient χ F ψ j (frozenBase v) ρ₀ amin d * (χ d x) ^ 3 := by
  unfold rowCoefficient
  rw [map_mul, map_pow, negativeOrdinaryInteraction_frozen F ψ j v hv d]
  ring

end

end HeckeSkeleton.LowFrozenCube
