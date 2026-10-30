import ThetaGlobal.FiniteShellCoefficients
import ThetaGlobal.FiniteClassExpansion

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
