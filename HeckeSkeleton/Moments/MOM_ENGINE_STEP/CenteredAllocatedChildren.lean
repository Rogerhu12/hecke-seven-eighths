import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocationKernel
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocatedChildProvider

/-!
# Centered allocations are compared only after actual child calibration

The original subtraction remains inside the allocated Fourier polynomial.
Once both rectangles have genuine nonexceptional child term dictionaries,
weighted Minkowski gives their two actual child square-root energies.
No centered coefficient is split at either Poisson transform or at the
prime-pool operation.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open DedekindZetaZeroFree

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem sqrt_joint_energy_sub {H ι : Type*} (rows : Finset H) (columns : Finset ι)
    (q : H → ℂ) (c f : H → ι → ℂ) (x : H → ι → V) (ξ : V) :
    Real.sqrt (jointColumnEnergy rows columns q (fun h i => c h i - f h i) x ξ) ≤
      Real.sqrt (jointColumnEnergy rows columns q c x ξ) +
        Real.sqrt (jointColumnEnergy rows columns q f x ξ) := by
  have he (h : H) :
      jointFourierColumn columns (fun i => c h i - f h i) (x h) ξ =
        jointFourierColumn columns (c h) (x h) ξ - jointFourierColumn columns (f h) (x h) ξ := by
    simp only [jointFourierColumn, sub_mul, Finset.sum_sub_distrib]
  unfold jointColumnEnergy
  simp_rw [he]
  simpa only [sub_eq_add_neg, norm_neg] using
    sqrt_row_energy_add rows q
      (fun h => jointFourierColumn columns (c h) (x h) ξ)
      (fun h => -jointFourierColumn columns (f h) (x h) ξ)

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {H : Type*} {k : ℕ} {ω ψ : HeckeCharacter F}

namespace ActualAllocatedSource

/-- The comparison rectangle changes only its two original plain scales
and weights.  The entire actual allocation, masks, row map, characters,
prime slots, and Fourier locations are shared. -/
def comparison (s : ActualAllocatedSource A V H k) (N₁ N₂ : ℝ)
    (w₁ w₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → ℂ) :
    ActualAllocatedSource A V H k :=
  { s with scale₁ := N₁, scale₂ := N₂, leftWeight := w₁, rightWeight := w₂ }

def centeredEnergy (s : ActualAllocatedSource A V H k) (N₁ N₂ : ℝ)
    (w₁ w₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → ℂ) (ξ : V) : ℝ :=
  jointColumnEnergy s.rows s.allocation.columns s.weight
    (fun h => fun v =>
      rawSourceCoefficient (σ := σ) (s.characters h) (s.extractedFactor h) (s.row h).element
        s.scale₁ s.scale₂ s.base s.length (s.leftWeight h) (s.rightWeight h) (s.slotWeight h) v -
      rawSourceCoefficient (σ := σ) (s.characters h) (s.extractedFactor h) (s.row h).element
        N₁ N₂ s.base s.length (w₁ h) (w₂ h) (s.slotWeight h) v)
    (fun h => rawSourceLocation (s.leftLocation h) (s.rightLocation h) (s.slotLocation h)) ξ

theorem centered_sqrt_energy_le (s : ActualAllocatedSource A V H k) (N₁ N₂ : ℝ)
    (w₁ w₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → ℂ) (ξ : V) :
    Real.sqrt (s.centeredEnergy (σ := σ) N₁ N₂ w₁ w₂ ξ) ≤
      Real.sqrt (s.energy (σ := σ) ξ) +
        Real.sqrt ((s.comparison N₁ N₂ w₁ w₂).energy (σ := σ) ξ) :=
  sqrt_joint_energy_sub _ _ _ _ _ _ _

/-- Both actual arithmetic/profile dictionaries are required before the
centered branch is dominated by ordinary actual child moments. -/
theorem centered_sqrt_energy_le_actual_children
    (s : ActualAllocatedSource A V H k) (N₁ N₂ : ℝ)
    (w₁ w₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (left : s.Calibration (σ := σ) ω ψ)
    (right : (s.comparison N₁ N₂ w₁ w₂).Calibration (σ := σ) ω ψ)
    (ξ : V) :
    Real.sqrt (s.centeredEnergy (σ := σ) N₁ N₂ w₁ w₂ ξ) ≤
      Real.sqrt left.mass *
        Real.sqrt (pairedEnergy (left.clippedData ξ) left.clippedParameters s.base (left.height ξ)) +
      Real.sqrt right.mass *
        Real.sqrt (pairedEnergy (right.clippedData ξ) right.clippedParameters s.base (right.height ξ)) := by
  apply (s.centered_sqrt_energy_le N₁ N₂ w₁ w₂ ξ).trans
  apply add_le_add
  · exact (Real.sqrt_le_sqrt (left.energy_le_clipped ξ)).trans_eq
      (Real.sqrt_mul left.mass_nonneg _)
  · exact (Real.sqrt_le_sqrt (right.energy_le_clipped ξ)).trans_eq
      (Real.sqrt_mul right.mass_nonneg _)

end ActualAllocatedSource

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.centered_sqrt_energy_le_actual_children
