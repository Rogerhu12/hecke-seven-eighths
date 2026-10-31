import HeckeSkeleton.Moments.MOM_BASE.CanonicalCalibration
import HeckeGeneral.Characters.InfinityPacket

/-! Finite twists preserve the actual infinity parameters and the
nonzero angular condition of the live canonical period. -/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_BASE

open NumberField HeckeGeneral.Characters

variable (K : Type) [Field K] [NumberField K]

theorem finiteTwist_radialParameter (ν θ : HeckeCharacter K) (hθ : FiniteOrder θ)
    (v : InfinitePlace K) :
    heckeRadialParameter K v (ν * θ) = heckeRadialParameter K v ν := by
  rw [heckeRadialParameter_mul, heckeRadialParameter_finiteOrder K v hθ, add_zero]

theorem finiteTwist_complexWeight (ν θ : HeckeCharacter K) (hθ : FiniteOrder θ)
    (v : InfinitePlace K) (hv : v.IsComplex) :
    heckeComplexWeight K v hv (ν * θ) = heckeComplexWeight K v hv ν := by
  rw [heckeComplexWeight_mul, heckeComplexWeight_finiteOrder K v hv hθ, add_zero]

theorem finiteTwist_nonzero_angular (ν θ : HeckeCharacter K) (hθ : FiniteOrder θ) :
    (∃ (v : InfinitePlace K) (hv : v.IsComplex),
      heckeComplexWeight K v hv (ν * θ) ≠ 0) ↔
    (∃ (v : InfinitePlace K) (hv : v.IsComplex),
      heckeComplexWeight K v hv ν ≠ 0) := by
  simp only [finiteTwist_complexWeight K ν θ hθ]

/-- The live period keeps both its continuous radial data and its angular
weight after either of the finite primitive transforms. -/
theorem canonicalPeriod_finiteTwist_parameters (c : TargetContext K)
    (ν θ : HeckeCharacter K) (hθ : FiniteOrder θ) :
    (∀ v : InfinitePlace K,
      heckeRadialParameter K v (canonicalPeriod K c (ν * θ)) =
        heckeRadialParameter K v (canonicalPeriod K c ν)) ∧
      (∀ (v : InfinitePlace K) (hv : v.IsComplex),
        heckeComplexWeight K v hv (canonicalPeriod K c (ν * θ)) =
          heckeComplexWeight K v hv (canonicalPeriod K c ν)) := by
  have he : canonicalPeriod K c (ν * θ) = canonicalPeriod K c ν * θ := by
    unfold canonicalPeriod
    exact (mul_assoc _ _ _).symm
  rw [he]
  exact ⟨finiteTwist_radialParameter K _ θ hθ,
    finiteTwist_complexWeight K _ θ hθ⟩

end HeckeSkeleton.Moments.MOM_BASE
