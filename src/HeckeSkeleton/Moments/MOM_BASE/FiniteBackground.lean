import HeckeSkeleton.Moments.MOM_BASE.CanonicalCalibration
import HeckeGeneral.Characters.InfinityPacket
import HeckeAxiom.LambdaInfinityType
import HeckeGeneral.Analysis.MomentInputs

/-! Finite twists preserve the actual infinity parameters and the
nonzero angular condition of the live canonical period.  The two canonical
background classes obtain that nonzero condition from the actual target
orientation and the calibrated angular weight of Λ. -/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_BASE

open NumberField HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments

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

/-- The finite part of the canonical background class has a nonzero
angular period for the actual target choice: Λ has weight ±1 and every
finite-order background has weight zero. -/
theorem canonicalPeriod_finite_nonzero_angular (c : TargetContext K)
    (θ : HeckeCharacter K) (hθ : FiniteOrder θ) :
    ∃ (v : InfinitePlace K) (hv : v.IsComplex),
      heckeComplexWeight K v hv (canonicalPeriod K c θ) ≠ 0 := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace K))
  have hv := isComplex_of_family K c v
  refine ⟨v, hv, ?_⟩
  rw [canonicalPeriod, heckeComplexWeight_mul, heckeComplexWeight_inv,
    heckeComplexWeight_finiteOrder K v hv hθ, add_zero]
  rcases (axiomChoice K c).Lambda_weight v hv with h | h <;> rw [h] <;> norm_num

/-- The ψΘ part has the nonzero angular period selected by the actual
target orientation.  Its finite factors, including G, contribute zero
angular weight at the same place. -/
theorem canonicalPeriod_target_finite_nonzero_angular (c : TargetContext K)
    (θ : HeckeCharacter K) (hθ : FiniteOrder θ) :
    ∃ (v : InfinitePlace K) (hv : v.IsComplex),
      heckeComplexWeight K v hv (canonicalPeriod K c (targetCharacter K c * θ)) ≠ 0 := by
  have hΛ : ∀ (v : InfinitePlace K) (hv : v.IsComplex),
      heckeComplexWeight K v hv (signalCharacters K c).1 = 1 ∨
        heckeComplexWeight K v hv (signalCharacters K c).1 = -1 :=
    fun v hv => (axiomChoice K c).Lambda_weight v hv
  have hG : FiniteOrder (signalCharacters K c).2 := canonical_G_finiteOrder K c
  obtain ⟨v, hv, hψ⟩ := representative_angular K c hΛ hG
  refine ⟨v, hv, ?_⟩
  change heckeComplexWeight K v hv
    ((signalCharacters K c).1⁻¹ * (targetCharacter K c * θ)) ≠ 0
  have heq :
      heckeComplexWeight K v hv ((signalCharacters K c).1⁻¹ *
        (targetCharacter K c * θ)) =
      heckeComplexWeight K v hv (conjugate (signalCharacters K c).1 *
        conjugate (signalCharacters K c).2 * targetCharacter K c) := by
    simp only [conjugate, heckeComplexWeight_mul, heckeComplexWeight_inv,
      heckeComplexWeight_finiteOrder K v hv hθ,
      heckeComplexWeight_finiteOrder K v hv hG, neg_zero, add_zero]
  rw [heq]
  exact hψ

/-- The existing directed-background field of the actual moment model
therefore supplies the theta period condition, without an additional
angular hypothesis and without requiring its finite set to be closed. -/
theorem momentData_canonicalPeriod_nonzero_angular (c : TargetContext K)
    (d : MomentData K c.family.omega (targetCharacter K c)) :
    ∃ (v : InfinitePlace K) (hv : v.IsComplex),
      heckeComplexWeight K v hv
        (canonicalPeriod K c (d.inverseBackground ^ (-d.direction))) ≠ 0 := by
  rcases d.directed_background with h | ⟨θ, hθ, heq⟩
  · exact canonicalPeriod_finite_nonzero_angular K c _ (d.theta_finite _ h)
  · rw [heq]
    exact canonicalPeriod_target_finite_nonzero_angular K c θ (d.theta_finite _ hθ)

end HeckeSkeleton.Moments.MOM_BASE
