import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridZeroRowSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridOrdinaryProduction

/-!
# Literal finite leaves enter the ordinary child producer

All identifications concern the finite row and column carriers or a
single coefficient/location. Arithmetic rows may omit an original row
only when its actual row weight is zero. The two energy identities are
proved by deleting those zero summands in the actual finite sums. The
right coefficient is conjugated once and its first Fourier location has
the original negative sign.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H ι U V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]

namespace ActualHybridLeaf

variable (leaf : ActualHybridLeaf K H U V)
variable {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin leaf.leftSlots → Finset (HeightOneSpectrum (𝓞 K))}
variable {T₁ T₂ : Finset (Ideal (𝓞 K))}
variable {T : Fin leaf.rightSlots → Finset (HeightOneSpectrum (𝓞 K))}
variable {IA : AllocationColumn K leaf.leftSlots → A.Exterior}
variable {IB : AllocationColumn K leaf.rightSlots → A.Exterior}
variable {rayLeft : AllocationColumn K leaf.leftSlots → Ray}
variable {rayRight : AllocationColumn K leaf.rightSlots → Ray}
variable {wholeLeft : AllocationColumn K leaf.leftSlots → ℂ}
variable {wholeRight : AllocationColumn K leaf.rightSlots → ℂ}
variable {x : H → AllocationColumn K leaf.leftSlots → WithLp 2 (U × V)}
variable {y : H → AllocationColumn K leaf.rightSlots → WithLp 2 (U × V)}
variable {b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB}
variable {exceptional : H → Prop}
variable (B : HybridOrdinaryRectangles R Ray S₁ S₂ S T₁ T₂ T IA IB
  rayLeft rayRight wholeLeft wholeRight x y b exceptional)

/-- A primitive identification of the stored finite leaf with the
genuine arithmetic branch.  No polynomial, energy or total bound is a
field of this dictionary. -/
structure OrdinaryBinding
    (_B : HybridOrdinaryRectangles R Ray S₁ S₂ S T₁ T₂ T IA IB
      rayLeft rayRight wholeLeft wholeRight x y b exceptional) : Prop where
  rows : R.rows ⊆ leaf.rows
  rows_zero : ∀ h ∈ leaf.rows, h ∉ R.rows → leaf.rowWeight h = 0
  left : leaf.left = b.val.leftColumns S₁ S₂ S
  right : leaf.right = b.val.rightColumns
  exceptional : ∀ h ∈ leaf.rows, leaf.exceptional h ↔ exceptional h
  rowWeight : ∀ h ∈ leaf.rows, leaf.rowWeight h = R.weight h * R.correlation h
  leftCoefficient : ∀ h ∈ leaf.rows, ∀ i ∈ leaf.left,
    leaf.leftCoefficient h i =
      secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency rayLeft b.val.2.1 wholeLeft h i
  rightCoefficient : ∀ h ∈ leaf.rows, ∀ j ∈ leaf.right,
    star (leaf.rightCoefficient h j) =
      secondAllocatedRightCoefficient (σ := σ) Ray IB R.frequency rayRight b.val.2.1 wholeRight h j
  leftPoint : ∀ h ∈ leaf.rows, ∀ i ∈ leaf.left,
    WithLp.toLp 2 (leaf.leftFirst h i, leaf.leftSecond h i) = x h i
  rightPoint : ∀ h ∈ leaf.rows, ∀ j ∈ leaf.right,
    WithLp.toLp 2 (-leaf.rightFirst h j, leaf.rightSecond h j) = y h j

namespace OrdinaryBinding

variable {leaf B} (d : leaf.OrdinaryBinding B)

include d

theorem ordinary_rows_subset :
    R.rows.filter (fun h => ¬exceptional h) ⊆
      leaf.rows.filter (fun h => ¬leaf.exceptional h) := by
  intro h hh
  obtain ⟨hm, hn⟩ := Finset.mem_filter.mp hh
  have hl : h ∈ leaf.rows := d.rows hm
  exact Finset.mem_filter.mpr ⟨hl, fun he => hn ((d.exceptional h hl).mp he)⟩

theorem ordinary_rows_zero :
    ∀ h ∈ leaf.rows.filter (fun h => ¬leaf.exceptional h),
      h ∉ R.rows.filter (fun h => ¬exceptional h) → leaf.rowWeight h = 0 := by
  intro h hh hn
  obtain ⟨hm, he⟩ := Finset.mem_filter.mp hh
  apply d.rows_zero h hm
  intro hr
  exact hn (Finset.mem_filter.mpr
    ⟨hr, fun hx => he ((d.exceptional h hm).mpr hx)⟩)

/-- Both energies are computed from the same stored row and column
atoms; their equality is a consequence of the dictionary above. -/
theorem ordinaryIntegrand_eq (z : U × V) :
    leaf.ordinaryIntegrand z = B.originalIntegrand (WithLp.toLp 2 z) := by
  have hleft :
      jointColumnEnergy (leaf.rows.filter (fun h => ¬leaf.exceptional h)) leaf.left
        leaf.rowWeight leaf.leftCoefficient
        (fun h i => WithLp.toLp 2 (leaf.leftFirst h i, leaf.leftSecond h i))
        (WithLp.toLp 2 z) =
      jointColumnEnergy (R.rows.filter (fun h => ¬exceptional h))
        (b.val.leftColumns S₁ S₂ S) (fun h => R.weight h * R.correlation h)
        (secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency rayLeft b.val.2.1 wholeLeft)
        x (WithLp.toLp 2 z) := by
    calc
      _ = jointColumnEnergy (R.rows.filter (fun h => ¬exceptional h)) leaf.left
          leaf.rowWeight leaf.leftCoefficient
          (fun h i => WithLp.toLp 2 (leaf.leftFirst h i, leaf.leftSecond h i))
          (WithLp.toLp 2 z) :=
        jointColumnEnergy_eq_on_zero_rows _ _ _ _ _ _ _
          d.ordinary_rows_subset d.ordinary_rows_zero
      _ = _ := by
        rw [← d.left]
        unfold jointColumnEnergy
        apply Finset.sum_congr rfl
        intro h hh
        have hm : h ∈ leaf.rows := d.rows (Finset.mem_filter.mp hh).1
        have hc :
            jointFourierColumn leaf.left (leaf.leftCoefficient h)
              (fun i => WithLp.toLp 2 (leaf.leftFirst h i, leaf.leftSecond h i))
              (WithLp.toLp 2 z) =
            jointFourierColumn leaf.left
              (secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency rayLeft b.val.2.1 wholeLeft h)
              (x h) (WithLp.toLp 2 z) := by
          unfold jointFourierColumn
          apply Finset.sum_congr rfl
          intro i hi
          rw [d.leftCoefficient h hm i hi, d.leftPoint h hm i hi]
        rw [d.rowWeight h hm, hc]
  have hright :
      jointColumnEnergy (leaf.rows.filter (fun h => ¬leaf.exceptional h)) leaf.right
        leaf.rowWeight (fun h j => star (leaf.rightCoefficient h j))
        (fun h j => WithLp.toLp 2 (-leaf.rightFirst h j, leaf.rightSecond h j))
        (WithLp.toLp 2 z) =
      jointColumnEnergy (R.rows.filter (fun h => ¬exceptional h))
        b.val.rightColumns (fun h => R.weight h * R.correlation h)
        (secondAllocatedRightCoefficient (σ := σ) Ray IB R.frequency rayRight b.val.2.1 wholeRight)
        y (WithLp.toLp 2 z) := by
    calc
      _ = jointColumnEnergy (R.rows.filter (fun h => ¬exceptional h)) leaf.right
          leaf.rowWeight (fun h j => star (leaf.rightCoefficient h j))
          (fun h j => WithLp.toLp 2 (-leaf.rightFirst h j, leaf.rightSecond h j))
          (WithLp.toLp 2 z) :=
        jointColumnEnergy_eq_on_zero_rows _ _ _ _ _ _ _
          d.ordinary_rows_subset d.ordinary_rows_zero
      _ = _ := by
        rw [← d.right]
        unfold jointColumnEnergy
        apply Finset.sum_congr rfl
        intro h hh
        have hm : h ∈ leaf.rows := d.rows (Finset.mem_filter.mp hh).1
        have hc :
            jointFourierColumn leaf.right (fun j => star (leaf.rightCoefficient h j))
              (fun j => WithLp.toLp 2 (-leaf.rightFirst h j, leaf.rightSecond h j))
              (WithLp.toLp 2 z) =
            jointFourierColumn leaf.right
              (secondAllocatedRightCoefficient (σ := σ) Ray IB R.frequency rayRight b.val.2.1 wholeRight h)
              (y h) (WithLp.toLp 2 z) := by
          unfold jointFourierColumn
          apply Finset.sum_congr rfl
          intro j hj
          rw [d.rightCoefficient h hm j hj, d.rightPoint h hm j hj]
        rw [d.rowWeight h hm, hc]
  exact congrArg₂ (fun a c : ℝ => Real.sqrt a * Real.sqrt c) hleft hright

end OrdinaryBinding
end ActualHybridLeaf

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.OrdinaryBinding.ordinaryIntegrand_eq

