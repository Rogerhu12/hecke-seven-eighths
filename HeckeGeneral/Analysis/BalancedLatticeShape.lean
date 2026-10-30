import HeckeGeneral.Analysis.LatticeShapeTail
import HeckeGeneral.Arithmetic.PrincipalGeneratorBalancing
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
Actual coordinate multiplication on the nondegenerate mixed space, transported
to the trace-normalized Euclidean model. Coordinate inversion is proved
continuous where every coordinate is nonzero. The compact shape comes from
the existing ordinary-unit balancing theorem; no new balancing or S-unit
unfolding is assumed here.
-/

noncomputable section

open Classical NumberField NumberField.InfinitePlace
open scoped Classical
open HeckeGeneral.Arithmetic

namespace HeckeGeneral.Analysis

variable (K : Type*) [Field K] [NumberField K]

def mixedCoordinateInverse (x : mixedEmbedding.mixedSpace K) :
    mixedEmbedding.mixedSpace K :=
  (fun w => (x.1 w)⁻¹, fun w => (x.2 w)⁻¹)

omit [NumberField K] in
theorem realCoordinate_ne_zero {x : mixedEmbedding.mixedSpace K}
    (hx : ∀ w, mixedEmbedding.normAtPlace w x ≠ 0)
    (w : {w : InfinitePlace K // IsReal w}) : x.1 w ≠ 0 := by
  apply norm_ne_zero_iff.mp
  simpa only [mixedEmbedding.normAtPlace_apply_of_isReal w.2] using hx w.1

omit [NumberField K] in
theorem complexCoordinate_ne_zero {x : mixedEmbedding.mixedSpace K}
    (hx : ∀ w, mixedEmbedding.normAtPlace w x ≠ 0)
    (w : {w : InfinitePlace K // IsComplex w}) : x.2 w ≠ 0 := by
  apply norm_ne_zero_iff.mp
  simpa only [mixedEmbedding.normAtPlace_apply_of_isComplex w.2] using hx w.1

/-- Coordinate multiplication is invertible because all real and complex
coordinates are nonzero, rather than because the product ring is a field. -/
def mixedCoordinateMulEquiv (x : mixedEmbedding.mixedSpace K)
    (hx : ∀ w, mixedEmbedding.normAtPlace w x ≠ 0) :
    mixedEmbedding.mixedSpace K ≃L[ℝ] mixedEmbedding.mixedSpace K where
  toLinearEquiv :=
    { (ContinuousLinearMap.mul ℝ (mixedEmbedding.mixedSpace K) x).toLinearMap with
      invFun := fun y => mixedCoordinateInverse K x * y
      left_inv := by
        intro y
        apply Prod.ext
        · funext w
          change (x.1 w)⁻¹ * (x.1 w * y.1 w) = y.1 w
          exact inv_mul_cancel_left₀ (realCoordinate_ne_zero K hx w) _
        · funext w
          change (x.2 w)⁻¹ * (x.2 w * y.2 w) = y.2 w
          exact inv_mul_cancel_left₀ (complexCoordinate_ne_zero K hx w) _
      right_inv := by
        intro y
        apply Prod.ext
        · funext w
          change x.1 w * ((x.1 w)⁻¹ * y.1 w) = y.1 w
          exact mul_inv_cancel_left₀ (realCoordinate_ne_zero K hx w) _
        · funext w
          change x.2 w * ((x.2 w)⁻¹ * y.2 w) = y.2 w
          exact mul_inv_cancel_left₀ (complexCoordinate_ne_zero K hx w) _ }
  continuous_toFun := (ContinuousLinearMap.mul ℝ (mixedEmbedding.mixedSpace K) x).continuous
  continuous_invFun :=
    (ContinuousLinearMap.mul ℝ (mixedEmbedding.mixedSpace K) (mixedCoordinateInverse K x)).continuous

@[simp] theorem mixedCoordinateMulEquiv_apply (x : mixedEmbedding.mixedSpace K)
    (hx : ∀ w, mixedEmbedding.normAtPlace w x ≠ 0) (y : mixedEmbedding.mixedSpace K) :
    mixedCoordinateMulEquiv K x hx y = x * y := rfl

/-- The trace model uses genuine conjugation by `traceToMixed`; the two norms
are not silently identified. -/
def traceCoordinateMulEquiv (x : mixedEmbedding.mixedSpace K)
    (hx : ∀ w, mixedEmbedding.normAtPlace w x ≠ 0) :
    mixedEmbedding.euclidean.mixedSpace K ≃L[ℝ] mixedEmbedding.euclidean.mixedSpace K :=
  ((traceToMixed K).trans (mixedCoordinateMulEquiv K x hx)).trans (traceToMixed K).symm

theorem traceCoordinateMulEquiv_inverseCLM (x : mixedEmbedding.mixedSpace K)
    (hx : ∀ w, mixedEmbedding.normAtPlace w x ≠ 0) :
    (traceCoordinateMulEquiv K x hx).symm.toContinuousLinearMap =
      (traceToMixed K).symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.mul ℝ (mixedEmbedding.mixedSpace K)
          (mixedCoordinateInverse K x)).comp (traceToMixed K).toContinuousLinearMap) := by
  ext y
  rfl

omit [NumberField K] in
theorem continuous_mixedCoordinateInverse {T : Type*} [TopologicalSpace T]
    (x : T → mixedEmbedding.mixedSpace K) (hc : Continuous x)
    (hx : ∀ t w, mixedEmbedding.normAtPlace w (x t) ≠ 0) :
    Continuous (fun t => mixedCoordinateInverse K (x t)) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro w
    exact ((continuous_apply w).comp (continuous_fst.comp hc)).inv₀
      (fun t => realCoordinate_ne_zero K (hx t) w)
  · apply continuous_pi
    intro w
    exact ((continuous_apply w).comp (continuous_snd.comp hc)).inv₀
      (fun t => complexCoordinate_ne_zero K (hx t) w)

/-- The inverse family is continuous in the actual operator-norm topology. -/
theorem continuous_traceCoordinateMulEquiv_inverseCLM
    {T : Type*} [TopologicalSpace T] (x : T → mixedEmbedding.mixedSpace K)
    (hc : Continuous x) (hx : ∀ t w, mixedEmbedding.normAtPlace w (x t) ≠ 0) :
    Continuous (fun t => (traceCoordinateMulEquiv K (x t) (hx t)).symm.toContinuousLinearMap) := by
  simp_rw [traceCoordinateMulEquiv_inverseCLM]
  exact continuous_const.clm_comp
    (((ContinuousLinearMap.mul ℝ (mixedEmbedding.mixedSpace K)).continuous.comp
      (continuous_mixedCoordinateInverse K x hc hx)).clm_comp continuous_const)

abbrev BalancedMixedShape := {x : mixedEmbedding.mixedSpace K // x ∈ balancedNormOneShape K}

def balancedTraceMulEquiv (x : BalancedMixedShape K) :
    mixedEmbedding.euclidean.mixedSpace K ≃L[ℝ] mixedEmbedding.euclidean.mixedSpace K :=
  traceCoordinateMulEquiv K x (normAtPlace_ne_zero_of_mem_balancedNormOneShape K x.property)

theorem continuous_balancedTraceMulEquiv_inverseCLM :
    Continuous (fun x : BalancedMixedShape K =>
      (balancedTraceMulEquiv K x).symm.toContinuousLinearMap) :=
  continuous_traceCoordinateMulEquiv_inverseCLM K Subtype.val continuous_subtype_val
    (fun x => normAtPlace_ne_zero_of_mem_balancedNormOneShape K x.property)

/-- The actual balanced family has a uniform inverse-power mass bound, depending
on the number field and fixed lattice but independent of the balanced point. -/
theorem exists_uniform_balancedTraceLattice_mass_bound
    (L : Submodule ℤ (mixedEmbedding.euclidean.mixedSpace K)) [DiscreteTopology L]
    (M : ℕ) (hM : Module.finrank ℤ L < M) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : BalancedMixedShape K,
      latticeInversePowerMass (imageLattice L (balancedTraceMulEquiv K x)) M ≤
        B ^ M * latticeInversePowerMass L M := by
  have hc : IsCompact (Set.univ : Set (BalancedMixedShape K)) :=
    isCompact_iff_isCompact_univ.mp (isCompact_balancedNormOneShape K)
  obtain ⟨B, hB, hb⟩ := exists_uniform_latticeInversePowerMass_image_bound hc
    (balancedTraceMulEquiv K) (continuous_balancedTraceMulEquiv_inverseCLM K).continuousOn L M hM
  exact ⟨B, hB, fun x => (hb x (Set.mem_univ x)).2⟩

end HeckeGeneral.Analysis
