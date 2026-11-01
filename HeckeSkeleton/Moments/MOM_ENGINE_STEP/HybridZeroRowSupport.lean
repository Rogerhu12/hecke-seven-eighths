import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridFiniteLeaf
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondBranchPartition

/-!
# Exact removal of zero-weight rows before Fourier Cauchy

All equalities below are proved from the literal finite sums. A retained
row set may omit an original row only when its actual complex weight is
zero. Both complete column polynomials, both Fourier kernels and every
remaining row weight are unchanged. In particular these identities do
not split a paired Cauchy product into products from different classes.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

section FiniteSums

variable {H I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem jointColumnEnergy_eq_on_zero_rows
    (rows kept : Finset H) (cols : Finset I) (q : H → ℂ)
    (c : H → I → ℂ) (x : H → I → E) (ξ : E)
    (hkeep : kept ⊆ rows)
    (hzero : ∀ h ∈ rows, h ∉ kept → q h = 0) :
    jointColumnEnergy rows cols q c x ξ = jointColumnEnergy kept cols q c x ξ := by
  unfold jointColumnEnergy
  symm
  apply Finset.sum_subset hkeep
  intro h hh hn
  simp only [hzero h hh hn, norm_zero, zero_mul]

theorem jointColumnPairMagnitude_eq_on_zero_rows
    (rows kept : Finset H) (left : Finset I) (right : Finset J)
    (q : H → ℂ) (c : H → I → ℂ) (d : H → J → ℂ)
    (x : H → I → E) (y : H → J → E) (ξ : E)
    (hkeep : kept ⊆ rows)
    (hzero : ∀ h ∈ rows, h ∉ kept → q h = 0) :
    jointColumnPairMagnitude rows left right q c d x y ξ =
      jointColumnPairMagnitude kept left right q c d x y ξ := by
  unfold jointColumnPairMagnitude
  symm
  apply Finset.sum_subset hkeep
  intro h hh hn
  simp only [hzero h hh hn, norm_zero, zero_mul]

theorem jointColumnEnergy_filter_eq_on_zero_rows
    (rows kept : Finset H) (cols : Finset I) (q : H → ℂ)
    (c : H → I → ℂ) (x : H → I → E) (P : H → Prop) (ξ : E)
    (hkeep : kept ⊆ rows)
    (hzero : ∀ h ∈ rows, h ∉ kept → q h = 0) :
    jointColumnEnergy (rows.filter P) cols q c x ξ =
      jointColumnEnergy (kept.filter P) cols q c x ξ := by
  apply jointColumnEnergy_eq_on_zero_rows
  · intro h hh
    exact Finset.mem_filter.mpr
      ⟨hkeep (Finset.mem_filter.mp hh).1, (Finset.mem_filter.mp hh).2⟩
  · intro h hh hn
    exact hzero h (Finset.mem_filter.mp hh).1 (fun hk =>
      hn (Finset.mem_filter.mpr ⟨hk, (Finset.mem_filter.mp hh).2⟩))

theorem jointColumnPairMagnitude_filter_eq_on_zero_rows
    (rows kept : Finset H) (left : Finset I) (right : Finset J)
    (q : H → ℂ) (c : H → I → ℂ) (d : H → J → ℂ)
    (x : H → I → E) (y : H → J → E) (P : H → Prop) (ξ : E)
    (hkeep : kept ⊆ rows)
    (hzero : ∀ h ∈ rows, h ∉ kept → q h = 0) :
    jointColumnPairMagnitude (rows.filter P) left right q c d x y ξ =
      jointColumnPairMagnitude (kept.filter P) left right q c d x y ξ := by
  apply jointColumnPairMagnitude_eq_on_zero_rows
  · intro h hh
    exact Finset.mem_filter.mpr
      ⟨hkeep (Finset.mem_filter.mp hh).1, (Finset.mem_filter.mp hh).2⟩
  · intro h hh hn
    exact hzero h (Finset.mem_filter.mp hh).1 (fun hk =>
      hn (Finset.mem_filter.mpr ⟨hk, (Finset.mem_filter.mp hh).2⟩))

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The original complex bilinear source is already unchanged before
absolute values, Fourier integration, or either Cauchy inequality. -/
theorem jointKernelPairing_eq_on_zero_rows
    (F : SchwartzMap E ℂ) (rows kept : Finset H) (left : Finset I) (right : Finset J)
    (q : H → ℂ) (c : H → I → ℂ) (d : H → J → ℂ)
    (x : H → I → E) (y : H → J → E)
    (hkeep : kept ⊆ rows)
    (hzero : ∀ h ∈ rows, h ∉ kept → q h = 0) :
    jointKernelPairing F rows left right q c d x y =
      jointKernelPairing F kept left right q c d x y := by
  unfold jointKernelPairing
  symm
  apply Finset.sum_subset hkeep
  intro h hh hn
  simp only [hzero h hh hn, zero_mul]

theorem jointHybridKernelCost_eq_on_zero_rows
    (F : SchwartzMap E ℂ) (rows kept : Finset H) (left : Finset I) (right : Finset J)
    (q : H → ℂ) (c : H → I → ℂ) (d : H → J → ℂ)
    (x : H → I → E) (y : H → J → E) (P : H → Prop)
    (hkeep : kept ⊆ rows)
    (hzero : ∀ h ∈ rows, h ∉ kept → q h = 0) :
    jointHybridKernelCost F rows left right q c d x y P =
      jointHybridKernelCost F kept left right q c d x y P := by
  unfold jointHybridKernelCost
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    rw [jointColumnPairMagnitude_filter_eq_on_zero_rows rows kept left right q c
      (fun h j => star (d h j)) x y P ξ hkeep hzero,
      jointColumnEnergy_filter_eq_on_zero_rows rows kept left q c x (fun h => ¬P h)
        ξ hkeep hzero,
      jointColumnEnergy_filter_eq_on_zero_rows rows kept right q
        (fun h j => star (d h j)) y (fun h => ¬P h) ξ hkeep hzero]

end FiniteSums

variable {K : Type} [Field K] [NumberField K]
variable {H U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

namespace ActualHybridLeaf

variable (B : ActualHybridLeaf K H U V)

/-- Only the finite row set changes. This is used to display the exact
support identity; the normalizer can retain the original leaf itself. -/
def withRows (kept : Finset H) : ActualHybridLeaf K H U V :=
  { B with rows := kept }

@[simp] theorem withRows_firstKernel (kept : Finset H) :
    (B.withRows kept).firstKernel = B.firstKernel := rfl

@[simp] theorem withRows_secondKernel (kept : Finset H) :
    (B.withRows kept).secondKernel = B.secondKernel := rfl

@[simp] theorem withRows_measure (kept : Finset H) :
    (B.withRows kept).measure = B.measure := rfl

variable (kept : Finset H) (hkeep : kept ⊆ B.rows)
variable (hzero : ∀ h ∈ B.rows, h ∉ kept → B.rowWeight h = 0)

include hkeep hzero

theorem ordinaryIntegrand_eq_withRows (z : U × V) :
    B.ordinaryIntegrand z = (B.withRows kept).ordinaryIntegrand z := by
  unfold ordinaryIntegrand
  dsimp only [withRows]
  apply congrArg₂ (fun a b : ℝ => Real.sqrt a * Real.sqrt b)
  · exact jointColumnEnergy_filter_eq_on_zero_rows B.rows kept B.left B.rowWeight
      B.leftCoefficient _ (fun h => ¬B.exceptional h) (WithLp.toLp 2 z) hkeep hzero
  · exact jointColumnEnergy_filter_eq_on_zero_rows B.rows kept B.right B.rowWeight
      (fun h j => star (B.rightCoefficient h j)) _ (fun h => ¬B.exceptional h)
      (WithLp.toLp 2 z) hkeep hzero

theorem exceptionalIntegrand_eq_withRows (z : U × V) :
    B.exceptionalIntegrand z = (B.withRows kept).exceptionalIntegrand z :=
  jointColumnPairMagnitude_filter_eq_on_zero_rows B.rows kept B.left B.right B.rowWeight
    B.leftCoefficient (fun h j => star (B.rightCoefficient h j)) _ _ B.exceptional
    (WithLp.toLp 2 z) hkeep hzero

theorem ordinaryCost_eq_withRows :
    B.ordinaryCost = (B.withRows kept).ordinaryCost := by
  change B.weight * (∫ z, B.ordinaryIntegrand z ∂B.measure) =
    B.weight * (∫ z, (B.withRows kept).ordinaryIntegrand z ∂B.measure)
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall
    (B.ordinaryIntegrand_eq_withRows kept hkeep hzero))

theorem exceptionalCost_eq_withRows :
    B.exceptionalCost = (B.withRows kept).exceptionalCost := by
  change B.weight * (∫ z, B.exceptionalIntegrand z ∂B.measure) =
    B.weight * (∫ z, (B.withRows kept).exceptionalIntegrand z ∂B.measure)
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall
    (B.exceptionalIntegrand_eq_withRows kept hkeep hzero))

theorem cost_eq_withRows : B.cost = (B.withRows kept).cost := by
  rw [cost, cost, B.exceptionalCost_eq_withRows kept hkeep hzero,
    B.ordinaryCost_eq_withRows kept hkeep hzero]

theorem firstPhaseCost_eq_withRows (ξ : U) :
    B.firstPhaseCost ξ = (B.withRows kept).firstPhaseCost ξ := by
  unfold firstPhaseCost
  dsimp only [withRows]
  congr 1
  exact jointHybridKernelCost_eq_on_zero_rows _ _ _ _ _ _ _ _ _ _ _ hkeep hzero

end ActualHybridLeaf

open HeckeGeneral.Characters

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ActualSecondCorrelationRows

variable (R : ActualSecondCorrelationRows A σ H ι)

@[simp] theorem restrictRows_correlationSupport_rows :
    (R.restrictRows (fun h => R.correlation h ≠ 0)).rows = R.live := rfl

@[simp] theorem restrictRows_correlationSupport_live :
    (R.restrictRows (fun h => R.correlation h ≠ 0)).live = R.live := by
  change (R.rows.filter (fun h => R.correlation h ≠ 0)).filter
    (fun h => R.correlation h ≠ 0) = R.rows.filter (fun h => R.correlation h ≠ 0)
  ext h
  simp only [Finset.mem_filter, and_assoc, and_self]

theorem weight_correlation_eq_zero_of_not_live
    (h : H) (hh : h ∈ R.rows) (hn : h ∉ R.live) :
    R.weight h * R.correlation h = 0 := by
  have hc : R.correlation h = 0 := by
    by_contra hc
    exact hn (Finset.mem_filter.mpr ⟨hh, hc⟩)
  rw [hc, mul_zero]

/-- In particular the literal complete-correlation source, before
Cauchy, is the source on exactly these same live physical rows. -/
theorem jointKernelPairing_correlationSupport {I J : Type*}
    (F : SchwartzMap V ℂ) (left : Finset I) (right : Finset J)
    (c : H → I → ℂ) (d : H → J → ℂ)
    (x : H → I → V) (y : H → J → V) :
    jointKernelPairing F R.rows left right
        (fun h => R.weight h * R.correlation h) c d x y =
      jointKernelPairing F R.live left right
        (fun h => R.weight h * R.correlation h) c d x y :=
  jointKernelPairing_eq_on_zero_rows F R.rows R.live left right _ c d x y
    (Finset.filter_subset _ _) R.weight_correlation_eq_zero_of_not_live

theorem jointHybridKernelCost_correlationSupport {I J : Type*}
    (F : SchwartzMap V ℂ) (left : Finset I) (right : Finset J)
    (c : H → I → ℂ) (d : H → J → ℂ)
    (x : H → I → V) (y : H → J → V) (P : H → Prop) :
    jointHybridKernelCost F R.rows left right
        (fun h => R.weight h * R.correlation h) c d x y P =
      jointHybridKernelCost F R.live left right
        (fun h => R.weight h * R.correlation h) c d x y P :=
  jointHybridKernelCost_eq_on_zero_rows F R.rows R.live left right _ c d x y P
    (Finset.filter_subset _ _) R.weight_correlation_eq_zero_of_not_live

end ActualSecondCorrelationRows

namespace ActualHybridLeaf

/-- The whole stored cost, including its exceptional part, agrees on
the genuine correlation support with both original kernels fixed. -/
theorem cost_eq_on_correlationSupport
    (B : ActualHybridLeaf K H U V) (R : ActualSecondCorrelationRows A σ H ι)
    (hrows : B.rows = R.rows)
    (hweight : ∀ h ∈ B.rows, B.rowWeight h = R.weight h * R.correlation h) :
    B.cost = (B.withRows R.live).cost := by
  apply B.cost_eq_withRows R.live
  · intro h hh
    exact hrows.symm ▸ (Finset.mem_filter.mp hh).1
  · intro h hh hn
    rw [hweight h hh]
    exact R.weight_correlation_eq_zero_of_not_live h (hrows ▸ hh) hn

end ActualHybridLeaf
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.jointKernelPairing_eq_on_zero_rows
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.cost_eq_withRows
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.firstPhaseCost_eq_withRows
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.jointKernelPairing_correlationSupport
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.cost_eq_on_correlationSupport
