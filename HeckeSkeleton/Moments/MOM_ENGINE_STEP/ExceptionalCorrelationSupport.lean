import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalExceptionalSavingCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalThetaRows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ConstantCommonLeaf

/-!
# Empty actual correlation classes and inherited second savings

An empty nonzero-correlation carrier contributes zero on the literal
exceptional leaf.  The proof uses the individual row identity and keeps
both Fourier kernels, the outer scalar and both complete columns.
Constant common atoms may first be extracted by their existing exact
identity; this does not require a numerical saving on an empty class.

When a class before the finite-character partition does contain a live
row, the second saving proved there applies to every restriction.  The
original unit and nonunit ideals and the exact multiplicity-one radical
are unchanged by restriction, even when a particular theta class is
empty.  No implication from coefficient support to correlation support
is assumed.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ActualSecondCorrelationRows

variable (R : ActualSecondCorrelationRows A σ H ι)

theorem correlation_eq_zero_of_live_empty (hR : R.live = ∅)
    (h : H) (hh : h ∈ R.rows) : R.correlation h = 0 := by
  by_contra hne
  have hm : h ∈ R.live := Finset.mem_filter.mpr ⟨hh, hne⟩
  rw [hR] at hm
  exact Finset.not_mem_empty h hm

end ActualSecondCorrelationRows

section Leaves

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace ActualHybridLeaf

variable (B : ActualHybridLeaf K H U E)

theorem exceptionalIntegrand_eq_zero_of_rowWeight_zero
    (hweight : ∀ h ∈ B.rows, B.rowWeight h = 0) (z : U × E) :
    B.exceptionalIntegrand z = 0 := by
  unfold exceptionalIntegrand jointColumnPairMagnitude
  apply Finset.sum_eq_zero
  intro h hh
  rw [hweight h (Finset.mem_filter.mp hh).1, norm_zero, zero_mul, zero_mul]

theorem exceptionalCost_eq_zero_of_rowWeight_zero
    (hweight : ∀ h ∈ B.rows, B.rowWeight h = 0) : B.exceptionalCost = 0 := by
  simp only [exceptionalCost, B.exceptionalIntegrand_eq_zero_of_rowWeight_zero hweight,
    integral_zero, mul_zero]

/-- The exact original row binding suffices; no bound on a sum, a
kernel or a source coefficient is needed. -/
theorem exceptionalCost_eq_zero_of_correlation_live_empty
    (R : ActualSecondCorrelationRows A σ H ι)
    (hrows : B.rows = R.rows)
    (hweight : ∀ h ∈ B.rows, B.rowWeight h = R.weight h * R.correlation h)
    (hR : R.live = ∅) : B.exceptionalCost = 0 := by
  apply B.exceptionalCost_eq_zero_of_rowWeight_zero
  intro h hh
  have hr : h ∈ R.rows := hrows ▸ hh
  rw [hweight h hh, R.correlation_eq_zero_of_live_empty hR h hr, mul_zero]

namespace ConstantAtomExtraction

variable {B} (X : B.ConstantAtomExtraction)

/-- Return the zero contribution to the original leaf, before the
same constant-atom extraction used by the nonempty terminal estimate. -/
theorem exceptionalCost_eq_zero_of_correlation_live_empty
    (R : ActualSecondCorrelationRows A σ H ι)
    (hrows : X.leaf.rows = R.rows)
    (hweight : ∀ h ∈ X.leaf.rows, X.leaf.rowWeight h = R.weight h * R.correlation h)
    (hR : R.live = ∅) : B.exceptionalCost = 0 :=
  X.exceptionalCost_eq.trans
    (X.leaf.exceptionalCost_eq_zero_of_correlation_live_empty R hrows hweight hR)

end ConstantAtomExtraction
end ActualHybridLeaf
end Leaves

variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS} {kLeft kRight : ℕ}

namespace ActualSecondRowMass

variable (W : ActualSecondRowMass R C kLeft kRight)

@[simp] theorem restrictRows_originalMultiplicityOneIdeal (p : H → Prop) :
    (W.restrictRows p).originalMultiplicityOneIdeal = W.originalMultiplicityOneIdeal := rfl

@[simp] theorem restrictRows_originalMultiplicityOneLength (p : H → Prop) (Z : ℝ) :
    (W.restrictRows p).originalMultiplicityOneLength Z = W.originalMultiplicityOneLength Z := rfl

end ActualSecondRowMass

namespace OriginalNominalGeometry

variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)
variable (W : ActualSecondRowMass R C kLeft kRight)
variable (vStar r₁ r₂ slotError firstProfile : ℝ)

theorem exceptionalNumbers_restrictRows (p : H → Prop) :
    G.exceptionalNumbers (W.restrictRows p) vStar r₁ r₂ slotError firstProfile =
      G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile := rfl

theorem exceptionalNumbersAtNormalization_restrictRows
    (p : H → Prop) (normalization total : ℝ) :
    G.exceptionalNumbersAtNormalization (W.restrictRows p) vStar r₁ r₂ slotError firstProfile
        normalization total =
      G.exceptionalNumbersAtNormalization W vStar r₁ r₂ slotError firstProfile
        normalization total := rfl

/-- The witness comes from the original class before theta
restriction.  The restricted class itself may be empty. -/
theorem exceptionalNumbers_restrictRows_second_saving
    (p : H → Prop) (hZ : 1 < Z)
    (hright : ∀ i, 0 < R.rightMultiplicity i) (h : R.live) :
    let n := G.exceptionalNumbers (W.restrictRows p) vStar r₁ r₂ slotError firstProfile
    2 * n.b₂ / 3 ≤ 2 * n.b₂ - 5 * n.g₂ / 6 - n.p₂ + n.t₂ + n.V₀ / 6 +
      (2 * n.v) / 6 :=
  G.exceptionalNumbers_second_saving W vStar r₁ r₂ slotError firstProfile hZ hright h

theorem exceptionalNumbersAtNormalization_restrictRows_second_saving
    (p : H → Prop) (normalization total : ℝ) (hZ : 1 < Z)
    (hright : ∀ i, 0 < R.rightMultiplicity i) (h : R.live) :
    let n := G.exceptionalNumbersAtNormalization (W.restrictRows p)
      vStar r₁ r₂ slotError firstProfile normalization total
    2 * n.b₂ / 3 ≤ 2 * n.b₂ - 5 * n.g₂ / 6 - n.p₂ + n.t₂ + n.V₀ / 6 +
      (2 * n.v) / 6 :=
  G.exceptionalNumbersAtNormalization_second_saving W vStar r₁ r₂ slotError firstProfile
    normalization total hZ hright h

end OriginalNominalGeometry

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.exceptionalCost_eq_zero_of_correlation_live_empty
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.ConstantAtomExtraction.exceptionalCost_eq_zero_of_correlation_live_empty
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.exceptionalNumbers_restrictRows_second_saving
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.exceptionalNumbersAtNormalization_restrictRows_second_saving
