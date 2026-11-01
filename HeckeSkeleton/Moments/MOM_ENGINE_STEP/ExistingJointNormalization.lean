import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExistingJointRowBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.JointNormalizedLeaves

/-!
# The existing normalized family already satisfies its joint row budget

The original allowed rows below already obey the same joint budget.
Consequently the existing row-filter constructors preserve the complete
side normalization and the complete two-sided normalization. Capacity
inputs, profile representatives and the subsequently chosen children
are those of this same object.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {ω ψ : HeckeCharacter K}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)}

namespace SecondSideNormalization

variable {V H ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [Fintype ι] [DecidableEq ι]
variable {rows : ActualSecondCorrelationRows A σ H ι}
variable {side : SecondColumnSide} {k : ℕ}
variable {f : SecondSideFrame (V := V) C rows Ray side k}
variable (N : SecondSideNormalization f ω ψ rowDomain heightDomain window seminorms)

private theorem rawProfileWindow_eq
    {d : MomentData K ω ψ} {radius : ℝ}
    (P Q : RawProfileWindow rowDomain heightDomain window seminorms d radius) : P = Q := by
  have hinverse : P.inverseRep = Q.inverseRep := by
    funext u t
    exact DFunLike.ext _ _ fun y => (P.inverse_eq u t y).symm.trans (Q.inverse_eq u t y)
  have hleft : P.leftRep = Q.leftRep := by
    funext u t
    exact DFunLike.ext _ _ fun y => (P.left_eq u t y).symm.trans (Q.left_eq u t y)
  have hright : P.rightRep = Q.rightRep := by
    funext u t
    exact DFunLike.ext _ _ fun y => (P.right_eq u t y).symm.trans (Q.right_eq u t y)
  have hprime : P.primeRep = Q.primeRep := by
    funext i t
    exact DFunLike.ext _ _ fun y => (P.prime_eq i t y).symm.trans (Q.prime_eq i t y)
  cases P
  cases Q
  cases hinverse
  cases hleft
  cases hright
  cases hprime
  rfl

private theorem capacityInput_heq_of_fields
    {D₁ D₂ : f.source.Calibration (σ := σ) ω ψ} (hD : D₁ = D₂)
    (I₁ : D₁.CapacityInput) (I₂ : D₂.CapacityInput)
    (hskeleton : I₁.skeleton = I₂.skeleton)
    (hb₂ : I₁.b₂ = I₂.b₂) (hp₂ : I₁.p₂ = I₂.p₂)
    (hboundary : I₁.boundary = I₂.boundary) (hell : I₁.ell = I₂.ell)
    (hgap : I₁.gap = I₂.gap) (hdelta : I₁.delta = I₂.delta)
    (hmesh : I₁.mesh = I₂.mesh)
    (hsupport : I₁.supportError = I₂.supportError)
    (hclip : I₁.rawClipError = I₂.rawClipError)
    (hwidth : I₁.widthError = I₂.widthError)
    (hleft : I₁.leftAnnulus = I₂.leftAnnulus)
    (hright : I₁.rightAnnulus = I₂.rightAnnulus)
    (hprime : I₁.primeBound = I₂.primeBound) : HEq I₁ I₂ := by
  cases hD
  cases I₁
  cases I₂
  cases hskeleton
  cases hb₂
  cases hp₂
  cases hboundary
  cases hell
  cases hgap
  cases hdelta
  cases hmesh
  cases hsupport
  cases hclip
  cases hwidth
  cases hleft
  cases hright
  cases hprime
  rfl

private theorem eq_of_calibration_capacity_fields
    (N₁ N₂ : SecondSideNormalization f ω ψ rowDomain heightDomain window seminorms)
    (hcal : N₁.calibration = N₂.calibration)
    (hcap : HEq N₁.capacity N₂.capacity)
    (hamp : N₁.amplitude = N₂.amplitude)
    (hbounds : N₁.bounds = N₂.bounds) : N₁ = N₂ := by
  cases N₁ with
  | mk D₁ I₁ a₁ ha₁ b₁ hb₁ hf₁ p₁ =>
    cases N₂ with
    | mk D₂ I₂ a₂ ha₂ b₂ hb₂ hf₂ p₂ =>
      cases hcal
      cases eq_of_heq hcap
      cases hamp
      cases hbounds
      have hp : p₁ = p₂ := by
        funext ξ
        exact rawProfileWindow_eq _ _
      cases hp
      rfl

/-- The filter retains every original allowed row. Its capacity record
copies all computational fields, and its four Schwartz representatives
are the original representatives. Thus the entire side is unchanged. -/
theorem withJointRowBudget_eq_self
    (M : ActualMovingMaskRecipe A N.calibration.data)
    (hsource : ∀ h ∈ f.source.rows,
      A.exteriorNorm (f.source.originalIdeal h) *
        A.exteriorNorm (M.support (f.source.row h).momentIdeal) ≤
          f.source.normFactor h * f.source.base ^
            (N.calibration.parameters.m + N.calibration.parameters.q))
    (hbudget : ∀ ξ u, (N.calibration.data ξ).allowedRow u →
      idealNorm K u * A.exteriorNorm (M.support u) ≤
        f.source.base ^ (N.calibration.parameters.m + N.calibration.parameters.q)) :
    N.withJointRowBudget M hsource = N := by
  have hcal : (N.withJointRowBudget M hsource).calibration = N.calibration :=
    N.calibration.withJointRowBudget_eq_self M hsource hbudget
  have hcap : HEq (N.withJointRowBudget M hsource).capacity N.capacity :=
    capacityInput_heq_of_fields (f := f) hcal (N.withJointRowBudget M hsource).capacity N.capacity
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  exact eq_of_calibration_capacity_fields (N.withJointRowBudget M hsource) N
    hcal hcap rfl rfl

end SecondSideNormalization

namespace ActualHybridLeaf.NormalizationData

variable {H : Type} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {leaf : ActualHybridLeaf K H U E} {Z : ℝ}
variable (N : leaf.NormalizationData (ι := ι) C Ray ω ψ Z
  rowDomain heightDomain window seminorms)

/-- These are the same original allowed-row budgets on the two sides.
The complete normalization equality also preserves the actual family,
its selected capacity children and their two Fourier kernels. -/
theorem withJointRows_eq_self (J : N.JointRowInput)
    (hleft : ∀ r ξ u, ((N.left r).calibration.data ξ).allowedRow u →
      idealNorm K u * A.exteriorNorm ((J.leftMask r).support u) ≤
        (N.rectangles.leftFrame C r).source.base ^
          ((N.left r).calibration.parameters.m + (N.left r).calibration.parameters.q))
    (hright : ∀ r ξ u, ((N.right r).calibration.data ξ).allowedRow u →
      idealNorm K u * A.exteriorNorm ((J.rightMask r).support u) ≤
        (N.rectangles.rightFrame C r).source.base ^
          ((N.right r).calibration.parameters.m + (N.right r).calibration.parameters.q)) :
    N.withJointRows J = N := by
  have hl : (fun r => (N.left r).withJointRowBudget
      (J.leftMask r) (J.left_budget r)) = N.left := by
    funext r
    exact (N.left r).withJointRowBudget_eq_self (J.leftMask r) (J.left_budget r) (hleft r)
  have hr : (fun r => (N.right r).withJointRowBudget
      (J.rightMask r) (J.right_budget r)) = N.right := by
    funext r
    exact (N.right r).withJointRowBudget_eq_self (J.rightMask r) (J.right_budget r) (hright r)
  simp only [withJointRows, hl, hr]

end ActualHybridLeaf.NormalizationData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideNormalization.withJointRowBudget_eq_self
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.NormalizationData.withJointRows_eq_self
