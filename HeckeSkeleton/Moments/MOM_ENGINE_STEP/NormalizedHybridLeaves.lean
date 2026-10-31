import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteNormalizedProductFamily
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafOrdinaryBinding

/-!
# The original live finite leaves produce the normalized child family

The input record contains the actual arithmetic rectangle dictionaries
and their single-atom identification with a stored finite leaf. Its
capacity and profile fields precede both continuous Fourier variables.
The source inequalities and all measure integrability are proved by the
engine. The output carrier is literally the original finite leaf type
times the four rectangle choices.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open WholeAllocation

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H : Type} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ω ψ : HeckeCharacter K}

namespace ActualHybridLeaf

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Only original row/column/character dictionaries, individual raw
prime estimates and individual profile windows occur here. -/
structure NormalizationData (leaf : ActualHybridLeaf K H U E)
    (C : A.GeneralArithmeticContext σ η hS)
    (Ray : Type*) [CommGroup Ray] [Fintype Ray]
    (ω ψ : HeckeCharacter K) (Z : ℝ)
    (rowDomain : Set (NonzeroIdeal K)) (heightDomain window : Set ℝ)
    (seminorms : Finset (ℕ × ℕ)) where
  rows : ActualSecondCorrelationRows A σ H ι
  leftPlain₁ : Finset (Ideal (𝓞 K))
  leftPlain₂ : Finset (Ideal (𝓞 K))
  leftPrimes : Fin leaf.leftSlots → Finset (HeightOneSpectrum (𝓞 K))
  rightPlain₁ : Finset (Ideal (𝓞 K))
  rightPlain₂ : Finset (Ideal (𝓞 K))
  rightPrimes : Fin leaf.rightSlots → Finset (HeightOneSpectrum (𝓞 K))
  leftIdeal : AllocationColumn K leaf.leftSlots → A.Exterior
  rightIdeal : AllocationColumn K leaf.rightSlots → A.Exterior
  leftRay : AllocationColumn K leaf.leftSlots → Ray
  rightRay : AllocationColumn K leaf.rightSlots → Ray
  leftWhole : AllocationColumn K leaf.leftSlots → ℂ
  rightWhole : AllocationColumn K leaf.rightSlots → ℂ
  /-- The residual occurrence coordinates may differ from the stored
  source by a common row translation. `binding` proves that exact
  relation, and cancels its unit Fourier phase in the column norm. -/
  leftPoint : H → AllocationColumn K leaf.leftSlots → WithLp 2 (U × E) :=
    fun h i => WithLp.toLp 2 (leaf.leftFirst h i, leaf.leftSecond h i)
  rightPoint : H → AllocationColumn K leaf.rightSlots → WithLp 2 (U × E) :=
    fun h j => WithLp.toLp 2 (-leaf.rightFirst h j, leaf.rightSecond h j)
  branch : liveSecondAllocationBranches (Ray := Ray)
    leftPlain₁ leftPlain₂ leftPrimes rightPlain₁ rightPlain₂ rightPrimes rightIdeal
  rectangles : HybridOrdinaryRectangles rows Ray
    leftPlain₁ leftPlain₂ leftPrimes rightPlain₁ rightPlain₂ rightPrimes leftIdeal rightIdeal
    leftRay rightRay leftWhole rightWhole
    leftPoint rightPoint
    branch leaf.exceptional
  binding : leaf.OrdinaryBinding rectangles
  left : ∀ r : Bool, SecondSideNormalization (rectangles.leftFrame C r)
    ω ψ rowDomain heightDomain window seminorms
  right : ∀ r : Bool, SecondSideNormalization (rectangles.rightFrame C r)
    ω ψ rowDomain heightDomain window seminorms
  left_base : ∀ r, (rectangles.leftFrame C r).source.base = Z
  right_base : ∀ r, (rectangles.rightFrame C r).source.base = Z
  left_height : ∀ r ξ, (left r).calibration.height ξ ∈ heightDomain
  right_height : ∀ r ξ, (right r).calibration.height ξ ∈ heightDomain

namespace NormalizationData

variable {leaf : ActualHybridLeaf K H U E} {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray] {Z : ℝ}
variable {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}
variable (N : leaf.NormalizationData (ι := ι) C Ray ω ψ Z rowDomain heightDomain window seminorms)

def family : ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) (Bool × Bool) ω ψ Z :=
  N.rectangles.normalizedFamily C N.left N.right Z N.left_base N.right_base

theorem in_fixed_window :
    ∀ rs : N.family.active Finset.univ, ∀ ξ,
      InFixedProfileWindow rowDomain Set.univ window seminorms
        (N.family.leftData Finset.univ rs ξ) ∧
      InFixedProfileWindow rowDomain Set.univ window seminorms
        (N.family.rightData Finset.univ rs ξ) :=
  N.rectangles.normalizedFamily_in_fixed_window C N.left N.right Z
    N.left_base N.right_base N.left_height N.right_height

/-- The literal stored ordinary source is bounded by its own four
constructed original frame pairs. No summed source identity is input. -/
theorem ordinary_le_sourcePairs (parentWidth : ℝ) (hZ : 0 < Z) (z : U × E) :
    leaf.ordinaryIntegrand z / Z ^ parentWidth ≤
      ∑ rs : Bool × Bool, N.family.sourcePair parentWidth rs (WithLp.toLp 2 z) := by
  rw [N.binding.ordinaryIntegrand_eq]
  exact N.rectangles.ordinary_le_source_pairs C N.left N.right Z
    N.left_base N.right_base parentWidth hZ (WithLp.toLp 2 z)

/-- Original finite coefficients prove source convergence. The exact
outer scalar and the parent normalization are each retained once. -/
theorem ordinaryCost_le_sourcePairs (parentWidth : ℝ) (hZ : 0 < Z) :
    leaf.ordinaryCost / Z ^ parentWidth ≤
      ∑ rs : Bool × Bool, leaf.weight *
        ∫ z : U × E, N.family.sourcePair parentWidth rs (WithLp.toLp 2 z) ∂leaf.measure := by
  have hi (rs : Bool × Bool) :
      Integrable (fun z : U × E => N.family.sourcePair parentWidth rs (WithLp.toLp 2 z))
        leaf.measure :=
    N.family.sourcePair_nested_integrable leaf.firstKernel leaf.secondKernel parentWidth rs
  calc
    _ = leaf.weight * ∫ z, leaf.ordinaryIntegrand z / Z ^ parentWidth ∂leaf.measure := by
      rw [integral_div]
      unfold ordinaryCost
      ring
    _ ≤ leaf.weight * ∫ z, ∑ rs : Bool × Bool,
        N.family.sourcePair parentWidth rs (WithLp.toLp 2 z) ∂leaf.measure := by
      apply mul_le_mul_of_nonneg_left _ leaf.weight_nonneg
      apply integral_mono (leaf.ordinaryIntegrand_integrable.div_const _)
        (integrable_finsetSum Finset.univ (fun rs _ => hi rs))
      exact N.ordinary_le_sourcePairs parentWidth hZ
    _ = _ := by
      rw [integral_finsetSum Finset.univ (fun rs _ => hi rs), Finset.mul_sum]

end NormalizationData

end ActualHybridLeaf

namespace ActualHybridFamily

variable {J : Type*} [Fintype J]
variable {I : J → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable (leaves : J → ActualHybridLeaf K H U E)
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray] {Z : ℝ}
variable {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}
variable (N : ∀ j, (leaves j).NormalizationData (ι := I j)
  C Ray ω ψ Z rowDomain heightDomain window seminorms)

/-- On application J is exactly the subtype of the original live
finite leaves. Both Boolean rectangle labels remain on the carrier. -/
def normalizedFamily :
    ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) (J × (Bool × Bool)) ω ψ Z :=
  ActualNormalizedPairFamily.combine (fun j => (N j).family)

def firstKernels (b : J × (Bool × Bool)) : 𝓢(U, ℂ) := (leaves b.1).firstKernel
def secondKernels (b : J × (Bool × Bool)) : 𝓢(E, ℂ) := (leaves b.1).secondKernel
def outerWeights (b : J × (Bool × Bool)) : ℝ := (leaves b.1).weight

theorem outerWeights_nonneg (b : J × (Bool × Bool)) : 0 ≤ outerWeights leaves b :=
  (leaves b.1).weight_nonneg

/-- The full original finite ordinary budget is compared with the
same indexed source pairs used by the normalized kernel theorem. -/
theorem ordinaryBudget_le_sourcePairs (parentWidth : ℝ) (hZ : 0 < Z) :
    (∑ j, (leaves j).ordinaryCost) / Z ^ parentWidth ≤
      ∑ b : J × (Bool × Bool), outerWeights leaves b *
        ∫ z : U × E,
          (normalizedFamily leaves N).sourcePair parentWidth b (WithLp.toLp 2 z)
          ∂nestedFourierMeasure (firstKernels leaves b) (secondKernels leaves b) := by
  rw [Finset.sum_div]
  calc
    _ ≤ ∑ j, ∑ rs : Bool × Bool, (leaves j).weight *
        ∫ z : U × E, (N j).family.sourcePair parentWidth rs (WithLp.toLp 2 z)
          ∂(leaves j).measure :=
      Finset.sum_le_sum fun j _ => (N j).ordinaryCost_le_sourcePairs parentWidth hZ
    _ = _ := by
      rw [Fintype.sum_prod_type]
      rfl

end ActualHybridFamily

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.NormalizationData.in_fixed_window
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.NormalizationData.ordinaryCost_le_sourcePairs
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridFamily.ordinaryBudget_le_sourcePairs

