import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralNormFactorTransport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralStripExistingBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActualCharacters

/-!
# Exact residual-factor redistribution on the original covered leaf

The original direct, main and valuation constructors have already proved
their individual column identities. This module reuses those identities
after moving the positive norm-profile factors into the first scalar.
It recomputes the actual second common scalar and residual table on the
stored allocation, rather than keeping an obsolete common-atom weight.

Only the original conditional comparison-scale identity is needed for
the redistribution. The two common-scalar identities below are literal
projections of the original extraction constructors. All new column,
row-weight and ordinary-source identities are proved here. The original
leaf, both kernels, its columns and its exceptional predicate remain
the same.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckePort.Moments HeckePort.Moments.Support WholeAllocation

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralActualCharacters.Recipe

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K}
variable {F : CanonicalLiteralPhaseCalibration.FixedPhases A}
variable {parent : MomentData K ω ψ} {oldMoving : OriginalMovingFactors A P R}
variable {correction : HeckeCharacter K}
variable {remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K}
variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}

/-- The redistribution changes no original character or slot index. -/
def redistributeNormFactors
    (E : Recipe P R F parent oldMoving correction remaining extra d)
    (δ₁ δ₂ : ℝ) :
    Recipe P R F parent oldMoving correction remaining extra
      (d.redistributeNormFactors δ₁ δ₂) where
  slots := E.slots
  characters := E.characters

end CanonicalLiteralActualCharacters.Recipe

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}

local instance canonicalLiteralRedistributedBindingCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace ActualGaussStage.CoveredClassKey

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualGaussStage (E := ℝ) hΓ μv hDiff G finiteTest}
variable {LC RC : SourceCartesianCover G.columns G.ideal}
variable (v : s.CoveredClassKey LC RC)
variable (leftAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (LC.branch v.2.2.1).slotCount)
variable (rightAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (RC.branch v.2.2.2.1).slotCount)
variable (δ₁ δ₂ : ℝ)
variable (hproductLeft : leftAtoms.centered = true →
  leftAtoms.scale₁ true * leftAtoms.scale₂ true =
    leftAtoms.scale₁ false * leftAtoms.scale₂ false)
variable (hproductRight : rightAtoms.centered = true →
  rightAtoms.scale₁ true * rightAtoms.scale₂ true =
    rightAtoms.scale₁ false * rightAtoms.scale₂ false)

local notation "newLeft" => leftAtoms.redistributeNormFactors δ₁ δ₂
local notation "newRight" => rightAtoms.redistributeNormFactors δ₁ δ₂

include hproductLeft in
private theorem redistributed_left_common_whole
    (i : AllocationColumn K v.leftSlots) (hi : i ∈ v.leftReindex.cartesian) :
    (v.literalLeftOriginal newLeft).commonScalar v.literalLeftBranch *
        (v.literalLeftAtoms newLeft).whole i =
      (v.literalLeftOriginal leftAtoms).commonScalar v.literalLeftBranch *
        (v.literalLeftAtoms leftAtoms).whole i := by
  have hr := (v.literalLeft_cartesian i).mp hi
  calc
    _ = (v.literalLeftOriginal newLeft).whole (v.literalLeftBranch.reconstruct i) :=
      ((v.literalLeftOriginal newLeft).extract_whole v.literalLeftBranch i hr).symm
    _ = (v.literalLeftOriginal leftAtoms).whole (v.literalLeftBranch.reconstruct i) :=
      leftAtoms.redistributeNormFactors_whole δ₁ δ₂ hproductLeft _
    _ = _ := (v.literalLeftOriginal leftAtoms).extract_whole v.literalLeftBranch i hr

include hproductRight in
private theorem redistributed_right_common_whole
    (i : AllocationColumn K v.literalRightBranch.keep.card)
    (hi : i ∈ v.rightReindex.cartesian) :
    (v.literalRightOriginal newRight).commonScalar v.literalRightBranch *
        (v.literalRightAtoms newRight).whole i =
      (v.literalRightOriginal rightAtoms).commonScalar v.literalRightBranch *
        (v.literalRightAtoms rightAtoms).whole i := by
  have hr := (v.literalRight_cartesian i).mp hi
  calc
    _ = (v.literalRightOriginal newRight).whole (v.literalRightBranch.reconstruct i) :=
      ((v.literalRightOriginal newRight).extract_whole v.literalRightBranch i hr).symm
    _ = (v.literalRightOriginal rightAtoms).whole (v.literalRightBranch.reconstruct i) :=
      rightAtoms.redistributeNormFactors_whole δ₁ δ₂ hproductRight _
    _ = _ := (v.literalRightOriginal rightAtoms).extract_whole v.literalRightBranch i hr

private theorem scalar_coefficient_congr {a b c d : ℂ}
    (h : a * b = c * d) (u w : ℂ) :
    a * (b * u * w) = c * (d * u * w) := by
  calc
    _ = (a * b) * u * w := by ring
    _ = (c * d) * u * w := by rw [h]
    _ = _ := by ring

variable (exceptional : s.CoverHybridPredicates LC RC)
variable (firstKernel : SchwartzMap ℝ ℂ) (x : ι → ℝ) (j : v.AllocationKey)
variable (firstSign : ℝ) (hlive : (v.leaf exceptional firstKernel x j).Live)
variable (X : (v.leaf exceptional firstKernel x j).ConstantAtomExtraction)
variable (binding : X.leaf.OrdinaryBinding
  (v.literalRectangles leftAtoms rightAtoms exceptional firstKernel x j firstSign hlive))
variable (hleftCommon : X.leftScalar =
  (v.literalLeftOriginal leftAtoms).commonScalar v.literalLeftBranch)
variable (hrightCommon : X.rightScalar =
  (v.literalRightOriginal rightAtoms).commonScalar v.literalRightBranch)

/-- Recompute the common extraction from the redistributed original
tables. Its two proofs use the previously established individual
coefficient identities, before any norm or sum. -/
def redistributedLiteralExtraction :
    (v.leaf exceptional firstKernel x j).ConstantAtomExtraction where
  leftScalar := (v.literalLeftOriginal newLeft).commonScalar v.literalLeftBranch
  rightScalar := (v.literalRightOriginal newRight).commonScalar v.literalRightBranch
  leftResidual := secondAllocatedLeftCoefficient (σ := σ) PUnit.{1}
    (fun i => v.block.leftResidual (v.leftReindex.index i))
    (v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).frequency
    (fun _ => PUnit.unit) j.2.1 (v.literalLeftAtoms newLeft).whole
  rightResidual := fun h i => star (secondAllocatedRightCoefficient (σ := σ) PUnit.{1}
    (fun i => v.block.rightResidual (v.rightReindex.index i))
    (v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).frequency
    (fun _ => PUnit.unit) j.2.1 (v.literalRightAtoms newRight).whole h i)
  left h hh i hi := by
    have hi' : i ∈ v.leftReindex.cartesian := by
      change i ∈ pairedAllocatedColumns j.1.val j.2.2.1.val
        v.leftReindex.plain₁ v.leftReindex.plain₂ v.leftReindex.slots
        id id HeightOneSpectrum.asIdeal at hi
      rw [paired_allocated_columns_eq_filter] at hi
      exact (Finset.mem_filter.mp hi).1
    have hc : X.leftResidual h i = secondAllocatedLeftCoefficient (σ := σ) PUnit.{1}
        (fun i => v.block.leftResidual (v.leftReindex.index i))
        (v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).frequency
        (fun _ => PUnit.unit) j.2.1 (v.literalLeftAtoms leftAtoms).whole h i :=
      binding.leftCoefficient h hh i hi
    rw [X.left h hh i hi, hleftCommon, hc]
    exact scalar_coefficient_congr
      (v.redistributed_left_common_whole leftAtoms δ₁ δ₂ hproductLeft i hi').symm _ _
  right h hh i hi := by
    have hi' : i ∈ v.rightReindex.cartesian := by
      change i ∈ pairedAllocatedColumns j.1.val j.2.2.2.val
        v.rightReindex.plain₁ v.rightReindex.plain₂ v.rightReindex.slots
        id id HeightOneSpectrum.asIdeal at hi
      rw [paired_allocated_columns_eq_filter] at hi
      exact (Finset.mem_filter.mp hi).1
    have hc : X.rightResidual h i = star (secondAllocatedRightCoefficient (σ := σ) PUnit.{1}
        (fun i => v.block.rightResidual (v.rightReindex.index i))
        (v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).frequency
        (fun _ => PUnit.unit) j.2.1 (v.literalRightAtoms rightAtoms).whole h i) := by
      simpa only [star_star] using congrArg star (binding.rightCoefficient h hh i hi)
    rw [X.right h hh i hi, hrightCommon, hc]
    simp only [secondAllocatedRightCoefficient, star_star]
    exact scalar_coefficient_congr
      (v.redistributed_right_common_whole rightAtoms δ₁ δ₂ hproductRight i hi').symm _ _

local notation "Y" => v.redistributedLiteralExtraction leftAtoms rightAtoms δ₁ δ₂
  hproductLeft hproductRight exceptional firstKernel x j firstSign hlive X binding
  hleftCommon hrightCommon

/-- The new common weight belongs to the exact original leaf. The
only omitted rows still have zero original full correlation. -/
def redistributedLiteralOrdinaryBinding :
    (Y).leaf.OrdinaryBinding
      (v.literalRectangles newLeft newRight exceptional firstKernel x j firstSign hlive) where
  rows := binding.rows
  rows_zero h hh hn := by
    have hc : (v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).correlation h = 0 := by
      by_contra hc
      exact hn (Finset.mem_filter.mpr ⟨hh, hc⟩)
    change ((_ * (v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).correlation h) *
      _ * _) = 0
    simp only [hc, mul_zero, zero_mul]
  left := rfl
  right := rfl
  exceptional _ _ := Iff.rfl
  rowWeight _ _ := by
    change ((_ * _) * _ * _) = ((_ * _ * _) * _)
    ring
  leftCoefficient _ _ _ _ := rfl
  rightCoefficient _ _ _ _ := by
    simp only [redistributedLiteralExtraction, ActualHybridLeaf.ConstantAtomExtraction.leaf,
      ActualHybridLeaf.withConstantAtoms, star_star]
  leftPoint := binding.leftPoint
  rightPoint := binding.rightPoint

@[simp] theorem redistributedLiteralExtraction_firstKernel :
    (Y).leaf.firstKernel = firstKernel := rfl

@[simp] theorem redistributedLiteralExtraction_secondKernel :
    (Y).leaf.secondKernel = v.chart.kernel := rfl

@[simp] theorem redistributedLiteralExtraction_outerWeight :
    (Y).leaf.weight = (v.leaf exceptional firstKernel x j).weight := rfl

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralActualCharacters.Recipe.redistributeNormFactors
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.redistributedLiteralExtraction
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.redistributedLiteralOrdinaryBinding
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.redistributedLiteralExtraction_firstKernel
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.redistributedLiteralExtraction_secondKernel
