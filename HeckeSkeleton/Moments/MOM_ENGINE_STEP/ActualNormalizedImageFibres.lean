import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualParentFibre
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectParentFibre
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedOriginalImageMass

/-!
# Physical source fibres in the normalized-kernel mass window

The constants below use only the original cap, fixed row classifier,
dyadic box, norm window and requested loss. The two actual physical
counting theorems are applied with ε/8 each. Thus their original leaf
fibres use ε/4, before any rectangle is selected.

The same active combined family is then projected to that original
image. Its four centered rectangles multiply the constant by four once.
The two side choices already in the physical theorem are not recounted.
No aggregate fibre or normalized-kernel estimate is assumed here.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments OriginalFiniteFibre ActualNormalizedPairFamily

/-- Chosen from the fixed original data before the source, scale,
normalization, active family or Fourier variables. The factor two is
the original left/right source split. -/
def kernelSourceFibreConstant (K : Type) [Field K] [NumberField K]
    (cap classifierCount dimension width : ℕ) (B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) : ℝ :=
  2 * firstMaskConstant (K := K) B (ε / 8) hB (by positivity) *
    coordinateConstant (K := K) cap classifierCount dimension width B (ε / 8)
      hB (by positivity)

theorem kernelSourceFibreConstant_pos (K : Type) [Field K] [NumberField K]
    (cap classifierCount dimension width : ℕ) (B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) :
    0 < kernelSourceFibreConstant K cap classifierCount dimension width B ε hB hε :=
  mul_pos
    (mul_pos (by norm_num) (firstMaskConstant_pos (K := K) B (ε / 8) hB (by positivity)))
    (coordinateConstant_pos (K := K) cap classifierCount dimension width B (ε / 8)
      hB (by positivity))

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Θ : Type*} [Fintype Θ] {cap dimension width : ℕ} {B Z : ℝ}
variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}

section Amplified

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)
variable (hcap : L.slotCount ≤ cap) (ε B₀ : ℝ)
variable (hB : 0 ≤ B) (hε : 0 < ε) (hbox : B₀ + 7 * ell ≤ B)
variable (rows : R.OriginalFibreRows Θ dimension width B Z)
variable (maskIdeal : Ideal (𝓞 K)) (hmask0 : maskIdeal ≠ 0)
variable (mask : OriginalMaskPrimeData s.mask maskIdeal)
variable (hmaskN : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ B)
variable (hN : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B₀)
variable (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)

include hbox rows hmask0 mask hmaskN hN

/-- Exactly the source-fibre argument of the original-image kernel
mass theorem, now proved from the actual source classifier and windows. -/
theorem original_image_kernel_source_fibre :
    ∀ j,
      ((Finset.univ.filter (fun i : R.liveLeaves L exceptional N =>
        (R.arithmeticLabels L hcap exceptional N).amplifiedIndex
          (R.arithmeticTag L exceptional N) P (R.arithmeticTag_mem L exceptional N) i = j)).card : ℝ) ≤
        kernelSourceFibreConstant K cap (Fintype.card Θ) dimension width B ε hB hε *
          Z ^ (ε / 4) := by
  intro j
  have h := R.originalAmplifiedIndex_fibre_subpower L hcap (ε / 8) (ε / 8) B₀
    hB (by positivity) (by positivity) hbox rows maskIdeal hmask0 mask hmaskN hN exceptional N j
  have he : ε / 8 + ε / 8 = ε / 4 := by ring
  simpa only [originalAmplifiedIndex, kernelSourceFibreConstant, he] using h

/-- This is the literal active carrier of the already chosen normalized
family. The genuine prime/valuation index is unchanged and costs eight
physical coordinate constants in total, not thirty-two. -/
theorem normalized_image_kernel_fibre
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (families : (R.liveLeaves L exceptional N) →
      ActualNormalizedPairFamily A σ V (Bool × Bool) ω ψ Z) :
    ∀ j,
      ((Finset.univ.filter (fun b : (combine families).active Finset.univ =>
        (R.arithmeticLabels L hcap exceptional N).rectangleAmplifiedIndex families P
          (R.arithmeticTag L exceptional N) (R.arithmeticTag_mem L exceptional N) b = j)).card : ℝ) ≤
        (4 * kernelSourceFibreConstant K cap (Fintype.card Θ) dimension width B ε hB hε) *
          Z ^ (ε / 4) := by
  intro j
  have hs := R.original_image_kernel_source_fibre L hcap ε B₀ hB hε hbox rows
    maskIdeal hmask0 mask hmaskN hN exceptional N j
  have h := activeCombine_rectangle_fibre_le families
    ((R.arithmeticLabels L hcap exceptional N).amplifiedIndex
      (R.arithmeticTag L exceptional N) P (R.arithmeticTag_mem L exceptional N)) j
    (kernelSourceFibreConstant K cap (Fintype.card Θ) dimension width B ε hB hε *
      Z ^ (ε / 4)) hs
  simpa only [OriginalArithmeticLabels.rectangleAmplifiedIndex, mul_assoc] using h

end ActualFirstSource.SecondStages
end Amplified

section Direct

variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualDirectFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)
variable (hcap : L.slotCount ≤ cap) (ε : ℝ)
variable (hB : 0 ≤ B) (hε : 0 < ε) (hZ : 1 ≤ Z)
variable (rows : R.OriginalFibreRows Θ dimension width B Z)
variable (maskIdeal : Ideal (𝓞 K)) (hmask0 : maskIdeal ≠ 0)
variable (mask : OriginalMaskPrimeData s.mask maskIdeal)
variable (hmaskN : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ B)
variable (hN : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B)
variable (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)

include hZ rows hmask0 mask hmaskN hN

theorem original_image_kernel_source_fibre :
    ∀ j,
      ((Finset.univ.filter (fun i : R.liveLeaves L exceptional N =>
        (R.arithmeticLabels L hcap exceptional N).index i = j)).card : ℝ) ≤
        kernelSourceFibreConstant K cap (Fintype.card Θ) dimension width B ε hB hε *
          Z ^ (ε / 4) := by
  intro j
  have h := R.originalIndex_fibre_subpower L hcap (ε / 8) (ε / 8) hB
    (by positivity) (by positivity) hZ rows maskIdeal hmask0 mask hmaskN hN exceptional N j
  have he : ε / 8 + ε / 8 = ε / 4 := by ring
  simpa only [originalIndex, kernelSourceFibreConstant, he] using h

/-- The direct branch works on exactly the same retained rectangles;
neither the empty slot family nor the empty active carrier is excluded. -/
theorem normalized_image_kernel_fibre
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (families : (R.liveLeaves L exceptional N) →
      ActualNormalizedPairFamily A σ V (Bool × Bool) ω ψ Z) :
    ∀ j,
      ((Finset.univ.filter (fun b : (combine families).active Finset.univ =>
        (R.arithmeticLabels L hcap exceptional N).rectangleIndex families b = j)).card : ℝ) ≤
        (4 * kernelSourceFibreConstant K cap (Fintype.card Θ) dimension width B ε hB hε) *
          Z ^ (ε / 4) := by
  intro j
  have hs := R.original_image_kernel_source_fibre L hcap ε hB hε hZ rows
    maskIdeal hmask0 mask hmaskN hN exceptional N j
  have h := activeCombine_rectangle_fibre_le families
    (R.arithmeticLabels L hcap exceptional N).index j
    (kernelSourceFibreConstant K cap (Fintype.card Θ) dimension width B ε hB hε *
      Z ^ (ε / 4)) hs
  simpa only [OriginalArithmeticLabels.rectangleIndex, mul_assoc] using h

end ActualDirectFirstSource.SecondStages
end Direct
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.kernelSourceFibreConstant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.original_image_kernel_source_fibre
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.original_image_kernel_source_fibre
