import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualParentFibre
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectCoveredFibreMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectLeafNormWindows

set_option linter.unusedSectionVars false

/-!
# Original finite fibres for the direct parent entrance

The direct source uses the same literal allocation fingerprint and the
same dependent finite-count lemmas as the amplified source.  Its index
is computed from the actual live leaves without any prime-pool tag.
The original masks, row classifier and Cartesian atlas prove the full
fibre estimate, including any actual retained rectangle subset.
-/

noncomputable section
open HeckePort.IdealMobiusDivisorSum
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup HeckePort.Moments.Support
open CommonSupportMass UniqueFactorizationMonoid OriginalFiniteFibre

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
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local instance directParentFibreCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Θ : Type*} [Fintype Θ] {cap dimension width : ℕ} {B Z : ℝ}

namespace DirectGaussData

variable {ι : Type*} {originalColumns : Finset ι} {originalIdeal : ι → A.Exterior}
variable (d : DirectGaussData C ι)
variable (T : SourceCartesianAtlas originalColumns originalIdeal)
variable (support : Finset (Ideal (𝓞 K))) (D₀ : Ideal (𝓞 K))
variable (hcolumns : d.columns = originalColumns.filter
  (fun i => supportExtract (originalIdeal i).val support = D₀))
variable (hideal : ∀ i, (d.ideal i).val = supportResidual (originalIdeal i).val support)
variable (c : ι → ℂ)
variable (s : ActualGaussStage (E := E) hΓ μv hDiff (d.directSource c) finiteTest)
local notation "CV" => d.sourceCartesianCover T support D₀ hcolumns hideal c

theorem original_predicate_subpower
    (hcap : T.slotCount ≤ cap) (ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (hZ : 1 ≤ Z)
    (rows : s.OriginalFibreRows Θ dimension width B Z)
    (hD₀ : D₀ ≠ 0) (hND₀ : (Ideal.absNorm D₀ : ℝ) ≤ Z ^ B)
    (hN : ∀ i ∈ d.columns, (Ideal.absNorm (d.ideal i).val : ℝ) ≤ Z ^ B)
    (pred : s.CoveredLeafKey CV CV → Prop)
    (hrow : ∀ j, pred j → s.rowPresent CV CV j)
    (pair : Ideal (𝓞 K) × Ideal (𝓞 K)) (a : OriginalAllocationFingerprint K cap)
    (hcommon : ∀ j, pred j → j.1.1.val = pair)
    (hallocation : ∀ j, pred j →
      s.cappedAllocationFingerprint CV CV
        (fun q => (d.sourceCartesianCover_slotCount_le T support D₀ hcolumns hideal c q).trans hcap)
        (fun q => (d.sourceCartesianCover_slotCount_le T support D₀ hcolumns hideal c q).trans hcap)
        j = a) :
    realCount pred ≤ coordinateConstant (K := K) cap (Fintype.card Θ)
      dimension width B ε hB hε * Z ^ ε := by
  sorry

end DirectGaussData

namespace FirstBlockDirectData

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockDirectData chart M X hX}

namespace SecondStages

variable (R : p.SecondStages (E := E) (hDiff := hDiff))
variable (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)

def rowPresent (j : R.CoveredLeafKey LA RA) : Prop :=
  match j.2.2 with
  | .inl k => (R.left j.1 j.2.1).rowPresent
      (p.leftSourceCover LA j.1 j.2.1) (p.leftSourceCover LA j.1 j.2.1) k
  | .inr k => (R.right j.1 j.2.1).rowPresent
      (p.rightSourceCover RA j.1 j.2.1) (p.rightSourceCover RA j.1 j.2.1) k

structure OriginalFibreRows (Θ : Type*) (dimension width : ℕ) (B Z : ℝ) where
  left : ∀ S χ, (R.left S χ).OriginalFibreRows Θ dimension width B Z
  right : ∀ S χ, (R.right S χ).OriginalFibreRows Θ dimension width B Z

theorem rowPresent_of_leaf_live
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)
    (exceptional : R.CoverHybridPredicates LA RA)
    (j : R.CoveredLeafKey LA RA)
    (hj : (R.coveredLeaf LA RA NL NR hNL hNR exceptional j).Live) :
    R.rowPresent LA RA j := by
  sorry

theorem original_predicate_subpower
    (hLA : LA.slotCount ≤ cap) (hRA : RA.slotCount ≤ cap)
    (ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (hZ : 1 ≤ Z)
    (rows : R.OriginalFibreRows Θ dimension width B Z)
    (hDE : DE.1 ≠ 0 ∧ DE.2 ≠ 0)
    (hNDE : (Ideal.absNorm DE.1 : ℝ) ≤ Z ^ B ∧ (Ideal.absNorm DE.2 : ℝ) ≤ Z ^ B)
    (hL : ∀ i ∈ left, (Ideal.absNorm (fullI i).val : ℝ) ≤ Z ^ B)
    (hR : ∀ i ∈ right, (Ideal.absNorm (fullJ i).val : ℝ) ≤ Z ^ B)
    (pred : R.CoveredLeafKey LA RA → Prop)
    (hrow : ∀ j, pred j → R.rowPresent LA RA j)
    (S₀ : Ideal (𝓞 K)) (pair : Ideal (𝓞 K) × Ideal (𝓞 K))
    (a : OriginalAllocationFingerprint K cap)
    (hS₀ : ∀ j, pred j → j.1.val = S₀)
    (hcommon : ∀ j, pred j → R.commonLabel LA RA j = pair)
    (hallocation : ∀ j, pred j → R.allocationFingerprint LA RA hLA hRA j = a) :
    realCount pred ≤ 2 * (coordinateConstant (K := K) cap (Fintype.card Θ)
      dimension width B ε hB hε * Z ^ ε) := by
  sorry

end SecondStages
end FirstBlockDirectData

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualDirectFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)

def rowPresent (j : R.CoveredLeafKey L) : Prop :=
  (R j.1 j.2.1).rowPresent L L j.2.2

structure OriginalFibreRows (Θ : Type*) (dimension width : ℕ) (B Z : ℝ) where
  source : ∀ v D, (R v D).OriginalFibreRows Θ dimension width B Z

theorem rowPresent_of_live (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.liveLeaves L exceptional N) : R.rowPresent L j.val := by
  sorry

theorem original_predicate_subpower
    (hcap : L.slotCount ≤ cap) (δ₁ δ₂ : ℝ)
    (hB : 0 ≤ B) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hZ : 1 ≤ Z)
    (rows : R.OriginalFibreRows Θ dimension width B Z)
    (maskIdeal : Ideal (𝓞 K)) (hmask0 : maskIdeal ≠ 0)
    (mask : OriginalMaskPrimeData s.mask maskIdeal)
    (hmaskN : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ B)
    (hN : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B)
    (pred : R.CoveredLeafKey L → Prop) (hrow : ∀ j, pred j → R.rowPresent L j)
    (firstPair : Ideal (𝓞 K) × Ideal (𝓞 K)) (S₀ : Ideal (𝓞 K))
    (secondPair : Ideal (𝓞 K) × Ideal (𝓞 K))
    (allocation : OriginalAllocationFingerprint K cap)
    (hfirst : ∀ j, pred j → j.1.val = firstPair)
    (hS₀ : ∀ j, pred j → j.2.2.1.val = S₀)
    (hsecond : ∀ j, pred j → R.commonLabel L j = secondPair)
    (halloc : ∀ j, pred j →
      (R j.1 j.2.1).allocationFingerprint L L hcap hcap j.2.2 = allocation) :
    realCount pred ≤
      2 * firstMaskConstant (K := K) B δ₁ hB hδ₁ *
        coordinateConstant (K := K) cap (Fintype.card Θ) dimension width B δ₂ hB hδ₂ *
          Z ^ (δ₁ + δ₂) := by
  sorry

abbrev ArithmeticIndex (hcap : L.slotCount ≤ cap)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization) :=
  (R.arithmeticLabels L hcap exceptional N).carrier.Index

def originalIndex (hcap : L.slotCount ≤ cap)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.liveLeaves L exceptional N) : R.ArithmeticIndex L hcap exceptional N :=
  (R.arithmeticLabels L hcap exceptional N).index j

theorem originalIndex_fibre_subpower
    (hcap : L.slotCount ≤ cap) (δ₁ δ₂ : ℝ)
    (hB : 0 ≤ B) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hZ : 1 ≤ Z)
    (rows : R.OriginalFibreRows Θ dimension width B Z)
    (maskIdeal : Ideal (𝓞 K)) (hmask0 : maskIdeal ≠ 0)
    (mask : OriginalMaskPrimeData s.mask maskIdeal)
    (hmaskN : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ B)
    (hN : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.ArithmeticIndex L hcap exceptional N) :
    ((Finset.univ.filter (fun i : R.liveLeaves L exceptional N =>
        R.originalIndex L hcap exceptional N i = j)).card : ℝ) ≤
      2 * firstMaskConstant (K := K) B δ₁ hB hδ₁ *
        coordinateConstant (K := K) cap (Fintype.card Θ) dimension width B δ₂ hB hδ₂ *
          Z ^ (δ₁ + δ₂) := by
  sorry

/-- The exact active label subset of the normalized direct family,
including all retained ordinary rectangles, has the uniform fibre. -/
theorem originalIndex_retained_rectangles_fibre_subpower
    (hcap : L.slotCount ≤ cap) (δ₁ δ₂ : ℝ)
    (hB : 0 ≤ B) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hZ : 1 ≤ Z)
    (rows : R.OriginalFibreRows Θ dimension width B Z)
    (maskIdeal : Ideal (𝓞 K)) (hmask0 : maskIdeal ≠ 0)
    (mask : OriginalMaskPrimeData s.mask maskIdeal)
    (hmaskN : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ B)
    (hN : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (active : Finset ((R.liveLeaves L exceptional N) × (Bool × Bool)))
    (j : R.ArithmeticIndex L hcap exceptional N) :
    ((Finset.univ.filter (fun i : active => R.originalIndex L hcap exceptional N i.val.1 = j)).card : ℝ) ≤
      8 * firstMaskConstant (K := K) B δ₁ hB hδ₁ *
        coordinateConstant (K := K) cap (Fintype.card Θ) dimension width B δ₂ hB hδ₂ *
          Z ^ (δ₁ + δ₂) := by
  sorry

end ActualDirectFirstSource.SecondStages
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.DirectGaussData.original_predicate_subpower
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.originalIndex_fibre_subpower
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.originalIndex_retained_rectangles_fibre_subpower
