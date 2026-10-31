import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCoveredLabels
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstBlockFiniteLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityRelativeScalar

/-!
# Literal canonical weights for the exceptional terminal

These identities expose the original second divisor and phase in each
canonical leaf, then the one actual pool density and valuation tag.
The original first coefficient is normalized by its two actual Cauchy
allowances.  Each side keeps its factor one half and the selected
allowance denominator; no terminal estimate or reweighted carrier is
introduced by these identities.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments HeckePort.Moments.MobiusRegroup

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
local instance : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}


namespace ActualGaussStage.CoveredClassKey

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest}
variable {LC RC : SourceCartesianCover G.columns G.ideal}
variable (v : s.CoveredClassKey LC RC)

@[simp] theorem leaf_weight_original
    (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (j : v.AllocationKey) :
    (v.leaf exceptional F x j).weight =
      ‖(moebius j.1.val : ℂ)‖ *
        ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) j.2.1‖ := rfl

end ActualGaussStage.CoveredClassKey

namespace ActualPoolStages

variable {ι : Type*} {d : FirstGaussPoolData C P ι} {c : ι → ℂ}
variable (s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest)
variable (B : d.SourceCovers c)

/-- Projection from the canonical leaf to its literal pool source tag. -/
def leafTag : s.CoveredLeafKey B → PoolSourceTag P
  | .inl _ => .inl ()
  | .inr (.inl j) => .inr (.inl j.1)
  | .inr (.inr (.inl j)) => .inr (.inr (.inl j.1))
  | .inr (.inr (.inr j)) => .inr (.inr (.inr j.1))

/-- The remaining key stays in the genuine stage at that original tag. -/
def leafStageKey : ∀ j : s.CoveredLeafKey B,
    (s.tag (s.leafTag B j)).CoveredLeafKey
      (B.tag (s.leafTag B j)) (B.tag (s.leafTag B j))
  | .inl j => j
  | .inr (.inl j) => j.2
  | .inr (.inr (.inl j)) => j.2
  | .inr (.inr (.inr j)) => j.2

def leafSecondDivisor (j : s.CoveredLeafKey B) : Ideal (𝓞 K) :=
  (s.leafStageKey B j).2.1.val

def leafSecondPhase (j : s.CoveredLeafKey B) : (PUnit × PUnit) →* Circle :=
  (s.leafStageKey B j).2.2.1

/-- The canonical scalar has one density, the actual local valuation
weight, the actual orbital fibre, and the actual L/phase coefficients. -/
theorem coveredLeaf_weight_original
    (exceptional : s.CoverHybridPredicates B)
    (F : SchwartzMap W ℂ) (x : ι → W) (j : s.CoveredLeafKey B) :
    (s.coveredLeaf B exceptional F x j).weight =
      (4 / d.density) * d.tagWeight (s.leafTag B j) *
        ((s.tag (s.leafTag B j)).fiber : ℝ) *
        ‖(moebius (s.leafSecondDivisor B j) : ℂ)‖ *
        ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) (s.leafSecondPhase B j)‖ := by
  rcases j with j | (⟨p, j⟩ | (⟨p, j⟩ | ⟨p, j⟩)) <;>
    dsimp only [coveredLeaf, ActualHybridLeaf.scale, ActualGaussStage.fiberCoveredLeaf,
      ActualGaussStage.coveredLeaf, ActualGaussStage.CoveredClassKey.leaf,
      fullCorrelationHybridLeaf, leafTag, leafStageKey, leafSecondDivisor, leafSecondPhase,
      tag, FirstGaussPoolData.tagWeight] <;> ring

end ActualPoolStages

namespace FirstBlockPoolData

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap V ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockPoolData chart P M X hX}


namespace SecondStages

variable (s : p.SecondStages (E := E) (hDiff := hDiff))
variable (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)
variable
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)
variable (exceptional : s.CoverHybridPredicates LA RA)

/-- Exact original first normalization on a canonical left leaf. -/
theorem classLeaf_left_exceptional_relative
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (j : (s.left S χ).CoveredLeafKey (p.leftSourceCovers LA S χ))
    (parentWidth total : ℝ)
    (hleftScale : NL S χ = firstLeftAllowance Z total DE.1 DE.2)
    (hrightScale : NR S χ = firstRightAllowance Z total DE.1 DE.2) :
    (s.classLeaf LA RA NL NR hNL hNR exceptional S χ (.inl j)).exceptionalCost /
        Z ^ parentWidth =
      ‖(moebius S.val : ℂ)‖ * ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖ *
        (firstOriginalAllowanceWeight Z parentWidth total p.weightBound DE.1 DE.2 / 2) *
        ((s.left S χ).coveredLeaf (p.leftSourceCovers LA S χ) (exceptional.left S χ)
          chart.kernel chart.leftPoint j).exceptionalCost /
        firstLeftAllowance Z total DE.1 DE.2 := by
  change (((s.left S χ).coveredLeaf (p.leftSourceCovers LA S χ) (exceptional.left S χ)
      chart.kernel chart.leftPoint j).scale
      (classWeight NL NR S χ / NL S χ)
      (div_nonneg (classWeight_nonneg NL NR S χ) (hNL S χ).le)).exceptionalCost / _ = _
  rw [ActualHybridLeaf.scale_exceptionalCost]
  simp only [classWeight, FirstBlockPoolData.rowBound, hleftScale, hrightScale,
    b.activeNorm_eq, firstOriginalAllowanceWeight]
  ring

/-- The same computation holds on the original right leaf with its
own denominator; the two sides therefore pay the factor one half once. -/
theorem classLeaf_right_exceptional_relative
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (j : (s.right S χ).CoveredLeafKey (p.rightSourceCovers RA S χ))
    (parentWidth total : ℝ)
    (hleftScale : NL S χ = firstLeftAllowance Z total DE.1 DE.2)
    (hrightScale : NR S χ = firstRightAllowance Z total DE.1 DE.2) :
    (s.classLeaf LA RA NL NR hNL hNR exceptional S χ (.inr j)).exceptionalCost /
        Z ^ parentWidth =
      ‖(moebius S.val : ℂ)‖ * ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖ *
        (firstOriginalAllowanceWeight Z parentWidth total p.weightBound DE.1 DE.2 / 2) *
        ((s.right S χ).coveredLeaf (p.rightSourceCovers RA S χ) (exceptional.right S χ)
          chart.kernel (fun j => -chart.rightPoint j) j).exceptionalCost /
        firstRightAllowance Z total DE.1 DE.2 := by
  change (((s.right S χ).coveredLeaf (p.rightSourceCovers RA S χ) (exceptional.right S χ)
      chart.kernel (fun j => -chart.rightPoint j) j).scale
      (classWeight NL NR S χ / NR S χ)
      (div_nonneg (classWeight_nonneg NL NR S χ) (hNR S χ).le)).exceptionalCost / _ = _
  rw [ActualHybridLeaf.scale_exceptionalCost]
  simp only [classWeight, FirstBlockPoolData.rowBound, hleftScale, hrightScale,
    b.activeNorm_eq, firstOriginalAllowanceWeight]
  ring

end SecondStages
end FirstBlockPoolData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.coveredLeaf_weight_original
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.SecondStages.classLeaf_left_exceptional_relative
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.SecondStages.classLeaf_right_exceptional_relative
