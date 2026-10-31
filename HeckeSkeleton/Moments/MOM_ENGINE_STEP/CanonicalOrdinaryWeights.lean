import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalCapacityKernelMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ConstantCommonLeaf

/-!
# The literal outer weight of the same ordinary child

The original first Cauchy allowance is separated from the same actual
second child weight.  The parent's width normalization is moved once;
the original Gauss normalizers and all common/frozen/removed factors
remain inside that unchanged child weight.

The outer scalar is computed from the genuine first divisor and phase,
the first row coefficient, one pool density, the actual valuation tag,
the original orbital fiber and the second divisor and phase.  Constant
common-atom extraction changes neither this scalar nor the label.
There are no mass estimates or aggregate calibration premises here.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}

section NormalizedPair

variable {V HL HR : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ω ψ : HeckeCharacter K} {k l : ℕ}
variable {sL : ActualAllocatedSource A V HL k} {sR : ActualAllocatedSource A V HR l}
variable {DL : sL.Calibration (σ := σ) ω ψ} {DR : sR.Calibration (σ := σ) ω ψ}
variable {GL : DL.NormalizedCapacityData} {GR : DR.NormalizedCapacityData}

theorem normalizedCapacityPairWeight_parent_zero (left : GL.Child) (right : GR.Child)
    (originalLeft originalRight : ℂ) (Z parentWidth : ℝ) :
    normalizedCapacityPairWeight left right originalLeft originalRight Z parentWidth =
      normalizedCapacityPairWeight left right originalLeft originalRight Z 0 / Z ^ parentWidth := by
  simp only [normalizedCapacityPairWeight, Real.rpow_zero, div_one]

theorem normalizedCapacityPairWeight_outer_parent_zero (left : GL.Child) (right : GR.Child)
    (originalLeft originalRight : ℂ) (Z parentWidth outer : ℝ) :
    outer * normalizedCapacityPairWeight left right originalLeft originalRight Z parentWidth =
      (outer / Z ^ parentWidth) *
        normalizedCapacityPairWeight left right originalLeft originalRight Z 0 := by
  rw [normalizedCapacityPairWeight_parent_zero]
  ring

end NormalizedPair

section ActualPair

variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {H ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [IsPrincipalIdealRing A.R]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {ω ψ : HeckeCharacter K} {k l kLeft kRight : ℕ}
variable (left : SecondSideFrame (V := V) C R Ray .left k)
variable (right : SecondSideFrame (V := V) C R Ray .right l)
variable (calL : left.source.Calibration (σ := σ) ω ψ)
variable (calR : right.source.Calibration (σ := σ) ω ψ)
variable (W : ActualSecondRowMass R C kLeft kRight)
variable (BL : left.source.FrozenAtomBounds) (BR : right.source.FrozenAtomBounds)
local notation "LC" => left.arithmeticCalibration calL W BL
local notation "RC" => right.arithmeticCalibration calR W BR
variable {li : LC.CapacityInput} {ri : RC.CapacityInput}
variable (lc : LC.CapacityChild li) (rc : RC.CapacityChild ri)
variable (boundsL : Fin left.source.allocation.keep.card → ℝ)
variable (boundsR : Fin right.source.allocation.keep.card → ℝ)

theorem actualCapacityPairWeight_parent_zero (Z parentWidth : ℝ) :
    actualCapacityPairWeight left right calL calR W BL BR lc rc boundsL boundsR Z parentWidth =
      actualCapacityPairWeight left right calL calR W BL BR lc rc boundsL boundsR Z 0 /
        Z ^ parentWidth := by
  simp only [actualCapacityPairWeight, Real.rpow_zero, div_one]

theorem actualCapacityPairWeight_outer_parent_zero (Z parentWidth outer : ℝ) :
    outer * actualCapacityPairWeight left right calL calR W BL BR lc rc boundsL boundsR
      Z parentWidth =
      (outer / Z ^ parentWidth) *
        actualCapacityPairWeight left right calL calR W BL BR lc rc boundsL boundsR Z 0 := by
  rw [actualCapacityPairWeight_parent_zero]
  ring

end ActualPair

namespace ActualHybridLeaf.ConstantAtomExtraction

variable {H U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {B : ActualHybridLeaf K H U V}

/-- Moving the proved constant common atoms into rowWeight does not
alter the outer first/pool/divisor scalar of this same leaf. -/
theorem weight_eq (X : B.ConstantAtomExtraction) : X.leaf.weight = B.weight := rfl

end ActualHybridLeaf.ConstantAtomExtraction

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
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local instance : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

namespace FirstBlockPoolData.SecondStages

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap V ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockPoolData chart P M X hX}
variable (s : p.SecondStages (E := E) (hDiff := hDiff))
variable (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)
variable
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)
variable (exceptional : s.CoverHybridPredicates LA RA)

theorem classLeaf_left_weight_relative
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (j : (s.left S χ).CoveredLeafKey (p.leftSourceCovers LA S χ))
    (parentWidth total : ℝ)
    (hleftScale : NL S χ = firstLeftAllowance Z total DE.1 DE.2)
    (hrightScale : NR S χ = firstRightAllowance Z total DE.1 DE.2) :
    (s.classLeaf LA RA NL NR hNL hNR exceptional S χ (.inl j)).weight / Z ^ parentWidth =
      ‖(moebius S.val : ℂ)‖ * ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖ *
        (firstOriginalAllowanceWeight Z parentWidth total p.weightBound DE.1 DE.2 / 2) *
        ((s.left S χ).coveredLeaf (p.leftSourceCovers LA S χ) (exceptional.left S χ)
          chart.kernel chart.leftPoint j).weight / firstLeftAllowance Z total DE.1 DE.2 := by
  change ((classWeight NL NR S χ / NL S χ) *
    ((s.left S χ).coveredLeaf (p.leftSourceCovers LA S χ) (exceptional.left S χ)
      chart.kernel chart.leftPoint j).weight) / _ = _
  simp only [classWeight, FirstBlockPoolData.rowBound, hleftScale, hrightScale,
    b.activeNorm_eq, firstOriginalAllowanceWeight]
  ring

theorem classLeaf_right_weight_relative
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (j : (s.right S χ).CoveredLeafKey (p.rightSourceCovers RA S χ))
    (parentWidth total : ℝ)
    (hleftScale : NL S χ = firstLeftAllowance Z total DE.1 DE.2)
    (hrightScale : NR S χ = firstRightAllowance Z total DE.1 DE.2) :
    (s.classLeaf LA RA NL NR hNL hNR exceptional S χ (.inr j)).weight / Z ^ parentWidth =
      ‖(moebius S.val : ℂ)‖ * ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖ *
        (firstOriginalAllowanceWeight Z parentWidth total p.weightBound DE.1 DE.2 / 2) *
        ((s.right S χ).coveredLeaf (p.rightSourceCovers RA S χ) (exceptional.right S χ)
          chart.kernel (fun j => -chart.rightPoint j) j).weight /
        firstRightAllowance Z total DE.1 DE.2 := by
  change ((classWeight NL NR S χ / NR S χ) *
    ((s.right S χ).coveredLeaf (p.rightSourceCovers RA S χ) (exceptional.right S χ)
      chart.kernel (fun j => -chart.rightPoint j) j).weight) / _ = _
  simp only [classWeight, FirstBlockPoolData.rowBound, hleftScale, hrightScale,
    b.activeNorm_eq, firstOriginalAllowanceWeight]
  ring

/-- Instantiate cost with the computed pairWeight at parent width zero.
Together with actualCapacityPairWeight_parent_zero this is the exact
original first allowance, rather than an additional normalization. -/
theorem classLeaf_left_weighted_cost_relative
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (j : (s.left S χ).CoveredLeafKey (p.leftSourceCovers LA S χ))
    (parentWidth total cost : ℝ)
    (hleftScale : NL S χ = firstLeftAllowance Z total DE.1 DE.2)
    (hrightScale : NR S χ = firstRightAllowance Z total DE.1 DE.2) :
    (s.classLeaf LA RA NL NR hNL hNR exceptional S χ (.inl j)).weight *
        (cost / Z ^ parentWidth) =
      ‖(moebius S.val : ℂ)‖ * ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖ *
        (firstOriginalAllowanceWeight Z parentWidth total p.weightBound DE.1 DE.2 / 2) *
        (((s.left S χ).coveredLeaf (p.leftSourceCovers LA S χ) (exceptional.left S χ)
          chart.kernel chart.leftPoint j).weight * cost / firstLeftAllowance Z total DE.1 DE.2) := by
  calc
    _ = ((s.classLeaf LA RA NL NR hNL hNR exceptional S χ (.inl j)).weight /
        Z ^ parentWidth) * cost := by ring
    _ = _ := by
      rw [s.classLeaf_left_weight_relative LA RA NL NR hNL hNR exceptional
        S χ j parentWidth total hleftScale hrightScale]
      ring

theorem classLeaf_right_weighted_cost_relative
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (j : (s.right S χ).CoveredLeafKey (p.rightSourceCovers RA S χ))
    (parentWidth total cost : ℝ)
    (hleftScale : NL S χ = firstLeftAllowance Z total DE.1 DE.2)
    (hrightScale : NR S χ = firstRightAllowance Z total DE.1 DE.2) :
    (s.classLeaf LA RA NL NR hNL hNR exceptional S χ (.inr j)).weight *
        (cost / Z ^ parentWidth) =
      ‖(moebius S.val : ℂ)‖ * ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖ *
        (firstOriginalAllowanceWeight Z parentWidth total p.weightBound DE.1 DE.2 / 2) *
        (((s.right S χ).coveredLeaf (p.rightSourceCovers RA S χ) (exceptional.right S χ)
          chart.kernel (fun j => -chart.rightPoint j) j).weight * cost /
            firstRightAllowance Z total DE.1 DE.2) := by
  calc
    _ = ((s.classLeaf LA RA NL NR hNL hNR exceptional S χ (.inr j)).weight /
        Z ^ parentWidth) * cost := by ring
    _ = _ := by
      rw [s.classLeaf_right_weight_relative LA RA NL NR hNL hNR exceptional
        S χ j parentWidth total hleftScale hrightScale]
      ring

/-- Expose the one actual pool average and the two literal L factors
on a canonical left leaf.  The first S remains a separate coefficient. -/
theorem classLeaf_left_weight_original
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (j : (s.left S χ).CoveredLeafKey (p.leftSourceCovers LA S χ))
    (parentWidth total : ℝ)
    (hleftScale : NL S χ = firstLeftAllowance Z total DE.1 DE.2)
    (hrightScale : NR S χ = firstRightAllowance Z total DE.1 DE.2) :
    let cover := p.leftSourceCovers LA S χ;
    let tag := (s.left S χ).leafTag cover j;
    (s.classLeaf LA RA NL NR hNL hNR exceptional S χ (.inl j)).weight / Z ^ parentWidth =
      ‖(moebius S.val : ℂ)‖ * ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖ *
        (firstOriginalAllowanceWeight Z parentWidth total p.weightBound DE.1 DE.2 / 2) *
        ((4 / (p.divisorPools.leftData S).density) *
          (p.divisorPools.leftData S).tagWeight tag * (((s.left S χ).tag tag).fiber : ℝ) *
          ‖(moebius ((s.left S χ).leafSecondDivisor cover j) : ℂ)‖ *
          ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle))
            ((s.left S χ).leafSecondPhase cover j)‖) /
        firstLeftAllowance Z total DE.1 DE.2 := by
  exact (s.classLeaf_left_weight_relative LA RA NL NR hNL hNR exceptional
    S χ j parentWidth total hleftScale hrightScale).trans (by
      rw [(s.left S χ).coveredLeaf_weight_original (p.leftSourceCovers LA S χ)
        (exceptional.left S χ) chart.kernel chart.leftPoint j])

theorem classLeaf_right_weight_original
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (j : (s.right S χ).CoveredLeafKey (p.rightSourceCovers RA S χ))
    (parentWidth total : ℝ)
    (hleftScale : NL S χ = firstLeftAllowance Z total DE.1 DE.2)
    (hrightScale : NR S χ = firstRightAllowance Z total DE.1 DE.2) :
    let cover := p.rightSourceCovers RA S χ;
    let tag := (s.right S χ).leafTag cover j;
    (s.classLeaf LA RA NL NR hNL hNR exceptional S χ (.inr j)).weight / Z ^ parentWidth =
      ‖(moebius S.val : ℂ)‖ * ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖ *
        (firstOriginalAllowanceWeight Z parentWidth total p.weightBound DE.1 DE.2 / 2) *
        ((4 / (p.divisorPools.rightData S).density) *
          (p.divisorPools.rightData S).tagWeight tag * (((s.right S χ).tag tag).fiber : ℝ) *
          ‖(moebius ((s.right S χ).leafSecondDivisor cover j) : ℂ)‖ *
          ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle))
            ((s.right S χ).leafSecondPhase cover j)‖) /
        firstRightAllowance Z total DE.1 DE.2 := by
  exact (s.classLeaf_right_weight_relative LA RA NL NR hNL hNR exceptional
    S χ j parentWidth total hleftScale hrightScale).trans (by
      rw [(s.right S χ).coveredLeaf_weight_original (p.rightSourceCovers RA S χ)
        (exceptional.right S χ) chart.kernel (fun j => -chart.rightPoint j) j])

end FirstBlockPoolData.SecondStages
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actualCapacityPairWeight_outer_parent_zero
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.SecondStages.classLeaf_left_weighted_cost_relative
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.SecondStages.classLeaf_left_weight_original
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.SecondStages.classLeaf_right_weight_original
