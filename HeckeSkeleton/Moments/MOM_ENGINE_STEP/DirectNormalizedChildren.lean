import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectCoveredStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedHybridLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedFamilyAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ConstantCommonLeaf

/-!
# Direct Gauss sources produce the same normalized children

The direct entrance has no prime-pool parameter. Its original second
source is flattened into the same actual hybrid leaves as every main or
valuation-error source. Dead leaves are removed by their literal finite
coefficients, and the ordinary part is passed to the same four-rectangle
normalization and capacity producer.

All slot counts are allowed. The choice between a direct entrance and
a single amplification belongs to the original finite source assembly;
there is no separate child construction for zero slots.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments

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
  [MeasurableSpace (WithLp 2 (W × E))] [BorelSpace (WithLp 2 (W × E))]
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
variable (LC RC : SourceCartesianCover G.columns G.ideal)
variable (exceptional : s.CoverHybridPredicates LC RC)
variable (F : SchwartzMap W ℂ) (x : ι → W)

/-- The direct source uses the same genuine finite support test as all
other sources. Its zero scalar and empty polynomial leaves vanish
before either continuous Fourier parameter. -/
def directLiveLeaves : Finset (s.CoveredLeafKey LC RC) :=
  ActualHybridFamily.live (s.fiberCoveredLeaf LC RC exceptional F x)

def directLiveLeaf (j : s.directLiveLeaves LC RC exceptional F x) :
    ActualHybridLeaf K Q W E :=
  s.fiberCoveredLeaf LC RC exceptional F x j.val

theorem directLiveLeaf_live (j : s.directLiveLeaves LC RC exceptional F x) :
    (s.directLiveLeaf LC RC exceptional F x j).Live :=
  ActualHybridFamily.live_spec _ j

/-- Exact separation of the original direct finite source, with the
same orbital fiber multiplicity in both terminal components. -/
theorem direct_cost_eq_live_components :
    (∑ j : s.CoveredLeafKey LC RC,
      (s.fiberCoveredLeaf LC RC exceptional F x j).cost) =
      (∑ j : s.directLiveLeaves LC RC exceptional F x,
        (s.directLiveLeaf LC RC exceptional F x j).exceptionalCost) +
      (∑ j : s.directLiveLeaves LC RC exceptional F x,
        (s.directLiveLeaf LC RC exceptional F x j).ordinaryCost) := by
  rw [ActualHybridFamily.sum_cost_eq_live]
  simp only [ActualHybridLeaf.cost, Finset.sum_add_distrib, directLiveLeaves, directLiveLeaf]

/-- The direct leaf's actual whole coefficients, rows and two Fourier
locations are identified only term by term. The child-energy bound and
its integrability are proved by the common producer. -/
theorem direct_cost_le_normalized_children
    {ω ψ : HeckeCharacter K} {Ray : Type} [CommGroup Ray] [Fintype Ray]
    {I : s.directLiveLeaves LC RC exceptional F x → Type}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    (Z parentWidth : ℝ) (hZ : 0 < Z)
    (rowDomain : Set (NonzeroIdeal K)) (heightDomain window : Set ℝ)
    (seminorms : Finset (ℕ × ℕ))
    (extract : ∀ j : s.directLiveLeaves LC RC exceptional F x,
      (s.directLiveLeaf LC RC exceptional F x j).ConstantAtomExtraction)
    (N : ∀ j : s.directLiveLeaves LC RC exceptional F x,
      (extract j).leaf.NormalizationData
        (ι := I j) C Ray ω ψ Z rowDomain heightDomain window seminorms)
    (J₁₁ J₁₂ J₂₁ J₂₂ : ℕ)
    (atoms : (ActualHybridFamily.normalizedFamily
      (ActualHybridFamily.withConstantAtoms (s.directLiveLeaf LC RC exceptional F x) extract)
        N).FourierAtomControl
        Finset.univ J₁₁ J₁₂ J₂₁ J₂₂) :
    let leaves := ActualHybridFamily.withConstantAtoms
      (s.directLiveLeaf LC RC exceptional F x) extract;
    let family := ActualHybridFamily.normalizedFamily leaves N;
    let kernels := family.kernel Finset.univ
      (actualNestedLabelMeasure (ActualHybridFamily.firstKernels leaves)
        (ActualHybridFamily.secondKernels leaves) (ActualHybridFamily.outerWeights leaves))
      parentWidth;
    (∑ j : s.CoveredLeafKey LC RC,
      (s.fiberCoveredLeaf LC RC exceptional F x j).cost) / Z ^ parentWidth ≤
      (∑ j : s.directLiveLeaves LC RC exceptional F x,
        (s.directLiveLeaf LC RC exceptional F x j).exceptionalCost) / Z ^ parentWidth +
      ∑ b : family.active Finset.univ, ∫ ξ,
        Real.sqrt (normalizedPairedEnergy (family.leftData Finset.univ b ξ)
          (family.leftParameters Finset.univ b) Z 0) *
        Real.sqrt (normalizedPairedEnergy (family.rightData Finset.univ b ξ)
          (family.rightParameters Finset.univ b) Z 0) ∂kernels b := by
  dsimp only
  let originalLeaves := s.directLiveLeaf LC RC exceptional F x
  let leaves := ActualHybridFamily.withConstantAtoms originalLeaves extract
  let family := ActualHybridFamily.normalizedFamily leaves N
  have ho := ActualHybridFamily.ordinaryBudget_le_sourcePairs leaves N parentWidth hZ
  have hc := atoms.source_integral
    (ActualHybridFamily.firstKernels leaves) (ActualHybridFamily.secondKernels leaves)
    (ActualHybridFamily.outerWeights leaves) parentWidth hZ
    (fun b _ => ActualHybridFamily.outerWeights_nonneg leaves b)
  have hord := ho.trans hc
  have horiginal := ActualHybridFamily.sum_ordinaryCost_eq_withConstantAtoms
    originalLeaves extract
  rw [← horiginal] at hord
  simp_rw [family.childPair_eq_frozen Finset.univ] at hord
  rw [s.direct_cost_eq_live_components LC RC exceptional F x, add_div]
  exact add_le_add le_rfl hord

end ActualGaussStage

variable (hΓ μv hDiff)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- A direct original Gauss source reaches the same actual normalized
family as an amplified source. The genuine zero and tail constants
are chosen uniformly before the source. There is no prime pool,
positive-slot hypothesis, or assumed source-to-child inequality. -/
theorem actual_direct_normalized_child_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (k J₁₁ J₁₂ J₂₁ J₂₂ : ℕ) (ε : ℝ) (hε : 0 < ε)
    (Lmax Nsave ξmax : ℝ) (hξmax : 0 < ξmax) :
    ∃ (decay : ℝ) (hdecay : 1 < decay),
      decay = tailDecayForWidth Lmax Nsave ξmax ∧
      firstTailCutoffExponent Lmax Nsave decay ≤ ξmax ∧
    ∃ sTail sZero : Finset (ℕ × ℕ), ∃ Cerror Czero : ℝ, 0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (Z parentWidth : ℝ), 0 < Z →
    ∀ {ι : Type*} (G : ActualGaussSource C ι)
      (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
      (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
      (LC RC : SourceCartesianCover G.columns G.ideal)
      (exceptional : s.CoverHybridPredicates LC RC)
      (F : SchwartzMap W ℂ) (x : ι → W),
    ∀ {ω ψ : HeckeCharacter K} {Ray : Type} [CommGroup Ray] [Fintype Ray],
    ∀ (I : s.directLiveLeaves LC RC exceptional F x → Type)
      [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)],
    ∀ (rowDomain : Set (NonzeroIdeal K)) (heightDomain window : Set ℝ)
      (seminorms : Finset (ℕ × ℕ)),
    ∀ extract : ∀ j : s.directLiveLeaves LC RC exceptional F x,
      (s.directLiveLeaf LC RC exceptional F x j).ConstantAtomExtraction,
    ∀ N : ∀ j : s.directLiveLeaves LC RC exceptional F x,
      (extract j).leaf.NormalizationData
        (ι := I j) C Ray ω ψ Z rowDomain heightDomain window seminorms,
    let leaves := ActualHybridFamily.withConstantAtoms
      (s.directLiveLeaf LC RC exceptional F x) extract;
    let family := ActualHybridFamily.normalizedFamily leaves N;
    ∀ atoms : family.FourierAtomControl Finset.univ J₁₁ J₁₂ J₂₁ J₂₂,
    let kernels := family.kernel Finset.univ
      (actualNestedLabelMeasure (ActualHybridFamily.firstKernels leaves)
        (ActualHybridFamily.secondKernels leaves) (ActualHybridFamily.outerWeights leaves))
      parentWidth;
    s.cutoff ≤ Z ^ ξmax ∧
      (∫ ξ, G.phaseEnergy (hDiff := hDiff) x ξ ∂actualFourierMeasure F) / Z ^ parentWidth ≤
        (actualFourierMeasure F).real Set.univ *
          (T.zeroBudget ε Czero + T.tailBudget Cerror) / Z ^ parentWidth +
        (∑ j : s.directLiveLeaves LC RC exceptional F x,
          (s.directLiveLeaf LC RC exceptional F x j).exceptionalCost) / Z ^ parentWidth +
        ∑ b : family.active Finset.univ, ∫ ξ,
          Real.sqrt (normalizedPairedEnergy (family.leftData Finset.univ b ξ)
            (family.leftParameters Finset.univ b) Z 0) *
          Real.sqrt (normalizedPairedEnergy (family.rightData Finset.univ b ξ)
            (family.rightParameters Finset.univ b) Z 0) ∂kernels b := by
  obtain ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero,
    hCerror, hCzero, hb⟩ :=
    actual_direct_fourier_covered_terminal_bound (E := E) (W := W) (ν := ν) (μ := μ)
      hΓ μv hDiff C Drecipe hD finiteTest hlc hcs k ε hε Lmax Nsave ξmax hξmax
  refine ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero,
    hCerror, hCzero, ?_⟩
  intro Z parentWidth hZ ι G s T LC RC exceptional F x ω ψ Ray instRayComm instRayFinite
    I instIFinite instIDecidable rowDomain heightDomain window seminorms extract N
  dsimp only
  intro atoms
  obtain ⟨hcutoff, hsource⟩ := hb Z G s T LC RC exceptional F x
  have hchildren := s.direct_cost_le_normalized_children LC RC exceptional F x
    Z parentWidth hZ rowDomain heightDomain window seminorms extract N
      J₁₁ J₁₂ J₂₁ J₂₂ atoms
  refine ⟨hcutoff, ?_⟩
  have hn := div_le_div_of_nonneg_right hsource (Real.rpow_nonneg hZ.le parentWidth)
  rw [add_div] at hn
  exact hn.trans ((add_le_add le_rfl hchildren).trans_eq (by ring))

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.direct_cost_le_normalized_children
#print axioms HeckeSkeleton.Moments.EngineStep.actual_direct_normalized_child_bound

