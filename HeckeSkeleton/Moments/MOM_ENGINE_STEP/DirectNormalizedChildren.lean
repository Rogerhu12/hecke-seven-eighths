import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectCoveredStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectParentLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectSupportedLeaves
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
local instance : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

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

namespace ActualDirectFirstSource

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ} {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters} {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}

namespace TerminalCalibration

variable {sFirst sFirstZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def firstZeroBudget (F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay)
    (ε CfirstZero : ℝ) : ℝ :=
  (s.fiber : ℝ) * CfirstZero * F.zeroAmplitude * Z ^ (F.productExponent * ε)

def firstTailBudget (F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay)
    (CfirstError : ℝ) : ℝ :=
  (s.fiber : ℝ) * CfirstError * F.tailAmplitude * Z ^ (-Nsave)

end TerminalCalibration

namespace SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)
variable (exceptional : R.CoverHybridPredicates L) (N₀ : s.Normalization)

def liveLeaf (j : R.liveLeaves L exceptional N₀) : ActualHybridLeaf K Q W E :=
  R.parentLeaf L exceptional N₀ j.val

theorem liveLeaf_live (j : R.liveLeaves L exceptional N₀) :
    (R.liveLeaf L exceptional N₀ j).Live :=
  ActualHybridFamily.live_spec _ j

def exceptionalBudget : ℝ :=
  ∑ j : R.liveLeaves L exceptional N₀, (R.liveLeaf L exceptional N₀ j).exceptionalCost

def ordinaryBudget : ℝ :=
  ∑ j : R.liveLeaves L exceptional N₀, (R.liveLeaf L exceptional N₀ j).ordinaryCost

theorem cost_eq_live_components :
    (∑ j : R.CoveredLeafKey L, (R.parentLeaf L exceptional N₀ j).cost) =
      R.exceptionalBudget L exceptional N₀ + R.ordinaryBudget L exceptional N₀ := by
  rw [ActualHybridFamily.sum_cost_eq_live]
  simp only [ActualHybridLeaf.cost, Finset.sum_add_distrib,
    exceptionalBudget, ordinaryBudget, liveLeaves, liveLeaf]

end SecondStages
end ActualDirectFirstSource

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

include ν μ in
/-- The literal original paired parent also reaches the same retained
normalized children through the direct entrance.  Both Poisson stages,
both zero terms and both tails are obtained from their proved source
theorems.  The only new coefficient input is the individual constant
common-atom extraction; all original labels and Fourier measures stay
in the same family.  No prime pool or slot-count case is assumed. -/
theorem actual_parent_direct_normalized_child_bound
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
    ∃ sFirst sFirstZero sTail sZero : Finset (ℕ × ℕ),
    ∃ CfirstError CfirstZero Cerror Czero : ℝ,
      0 ≤ CfirstError ∧ 0 < CfirstZero ∧ 0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (Z : ℝ), ∀ {omega psi : HeckeCharacter K} (centered : Bool) (d : MomentData K omega psi)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX,
    ∀ N₀ : s.Normalization, ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ T : R.TerminalCalibration sTail sZero k Lmax Nsave decay,
    ∀ F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay,
    ∀ (L : SourceCartesianAtlas s.columns s.ideal) (exceptional : R.CoverHybridPredicates L),
    ∀ {Ray : Type} [CommGroup Ray] [Fintype Ray],
    ∀ (I : R.liveLeaves L exceptional N₀ → Type)
      [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)],
    ∀ (rowDomain : Set (NonzeroIdeal K)) (heightDomain window : Set ℝ)
      (seminorms : Finset (ℕ × ℕ)),
    ∀ extract : ∀ j : R.liveLeaves L exceptional N₀,
      (R.liveLeaf L exceptional N₀ j).ConstantAtomExtraction,
    ∀ N : ∀ j : R.liveLeaves L exceptional N₀,
      (extract j).leaf.NormalizationData
        (ι := I j) C Ray omega psi Z rowDomain heightDomain window seminorms,
    let leaves := ActualHybridFamily.withConstantAtoms (R.liveLeaf L exceptional N₀) extract;
    let family := ActualHybridFamily.normalizedFamily leaves N;
    ∀ atoms : family.FourierAtomControl Finset.univ J₁₁ J₁₂ J₂₁ J₂₂,
    let kernels := family.kernel Finset.univ
      (actualNestedLabelMeasure (ActualHybridFamily.firstKernels leaves)
        (ActualHybridFamily.secondKernels leaves) (ActualHybridFamily.outerWeights leaves))
      (a.m + a.q);
    X ≤ Z ^ ξmax ∧
      pairedStageEnergy centered d a Z t Y₁ Y₂ / Z ^ (a.m + a.q) ≤
        F.firstZeroBudget ε CfirstZero / Z ^ (a.m + a.q) +
          R.secondZeroBudget T N₀ ε Czero / Z ^ (a.m + a.q) +
          R.exceptionalBudget L exceptional N₀ / Z ^ (a.m + a.q) +
          (F.firstTailBudget CfirstError + R.secondTailBudget T N₀ Cerror) /
            Z ^ (a.m + a.q) +
          ∑ b : family.active Finset.univ, ∫ ξ,
            Real.sqrt (normalizedPairedEnergy (family.leftData Finset.univ b ξ)
              (family.leftParameters Finset.univ b) Z 0) *
            Real.sqrt (normalizedPairedEnergy (family.rightData Finset.univ b ξ)
              (family.rightParameters Finset.univ b) Z 0) ∂kernels b := by
  obtain ⟨decay, hdecay, hchoice, hq, sFirst, sFirstZero, sTail, sZero,
      CfirstError, CfirstZero, Cerror, Czero, hCfE, hCfZ, hCE, hCZ, hb⟩ :=
    actual_parent_direct_two_stage_finite_leaf_bound (W := W) (E := E) (ν := ν) (μ := μ)
      hΓ μv hDiff C Drecipe hD finiteTest hlc hcs k ε hε Lmax Nsave ξmax hξmax
  refine ⟨decay, hdecay, hchoice, hq, sFirst, sFirstZero, sTail, sZero,
    CfirstError, CfirstZero, Cerror, Czero, hCfE, hCfZ, hCE, hCZ, ?_⟩
  intro Z omega psi centered d a t Y₁ Y₂ X hX s N₀ R T F L exceptional
    Ray instRayComm instRayFinite I instIFinite instIDecidable
    rowDomain heightDomain window seminorms extract N
  dsimp only
  intro atoms
  let originalLeaves := R.liveLeaf L exceptional N₀
  let leaves := ActualHybridFamily.withConstantAtoms originalLeaves extract
  let family := ActualHybridFamily.normalizedFamily leaves N
  have hZ : 0 < Z := lt_of_lt_of_le zero_lt_one F.windows.base_ge_one
  obtain ⟨hcutoff, hp⟩ := hb Z centered d a t Y₁ Y₂ X hX s N₀ R T F L exceptional
  have ho := ActualHybridFamily.ordinaryBudget_le_sourcePairs leaves N (a.m + a.q) hZ
  have hc := atoms.source_integral
    (ActualHybridFamily.firstKernels leaves) (ActualHybridFamily.secondKernels leaves)
    (ActualHybridFamily.outerWeights leaves) (a.m + a.q) hZ
    (fun b _ => ActualHybridFamily.outerWeights_nonneg leaves b)
  have hord := ho.trans hc
  have horiginal : R.ordinaryBudget L exceptional N₀ = ∑ j, (leaves j).ordinaryCost := by
    change (∑ j, (originalLeaves j).ordinaryCost) = _
    exact ActualHybridFamily.sum_ordinaryCost_eq_withConstantAtoms originalLeaves extract
  rw [← horiginal] at hord
  simp_rw [family.childPair_eq_frozen Finset.univ] at hord
  have hraw : pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
      F.firstZeroBudget ε CfirstZero + R.secondZeroBudget T N₀ ε Czero +
        R.exceptionalBudget L exceptional N₀ +
        (F.firstTailBudget CfirstError + R.secondTailBudget T N₀ Cerror) +
        R.ordinaryBudget L exceptional N₀ := by
    apply hp.trans_eq
    rw [R.cost_eq_live_components L exceptional N₀]
    simp only [ActualDirectFirstSource.TerminalCalibration.cost,
      ActualDirectFirstSource.TerminalCalibration.firstZeroBudget,
      ActualDirectFirstSource.TerminalCalibration.firstTailBudget]
    ring
  refine ⟨hcutoff, ?_⟩
  calc
    _ ≤ F.firstZeroBudget ε CfirstZero / Z ^ (a.m + a.q) +
          R.secondZeroBudget T N₀ ε Czero / Z ^ (a.m + a.q) +
          R.exceptionalBudget L exceptional N₀ / Z ^ (a.m + a.q) +
          (F.firstTailBudget CfirstError + R.secondTailBudget T N₀ Cerror) /
            Z ^ (a.m + a.q) + R.ordinaryBudget L exceptional N₀ / Z ^ (a.m + a.q) := by
      simpa only [add_div] using
        div_le_div_of_nonneg_right hraw (Real.rpow_nonneg hZ.le (a.m + a.q))
    _ ≤ _ := add_le_add le_rfl hord

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.direct_cost_le_normalized_children
#print axioms HeckeSkeleton.Moments.EngineStep.actual_direct_normalized_child_bound
#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_direct_normalized_child_bound

