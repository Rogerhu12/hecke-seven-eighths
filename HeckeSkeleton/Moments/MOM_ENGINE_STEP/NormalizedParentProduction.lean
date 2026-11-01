import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SupportedGaussStages
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedHybridLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedFamilyAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedSourceBudgets
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ConstantCommonLeaf

/-!
# The original paired parent reaches the actual normalized child kernels

This source-producing theorem combines both actual Poisson transforms,
one original pool, the supported finite carrier, and the real normalized
capacity choices. Its four terminal quantities are the exact original
budgets. Their global small-power estimates and the mass estimate are
proved separately on this same carrier before the full output is packaged.
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
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ


variable (hΓ μv hDiff)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
variable [MeasurableSpace (WithLp 2 (W × E))] [BorelSpace (WithLp 2 (W × E))]

include ν μ in
/-- The complete original source reaches its actual normalized finite
child integrals. The same supported live leaves, all four rectangles,
and both original continuous Fourier variables are retained. Constants
for both genuine zero terms and both tails are chosen before the source.
Only individual atom/profile/capacity dictionaries are inputs. -/
theorem actual_parent_normalized_child_bound
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
    ∀ (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Z ell eps),
    ∀ {omega psi : HeckeCharacter K} (centered : Bool) (d : MomentData K omega psi)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX,
    ∀ N₀ : s.Normalization, ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ T : R.TerminalCalibration sTail sZero k Lmax Nsave decay,
    ∀ F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay,
    ∀ (L : SourceCartesianAtlas s.columns s.ideal)
      (exceptional : R.supported.gated.CoverHybridPredicates L),
    ∀ {Ray : Type} [CommGroup Ray] [Fintype Ray],
    ∀ (I : R.supported.gated.liveLeaves L exceptional N₀ → Type)
      [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)],
    ∀ (rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)) (heightDomain window : Set ℝ)
      (seminorms : Finset (ℕ × ℕ)),
    ∀ extract : ∀ j : R.supported.gated.liveLeaves L exceptional N₀,
      (R.supported.gated.parentLeaf L exceptional N₀ j.val).ConstantAtomExtraction,
    ∀ N : ∀ j : R.supported.gated.liveLeaves L exceptional N₀,
      (extract j).leaf.NormalizationData
        (ι := I j) C Ray omega psi Z rowDomain heightDomain window seminorms,
    let leaves := ActualHybridFamily.withConstantAtoms
      (fun j : R.supported.gated.liveLeaves L exceptional N₀ =>
        R.supported.gated.parentLeaf L exceptional N₀ j.val) extract;
    let family := ActualHybridFamily.normalizedFamily leaves N;
    ∀ atoms : family.FourierAtomControl Finset.univ J₁₁ J₁₂ J₂₁ J₂₂,
    let kernels := family.kernel Finset.univ
      (actualNestedLabelMeasure (ActualHybridFamily.firstKernels leaves)
        (ActualHybridFamily.secondKernels leaves) (ActualHybridFamily.outerWeights leaves))
      (a.m + a.q);
    X ≤ Z ^ ξmax ∧
      pairedStageEnergy centered d a Z t Y₁ Y₂ / Z ^ (a.m + a.q) ≤
        ActualFirstSource.SecondStages.firstZeroBudget F ε CfirstZero / Z ^ (a.m + a.q) +
          R.supported.gated.secondZeroBudget T.supported.gated N₀ ε Czero / Z ^ (a.m + a.q) +
          R.supported.gated.exceptionalBudget L exceptional N₀ / Z ^ (a.m + a.q) +
          R.supported.gated.totalTailBudget T.supported.gated F N₀ CfirstError Cerror /
            Z ^ (a.m + a.q) +
          ∑ b : family.active Finset.univ, ∫ ξ,
            Real.sqrt (normalizedPairedEnergy (family.leftData Finset.univ b ξ)
              (family.leftParameters Finset.univ b) Z 0) *
            Real.sqrt (normalizedPairedEnergy (family.rightData Finset.univ b ξ)
              (family.rightParameters Finset.univ b) Z 0) ∂kernels b := by
  obtain ⟨decay, hdecay, hchoice, hq, sFirst, sFirstZero, sTail, sZero,
    CfirstError, CfirstZero, Cerror, Czero, hCfE, hCfZ, hCE, hCZ, hb⟩ :=
    actual_parent_two_stage_finite_leaf_bound (W := W) (E := E) (ν := ν) (μ := μ)
      hΓ μv hDiff C Drecipe hD finiteTest hlc hcs k ε hε Lmax Nsave ξmax hξmax
  refine ⟨decay, hdecay, hchoice, hq, sFirst, sFirstZero, sTail, sZero,
    CfirstError, CfirstZero, Cerror, Czero, hCfE, hCfZ, hCE, hCZ, ?_⟩
  intro Z ell eps bad P omega psi centered d a t Y₁ Y₂ X hX s N₀ R T F L exceptional
    Ray instRayComm instRayFinite I instIFinite instIDecidable rowDomain heightDomain window seminorms
    extract N
  dsimp only
  intro atoms
  let originalLeaves := fun j : R.supported.gated.liveLeaves L exceptional N₀ =>
    R.supported.gated.parentLeaf L exceptional N₀ j.val
  let leaves := ActualHybridFamily.withConstantAtoms originalLeaves extract
  let family := ActualHybridFamily.normalizedFamily leaves N
  have hZ : 0 < Z := zero_lt_one.trans P.base_gt_one
  obtain ⟨hcutoff, hp⟩ := hb Z ell eps bad P centered d a t Y₁ Y₂ X hX s N₀
    R.supported T.supported F L exceptional
  have ho := ActualHybridFamily.ordinaryBudget_le_sourcePairs leaves N (a.m + a.q) hZ
  have hc := atoms.source_integral
    (ActualHybridFamily.firstKernels leaves) (ActualHybridFamily.secondKernels leaves)
    (ActualHybridFamily.outerWeights leaves) (a.m + a.q) hZ
    (fun b _ => ActualHybridFamily.outerWeights_nonneg leaves b)
  have hord := ho.trans hc
  have horiginal :
      R.supported.gated.ordinaryBudget L exceptional N₀ = ∑ j, (leaves j).ordinaryCost := by
    change (∑ j, (originalLeaves j).ordinaryCost) = _
    exact ActualHybridFamily.sum_ordinaryCost_eq_withConstantAtoms originalLeaves extract
  rw [← horiginal] at hord
  simp_rw [family.childPair_eq_frozen Finset.univ] at hord
  refine ⟨hcutoff, ?_⟩
  calc
    _ ≤ ActualFirstSource.SecondStages.firstZeroBudget F ε CfirstZero / Z ^ (a.m + a.q) +
          R.supported.gated.secondZeroBudget T.supported.gated N₀ ε Czero / Z ^ (a.m + a.q) +
          R.supported.gated.exceptionalBudget L exceptional N₀ / Z ^ (a.m + a.q) +
          R.supported.gated.totalTailBudget T.supported.gated F N₀ CfirstError Cerror /
            Z ^ (a.m + a.q) +
          R.supported.gated.ordinaryBudget L exceptional N₀ / Z ^ (a.m + a.q) := by
      simpa only [add_div] using
        div_le_div_of_nonneg_right hp (Real.rpow_nonneg hZ.le (a.m + a.q))
    _ ≤ _ := add_le_add le_rfl hord

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_normalized_child_bound
