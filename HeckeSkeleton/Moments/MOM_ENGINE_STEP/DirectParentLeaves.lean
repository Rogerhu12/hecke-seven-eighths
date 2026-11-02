import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectFiniteLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectFirstTerminal
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

/-!
# The original direct parent produces the canonical finite hybrid leaves

No positive prime-pool witness is required. The original first source,
its true internal divisor/phase labels, and the same universal second
transform give the actual finite hybrid family. Both zero terms and the
original physical tails are bounded before this family is normalized.
The common capacity producer therefore receives the same leaf type for
both direct and amplified entrances.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup MeasureTheory

private abbrev direct_parent_nested_sum_fintype
    {I : Type*} {J : I → Type*} {S : (i : I) → J i → Type*} {Χ : Type*}
    {L R : (i : I) → (j : J i) → S i j → Χ → Type*}
    [Fintype I] [∀ i, Fintype (J i)] [∀ i j, Fintype (S i j)] [Fintype Χ]
    [∀ i j s χ, Fintype (L i j s χ)] [∀ i j s χ, Fintype (R i j s χ)] :
    Fintype (Σ i, Σ j, Σ s, Σ χ, L i j s χ ⊕ R i j s χ) :=
  inferInstance

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
variable {W E : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local instance directParentLeavesCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ}


variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

namespace ActualDirectFirstSource

variable (s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX)

abbrev SecondStages := ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
  (s.pieces v D).SecondStages (E := E) (hDiff := hDiff)

namespace SecondStages

variable {s} (R : s.SecondStages (E := E) (hDiff := hDiff))

abbrev TerminalCalibration (sTail sZero : Finset (ℕ × ℕ))
    (k : ℕ) (Lmax Nsave decay : ℝ) :=
  ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    (R v D).TerminalCalibration sTail sZero k Z Lmax Nsave decay

abbrev CoverHybridPredicates (L : SourceCartesianAtlas s.columns s.ideal) :=
  ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    (R v D).CoverHybridPredicates L L

abbrev CoveredLeafKey (L : SourceCartesianAtlas s.columns s.ideal) :=
  Σ v : s.CommonLabel, Σ D : ((s.block v).mask s.mask).powerset,
    (R v D).CoveredLeafKey L L

abbrev coveredLeafKeyFintype
    (L : SourceCartesianAtlas s.columns s.ideal) : Fintype (R.CoveredLeafKey L) :=
  @direct_parent_nested_sum_fintype
    s.CommonLabel
    (fun v => ((s.block v).mask s.mask).powerset)
    (fun v D => divisorPool (s.pieces v D).rightData.columns
      (fun j => ((s.pieces v D).rightData.ideal j).val))
    ((PUnit × PUnit) →* Circle)
    (fun v D S χ => ((R v D).left S χ).CoveredLeafKey
      ((s.pieces v D).leftSourceCover L S χ) ((s.pieces v D).leftSourceCover L S χ))
    (fun v D S χ => ((R v D).right S χ).CoveredLeafKey
      ((s.pieces v D).rightSourceCover L S χ) ((s.pieces v D).rightSourceCover L S χ))
    inferInstance
    (fun v => inferInstance)
    (fun v D => inferInstance)
    inferInstance
    (fun v D S χ => inferInstance)
    (fun v D S χ => inferInstance)

attribute [local instance] coveredLeafKeyFintype

def parentLeaf (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.CoveredLeafKey L) : ActualHybridLeaf K Q W E :=
  ((R j.1 j.2.1).coveredLeaf L L (N.left j.1 j.2.1) (N.right j.1 j.2.1)
    (N.left_pos j.1 j.2.1) (N.right_pos j.1 j.2.1)
    (exceptional j.1 j.2.1) j.2.2).scale (s.fiber : ℝ) (Nat.cast_nonneg _)

variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def finiteCost (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (ε Cerror Czero : ℝ) : ℝ :=
  ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    (T v D).finiteCost L L (exceptional v D)
      (N.left v D) (N.right v D) (N.left_pos v D) (N.right_pos v D) ε Cerror Czero

def secondZeroBudget (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (N : s.Normalization) (ε Czero : ℝ) : ℝ :=
  (s.fiber : ℝ) * ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    (T v D).zeroBudget (N.left v D) (N.right v D) ε Czero

def secondTailBudget (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (N : s.Normalization) (Cerror : ℝ) : ℝ :=
  (s.fiber : ℝ) * ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    (T v D).tailBudget (N.left v D) (N.right v D) Cerror

/-- Exact finite identity on the same actual second-transform leaves;
the parent fibre is paid once and the first divisor remains explicit. -/
theorem finiteCost_eq_budgets_leaves
    (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (ε Cerror Czero : ℝ) :
    (s.fiber : ℝ) * R.finiteCost T L exceptional N ε Cerror Czero =
      R.secondZeroBudget T N ε Czero + R.secondTailBudget T N Cerror +
      ∑ j : R.CoveredLeafKey L, (R.parentLeaf L exceptional N j).cost := by
  sorry

end SecondStages
end ActualDirectFirstSource

variable (hΓ μv hDiff)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
local notation "Lattice" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

include ν μ in
/-- The literal original parent reaches the same canonical hybrid
family without an artificial positive prime pool. All analytic choices
precede the moving source, first/second labels and Fourier parameters. -/
theorem actual_parent_direct_two_stage_finite_leaf_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (Lmax Nsave ξmax : ℝ) (hξmax : 0 < ξmax) :
    ∃ (decay : ℝ) (hdecay : 1 < decay),
      decay = tailDecayForWidth Lmax Nsave ξmax ∧
      firstTailCutoffExponent Lmax Nsave decay ≤ ξmax ∧
    ∃ sFirst sFirstZero sTail sZero : Finset (ℕ × ℕ),
    ∃ CfirstError CfirstZero Cerror Czero : ℝ,
      0 ≤ CfirstError ∧ 0 < CfirstZero ∧ 0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (Z : ℝ), ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX,
    ∀ N : s.Normalization,
    ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ T : R.TerminalCalibration sTail sZero k Lmax Nsave decay,
    ∀ F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay,
    ∀ (L : SourceCartesianAtlas s.columns s.ideal) (exceptional : R.CoverHybridPredicates L),
      X ≤ Z ^ ξmax ∧
      pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
        (s.fiber : ℝ) * F.cost ε CfirstError CfirstZero +
        R.secondZeroBudget T N ε Czero + R.secondTailBudget T N Cerror +
        ∑ j : R.CoveredLeafKey L, (R.parentLeaf L exceptional N j).cost := by
  sorry

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.finiteCost_eq_budgets_leaves
#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_direct_two_stage_finite_leaf_bound
