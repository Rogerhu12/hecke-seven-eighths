import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.DirectLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectFirstTerminal

set_option linter.unusedSectionVars false
set_option autoImplicit false

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

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup MeasureTheory

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
  FirstBlockDirectData.SecondStages (s.pieces v D) (E := E) (hDiff := hDiff)

namespace SecondStages

variable {s} (R : ActualDirectFirstSource.SecondStages s (E := E) (hDiff := hDiff))

abbrev TerminalCalibration (sTail sZero : Finset (ℕ × ℕ))
    (k : ℕ) (Lmax Nsave decay : ℝ) :=
  ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    FirstBlockDirectData.SecondStages.TerminalCalibration (R v D) sTail sZero k Z Lmax Nsave decay

abbrev CoverHybridPredicates (L : SourceCartesianAtlas s.columns s.ideal) :=
  ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    FirstBlockDirectData.SecondStages.CoverHybridPredicates (R v D) L L

abbrev CoveredLeafKey (L : SourceCartesianAtlas s.columns s.ideal) :=
  Σ v : s.CommonLabel, Σ D : ((s.block v).mask s.mask).powerset,
    FirstBlockDirectData.SecondStages.CoveredLeafKey (R v D) L L

def parentLeaf (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : ActualDirectFirstSource.SecondStages.CoverHybridPredicates R L) (N : s.Normalization)
    (j : ActualDirectFirstSource.SecondStages.CoveredLeafKey R L) : ActualHybridLeaf K Q W E :=
  (FirstBlockDirectData.SecondStages.coveredLeaf (R j.1 j.2.1) L L (N.left j.1 j.2.1) (N.right j.1 j.2.1)
    (N.left_pos j.1 j.2.1) (N.right_pos j.1 j.2.1)
    (exceptional j.1 j.2.1) j.2.2).scale (s.fiber : ℝ) (Nat.cast_nonneg _)

end SecondStages
end ActualDirectFirstSource
end HeckeSkeleton.Moments.EngineStepV2

