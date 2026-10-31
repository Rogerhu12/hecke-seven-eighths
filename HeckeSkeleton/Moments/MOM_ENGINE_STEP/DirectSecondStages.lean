import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualDirectFirstSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectSourceCover
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectCoveredStage

/-!
# Direct original first-divisor sources use the same second stages

There is one actual unamplified source on each side of every original
first Möbius/phase label. Its rows, coefficients and physical cutoff
precede Fourier parameters. The original Cartesian atlas constructs
its support cover, and the universal second transform constructs the
same canonical hybrid leaves used by prime-amplified input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

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
local instance directSecondStagesCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ}

namespace FirstBlockDirectData

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap V ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}

def leftDivisorCoefficient (p : FirstBlockDirectData chart M X hX)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (i : ι) : ℂ :=
  if S.val ∣ (p.leftData.ideal i).val then
    p.originalLeftCoefficient i * (fixedLeftPhase PUnit χ PUnit.unit : ℂ) else 0

def rightDivisorCoefficient (p : FirstBlockDirectData chart M X hX)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (j : κ) : ℂ :=
  if S.val ∣ (p.rightData.ideal j).val then
    p.originalRightCoefficient j * (fixedRightPhase PUnit χ PUnit.unit : ℂ) else 0

/-- Literal direct stages at every actual first divisor and phase.
There is no bound field; each stage contains only original charts. -/
structure SecondStages (p : FirstBlockDirectData chart M X hX) where
  left : ∀ S χ, ActualGaussStage (E := E) hΓ μv hDiff
    (p.leftData.directSource (p.leftDivisorCoefficient S χ)) finiteTest
  right : ∀ S χ, ActualGaussStage (E := E) hΓ μv hDiff
    (p.rightData.directSource (p.rightDivisorCoefficient S χ)) finiteTest


variable (p : FirstBlockDirectData chart M X hX)

def leftSourceCover (LA : SourceCartesianAtlas left fullI)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :
    SourceCartesianCover (p.leftData.directSource (p.leftDivisorCoefficient S χ)).columns
      (p.leftData.directSource (p.leftDivisorCoefficient S χ)).ideal :=
  p.leftData.sourceCartesianCover LA (primeSupport DE.1) DE.1
    p.left_columns (fun i => by rw [p.left_ideal]; exact b.left_residual i)
    (p.leftDivisorCoefficient S χ)

def rightSourceCover (RA : SourceCartesianAtlas right fullJ)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :
    SourceCartesianCover (p.rightData.directSource (p.rightDivisorCoefficient S χ)).columns
      (p.rightData.directSource (p.rightDivisorCoefficient S χ)).ideal :=
  p.rightData.sourceCartesianCover RA (primeSupport DE.1) DE.2
    p.right_columns (fun j => by rw [p.right_ideal]; exact b.right_residual j)
    (p.rightDivisorCoefficient S χ)

namespace SecondStages

variable {p}

structure TerminalCalibration (s : p.SecondStages (E := E) (hDiff := hDiff))
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ) (Z Lmax Nsave decay : ℝ) where
  left : ∀ S χ, (s.left S χ).TerminalCalibration sTail sZero k Z Lmax Nsave decay
  right : ∀ S χ, (s.right S χ).TerminalCalibration sTail sZero k Z Lmax Nsave decay

structure CoverHybridPredicates (s : p.SecondStages (E := E) (hDiff := hDiff))
    (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ) where
  left : ∀ S χ, (s.left S χ).CoverHybridPredicates
    (p.leftSourceCover LA S χ) (p.leftSourceCover LA S χ)
  right : ∀ S χ, (s.right S χ).CoverHybridPredicates
    (p.rightSourceCover RA S χ) (p.rightSourceCover RA S χ)

end SecondStages
end FirstBlockDirectData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.leftSourceCover
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.rightSourceCover
