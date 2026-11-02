import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawTerminals
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.DirectParent
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PooledParent

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! # The two literal terminal pairs on the complete first source -/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup

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
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}
variable {d : FirstGaussPoolData C P ι} {c : ι → ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}


namespace ActualPoolStages

variable (s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest)

def rawTerminals (F : SchwartzMap W ℂ) (x : ι → W) : RawTerminalPair :=
  (4 / d.density) •
    (d.multiplicity • ActualGaussStage.rawTerminals s.main F x +
      (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 1 •
        ActualGaussStage.rawTerminals (s.one p) F (fun i => x i.val)) +
      (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 6 •
        ActualGaussStage.rawTerminals (s.six p) F (fun i => x i.val)) +
      (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 7 •
        ActualGaussStage.rawTerminals (s.seven p) F (fun i => x i.val)))

end ActualPoolStages

section FirstBlocks

variable {κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}

local instance terminalCircleCharacterFintype :
    Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

namespace FirstBlockDirectData.SecondStages

variable {p : FirstBlockDirectData chart M X hX}
variable (s : FirstBlockDirectData.SecondStages p (E := E) (hDiff := hDiff))

def rawTerminals
    (NL NR : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val) →
      ((PUnit × PUnit) →* Circle) → ℝ) : RawTerminalPair :=
  ∑ S, ∑ χ, classWeight NL NR S χ •
    ((NL S χ)⁻¹ • ActualGaussStage.rawTerminals (s.left S χ) chart.kernel chart.leftPoint +
      (NR S χ)⁻¹ • ActualGaussStage.rawTerminals (s.right S χ) chart.kernel (fun j => -chart.rightPoint j))

end FirstBlockDirectData.SecondStages

namespace FirstBlockPoolData.SecondStages

variable {p : FirstBlockPoolData chart P M X hX}
variable (s : p.SecondStages (E := E) (hDiff := hDiff))

def rawTerminals
    (NL NR : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val) →
      ((PUnit × PUnit) →* Circle) → ℝ) : RawTerminalPair :=
  ∑ S, ∑ χ, classWeight NL NR S χ •
    ((NL S χ)⁻¹ • ActualPoolStages.rawTerminals (s.left S χ) chart.kernel chart.leftPoint +
      (NR S χ)⁻¹ • ActualPoolStages.rawTerminals (s.right S χ) chart.kernel (fun j => -chart.rightPoint j))

end FirstBlockPoolData.SecondStages
end FirstBlocks

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {parent : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}

namespace ActualDirectFirstSource

variable (s : ActualDirectFirstSource (E := W) hΓ μv C Z
  finiteTest centered parent a t Y₁ Y₂ X hX)

def firstRawTerminals : RawTerminalPair :=
  ((s.fiber : ℝ) * s.zeroCost hDiff,
    (s.fiber : ℝ) * ∑ v : s.CommonLabel,
      ‖(∑ i ∈ (s.source v).leftColumns, ∑ j ∈ (s.source v).rightColumns,
        ((s.source v).pairs i j).maskedSeries
          (sIntegerFiniteTestFunction K A.Sf finiteTest) s.radius s.mask) -
        (s.source v).transform μv hDiff finiteTest‖)

namespace SecondStages

variable {s} (R : ActualDirectFirstSource.SecondStages s (E := E) (hDiff := hDiff))

def secondRawTerminals (N : s.Normalization) : RawTerminalPair :=
  (s.fiber : ℝ) • ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    FirstBlockDirectData.SecondStages.rawTerminals (R v D) (N.left v D) (N.right v D)

end SecondStages
end ActualDirectFirstSource

namespace ActualFirstSource

variable (s : ActualFirstSource (E := W) hΓ μv C P
  finiteTest centered parent a t Y₁ Y₂ X hX)

def firstRawTerminals : RawTerminalPair :=
  ((s.fiber : ℝ) * s.zeroCost hDiff,
    (s.fiber : ℝ) * ∑ v : s.CommonLabel,
      ‖(∑ i ∈ (s.source v).leftColumns, ∑ j ∈ (s.source v).rightColumns,
        ((s.source v).pairs i j).maskedSeries
          (sIntegerFiniteTestFunction K A.Sf finiteTest) s.radius s.mask) -
        (s.source v).transform μv hDiff finiteTest‖)

namespace SecondStages

variable {s} (R : s.SecondStages (E := E) (hDiff := hDiff))

def secondRawTerminals (N : s.Normalization) : RawTerminalPair :=
  (s.fiber : ℝ) • ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    FirstBlockPoolData.SecondStages.rawTerminals (R v D) (N.left v D) (N.right v D)

end SecondStages
end ActualFirstSource
end HeckeSkeleton.Moments.EngineStepV2

