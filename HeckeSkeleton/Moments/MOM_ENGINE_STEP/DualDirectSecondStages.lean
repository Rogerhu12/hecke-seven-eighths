import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectParentLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectFirstDualTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualGaussHybridTerminal

set_option linter.unusedSectionVars false

/-!
# Both signed transforms on the actual direct source

Each second stage remains attached to its original first divisor and
finite phase. The first Fourier measure, the negative right location,
and both original positive normalizers are unchanged. The only signed
origin conditions concern the additional row mask and the individual
tensor at zero; no profile is required to vanish there.

The final theorem pays both pure-dual zeros and both physical tails,
then retains the actual finite second-row sums. All analytic choices
precede the moving source. This entrance has no prime-pool parameter.
-/

noncomputable section
open UniqueFactorizationMonoid
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
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

local instance dualDirectSecondStagesCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ}

namespace FirstBlockDirectData

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockDirectData chart M X hX}

namespace SecondStages

/-- Original additional masks and tensor values of the two actual
stages. Canonical unmasked row-ball stages supply these identities
without imposing a sign on any finite row sum. -/
structure DualSourceConditions (s : p.SecondStages (E := E) (hDiff := hDiff)) : Prop where
  left_mask : ∀ S χ, (s.left S χ).mask = ∅
  right_mask : ∀ S χ, (s.right S χ).mask = ∅
  left_origin_nonneg : ∀ S χ,
    0 ≤ (sIntegerTensorTerm K A.Sf
      (traceSchwartzToMixed K (s.left S χ).profile) finiteTest 0).re
  right_origin_nonneg : ∀ S χ,
    0 ≤ (sIntegerTensorTerm K A.Sf
      (traceSchwartzToMixed K (s.right S χ).profile) finiteTest 0).re

/-- Pure-dual terminal windows on the literal original direct stages.
In particular there is no vanishing-profile field. -/
structure DualTerminalCalibration (s : p.SecondStages (E := E) (hDiff := hDiff))
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ) (Z Lmax Nsave decay : ℝ) where
  left : ∀ S χ, (s.left S χ).DualTerminalCalibration sTail sZero k Z Lmax Nsave decay
  right : ∀ S χ, (s.right S χ).DualTerminalCalibration sTail sZero k Z Lmax Nsave decay

namespace DualTerminalCalibration

variable {s : p.SecondStages (E := E) (hDiff := hDiff)}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

/-- Both original first Fourier integrals, with the original finite
divisor/phase weights and the unchanged right frequency sign. -/
def rawCost (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ) (ε Cerror Czero : ℝ) : ℝ :=
  ∑ S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val), ‖(moebius S.val : ℂ)‖ *
    ∑ χ : (PUnit × PUnit) →* Circle, ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖ *
      (p.rowBound * Real.sqrt (NL S χ) * Real.sqrt (NR S χ) / 2) *
      ((∫ ξ, ((T.left S χ).fourierPhase chart.leftPoint ξ).rawCost ε Cerror Czero / NL S χ
          ∂actualFourierMeasure chart.kernel) +
        ∫ ξ, ((T.right S χ).fourierPhase (fun j => -chart.rightPoint j) ξ).rawCost
            ε Cerror Czero / NR S χ ∂actualFourierMeasure chart.kernel)

/-- The universal second-stage estimate is substituted on the same
finite labels. The final source theorem below proves that estimate;
it is not a source-calibration hypothesis. -/
theorem linearized_le_rawCost
    (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (conditions : s.DualSourceConditions)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)
    (ε Cerror Czero : ℝ)
    (hstageLeft : ∀ (G : ActualGaussSource C ι)
      (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
      (hmask : s.mask = ∅)
      (hpositive : 0 ≤ (sIntegerTensorTerm K A.Sf
        (traceSchwartzToMixed K s.profile) finiteTest 0).re)
      (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
      (x : ι → W) (ξ : W),
      G.phaseEnergy (hDiff := hDiff) x ξ ≤ (T.fourierPhase x ξ).rawCost ε Cerror Czero)
    (hstageRight : ∀ (G : ActualGaussSource C κ)
      (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
      (hmask : s.mask = ∅)
      (hpositive : 0 ≤ (sIntegerTensorTerm K A.Sf
        (traceSchwartzToMixed K s.profile) finiteTest 0).re)
      (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
      (x : κ → W) (ξ : W),
      G.phaseEnergy (hDiff := hDiff) x ξ ≤ (T.fourierPhase x ξ).rawCost ε Cerror Czero) :
    p.linearizedCost hDiff NL NR ≤ T.rawCost NL NR ε Cerror Czero := by
  sorry

end DualTerminalCalibration
end SecondStages
end FirstBlockDirectData

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}

namespace ActualDirectFirstSource.SecondStages

variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}
variable (R : s.SecondStages (E := E) (hDiff := hDiff))

abbrev DualSourceConditions : Prop :=
  ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    (R v D).DualSourceConditions

abbrev DualTerminalCalibration (sTail sZero : Finset (ℕ × ℕ))
    (k : ℕ) (Lmax Nsave decay : ℝ) :=
  ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    (R v D).DualTerminalCalibration sTail sZero k Z Lmax Nsave decay

variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def dualRawCost (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (N : s.Normalization) (ε Cerror Czero : ℝ) : ℝ :=
  ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    (T v D).rawCost (N.left v D) (N.right v D) ε Cerror Czero

end ActualDirectFirstSource.SecondStages

variable (hΓ μv hDiff)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- The same pure-dual second transform applies to an unamplified
source under its original first Fourier phase. -/
theorem actual_direct_dual_raw_fourier_stage_bound
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
    ∃ sTail sZero : Finset (ℕ × ℕ), ∃ Cerror Czero : ℝ, 0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (Z : ℝ) {ι : Type*} (G : ActualGaussSource C ι)
      (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
      (hmask : s.mask = ∅)
      (hpositive : 0 ≤ (sIntegerTensorTerm K A.Sf
        (traceSchwartzToMixed K s.profile) finiteTest 0).re)
      (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
      (x : ι → W) (ξ : W),
      G.phaseEnergy (hDiff := hDiff) x ξ ≤ (T.fourierPhase x ξ).rawCost ε Cerror Czero := by
  sorry

include ν μ in
/-- The original direct parent reaches its literal finite second rows.
The two first terminals come from the original factor/profile/mask
windows, and both second terminals come from the actual second stages.
There is no slot-count restriction and no prime pool. -/
theorem actual_parent_direct_two_stage_dual_raw_terminal_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (rowBallSize normBound : ℝ) (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (Lmax Nsave ξmax : ℝ) (hξmax : 0 < ξmax) :
    ∃ (decay : ℝ) (hdecay : 1 < decay),
      decay = tailDecayForWidth Lmax Nsave ξmax ∧
      firstTailCutoffExponent Lmax Nsave decay ≤ ξmax ∧
    ∃ sFirst sFirstZero sTail sZero : Finset (ℕ × ℕ),
    ∃ CfirstError CfirstZero Cerror Czero : ℝ,
      0 ≤ CfirstError ∧ 0 < CfirstZero ∧ 0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (Z : ℝ), ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualDirectFirstSource (E := W) hΓ μv C Z
      (rowBallFiniteFamily K A.Sf rowBallSize) centered d a t Y₁ Y₂ X hX,
    ∀ coefficient : s.Column → ℂ,
      (∀ i j, s.profiles i j = (coefficient i * star (coefficient j)) •
        CanonicalRowBall.archTest K A.Sf rowBallSize) →
    ∀ N : s.Normalization,
    ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ conditions : R.DualSourceConditions,
    ∀ T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay,
    ∀ F : FirstDualOriginalWindows (hΓ := hΓ) C s.columns s.ideal s.block s.profiles
      s.radius s.mask sFirst sFirstZero k Z X normBound Lmax Nsave decay,
      X ≤ Z ^ ξmax ∧
      pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
        (s.fiber : ℝ) * (F.cost hB δ hδ ε CfirstError CfirstZero +
          R.dualRawCost T N ε Cerror Czero) := by
  sorry

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.SecondStages.DualTerminalCalibration.linearized_le_rawCost
#print axioms HeckeSkeleton.Moments.EngineStep.actual_direct_dual_raw_fourier_stage_bound
#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_direct_two_stage_dual_raw_terminal_bound
