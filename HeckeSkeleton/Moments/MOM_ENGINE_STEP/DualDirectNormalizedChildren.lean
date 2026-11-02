import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualDirectCoveredStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualTerminalPower
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectNormalizedChildren

set_option linter.unusedSectionVars false

/-!
# The signed direct parent reaches the same normalized children

The actual direct parent and both pure-dual terminal calibrations are
connected to the existing live leaf family. The original constant-atom
extraction, capacity choices, four rectangles, kernels, and continuous
Fourier variables are unchanged. The common normalized-family producer
supplies the actual energy comparison and integrability internally.

Both first terminal scalars below are computed from the same generic
`FirstDualOriginalWindows`; their normalized estimates are immediate
specializations of its proved original-window bounds. The second
budgets are the existing direct budgets, and all their signs are proved.
No prime pool, vanishing profile, or whole-child inequality is assumed.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

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
local instance dualDirectNormalizedChildrenCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}

namespace FirstBlockDirectData.SecondStages.DualTerminalCalibration

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockDirectData chart M X hX}
variable {s : p.SecondStages (E := E) (hDiff := hDiff)}
variable (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
variable (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
  ((PUnit × PUnit) →* Circle) → ℝ)
variable (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)

include hNL hNR

theorem zeroBudget_nonneg (ε Czero : ℝ) (hC : 0 ≤ Czero) :
    0 ≤ T.zeroBudget NL NR ε Czero := by
  sorry

theorem tailBudget_nonneg (Cerror : ℝ) (hC : 0 ≤ Cerror) :
    0 ≤ T.tailBudget NL NR Cerror := by
  sorry

end FirstBlockDirectData.SecondStages.DualTerminalCalibration

namespace ActualDirectFirstSource

variable {omega psi : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K omega psi} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable (s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX)
variable {sFirst sFirstZero : Finset (ℕ × ℕ)} {normBound : ℝ}
variable (F : FirstDualOriginalWindows (hΓ := hΓ) C s.columns s.ideal s.block s.profiles
  s.radius s.mask sFirst sFirstZero k Z X normBound Lmax Nsave decay)

def dualFirstZeroBudget (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ)
    (ε CfirstZero : ℝ) : ℝ :=
  (s.fiber : ℝ) * CfirstZero * F.zeroAmplitude hB δ hδ * Z ^ (F.zeroProductExponent * ε)

def dualFirstTailBudget (CfirstError : ℝ) : ℝ :=
  (s.fiber : ℝ) * CfirstError * F.tailProfileConstant * Z ^ (-Nsave)

theorem dualFirstCost_eq_budgets (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ)
    (ε CfirstError CfirstZero : ℝ) :
    (s.fiber : ℝ) * F.cost hB δ hδ ε CfirstError CfirstZero =
      s.dualFirstZeroBudget F hB δ hδ ε CfirstZero + s.dualFirstTailBudget F CfirstError := by
  sorry

theorem dualFirstZeroBudget_nonneg (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ)
    (ε CfirstZero : ℝ) (hC : 0 ≤ CfirstZero) :
    0 ≤ s.dualFirstZeroBudget F hB δ hδ ε CfirstZero := by
  sorry

theorem dualFirstTailBudget_nonneg (CfirstError : ℝ) (hC : 0 ≤ CfirstError) :
    0 ≤ s.dualFirstTailBudget F CfirstError := by
  sorry

/-- The exact same first-window zero estimate, with the original
parent width and parent fibre. -/
theorem normalizedFirstDualZero_of_original_le
    (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ)
    (ε CfirstZero terminalExponent : ℝ) (hC : 0 ≤ CfirstZero)
    (hledger : F.zeroExponent δ + F.zeroProductExponent * ε - (a.m + a.q) ≤ terminalExponent) :
    s.dualFirstZeroBudget F hB δ hδ ε CfirstZero / Z ^ (a.m + a.q) ≤
      (s.fiber : ℝ) * CfirstZero * originalFirstMaskConstant (K := K) normBound δ hB hδ *
        F.zeroProfileConstant * Z ^ terminalExponent := by
  sorry

theorem normalizedFirstDualTail_of_original_le
    (CfirstError terminalExponent : ℝ) (hC : 0 ≤ CfirstError)
    (hledger : -Nsave - (a.m + a.q) ≤ terminalExponent) :
    s.dualFirstTailBudget F CfirstError / Z ^ (a.m + a.q) ≤
      (s.fiber : ℝ) * CfirstError * F.tailProfileConstant * Z ^ terminalExponent := by
  sorry

namespace SecondStages

variable {s} (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay) (N₀ : s.Normalization)

theorem dualSecondZeroBudget_nonneg (ε Czero : ℝ) (hC : 0 ≤ Czero) :
    0 ≤ R.dualSecondZeroBudget T N₀ ε Czero := by
  sorry

theorem dualSecondTailBudget_nonneg (Cerror : ℝ) (hC : 0 ≤ Cerror) :
    0 ≤ R.dualSecondTailBudget T N₀ Cerror := by
  sorry

theorem exceptionalBudget_nonneg (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) :
    0 ≤ R.exceptionalBudget L exceptional N₀ := by
  sorry

theorem ordinaryBudget_nonneg (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) :
    0 ≤ R.ordinaryBudget L exceptional N₀ := by
  sorry

end SecondStages
end ActualDirectFirstSource

variable (hΓ μv hDiff)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
variable [MeasurableSpace (WithLp 2 (W × E))] [BorelSpace (WithLp 2 (W × E))]

include ν μ in
/-- The literal signed parent uses the original direct live family and
the common capacity/normalization producer. The two actual Fourier
kernels and zero child twists are retained. Only original individual
atom, profile and capacity dictionaries are supplied. -/
theorem actual_parent_direct_dual_normalized_child_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (rowBallSize normBound : ℝ) (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ)
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
    ∀ s : ActualDirectFirstSource (E := W) hΓ μv C Z
      (rowBallFiniteFamily K A.Sf rowBallSize) centered d a t Y₁ Y₂ X hX,
    ∀ coefficient : s.Column → ℂ,
      (∀ i j, s.profiles i j = (coefficient i * star (coefficient j)) •
        CanonicalRowBall.archTest K A.Sf rowBallSize) →
    ∀ N₀ : s.Normalization, ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ conditions : R.DualSourceConditions,
    ∀ T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay,
    ∀ F : FirstDualOriginalWindows (hΓ := hΓ) C s.columns s.ideal s.block s.profiles
      s.radius s.mask sFirst sFirstZero k Z X normBound Lmax Nsave decay,
    ∀ (L : SourceCartesianAtlas s.columns s.ideal) (exceptional : R.CoverHybridPredicates L),
    ∀ {Ray : Type} [CommGroup Ray] [Fintype Ray],
    ∀ (I : R.liveLeaves L exceptional N₀ → Type)
      [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)],
    ∀ (rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)) (heightDomain window : Set ℝ)
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
        s.dualFirstZeroBudget F hB δ hδ ε CfirstZero / Z ^ (a.m + a.q) +
          R.dualSecondZeroBudget T N₀ ε Czero / Z ^ (a.m + a.q) +
          R.exceptionalBudget L exceptional N₀ / Z ^ (a.m + a.q) +
          (s.dualFirstTailBudget F CfirstError + R.dualSecondTailBudget T N₀ Cerror) /
            Z ^ (a.m + a.q) +
          ∑ b : family.active Finset.univ, ∫ ξ,
            Real.sqrt (normalizedPairedEnergy (family.leftData Finset.univ b ξ)
              (family.leftParameters Finset.univ b) Z 0) *
            Real.sqrt (normalizedPairedEnergy (family.rightData Finset.univ b ξ)
              (family.rightParameters Finset.univ b) Z 0) ∂kernels b := by
  sorry

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.normalizedFirstDualZero_of_original_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.dualSecondZeroBudget_nonneg
#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_direct_dual_normalized_child_bound
