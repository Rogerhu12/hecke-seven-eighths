import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualDirectCoveredStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectNormalizedChildren
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualFirstSourceFiniteLeaves

set_option linter.unusedSectionVars false

/-!
# The original finite rows reach the same live parent leaves

These internal substitution lemmas use the universal second-transform
theorem on its original stages.  The first fibre is paid once, and the
result contains the literal zero and tail budgets together with the
exceptional and ordinary costs of the original live parent leaves.
The primitive specializations construct the stage conditions and then
replace the ordinary cost by the kernels of their existing family.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
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
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {Z t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

local instance literalParentCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace ActualDirectFirstSource.SecondStages

variable {s : ActualDirectFirstSource (E := ℝ) hΓ μv C Z finiteTest
  centered d a t Y₁ Y₂ X hX}
variable (R : s.SecondStages (E := ℝ) (hDiff := hDiff))

/-- The universal stage theorem is evaluated on every actual first
divisor and phase before the original finite cover is flattened. -/
theorem rawRowCost_le_dual_live
    (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (conditions : R.DualSourceConditions)
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (ε Cerror Czero : ℝ)
    (hstage : ∀ {j : Type*} (G : ActualGaussSource C j)
      (stage : ActualGaussStage (E := ℝ) hΓ μv hDiff G finiteTest)
      (hmask : stage.mask = ∅)
      (hpositive : 0 ≤ (sIntegerTensorTerm K A.Sf
        (traceSchwartzToMixed K stage.profile) finiteTest 0).re)
      (cal : stage.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
      (x : j → ℝ) (ξ : ℝ),
      G.phaseEnergy (hDiff := hDiff) x ξ ≤
        (cal.fourierPhase x ξ).rawCost ε Cerror Czero) :
    (s.fiber : ℝ) * s.rawRowCost hDiff ≤
      R.dualSecondZeroBudget T N ε Czero + R.dualSecondTailBudget T N Cerror +
        R.exceptionalBudget L exceptional N + R.ordinaryBudget L exceptional N := by
  sorry

end ActualDirectFirstSource.SecondStages

section Pooled

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {ell eps : ℝ}
variable {pool : PowerScaleExteriorPool A bad Z ell eps}
variable {s : ActualFirstSource (E := ℝ) hΓ μv C pool finiteTest
  centered d a t Y₁ Y₂ X hX}

namespace ActualFirstSource.SecondStages

variable (R : s.SecondStages (E := ℝ) (hDiff := hDiff))

/-- Both original prime-pool orientations and all four pool tags are
kept by the original covered-cost identity. -/
theorem rawRowCost_le_dual_live
    (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (conditions : R.DualSourceConditions)
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (ε Cerror Czero : ℝ)
    (hstage : ∀ {j : Type*} (p : FirstGaussPoolData C pool j)
      (c : j → ℂ) (x : j → ℝ)
      (stage : ActualPoolStages (E := ℝ) hΓ μv hDiff p c finiteTest)
      (hs : stage.DualSourceConditions)
      (cal : stage.DualTerminalCalibration sTail sZero k Lmax Nsave decay) (ξ : ℝ),
      p.energy (FirstGaussPoolData.twistedCoefficient c x ξ) ≤
        cal.rawPhaseCost x ξ ε Cerror Czero) :
    (s.fiber : ℝ) * s.rawRowCost hDiff ≤
      R.dualSecondZeroBudget T N ε Czero + R.dualSecondTailBudget T N Cerror +
        R.exceptionalBudget L exceptional N + R.ordinaryBudget L exceptional N := by
  sorry

end ActualFirstSource.SecondStages
end Pooled
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.rawRowCost_le_dual_live
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.rawRowCost_le_dual_live
