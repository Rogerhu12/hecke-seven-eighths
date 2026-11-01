import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualDirectCoveredStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectNormalizedChildren
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualFirstSourceFiniteLeaves

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
  have hlinear : s.linearizedCost hDiff N ≤ R.dualRawCost T N ε Cerror Czero := by
    unfold ActualDirectFirstSource.linearizedCost dualRawCost
    apply Finset.sum_le_sum
    intro v _
    apply Finset.sum_le_sum
    intro D _
    exact (T v D).linearized_le_rawCost (conditions v D)
      (N.left v D) (N.right v D) (N.left_pos v D) (N.right_pos v D)
      ε Cerror Czero hstage
  have hraw := mul_le_mul_of_nonneg_left
    ((s.rawRowCost_le_linearized hDiff N).trans
      (hlinear.trans (R.dualRawCost_le_finiteCost T L exceptional N ε Cerror Czero)))
    (Nat.cast_nonneg s.fiber : (0 : ℝ) ≤ (s.fiber : ℝ))
  rw [R.dualFiniteCost_eq_budgets_leaves T L exceptional N ε Cerror Czero,
    R.cost_eq_live_components L exceptional N] at hraw
  simpa only [add_assoc] using hraw

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
  have hlinear : s.linearizedCost N ≤ R.dualRawCost T N ε Cerror Czero := by
    unfold ActualFirstSource.linearizedCost dualRawCost
    apply Finset.sum_le_sum
    intro v _
    apply Finset.sum_le_sum
    intro D _
    exact (T v D).linearized_le_rawCost (conditions v D)
      (N.left v D) (N.right v D) (N.left_pos v D) (N.right_pos v D)
      ε Cerror Czero hstage hstage
  have hleaves :
      (s.fiber : ℝ) * (∑ j : R.CoveredLeafKey L, (R.coveredLeaf L exceptional N j).cost) =
        R.exceptionalBudget L exceptional N + R.ordinaryBudget L exceptional N := by
    calc
      _ = ∑ j : R.CoveredLeafKey L, (R.parentLeaf L exceptional N j).cost := by
        simp only [parentLeaf, ActualHybridLeaf.scale_cost, Finset.mul_sum]
      _ = ∑ j : R.liveLeaves L exceptional N,
          (R.parentLeaf L exceptional N j.val).cost :=
        ActualHybridFamily.sum_cost_eq_live _
      _ = _ := by
        simp only [exceptionalBudget, ordinaryBudget, ActualHybridLeaf.cost,
          Finset.sum_add_distrib]
  have hraw := mul_le_mul_of_nonneg_left
    ((s.rawRowCost_le_linearized hDiff N).trans
      (hlinear.trans (R.dualRawCost_le_covered T L exceptional N ε Cerror Czero)))
    (Nat.cast_nonneg s.fiber : (0 : ℝ) ≤ (s.fiber : ℝ))
  rw [R.dualCoveredCost_eq_budgets_leaves T L exceptional N ε Cerror Czero] at hraw
  simpa only [dualSecondZeroBudget, dualSecondTailBudget, mul_add, hleaves,
    add_assoc] using hraw

end ActualFirstSource.SecondStages
end Pooled
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.rawRowCost_le_dual_live
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.rawRowCost_le_dual_live
