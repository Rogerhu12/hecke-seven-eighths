import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S2FirstFamilyData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Exact cost of the original first-Cauchy family

The two Cauchy halves use their original positive denominators. The
physical divisor and the mutual coprimality divisor remain separate
coordinates, and the outer source multiplicity is paid exactly once.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.MobiusRegroup
open UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

local instance s2CostCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem source_cost_two_sides (F : FirstPresentation call p)
    (N : F.source.Normalization) (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset)
    (S : divisorPool (F.source.pieces v D).rightData.columns
      (fun i => ((F.source.pieces v D).rightData.ideal i).val))
    (chi : (PUnit.{1} × PUnit.{1}) →* Circle) :
    (∑ side : Bool, (source ⟨v, D, S, chi, side⟩ N).cost) =
      (F.source.fiber : ℝ) * ‖(moebius S.val : ℂ)‖ *
        ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) chi‖ *
        ((F.source.pieces v D).rowBound * Real.sqrt (N.left v D S chi) *
          Real.sqrt (N.right v D S chi) / 2) *
        ((∫ x, ((F.source.pieces v D).leftData.directSource
            (FirstGaussPoolData.twistedCoefficient
              (fun i => if S.val ∣ ((F.source.pieces v D).leftData.ideal i).val then
                (F.source.pieces v D).originalLeftCoefficient i *
                  (fixedLeftPhase PUnit chi PUnit.unit : ℂ) else 0)
              (F.source.charts v D).leftPoint x)).energy (Arithmetic.different c) /
                N.left v D S chi ∂actualFourierMeasure (F.source.charts v D).kernel) +
          ∫ x, ((F.source.pieces v D).rightData.directSource
            (FirstGaussPoolData.twistedCoefficient
              (fun i => if S.val ∣ ((F.source.pieces v D).rightData.ideal i).val then
                (F.source.pieces v D).originalRightCoefficient i *
                  (fixedRightPhase PUnit chi PUnit.unit : ℂ) else 0)
              (fun i => -(F.source.charts v D).rightPoint i) x)).energy
                (Arithmetic.different c) / N.right v D S chi
                  ∂actualFourierMeasure (F.source.charts v D).kernel) := by
  simp only [Fintype.sum_bool, source, PhysicalSource.cost,
    FirstCauchyKey.outer, FirstCauchyKey.data, FirstCauchyKey.coefficient,
    FirstCauchyKey.point, FirstCauchyKey.phase, FirstCauchyKey.side,
    FirstCauchyKey.piece, FirstCauchyKey.chart, FirstCauchyKey.residual,
    FirstCauchyKey.character, Bool.false_eq_true, if_false, if_true,
    DirectGaussData.directSource_phaseEnergy, integral_div]
  ring

theorem sum_source_cost (F : FirstPresentation call p) (N : F.source.Normalization) :
    (∑ key : FirstCauchyKey F, (source key N).cost) =
      (F.source.fiber : ℝ) * F.source.linearizedCost (Arithmetic.different c) N := by
  rw [Fintype.sum_sigma]
  unfold ActualDirectFirstSource.linearizedCost
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  rw [Fintype.sum_prod_type]
  unfold FirstBlockDirectData.linearizedCost firstDirectLinearizedCost
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro chi _
  rw [source_cost_two_sides]
  ring

theorem family_cost (F : FirstPresentation call p) :
    (F.source.fiber : ℝ) * F.source.linearizedCost
      (Arithmetic.different c) (family F).normalization = (family F).cost := by
  change (F.source.fiber : ℝ) * F.source.linearizedCost
    (Arithmetic.different c) (normalization F) =
      ∑ i : Fin (Fintype.card (FirstCauchyKey F)),
        (source ((Fintype.equivFin (FirstCauchyKey F)).symm i) (normalization F)).cost
  calc
    _ = ∑ key : FirstCauchyKey F, (source key (normalization F)).cost :=
      (sum_source_cost F (normalization F)).symm
    _ = _ :=
      (Fintype.sum_equiv (Fintype.equivFin (FirstCauchyKey F)).symm _ _
        (fun _ => rfl)).symm

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2.family_cost
