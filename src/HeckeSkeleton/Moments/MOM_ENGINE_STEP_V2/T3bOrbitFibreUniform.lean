module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bOriginalGeometry

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! # A fixed constant for the actual second physical orbit fibre -/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace T3b

/-- Both the retained-scale boundary and the original direct padding
are paid here, before the main source is amplified. -/
def firstRowExponentBound (c : TargetContext K) (p : SourceParameters c) : ℝ :=
  4 + recipeInductionSigma c / 8 + 4 * p.loss + recipeInductionSigma c

theorem firstRowExponentBound_nonneg : 0 ≤ firstRowExponentBound c p := by
  have hs := (recipeInduction_budget (c := c)).1
  have hp := p.loss_pos
  unfold firstRowExponentBound
  positivity

def physicalOrbitFibreConstant (c : TargetContext K) (p : SourceParameters c) : ℝ :=
  max 1 ((firstRowExponentBound c p + 6 * (recipeInductionSigma c / 3)) /
    ((recipeInductionSigma c / 3) / 2))

theorem physicalOrbitFibreConstant_one_le : 1 ≤ physicalOrbitFibreConstant c p :=
  le_max_left _ _

theorem physicalOrbitFibreConstant_nonneg : 0 ≤ physicalOrbitFibreConstant c p :=
  zero_le_one.trans physicalOrbitFibreConstant_one_le

end T3b

namespace FirstCauchyFamily

variable {F : FirstPresentation call p} (family : FirstCauchyFamily F)

theorem t3b_row_norm_uniform (hF : F.Realizes) (hfamily : family.Realizes)
    (hwindows : ∀ i, (family.source i).Windows) (i : Fin family.count)
    (h : (Arithmetic.data c).R) (hh : h ∈ (family.source i).source.rows) :
    (Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h) ≤
      call.base ^ T3b.firstRowExponentBound c p := by
  let source := family.source i
  have hretained : source.first.retainedScale ≤
      call.base ^ (source.firstFrequency + 4 * p.loss) :=
    (hwindows i).retained_upper ⟨h, hh⟩
  have hn := (hwindows i).row_upper h hh
  rw [hfamily.tag i] at hn
  change (Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h) ≤
    source.first.retainedScale * call.base ^ recipeInductionSigma c at hn
  calc
    _ ≤ source.first.retainedScale * call.base ^ recipeInductionSigma c := hn
    _ ≤ call.base ^ (source.firstFrequency + 4 * p.loss) *
        call.base ^ recipeInductionSigma c :=
      mul_le_mul_of_nonneg_right hretained (Real.rpow_nonneg call.base_pos.le _)
    _ ≤ _ := by
      rw [← Real.rpow_add call.base_pos]
      apply Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
      have hf := family.t3b_firstFrequency_le hF hfamily i
      unfold T3b.firstRowExponentBound
      change source.firstFrequency + 4 * p.loss + recipeInductionSigma c ≤ _
      linarith

/-- The literal finite supremum used to define the pool's row exponent
is bounded using those very rows; an empty source contributes norm one. -/
theorem t3b_rowSize_le (hF : F.Realizes) (hfamily : family.Realizes)
    (hwindows : ∀ i, (family.source i).Windows) (i : Fin family.count) :
    (family.source i).rowSize ≤ call.base ^ T3b.firstRowExponentBound c p := by
  let B : NNReal := ⟨call.base ^ T3b.firstRowExponentBound c p,
    Real.rpow_nonneg call.base_pos.le _⟩
  have hsup : (family.source i).source.rows.sup
      (fun h => (⟨(Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h),
        ((Arithmetic.data c).exteriorNorm_pos (originalFrequencyIdeal h)).le⟩ : NNReal)) ≤ B := by
    apply Finset.sup_le
    intro h hh
    exact family.t3b_row_norm_uniform hF hfamily hwindows i h hh
  exact max_le
    (Real.one_le_rpow call.domain.scale.le T3b.firstRowExponentBound_nonneg) hsup

theorem t3b_rowExponent_le (hF : F.Realizes) (hfamily : family.Realizes)
    (hwindows : ∀ i, (family.source i).Windows) (i : Fin family.count) :
    (family.source i).rowExponent ≤ T3b.firstRowExponentBound c p := by
  have hsize : 0 < (family.source i).rowSize :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hl := Real.log_le_log hsize (family.t3b_rowSize_le hF hfamily hwindows i)
  rw [Real.log_rpow call.base_pos] at hl
  unfold PhysicalSource.rowExponent
  apply (div_le_iff₀ (Real.log_pos call.domain.scale)).mpr
  nlinarith

end FirstCauchyFamily

namespace PoolExpansion

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

/-- The pool's lower norm scale is positive and fixed before the
source labels. Its multiplicity therefore contributes a fixed constant. -/
theorem t3bOrbitFibreAllowance_le_constant (expansion : PoolExpansion family)
    (hF : F.Realizes) (hfamily : family.Realizes)
    (hwindows : ∀ i, (family.source i).Windows) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count) :
    expansion.t3bOrbitFibreAllowance i ≤ T3b.physicalOrbitFibreConstant c p := by
  cases expansion with
  | direct => exact T3b.physicalOrbitFibreConstant_one_le
  | pooled P count index source =>
    dsimp only [t3bOrbitFibreAllowance]
    cases (index i).2 with
    | inl u =>
      have hr := family.t3b_rowExponent_le hF hfamily hwindows (index i).1
      rw [← hexpansion.2.1.rowExponent (index i).1] at hr
      have hs : 0 ≤ (recipeInductionSigma c / 3) / 2 := by
        have hσ := (recipeInduction_budget (c := c)).1
        positivity
      calc
        (P.data (index i).1).multiplicity ≤
            (T3b.firstRowExponentBound c p + 6 * (recipeInductionSigma c / 3)) /
              ((recipeInductionSigma c / 3) / 2) :=
          div_le_div_of_nonneg_right (by linarith only [hr]) hs
        _ ≤ _ := le_max_right _ _
    | inr qe => exact T3b.physicalOrbitFibreConstant_one_le

end PoolExpansion

namespace RawFamily

/-- The original second stage's physical fibre is uniformly bounded
from its own source-chain realization, with no additional premise. -/
theorem t3b_secondFiber_uniform (trace : SourceTrace call p) (htrace : trace.Realizes)
    {geometry : GeometryFamily trace.second} (raw : RawFamily geometry) (j : Fin raw.count) :
    ((raw.packet j).second.stage.fiber : ℝ) ≤ T3b.physicalOrbitFibreConstant c p :=
  (raw.t3b_secondFiber_le trace htrace j).trans
    (trace.expansion.t3bOrbitFibreAllowance_le_constant htrace.first htrace.cauchy
      htrace.firstWindows htrace.expansion (raw.sourceIndex j))

end RawFamily

namespace RawLeafPacket

theorem t3b_secondFiber_uniform (packet : RawLeafPacket call p) (hpacket : packet.Realizes) :
    (packet.second.stage.fiber : ℝ) ≤ T3b.physicalOrbitFibreConstant c p := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  exact raw.t3b_secondFiber_uniform trace htrace j

end RawLeafPacket

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_secondFiber_uniform
