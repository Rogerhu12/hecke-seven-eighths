import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3aRealization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.WeightedNestedFourierMeasure

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The two original exceptional kernels are the same fixed kernel

Both Poisson charts are built from the original row-ball test and the
same fixed Mellin tilt.  Their kernel is independent of every moving
source, mask, radius and row.  The realization equalities carry this
fixed kernel through the single prime pool and the original raw leaf.
-/

noncomputable section
open scoped Classical NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

open EngineStep
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem canonicalFirst_kernel (F : FirstPresentation call p)
    (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) :
    (F.canonicalChart v D).kernel = secondKernel c p := rfl

theorem realizedFirst_kernel (F : FirstPresentation call p) (hF : F.Realizes)
    (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) :
    (F.source.charts v D).kernel = secondKernel c p := by
  let Chart := fun profiles : F.source.Column → F.source.Column →
      SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ =>
    FirstBlockProfileChart (E := ℝ) (Arithmetic.units_are_sixth c)
      (Arithmetic.localMeasures (K := K)) (F.source.block v)
      (Arithmetic.context c) F.source.columns F.source.columns profiles
      (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) F.source.radius D.val
  have hpairs : (⟨F.source.profiles, F.source.charts v D⟩ : Sigma Chart) =
      (⟨F.originalProfile, F.canonicalChart v D⟩ : Sigma Chart) :=
    Sigma.ext hF.profile (hF.chart v D)
  have hkernel := congrArg (fun x : Sigma Chart => x.2.kernel) hpairs
  exact hkernel.trans (canonicalFirst_kernel F v D)

theorem firstCauchy_kernel {F : FirstPresentation call p}
    (hF : F.Realizes) (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (i : Fin family.count) :
    (family.source i).firstKernel = secondKernel c p := by
  rw [hfamily.kernel i]
  exact realizedFirst_kernel F hF (family.index i).1 (family.index i).2.1

theorem pool_kernel {F : FirstPresentation call p} {family : FirstCauchyFamily F}
    (expansion : PoolExpansion family) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count) :
    (expansion.source i).firstKernel =
      (family.source (expansion.firstIndex i)).firstKernel := by
  cases expansion with
  | direct => rfl
  | pooled pool count index source =>
      have hi := hexpansion.2.2 i
      cases htag : (index i).2 with
      | inl a =>
          simp only [PoolPresentation.Origin, htag] at hi
          exact hi.2.2.2.2.1
      | inr qe =>
          simp only [PoolPresentation.Origin, htag] at hi
          exact hi.2.2.2.2.1

theorem traceFirst_kernel (trace : SourceTrace call p) (htrace : trace.Realizes)
    (i : Fin trace.expansion.count) :
    (trace.second.source i).physical.firstKernel = secondKernel c p := by
  rw [htrace.second.physical i,
    pool_kernel trace.expansion htrace.expansion i]
  exact firstCauchy_kernel htrace.first trace.cauchy htrace.cauchy
    (trace.expansion.firstIndex i)

theorem leaf_firstKernel (packet : RawLeafPacket call p) (hpacket : packet.Realizes) :
    packet.leaf.firstKernel = secondKernel c p := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, _, _, rfl⟩
  exact traceFirst_kernel trace htrace (raw.index j).val.1.1

theorem leaf_secondKernel (packet : RawLeafPacket call p) (hpacket : packet.Realizes) :
    packet.leaf.secondKernel = secondKernel c p :=
  (packet.exceptional_second_realizes hpacket).kernel packet.key.1 packet.key.2.1

theorem leaf_measure (packet : RawLeafPacket call p) (hpacket : packet.Realizes) :
    packet.leaf.measure = nestedFourierMeasure (secondKernel c p) (secondKernel c p) := by
  rw [ActualHybridLeaf.measure, leaf_firstKernel packet hpacket,
    leaf_secondKernel packet hpacket]

/-- This finite number is selected before every moving call. -/
def kernelMoment (c : TargetContext K) (p : SourceParameters c) (J₁ J₂ : ℕ) : ℝ :=
  ∫ z : ℝ × ℝ, (1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂
    ∂nestedFourierMeasure (secondKernel c p) (secondKernel c p)

theorem kernelMoment_nonneg (c : TargetContext K) (p : SourceParameters c)
    (J₁ J₂ : ℕ) : 0 ≤ kernelMoment c p J₁ J₂ :=
  integral_nonneg (fun _ => mul_nonneg
    (pow_nonneg (by positivity) _) (pow_nonneg (by positivity) _))

/-- Integrate a polynomial bound with the two genuine fixed kernels.
The original outer leaf weight is paid exactly once. -/
theorem exceptionalCost_le_kernelMoment
    (packet : RawLeafPacket call p) (hpacket : packet.Realizes)
    (coefficient : ℝ) (J₁ J₂ : ℕ)
    (hpoint : ∀ z : ℝ × ℝ,
      packet.leaf.exceptionalIntegrand z ≤
        coefficient * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂)) :
    packet.leaf.exceptionalCost ≤
      packet.leaf.weight * coefficient * kernelMoment c p J₁ J₂ := by
  have hmajor : Integrable (fun z : ℝ × ℝ =>
      coefficient * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂))
        packet.leaf.measure := by
    rw [leaf_measure packet hpacket]
    exact (nestedFourierMeasure_mixed_polynomial_integrable
      (secondKernel c p) (secondKernel c p) J₁ J₂).const_mul coefficient
  calc
    packet.leaf.exceptionalCost ≤ packet.leaf.weight *
        ∫ z : ℝ × ℝ,
          coefficient * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂)
          ∂packet.leaf.measure :=
      mul_le_mul_of_nonneg_left
        (integral_mono packet.leaf.exceptionalIntegrand_integrable hmajor hpoint)
        packet.leaf.weight_nonneg
    _ = packet.leaf.weight * coefficient * kernelMoment c p J₁ J₂ := by
      rw [leaf_measure packet hpacket, integral_const_mul]
      exact (mul_assoc _ _ _).symm

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.leaf_measure
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.exceptionalCost_le_kernelMoment
