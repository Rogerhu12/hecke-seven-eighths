import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original first kernel through Cauchy and prime pooling

The first Poisson chart uses the fixed logarithmic kernel. Its original
realization equalities carry that kernel through weighted Cauchy and
the prime pool, up to the physical source of the second stage.
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

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.canonicalFirst_kernel
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.realizedFirst_kernel
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.firstCauchy_kernel
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.pool_kernel
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.traceFirst_kernel
