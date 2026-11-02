import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RefinementAssembly

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original two Fourier kernels are fixed before every moving label

Both canonical logarithmic charts use the original row-ball test and
the same fixed tilt.  The Cauchy side, the single pool, its main/error
tag, both covered allocations and every passive label only transport
this Schwartz function.  These are exact identities, not kernel bounds.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace FirstPresentation

variable (F : FirstPresentation call p)

/-- Project a heterogeneous chart equality after identifying its original
profile parameter.  This does not unfold the orbital transform. -/
private theorem chart_kernel_congr
    (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset)
    {f g : F.source.Column → F.source.Column →
      SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
    (hfg : f = g)
    (a : FirstBlockProfileChart (E := ℝ) (Arithmetic.units_are_sixth c)
      (Arithmetic.localMeasures (K := K)) (F.source.block v)
      (Arithmetic.context c) F.source.columns F.source.columns f
      (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) F.source.radius D.val)
    (b : FirstBlockProfileChart (E := ℝ) (Arithmetic.units_are_sixth c)
      (Arithmetic.localMeasures (K := K)) (F.source.block v)
      (Arithmetic.context c) F.source.columns F.source.columns g
      (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) F.source.radius D.val)
    (hab : HEq a b) : a.kernel = b.kernel := by
  cases hfg
  cases (eq_of_heq hab)
  rfl

theorem kernel_eq_original (hF : F.Realizes)
    (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) :
    (F.source.charts v D).kernel = secondKernel c p := by
  have he := F.chart_kernel_congr v D hF.profile
    (F.source.charts v D) (F.canonicalChart v D) (hF.chart v D)
  exact he.trans rfl

end FirstPresentation

namespace FirstCauchyFamily

variable {F : FirstPresentation call p} (family : FirstCauchyFamily F)

theorem firstKernel_eq_original (hF : F.Realizes) (hfamily : family.Realizes)
    (i : Fin family.count) :
    (family.source i).firstKernel = secondKernel c p :=
  (hfamily.kernel i).trans
    (F.kernel_eq_original hF (family.index i).1 (family.index i).2.1)

end FirstCauchyFamily

namespace PoolExpansion

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

theorem firstKernel_eq_original (expansion : PoolExpansion family)
    (hF : F.Realizes) (hfamily : family.Realizes) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count) :
    (expansion.source i).firstKernel = secondKernel c p := by
  cases expansion with
  | direct => exact family.firstKernel_eq_original hF hfamily i
  | pooled pool count index source =>
    have horigin := hexpansion.2.2 i
    have hk : (source i).firstKernel = (family.source (index i).1).firstKernel := by
      rcases htag : (index i).2 with u | qe
      · simp only [PoolPresentation.Origin, htag] at horigin
        exact horigin.2.2.2.2.1
      · simp only [PoolPresentation.Origin, htag] at horigin
        exact horigin.2.2.2.2.1
    exact hk.trans (family.firstKernel_eq_original hF hfamily (index i).1)

end PoolExpansion

namespace RawFamily

variable (trace : SourceTrace call p) (htrace : trace.Realizes)
variable {geometry : GeometryFamily trace.second} (raw : RawFamily geometry)

theorem firstKernel_eq_original (j : Fin raw.count) :
    (raw.packet j).leaf.firstKernel = secondKernel c p := by
  change (trace.second.source (raw.index j).val.1.1).physical.firstKernel = _
  rw [htrace.second.physical]
  exact trace.expansion.firstKernel_eq_original
    htrace.first htrace.cauchy htrace.expansion _

theorem secondKernel_eq_original (j : Fin raw.count) :
    (raw.packet j).leaf.secondKernel = secondKernel c p :=
  (htrace.second.stage (raw.index j).val.1.1).kernel
    (raw.index j).val.1.2.1 (raw.index j).val.1.2.2.1

theorem measure_eq_original (j : Fin raw.count) :
    (raw.packet j).leaf.measure =
      nestedFourierMeasure (secondKernel c p) (secondKernel c p) := by
  change nestedFourierMeasure _ _ = _
  rw [raw.firstKernel_eq_original trace htrace, raw.secondKernel_eq_original trace htrace]

end RawFamily

namespace RawLeafPacket

theorem original_kernels (packet : RawLeafPacket call p) (hpacket : packet.Realizes) :
    packet.leaf.firstKernel = secondKernel c p ∧
      packet.leaf.secondKernel = secondKernel c p := by
  obtain ⟨trace, geometry, raw, j, htrace, _, _, rfl⟩ := hpacket
  exact ⟨raw.firstKernel_eq_original trace htrace j,
    raw.secondKernel_eq_original trace htrace j⟩

end RawLeafPacket

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open Blueprint EngineStep
open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {input : ProfileInput call}
variable (trace : SourceTrace call p) (htrace : trace.Realizes)
variable {geometry : GeometryFamily trace.second} (raw : RawFamily geometry)
variable (O : ∀ j : Fin raw.count, OrdinaryData (raw.packet j))
variable (R : ∀ j, RefinementData (O j) input)
variable (C : ∀ j, (R j).Calibrations) (G : ∀ j, (C j).Capacities)

theorem refinedNormalizedData_original_kernels
    (b : (refinedNormalizedData raw O R C G).Label) :
    (refinedNormalizedData raw O R C G).firstKernel b = secondKernel c p ∧
      (refinedNormalizedData raw O R C G).secondKernel b = secondKernel c p :=
  ⟨raw.firstKernel_eq_original trace htrace b.1,
    raw.secondKernel_eq_original trace htrace b.1⟩

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstPresentation.kernel_eq_original
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawFamily.firstKernel_eq_original
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawFamily.secondKernel_eq_original
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.refinedNormalizedData_original_kernels
