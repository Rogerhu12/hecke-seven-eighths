import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinarySourceTransport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceScalarData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralLocations

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original first Fourier point through the single prime pool

The point is the signed logarithm of the same original first ideal.
The pool removes a literal prime power from the ideal, while its point
continues to contain that fixed power. These identities precede the
common row translations used by the four ordinary rectangles.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

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

variable (F : FirstPresentation call p) (hF : F.Realizes)

theorem chart_leftPoint (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) (i : F.source.Column) :
    (F.source.charts v D).leftPoint i =
      -Real.log ((Arithmetic.data c).exteriorNorm ((F.source.block v).leftResidual i)) := by
  have heq : (F.source.charts v D).leftPoint = (F.canonicalChart v D).leftPoint := by
    congr 1 <;> first | exact hF.profile | exact hF.chart v D
  rw [congrFun heq i]
  rfl

theorem chart_rightPoint (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) (i : F.source.Column) :
    (F.source.charts v D).rightPoint i =
      -Real.log ((Arithmetic.data c).exteriorNorm ((F.source.block v).rightResidual i)) := by
  have heq : (F.source.charts v D).rightPoint = (F.canonicalChart v D).rightPoint := by
    congr 1 <;> first | exact hF.profile | exact hF.chart v D
  rw [congrFun heq i]
  rfl

end FirstPresentation

namespace FirstCauchyKey

variable {F : FirstPresentation call p} (key : FirstCauchyKey F)

theorem point_eq_log (hF : F.Realizes) (i : F.source.Column) :
    FirstCauchyKey.point key i = -(if FirstCauchyKey.side key then -1 else (1 : ℝ)) *
      Real.log ((Arithmetic.data c).exteriorNorm ((FirstCauchyKey.data key).ideal i)) := by
  rw [key.data_ideal i]
  cases hs : FirstCauchyKey.side key
  · simp only [FirstCauchyKey.point, hs, Bool.false_eq_true, if_false]
    rw [F.chart_leftPoint hF key.1 key.2.1 i]
    ring
  · simp only [FirstCauchyKey.point, hs, if_true]
    rw [F.chart_rightPoint hF key.1 key.2.1 i]
    ring

end FirstCauchyKey

namespace PhysicalSource

variable (source : PhysicalSource call p)

/-- An error source retains the point of its original full first
ideal; its removed prime power is present exactly once. -/
def PointRealizes : Prop := ∀ i,
  source.firstPoint i = -(if source.first.firstRight then -1 else (1 : ℝ)) *
    Real.log ((Arithmetic.data c).exteriorNorm source.first.poolPower *
      (Arithmetic.data c).exteriorNorm (source.source.ideal i))

theorem pointRealizes_of_transport {ι : Type}
    (G : ActualGaussSource (Arithmetic.context c) ι) (point : ι → ℝ)
    (right : Bool) (power : (Arithmetic.data c).Exterior)
    (column : source.Column = ι) (hsource : HEq source.source G)
    (hpoint : HEq source.firstPoint point)
    (hright : source.first.firstRight = right) (hpower : source.first.poolPower = power)
    (hformula : ∀ i, point i = -(if right then -1 else (1 : ℝ)) *
      Real.log ((Arithmetic.data c).exteriorNorm power *
        (Arithmetic.data c).exteriorNorm (G.ideal i))) : source.PointRealizes := by
  subst ι
  have hs := eq_of_heq hsource
  have hp := eq_of_heq hpoint
  intro i
  rw [hp, hs, hright, hpower]
  exact hformula i

end PhysicalSource

namespace FirstCauchyFamily

variable {F : FirstPresentation call p} (family : FirstCauchyFamily F)

theorem pointRealizes (hF : F.Realizes) (hfamily : family.Realizes)
    (i : Fin family.count) : (family.source i).PointRealizes := by
  apply (family.source i).pointRealizes_of_transport
    ((FirstCauchyKey.data (family.index i)).directSource
      (FirstCauchyKey.coefficient (family.index i)))
    (FirstCauchyKey.point (family.index i)) (FirstCauchyKey.side (family.index i))
    (unitExterior (Arithmetic.data c))
    (hfamily.column i) (hfamily.source i) (hfamily.point i)
    (hfamily.firstRight i) (hfamily.poolPower i)
  intro j
  have hunit : (Arithmetic.data c).exteriorNorm (unitExterior (Arithmetic.data c)) = 1 := by
    change (Ideal.absNorm (1 : Ideal (𝓞 K)) : ℝ) = 1
    simp only [map_one, Nat.cast_one]
  rw [hunit, one_mul]
  exact FirstCauchyKey.point_eq_log (family.index i) hF j

end FirstCauchyFamily

namespace PoolPresentation

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable (P : PoolPresentation family)

theorem main_pointRealizes (hP : P.Realizes) (i : Fin family.count)
    (source : PhysicalSource call p) (horigin : P.MainOrigin i source)
    (hfirst : (family.source i).PointRealizes) : source.PointRealizes := by
  rcases horigin with ⟨hcolumn, hsource, hancestor, hmultiplier, hkernel,
    hpoint, houter, hcoordinates⟩
  apply source.pointRealizes_of_transport
    ((P.data i).mainSource (family.source i).source.coefficient)
    (family.source i).firstPoint (family.source i).first.firstRight
    (family.source i).first.poolPower hcolumn hsource hpoint
    (congrArg FirstCoordinates.firstRight hcoordinates)
    (congrArg FirstCoordinates.poolPower hcoordinates)
  intro j
  have hideal : (P.data i).ideal j = (family.source i).source.ideal j :=
    congrArg (fun G => G.ideal j) (hP.original i)
  change (family.source i).firstPoint j = _ * Real.log
    (_ * (Arithmetic.data c).exteriorNorm ((P.data i).ideal j))
  rw [hideal]
  exact hfirst j

theorem error_pointRealizes (hP : P.Realizes) (i : Fin family.count)
    (q : P.pool.primes) (e : AmplifierValuation)
    (source : PhysicalSource call p) (horigin : P.ErrorOrigin i q e source)
    (hpower : (family.source i).first.poolPower = unitExterior (Arithmetic.data c))
    (hfirst : (family.source i).PointRealizes) : source.PointRealizes := by
  rcases horigin with ⟨hcolumn, hsource, hancestor, hmultiplier, hkernel,
    hpoint, houter, hselected, hopposite, hcomplementary, hresidual,
    helement, hright, hpool, hretained, htag, hdeletion, hpaid⟩
  apply source.pointRealizes_of_transport
    ((P.data i).residualSource q.val e.multiplicity (family.source i).source.coefficient)
    (fun j : (P.data i).valuationColumns q.val e.multiplicity =>
      (family.source i).firstPoint j.val)
    (family.source i).first.firstRight (powerIdeal q.val e.multiplicity)
    hcolumn hsource hpoint hright hpool
  intro j
  have hideal : (P.data i).ideal j.val = (family.source i).source.ideal j.val :=
    congrArg (fun G => G.ideal j.val) (hP.original i)
  have hunit : (Arithmetic.data c).exteriorNorm (unitExterior (Arithmetic.data c)) = 1 := by
    change (Ideal.absNorm (1 : Ideal (𝓞 K)) : ℝ) = 1
    simp only [map_one, Nat.cast_one]
  have hnorm : (Arithmetic.data c).exteriorNorm ((P.data i).ideal j.val) =
      (Arithmetic.data c).exteriorNorm (powerIdeal q.val e.multiplicity) *
        (Arithmetic.data c).exteriorNorm
          ((P.data i).residualPresentation q.val e.multiplicity j).residual := by
    change (Ideal.absNorm ((P.data i).ideal j.val).val : ℝ) = _
    rw [((P.data i).residualPresentation q.val e.multiplicity j).reconstructed,
      map_mul, Nat.cast_mul]
    rfl
  rw [hfirst j.val, hpower, hunit, one_mul, ← hideal, hnorm]
  rfl

end PoolPresentation

namespace PoolExpansion

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable (expansion : PoolExpansion family)

theorem pointRealizes
    (hfirst : ∀ i, (family.source i).PointRealizes)
    (hpower : ∀ i, (family.source i).first.poolPower = unitExterior (Arithmetic.data c))
    (hexpansion : expansion.Realizes) (i : Fin expansion.count) :
    (expansion.source i).PointRealizes := by
  cases expansion with
  | direct => exact hfirst i
  | pooled P count index source =>
    have horigin := hexpansion.2.2 i
    cases hi : (index i).2 with
    | inl u =>
      apply P.main_pointRealizes hexpansion.2.1 (index i).1 (source i) _
        (hfirst (index i).1)
      simpa only [PoolPresentation.Origin, hi] using horigin
    | inr qe =>
      apply P.error_pointRealizes hexpansion.2.1 (index i).1 qe.1 qe.2 (source i) _
        (hpower (index i).1) (hfirst (index i).1)
      simpa only [PoolPresentation.Origin, hi] using horigin

end PoolExpansion

namespace SourceTrace

variable (trace : SourceTrace call p)

theorem pointRealizes (htrace : trace.Realizes) (i : Fin trace.expansion.count) :
    (trace.second.source i).physical.PointRealizes := by
  rw [htrace.second.physical i]
  exact trace.expansion.pointRealizes
    (trace.cauchy.pointRealizes htrace.first htrace.cauchy)
    htrace.cauchy.poolPower htrace.expansion i

end SourceTrace

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

theorem realizes_point (hpacket : packet.Realizes) : packet.second.physical.PointRealizes := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  exact trace.pointRealizes htrace (raw.index j).val.1.1

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstCauchyKey.point_eq_log
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.realizes_point
