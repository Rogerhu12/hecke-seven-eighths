import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryRectangleFactors
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PoolContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The same original coefficient through the first source and prime pool

These lemmas transport an actual scalar column operation along an
explicit equality of its column types. The equality is used once and
coherently for the source, original index and multiplier. The residual
prime-pool operation is linear in each original column coefficient.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

namespace OrdinarySourceTransport

section PoolScalar

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}

/-- The pool changes the same column by a fixed scalar. An original
comparison factor is neither conjugated nor evaluated at a new index. -/
theorem residualCoefficient_mul (d : FirstGaussPoolData C P ι)
    (q : ExteriorPrime A) (n : ℕ) (f g : ι → ℂ)
    (i : d.valuationColumns q n) :
    d.residualCoefficient q n (fun j => f j * g j) i =
      d.residualCoefficient q n f i * g i.val := by
  unfold FirstGaussPoolData.residualCoefficient FirstGaussPoolData.adjustedCoefficient
  ring

/-- The preceding identity is pointwise, so only the original column
formula is required; all pool weights and row sets remain unchanged. -/
theorem residualCoefficient_eq_mul (d : FirstGaussPoolData C P ι)
    (q : ExteriorPrime A) (n : ℕ) (f g v : ι → ℂ)
    (hf : ∀ j, f j = g j * v j) (i : d.valuationColumns q n) :
    d.residualCoefficient q n f i = d.residualCoefficient q n g i * v i.val := by
  have hfun : f = fun j => g j * v j := funext hf
  rw [hfun]
  exact residualCoefficient_mul d q n g v i

end PoolScalar
end OrdinarySourceTransport

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace PhysicalSource

variable (source : PhysicalSource call p)

/-- The whole source coefficient is the original centered coefficient
after its actual linear column multiplier. -/
def CoefficientRealizes : Prop := ∀ i,
  source.source.coefficient i = source.multiplier i *
    call.workingValues.coefficient call.node.centered (source.ancestor i)

/-- Heterogeneous record fields are transported over one explicit
column equality, rather than assuming that an indexed type constructor
is injective on arbitrary types. -/
theorem coefficientRealizes_of_transport {ι : Type}
    (G : ActualGaussSource (Arithmetic.context c) ι)
    (ancestor : ι → call.workingRaw.Column) (multiplier : ι → ℂ)
    (column : source.Column = ι)
    (hsource : HEq source.source G)
    (hancestor : HEq source.ancestor ancestor)
    (hmultiplier : HEq source.multiplier multiplier)
    (hcoefficient : ∀ i, G.coefficient i = multiplier i *
      call.workingValues.coefficient call.node.centered (ancestor i)) :
    source.CoefficientRealizes := by
  subst ι
  have hs := eq_of_heq hsource
  have ha := eq_of_heq hancestor
  have hm := eq_of_heq hmultiplier
  intro i
  rw [hs, ha, hm]
  exact hcoefficient i

end PhysicalSource

namespace FirstCauchyFamily

variable {F : FirstPresentation call p} (family : FirstCauchyFamily F)

/-- The first original rectangle multiplier is valid at every column,
including zero coefficients and the original divisibility zero gate. -/
theorem coefficientRealizes (hF : F.Realizes) (hfamily : family.Realizes)
    (i : Fin family.count) : (family.source i).CoefficientRealizes := by
  apply (family.source i).coefficientRealizes_of_transport
    ((FirstCauchyKey.data (family.index i)).directSource
      (FirstCauchyKey.coefficient (family.index i)))
    (fun j : F.source.Column => F.index j)
    (FirstCauchyKey.multiplier (family.index i))
    (hfamily.column i) (hfamily.source i) (hfamily.ancestor i) (hfamily.multiplier i)
  intro j
  exact FirstCauchyKey.coefficient_eq_multiplier (family.index i) hF j

end FirstCauchyFamily

namespace PoolPresentation

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable (P : PoolPresentation family)

theorem main_coefficientRealizes (i : Fin family.count)
    (source : PhysicalSource call p)
    (horigin : P.MainOrigin i source)
    (hfirst : (family.source i).CoefficientRealizes) :
    source.CoefficientRealizes := by
  apply source.coefficientRealizes_of_transport
    ((P.data i).mainSource (family.source i).source.coefficient)
    (family.source i).ancestor (family.source i).multiplier
    horigin.1 horigin.2.1 horigin.2.2.1 horigin.2.2.2.1
  exact hfirst

theorem error_coefficientRealizes (i : Fin family.count)
    (q : P.pool.primes) (e : AmplifierValuation)
    (source : PhysicalSource call p)
    (horigin : P.ErrorOrigin i q e source)
    (hfirst : (family.source i).CoefficientRealizes) :
    source.CoefficientRealizes := by
  apply source.coefficientRealizes_of_transport
    ((P.data i).residualSource q.val e.multiplicity (family.source i).source.coefficient)
    (fun j : (P.data i).valuationColumns q.val e.multiplicity =>
      (family.source i).ancestor j.val)
    ((P.data i).residualCoefficient q.val e.multiplicity (family.source i).multiplier)
    horigin.1 horigin.2.1 horigin.2.2.1 horigin.2.2.2.1
  intro j
  exact OrdinarySourceTransport.residualCoefficient_eq_mul (P.data i)
    q.val e.multiplicity (family.source i).source.coefficient
    (family.source i).multiplier
    (fun j => call.workingValues.coefficient call.node.centered ((family.source i).ancestor j))
    hfirst j

end PoolPresentation

namespace PoolExpansion

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable (expansion : PoolExpansion family)

/-- The direct source and every member of the single chosen pool
retain the same centered coefficient at their original column. -/
theorem coefficientRealizes
    (hfirst : ∀ i, (family.source i).CoefficientRealizes)
    (hexpansion : expansion.Realizes) (i : Fin expansion.count) :
    (expansion.source i).CoefficientRealizes := by
  cases expansion with
  | direct => exact hfirst i
  | pooled P count index source =>
    have horigin := hexpansion.2.2 i
    cases hi : (index i).2 with
    | inl u =>
      apply P.main_coefficientRealizes (index i).1 (source i) _ (hfirst (index i).1)
      simpa only [PoolPresentation.Origin, hi] using horigin
    | inr qe =>
      apply P.error_coefficientRealizes (index i).1 qe.1 qe.2 (source i) _
        (hfirst (index i).1)
      simpa only [PoolPresentation.Origin, hi] using horigin

end PoolExpansion

namespace SourceTrace

variable (trace : SourceTrace call p)

/-- An exact invariant of the original first transform, the one pool
and the physical input to the second transform. -/
theorem coefficientRealizes (htrace : trace.Realizes)
    (i : Fin trace.expansion.count) :
    (trace.second.source i).physical.CoefficientRealizes := by
  rw [htrace.second.physical i]
  exact trace.expansion.coefficientRealizes
    (trace.cauchy.coefficientRealizes htrace.first htrace.cauchy) htrace.expansion i

end SourceTrace

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

/-- Both ordinary rectangles inherit this equality from their actual
source trace; no new coefficient hypothesis is needed at a leaf. -/
theorem realizes_coefficient (hpacket : packet.Realizes) :
    packet.second.physical.CoefficientRealizes := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  exact trace.coefficientRealizes htrace (raw.index j).val.1.1

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySourceTransport.residualCoefficient_mul
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PhysicalSource.coefficientRealizes_of_transport
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.realizes_coefficient
