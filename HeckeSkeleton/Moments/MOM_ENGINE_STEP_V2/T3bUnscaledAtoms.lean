import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bAtomFrames

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original common scalars stay outside the exceptional profiles

The two actual extraction scalars multiply the complete centered
columns.  Removing them from the plain profile is an exact finite-sum
identity, including when one scalar is zero.  Both quotient scales,
prime occurrences, masks and inner divisor allocations are unchanged.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

namespace T3b

theorem pairMagnitude_scalar
    {H I J V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (rows : Finset H) (left : Finset I) (right : Finset J)
    (q : H → ℂ) (c : H → I → ℂ) (d : H → J → ℂ)
    (x : H → I → V) (y : H → J → V) (a b : ℂ) (ξ : V) :
    jointColumnPairMagnitude rows left right q
      (fun h i => a * c h i) (fun h j => b * d h j) x y ξ =
      (‖a‖ * ‖b‖) * jointColumnPairMagnitude rows left right q c d x y ξ := by
  have hl (h : H) : jointFourierColumn left (fun i => a * c h i) (x h) ξ =
      a * jointFourierColumn left (c h) (x h) ξ := by
    simp only [jointFourierColumn, Finset.mul_sum, mul_assoc]
  have hr (h : H) : jointFourierColumn right (fun j => b * d h j) (y h) ξ =
      b * jointFourierColumn right (d h) (y h) ξ := by
    simp only [jointFourierColumn, Finset.mul_sum, mul_assoc]
  simp only [jointColumnPairMagnitude, hl, hr, norm_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

end T3b

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)
variable (hpacket : packet.Realizes) (phases : OriginalPhaseData packet)

def t3bUnscaledTable : (side : Bool) → OrdinaryAtomTable (K := K) (packet.ordinarySlots side)
  | false => (packet.firstAtomTable hpacket phases false).unitGaussExtract
      (packet.secondBranch false)
  | true => (packet.firstAtomTable hpacket phases true).unitGaussExtract
      (packet.secondBranch true)

theorem t3b_before_eq_scale (side : Bool) :
    packet.beforeAtomTable hpacket phases side =
      (packet.t3bUnscaledTable hpacket phases side).scale
        (packet.secondAtomScalar hpacket phases side) := by
  cases side <;> rfl

theorem t3bUnscaled_leftWeight (side rectangle : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (packet.t3bUnscaledTable hpacket phases side).leftWeight rectangle I =
      packet.normProfile false
        (idealNorm K I / (packet.t3bUnscaledTable hpacket phases side).scale₁ rectangle) := by
  cases side <;>
    change packet.normProfile false
      (idealNorm K (_ * I) / packet.firstPlainScale _ rectangle false) = _ <;>
    rw [original_norm_quotient _ I _ (packet.firstPlainScale_pos _ rectangle false)] <;> rfl

theorem t3bUnscaled_rightWeight (side rectangle : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (packet.t3bUnscaledTable hpacket phases side).rightWeight rectangle I =
      packet.normProfile true
        (idealNorm K I / (packet.t3bUnscaledTable hpacket phases side).scale₂ rectangle) := by
  cases side <;>
    change packet.normProfile true
      (idealNorm K (_ * I) / packet.firstPlainScale _ rectangle true) = _ <;>
    rw [original_norm_quotient _ I _ (packet.firstPlainScale_pos _ rectangle true)] <;> rfl

theorem t3bUnscaled_scale_product (side rectangle : Bool) :
    (packet.t3bUnscaledTable hpacket phases side).scale₁ rectangle *
        (packet.t3bUnscaledTable hpacket phases side).scale₂ rectangle =
      (packet.t3bUnscaledTable hpacket phases side).scale₁ false *
        (packet.t3bUnscaledTable hpacket phases side).scale₂ false := by
  cases side <;>
    change packet.firstPlainScale _ rectangle false / _ *
        (packet.firstPlainScale _ rectangle true / _) =
      packet.firstPlainScale _ false false / _ *
        (packet.firstPlainScale _ false true / _) <;>
    rw [div_mul_div_comm, div_mul_div_comm, packet.firstPlainScale_product]

def t3bUnscaledLeftFrame :
    SecondSideFrame (V := EngineParameter) (Arithmetic.context c) packet.R
      PUnit.{1} .left packet.leaf.leftSlots :=
  { packet.t3bLeftFrame hpacket phases with
    dictionary := (packet.t3bUnscaledTable hpacket phases false).dictionary
      (SecondColumnSide.left.phase PUnit.{1} packet.allocation.2.1)
      packet.leftReindex.plain₁ packet.leftReindex.plain₂ packet.leftReindex.slots false }

def t3bUnscaledRightFrame :
    SecondSideFrame (V := EngineParameter) (Arithmetic.context c) packet.R
      PUnit.{1} .right packet.leaf.rightSlots :=
  { packet.t3bRightFrame hpacket phases with
    dictionary := (packet.t3bUnscaledTable hpacket phases true).dictionary
      (SecondColumnSide.right.phase PUnit.{1} packet.allocation.2.1)
      packet.rightReindex.plain₁ packet.rightReindex.plain₂ packet.rightReindex.slots false }

def t3bUnscaledLeftComparison :
    SecondCoefficientComparison (packet.t3bUnscaledLeftFrame hpacket phases).dictionary :=
  (packet.t3bUnscaledTable hpacket phases false).t3bComparison
    (SecondColumnSide.left.phase PUnit.{1} packet.allocation.2.1)
    packet.leftReindex.plain₁ packet.leftReindex.plain₂ packet.leftReindex.slots

def t3bUnscaledRightComparison :
    SecondCoefficientComparison (packet.t3bUnscaledRightFrame hpacket phases).dictionary :=
  (packet.t3bUnscaledTable hpacket phases true).t3bComparison
    (SecondColumnSide.right.phase PUnit.{1} packet.allocation.2.1)
    packet.rightReindex.plain₁ packet.rightReindex.plain₂ packet.rightReindex.slots

theorem t3b_left_scalar (h : Arithmetic.Orbit c)
    (i : AllocationColumn K packet.leaf.leftSlots) :
    (packet.t3bLeftFrame hpacket phases).centeredCoefficient
        (packet.t3bLeftComparison hpacket phases) h i =
      packet.secondAtomScalar hpacket phases false *
        (packet.t3bUnscaledLeftFrame hpacket phases).centeredCoefficient
          (packet.t3bUnscaledLeftComparison hpacket phases) h i := by
  let d := packet.t3bUnscaledTable hpacket phases false
  let a := packet.secondAtomScalar hpacket phases false
  let phase := SecondColumnSide.left.phase PUnit.{1} packet.allocation.2.1
  change ((d.scale a).t3bComparison phase _ _ _).centeredCoefficient
      (Real.sqrt d.gauss₁ : ℂ)⁻¹ (Real.sqrt d.gauss₂ : ℂ)⁻¹
      (fun j => (Real.sqrt (d.gaussSlot j) : ℂ)⁻¹) i * _ * _ =
    a * ((d.t3bComparison phase _ _ _).centeredCoefficient
      (Real.sqrt d.gauss₁ : ℂ)⁻¹ (Real.sqrt d.gauss₂ : ℂ)⁻¹
      (fun j => (Real.sqrt (d.gaussSlot j) : ℂ)⁻¹) i * _ * _)
  rw [(d.scale a).t3bComparison_centeredCoefficient,
    d.t3bComparison_centeredCoefficient, d.scale_whole]
  ring

theorem t3b_right_scalar (h : Arithmetic.Orbit c)
    (i : AllocationColumn K packet.leaf.rightSlots) :
    (packet.t3bRightFrame hpacket phases).centeredCoefficient
        (packet.t3bRightComparison hpacket phases) h i =
      star (packet.secondAtomScalar hpacket phases true) *
        (packet.t3bUnscaledRightFrame hpacket phases).centeredCoefficient
          (packet.t3bUnscaledRightComparison hpacket phases) h i := by
  let d := packet.t3bUnscaledTable hpacket phases true
  let a := packet.secondAtomScalar hpacket phases true
  let phase := SecondColumnSide.right.phase PUnit.{1} packet.allocation.2.1
  change star (((d.scale a).t3bComparison phase _ _ _).centeredCoefficient
      (Real.sqrt d.gauss₁ : ℂ)⁻¹ (Real.sqrt d.gauss₂ : ℂ)⁻¹
      (fun j => (Real.sqrt (d.gaussSlot j) : ℂ)⁻¹) i * _ * _) =
    star a * star ((d.t3bComparison phase _ _ _).centeredCoefficient
      (Real.sqrt d.gauss₁ : ℂ)⁻¹ (Real.sqrt d.gauss₂ : ℂ)⁻¹
      (fun j => (Real.sqrt (d.gaussSlot j) : ℂ)⁻¹) i * _ * _)
  rw [(d.scale a).t3bComparison_centeredCoefficient,
    d.t3bComparison_centeredCoefficient, d.scale_whole]
  simp only [star_mul']
  ring

theorem t3b_magnitude_scalar {theta : Finset (HeckeCharacter K)}
    (Q : PairedFiniteCharacters theta (Arithmetic.Orbit c)) (ξ : EngineParameter) :
    (packet.t3bLeftFrame hpacket phases).exceptionalMagnitude
        (packet.t3bRightFrame hpacket phases)
        (packet.t3bLeftComparison hpacket phases)
        (packet.t3bRightComparison hpacket phases) Q ξ =
      (‖packet.secondAtomScalar hpacket phases false‖ *
          ‖packet.secondAtomScalar hpacket phases true‖) *
        (packet.t3bUnscaledLeftFrame hpacket phases).exceptionalMagnitude
          (packet.t3bUnscaledRightFrame hpacket phases)
          (packet.t3bUnscaledLeftComparison hpacket phases)
          (packet.t3bUnscaledRightComparison hpacket phases) Q ξ := by
  unfold SecondSideFrame.exceptionalMagnitude
  simp_rw [packet.t3b_left_scalar hpacket phases, packet.t3b_right_scalar hpacket phases]
  rw [T3b.pairMagnitude_scalar, norm_star]

theorem t3b_exceptional_integrand_unscaled {theta : Finset (HeckeCharacter K)}
    (Q : PairedFiniteCharacters theta (Arithmetic.Orbit c))
    (hpredicate : packet.leaf.exceptional = Q.exceptional) (z : ℝ × ℝ) :
    packet.leaf.exceptionalIntegrand z =
      (‖packet.secondAtomScalar hpacket phases false‖ *
          ‖packet.secondAtomScalar hpacket phases true‖) *
        (packet.t3bUnscaledLeftFrame hpacket phases).exceptionalMagnitude
          (packet.t3bUnscaledRightFrame hpacket phases)
          (packet.t3bUnscaledLeftComparison hpacket phases)
          (packet.t3bUnscaledRightComparison hpacket phases) Q (WithLp.toLp 2 z) := by
  rw [packet.t3b_exceptional_integrand hpacket phases Q hpredicate,
    packet.t3b_magnitude_scalar hpacket phases Q]

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3bUnscaled_scale_product
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_exceptional_integrand_unscaled
