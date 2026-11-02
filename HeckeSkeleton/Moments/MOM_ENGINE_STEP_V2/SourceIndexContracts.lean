import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AmplifiedFiniteIndex

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N8a: the original arithmetic index and its physical fibres

This ledger contains no child, capacity, profile normalization or kernel.
Its four ideals are the two genuine common pairs and the two independent
Mobius divisors already present in the actual raw key. Both occurrence
allocations remain in that key. The source task sums this explicit
scalar over the physical labels, using the same single prime pool.

The main allowance contributes the pool length; each error contributes
its actual moving prime power. These are the factors in the base
`amplifiedIndexWeight`, not a second amplification or a pool cardinality.
Paper: Section 4.8, lines 2842--2850, 2852--2881 and 2895--2906.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open CommonSupportMass HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  coveredClassKeyFintype

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

namespace PoolExpansion

/-- The one original pool prefactor and the corresponding allowance.
No first-profile or normalized-child cost is included. -/
def indexPrefactor (expansion : PoolExpansion family) : Fin expansion.count → ℝ :=
  match expansion with
  | .direct => fun _ => 1
  | .pooled pool _ index _ => fun i =>
    let d := pool.data (index i).1
    (4 / d.density) *
      match (index i).2 with
      | .inl _ => d.multiplicity * call.base ^ (recipeInductionSigma c / 3)
      | .inr qe => FirstGaussPoolData.localErrorWeight qe.1.val qe.2.multiplicity *
          Q qe.1.val ^ qe.2.movingMultiplicity

end PoolExpansion

namespace RawFamily

variable {expansion : PoolExpansion family} {second : SecondFamily expansion}
variable {geometry : GeometryFamily second} (raw : RawFamily geometry)

def sourceIndex (j : Fin raw.count) : Fin expansion.count :=
  (raw.index j).val.1.1

def innerDivisor (j : Fin raw.count) : Ideal (𝓞 K) :=
  (raw.packet j).allocation.1.val

/-- The two common radicals and the two actual Mobius factors.
The second divisor norm is kept separate for the exceptional dyad. -/
def commonIndexFactor (j : Fin raw.count) : ℝ :=
  let packet := raw.packet j
  (1 / (Ideal.absNorm (commonRadical packet.second.physical.first.selected.val
    packet.second.physical.first.opposite.val) : ℝ)) *
    ‖(moebius packet.second.physical.first.residualDivisor.val : ℂ)‖ *
    (1 / (Ideal.absNorm (commonRadical packet.key.1.val.1 packet.key.1.val.2) : ℝ)) *
    ‖(moebius (raw.innerDivisor j) : ℂ)‖

def indexWeight (j : Fin raw.count) : ℝ :=
  expansion.indexPrefactor (raw.sourceIndex j) * raw.commonIndexFactor j /
    (Ideal.absNorm (raw.innerDivisor j) : ℝ)

def exceptionalDyadWeight (lower : ℝ) (j : Fin raw.count) : ℝ :=
  expansion.indexPrefactor (raw.sourceIndex j) * raw.commonIndexFactor j *
    call.base ^ (-lower)

def indexMass : ℝ := ∑ j, raw.indexWeight j

end RawFamily

/-- A uniform scalar estimate for the original arithmetic carrier.
The fixed constant and threshold precede the original call and all
physical/occurrence labels. The arbitrary positive `loss` pays the
physical finite fibres and harmonic sum; `p.loss` pays the one pool.
No transformed-family conclusion appears in this certificate. -/
structure SourceIndexCertificate (c : TargetContext K) (frame : SourceFrame)
    (p : SourceParameters c) (loss : ℝ) where
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  threshold : ℝ
  threshold_one : 1 ≤ threshold
  bound : ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
    threshold ≤ call.base → ∀ trace : SourceTrace call p, trace.Realizes →
    ∀ geometry : GeometryFamily trace.second, geometry.Realizes →
    ∀ raw : RawFamily geometry, raw.Realizes →
      raw.indexMass ≤ coefficient * call.base ^ (loss + p.loss)

/-- N8a. Construct the literal two-divisor arithmetic index map,
bound its original physical fibres, and sum its explicit weight.
Later passive/allocation/capacity fibres are a separate task. -/
def SourceIndexTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ (frame : SourceFrame) (loss : ℝ), 0 < loss →
    Nonempty (SourceIndexCertificate c frame p loss)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
