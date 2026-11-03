import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualExceptionalRows
import HeckeGeneral.Analysis.SixthPowerFreeDecomposition

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T3a: arithmetic recovery on the original exceptional rows

The rows, sixth-free bases and multiplicity-one radical below are real
definitions on the actual second correlation. The task proves their
arithmetic properties from the original theta test and the nonzero
frozen source mask. It chooses neither an exceptional majorant nor a
new row predicate. The finite unit sectors and original orbit fibres
remain visible before the supported-volume estimate in T3b.

Paper: Section 4.8, lines 2948--2965.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

def exceptionalRows : Finset packet.R.live :=
  Finset.univ.filter (fun h => packet.leaf.exceptional h.val ∧
    packet.leaf.rowWeight h.val ≠ 0 ∧
    (∃ i ∈ packet.leaf.left, packet.leaf.leftCoefficient h.val i ≠ 0) ∧
    (∃ j ∈ packet.leaf.right, packet.leaf.rightCoefficient h.val j ≠ 0))

/-- The same two whole finite polynomials, with only identically zero
row contributions removed. Neither column is replaced by its absolute
coefficient sum. -/
def supportedExceptionalIntegrand (z : ℝ × ℝ) : ℝ :=
  jointColumnPairMagnitude packet.exceptionalRows packet.leaf.left packet.leaf.right
    (fun h => packet.leaf.rowWeight h.val)
    (fun h i => packet.leaf.leftCoefficient h.val i)
    (fun h j => star (packet.leaf.rightCoefficient h.val j))
    (fun h i => WithLp.toLp 2
      (packet.leaf.leftFirst h.val i, packet.leaf.leftSecond h.val i))
    (fun h j => WithLp.toLp 2
      (-packet.leaf.rightFirst h.val j, packet.leaf.rightSecond h.val j))
    (WithLp.toLp 2 z)

def sixthBase (h : packet.R.live) : HeckeGeneral.Analysis.NonzeroIdeal K :=
  sixthPowerFreePart (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal

def exceptionalBases : Finset (HeckeGeneral.Analysis.NonzeroIdeal K) :=
  packet.exceptionalRows.image packet.sixthBase

def multiplicityOneRadical (h : packet.R.live) : (Arithmetic.data c).Exterior :=
  multiplicityOneNonunitRadical (Arithmetic.context c) packet.R.primes
    packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val)

/-- Every field concerns the actual original row or its actual
sixth-power decomposition. In particular the fibre bound is the fixed
index of the original sixth-power S-unit subgroup. -/
structure ExceptionalRecovery : Prop where
  exact_support : ∀ z, packet.leaf.exceptionalIntegrand z =
    packet.supportedExceptionalIntegrand z
  bases_card : packet.exceptionalBases.card ≤
    call.node.data.theta.card * Nat.card (SixthUnitClasses K (places K c))
  factorization : ∀ h ∈ packet.exceptionalRows,
    (packet.R.extractedRow (Arithmetic.context c) h).ideal.val =
      (packet.sixthBase h).val *
        (sixthPowerAmplifierPart
          (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal).val ^ 6
  sixth_free : ∀ I ∈ packet.exceptionalBases, SixthPowerFreeIdeal I
  valuations : ∀ h ∈ packet.exceptionalRows,
    ∀ i ∈ multiplicityOneNonunitPrimes (Arithmetic.context c) packet.R.primes
      packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val),
      6 ∣ (normalizedFactors (packet.R.originalIdeal h.val).val).count
        (packet.R.primes i).val.asIdeal
  extracted_fibres : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K,
    (packet.exceptionalRows.filter (fun h =>
      (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal = I)).card ≤
        (Arithmetic.unitSubgroup c).index
  fourth_power : ∀ h ∈ packet.exceptionalRows,
    (packet.multiplicityOneRadical h).val ^ 4 ∣ (packet.sixthBase h).val ∧
      (Arithmetic.data c).exteriorNorm (packet.multiplicityOneRadical h) ^ 4 ≤
        (Ideal.absNorm (packet.sixthBase h).val : ℝ)

end RawLeafPacket

/-- T3a. Recover the sixth-power classes and valuation savings on
each leaf produced by the fixed original source chain. -/
def ExceptionalRecoveryTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ (call : Call c) (packet : RawLeafPacket call p), packet.Realizes →
    packet.ExceptionalRecovery

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

