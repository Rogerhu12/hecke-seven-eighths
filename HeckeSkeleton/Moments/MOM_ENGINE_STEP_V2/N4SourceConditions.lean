import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4SourceBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CanonicalRefinement
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4PacketGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4PaidSupport

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N4: original support atoms and the same finite source rows

The S5 support window bounds the product of the paid old support and
the two actual second radicals. The complete second sixth root remains
in the deletion ideal and is charged once, through its actual norm.
The primitive input is the original generated-ideal atom certificate;
the support and full joint budgets are conclusions.

The final constructor uses the calibration's exact finite row image.
Thus a passive allocation changes neither the row tested by S5 nor the
row to which the full joint budget applies.

Paper: Section 4.8, lines 2883--2906 and 2927--2946.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

variable {c : TargetContext K} {call : Call c} {H : Type} {k : ℕ}
variable {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter H k}

section Canonical

variable {p : SourceParameters c} {packet : RawLeafPacket call p}

private def originalLiveRow (O : OrdinaryData packet) (h : O.rows.live) : packet.R.live :=
  ⟨h.val, Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp h.property).1).1,
      (Finset.mem_filter.mp h.property).2⟩⟩

private theorem originalSource_momentIdeal (O : OrdinaryData packet)
    (side rectangle : Bool) (h : O.rows.live) :
    ((O.originalSource side rectangle).row h).momentIdeal =
      (packet.R.extractedRow (Arithmetic.context c) (originalLiveRow O h)).momentIdeal := by
  cases side <;> rfl

private theorem canonicalSource_rowWindow (seed : OrdinarySeed packet)
    (input : ProfileInput call) (support : seed.ordinary.PassiveSupport input)
    (hpacket : packet.Realizes) (side : Bool) (a : support.labels side) (rectangle : Bool)
    (h : seed.ordinary.rows.live) :
    idealNorm K ((seed.canonicalSource input support side a rectangle).row h).momentIdeal ≤
      call.base ^ ((packet.nominal side).skeleton.nominalRow + 12 * p.loss) := by
  change idealNorm K ((seed.ordinary.originalSource side false).row h).momentIdeal ≤ _
  rw [originalSource_momentIdeal]
  have hrow : ∀ h : packet.R.live,
      idealNorm K (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal ≤
        call.base ^ ((packet.nominal side).skeleton.nominalRow + 12 * p.loss) := by
    rcases hpacket with ⟨trace, geometry, raw, j, _, hgeometry, _, rfl⟩
    exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).rowWindow side
  exact hrow (originalLiveRow seed.ordinary h)

private theorem paid_radical_window (hpacket : packet.Realizes) (side : Bool)
    (h : packet.R.live) :
    (Arithmetic.data c).exteriorNorm packet.second.physical.first.paidSupport *
      (Arithmetic.data c).exteriorNorm
        (unitFrequencyRadical (Arithmetic.context c) packet.R.primes
          packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val)) *
      (Arithmetic.data c).exteriorNorm
        (nonunitFrequencyRadical (Arithmetic.context c) packet.R.primes
          packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val)) ≤
      call.base ^ ((packet.nominal side).skeleton.nominalSupport + 4 * p.loss) := by
  have hw : (Arithmetic.data c).exteriorNorm packet.second.physical.first.paidSupport *
      (Ideal.absNorm (packet.nominal side).ideals.unitPart.val : ℝ) *
      (Ideal.absNorm (packet.nominal side).ideals.nonunitPart.val : ℝ) ≤
        call.base ^ ((packet.nominal side).skeleton.nominalSupport + 4 * p.loss) := by
    rcases hpacket with ⟨trace, geometry, raw, j, _, hgeometry, _, rfl⟩
    exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).supportWindow side
  rw [packet_unit_ideal packet hpacket side h, packet_nonunit_ideal packet hpacket side h] at hw
  exact hw

/-- Exact N3 recipe identities, together with its original row image
and profile predicates, give both N4 budgets on that same calibration.
The actual support atoms and both physical windows are proved here
from the packet's original trace; none is a new calibration premise. -/
def sourceConditions_of_exact_recipe
    (seed : OrdinarySeed packet) (input : ProfileInput call)
    (support : seed.ordinary.PassiveSupport input) (hpacket : packet.Realizes)
    (side : Bool) (a : support.labels side) (rectangle : Bool)
    (D : OriginalCalibration call (seed.canonicalSource input support side a rectangle))
    (pattern : Fin packet.block.primeCount → Bool)
    (h : packet.R.NonunitClass (Arithmetic.context c) pattern)
    (moving_eq : D.recipe.moving = (seed.phases.moving true).append
      (secondOriginalMovingFactors (probeData K c) (momentRowCharacters K c)
        (Arithmetic.context c) packet.R.primes packet.R.leftMultiplicity
        packet.R.rightMultiplicity pattern))
    (remaining_eq : D.recipe.remaining =
      remainingMaskIdeal (Arithmetic.data c) call.localizedSource.source.recipe.remaining *
        exteriorMomentIdeal (secondSixthRootIdeal packet.R.primes
          packet.R.leftMultiplicity packet.R.rightMultiplicity))
    (hm : D.calibration.parameters.m = (packet.nominal side).skeleton.nominalRow + 12 * p.loss)
    (hq : D.calibration.parameters.q = (packet.nominal side).skeleton.nominalSupport + 4 * p.loss +
      idealLogLength call.base (secondSixthRootIdeal packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity).val)
    (allowed : ∀ ξ u, (D.calibration.data ξ).allowedRow u ↔
      ∃ h ∈ (seed.canonicalSource input support side a rectangle).rows,
        ((seed.canonicalSource input support side a rectangle).row h).momentIdeal = u)
    (timeIndependent : ∀ ξ, ProfileTimeIndependent (D.calibration.data ξ))
    (primeSupport : ∀ ξ, PrimeProfileSupport (D.calibration.data ξ)) : D.SourceConditions := by
  let paid := packet.second.physical.first.paidSupport
  let root := secondSixthRootIdeal packet.R.primes packet.R.leftMultiplicity packet.R.rightMultiplicity
  let unit := unitFrequencyRadical (Arithmetic.context c) packet.R.primes packet.R.leftMultiplicity
    packet.R.rightMultiplicity (packet.R.frequency h.val.val)
  let nonunit := nonunitFrequencyRadical (Arithmetic.context c) packet.R.primes packet.R.leftMultiplicity
    packet.R.rightMultiplicity (packet.R.frequency h.val.val)
  have atoms : D.recipe.moving.SupportAtoms (ExteriorIdealEuler.mul paid root)
      unit nonunit D.recipe.remaining := by
    rw [moving_eq, remaining_eq]
    exact paidSecondSupportAtoms seed.phases hpacket
      (packet_leftMultiplicity_pos packet) (packet_rightMultiplicity_pos packet) pattern h
  exact sourceConditions_of_original_atoms D paid unit nonunit root atoms
    ((packet.nominal side).skeleton.nominalRow + 12 * p.loss)
    ((packet.nominal side).skeleton.nominalSupport + 4 * p.loss) hm hq
    (fun h _ => canonicalSource_rowWindow seed input support hpacket side a rectangle h)
    (paid_radical_window hpacket side h.val) allowed timeIndependent primeSupport

end Canonical

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.sourceConditions_of_exact_recipe
