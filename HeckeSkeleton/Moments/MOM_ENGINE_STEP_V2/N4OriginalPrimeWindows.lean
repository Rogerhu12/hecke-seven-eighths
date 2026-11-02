import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OriginalOccurrenceData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.EstimateData
import Lean.Elab.Command

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option autoImplicit false
set_option Elab.async false
set_option stderrAsMessages false

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N4OriginalPrimeWindows checkpoint: imports/options"
    stderr.flush

/-!
# N4: both actual frozen prime lists retain the original support window

The first branch has an original Cartesian witness. The second branch
has a witness in the first retained Cartesian support, whose exact slot
dictionary is part of the original cover realization. Transporting those
indices recovers the same original prime profile, including repeated
occurrences. No bound on a completed scale product is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N4OriginalPrimeWindows checkpoint: before original_slot_norm_le"
    stderr.flush

/-- The actual finite prime carrier lies in the original profile annulus. -/
theorem original_slot_norm_le (input : ProfileInput call)
    (i : Fin call.localizedData.geometry.slotCount)
    (q : HeightOneSpectrum (𝓞 K))
    (hq : q ∈ call.workingRaw.exteriorSlots i) :
    (Ideal.absNorm q.asIdeal : ℝ) ≤
      max 1 (2 * call.prepared.upper) * call.base ^ call.originalLength i := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N4OriginalPrimeWindows checkpoint: original_slot_norm_le proof entered"
    stderr.flush
  have hp : q ∈ (call.localizedData.geometry.slots i).support 0
      (call.base ^ call.originalLength i) := (Finset.mem_filter.mp hq).1
  have hprofile := ((call.localizedData.geometry.slots i).support_spec 0
    (call.base ^ call.originalLength i) q).mp hp
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N4OriginalPrimeWindows checkpoint: original_slot_norm_le after profile"
    stderr.flush
  have hrep : input.localized.primeRep i 0
      ((Ideal.absNorm q.asIdeal : ℝ) / call.base ^ call.originalLength i) ≠ 0 := by
    simpa only [input.localized.prime_eq] using hprofile
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N4OriginalPrimeWindows checkpoint: original_slot_norm_le after representative"
    stderr.flush
  have hupper : (Ideal.absNorm q.asIdeal : ℝ) / call.base ^ call.originalLength i ≤
      2 * call.prepared.upper :=
    (input.localized.prime_support i 0 (Set.mem_univ 0) hrep).2
  have hpow : 0 < call.base ^ call.originalLength i :=
    Real.rpow_pos_of_pos (zero_lt_one.trans call.domain.scale) _
  exact ((div_le_iff₀ hpow).mp hupper).trans
    (mul_le_mul_of_nonneg_right (le_max_right 1 (2 * call.prepared.upper)) hpow.le)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N4OriginalPrimeWindows checkpoint: after original_slot_norm_le / before first_frozen_prime_norm_le"
    stderr.flush

theorem first_frozen_prime_norm_le (input : ProfileInput call)
    (packet : RawLeafPacket call p) (side : Bool)
    (i : Fin call.localizedData.geometry.slotCount) :
    (Ideal.absNorm ((packet.firstBranch side).witness.2 i).asIdeal : ℝ) ≤
      max 1 (2 * call.prepared.upper) * call.base ^ call.originalLength i :=
  original_slot_norm_le input i ((packet.firstBranch side).witness.2 i)
    (Finset.mem_filter.mp ((packet.firstBranch side).witness_slots i)).1

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N4OriginalPrimeWindows checkpoint: after first_frozen_prime_norm_le / before slots_apply_eq"
    stderr.flush

private theorem slots_apply_eq {α : Type} {m n : ℕ} (h : m = n)
    (f : Fin m → Finset α) (g : Fin n → Finset α) (hfg : HEq f g)
    (i : Fin n) : g i = f (Fin.cast h.symm i) := by
  cases h
  rw [eq_of_heq hfg]
  rfl

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N4OriginalPrimeWindows checkpoint: after slots_apply_eq / before originalCover_slot_mem"
    stderr.flush

/-- Cover realization records the original retained slot dictionary. -/
theorem originalCover_slot_mem {source : PhysicalSource call p}
    (cover : OriginalCover source) (hcover : cover.Realizes) (a : cover.cover.labels)
    (i : Fin (cover.cover.branch a).slotCount) (q : HeightOneSpectrum (𝓞 K))
    (hq : q ∈ (cover.cover.branch a).reindex.slots i) :
    q ∈ call.workingRaw.exteriorSlots
      (SlotRestriction.index (cover.first a).keep (Fin.cast (hcover.count a).symm i)) := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N4OriginalPrimeWindows checkpoint: originalCover_slot_mem proof entered"
    stderr.flush
  have he := slots_apply_eq (hcover.count a)
    (fun j : Fin (cover.first a).keep.card =>
      SupportCartesian.primeLive
        (call.workingRaw.exteriorSlots (SlotRestriction.index (cover.first a).keep j))
        source.first.fullDeletion)
    (cover.cover.branch a).reindex.slots (hcover.slots a).symm i
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N4OriginalPrimeWindows checkpoint: originalCover_slot_mem after slots equality"
    stderr.flush
  rw [he] at hq
  exact (Finset.mem_filter.mp hq).1

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N4OriginalPrimeWindows checkpoint: after originalCover_slot_mem / before firstAtlas_slot_mem"
    stderr.flush

private theorem firstAtlas_slot_mem_of_count {packet : RawLeafPacket call p}
    (hpacket : packet.Realizes) (side : Bool)
    (hcount : (packet.firstBranch side).keep.card = (packet.firstAtlas side).slotCount)
    (i : Fin (packet.firstAtlas side).slotCount) (q : HeightOneSpectrum (𝓞 K))
    (hq : q ∈ (packet.firstAtlas side).reindex.slots i) :
    q ∈ call.workingRaw.exteriorSlots
      (SlotRestriction.index (packet.firstBranch side).keep (Fin.cast hcount.symm i)) := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N4OriginalPrimeWindows checkpoint: firstAtlas_slot_mem_of_count proof entered"
    stderr.flush
  rcases hpacket with ⟨trace, geometry, raw, j, _, _, hraw, rfl⟩
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N4OriginalPrimeWindows checkpoint: firstAtlas_slot_mem_of_count after packet substitution"
    stderr.flush
  cases side
  · run_tac do
      let stderr ← IO.getStderr
      stderr.putStrLn "MOM_ENGINE_STEP_V2 N4OriginalPrimeWindows checkpoint: firstAtlas_slot_mem_of_count left branch"
      stderr.flush
      Lean.Elab.Tactic.evalTactic
        (← `(tactic| exact originalCover_slot_mem (raw.covers.left (raw.index j).val.1.1)
          (hraw (raw.index j).val.1.1).1 (raw.index j).val.1.2.2.2.1 i q hq))
      stderr.putStrLn "MOM_ENGINE_STEP_V2 N4OriginalPrimeWindows checkpoint: firstAtlas_slot_mem_of_count left proof complete"
      stderr.flush
  · run_tac do
      let stderr ← IO.getStderr
      stderr.putStrLn "MOM_ENGINE_STEP_V2 N4OriginalPrimeWindows checkpoint: firstAtlas_slot_mem_of_count right branch"
      stderr.flush
      Lean.Elab.Tactic.evalTactic
        (← `(tactic| exact originalCover_slot_mem (raw.covers.right (raw.index j).val.1.1)
          (hraw (raw.index j).val.1.1).2 (raw.index j).val.1.2.2.2.2.1 i q hq))
      stderr.putStrLn "MOM_ENGINE_STEP_V2 N4OriginalPrimeWindows checkpoint: firstAtlas_slot_mem_of_count right proof complete"
      stderr.flush

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N4OriginalPrimeWindows checkpoint: after firstAtlas_slot_mem_of_count"
    stderr.flush

theorem firstAtlas_slot_mem {packet : RawLeafPacket call p}
    (hpacket : packet.Realizes) {O : OrdinaryData packet}
    (D : OriginalOccurrenceData O) (side : Bool)
    (i : Fin (packet.firstAtlas side).slotCount) (q : HeightOneSpectrum (𝓞 K))
    (hq : q ∈ (packet.firstAtlas side).reindex.slots i) :
    q ∈ call.workingRaw.exteriorSlots (D.firstIndex side i) := by
  exact firstAtlas_slot_mem_of_count hpacket side (D.first_count side) i q hq

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N4OriginalPrimeWindows checkpoint: after firstAtlas_slot_mem / before second_frozen_prime_norm_le"
    stderr.flush

theorem second_frozen_prime_norm_le (input : ProfileInput call)
    {packet : RawLeafPacket call p} (hpacket : packet.Realizes)
    {O : OrdinaryData packet} (D : OriginalOccurrenceData O) (side : Bool)
    (i : Fin (packet.firstAtlas side).slotCount) :
    (Ideal.absNorm ((packet.secondBranch side).witness.2 i).asIdeal : ℝ) ≤
      max 1 (2 * call.prepared.upper) * call.base ^ call.originalLength (D.firstIndex side i) :=
  original_slot_norm_le input (D.firstIndex side i) ((packet.secondBranch side).witness.2 i)
    (firstAtlas_slot_mem hpacket D side i ((packet.secondBranch side).witness.2 i)
      (Finset.mem_filter.mp ((packet.secondBranch side).witness_slots i)).1)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 N4OriginalPrimeWindows checkpoint: after second_frozen_prime_norm_le"
    stderr.flush

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.original_slot_norm_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.first_frozen_prime_norm_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.originalCover_slot_mem
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.firstAtlas_slot_mem
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.second_frozen_prime_norm_le
