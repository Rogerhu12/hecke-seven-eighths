import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveCanonicalSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationFourierProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveScalar

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original single weights in the canonical residual source

The actual reference row identifies the parent norm profiles globally.
After the old plain divisors have been extracted, their quotient norm
arguments agree with the fixed canonical formulas. The two plain
locations differ only by their common divisor translation.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p}

namespace OrdinarySeed

variable (seed : OrdinarySeed packet) (input : ProfileInput call)

theorem plainProfile_original (side rectangle plain : Bool) (x : ℝ) :
    (seed.plainProfile input side rectangle plain).formula.original x =
      if plain then call.localizedNormProfiles.right PUnit.unit 0 x
      else call.localizedNormProfiles.left PUnit.unit 0 x := by
  cases plain
  · calc
      _ = call.node.data.plainTest₁.profile seed.reference 0 x :=
        (seed.plainProfile input side rectangle false).left_original rfl x
      _ = _ := call.normProfiles.left_paired PUnit.unit call.node.parameters call.base
        seed.reference seed.reference_mem 0 x
  · calc
      _ = call.node.data.plainTest₂.profile seed.reference 0 x :=
        (seed.plainProfile input side rectangle true).right_original rfl x
      _ = _ := call.normProfiles.right_paired PUnit.unit call.node.parameters call.base
        seed.reference seed.reference_mem 0 x

theorem plainProfile_zero (side rectangle plain : Bool) (x : ℝ) (hx : 0 < x) :
    (seed.plainProfile input side rectangle plain).formula.value 0 x =
      if rectangle && !call.node.centered && !plain then 0
      else seed.occurrences.plainProfile plain x := by
  rw [ProfileFormula.value_zero]
  change (if 0 < x then
    (if rectangle && !call.node.centered && !plain then (0 : ℂ) else 1) *
      (seed.plainProfile input side rectangle plain).formula.original (1 * x) *
        (x ^ seed.occurrences.normPower : ℝ) else 0) = _
  rw [if_pos hx, one_mul, seed.plainProfile_original input side rectangle plain]
  split <;> simp_all [OriginalOccurrenceData.plainProfile]

/-- The actual old plain divisor is evaluated before the new quotient
argument. No quotient by the possibly zero common scalar occurs. -/
theorem beforePlainWeight_quotient (side rectangle plain : Bool) (I : NonzeroIdeal K) :
    seed.occurrences.beforePlainWeight side rectangle plain
        ((seed.ordinary.originalAllocation side).plainDivisor
          (if plain then Fin.succ 0 else 0) * I) =
      (seed.plainProfile input side rectangle plain).formula.value 0
        (idealNorm K I / seed.occurrences.plainScale side rectangle plain) := by
  rw [seed.plainProfile_zero input side rectangle plain _
    (div_pos (idealNorm_pos K I) (seed.occurrences.plainScale_pos side rectangle plain))]
  unfold OriginalOccurrenceData.beforePlainWeight OriginalOccurrenceData.plainScale
  rw [ProfileFormula.divided_scale_argument]

theorem primeProfile_zero (side : Bool) (i : Fin (seed.ordinary.residualSlotCount side))
    (x : ℝ) (hx : 0 < x) :
    (seed.primeProfile input side i).formula.value 0 x =
      (call.node.data.geometry.slots (seed.slotIndex side i)).profile 0 x *
        (x ^ seed.occurrences.normPower : ℝ) := by
  rw [ProfileFormula.value_zero]
  change (if 0 < x then
    (1 : ℂ) * (input.raw.primeRep (seed.slotIndex side i) 0) (1 * x) *
      (x ^ seed.occurrences.normPower : ℝ) else 0) = _
  simp only [if_pos hx, one_mul]
  rw [← input.raw.prime_eq]

theorem beforeSlotWeight_remaining (side : Bool)
    (i : Fin (seed.ordinary.residualSlotCount side)) (q : HeightOneSpectrum (𝓞 K)) :
    seed.occurrences.beforeSlotWeight side
      (SlotRestriction.index (seed.ordinary.originalAllocation side).keep
        (Fin.cast (seed.residual_count side).symm i)) q =
      (seed.primeProfile input side i).formula.value 0
        ((Ideal.absNorm q.asIdeal : ℝ) /
          call.base ^ (call.node.data.geometry.slots (seed.slotIndex side i)).length) := by
  have hq : 0 < (Ideal.absNorm q.asIdeal : ℝ) :=
    idealNorm_pos K (CanonicalOriginalPhaseCalibration.primeIdeal q)
  rw [seed.primeProfile_zero input side i _
    (div_pos hq (Real.rpow_pos_of_pos call.base_pos _))]
  rfl

theorem literalLocation (side : Bool) (x : ℝ) :
    (if side then
      -(-Real.log x • CanonicalLiteralLocations.direction (-packet.firstSign))
     else -Real.log x • CanonicalLiteralLocations.direction packet.firstSign) =
      seed.location side x := by
  cases side
  · change WithLp.toLp 2 (-Real.log x * packet.firstSign, -Real.log x * 1) =
      WithLp.toLp 2 (-packet.firstSign * Real.log x, -1 * Real.log x)
    congr 1
    apply Prod.ext <;> dsimp <;> ring
  · change WithLp.toLp 2 (-(-Real.log x * -packet.firstSign), -(-Real.log x * 1)) =
      WithLp.toLp 2 (-packet.firstSign * Real.log x, 1 * Real.log x)
    congr 1
    apply Prod.ext <;> dsimp <;> ring

theorem original_leftLocation (side rectangle : Bool)
    (h : seed.ordinary.rows.live) (I : NonzeroIdeal K) :
    (seed.ordinary.originalSource side rectangle).leftLocation h I =
      seed.location side (idealNorm K I) := by
  rw [seed.atoms.leftLocation]
  exact seed.literalLocation side (idealNorm K I)

theorem original_rightLocation (side rectangle : Bool)
    (h : seed.ordinary.rows.live) (I : NonzeroIdeal K) :
    (seed.ordinary.originalSource side rectangle).rightLocation h I =
      seed.location side (idealNorm K I) := by
  rw [seed.atoms.rightLocation]
  exact seed.literalLocation side (idealNorm K I)

theorem original_slotLocation (side rectangle : Bool)
    (h : seed.ordinary.rows.live) (i : Fin (seed.ordinary.originalSlotCount side))
    (q : HeightOneSpectrum (𝓞 K)) :
    (seed.ordinary.originalSource side rectangle).slotLocation h i q =
      seed.location side (Ideal.absNorm q.asIdeal : ℝ) := by
  rw [seed.atoms.slotLocation]
  exact seed.literalLocation side (Ideal.absNorm q.asIdeal : ℝ)

theorem location_mul (side : Bool) (B I : NonzeroIdeal K) :
    seed.location side (idealNorm K (B * I)) =
      seed.location side (idealNorm K B) + seed.location side (idealNorm K I) := by
  unfold location
  rw [ProfileFormula.norm_mul, Real.log_mul (idealNorm_pos K B).ne' (idealNorm_pos K I).ne']
  change WithLp.toLp 2
    ((seed.logDirection side).1 * (Real.log (idealNorm K B) + Real.log (idealNorm K I)),
      (seed.logDirection side).2 * (Real.log (idealNorm K B) + Real.log (idealNorm K I))) =
    WithLp.toLp 2
      ((seed.logDirection side).1 * Real.log (idealNorm K B) +
          (seed.logDirection side).1 * Real.log (idealNorm K I),
        (seed.logDirection side).2 * Real.log (idealNorm K B) +
          (seed.logDirection side).2 * Real.log (idealNorm K I))
  congr 1
  apply Prod.ext <;> dsimp <;> ring

/-- The unscaled source uses the original formula in its first factor.
Its arithmetic extraction and both allocation scalars remain fixed. -/
def unscaledOriginal (side rectangle : Bool) :=
  PassiveSource.withLeftWeight (seed.ordinary.originalSource side rectangle)
    (fun _ => seed.occurrences.beforePlainWeight side rectangle false)

theorem original_energy (side rectangle : Bool) (ξ : EngineParameter) :
    (seed.ordinary.originalSource side rectangle).energy (σ := Arithmetic.embedding c) ξ =
      ‖seed.occurrences.normalizer seed.phases side‖ ^ 2 *
        (seed.unscaledOriginal side rectangle).energy (σ := Arithmetic.embedding c) ξ :=
  PassiveSource.energy_of_leftWeight_eq _ _ _ (seed.atoms.leftWeight side rectangle) ξ

end OrdinarySeed
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.beforePlainWeight_quotient
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.beforeSlotWeight_remaining
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.original_energy
