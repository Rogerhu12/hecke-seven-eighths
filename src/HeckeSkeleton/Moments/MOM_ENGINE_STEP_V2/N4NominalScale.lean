module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4ScaleProduct
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OriginalPhaseData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawContracts

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N4: the two frozen norms equal the original nominal degree loss

The realized S5 geometry identifies the first ideal, the actual pool
tag and the selected second common ideal. The original phase record
identifies the full pool power, including every valuation occurrence.
Their exact norm product is the power removed from the raw degree.
Only the original ideal identity is supplied to the numerical division;
no bound on the final child scale product is assumed.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p}

theorem nominal_first_eq (hpacket : packet.Realizes) (side : Bool) :
    (packet.nominal side).ideals.first.val =
      packet.second.physical.first.selected.val := by
  rcases hpacket with ⟨trace, geometry, raw, j, _, hgeometry, _, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).first side

theorem nominal_tag_eq (hpacket : packet.Realizes) (side : Bool) :
    (packet.nominal side).tag = packet.second.physical.first.tag := by
  rcases hpacket with ⟨trace, geometry, raw, j, _, hgeometry, _, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).tag side

theorem nominal_second_eq (hpacket : packet.Realizes) (side : Bool) :
    (packet.nominal side).ideals.second.val = packet.secondIdeal side := by
  rcases hpacket with ⟨trace, geometry, raw, j, _, hgeometry, _, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).second side

/-- The full pool valuation, not its paid moving exponent, determines
the norm extracted from the original plain and prime occurrences. -/
theorem poolPower_norm (phases : OriginalPhaseData packet) :
    (Ideal.absNorm packet.second.physical.first.poolPower.val : ℝ) =
      call.base ^ packet.second.physical.first.tag.removedLength call.base := by
  rcases phases with ⟨hfirst, pool, htag, hpower, hdeletion⟩
  cases pool with
  | none =>
      change packet.second.physical.first.poolPower =
        unitExterior (Arithmetic.data c) at hpower
      change packet.second.physical.first.tag = .direct ∨
        packet.second.physical.first.tag = .main at htag
      rcases htag with htag | htag <;>
        simp only [hpower, htag, unitExterior, OriginalNominalTag.removedLength,
          Ideal.absNorm_top, Nat.cast_one, Real.rpow_zero]
  | some value =>
      rcases value with ⟨e, q⟩
      change packet.second.physical.first.poolPower =
        powerIdeal q e.multiplicity at hpower
      change packet.second.physical.first.tag = .error e q.val at htag
      rw [hpower, htag]
      change (Ideal.absNorm (q.val.asIdeal ^ e.multiplicity) : ℝ) =
        call.base ^ ((e.multiplicity : ℝ) * idealLogLength call.base q.val.asIdeal)
      calc
        _ = (Ideal.absNorm q.val.asIdeal : ℝ) ^ e.multiplicity := by
          rw [map_pow, Nat.cast_pow]
        _ = (call.base ^ idealLogLength call.base q.val.asIdeal) ^ e.multiplicity :=
          congrArg (fun x : ℝ => x ^ e.multiplicity)
            (rpow_idealLogLength call.base call.domain.scale q.val.asIdeal q.val.ne_bot).symm
        _ = _ := by
          rw [mul_comm (e.multiplicity : ℝ), Real.rpow_mul call.base_pos.le,
            Real.rpow_natCast]

/-- The exact original ideal product pays c, w and the selected c₂. -/
theorem frozen_norm_product_eq (hpacket : packet.Realizes)
    (phases : OriginalPhaseData packet) (side : Bool)
    (hfirst : firstFrozenIdeal packet side =
      packet.second.physical.first.selected.val * packet.second.physical.first.poolPower.val) :
    (Ideal.absNorm (firstFrozenIdeal packet side) : ℝ) *
        (Ideal.absNorm (secondFrozenIdeal packet side) : ℝ) =
      call.base ^ ((packet.nominal side).skeleton.c +
        (packet.nominal side).skeleton.w + (packet.nominal side).skeleton.c₂) := by
  have hc : (Ideal.absNorm packet.second.physical.first.selected.val : ℝ) =
      call.base ^ (packet.nominal side).skeleton.c := by
    change _ = call.base ^ idealLogLength call.base (packet.nominal side).ideals.first.val
    rw [nominal_first_eq hpacket side]
    exact (rpow_idealLogLength call.base call.domain.scale _
      (nonZeroDivisors.coe_ne_zero packet.second.physical.first.selected)).symm
  have hw : (Ideal.absNorm packet.second.physical.first.poolPower.val : ℝ) =
      call.base ^ (packet.nominal side).skeleton.w := by
    change _ = call.base ^ (packet.nominal side).tag.removedLength call.base
    rw [nominal_tag_eq hpacket side]
    exact poolPower_norm phases
  have hc₂ : (Ideal.absNorm (secondFrozenIdeal packet side) : ℝ) =
      call.base ^ (packet.nominal side).skeleton.c₂ := by
    rw [secondFrozenIdeal_eq, ← nominal_second_eq hpacket side]
    exact (rpow_idealLogLength call.base call.domain.scale _
      (nonZeroDivisors.coe_ne_zero (packet.nominal side).ideals.second)).symm
  rw [hfirst, map_mul, Nat.cast_mul, hc, hw, hc₂,
    ← Real.rpow_add call.base_pos, ← Real.rpow_add call.base_pos]

/-- Dividing the compensated original scale bound by its positive
exact frozen norm leaves precisely the nominal raw degree and loss. -/
theorem rawScaleProduct_le_of_compensated (hpacket : packet.Realizes)
    (phases : OriginalPhaseData packet) (side : Bool)
    (hfirst : firstFrozenIdeal packet side =
      packet.second.physical.first.selected.val * packet.second.physical.first.poolPower.val)
    {product annulus : ℝ}
    (hproduct : product * ((Ideal.absNorm (firstFrozenIdeal packet side) : ℝ) *
        (Ideal.absNorm (secondFrozenIdeal packet side) : ℝ)) ≤
      annulus ^ (2 * c.geometry.slots) *
        call.base ^ (call.node.parameters.n₁ + call.node.parameters.n₂ +
          call.node.parameters.z))
    (hannulus : annulus ^ (2 * c.geometry.slots) ≤ call.base ^ p.loss) :
    product ≤ call.base ^ ((packet.nominal side).skeleton.rawDegree + p.loss) := by
  have hbound := hproduct.trans (mul_le_mul_of_nonneg_right hannulus
    (Real.rpow_nonneg call.base_pos.le _))
  rw [frozen_norm_product_eq hpacket phases side hfirst] at hbound
  have he : call.base ^ ((packet.nominal side).skeleton.rawDegree + p.loss) *
      call.base ^ ((packet.nominal side).skeleton.c +
        (packet.nominal side).skeleton.w + (packet.nominal side).skeleton.c₂) =
      call.base ^ p.loss * call.base ^ (call.node.parameters.n₁ +
        call.node.parameters.n₂ + call.node.parameters.z) := by
    rw [← Real.rpow_add call.base_pos, ← Real.rpow_add call.base_pos]
    apply congrArg (fun x : ℝ => call.base ^ x)
    change ((packet.nominal side).skeleton.A - (packet.nominal side).skeleton.c -
      (packet.nominal side).skeleton.w - (packet.nominal side).skeleton.c₂ + p.loss) +
      ((packet.nominal side).skeleton.c + (packet.nominal side).skeleton.w +
        (packet.nominal side).skeleton.c₂) = _
    have hA : (packet.nominal side).skeleton.A = call.node.parameters.n₁ +
        call.node.parameters.n₂ + call.node.parameters.z := rfl
    rw [hA]
    ring
  rw [← he] at hbound
  have hpositive : 0 < call.base ^ ((packet.nominal side).skeleton.c +
      (packet.nominal side).skeleton.w + (packet.nominal side).skeleton.c₂) :=
    Real.rpow_pos_of_pos call.base_pos _
  exact (mul_le_mul_iff_right₀ hpositive).mp (by simpa only [mul_comm] using hbound)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.nominal_first_eq
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.nominal_tag_eq
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.nominal_second_eq
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.poolPower_norm
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.frozen_norm_product_eq
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.rawScaleProduct_le_of_compensated
