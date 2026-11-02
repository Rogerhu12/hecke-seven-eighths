import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bPairedAssembly
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bTimeBounds

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual exceptional integrand has the paid paired-row bound

The finite source sum is exactly the original whole-polynomial sum.
The original theta classification supplies each row's analytic
character and the actual sixth-base partition supplies its count.
The same two inner frozen ideals pay the two-divisor ledger in both
the centered and the ordinary branch, including all pool tags.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {frame : SourceFrame}

namespace T3b

def pairCoefficient (bounds : SourceBounds c p frame) (P : ℝ) : ℝ :=
  rowCountConstant c * bounds.coefficient ^ 2 * P ^ 4 *
    (atomRadius K (profileAnnulus c frame) P) ^ (6 * c.geometry.slots)

def pointCoefficient (bounds : SourceBounds c p frame) (P : ℝ) : ℝ :=
  pairCoefficient bounds P * (1 + 2 * Real.pi) ^ bounds.degree

theorem pairCoefficient_nonneg (bounds : SourceBounds c p frame) (P : ℝ) (hP : 1 ≤ P) :
    0 ≤ pairCoefficient bounds P :=
  mul_nonneg
    (mul_nonneg (mul_nonneg (rowCountConstant_nonneg c) (sq_nonneg _)) (pow_nonneg (by linarith) _))
    (pow_nonneg (zero_le_one.trans (atomRadius_one (K := K)
      (profileAnnulus_one_le c frame) hP)) _)

theorem pointCoefficient_nonneg (bounds : SourceBounds c p frame) (P : ℝ) (hP : 1 ≤ P) :
    0 ≤ pointCoefficient bounds P :=
  mul_nonneg (pairCoefficient_nonneg bounds P hP) (pow_nonneg (by positivity) _)

end T3b

namespace RawLeafPacket

variable (packet : RawLeafPacket call p) (hpacket : packet.Realizes)
variable (phases : OriginalPhaseData packet) (input : ProfileInput call)

theorem t3b_selected_column_bound (bounds : T3b.SourceBounds c p frame)
    (hframe : call.frame = frame) (side : Bool) (ξ : EngineParameter) (h : packet.R.live)
    (hcatalogue : ∃ index : T3b.CharacterIndex c,
      T3b.character c index = call.localizedData.plainBackground *
        packet.t3bOriginalCharacter phases h)
    (hmask : (Ideal.absNorm (packet.t3bCompleteMask phases h) : ℝ) ≤
      call.base ^ T3b.completeMaskExponentBound c p)
    (P : ℝ) (hP : 1 ≤ P)
    (hprofile : ∀ plain : Bool,
      bounds.orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (packet.t3bNormProfile hpacket input plain) ≤ P) :
    ‖packet.t3bColumnValue hpacket phases side ξ h‖ ≤
      bounds.coefficient * P ^ 2 * call.base ^ p.loss *
        (1 + ‖T3b.time (packet.t3bFourierSign side) (packet.t3bFourierMode side ξ)‖) ^
          bounds.degree * packet.t3bColumnRawMass hpacket phases input side ξ h *
            call.base ^ (-packet.t3bAnalyticSaving hpacket phases side) := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  cases hc : call.node.centered with
  | true =>
    simpa only [t3bAnalyticSaving, hc, if_true] using
      packet.t3b_column_centered_bound hpacket phases input bounds hframe hc side ξ h
        hcatalogue hmask P hP0 hprofile
        ((call.node.parameters.m + call.node.parameters.q) / 4 -
          packet.t3bScaleLoss side - packet.t3bInnerLoss hpacket phases side)
        (packet.t3bScaleLower_centered_lower hpacket phases hc side)
  | false =>
    have hb := packet.t3b_column_absolute_bound hpacket phases input bounds hframe
      side ξ h hcatalogue P hP0 hprofile
    have hC : 0 ≤ bounds.coefficient * P ^ 2 :=
      mul_nonneg bounds.coefficient_pos.le (sq_nonneg _)
    have hZ : 1 ≤ call.base ^ p.loss := Real.one_le_rpow call.domain.scale.le p.loss_pos.le
    have hH : 1 ≤
        (1 + ‖T3b.time (packet.t3bFourierSign side) (packet.t3bFourierMode side ξ)‖) ^
          bounds.degree := one_le_pow₀ (by positivity)
    have hscale : bounds.coefficient * P ^ 2 ≤ bounds.coefficient * P ^ 2 *
        call.base ^ p.loss *
          (1 + ‖T3b.time (packet.t3bFourierSign side) (packet.t3bFourierMode side ξ)‖) ^
            bounds.degree :=
      (le_mul_of_one_le_right hC hZ).trans
        (le_mul_of_one_le_right (mul_nonneg hC (Real.rpow_nonneg call.base_pos.le _)) hH)
    simpa only [t3bAnalyticSaving, hc, Bool.false_eq_true, if_false, neg_zero,
      Real.rpow_zero, mul_one] using hb.trans (mul_le_mul_of_nonneg_right hscale
        (packet.t3bColumnRawMass_nonneg hpacket phases input side ξ h))

/-- A single uniform analytic bound is applied row by row. Its
catalogue is never counted a second time in the actual row sum. -/
theorem t3b_source_sum_bound (bounds : T3b.SourceBounds c p frame)
    (hframe : call.frame = frame) (recovery : packet.ExceptionalRecovery)
    (hcatalogue : ∀ h ∈ packet.exceptionalRows, ∃ index : T3b.CharacterIndex c,
      T3b.character c index = call.localizedData.plainBackground *
        packet.t3bOriginalCharacter phases h)
    (hmask : ∀ h ∈ packet.exceptionalRows,
      (Ideal.absNorm (packet.t3bCompleteMask phases h) : ℝ) ≤
        call.base ^ T3b.completeMaskExponentBound c p)
    (P : ℝ) (hP : 1 ≤ P)
    (hprofile : ∀ plain : Bool,
      bounds.orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (packet.t3bNormProfile hpacket input plain) ≤ P)
    (hprime : ∀ (i : Fin call.localizedData.geometry.slotCount) (x : ℝ),
      ‖call.t3bPrimeNormProfile p input i x‖ ≤ P)
    (side : Bool)
    (hside : packet.t3bScaleLoss side ≤ (packet.nominal side).skeleton.c +
      (packet.nominal side).skeleton.w + (packet.nominal side).halfSecond)
    (z : ℝ × ℝ) :
    call.base ^ (-packet.t3bNominalNorm side) *
      (∑ h ∈ packet.exceptionalRows,
        ‖packet.t3bColumnValue hpacket phases side (WithLp.toLp 2 z) h‖ *
          ‖packet.t3bColumnValue hpacket phases (!side) (WithLp.toLp 2 z) h‖) ≤
      packet.t3bRawNormalizer hpacket side * T3b.pointCoefficient bounds P *
        ((1 + ‖z.1‖) ^ bounds.degree * (1 + ‖z.2‖) ^ bounds.degree) *
          call.base ^ (T3b.pointExponent call p - idealLogLength call.base packet.allocation.1.val) := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hB : 0 ≤ T3b.atomRadius K (T3b.profileAnnulus c call.frame) P :=
    zero_le_one.trans (T3b.atomRadius_one (K := K) (T3b.profileAnnulus_one_le c call.frame) hP)
  have hnormal := packet.t3bRawNormalizer_nonneg hpacket side
  have hpair := T3b.pairCoefficient_nonneg bounds P hP
  have hpoint := T3b.pointCoefficient_nonneg bounds P hP
  by_cases hne : packet.exceptionalRows.Nonempty
  · obtain ⟨h₀, hh₀⟩ := hne
    let ξ : EngineParameter := WithLp.toLp 2 z
    let H := (1 + ‖T3b.time (packet.t3bFourierSign side)
      (packet.t3bFourierMode side ξ)‖) ^ bounds.degree
    let CL := bounds.coefficient * P ^ 2 * call.base ^ p.loss * H *
      call.base ^ (-packet.t3bAnalyticSaving hpacket phases side)
    let CR := bounds.coefficient * P ^ 2
    let M := (T3b.atomRadius K (T3b.profileAnnulus c call.frame) P) ^ (6 * c.geometry.slots) *
      packet.t3bRawNormalizer hpacket side *
        call.base ^ (packet.t3bRawExponent side - packet.t3bInnerLoss hpacket phases side -
          packet.t3bInnerLoss hpacket phases (!side))
    let N := T3b.rowCountConstant c * call.base ^ packet.t3bRowExponent side h₀
    have hH : 0 ≤ H := by dsimp only [H]; positivity
    have hCL : 0 ≤ CL := by
      dsimp only [CL]
      exact mul_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg bounds.coefficient_pos.le (sq_nonneg _))
        (Real.rpow_nonneg call.base_pos.le _)) hH) (Real.rpow_nonneg call.base_pos.le _)
    have hCR : 0 ≤ CR := mul_nonneg bounds.coefficient_pos.le (sq_nonneg _)
    have hM : 0 ≤ M := mul_nonneg (mul_nonneg (pow_nonneg hB _) hnormal)
      (Real.rpow_nonneg call.base_pos.le _)
    have hleft (h) (hh : h ∈ packet.exceptionalRows) :
        ‖packet.t3bColumnValue hpacket phases side ξ h‖ ≤
          CL * packet.t3bColumnRawMass hpacket phases input side ξ h := by
      have he := packet.t3b_selected_column_bound hpacket phases input bounds hframe
        side ξ h (hcatalogue h hh) (hmask h hh) P hP hprofile
      convert he using 1 <;> dsimp only [CL, H] <;> ring
    have hright (h) (hh : h ∈ packet.exceptionalRows) :
        ‖packet.t3bColumnValue hpacket phases (!side) ξ h‖ ≤
          CR * packet.t3bColumnRawMass hpacket phases input (!side) ξ h :=
      packet.t3b_column_absolute_bound hpacket phases input bounds hframe (!side) ξ h
        (hcatalogue h hh) P hP0 hprofile
    have hsum := T3b.finite_pair_bound packet.exceptionalRows
      (packet.t3bColumnValue hpacket phases side ξ)
      (packet.t3bColumnValue hpacket phases (!side) ξ)
      (packet.t3bColumnRawMass hpacket phases input side ξ)
      (packet.t3bColumnRawMass hpacket phases input (!side) ξ)
      CL CR M N hCL hCR hM hleft hright
      (fun h _ => packet.t3bColumnRawMass_nonneg hpacket phases input side ξ h)
      (fun h _ => packet.t3b_rawMass_pair_le hpacket phases input P hP hprime side ξ h)
      (packet.t3b_exceptional_rows_count hpacket recovery side h₀)
    have hnormalized :
        call.base ^ (-packet.t3bNominalNorm side) *
          (∑ h ∈ packet.exceptionalRows,
            ‖packet.t3bColumnValue hpacket phases side ξ h‖ *
              ‖packet.t3bColumnValue hpacket phases (!side) ξ h‖) ≤
        packet.t3bRawNormalizer hpacket side * T3b.pairCoefficient bounds P * H *
          call.base ^ (T3b.pointExponent call p - idealLogLength call.base packet.allocation.1.val) := by
      calc
        _ ≤ call.base ^ (-packet.t3bNominalNorm side) * (N * (CL * CR * M)) :=
          mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg call.base_pos.le _)
        _ = packet.t3bRawNormalizer hpacket side * T3b.pairCoefficient bounds P * H *
            call.base ^ (-packet.t3bNominalNorm side + packet.t3bRowExponent side h₀ +
              (packet.t3bRawExponent side - packet.t3bInnerLoss hpacket phases side -
                packet.t3bInnerLoss hpacket phases (!side) + p.loss -
                  packet.t3bAnalyticSaving hpacket phases side)) := by
          dsimp only [N, CL, CR, M, T3b.pairCoefficient]
          simp only [hframe, Real.rpow_add call.base_pos, Real.rpow_sub call.base_pos,
            Real.rpow_neg call.base_pos.le, div_eq_mul_inv]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
            (packet.t3b_paired_exponent hpacket phases side h₀ hside))
          (mul_nonneg (mul_nonneg hnormal hpair) hH)
    have htime : H ≤ (1 + 2 * Real.pi) ^ bounds.degree *
        ((1 + ‖z.1‖) ^ bounds.degree * (1 + ‖z.2‖) ^ bounds.degree) := by
      simpa only [H, ξ, mul_assoc] using packet.t3b_time_power_le side z bounds.degree
    calc
      _ ≤ packet.t3bRawNormalizer hpacket side * T3b.pairCoefficient bounds P * H *
          call.base ^ (T3b.pointExponent call p - idealLogLength call.base packet.allocation.1.val) :=
        hnormalized
      _ ≤ packet.t3bRawNormalizer hpacket side * T3b.pairCoefficient bounds P *
          ((1 + 2 * Real.pi) ^ bounds.degree *
            ((1 + ‖z.1‖) ^ bounds.degree * (1 + ‖z.2‖) ^ bounds.degree)) *
          call.base ^ (T3b.pointExponent call p - idealLogLength call.base packet.allocation.1.val) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htime (mul_nonneg hnormal hpair))
          (Real.rpow_nonneg call.base_pos.le _)
      _ = _ := by unfold T3b.pointCoefficient; ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty, mul_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hnormal hpoint)
      (mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (by positivity) _)))
      (Real.rpow_nonneg call.base_pos.le _)

/-- The paid source-sum estimate is returned on the original leaf
integrand, with its actual common scalars and row amplitude intact. -/
theorem t3b_exceptional_pointwise (bounds : T3b.SourceBounds c p frame)
    (hframe : call.frame = frame) (recovery : packet.ExceptionalRecovery)
    (hcatalogue : ∀ h ∈ packet.exceptionalRows, ∃ index : T3b.CharacterIndex c,
      T3b.character c index = call.localizedData.plainBackground *
        packet.t3bOriginalCharacter phases h)
    (hmask : ∀ h ∈ packet.exceptionalRows,
      (Ideal.absNorm (packet.t3bCompleteMask phases h) : ℝ) ≤
        call.base ^ T3b.completeMaskExponentBound c p)
    (P : ℝ) (hP : 1 ≤ P)
    (hprofile : ∀ plain : Bool,
      bounds.orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (packet.t3bNormProfile hpacket input plain) ≤ P)
    (hprime : ∀ (i : Fin call.localizedData.geometry.slotCount) (x : ℝ),
      ‖call.t3bPrimeNormProfile p input i x‖ ≤ P) :
    ∃ side : Bool, ∀ z : ℝ × ℝ,
      call.base ^ (-packet.t3bNominalNorm side) * packet.leaf.exceptionalIntegrand z ≤
        packet.t3bPointScalar hpacket phases side * T3b.pointCoefficient bounds P *
          ((1 + ‖z.1‖) ^ bounds.degree * (1 + ‖z.2‖) ^ bounds.degree) *
            call.base ^ (T3b.pointExponent call p - idealLogLength call.base packet.allocation.1.val) := by
  obtain ⟨side, hside⟩ := packet.t3b_exists_small_second_side hpacket phases
  refine ⟨side, ?_⟩
  intro z
  let S := ‖packet.secondAtomScalar hpacket phases false‖ *
    ‖packet.secondAtomScalar hpacket phases true‖ * packet.t3bRowAmplitude *
      call.base ^ ((packet.nominal side).skeleton.g₂ - (packet.nominal side).skeleton.t₂)
  have hS : 0 ≤ S := mul_nonneg
    (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) packet.t3bRowAmplitude_nonneg)
    (Real.rpow_nonneg call.base_pos.le _)
  have hI := packet.t3b_exceptional_integrand_le_source_sum hpacket phases recovery side z
  have he : (∑ h ∈ packet.exceptionalRows,
      ‖packet.t3bColumnValue hpacket phases false (WithLp.toLp 2 z) h‖ *
        ‖packet.t3bColumnValue hpacket phases true (WithLp.toLp 2 z) h‖) =
    ∑ h ∈ packet.exceptionalRows,
      ‖packet.t3bColumnValue hpacket phases side (WithLp.toLp 2 z) h‖ *
        ‖packet.t3bColumnValue hpacket phases (!side) (WithLp.toLp 2 z) h‖ := by
    cases side with
    | false => rfl
    | true =>
      apply Finset.sum_congr rfl
      intro h _
      exact mul_comm _ _
  rw [he] at hI
  calc
    _ ≤ call.base ^ (-packet.t3bNominalNorm side) *
        (S * ∑ h ∈ packet.exceptionalRows,
          ‖packet.t3bColumnValue hpacket phases side (WithLp.toLp 2 z) h‖ *
            ‖packet.t3bColumnValue hpacket phases (!side) (WithLp.toLp 2 z) h‖) :=
      mul_le_mul_of_nonneg_left hI (Real.rpow_nonneg call.base_pos.le _)
    _ = S * (call.base ^ (-packet.t3bNominalNorm side) *
        (∑ h ∈ packet.exceptionalRows,
          ‖packet.t3bColumnValue hpacket phases side (WithLp.toLp 2 z) h‖ *
            ‖packet.t3bColumnValue hpacket phases (!side) (WithLp.toLp 2 z) h‖)) := by ring
    _ ≤ S * (packet.t3bRawNormalizer hpacket side * T3b.pointCoefficient bounds P *
        ((1 + ‖z.1‖) ^ bounds.degree * (1 + ‖z.2‖) ^ bounds.degree) *
          call.base ^ (T3b.pointExponent call p - idealLogLength call.base packet.allocation.1.val)) :=
      mul_le_mul_of_nonneg_left
        (packet.t3b_source_sum_bound hpacket phases input bounds hframe recovery hcatalogue hmask
          P hP hprofile hprime side hside z) hS
    _ = _ := by dsimp only [S, t3bPointScalar]; ring

end RawLeafPacket

namespace RawFamily

variable (trace : SourceTrace call p) (htrace : trace.Realizes)
variable {geometry : GeometryFamily trace.second} (raw : RawFamily geometry)
variable (hgeometry : geometry.Realizes) (hraw : raw.Realizes)

/-- This actual-raw wrapper consumes formal T3a, proves the original
catalogue membership and pays the fixed mask threshold itself. -/
theorem t3b_exceptional_pointwise (recovery : ExceptionalRecoveryTask c p)
    (bounds : T3b.SourceBounds c p frame) (j : Fin raw.count)
    (input : ProfileInput call) (hframe : call.frame = frame)
    (hthreshold : T3b.completeMaskCoefficient c call.frame ≤ call.base)
    (P : ℝ) (hP : 1 ≤ P)
    (hprofile : ∀ plain : Bool,
      bounds.orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        ((raw.packet j).t3bNormProfile
          (raw.packet_realizes trace htrace hgeometry hraw j) input plain) ≤ P)
    (hprime : ∀ (i : Fin call.localizedData.geometry.slotCount) (x : ℝ),
      ‖call.t3bPrimeNormProfile p input i x‖ ≤ P) :
    ∃ side : Bool, ∀ z : ℝ × ℝ,
      call.base ^ (-(raw.packet j).t3bNominalNorm side) *
          (raw.packet j).leaf.exceptionalIntegrand z ≤
        (raw.packet j).t3bPointScalar (raw.packet_realizes trace htrace hgeometry hraw j)
          (OrdinaryPhaseFacts.ofRaw trace htrace raw j) side * T3b.pointCoefficient bounds P *
          ((1 + ‖z.1‖) ^ bounds.degree * (1 + ‖z.2‖) ^ bounds.degree) *
            call.base ^ (T3b.pointExponent call p - idealLogLength call.base (raw.innerDivisor j)) := by
  let hpacket := raw.packet_realizes trace htrace hgeometry hraw j
  exact (raw.packet j).t3b_exceptional_pointwise hpacket
    (OrdinaryPhaseFacts.ofRaw trace htrace raw j) input bounds hframe
    (recovery call (raw.packet j) hpacket)
    (fun h hh => raw.t3b_exceptional_catalogue trace htrace j h hh)
    (fun h _ => raw.t3bCompleteMask_norm_uniform trace htrace hgeometry hraw j input h hthreshold)
    P hP hprofile hprime

end RawFamily

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawFamily.t3b_exceptional_pointwise
