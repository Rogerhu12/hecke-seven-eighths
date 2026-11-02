import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bSourceBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bActualMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bOldMaskBounds

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Applying the supported volume theorem to the actual exceptional columns

The orders, degree and scalar are selected on the fixed parent annulus
and the fixed theta catalogue.  Each exceptional row then selects its
original character in that catalogue.  All four quotient scales and
the whole centered subtraction are those of the literal source record.
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

namespace T3b

/-- Fixed analytic witnesses, obtained below from the actual annular
contour theorem. Their parameters contain no moving call or source. -/
structure SourceBounds (c : TargetContext K) (p : SourceParameters c)
    (frame : SourceFrame) where
  orders : Finset (ℕ × ℕ)
  zero_mem : (0, 0) ∈ orders
  degree : ℕ
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  estimate : ∀ (j : CharacterIndex c) (phi₁ phi₂ : SchwartzMap ℝ ℂ),
    tsupport phi₁ ⊆ profileWindow c frame →
    tsupport phi₂ ⊆ profileWindow c frame →
    ∀ amplitude : ℝ, 0 ≤ amplitude →
    orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) phi₁ ≤ amplitude →
    orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) phi₂ ≤ amplitude →
    (∀ {g h : (Arithmetic.data c).R} {slots : ℕ}
      (source : AllocatedExceptionalSource (V := EngineParameter) (σ := Arithmetic.embedding c)
        (CanonicalExceptionalVolume.coefficient (character c j)) phi₁ phi₂ g h slots),
      ‖source.ordinaryValue‖ ≤ coefficient * amplitude ^ 2 * source.rawMass ∧
      ‖source.value‖ ≤ coefficient * amplitude ^ 2 * source.rawMass) ∧
    (∀ base : ℝ, 1 ≤ base → ∀ {g h : (Arithmetic.data c).R} {slots : ℕ}
      (source : AllocatedExceptionalSource (V := EngineParameter) (σ := Arithmetic.embedding c)
        (CanonicalExceptionalVolume.coefficient (character c j)) phi₁ phi₂ g h slots),
      source.mask ≠ ⊥ → (Ideal.absNorm source.mask : ℝ) ≤ base ^ completeMaskExponentBound c p →
      ∀ lowerLength : ℝ, base ^ lowerLength ≤ source.lower →
      ‖source.value‖ ≤ coefficient * amplitude ^ 2 * base ^ p.loss *
        (1 + ‖source.time‖) ^ degree * source.rawMass * base ^ (-max lowerLength 0))

theorem sourceBounds_nonempty (c : TargetContext K) (p : SourceParameters c)
    (frame : SourceFrame) : Nonempty (SourceBounds c p frame) := by
  obtain ⟨orders, hzero, degree, coefficient, hcoefficient, hbound⟩ :=
    exists_source_bounds (V := EngineParameter) c
      (profileRange c frame).expanded.lower (profileRange c frame).expanded.upper
      (profileRange c frame).expanded.lower_pos
      (profileRange c frame).expanded.interval
      p.loss (completeMaskExponentBound c p) p.loss_pos
      (completeMaskExponentBound_nonneg (c := c) (p := p))
  exact ⟨⟨orders, hzero, degree, coefficient, hcoefficient, hbound⟩⟩

end T3b

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {frame : SourceFrame}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p) (hpacket : packet.Realizes)
variable (phases : OriginalPhaseData packet) (input : ProfileInput call)

def t3bColumnRawMass (side : Bool) (ξ : EngineParameter) (h : packet.R.live) : ℝ :=
  (packet.t3bOrdinaryExceptionalAt hpacket phases input side ξ h).source.rawMass

theorem t3bColumnRawMass_nonneg (side : Bool) (ξ : EngineParameter) (h : packet.R.live) :
    0 ≤ packet.t3bColumnRawMass hpacket phases input side ξ h :=
  (packet.t3bOrdinaryExceptionalAt hpacket phases input side ξ h).source.rawMass_nonneg

/-- The absolute alternative applies to the same complete source in
the centered case and to its actual ordinary value in the other case. -/
theorem t3b_column_absolute_bound (bounds : T3b.SourceBounds c p frame)
    (hframe : call.frame = frame) (side : Bool) (ξ : EngineParameter)
    (h : packet.R.live)
    (hcatalogue : ∃ index : T3b.CharacterIndex c,
      T3b.character c index = call.localizedData.plainBackground *
        packet.t3bOriginalCharacter phases h)
    (P : ℝ) (hP : 0 ≤ P)
    (hprofile : ∀ plain : Bool,
      bounds.orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (packet.t3bNormProfile hpacket input plain) ≤ P) :
    ‖packet.t3bColumnValue hpacket phases side ξ h‖ ≤
      bounds.coefficient * P ^ 2 * packet.t3bColumnRawMass hpacket phases input side ξ h := by
  obtain ⟨index, hindex⟩ := hcatalogue
  have hs (plain : Bool) : tsupport
      (packet.t3bPlainProfile hpacket phases input side plain ξ) ⊆ T3b.profileWindow c frame := by
    simpa only [hframe] using packet.t3bPlainProfile_support hpacket phases input side plain ξ
  have hp (plain : Bool) : bounds.orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      (packet.t3bPlainProfile hpacket phases input side plain ξ) ≤ P := by
    rw [packet.t3bPlainProfile_seminorm]
    exact hprofile plain
  have hb := (bounds.estimate index
    (packet.t3bPlainProfile hpacket phases input side false ξ)
    (packet.t3bPlainProfile hpacket phases input side true ξ)
    (hs false) (hs true) P hP (hp false) (hp true)).1
  rw [hindex] at hb
  cases hc : call.node.centered with
  | false =>
    rw [packet.t3bColumnValue_uncentered hpacket phases input hc]
    exact (hb (packet.t3bOrdinaryExceptionalAt hpacket phases input side ξ h).source).1
  | true =>
    rw [packet.t3bColumnValue_centered hpacket phases input hc]
    have he := (hb (packet.t3bExceptionalAt hpacket phases input hc side ξ h).source).2
    rwa [packet.t3b_rawMass_centered_eq_ordinary hpacket phases input hc] at he

/-- The positive part is taken only after the actual divisor loss in
the lower bound for the minimum of all four quotient scales. -/
theorem t3b_column_centered_bound (bounds : T3b.SourceBounds c p frame)
    (hframe : call.frame = frame) (hc : call.node.centered = true)
    (side : Bool) (ξ : EngineParameter) (h : packet.R.live)
    (hcatalogue : ∃ index : T3b.CharacterIndex c,
      T3b.character c index = call.localizedData.plainBackground *
        packet.t3bOriginalCharacter phases h)
    (hmask : (Ideal.absNorm (packet.t3bCompleteMask phases h) : ℝ) ≤
      call.base ^ T3b.completeMaskExponentBound c p)
    (P : ℝ) (hP : 0 ≤ P)
    (hprofile : ∀ plain : Bool,
      bounds.orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (packet.t3bNormProfile hpacket input plain) ≤ P)
    (lowerLength : ℝ)
    (hlower : call.base ^ lowerLength ≤ packet.t3bScaleLower hpacket phases side) :
    ‖packet.t3bColumnValue hpacket phases side ξ h‖ ≤
      bounds.coefficient * P ^ 2 * call.base ^ p.loss *
        (1 + ‖T3b.time (packet.t3bFourierSign side) (packet.t3bFourierMode side ξ)‖) ^
          bounds.degree * packet.t3bColumnRawMass hpacket phases input side ξ h *
            call.base ^ (-max lowerLength 0) := by
  obtain ⟨index, hindex⟩ := hcatalogue
  have hs (plain : Bool) : tsupport
      (packet.t3bPlainProfile hpacket phases input side plain ξ) ⊆ T3b.profileWindow c frame := by
    simpa only [hframe] using packet.t3bPlainProfile_support hpacket phases input side plain ξ
  have hp (plain : Bool) : bounds.orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      (packet.t3bPlainProfile hpacket phases input side plain ξ) ≤ P := by
    rw [packet.t3bPlainProfile_seminorm]
    exact hprofile plain
  have hb := (bounds.estimate index
    (packet.t3bPlainProfile hpacket phases input side false ξ)
    (packet.t3bPlainProfile hpacket phases input side true ξ)
    (hs false) (hs true) P hP (hp false) (hp true)).2
  rw [hindex] at hb
  have he := hb call.base call.domain.scale.le
    (packet.t3bExceptionalAt hpacket phases input hc side ξ h).source
    (packet.t3bCompleteMask_ne_zero phases h) hmask lowerLength hlower
  rw [packet.t3b_rawMass_centered_eq_ordinary hpacket phases input hc] at he
  rw [packet.t3bColumnValue_centered hpacket phases input hc]
  exact he

end RawLeafPacket

namespace RawFamily

variable (trace : SourceTrace call p) (htrace : trace.Realizes)
variable {geometry : GeometryFamily trace.second} (raw : RawFamily geometry)
variable (hgeometry : geometry.Realizes) (hraw : raw.Realizes)

/-- Actual character membership and the uniform original mask bound
are produced here; neither is an added hypothesis of T3b. -/
theorem t3b_column_centered_bound (bounds : T3b.SourceBounds c p frame)
    (j : Fin raw.count) (input : ProfileInput call) (hframe : call.frame = frame)
    (hc : call.node.centered = true) (side : Bool) (ξ : EngineParameter)
    (h : (raw.packet j).R.live) (hh : h ∈ (raw.packet j).exceptionalRows)
    (hthreshold : T3b.completeMaskCoefficient c call.frame ≤ call.base)
    (P : ℝ) (hP : 0 ≤ P)
    (hprofile : ∀ plain : Bool,
      bounds.orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        ((raw.packet j).t3bNormProfile
          (raw.packet_realizes trace htrace hgeometry hraw j) input plain) ≤ P)
    (lowerLength : ℝ)
    (hlower : call.base ^ lowerLength ≤
      (raw.packet j).t3bScaleLower (raw.packet_realizes trace htrace hgeometry hraw j)
        (OrdinaryPhaseFacts.ofRaw trace htrace raw j) side) :
    ‖(raw.packet j).t3bColumnValue (raw.packet_realizes trace htrace hgeometry hraw j)
        (OrdinaryPhaseFacts.ofRaw trace htrace raw j) side ξ h‖ ≤
      bounds.coefficient * P ^ 2 * call.base ^ p.loss *
        (1 + ‖T3b.time ((raw.packet j).t3bFourierSign side)
          ((raw.packet j).t3bFourierMode side ξ)‖) ^ bounds.degree *
        (raw.packet j).t3bColumnRawMass (raw.packet_realizes trace htrace hgeometry hraw j)
          (OrdinaryPhaseFacts.ofRaw trace htrace raw j) input side ξ h *
        call.base ^ (-max lowerLength 0) :=
  (raw.packet j).t3b_column_centered_bound
    (raw.packet_realizes trace htrace hgeometry hraw j)
    (OrdinaryPhaseFacts.ofRaw trace htrace raw j) input bounds hframe hc side ξ h
    (raw.t3b_exceptional_catalogue trace htrace j h hh)
    (raw.t3bCompleteMask_norm_uniform trace htrace hgeometry hraw j input h hthreshold)
    P hP hprofile lowerLength hlower

end RawFamily

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.sourceBounds_nonempty
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawFamily.t3b_column_centered_bound
