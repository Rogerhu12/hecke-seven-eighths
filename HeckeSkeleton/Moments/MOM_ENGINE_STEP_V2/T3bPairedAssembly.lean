import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bPointwiseData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bVolumeApplication
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bRowCount
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bNumericalLedger

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The two actual raw masses and the exceptional exponent ledger

Both original inner frozen ideals remain in the denominator.  The
opposite one pays the independent inner divisor while the chosen side
retains the whole centered positive-part saving.  The row window pays
exactly `12 * loss`, and the first geometric error is `4 * loss`.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

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

namespace T3b

def pointExponent (call : Call c) (p : SourceParameters c) : ℝ :=
  max (call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z -
    (call.node.parameters.m + call.node.parameters.q)) 0 +
      3 * recipeInductionSigma c + (19 / 3) * p.loss

/-- A finite sum of the original paired norms, after both whole
column estimates. This elementary step never expands either column
into the absolute sum of its individual coefficients. -/
theorem finite_pair_bound {H : Type*} (rows : Finset H)
    (left right : H → ℂ) (massLeft massRight : H → ℝ)
    (CL CR M N : ℝ) (hCL : 0 ≤ CL) (hCR : 0 ≤ CR) (hM : 0 ≤ M)
    (hleft : ∀ h ∈ rows, ‖left h‖ ≤ CL * massLeft h)
    (hright : ∀ h ∈ rows, ‖right h‖ ≤ CR * massRight h)
    (hmassLeft : ∀ h ∈ rows, 0 ≤ massLeft h)
    (hmass : ∀ h ∈ rows, massLeft h * massRight h ≤ M)
    (hrows : (rows.card : ℝ) ≤ N) :
    (∑ h ∈ rows, ‖left h‖ * ‖right h‖) ≤ N * (CL * CR * M) := by
  have hpoint (h) (hh : h ∈ rows) :
      ‖left h‖ * ‖right h‖ ≤ CL * CR * M := by
    calc
      _ ≤ (CL * massLeft h) * (CR * massRight h) :=
        mul_le_mul (hleft h hh) (hright h hh) (norm_nonneg _)
          (mul_nonneg hCL (hmassLeft h hh))
      _ = CL * CR * (massLeft h * massRight h) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmass h hh) (mul_nonneg hCL hCR)
  calc
    _ ≤ (rows.card : ℝ) * (CL * CR * M) := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hpoint
    _ ≤ _ := mul_le_mul_of_nonneg_right hrows (mul_nonneg (mul_nonneg hCL hCR) hM)

end T3b

namespace RawLeafPacket

variable (packet : RawLeafPacket call p) (hpacket : packet.Realizes)
variable (phases : OriginalPhaseData packet)

/-- The full frozen ideal on each side, including removed prime
occurrences, occurs with its own exact norm logarithm. -/
theorem t3b_rawMass_pair_le (input : ProfileInput call) (P : ℝ) (hP : 1 ≤ P)
    (hprofiles : ∀ (i : Fin call.localizedData.geometry.slotCount) (x : ℝ),
      ‖call.t3bPrimeNormProfile p input i x‖ ≤ P)
    (side : Bool) (ξ : EngineParameter) (h : packet.R.live) :
    packet.t3bColumnRawMass hpacket phases input side ξ h *
        packet.t3bColumnRawMass hpacket phases input (!side) ξ h ≤
      (T3b.atomRadius K (T3b.profileAnnulus c call.frame) P) ^ (6 * c.geometry.slots) *
        packet.t3bRawNormalizer hpacket side *
          call.base ^ (packet.t3bRawExponent side - packet.t3bInnerLoss hpacket phases side -
            packet.t3bInnerLoss hpacket phases (!side)) := by
  have hl := packet.t3b_ordinary_rawMass_le hpacket phases input P hP hprofiles side ξ h
  have hr := packet.t3b_ordinary_rawMass_le hpacket phases input P hP hprofiles (!side) ξ h
  have hbound : 0 ≤
      (T3b.atomRadius K (T3b.profileAnnulus c call.frame) P) ^ (3 * c.geometry.slots) *
        Real.sqrt (packet.t3bBeforeScaleProduct hpacket side) /
        (Ideal.absNorm (packet.t3bInnerFrozenIdeal hpacket phases side) : ℝ) := by
    have hB : 0 ≤ T3b.atomRadius K (T3b.profileAnnulus c call.frame) P :=
      zero_le_one.trans (T3b.atomRadius_one (K := K)
        (T3b.profileAnnulus_one_le c call.frame) hP)
    exact div_nonneg (mul_nonneg (pow_nonneg hB _) (Real.sqrt_nonneg _)) (Nat.cast_nonneg _)
  calc
    _ ≤
        ((T3b.atomRadius K (T3b.profileAnnulus c call.frame) P) ^ (3 * c.geometry.slots) *
          Real.sqrt (packet.t3bBeforeScaleProduct hpacket side) /
          (Ideal.absNorm (packet.t3bInnerFrozenIdeal hpacket phases side) : ℝ)) *
        ((T3b.atomRadius K (T3b.profileAnnulus c call.frame) P) ^ (3 * c.geometry.slots) *
          Real.sqrt (packet.t3bBeforeScaleProduct hpacket (!side)) /
          (Ideal.absNorm (packet.t3bInnerFrozenIdeal hpacket phases (!side)) : ℝ)) :=
      mul_le_mul hl hr (packet.t3bColumnRawMass_nonneg hpacket phases input (!side) ξ h) hbound
    _ = _ := by
      have hn (s : Bool) : (Ideal.absNorm (packet.t3bInnerFrozenIdeal hpacket phases s) : ℝ) =
          call.base ^ packet.t3bInnerLoss hpacket phases s :=
        (rpow_idealLogLength call.base call.domain.scale _
          (packet.t3bInnerFrozenIdeal_ne_zero hpacket phases s)).symm
      rw [hn side, hn (!side), t3bRawNormalizer]
      simp only [Real.rpow_sub call.base_pos, Real.rpow_neg call.base_pos.le]
      have hE := (Real.rpow_pos call.base_pos (packet.t3bRawExponent side)).ne'
      have hL := (Real.rpow_pos call.base_pos (packet.t3bInnerLoss hpacket phases side)).ne'
      have hR := (Real.rpow_pos call.base_pos (packet.t3bInnerLoss hpacket phases (!side))).ne'
      rw [show 6 * c.geometry.slots = 3 * c.geometry.slots + 3 * c.geometry.slots by omega,
        pow_add]
      field_simp [hE, hL, hR]
      cases side <;> simp only [Bool.not_false, Bool.not_true] <;> ring

def t3bRowExponent (side : Bool) (h : packet.R.live) : ℝ :=
  ((packet.nominal side).skeleton.nominalRow + 12 * p.loss -
    2 * packet.t3bMultiplicityOneLength h) / 6

def t3bAnalyticSaving (side : Bool) : ℝ :=
  if call.node.centered then
    max ((call.node.parameters.m + call.node.parameters.q) / 4 -
      packet.t3bScaleLoss side - packet.t3bInnerLoss hpacket phases side) 0
  else 0

theorem t3b_excess_identity (side : Bool) (h : packet.R.live) :
    ((packet.nominal side).skeleton.nominalRow - 2 * packet.t3bMultiplicityOneLength h) / 6 +
        packet.t3bRawExponent side - packet.t3bNominalNorm side =
      (packet.nominal side).skeleton.A -
        5 * ((packet.nominal side).skeleton.m + (packet.nominal side).skeleton.q) / 6 -
          packet.t3bFirstSaving side - packet.t3bSecondSaving side h := by
  let G := packet.nominal side
  exact exceptional_excess_identity G.skeleton.A G.skeleton.m G.skeleton.q
    G.skeleton.c G.skeleton.d G.skeleton.R G.skeleton.E G.skeleton.Krow
    G.skeleton.w G.skeleton.wo G.boundary G.skeleton.g
    (G.tag.poolLength (recipeInductionSigma c)) G.halfSecond G.secondRadical
    G.skeleton.g₂ G.skeleton.t₂ G.skeleton.V (2 * packet.t3bMultiplicityOneLength h)

theorem t3b_centered_exponent (side : Bool) (h : packet.R.live)
    (hside : packet.t3bScaleLoss side ≤ (packet.nominal side).skeleton.c +
      (packet.nominal side).skeleton.w + (packet.nominal side).halfSecond) :
    -packet.t3bNominalNorm side + packet.t3bRowExponent side h +
      (packet.t3bRawExponent side - packet.t3bInnerLoss hpacket phases side -
        packet.t3bInnerLoss hpacket phases (!side) + p.loss -
          max ((call.node.parameters.m + call.node.parameters.q) / 4 -
            packet.t3bScaleLoss side - packet.t3bInnerLoss hpacket phases side) 0) ≤
      T3b.pointExponent call p - idealLogLength call.base packet.allocation.1.val := by
  let G := packet.nominal side
  have hid := packet.t3b_excess_identity side h
  have hledger := T3b.centered_divisor_exponent G.skeleton.A
    (G.skeleton.m + G.skeleton.q) G.skeleton.c G.skeleton.w G.halfSecond
    (packet.t3bScaleLoss side) (packet.t3bFirstSaving side) (packet.t3bSecondSaving side h)
    (recipeInductionSigma c) (4 * p.loss)
    (packet.t3bInnerLoss hpacket phases side) (packet.t3bInnerLoss hpacket phases (!side))
    (idealLogLength call.base packet.allocation.1.val) 0
    (packet.t3bInnerLoss_nonneg hpacket phases side)
    (packet.t3b_divisor_slotError_zero hpacket phases (!side))
    (packet.t3bFirstSaving_lower hpacket side) (packet.t3bSecondSaving_lower hpacket side h) hside
  change G.skeleton.A - 5 * (G.skeleton.m + G.skeleton.q) / 6 -
      packet.t3bFirstSaving side - packet.t3bSecondSaving side h -
      packet.t3bInnerLoss hpacket phases side - packet.t3bInnerLoss hpacket phases (!side) -
      max ((call.node.parameters.m + call.node.parameters.q) / 4 - packet.t3bScaleLoss side -
        packet.t3bInnerLoss hpacket phases side) 0 ≤
    max (call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z -
      (call.node.parameters.m + call.node.parameters.q)) 0 + 3 * recipeInductionSigma c +
      5 * (4 * p.loss) / 6 + 0 - idealLogLength call.base packet.allocation.1.val at hledger
  dsimp only [t3bRowExponent, T3b.pointExponent]
  linarith

theorem t3b_uncentered_exponent (hc : call.node.centered = false)
    (side : Bool) (h : packet.R.live) :
    -packet.t3bNominalNorm side + packet.t3bRowExponent side h +
      (packet.t3bRawExponent side - packet.t3bInnerLoss hpacket phases side -
        packet.t3bInnerLoss hpacket phases (!side) + p.loss) ≤
      T3b.pointExponent call p - idealLogLength call.base packet.allocation.1.val := by
  let G := packet.nominal side
  have hid := packet.t3b_excess_identity side h
  have hc0 : 0 ≤ G.skeleton.c := idealLogLength_nonneg call.base call.domain.scale _
    (nonZeroDivisors.coe_ne_zero _)
  have hw0 : 0 ≤ G.skeleton.w := G.tag.removedLength_nonneg call.base call.domain.scale
  have hb0 : 0 ≤ G.halfSecond := by
    apply div_nonneg (add_nonneg
      (idealLogLength_nonneg call.base call.domain.scale _ (nonZeroDivisors.coe_ne_zero _))
      (idealLogLength_nonneg call.base call.domain.scale _ (nonZeroDivisors.coe_ne_zero _)))
      (by norm_num)
  have hledger := T3b.absolute_divisor_exponent G.skeleton.A
    (G.skeleton.m + G.skeleton.q) G.skeleton.c G.skeleton.w G.halfSecond
    (packet.t3bFirstSaving side) (packet.t3bSecondSaving side h)
    (recipeInductionSigma c) (4 * p.loss)
    (packet.t3bInnerLoss hpacket phases side) (packet.t3bInnerLoss hpacket phases (!side))
    (idealLogLength call.base packet.allocation.1.val) 0
    (call.domain.ordinary hc) hc0 hw0 hb0
    (packet.t3bInnerLoss_nonneg hpacket phases side)
    (packet.t3b_divisor_slotError_zero hpacket phases (!side))
    (packet.t3bFirstSaving_lower hpacket side) (packet.t3bSecondSaving_lower hpacket side h)
  have hcore : 0 ≤ max (call.node.parameters.n₁ + call.node.parameters.n₂ +
      call.node.parameters.z - (call.node.parameters.m + call.node.parameters.q)) 0 := le_max_right _ _
  have hloss := p.loss_pos
  dsimp only [t3bRowExponent, T3b.pointExponent]
  linarith

theorem t3b_paired_exponent (side : Bool) (h : packet.R.live)
    (hside : packet.t3bScaleLoss side ≤ (packet.nominal side).skeleton.c +
      (packet.nominal side).skeleton.w + (packet.nominal side).halfSecond) :
    -packet.t3bNominalNorm side + packet.t3bRowExponent side h +
      (packet.t3bRawExponent side - packet.t3bInnerLoss hpacket phases side -
        packet.t3bInnerLoss hpacket phases (!side) + p.loss -
          packet.t3bAnalyticSaving hpacket phases side) ≤
      T3b.pointExponent call p - idealLogLength call.base packet.allocation.1.val := by
  cases hc : call.node.centered with
  | false =>
    simpa only [t3bAnalyticSaving, hc, Bool.false_eq_true, if_false, sub_zero] using
      packet.t3b_uncentered_exponent hpacket phases hc side h
  | true =>
    simpa only [t3bAnalyticSaving, hc, if_true] using
      packet.t3b_centered_exponent hpacket phases side h hside

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_rawMass_pair_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_centered_exponent
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_uncentered_exponent
