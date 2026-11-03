import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bScaleBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualSecondSaving
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCommonIndexSwap

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The two savings from the actual original geometry

The first saving uses the original retained-scale upper bound and the
actual pool prime's upper norm window. The second is the complete local
correlation saving, transported through the same S5 ideal coordinates.
The multiplicity-one radical is constant on the actual frequency class;
its exact logarithmic norm supplies the common row-count parameter.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

namespace T3b

theorem nominal_firstSaving_lower {a : RealParameters} {Z step : ℝ}
    (G : OriginalNominalGeometry (K := K) a Z step)
    (hZ : 1 < Z) (hstep : 0 ≤ step) (hq : 0 ≤ a.q)
    (hw : G.skeleton.w ≤ 7 * step / 3) :
    2 * (G.skeleton.c + G.skeleton.w) / 3 - 3 * step - 5 * G.supportError / 6 ≤
      firstSaving G.skeleton.c G.skeleton.shiftedCommon G.skeleton.w
        (G.skeleton.q + G.skeleton.R + G.skeleton.E) G.skeleton.wo
        G.boundary G.skeleton.g (G.tag.poolLength step) := by
  have hc : 0 ≤ G.skeleton.c :=
    idealLogLength_nonneg Z hZ _ (nonZeroDivisors.coe_ne_zero _)
  have hR : 0 ≤ G.skeleton.R :=
    idealLogLength_nonneg Z hZ _ (firstActiveRadical_ne_zero _ _)
  have hE : 0 ≤ G.skeleton.E :=
    idealLogLength_nonneg Z hZ _ (nonZeroDivisors.coe_ne_zero _)
  have hw0 : 0 ≤ G.skeleton.w := G.tag.removedLength_nonneg Z hZ
  have hwo : 0 ≤ G.skeleton.wo := by
    cases ht : G.tag with
    | direct =>
      simp only [OriginalNominalGeometry.skeleton, ht, OriginalNominalTag.movingLength]
      exact le_refl _
    | main =>
      simp only [OriginalNominalGeometry.skeleton, ht, OriginalNominalTag.movingLength]
      exact le_refl _
    | error e q =>
      change 0 ≤ G.tag.movingLength Z
      rw [ht]
      exact mul_nonneg (Nat.cast_nonneg _)
        (idealLogLength_nonneg Z hZ q.asIdeal q.ne_bot)
  have hboundary : max (3 * G.skeleton.c - 5 * G.skeleton.d - G.skeleton.R) 0 / 6 ≤
      G.boundary := by
    let x := 3 * G.skeleton.c - 5 * G.skeleton.d - G.skeleton.R
    change max x 0 / 6 ≤ max (x / 6) 0
    rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx, max_eq_left (div_nonneg hx (by norm_num))]
    · rw [max_eq_right hx, max_eq_right (div_nonpos_of_nonpos_of_nonneg hx (by norm_num))]
      norm_num
  have hretained : G.retainedLength ≤ G.ideals.firstFrequency a Z + G.supportError := by
    have h := Real.log_le_log G.retainedScale_pos G.retained_upper
    rw [Real.log_rpow (zero_lt_one.trans hZ)] at h
    apply (div_le_iff₀ (Real.log_pos hZ)).mpr
    nlinarith
  have hD : G.skeleton.d - G.supportError ≤ G.skeleton.shiftedCommon := by
    change idealLogLength Z G.ideals.opposite.val - G.supportError ≤
      idealLogLength Z G.ideals.opposite.val + G.ideals.firstFrequency a Z - G.retainedLength
    linarith
  have hg : G.skeleton.g ≤
      max (G.skeleton.shiftedCommon - G.skeleton.c - 2 * G.skeleton.w + G.skeleton.wo) 0 +
        2 * step := by
    have hpadding : G.tag.padding step ≤ 2 * step := by
      cases G.tag <;> simp only [OriginalNominalTag.padding] <;> linarith
    exact add_le_add (le_refl _) hpadding
  apply firstSaving_lower G.skeleton.c G.skeleton.d G.skeleton.shiftedCommon G.skeleton.w
    (G.skeleton.q + G.skeleton.R + G.skeleton.E) G.skeleton.R G.skeleton.wo
    G.boundary G.skeleton.g (G.tag.poolLength step) step G.supportError
    hc hw0 (by change 0 ≤ a.q + G.skeleton.R + G.skeleton.E; linarith)
    hwo G.boundary_nonneg hstep G.supportError_nonneg
    (by change G.skeleton.R ≤ a.q + G.skeleton.R + G.skeleton.E; linarith)
    hboundary hD hg (G.tag.poolLength_nonneg step hstep) hw

private theorem nominal_secondSaving_of_coordinates
    {a : RealParameters} {Z step v : ℝ}
    (G : OriginalNominalGeometry (K := K) a Z step) (side : Bool)
    {L R U V : Ideal (𝓞 K)}
    (hleft : G.ideals.second.val = if side then R else L)
    (hright : G.ideals.secondOpposite.val = if side then L else R)
    (hunit : G.ideals.unitPart.val = U)
    (hnonunit : G.ideals.nonunitPart.val = V)
    (hs : 2 * ((idealLogLength Z L + idealLogLength Z R) / 2) / 3 ≤
      2 * ((idealLogLength Z L + idealLogLength Z R) / 2) -
        5 * idealLogLength Z (gcd L R) / 6 - idealLogLength Z (commonRadical L R) +
        idealLogLength Z U + idealLogLength Z V / 6 + 2 * v / 6) :
    2 * G.halfSecond / 3 ≤
      2 * G.halfSecond - 5 * G.skeleton.g₂ / 6 - G.secondRadical + G.skeleton.t₂ +
        G.skeleton.V / 6 + 2 * v / 6 := by
  dsimp only [OriginalNominalGeometry.halfSecond, OriginalNominalGeometry.skeleton,
    OriginalNominalGeometry.secondRadical]
  rw [hleft, hright, hunit, hnonunit]
  cases side with
  | false => exact hs
  | true =>
    change 2 * ((idealLogLength Z R + idealLogLength Z L) / 2) / 3 ≤
      2 * ((idealLogLength Z R + idealLogLength Z L) / 2) -
        5 * idealLogLength Z (gcd R L) / 6 - idealLogLength Z (commonRadical R L) +
        idealLogLength Z U + idealLogLength Z V / 6 + 2 * v / 6
    rw [gcd_comm R L, commonRadical_comm R L,
      add_comm (idealLogLength Z R) (idealLogLength Z L)]
    exact hs

end T3b

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

namespace PoolExpansion

theorem t3b_removedLength_le (expansion : PoolExpansion family)
    (hfamily : family.Realizes) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count) :
    (expansion.source i).first.tag.removedLength call.base ≤ 7 * recipeInductionSigma c / 3 := by
  have hstep := (recipeInduction_budget (c := c)).1.le
  cases expansion with
  | direct =>
    have htag := congrArg
      (fun tag : OriginalNominalTag K => tag.removedLength call.base) (hfamily.tag i)
    exact htag.trans_le (by change 0 ≤ 7 * recipeInductionSigma c / 3; positivity)
  | pooled P count index source =>
    cases ht : (index i).2 with
    | inl u =>
      have ho : P.MainOrigin (index i).1 (source i) := by
        simpa only [PoolPresentation.Origin, ht] using hexpansion.2.2 i
      rcases ho with ⟨_, _, _, _, _, _, _, hfirst⟩
      change (source i).first.tag.removedLength call.base ≤ _
      rw [hfirst]
      change 0 ≤ 7 * recipeInductionSigma c / 3
      positivity
    | inr qe =>
      have ho : P.ErrorOrigin (index i).1 qe.1 qe.2 (source i) := by
        simpa only [PoolPresentation.Origin, ht] using hexpansion.2.2 i
      rcases ho with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htag, _, _⟩
      change (source i).first.tag.removedLength call.base ≤ _
      rw [htag]
      apply amplifier_error_length_le qe.2 _ (recipeInductionSigma c)
        (idealLogLength_nonneg call.base call.domain.scale _ qe.1.val.val.ne_bot)
      apply (Real.rpow_le_rpow_left_iff call.domain.scale).mp
      rw [rpow_idealLogLength call.base call.domain.scale _ qe.1.val.val.ne_bot]
      exact P.pool.norm_upper qe.1.val qe.1.property

end PoolExpansion

namespace RawLeafPacket

variable (packet : RawLeafPacket call p) (hpacket : packet.Realizes)

include hpacket in
theorem t3b_removedLength_le :
    packet.second.physical.first.tag.removedLength call.base ≤ 7 * recipeInductionSigma c / 3 := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, _, _, rfl⟩
  change (trace.second.source (raw.index j).val.1.1).physical.first.tag.removedLength call.base ≤ _
  rw [htrace.second.physical]
  exact trace.expansion.t3b_removedLength_le htrace.cauchy htrace.expansion _

include hpacket in
theorem t3b_nominal_supportError (side : Bool) :
    (packet.nominal side).supportError = 4 * p.loss := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, _, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).supportError side

def t3bFirstSaving (side : Bool) : ℝ :=
  let G := packet.nominal side
  firstSaving G.skeleton.c G.skeleton.shiftedCommon G.skeleton.w
    (G.skeleton.q + G.skeleton.R + G.skeleton.E) G.skeleton.wo
    G.boundary G.skeleton.g (G.tag.poolLength (recipeInductionSigma c))

include hpacket in
theorem t3bFirstSaving_lower (side : Bool) :
    2 * ((packet.nominal side).skeleton.c + (packet.nominal side).skeleton.w) / 3 -
        3 * recipeInductionSigma c - 5 * (4 * p.loss) / 6 ≤ packet.t3bFirstSaving side := by
  have h := T3b.nominal_firstSaving_lower (packet.nominal side)
    call.domain.scale (recipeInduction_budget (c := c)).1.le call.t3b_working_q_nonneg
    (by
      change (packet.nominal side).tag.removedLength call.base ≤ _
      rw [packet.t3b_nominal_tag hpacket]
      exact packet.t3b_removedLength_le hpacket)
  rwa [packet.t3b_nominal_supportError hpacket] at h

def t3bMultiplicityOneLength (h : packet.R.live) : ℝ :=
  idealLogLength call.base (packet.multiplicityOneRadical h).val

theorem t3bMultiplicityOneLength_nonneg (h : packet.R.live) :
    0 ≤ packet.t3bMultiplicityOneLength h :=
  idealLogLength_nonneg call.base call.domain.scale _ (packet.multiplicityOneRadical h).property.1

theorem t3bMultiplicityOneLength_rpow (h : packet.R.live) :
    call.base ^ packet.t3bMultiplicityOneLength h =
      (Arithmetic.data c).exteriorNorm (packet.multiplicityOneRadical h) :=
  rpow_idealLogLength call.base call.domain.scale _ (packet.multiplicityOneRadical h).property.1

include hpacket in
theorem t3b_multiplicityOneRadical_eq (h k : packet.R.live) :
    packet.multiplicityOneRadical h = packet.multiplicityOneRadical k := by
  have hprimes : multiplicityOneNonunitPrimes (Arithmetic.context c) packet.R.primes
      packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val) =
      multiplicityOneNonunitPrimes (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency k.val) := by
    ext i
    simp only [multiplicityOneNonunitPrimes, Finset.mem_filter,
      packet.exceptional_nonunit_classification hpacket h k i]
  unfold multiplicityOneRadical multiplicityOneNonunitRadical
  rw [hprimes]

include hpacket in
theorem t3bMultiplicityOneLength_eq (h k : packet.R.live) :
    packet.t3bMultiplicityOneLength h = packet.t3bMultiplicityOneLength k := by
  rw [t3bMultiplicityOneLength, t3bMultiplicityOneLength,
    packet.t3b_multiplicityOneRadical_eq hpacket h k]

def t3bSecondSaving (side : Bool) (h : packet.R.live) : ℝ :=
  let G := packet.nominal side
  2 * G.halfSecond - 5 * G.skeleton.g₂ / 6 - G.secondRadical + G.skeleton.t₂ +
    G.skeleton.V / 6 + 2 * packet.t3bMultiplicityOneLength h / 6

include hpacket in
/-- The original complete correlation gives the second saving for
every live row, on either orientation of the actual common pair. -/
theorem t3bSecondSaving_lower (side : Bool) (h : packet.R.live) :
    2 * (packet.nominal side).halfSecond / 3 ≤ packet.t3bSecondSaving side h := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  let packet := raw.packet j
  have hG := hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)
  have hs := packet.R.live_second_saving (Arithmetic.context c) call.base call.domain.scale
    packet.block.left_positive packet.block.right_positive h
  have hleft : (packet.nominal side).ideals.second.val =
      if side then (primePowerProduct packet.R.primes packet.R.rightMultiplicity).val
      else (primePowerProduct packet.R.primes packet.R.leftMultiplicity).val := by
    cases side with
    | false => exact (hG.second false).trans packet.block.common_left.symm
    | true => exact (hG.second true).trans packet.block.common_right.symm
  have hright : (packet.nominal side).ideals.secondOpposite.val =
      if side then (primePowerProduct packet.R.primes packet.R.leftMultiplicity).val
      else (primePowerProduct packet.R.primes packet.R.rightMultiplicity).val := by
    cases side with
    | false => exact (hG.secondOpposite false).trans packet.block.common_right.symm
    | true => exact (hG.secondOpposite true).trans packet.block.common_left.symm
  exact T3b.nominal_secondSaving_of_coordinates
    (v := packet.t3bMultiplicityOneLength h) (packet.nominal side) side
    (L := (primePowerProduct packet.R.primes packet.R.leftMultiplicity).val)
    (R := (primePowerProduct packet.R.primes packet.R.rightMultiplicity).val)
    (U := (unitFrequencyRadical (Arithmetic.context c) packet.R.primes
      packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val)).val)
    (V := (nonunitFrequencyRadical (Arithmetic.context c) packet.R.primes
      packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val)).val)
    hleft hright (hG.unitPart side h) (hG.nonunitPart side h) hs

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3bFirstSaving_lower
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3bSecondSaving_lower
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3bMultiplicityOneLength_eq
