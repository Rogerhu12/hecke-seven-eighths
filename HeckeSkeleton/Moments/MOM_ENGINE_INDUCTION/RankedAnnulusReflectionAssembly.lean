import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.UniversalReflectionBranches
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RankedAnnulusPrimitive
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RankedBaseBranch
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.FiniteProfileConstants

/-!
# Finite-rank reflection production with the actual annulus schedule

All analytic orders and constants are selected on the one fixed maximal
annulus. Actual nodes retain the tighter annulus prescribed by their
true geometric rank. The literal reflected power-window construction
proves that tighter support before its already proved unit seminorm
estimate is used; this is the concrete primitive transfer below.

The only aggregation is over finitely many geometric ranks. The actual
reflection producer, positive kernels, terminal bounds, normalized
children and arithmetic calibration are reused unchanged. No support
or energy conclusion is introduced as a source hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable [MeasurableSpace (ℕ × Bool)] [MeasurableSingletonClass (ℕ × Bool)]

private theorem profile_control_at_height {d : MomentData K ω ψ}
    {J : ℕ} {A C H lower upper T : ℝ}
    (h : ModelProfileControl d J A (profileFamilyBudget C H T) 0 lower upper 0) :
    ModelProfileControl d J A (1 + C) H lower upper T := by
  intro q
  refine ⟨(h q).1, (h q).2.1, ?_⟩
  simpa only [profileFamilyBudget, Real.rpow_zero, mul_one] using (h q).2.2

private theorem parameterCoreRank_pos_of_large {σ W padding : ℝ}
    (n : Node K ω ψ) (hlarge : 5 * n.width / 6 < n.totalLength) :
    0 < parameterCoreRank σ W padding n.parameters := by
  have hsmall : ¬n.parameters.n₁ + n.parameters.n₂ + n.parameters.z ≤
      5 * (n.parameters.m + n.parameters.q) / 6 := not_le.mpr hlarge
  simp only [parameterCoreRank, if_neg hsmall]
  split_ifs <;> omega

private theorem parameterCoreRank_pos_of_noncore {σ W padding : ℝ}
    (n : Node K ω ψ) (hnoncore : n.width + padding < n.totalLength) :
    0 < parameterCoreRank σ W padding n.parameters := by
  have hn : n.parameters.m + n.parameters.q + padding <
      n.parameters.n₁ + n.parameters.n₂ + n.parameters.z := hnoncore
  simp only [parameterCoreRank, if_pos hn]
  split_ifs <;> omega

private theorem envelope_scale_mono {A B U e f : ℝ}
    (hAB : A ≤ B) (hB : 0 ≤ B) (hU : 1 ≤ U) (hef : e ≤ f) :
    A * U ^ e ≤ B * U ^ f :=
  mul_le_mul hAB (Real.rpow_le_rpow_of_exponent_le hU hef)
    (Real.rpow_nonneg (zero_le_one.trans hU) _) hB

/-- Select every genuine reflection order before the backward schedule,
then unify the finitely many actual branch budgets with the base budget.
The resulting `C,H` precede all moving heights, scales, rows and models.
Both terminal and mass exponents may subsequently be enlarged, with the
same actual outputs and the same common constants.

This constructs actual branches in the ranked-annulus family. Its
source roots enter directly from the original annulus, and its literal
reflection children retain the parent support before passing to their
own earlier support layer.
-/
theorem uniform_rankedAnnulusReflection_branches
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (omegaCharacter psiCharacter : HeckeCharacter K)
    (cap : ℕ) (σ W padding overheadCap slotCap loss saving gap rounding branchLoss δ ε upper : ℝ)
    (hσ : 0 < σ) (hW : 0 ≤ W) (hpadding : 0 ≤ padding)
    (hoverheadCap : 0 ≤ overheadCap) (hslotCap : 0 ≤ slotCap)
    (hloss : 0 ≤ loss) (hsaving : 0 ≤ saving) (hgap : 0 < gap)
    (hrounding : 0 ≤ rounding) (hbranchLoss : 0 < branchLoss)
    (hδ : 0 < δ) (hδsmall : δ < 1 / 4) (hε : 0 < ε)
    (hmassLoss : ε * (W + overheadCap) ≤ loss) (hupper : 2 ≤ upper) :
    ∃ decay : ℝ, 1 < decay ∧ δ ≤ decay ∧ ∃ reflection : ℕ → ℕ,
      (∀ J, J ≤ reflection J ∧ 1 ≤ reflection J) ∧
      ∀ (ground : ℕ) (engine : ℕ → ℕ) (Cp Hp lower floor baseBoundary : ℝ),
      1 ≤ ground → 0 ≤ Cp → 0 ≤ Hp → 0 < lower → lower ≤ 1 / 2 →
      ∃ C H : ℝ, 0 ≤ C ∧ 0 ≤ H ∧
      ∀ massExponent terminalExponent : ℝ,
      branchLoss + 2 * loss ≤ massExponent → -2 * saving ≤ terminalExponent →
      ∀ T : ℝ, 0 ≤ T →
      ∀ (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
        (probe : ProbeData K S) (rows : RowCharacterInput K S probe)
        (U overhead : ℝ),
      1 < U → 0 ≤ overhead → overhead ≤ overheadCap →
      uniformReflectionConductorConstant S psiCharacter ≤ U ^ overhead →
      2 ≤ U ^ rounding →
      let primitive := reflectionRankedAnnulusPrimitive
        (ω := omegaCharacter) (ψ := psiCharacter) S probe rows U ground engine reflection
        σ W padding decay (profileFamilyBudget Cp Hp T) lower upper
      ∀ parent : ULift.{0} (UniversalNode primitive W padding cap),
      parent.down.val.data.geometry.totalLength ≤ slotCap →
      (parent.down.val.parameters.n₁ + parent.down.val.parameters.n₂ +
          parent.down.val.data.geometry.totalLength ≤ floor + padding + floor / 6 →
        Nonempty (TerminalComponents.{0} (parent.down.val.normalizedEnergy U 0)
          U T C H floor padding σ baseBoundary)) ∧
      (parent.down.val.centered = false →
        (∀ boundary : ℝ, overhead + gap + rounding ≤ boundary →
          boundary ≤ parent.down.val.width / 15 →
          (parent.down.val.parameters.n₁ ≤ parent.down.val.width / 4 ∨
            parent.down.val.parameters.n₂ ≤ parent.down.val.width / 4) →
          parent.down.val.totalLength ≤ parent.down.val.width + padding →
          padding ≤ parent.down.val.width / 4 →
          5 * parent.down.val.width / 6 < parent.down.val.totalLength →
          Nonempty (ShortReflectionBranchAt (Ω := (ℕ × Bool) × ℝ)
            (universalPolynomialSystem.{0} primitive σ W padding cap hσ) parent U boundary
              massExponent terminalExponent C ((1 + T) ^ H))) ∧
        (parent.down.val.width + padding < parent.down.val.totalLength →
          parent.down.val.parameters.z = 0 →
          (overhead + gap) + (overhead + gap + rounding) ≤ padding →
          Nonempty (OuterReflectionBranchAt (Ω := (ℕ × Bool) × ℝ)
            (universalPolynomialSystem.{0} primitive σ W padding cap hσ) parent U padding
              massExponent terminalExponent C ((1 + T) ^ H)))) := by
  let N := 6 * (widthBand σ W + 1)
  let upperMax := upper * (2 : ℝ) ^ N
  have hpower : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  have hupperMax : 2 ≤ upperMax := by
    apply hupper.trans
    calc
      upper = upper * 1 := (mul_one _).symm
      _ ≤ upper * (2 : ℝ) ^ N := mul_le_mul_of_nonneg_left hpower (by linarith)
  obtain ⟨decay, hdecay, hδdecay, hlevels⟩ := uniform_universalReflection_branches
    hcomplex omegaCharacter psiCharacter cap σ W padding overheadCap slotCap loss saving gap
      rounding branchLoss δ ε upperMax hσ hW hpadding hoverheadCap hslotCap hloss hsaving
        hgap hrounding hbranchLoss hδ hδsmall hε hmassLoss hupperMax
  choose E0 hE0 reflection horder hpositiveOrder hbudgets using hlevels
  refine ⟨decay, hdecay, hδdecay, reflection,
    fun J => ⟨horder J, hpositiveOrder J⟩, ?_⟩
  intro ground engine Cp Hp lower floor baseBoundary hground hCp hHp hlower hlowerSmall
  let lowerMax := lower / (2 : ℝ) ^ N
  have hlowerMax : 0 < lowerMax := div_pos hlower (by positivity)
  have hlowerMaxSmall : lowerMax ≤ 1 / 2 := by
    apply le_trans _ hlowerSmall
    calc
      lower / (2 : ℝ) ^ N ≤ lower / 1 :=
        div_le_div_of_nonneg_left hlower.le (by norm_num) hpower
      _ = lower := div_one _
  let requestedOrder := fun rank : ℕ => backwardProfileOrder ground engine reflection (rank - 1)
  have hCpOne : 1 ≤ 1 + Cp := by linarith
  choose coefficients degrees hcoefficients hdegrees produce using
    fun rank : ℕ => hbudgets (requestedOrder rank) (1 + Cp) Hp lowerMax
      hCpOne hHp hlowerMax hlowerMaxSmall
  obtain ⟨Cb, Hb, _hCb, _hHb, hCb0, hHb0, base⟩ :=
    uniform_ranked_profile_base_components.{0} (K := K) cap ground engine reflection
      σ W padding decay Cp Hp lowerMax upperMax floor baseBoundary
      hground (by linarith) hCp hHp hlowerMax (by linarith)
  let C := finiteStageBound N coefficients + Cb
  let H := finiteStageBound N degrees + Hb
  have hCf : 0 < finiteStageBound N coefficients := finiteStageBound_pos N coefficients
  have hHf : 0 < finiteStageBound N degrees := finiteStageBound_pos N degrees
  have hC : 0 ≤ C := by dsimp only [C]; linarith
  have hH : 0 ≤ H := by dsimp only [H]; linarith
  refine ⟨C, H, hC, hH, ?_⟩
  intro massExponent terminalExponent hmassExponent hterminalExponent
    T hT S instS probe rows U overhead hU hoverhead hoverheadBound hfixed hround
  dsimp only
  let primitive := reflectionRankedAnnulusPrimitive
    (ω := omegaCharacter) (ψ := psiCharacter) S probe rows U ground engine reflection
    σ W padding decay (profileFamilyBudget Cp Hp T) lower upper
  intro parent hslots
  have hU0 : 0 < U := zero_lt_one.trans hU
  have hX : 1 ≤ 1 + T := by linarith
  have hP : 1 ≤ profileFamilyBudget Cp Hp T := profileFamilyBudget_one_le hCp hHp hT
  have hparent : admissibleOfInvariant primitive parent.down.val.data
      parent.down.val.parameters := parent.down.property.admissible
  have hprofile : admissibleOfInvariant
      (rankedProfilePrimitive ground engine reflection σ W padding decay
        (profileFamilyBudget Cp Hp T) lowerMax upperMax)
      parent.down.val.data parent.down.val.parameters :=
    rankedAnnulusProfilePrimitive_maximal ground engine reflection hlower.le
      (by linarith) hparent.2
  have hcommon0 : 0 ≤ C * (1 + T) ^ H :=
    mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans hX) _)
  have hbaseEnvelope : Cb * (1 + T) ^ Hb ≤ C * (1 + T) ^ H := by
    apply mul_le_mul (by dsimp only [C]; linarith)
      (Real.rpow_le_rpow_of_exponent_le hX (by dsimp only [H]; linarith))
      (Real.rpow_nonneg (zero_le_one.trans hX) _) hC
  have hstageEnvelope (rank : ℕ) (hrank : rank ≤ N) :
      coefficients rank * (1 + T) ^ degrees rank ≤ C * (1 + T) ^ H := by
    apply (finiteStageBound_height_envelope N coefficients degrees hrank hT).trans
    exact mul_le_mul (by dsimp only [C]; linarith)
      (Real.rpow_le_rpow_of_exponent_le hX (by dsimp only [H]; linarith))
      (Real.rpow_nonneg (zero_le_one.trans hX) _) hC
  constructor
  · intro hlength
    obtain ⟨components⟩ := base T hT parent.down.val U hU.le
      parent.down.property.slot_count hprofile hlength
    exact ⟨{ components with mass := components.mass.trans hbaseEnvelope }⟩
  · intro hordinary
    let rank := parameterCoreRank σ W padding parent.down.val.parameters
    have hrankBound : rank ≤ N :=
      (parameterCoreRank_lt_bound parent.down.val.parameters hσ
        parent.down.property.width_le).le
    obtain ⟨extra, hcal, hmask, hnonNorm⟩ := hparent.1
    have cal : ReflectionRowCalibration S probe rows parent.down.val extra U :=
      ⟨hcal.identify, hcal.product_budget⟩
    have hactualMask : ∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U,
        ∀ I, parent.down.val.data.commonMask u I =
          (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val)) :=
      fun u _ I => hmask u I
    have hactualNonNorm : ∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U,
        ∀ t : ℝ, parent.down.val.data.plainBackground * parent.down.val.data.rowCharacter u ≠
          heckeNormTwist K t := hnonNorm
    have hparentProfiles (hrank : 0 < rank) : ModelProfileControl parent.down.val.data
        (reflection (requestedOrder rank)) decay (1 + Cp) Hp lowerMax upperMax T :=
      profile_control_at_height
        (rankedProfilePrimitive_parent_orders ground engine reflection hprofile hrank).2
    have htransfer : ∀ hPE : 1 ≤ profileFamilyBudget Cp Hp T * E0 (requestedOrder rank),
        ReflectionPrimitiveTransfer primitive σ W padding decay lowerMax upperMax U
          (profileFamilyBudget Cp Hp T * E0 (requestedOrder rank)) hPE
          (requestedOrder rank) parent.down.val := by
      intro hPE
      exact reflectionRankedAnnulusPrimitive_transfer ground engine reflection
        parent.down.val _ hPE hP hlower.le hlowerSmall hupper hparent
    have hbranches (hrank : 0 < rank) := produce rank T hT S probe rows primitive parent
      extra U overhead hU hoverhead hoverheadBound hordinary hslots cal hfixed hround
        hactualMask hactualNonNorm (hparentProfiles hrank) htransfer
    have hterminalScale : coefficients rank * (1 + T) ^ degrees rank * U ^ (-2 * saving) ≤
        C * (1 + T) ^ H * U ^ terminalExponent :=
      envelope_scale_mono (hstageEnvelope rank hrankBound) hcommon0 hU.le hterminalExponent
    have hmassScale : coefficients rank * (1 + T) ^ degrees rank * U ^ (branchLoss + 2 * loss) ≤
        C * (1 + T) ^ H * U ^ massExponent :=
      envelope_scale_mono (hstageEnvelope rank hrankBound) hcommon0 hU.le hmassExponent
    constructor
    · intro boundary hboundaryLower hboundary hshort hcore hpaddingWidth hlarge
      have hrank : 0 < rank := parameterCoreRank_pos_of_large parent.down.val hlarge
      obtain ⟨out⟩ := (hbranches hrank).1 boundary hboundaryLower hboundary hshort hcore
        hpaddingWidth hlarge
      exact ⟨{ output := out.output
               terminal := out.terminal.trans hterminalScale
               mass := out.mass.trans hmassScale }⟩
    · intro hnoncore hzero hcoreBudget
      have hrank : 0 < rank := parameterCoreRank_pos_of_noncore parent.down.val hnoncore
      obtain ⟨out⟩ := (hbranches hrank).2 hnoncore hzero hcoreBudget
      exact ⟨{ output := out.output
               terminal := out.terminal.trans hterminalScale
               mass := out.mass.trans hmassScale }⟩

end HeckeSkeleton.Moments.EngineInduction
