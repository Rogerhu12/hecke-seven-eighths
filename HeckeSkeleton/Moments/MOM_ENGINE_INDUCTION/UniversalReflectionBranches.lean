import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CutoffReflectionLabels
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryReflectionProduction
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RankedProfileControl

/-!
# Uniform reflection production in the actual universal node family

The analytic producer chooses every order and constant before the moving
height and node. This module consumes that proved producer, constructs
the supported universal child labels, and fills the actual short and
outer branches of `CoreRecursionInput`. No parent or child energy bound
is a premise of the public factory.

The remaining primitive transfer concerns only actual normalized child
profiles, preserved arithmetic and a proved strict parameter-rank drop.
It is separate from the local reflection output and from any final
moment estimate. A concrete admissibility predicate must prove this
transfer; the factory does not assert it for arbitrary predicates.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckeSkeleton.ThetaKernel
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable [MeasurableSpace (ℕ × Bool)] [MeasurableSingletonClass (ℕ × Bool)]

/-- Primitive admissibility of the actual normalized reflection child.
The profile and arithmetic inputs are produced by genuine reflection;
the strict rank inequality is proved from its retained geometry below.
There is no moment, local-step, terminal or kernel-mass conclusion among
these hypotheses. -/
def ReflectionPrimitiveTransfer
    (primitive : MomentData K ω ψ → PairedInvariantParameters → Prop)
    (σ W padding A lower upper U E0 : ℝ) (hE0 : 1 ≤ E0)
    (childOrder : ℕ) (parent : Node K ω ψ) : Prop :=
  ∀ x : (ℕ × Bool) × ℝ,
    let child := parent.fixedLineReflectionChild
      (reflectionLongFirst parent.parameters) U E0 hE0 childOrder x
    ModelProfileControl child.data childOrder A 1 0 lower upper 0 →
      ReflectionArithmeticPreserved parent child U →
      parameterCoreRank σ W padding child.parameters <
        parameterCoreRank σ W padding parent.parameters →
      admissibleOfInvariant primitive child.data child.parameters

private theorem normalizedEnergy_eq_ordinary (node : Node K ω ψ)
    (hordinary : node.centered = false) (U t : ℝ) :
    node.normalizedEnergy U t = (Node.ordinary node.data node.parameters).normalizedEnergy U t := by
  have he : node.energy U t = pairedEnergy node.data node.parameters U t := by
    simp only [Node.energy, Node.plainPair, hordinary, Bool.false_eq_true, if_false,
      sub_zero, pairedEnergy]
  change node.energy U t / U ^ node.width =
    (Node.ordinary node.data node.parameters).energy U t / U ^ node.width
  rw [he, Node.ordinary_energy]

private theorem parameterCoreRank_outer {σ W padding : ℝ}
    (child parent : Node K ω ψ)
    (hz : child.parameters.z = parent.parameters.z) (hw : child.width = parent.width)
    (hchild : child.totalLength ≤ child.width + padding)
    (hparent : parent.width + padding < parent.totalLength) :
    parameterCoreRank σ W padding child.parameters <
      parameterCoreRank σ W padding parent.parameters := by
  change (if child.parameters.z = 0 then 0 else 3 * (widthBand σ W + 1)) +
      3 * widthBand σ child.width +
        (if child.width + padding < child.totalLength then 2
          else if child.totalLength ≤ 5 * child.width / 6 then 0 else 1) <
    (if parent.parameters.z = 0 then 0 else 3 * (widthBand σ W + 1)) +
      3 * widthBand σ parent.width +
        (if parent.width + padding < parent.totalLength then 2
          else if parent.totalLength ≤ 5 * parent.width / 6 then 0 else 1)
  rw [if_neg (not_lt.mpr hchild), if_pos hparent, hz, hw]
  split_ifs <;> omega

private theorem parameterCoreRank_short {σ W padding : ℝ}
    (child parent : Node K ω ψ) (hpadding : 0 ≤ padding)
    (hz : child.parameters.z = parent.parameters.z) (hw : child.width = parent.width)
    (hwidth : 0 ≤ parent.width)
    (hchild : child.totalLength ≤ 5 * child.width / 6)
    (hparentCore : parent.totalLength ≤ parent.width + padding)
    (hparent : 5 * parent.width / 6 < parent.totalLength) :
    parameterCoreRank σ W padding child.parameters <
      parameterCoreRank σ W padding parent.parameters := by
  have hchildCore : child.totalLength ≤ child.width + padding := by
    rw [hw] at hchild ⊢
    linarith
  change (if child.parameters.z = 0 then 0 else 3 * (widthBand σ W + 1)) +
      3 * widthBand σ child.width +
        (if child.width + padding < child.totalLength then 2
          else if child.totalLength ≤ 5 * child.width / 6 then 0 else 1) <
    (if parent.parameters.z = 0 then 0 else 3 * (widthBand σ W + 1)) +
      3 * widthBand σ parent.width +
        (if parent.width + padding < parent.totalLength then 2
          else if parent.totalLength ≤ 5 * parent.width / 6 then 0 else 1)
  rw [if_neg (not_lt.mpr hchildCore), if_pos hchild,
    if_neg (not_lt.mpr hparentCore), if_neg (not_le.mpr hparent), hz, hw]
  omega

private theorem reflection_comparison_child_first_stage
    {primitive : MomentData K ω ψ → PairedInvariantParameters → Prop}
    {W padding : ℝ} {cap : ℕ} (parent : UniversalNode primitive W padding cap)
    (child : Node K ω ψ) (boundary : ℝ)
    (hw : child.width = parent.val.width)
    (hlarge : 5 * parent.val.width / 6 < parent.val.totalLength)
    (hboundary : boundary ≤ parent.val.width / 15)
    (hchild : child.totalLength ≤
      3 * parent.val.width / 2 - parent.val.totalLength + 2 * parent.val.parameters.z + boundary) :
    child.totalLength ≤ 5 * child.width / 6 := by
  rw [hw]
  rcases parent.property.capacity with hzero | hcapacity
  · have hw0 := parent.property.width_nonneg
    rw [hzero, mul_zero, add_zero] at hchild
    linarith
  · have hcapacity' : parent.val.totalLength +
        (6 * parent.val.parameters.κ - 1) * parent.val.parameters.z ≤ parent.val.width := by
      change parent.val.parameters.n₁ + parent.val.parameters.n₂ + parent.val.parameters.z +
        (6 * parent.val.parameters.κ - 1) * parent.val.parameters.z ≤ parent.val.width
      nlinarith
    have hsmall := centered_positive_slot_length
      (parent.val.slot_nonneg parent.property.length) parent.property.kappa_lower
      hlarge hcapacity'
    linarith

/-- The actual ordinary reflection produces the two branch objects
consumed by `CoreRecursionInput`. Constants are uniform in the moving
height, node, scale, row and retained Fourier parameter. Primitive
transfer is used only after its genuine strict rank drop has been proved.
The outer factory handles the whole-series terminal and the retained
core reflection in one exhaustive numerical case split. -/
theorem uniform_universalReflection_branches
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (omegaCharacter psiCharacter : HeckeCharacter K)
    (cap : ℕ) (σ W padding overheadCap slotCap loss saving gap rounding branchLoss δ ε upper : ℝ)
    (hσ : 0 < σ) (hW : 0 ≤ W) (hpadding : 0 ≤ padding)
    (hoverheadCap : 0 ≤ overheadCap) (hslotCap : 0 ≤ slotCap)
    (hloss : 0 ≤ loss) (hsaving : 0 ≤ saving) (hgap : 0 < gap)
    (hrounding : 0 ≤ rounding) (hbranchLoss : 0 < branchLoss)
    (hδ : 0 < δ) (hδsmall : δ < 1 / 4) (hε : 0 < ε)
    (hmassLoss : ε * (W + overheadCap) ≤ loss) (hupper : 2 ≤ upper) :
    ∃ decay : ℝ, 1 < decay ∧ δ ≤ decay ∧ ∀ childOrder : ℕ,
      ∃ E0 : ℝ, ∃ hE0 : 1 ≤ E0, ∃ L : ℕ, childOrder ≤ L ∧ 1 ≤ L ∧
      ∀ Cp Hp lower : ℝ, 1 ≤ Cp → 0 ≤ Hp → 0 < lower → lower ≤ 1 / 2 →
      ∃ C H : ℝ, 0 ≤ C ∧ 0 ≤ H ∧
      ∀ T : ℝ, 0 ≤ T →
      ∀ (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
        (probe : ProbeData K S) (rows : RowCharacterInput K S probe)
        (theta : Finset (HeckeCharacter K))
        (primitive : MomentData K omegaCharacter psiCharacter → PairedInvariantParameters → Prop)
        (parent : ULift.{0} (UniversalNode primitive W padding cap))
        (extra : NonzeroIdeal K → NonzeroIdeal K) (U overhead : ℝ),
      1 < U → 0 ≤ overhead → overhead ≤ overheadCap →
      parent.down.val.centered = false →
      parent.down.val.data.geometry.totalLength ≤ slotCap →
      MovingReflectionRowCalibration S probe rows theta parent.down.val extra U →
      movingReflectionConductorConstant S psiCharacter theta ≤ U ^ overhead →
      2 ≤ U ^ rounding →
      (∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U, ∀ I,
        parent.down.val.data.commonMask u I =
          (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val))) →
      (∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U, ∀ t : ℝ,
        parent.down.val.data.plainBackground * parent.down.val.data.rowCharacter u ≠
          heckeNormTwist K t) →
      ∀ hprofiles : ModelProfileControl parent.down.val.data L decay Cp Hp lower upper T,
      let P := Cp * (1 + T) ^ Hp
      (∀ hPE : 1 ≤ P * E0, ReflectionPrimitiveTransfer primitive σ W padding decay lower upper
        U (P * E0) hPE childOrder parent.down.val) →
      (∀ boundary : ℝ, overhead + gap + rounding ≤ boundary →
        boundary ≤ parent.down.val.width / 15 →
        (parent.down.val.parameters.n₁ ≤ parent.down.val.width / 4 ∨
          parent.down.val.parameters.n₂ ≤ parent.down.val.width / 4) →
        parent.down.val.totalLength ≤ parent.down.val.width + padding →
        padding ≤ parent.down.val.width / 4 →
        5 * parent.down.val.width / 6 < parent.down.val.totalLength →
        Nonempty (ShortReflectionBranchAt (Ω := (ℕ × Bool) × ℝ)
          (universalPolynomialSystem.{0} primitive σ W padding cap hσ) parent U boundary
            (branchLoss + 2 * loss) (-2 * saving) C ((1 + T) ^ H))) ∧
      (parent.down.val.width + padding < parent.down.val.totalLength →
        parent.down.val.parameters.z = 0 →
        (overhead + gap) + (overhead + gap + rounding) ≤ padding →
        Nonempty (OuterReflectionBranchAt (Ω := (ℕ × Bool) × ℝ)
          (universalPolynomialSystem.{0} primitive σ W padding cap hσ) parent U padding
            (branchLoss + 2 * loss) (-2 * saving) C ((1 + T) ^ H))) := by
  obtain ⟨decay, hdecay, hδdecay, hlevels⟩ := uniform_ordinaryReflection_production
    hcomplex omegaCharacter psiCharacter cap W overheadCap slotCap loss saving gap rounding
      branchLoss δ ε upper hW hoverheadCap hslotCap hloss hsaving hgap hrounding hbranchLoss
        hδ hδsmall hε hmassLoss hupper
  refine ⟨decay, hdecay, hδdecay, ?_⟩
  intro childOrder
  obtain ⟨E0, hE0, L, hchildL, h1L, D, hD, hbudgets⟩ := hlevels childOrder
  refine ⟨E0, hE0, L, hchildL, h1L, ?_⟩
  intro Cp Hp lower hCp hHp hlower hlowerSmall
  obtain ⟨C, H, hC, hH, hproduce⟩ := hbudgets Cp Hp lower hCp hHp hlower hlowerSmall
  refine ⟨C, H, hC, hH, ?_⟩
  intro T hT S instS probe rows theta primitive parent extra U overhead hU hoverhead hoverheadBound
    hordinary hslots cal hfixed hround hmask hcharacter hprofiles
  dsimp only
  intro htransfer
  let first := reflectionLongFirst parent.down.val.parameters
  let P := Cp * (1 + T) ^ Hp
  have hinterval : lower ≤ upper := by linarith
  have horder : (if first then parent.down.val.parameters.n₂ else parent.down.val.parameters.n₁) ≤
      (if first then parent.down.val.parameters.n₁ else parent.down.val.parameters.n₂) := by
    rw [reflectionLongFirst_short, reflectionLongFirst_long]
    exact (min_le_left _ _).trans (le_max_left _ _)
  have calOrdinary : MovingReflectionRowCalibration S probe rows theta
      (Node.ordinary parent.down.val.data parent.down.val.parameters) extra U :=
    ⟨cal.identify, cal.product_budget⟩
  obtain ⟨hPE, hwhole, cutoff, hlo, hhi, hestimate, hrem0, hremBound, hfinite, hint,
      hmass, hunit, harithmetic, _hgeometry⟩ := hproduce T hT S probe rows theta parent.down.val.data
    parent.down.val.parameters first extra U overhead hU parent.down.property.width_nonneg
      parent.down.property.width_le hoverhead hoverheadBound
      parent.down.property.plain_left_nonneg parent.down.property.plain_right_nonneg horder
      hslots parent.down.property.slot_count calOrdinary hfixed hround hmask hcharacter hprofiles
  let V := selectedPlainAnnularTest
    (modelProfileControl_fixed_budget hprofiles (le_refl P)) first hlower hinterval
  let weight := ordinaryReflectionEnvelope D (P ^ (cap + 3)) (U ^ loss)
  let child := parent.down.val.fixedLineReflectionChild first U (P * E0) hPE childOrder
  let remainder := 2 * rowRestorationEnergy true S parent.down.val extra V
    (if first then parent.down.val.data.plainTest₂ else parent.down.val.data.plainTest₁) δ U
    (if first then parent.down.val.parameters.n₁ else parent.down.val.parameters.n₂)
    (if first then parent.down.val.parameters.n₂ else parent.down.val.parameters.n₁) cutoff
  have hU0 : 0 < U := zero_lt_one.trans hU
  have hnext (j : ℕ) (hj : j ≤ cutoff) : reflectionDyadicExponent U j ≤
      max (parent.down.val.width -
        max parent.down.val.parameters.n₁ parent.down.val.parameters.n₂) 0 +
          (overhead + gap + rounding) := by
    have hj' := reflectionDyadicExponent_le hU hhi hj
    rw [reflectionLongFirst_long] at hj'
    have hmax :
        max (parent.down.val.width -
          max parent.down.val.parameters.n₁ parent.down.val.parameters.n₂ + overhead) 0 ≤
        max (parent.down.val.width -
          max parent.down.val.parameters.n₁ parent.down.val.parameters.n₂) 0 + overhead := by
      apply max_le
      · linarith [le_max_left
          (parent.down.val.width - max parent.down.val.parameters.n₁ parent.down.val.parameters.n₂)
          (0 : ℝ)]
      · positivity
    change reflectionDyadicExponent U j ≤
      max (parent.down.val.width -
        max parent.down.val.parameters.n₁ parent.down.val.parameters.n₂ + overhead) 0 + gap + rounding
        at hj'
    linarith
  have hactualEstimate : parent.down.val.normalizedEnergy U 0 ≤ remainder +
      ∫ x, (child x).normalizedEnergy U 0 ∂reflectionCommonKernel volume weight cutoff := by
    rw [normalizedEnergy_eq_ordinary parent.down.val hordinary U 0]
    exact hestimate
  have hactualProfiles (x : (ℕ × Bool) × ℝ) :
      ModelProfileControl (child x).data childOrder decay 1 0 lower upper 0 := hunit x
  have hactualArithmetic (x : (ℕ × Bool) × ℝ) :
      ReflectionArithmeticPreserved parent.down.val (child x) U := {
    rows := (harithmetic x).rows
    rowCharacter := (harithmetic x).rowCharacter
    plainBackground := (harithmetic x).plainBackground
    theta := (harithmetic x).theta
    commonMask := (harithmetic x).commonMask
    width := (harithmetic x).width
    q := (harithmetic x).q }
  constructor
  · intro boundary hboundaryLower hboundary hshort hcore hpadwidth hlarge
    have hnext' (j : ℕ) (hj : j ≤ cutoff) : reflectionDyadicExponent U j ≤
        max (parent.down.val.width -
          max parent.down.val.parameters.n₁ parent.down.val.parameters.n₂) 0 + boundary :=
      (hnext j hj).trans (add_le_add le_rfl hboundaryLower)
    have hrank (x : (ℕ × Bool) × ℝ) (hx : x.1.1 ≤ cutoff) :
        parameterCoreRank σ W padding (child x).parameters <
          parameterCoreRank σ W padding parent.down.val.parameters := by
      have hlength := parent.down.val.fixedLongReflectionChild_comparison_length
        U (P * E0) hPE childOrder x padding boundary parent.down.property.length
          hshort hcore hpadwidth (hnext' x.1.1 hx)
      have hstage := reflection_comparison_child_first_stage parent.down (child x) boundary
        rfl hlarge hboundary hlength
      exact parameterCoreRank_short (child x) parent.down.val hpadding rfl rfl
        parent.down.property.width_nonneg hstage hcore hlarge
    have hadmissible (x : (ℕ × Bool) × ℝ) (hx : x.1.1 ≤ cutoff) :
        admissibleOfInvariant primitive (child x).data (child x).parameters :=
      htransfer hPE x (hactualProfiles x) (hactualArithmetic x) (hrank x hx)
    let valid := fun (x : (ℕ × Bool) × ℝ) (hx : x.1.1 ≤ cutoff) =>
      parent.down.val.fixedLongReflectionChild_comparison_invariant parent.down.property
        U (P * E0) hU hPE childOrder x boundary hshort hcore hpadwidth hlarge hboundary
          (hnext' x.1.1 hx) (hadmissible x hx)
    let out : ReflectedComparisonData (Ω := (ℕ × Bool) × ℝ)
        (universalPolynomialSystem.{0} primitive σ W padding cap hσ) parent parent U 0 boundary := {
      kernel := reflectionCommonKernel volume weight cutoff
      finite_kernel := hfinite
      child := comparisonCutoffReflectionChild parent U (P * E0) hU hPE childOrder cutoff
        boundary hshort hcore hpadwidth hlarge hboundary hnext' hadmissible
      remainder := remainder
      remainder_nonneg := hrem0
      child_integrable := hint.congr
        (cutoffReflectionChild_energy_ae parent first U (P * E0) hPE childOrder cutoff
          valid weight).symm
      child_geometry := comparisonCutoffReflectionChild_geometry parent U (P * E0) hU hPE
        childOrder cutoff boundary hshort hcore hpadwidth hlarge hboundary hnext' hadmissible weight
      estimate := by
        change parent.down.val.normalizedEnergy U 0 ≤ remainder +
          ∫ x, (cutoffReflectionChild parent first U (P * E0) hPE childOrder cutoff
            valid x).down.val.normalizedEnergy U 0 ∂reflectionCommonKernel volume weight cutoff
        rw [cutoffReflectionChild_integral]
        exact hactualEstimate }
    exact ⟨{ output := out, terminal := hremBound, mass := hmass }⟩
  · intro hnoncore hzero hcoreBudget
    by_cases hwholeCondition : parent.down.val.width + overhead + gap ≤
        max parent.down.val.parameters.n₁ parent.down.val.parameters.n₂
    · let out := wholeReflectionCoreData hcomplex S σ hσ parent first hordinary extra V
        hδ hδsmall hU0 0 hmask hcharacter (fun _ _ => rfl)
      have hterminal := hwhole (by
        rw [reflectionLongFirst_long]
        exact hwholeCondition)
      refine ⟨{ output := out, terminal := ?_, mass := ?_ }⟩
      · have heq := pairedEnergy_wholeRestoration_eq hcomplex S parent.down.val.data
          parent.down.val.parameters first extra V hδ hδsmall hU0 0 hmask hcharacter
            (fun _ _ => rfl)
        change rowRestorationEnergy false S parent.down.val extra V
          (if first then parent.down.val.data.plainTest₂ else parent.down.val.data.plainTest₁) δ U
          (if first then parent.down.val.parameters.n₁ else parent.down.val.parameters.n₂)
          (if first then parent.down.val.parameters.n₂ else parent.down.val.parameters.n₁) 0 ≤ _
        exact heq.symm.le.trans hterminal
      · change (0 : Measure ((ℕ × Bool) × ℝ)).real Set.univ ≤
          C * (1 + T) ^ H * U ^ (branchLoss + 2 * loss)
        have hp : 0 ≤ C * (1 + T) ^ H * U ^ (branchLoss + 2 * loss) :=
          mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (by linarith) _))
            (Real.rpow_nonneg hU0.le _)
        simpa using hp
    · have hlong : max parent.down.val.parameters.n₁ parent.down.val.parameters.n₂ ≤
          parent.down.val.width + (overhead + gap) := by
        linarith [lt_of_not_ge hwholeCondition]
      have hgap' : 0 ≤ overhead + gap := by linarith
      have hchildCore (x : (ℕ × Bool) × ℝ) (hx : x.1.1 ≤ cutoff) :
          (child x).totalLength ≤ (child x).width + padding :=
        parent.down.val.fixedLongReflectionChild_outer_core U (P * E0) hPE childOrder x
          (overhead + gap) (overhead + gap + rounding) padding hzero hgap' hlong
            (hnext x.1.1 hx) hcoreBudget
      have hrank (x : (ℕ × Bool) × ℝ) (hx : x.1.1 ≤ cutoff) :
          parameterCoreRank σ W padding (child x).parameters <
            parameterCoreRank σ W padding parent.down.val.parameters :=
        parameterCoreRank_outer (child x) parent.down.val rfl rfl (hchildCore x hx) hnoncore
      have hadmissible (x : (ℕ × Bool) × ℝ) (hx : x.1.1 ≤ cutoff) :
          admissibleOfInvariant primitive (child x).data (child x).parameters :=
        htransfer hPE x (hactualProfiles x) (hactualArithmetic x) (hrank x hx)
      let valid := fun (x : (ℕ × Bool) × ℝ) (hx : x.1.1 ≤ cutoff) =>
        parent.down.val.fixedLongReflectionChild_outer_invariant parent.down.property
          U (P * E0) hU hPE childOrder x hzero (hadmissible x hx)
      let out : CoreReflectionData (Ω := (ℕ × Bool) × ℝ)
          (universalPolynomialSystem.{0} primitive σ W padding cap hσ) parent U 0 padding := {
        kernel := reflectionCommonKernel volume weight cutoff
        finite_kernel := hfinite
        child := outerCutoffReflectionChild parent U (P * E0) hU hPE childOrder cutoff
          hzero hadmissible
        remainder := remainder
        remainder_nonneg := hrem0
        child_integrable := hint.congr
          (cutoffReflectionChild_energy_ae parent first U (P * E0) hPE childOrder cutoff
            valid weight).symm
        child_geometry := outerCutoffReflectionChild_geometry parent U (P * E0) hU hPE
          childOrder cutoff hzero hadmissible weight (overhead + gap)
            (overhead + gap + rounding) hgap' hlong hnext hcoreBudget
        estimate := by
          change parent.down.val.normalizedEnergy U 0 ≤ remainder +
            ∫ x, (cutoffReflectionChild parent first U (P * E0) hPE childOrder cutoff
              valid x).down.val.normalizedEnergy U 0 ∂reflectionCommonKernel volume weight cutoff
          rw [cutoffReflectionChild_integral]
          exact hactualEstimate }
      exact ⟨{ output := out, terminal := hremBound, mass := hmass }⟩

end HeckeSkeleton.Moments.EngineInduction
