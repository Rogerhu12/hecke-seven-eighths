import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.UniformOrdinaryReflection
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CommonKernelMass

/-!
# Complete uniform production of an ordinary reflection

The decay exponent and all required Euler orders precede the common
profile constants. The latter precede the moving height, original
moment model, row, scale, cutoff and Fourier parameter. A single actual
model control supplies both the reflected long factor and the unchanged
short factor and prime slots. The passage to weight zero costs exactly
a factor two in the common profile constant.

The produced measure retains all dyadic windows and both fixed lines.
Its mass pays the complete squared branch count and the actual profile
normalization factor. The whole-series alternative is proved from the
same original finite polynomial; it does not introduce a child with a
negative length or an assumed recursive moment estimate.
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

/-- One true model control supplies the high-order reflected factor
and the weight-zero absolute estimates for every unchanged factor. -/
theorem modelProfileControl_restoration_orders
    {d : MomentData K ω ψ} {J L : ℕ} {A C H lower upper T : ℝ}
    (h : ModelProfileControl d L A C H lower upper T)
    (hJ : J ≤ L) (hfirst : 1 ≤ L) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hT : 0 ≤ T) (hlower : 0 < lower) (hinterval : lower ≤ upper) :
    ModelProfileControl d J A (2 * C) H lower upper T ∧
      ModelProfileControl d 1 0 (2 * C) H lower upper T := by
  constructor
  · intro q
    have hq := modelProfileControl_mono_order h hJ q
    refine ⟨hq.1, hq.2.1, hq.2.2.trans ?_⟩
    have hp : 0 ≤ C * (1 + T) ^ H :=
      mul_nonneg hC (Real.rpow_nonneg (by linarith) _)
    nlinarith
  · exact modelProfileControl_mono_order
      (modelProfileControl_weight_zero h hA hlower hinterval) hfirst

/-- The actual child has the original width, slots and surviving slot
geometry, while precisely one plain exponent becomes its dyadic one. -/
theorem Node.fixedLineReflectionChild_geometry
    (node : Node K ω ψ) (first : Bool) (U E0 : ℝ)
    (hE0 : 1 ≤ E0) (J : ℕ) (x : (ℕ × Bool) × ℝ) :
    let child := node.fixedLineReflectionChild first U E0 hE0 J x
    child.width = node.width ∧ child.parameters.z = node.parameters.z ∧
      child.data.geometry.slotCount = node.data.geometry.slotCount ∧
      child.data.geometry.totalLength = node.data.geometry.totalLength ∧
      child.totalLength = (if first then node.parameters.n₂ else node.parameters.n₁) +
        reflectionDyadicExponent U x.1.1 + node.parameters.z := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  cases first <;>
    simp only [Node.fixedLineReflectionChild, Node.normalizedOrdinaryPowerChildNode,
      Node.totalLength, Node.ordinary, ordinaryPowerParameters,
      Bool.false_eq_true, if_false, if_true] <;> ring

private theorem reflection_height_mass_identity
    (C D Cp Hp I U T loss branchLoss : ℝ) (cap : ℕ)
    (hU : 0 < U) (hT : 0 ≤ T) :
    C * U ^ branchLoss *
        (D * (Cp * (1 + T) ^ Hp) ^ (cap + 3) * U ^ loss * I) ^ 2 =
      (C * (D * Cp ^ (cap + 3) * I) ^ 2) *
        (1 + T) ^ (2 * Hp * (cap + 3 : ℕ)) * U ^ (branchLoss + 2 * loss) := by
  have hX : 0 ≤ 1 + T := by linarith
  have hheight : ((1 + T) ^ Hp) ^ (cap + 3) =
      (1 + T) ^ (Hp * (cap + 3 : ℕ)) :=
    (Real.rpow_mul_natCast hX Hp (cap + 3)).symm
  have hheight₂ : ((1 + T) ^ (Hp * (cap + 3 : ℕ))) ^ 2 =
      (1 + T) ^ (2 * Hp * (cap + 3 : ℕ)) := by
    rw [← Real.rpow_mul_natCast hX]
    congr 1
    norm_num <;> ring
  have hscale : U ^ branchLoss * (U ^ loss) ^ 2 = U ^ (branchLoss + 2 * loss) := by
    rw [← Real.rpow_mul_natCast hU.le, ← Real.rpow_add hU]
    congr 1
    norm_num <;> ring
  rw [mul_pow Cp ((1 + T) ^ Hp) (cap + 3), hheight]
  calc
    _ = (C * (D * Cp ^ (cap + 3) * I) ^ 2) *
        ((1 + T) ^ (Hp * (cap + 3 : ℕ))) ^ 2 *
          (U ^ branchLoss * (U ^ loss) ^ 2) := by ring
    _ = _ := by rw [hheight₂, hscale]

/-- Genuine reflection with one preselected order, common height
constants, a full finite positive kernel and literal normalized child
models. The displayed powers contain all profile and branch costs.
Every hypothesis concerns the original arithmetic, profiles or lengths;
no parent or child moment estimate is assumed. -/
theorem uniform_ordinaryReflection_production
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (omegaCharacter psiCharacter : HeckeCharacter K) (cap : ℕ)
    (widthCap overheadCap slotCap loss saving gap rounding branchLoss δ ε upper : ℝ)
    (hwidthCap : 0 ≤ widthCap) (hoverheadCap : 0 ≤ overheadCap)
    (hslotCap : 0 ≤ slotCap) (hloss : 0 ≤ loss) (hsaving : 0 ≤ saving)
    (hgap : 0 < gap) (hrounding : 0 ≤ rounding) (hbranchLoss : 0 < branchLoss)
    (hδ : 0 < δ) (hδsmall : δ < 1 / 4) (hε : 0 < ε)
    (hmassLoss : ε * (widthCap + overheadCap) ≤ loss) (hupper : 2 ≤ upper) :
    ∃ decay : ℝ, 1 < decay ∧ δ ≤ decay ∧ ∀ childOrder : ℕ,
      ∃ E0 : ℝ, ∃ hE0 : 1 ≤ E0, ∃ L : ℕ, childOrder ≤ L ∧ 1 ≤ L ∧
        ∃ densityConstant : ℝ, 0 ≤ densityConstant ∧
      ∀ (Cp Hp lower : ℝ) (_hCp : 1 ≤ Cp) (_hHp : 0 ≤ Hp)
        (hlower : 0 < lower) (hlowerSmall : lower ≤ 1 / 2),
      ∃ C H : ℝ, 0 ≤ C ∧ 0 ≤ H ∧
      ∀ T : ℝ, 0 ≤ T →
      ∀ (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
        (probe : ProbeData K S) (rows : RowCharacterInput K S probe)
        (d : MomentData K omegaCharacter psiCharacter) (a : RealParameters)
        (first : Bool) (extra : NonzeroIdeal K → NonzeroIdeal K)
        (U overhead : ℝ),
      1 < U → 0 ≤ a.m + a.q → a.m + a.q ≤ widthCap →
      0 ≤ overhead → overhead ≤ overheadCap →
      0 ≤ a.n₁ → 0 ≤ a.n₂ →
      (if first then a.n₂ else a.n₁) ≤ (if first then a.n₁ else a.n₂) →
      d.geometry.totalLength ≤ slotCap → d.geometry.slotCount ≤ cap →
      ReflectionRowCalibration S probe rows (Node.ordinary d a) extra U →
      uniformReflectionConductorConstant S psiCharacter ≤ U ^ overhead →
      2 ≤ U ^ rounding →
      (∀ u ∈ pairedRows d a U, ∀ I, d.commonMask u I =
        (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val))) →
      (∀ u ∈ pairedRows d a U, ∀ t : ℝ,
        d.plainBackground * d.rowCharacter u ≠ heckeNormTwist K t) →
      ∀ hprofiles : ModelProfileControl d L decay Cp Hp lower upper T,
      let P := Cp * (1 + T) ^ Hp
      ∃ hPE : 1 ≤ P * E0,
      let V := selectedPlainAnnularTest
        (modelProfileControl_fixed_budget hprofiles (le_refl P)) first
        hlower (by linarith)
      let child := (Node.ordinary d a).fixedLineReflectionChild first U (P * E0) hPE childOrder
      let weight := ordinaryReflectionEnvelope densityConstant (P ^ (cap + 3)) (U ^ loss)
      ((a.m + a.q + overhead + gap ≤ (if first then a.n₁ else a.n₂)) →
        (Node.ordinary d a).normalizedEnergy U 0 ≤ C * (1 + T) ^ H * U ^ (-2 * saving)) ∧
      ∃ cutoff : ℕ,
        U ^ (max (a.m + a.q - (if first then a.n₁ else a.n₂) + overhead) 0 + gap) ≤
          (2 : ℝ) ^ cutoff ∧
        (2 : ℝ) ^ cutoff ≤
          U ^ (max (a.m + a.q - (if first then a.n₁ else a.n₂) + overhead) 0 + gap + rounding) ∧
        let remainder := 2 * rowRestorationEnergy true S (Node.ordinary d a) extra V
          (if first then d.plainTest₂ else d.plainTest₁) δ U
          (if first then a.n₁ else a.n₂) (if first then a.n₂ else a.n₁) cutoff
        let kernel := reflectionCommonKernel volume weight cutoff
        (Node.ordinary d a).normalizedEnergy U 0 ≤ remainder +
          ∫ x, (child x).normalizedEnergy U 0 ∂kernel ∧
        0 ≤ remainder ∧ remainder ≤ C * (1 + T) ^ H * U ^ (-2 * saving) ∧
        IsFiniteMeasure kernel ∧
        Integrable (fun x => (child x).normalizedEnergy U 0) kernel ∧
        kernel.real Set.univ ≤ C * (1 + T) ^ H * U ^ (branchLoss + 2 * loss) ∧
        (∀ x, ModelProfileControl (child x).data childOrder decay 1 0 lower upper 0) ∧
        (∀ x, ReflectionArithmeticPreserved (Node.ordinary d a) (child x) U) ∧
        (∀ᵐ x ∂kernel,
          0 ≤ (child x).parameters.n₁ ∧ 0 ≤ (child x).parameters.n₂ ∧
          (child x).parameters.z = a.z ∧ (child x).width = a.m + a.q ∧
          (child x).data.geometry.slotCount = d.geometry.slotCount ∧
          (child x).data.geometry.totalLength = d.geometry.totalLength ∧
          (child x).totalLength ≤ (if first then a.n₂ else a.n₁) +
            max (a.m + a.q - (if first then a.n₁ else a.n₂)) 0 +
              (overhead + gap + rounding) + a.z) := by
  obtain ⟨decay, Lt, hdecay, hδdecay, hterminal⟩ :=
    uniform_rowRestorationEnergy_terminal (K := K) hcomplex psiCharacter cap widthCap
      overheadCap slotCap loss saving gap δ ε hwidthCap hoverheadCap hslotCap hloss
      hsaving hgap hδ hε hmassLoss
  refine ⟨decay, hdecay, hδdecay, ?_⟩
  intro childOrder
  obtain ⟨E0, hE0, Ld, hchildLd, D, hD, hreflection⟩ :=
    uniform_ordinaryReflection_output hcomplex omegaCharacter psiCharacter hδ hδsmall
      hδdecay (by linarith : 0 < upper) hε childOrder cap
  let L := max 1 (max Lt Ld)
  have hLt : Lt ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hLd : Ld ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  have h1L : 1 ≤ L := le_max_left _ _
  let Bcap := widthCap + overheadCap + gap + rounding
  have hBcap : 0 ≤ Bcap := by dsimp [Bcap]; positivity
  obtain ⟨Cm, hCm, hmass⟩ := reflectionCommonKernel_mass_subpower
    (Ω := ℝ) hBcap hbranchLoss
  refine ⟨E0, hE0, L, hchildLd.trans hLd, h1L, D, hD, ?_⟩
  intro Cp Hp lower hCp hHp hlower hlowerSmall
  have hinterval : lower ≤ upper := by linarith
  obtain ⟨Ct, Ht, hCt, hHt, _hHt_eq, htail⟩ :=
    hterminal (2 * Cp) Hp lower upper (by linarith) hHp hlower hinterval
  let I₂ : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ))
  let Cmass := Cm * (D * Cp ^ (cap + 3) * I₂) ^ 2
  let Hmass := 2 * Hp * (cap + 3 : ℕ)
  let C := 2 * Ct + Cmass
  let H := Ht + Hmass
  have hCmass : 0 ≤ Cmass := mul_nonneg hCm.le (sq_nonneg _)
  have hHmass : 0 ≤ Hmass := by dsimp [Hmass]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hH : 0 ≤ H := add_nonneg hHt hHmass
  refine ⟨C, H, hC, hH, ?_⟩
  intro T hT S instS probe rows d a first extra U overhead hU hwidth hwidthBound
    hoverhead hoverheadBound hn₁ hn₂ horder hslots hcount cal hfixed hround
    hmask hcharacter hprofiles
  let P := Cp * (1 + T) ^ Hp
  have hX : 1 ≤ 1 + T := by linarith
  have hP : 1 ≤ P := one_le_mul_of_one_le_of_one_le hCp (Real.one_le_rpow hX hHp)
  have hPE : 1 ≤ P * E0 := one_le_mul_of_one_le_of_one_le hP hE0
  refine ⟨hPE, ?_⟩
  dsimp only
  let V := selectedPlainAnnularTest
    (modelProfileControl_fixed_budget hprofiles (le_refl P)) first hlower hinterval
  let child := (Node.ordinary d a).fixedLineReflectionChild first U (P * E0) hPE childOrder
  let weight := ordinaryReflectionEnvelope D (P ^ (cap + 3)) (U ^ loss)
  let long := if first then a.n₁ else a.n₂
  let short := if first then a.n₂ else a.n₁
  let Wshort := if first then d.plainTest₂ else d.plainTest₁
  have hlong : 0 ≤ long := by cases first <;> assumption
  have hU0 : 0 < U := zero_lt_one.trans hU
  obtain ⟨hLongProfiles, hOtherProfiles⟩ := modelProfileControl_restoration_orders
    hprofiles hLt h1L (by linarith : 0 ≤ decay) (zero_le_one.trans hCp)
      hT hlower hinterval
  have hlongProfiles (u : NonzeroIdeal K) (_hu : u ∈ pairedRows d a U) :
      SliceControl Lt decay (2 * Cp) Hp lower upper T (V u).toFun := by
    change SliceControl Lt decay (2 * Cp) Hp lower upper T
      ((if first then d.plainTest₁ else d.plainTest₂).profile u 0)
    cases first with
    | false => exact modelProfileControl_plain₂ hLongProfiles u
    | true => exact modelProfileControl_plain₁ hLongProfiles u
  have hshortProfiles (u : NonzeroIdeal K) (_hu : u ∈ pairedRows d a U) :
      SliceControl 1 0 (2 * Cp) Hp lower upper T (Wshort.profile u 0) := by
    cases first with
    | false => exact modelProfileControl_plain₁ hOtherProfiles u
    | true => exact modelProfileControl_plain₂ hOtherProfiles u
  have hslotProfiles (i : Fin d.geometry.slotCount) :
      SliceControl 1 0 (2 * Cp) Hp lower upper T ((d.geometry.slots i).profile 0) :=
    modelProfileControl_prime hOtherProfiles i
  have hheightTail : Ct * (1 + T) ^ Ht ≤ C * (1 + T) ^ H := by
    exact mul_le_mul (by dsimp [C]; linarith)
      (Real.rpow_le_rpow_of_exponent_le hX (by dsimp [H]; linarith))
      (Real.rpow_nonneg (zero_le_one.trans hX) _) hC
  have hheightDoubleTail : 2 * Ct * (1 + T) ^ Ht ≤ C * (1 + T) ^ H := by
    exact mul_le_mul (by dsimp [C]; linarith)
      (Real.rpow_le_rpow_of_exponent_le hX (by dsimp [H]; linarith))
      (Real.rpow_nonneg (zero_le_one.trans hX) _) hC
  have hheightMass : Cmass * (1 + T) ^ Hmass ≤ C * (1 + T) ^ H := by
    exact mul_le_mul (by dsimp [C]; linarith)
      (Real.rpow_le_rpow_of_exponent_le hX (by dsimp [H]; linarith))
      (Real.rpow_nonneg (zero_le_one.trans hX) _) hC
  constructor
  · intro hwhole
    have ht := (htail T hT S probe rows (Node.ordinary d a) extra V Wshort
      U overhead long short false 0 hU hwidth hwidthBound hoverhead hoverheadBound
      hlong horder hslots hcount cal hfixed hlongProfiles hshortProfiles hslotProfiles
      (by simpa only [Node.width, Node.ordinary, long, Bool.false_eq_true, if_false]
        using hwhole)).1
    have heq := pairedEnergy_wholeRestoration_eq hcomplex S d a first extra V
      hδ hδsmall hU0 0 hmask hcharacter (fun _ _ => rfl)
    rw [heq]
    exact ht.trans (mul_le_mul_of_nonneg_right hheightTail (Real.rpow_nonneg hU0.le _))
  · obtain ⟨cutoff, hlo, hhi, hgeometry⟩ := exists_reflection_dyadic_geometry
      (M := a.m + a.q) (n := long) hU hoverhead hgap.le hround
    refine ⟨cutoff, hlo, hhi, ?_⟩
    have hbudget : ε * (a.m + a.q + overhead) ≤ loss :=
      (mul_le_mul_of_nonneg_left (add_le_add hwidthBound hoverheadBound) hε.le).trans hmassLoss
    have hdprofiles : ModelProfileControl d Ld decay P 0 lower upper 0 :=
      modelProfileControl_fixed_budget (modelProfileControl_mono_order hprofiles hLd) le_rfl
    have hout := hreflection P lower hP hlower hlowerSmall hupper S probe rows d a
      first extra U overhead loss hU hcount cal hfixed hbudget hmask hcharacter
      hdprofiles hinterval hPE cutoff
    have hcutoffTail : max ((Node.ordinary d a).width - long + overhead) 0 + gap ≤
        reflectionDyadicExponent U cutoff := le_reflectionDyadicExponent hU hlo
    have ht := (htail T hT S probe rows (Node.ordinary d a) extra V Wshort
      U overhead long short true cutoff hU hwidth hwidthBound hoverhead hoverheadBound
      hlong horder hslots hcount cal hfixed hlongProfiles hshortProfiles hslotProfiles
      (by simpa only [if_true] using hcutoffTail)).1
    have hrest : 2 * rowRestorationEnergy true S (Node.ordinary d a) extra V Wshort
        δ U long short cutoff ≤ C * (1 + T) ^ H * U ^ (-2 * saving) := by
      apply (mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 2)).trans
      have hh := mul_le_mul_of_nonneg_right hheightDoubleTail (Real.rpow_nonneg hU0.le (-2 * saving))
      simpa only [mul_assoc] using hh
    have hg := ordinaryReflectionEnvelope_data hD
      (pow_nonneg (zero_le_one.trans hP) (cap + 3)) (Real.rpow_nonneg hU0.le loss)
    have hcutoffCap : (2 : ℝ) ^ cutoff ≤ U ^ Bcap := by
      apply hhi.trans
      apply Real.rpow_le_rpow_of_exponent_le hU.le
      have hmax : max (a.m + a.q - long + overhead) 0 ≤ widthCap + overheadCap := by
        apply max_le
        · linarith
        · positivity
      dsimp only [Bcap]
      linarith
    have hm := hmass volume weight hg.1 hg.2.1 hg.2.2.1 U hU cutoff hcutoffCap
    have hmExact : Cm * U ^ branchLoss * (∫ t, weight t) ^ 2 =
        Cmass * (1 + T) ^ Hmass * U ^ (branchLoss + 2 * loss) := by
      rw [hg.2.2.2]
      exact reflection_height_mass_identity Cm D Cp Hp I₂ U T loss branchLoss cap hU0 hT
    have hmFinal : (reflectionCommonKernel volume weight cutoff).real Set.univ ≤
        C * (1 + T) ^ H * U ^ (branchLoss + 2 * loss) :=
      (hm.trans_eq hmExact).trans
        (mul_le_mul_of_nonneg_right hheightMass (Real.rpow_nonneg hU0.le _))
    refine ⟨hout.1, ?_, hrest, hout.2.1, hout.2.2.1, hmFinal, hout.2.2.2.1, ?_, ?_⟩
    · dsimp only [rowRestorationEnergy]
      positivity
    · intro x
      exact (Node.ordinary d a).normalizedOrdinaryPowerChildNode_reflectionArithmetic
        first (reflectionFixedLine x.1.2) (-x.2) (reflectionDyadicExponent U x.1.1)
        (P * E0) hPE childOrder U
    · apply ae_reflectionCommonKernel
      intro b hb
      apply Filter.Eventually.of_forall
      intro frequency
      have hj : b.1 ∈ Finset.range (cutoff + 1) := by
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((mem_reflectionBranches cutoff b).mp hb))
      obtain ⟨hn, _hscale, hlength⟩ := hgeometry b.1 hj
      have hgchild := (Node.ordinary d a).fixedLineReflectionChild_geometry
        first U (P * E0) hPE childOrder (b, frequency)
      have hnchild : 0 ≤ (child (b, frequency)).parameters.n₁ ∧
          0 ≤ (child (b, frequency)).parameters.n₂ := by
        cases first <;> exact ⟨by assumption, by assumption⟩
      refine ⟨hnchild.1, hnchild.2, hgchild.2.1, hgchild.1,
        hgchild.2.2.1, hgchild.2.2.2.1, ?_⟩
      rw [hgchild.2.2.2.2]
      simpa only [Node.ordinary, long, short, add_assoc, add_left_comm, add_comm] using
        (add_le_add_right (add_le_add_left hlength short) a.z)

end HeckeSkeleton.Moments.EngineInduction
