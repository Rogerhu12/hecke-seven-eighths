import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MovingReflectionCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ProfileSupremum
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ReflectionTailLedger

/-!
# Actual finite-row restoration terminals

The energy below is the square of the literal restoration tail or whole
restoration series, multiplied by the indicated original short plain
polynomial and every original prime slot, summed over the original
`pairedRows`, and divided by the original row-width power.  The actual
Boolean mask remains inside the short polynomial and slot product.

The decay order and required Euler order are chosen first.  The source
may then supply their profile constants.  Only after these choices are
the common terminal coefficient and height degree fixed, before every
moving node, height, remaining ideal, row, scale and dyadic cutoff.
The theorem proves the terminal estimate from primitive row/conductor
calibration and literal profile seminorms; no energy estimate is input.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckePort.CenteredMomentCounting HeckeSkeleton.Moments.UniformAmplify
open scoped Classical BigOperators

universe v

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- The literal normalized finite-row energy of the indicated restored
long factor, the unchanged short factor and the complete prime product.
The caller identifies `Wshort` and the annular tests with the appropriate
original plain profiles when applying the exact row reflection identity. -/
def rowRestorationEnergy (tail : Bool)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (node : Node K ω ψ) (extra : NonzeroIdeal K → NonzeroIdeal K)
    (V : NonzeroIdeal K → SmoothAnnularTest) (Wshort : IdealTest K)
    (δ U long short : ℝ) (J : ℕ) : ℝ :=
  (∑ u ∈ pairedRows node.data node.parameters U,
    ‖rowRestorationPiece tail S node.data extra V δ U long J u *
      plainPolynomial node.data Wshort u (U ^ short) 0 *
      slotProduct node.data u U 0‖ ^ 2) / U ^ node.width

/-- A convenient explicit envelope reuses the already proved common
slot and height constants. The first factor only overestimates the
restoration coefficient by the fixed ideal-count constant. -/
def restorationEnergyConstant (K : Type) [Field K] [NumberField K]
    (cap : ℕ) (b D B : ℝ) : ℝ :=
  uniformBaseConstant K cap (D * B) ((b / 2) * B) (supportProfileScale K b * B)

theorem restorationEnergyConstant_nonneg (cap : ℕ) (b D B : ℝ) :
    0 ≤ restorationEnergyConstant K cap b D B :=
  uniformBaseConstant_nonneg (K := K) cap _ _ _

/-- All height growth is polynomial, with exponent fixed by the original
profile degree and the actual uniform bound on surviving slot count. -/
theorem restorationEnergyConstant_height_le (cap : ℕ) (b D B X H : ℝ)
    (hX : 1 ≤ X) (hH : 0 ≤ H) :
    restorationEnergyConstant K cap b D (B * X ^ H) ≤
      restorationEnergyConstant K cap b D B * X ^ baseHeightDegree cap H H H := by
  simpa only [restorationEnergyConstant, mul_assoc] using
    uniformBaseConstant_height_le (K := K) cap (D * B) ((b / 2) * B)
      (supportProfileScale K b * B) X H H H hX hH

private theorem normalized_restoration_rows_le
    (tail : Bool) (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (node : Node K ω ψ) (extra : NonzeroIdeal K → NonzeroIdeal K)
    (V : NonzeroIdeal K → SmoothAnnularTest) (Wshort : IdealTest K)
    (δ U long short Q e : ℝ) (J : ℕ) (hU : 0 < U) (hQ : 0 ≤ Q)
    (hrow : ∀ u ∈ pairedRows node.data node.parameters U,
      ‖rowRestorationPiece tail S node.data extra V δ U long J u *
        plainPolynomial node.data Wshort u (U ^ short) 0 *
        slotProduct node.data u U 0‖ ^ 2 ≤ Q * U ^ e) :
    rowRestorationEnergy tail S node extra V Wshort δ U long short J ≤
      idealCountConstant K * Q * U ^ e := by
  have hc := finite_ideal_rows_count (pairedRows node.data node.parameters U)
    (U ^ node.width) (Real.rpow_pos_of_pos hU _).le
    (fun u hu => node.paired_row_norm_le hu)
  have hs : (∑ u ∈ pairedRows node.data node.parameters U,
      ‖rowRestorationPiece tail S node.data extra V δ U long J u *
        plainPolynomial node.data Wshort u (U ^ short) 0 *
        slotProduct node.data u U 0‖ ^ 2) ≤
      (idealCountConstant K * U ^ node.width) * (Q * U ^ e) := by
    calc
      _ ≤ ∑ _u ∈ pairedRows node.data node.parameters U, Q * U ^ e :=
        Finset.sum_le_sum hrow
      _ = ((pairedRows node.data node.parameters U).card : ℝ) * (Q * U ^ e) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  unfold rowRestorationEnergy
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hU node.width)).2
  exact hs.trans_eq (by ring)

private theorem rowRestorationEnergy_from_profile_bounds
    (tail : Bool) (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (node : Node K ω ψ) (extra : NonzeroIdeal K → NonzeroIdeal K)
    (V : NonzeroIdeal K → SmoothAnnularTest) (Wshort : IdealTest K)
    (cap : ℕ) (δ U long short b D B e : ℝ) (J : ℕ)
    (hU : 0 < U) (hb : 0 ≤ b) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hcount : node.data.geometry.slotCount ≤ cap)
    (hpiece : ∀ u ∈ pairedRows node.data node.parameters U,
      ‖rowRestorationPiece tail S node.data extra V δ U long J u‖ ≤ D * B * U ^ e)
    (hshortSupport : ∀ u ∈ pairedRows node.data node.parameters U,
      Function.support (Wshort.profile u 0) ⊆ Set.Iic b)
    (hshortNorm : ∀ u ∈ pairedRows node.data node.parameters U, ∀ y,
      ‖Wshort.profile u 0 y‖ ≤ B)
    (hslotSupport : ∀ i, Function.support ((node.data.geometry.slots i).profile 0) ⊆ Set.Iic b)
    (hslotNorm : ∀ i y, ‖(node.data.geometry.slots i).profile 0 y‖ ≤ B) :
    rowRestorationEnergy tail S node extra V Wshort δ U long short J ≤
      restorationEnergyConstant K cap b D B *
        U ^ (2 * e + short + node.data.geometry.totalLength) := by
  let P₁ := plainAbsoluteConstant K (D * B)
  let P₂ := plainAbsoluteConstant K ((b / 2) * B)
  let A := uniformSlotAbsoluteConstant K cap (supportProfileScale K b * B)
  have hP₁ : 0 ≤ P₁ := plainAbsoluteConstant_nonneg _ (mul_nonneg hD hB)
  have hP₂ : 0 ≤ P₂ := plainAbsoluteConstant_nonneg _ (by positivity)
  have hA : 0 ≤ A := uniformSlotAbsoluteConstant_nonneg (K := K) _ _
  have hfirst : D * B ≤ 2 * P₁ := by
    have hi := one_le_idealCountConstant K
    have hp := mul_le_mul_of_nonneg_right hi (mul_nonneg hD hB)
    dsimp only [P₁, plainAbsoluteConstant]
    nlinarith [mul_nonneg hD hB]
  have hrow (u : NonzeroIdeal K) (hu : u ∈ pairedRows node.data node.parameters U) :
      ‖rowRestorationPiece tail S node.data extra V δ U long J u *
        plainPolynomial node.data Wshort u (U ^ short) 0 *
        slotProduct node.data u U 0‖ ^ 2 ≤
      ((2 * P₁ * P₂) ^ 2 * A) * U ^ (2 * e + short + node.data.geometry.totalLength) := by
    have hr := (hpiece u hu).trans
      (mul_le_mul_of_nonneg_right hfirst (Real.rpow_nonneg hU.le e))
    have hs := plainPolynomial_absolute_bound_of_upper node.data Wshort u
      (U ^ short) 0 b B (Real.rpow_pos_of_pos hU _) hb hB
      (hshortSupport u hu) (hshortNorm u hu)
    have hp : ‖rowRestorationPiece tail S node.data extra V δ U long J u *
        plainPolynomial node.data Wshort u (U ^ short) 0‖ ≤
      (2 * P₁ * P₂) * (U ^ e * Real.sqrt (U ^ short)) := by
      rw [norm_mul]
      exact (mul_le_mul hr hs (norm_nonneg _) (by positivity)).trans_eq (by ring)
    have hp₂ : ‖rowRestorationPiece tail S node.data extra V δ U long J u *
        plainPolynomial node.data Wshort u (U ^ short) 0‖ ^ 2 ≤
      (2 * P₁ * P₂) ^ 2 * U ^ (2 * e + short) := by
      apply ((sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hp).trans_eq
      have he : (U ^ e) ^ 2 = U ^ (2 * e) := by
        rw [← Real.rpow_mul_natCast hU.le e 2]
        congr 1
        norm_num <;> ring
      calc
        _ = (2 * P₁ * P₂) ^ 2 * ((U ^ e) ^ 2 * (Real.sqrt (U ^ short)) ^ 2) := by ring
        _ = _ := by rw [he, Real.sq_sqrt (Real.rpow_nonneg hU.le _), Real.rpow_add hU]
    have hz := slotProduct_sq_uniform_bound_of_upper cap b B hb hB node.data
      hcount u U 0 hU hslotSupport hslotNorm
    rw [norm_mul, mul_pow]
    exact (mul_le_mul hp₂ hz (sq_nonneg _) (by positivity)).trans_eq (by
      rw [Real.rpow_add hU (2 * e + short) node.data.geometry.totalLength]
      ring)
  have h := normalized_restoration_rows_le tail S node extra V Wshort δ U long short
    ((2 * P₁ * P₂) ^ 2 * A) (2 * e + short + node.data.geometry.totalLength) J hU
    (mul_nonneg (sq_nonneg _) hA) hrow
  apply h.trans_eq
  unfold restorationEnergyConstant uniformBaseConstant nodeAbsoluteConstant
  dsimp only [P₁, P₂, A]
  ring

/-- Actual tail and whole-series terminal certificates.  The high decay
order and analytic Euler order precede the source profile constants;
those constants precede every moving height and node.  The joint
row/remaining-ideal budget is consumed by the arithmetic theorem, not
assumed in the form of a reflected scale or an energy estimate. -/
theorem uniform_rowRestorationEnergy_terminal
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) (ψ : HeckeCharacter K)
    (cap : ℕ) (widthCap overheadCap slotCap loss saving gap δ ε : ℝ)
    (hwidthCap : 0 ≤ widthCap) (hoverheadCap : 0 ≤ overheadCap)
    (hslotCap : 0 ≤ slotCap) (hloss : 0 ≤ loss) (hsaving : 0 ≤ saving)
    (hgap : 0 < gap) (hδ : 0 < δ) (hε : 0 < ε)
    (hmassLoss : ε * (widthCap + overheadCap) ≤ loss) :
    ∃ decay : ℝ, ∃ L : ℕ, 1 < decay ∧ δ ≤ decay ∧
      ∀ Cp Hp a b : ℝ, 0 ≤ Cp → 0 ≤ Hp → 0 < a → a ≤ b →
      ∃ C H : ℝ, 0 ≤ C ∧ 0 ≤ H ∧ H = baseHeightDegree cap Hp Hp Hp ∧
      ∀ T : ℝ, 0 ≤ T →
      ∀ (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
        (P : ProbeData K S) (R : RowCharacterInput K S P)
        (theta : Finset (HeckeCharacter K))
        {omega : HeckeCharacter K} (node : Node K omega ψ)
        (extra : NonzeroIdeal K → NonzeroIdeal K)
        (V : NonzeroIdeal K → SmoothAnnularTest) (Wshort : IdealTest K)
        (U overhead long short : ℝ) (tail : Bool) (J : ℕ),
      1 < U → 0 ≤ node.width → node.width ≤ widthCap →
      0 ≤ overhead → overhead ≤ overheadCap →
      0 ≤ long → short ≤ long → node.data.geometry.totalLength ≤ slotCap →
      node.data.geometry.slotCount ≤ cap →
      MovingReflectionRowCalibration S P R theta node extra U →
      movingReflectionConductorConstant S ψ theta ≤ U ^ overhead →
      (∀ u ∈ pairedRows node.data node.parameters U,
        SliceControl L decay Cp Hp a b T (V u).toFun) →
      (∀ u ∈ pairedRows node.data node.parameters U,
        SliceControl 1 0 Cp Hp a b T (Wshort.profile u 0)) →
      (∀ i, SliceControl 1 0 Cp Hp a b T ((node.data.geometry.slots i).profile 0)) →
      (if tail then max (node.width - long + overhead) 0 + gap ≤
          reflectionDyadicExponent U J else node.width + overhead + gap ≤ long) →
      (rowRestorationEnergy tail S node extra V Wshort δ U long short J ≤
        C * (1 + T) ^ H * U ^ (-2 * saving)) ∧
      ∀ ρ padding σ boundary : ℝ,
        Nonempty (TerminalComponents.{v}
          (rowRestorationEnergy tail S node extra V Wshort δ U long short J)
          U T C H ρ padding σ boundary) := by
  obtain ⟨decay, hdecay, hδdecay, hbudgetTail, hbudgetWhole⟩ :=
    exists_reflection_tail_decay_order widthCap overheadCap slotCap loss saving gap δ
      hwidthCap hoverheadCap hslotCap hloss hsaving hgap hδ
  obtain ⟨L, D, hD, hpieces⟩ := uniform_movingRowRestorationPiece_bound
    (K := K) hcomplex ψ hδ hδdecay hdecay hε
  refine ⟨decay, L, hdecay, hδdecay, ?_⟩
  intro Cp Hp a b hCp hHp ha hab
  let C := restorationEnergyConstant K cap b D Cp
  let H := baseHeightDegree cap Hp Hp Hp
  have hC : 0 ≤ C := restorationEnergyConstant_nonneg cap b D Cp
  have hH : 0 ≤ H := baseHeightDegree_nonneg cap hHp hHp hHp
  refine ⟨C, H, hC, hH, rfl, ?_⟩
  intro T hT S instS P R theta omega node extra V Wshort U overhead long short tail J
    hU hM hMcap hoverhead hoCap hlong hshort hzCap hcount cal hfixed
    hlongProfiles hshortProfiles hslotProfiles hcutoff
  have hU0 : 0 < U := zero_lt_one.trans hU
  have hT1 : 1 ≤ 1 + T := by linarith
  let B := Cp * (1 + T) ^ Hp
  have hB : 0 ≤ B := mul_nonneg hCp (Real.rpow_nonneg (zero_le_one.trans hT1) _)
  have hm : ε * (node.width + overhead) ≤ loss :=
    (mul_le_mul_of_nonneg_left (add_le_add hMcap hoCap) hε.le).trans hmassLoss
  let e := (decay + 1 / 2) * (node.width - long + overhead) +
    (if tail then (1 - decay) * reflectionDyadicExponent U J else 0) + loss
  have hpiece (u : NonzeroIdeal K) (hu : u ∈ pairedRows node.data node.parameters U) :
      ‖rowRestorationPiece tail S node.data extra V δ U long J u‖ ≤ D * B * U ^ e := by
    apply (hpieces S P R theta node extra V U overhead long loss hU cal hfixed hm tail J u hu).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hlongProfiles u hu).2.2 hD) (Real.rpow_nonneg hU0.le _)
  have henergy := rowRestorationEnergy_from_profile_bounds tail S node extra V Wshort cap
    δ U long short b D B e J hU0 (ha.le.trans hab) hD hB hcount hpiece
    (fun u hu y hy => ((hshortProfiles u hu).2.1 y hy).2)
    (fun u hu y => sliceControl_norm_le le_rfl ha hab (hshortProfiles u hu) y)
    (fun i y hy => ((hslotProfiles i).2.1 y hy).2)
    (fun i y => sliceControl_norm_le le_rfl ha hab (hslotProfiles i) y)
  have hexponent : 2 * e + short + node.data.geometry.totalLength ≤ -2 * saving := by
    cases tail with
    | false =>
      simp only [Bool.false_eq_true, if_false] at hcutoff
      have h := reflection_whole_tail_uniform_exponent node.width overhead long short
        node.data.geometry.totalLength decay gap loss saving widthCap overheadCap slotCap
        hshort (by linarith) hcutoff hMcap hoCap hzCap hbudgetWhole
      dsimp only [e]
      simp only [Bool.false_eq_true, if_false, add_zero]
      linarith
    | true =>
      simp only [if_true] at hcutoff
      have h := reflection_dyadic_tail_uniform_exponent node.width overhead long short
        node.data.geometry.totalLength decay gap (reflectionDyadicExponent U J)
        loss saving widthCap overheadCap slotCap hM hoverhead hlong hshort hdecay.le
        hMcap hoCap hzCap hcutoff hbudgetTail
      dsimp only [e]
      simp only [if_true]
      linarith
  have hfinal : rowRestorationEnergy tail S node extra V Wshort δ U long short J ≤
      C * (1 + T) ^ H * U ^ (-2 * saving) := by
    apply henergy.trans
    exact mul_le_mul
      (restorationEnergyConstant_height_le (K := K) cap b D Cp (1 + T) Hp hT1 hHp)
      (Real.rpow_le_rpow_of_exponent_le hU.le hexponent)
      (Real.rpow_nonneg hU0.le _) (mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans hT1) _))
  refine ⟨hfinal, ?_⟩
  intro ρ padding σ boundary
  refine ⟨{
    Label := ULift.{v} Unit
    terms := {⟨()⟩}
    coefficient := fun _ => C * (1 + T) ^ H
    exponent := fun _ => -2 * saving
    coefficient_nonneg := ?_
    estimate := ?_
    mass := ?_
    ledger := ?_ }⟩
  · intro j hj
    exact mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans hT1) _)
  · simpa only [Finset.sum_singleton] using hfinal
  · simp only [Finset.sum_singleton, le_refl]
  · intro j hj
    exact TerminalLedger.tail (by linarith)

end HeckeSkeleton.Moments.EngineInduction
