import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualExceptionalAmplitude
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualExceptionalRows

/-!
# Actual paired exceptional rows

Each value below is an original allocated centered finite polynomial.
Its exceptional character/profile chart is pointwise in one ideal.
The left amplitude uses the genuine centered volume estimate once; the
right uses only the ordinary absolute volume bound. The row count comes
from the actual extracted frequency and its sixth-power classification.

The remaining normalization input is explicitly the product of computed
frozen norms, finite per-prime L1 masses, and the two formal square roots.
It contains neither a whole polynomial norm nor an exceptional row sum.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.Moments.Twist HeckePort.CenteredMomentVolume
open HeckePort.CenteredMomentCounting UniqueFactorizationMonoid

set_option maxHeartbeats 4000000

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace ExceptionalVolumeControl

variable {Ψ : Ideal (𝓞 F) →* ℂ} {W₁ W₂ : ℝ → ℂ}

def absoluteConstant (H : ExceptionalVolumeControl Ψ W₁ W₂) : ℝ :=
  (idealCountConstant F * H.upper₁ * H.bound₁) *
    (idealCountConstant F * H.upper₂ * H.bound₂)

theorem absoluteConstant_nonneg (H : ExceptionalVolumeControl Ψ W₁ W₂) :
    0 ≤ H.absoluteConstant := by
  have hcount := zero_le_one.trans (one_le_idealCountConstant F)
  exact mul_nonneg
    (mul_nonneg (mul_nonneg hcount H.upper₁_nonneg) H.bound₁_nonneg)
    (mul_nonneg (mul_nonneg hcount H.upper₂_nonneg) H.bound₂_nonneg)

private theorem normalized_product_absolute (H : ExceptionalVolumeControl Ψ W₁ W₂)
    (R : Ideal (𝓞 F)) (t X₁ X₂ Q : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hp : X₁ * X₂ = Q) :
    ‖(Real.sqrt Q : ℂ)⁻¹ *
      (twistedMaskedSum Ψ R W₁ t X₁ * twistedMaskedSum Ψ R W₂ t X₂)‖ ≤
        H.absoluteConstant * Real.sqrt Q := by
  have h₁ := twistedMaskedSum_absolute H.coefficient_norm H.coefficient_zero R
    W₁ H.lower₁ H.upper₁ H.lower₁_pos H.support₁ H.profile₁ H.profile₁_eq
    H.bound₁ H.upper₁_nonneg H.bound₁_nonneg H.norm₁ t X₁ hX₁
  have h₂ := twistedMaskedSum_absolute H.coefficient_norm H.coefficient_zero R
    W₂ H.lower₂ H.upper₂ H.lower₂_pos H.support₂ H.profile₂ H.profile₂_eq
    H.bound₂ H.upper₂_nonneg H.bound₂_nonneg H.norm₂ t X₂ hX₂
  have hQ : 0 < Q := hp ▸ mul_pos hX₁ hX₂
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hd : Q / Real.sqrt Q = Real.sqrt Q := by
    apply (div_eq_iff hroot.ne').mpr
    nlinarith [Real.sq_sqrt hQ.le]
  have hcount := zero_le_one.trans (one_le_idealCountConstant F)
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg Q), norm_mul]
  calc
    _ ≤ (Real.sqrt Q)⁻¹ *
        ((idealCountConstant F * H.upper₁ * H.bound₁ * X₁) *
          (idealCountConstant F * H.upper₂ * H.bound₂ * X₂)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul h₁ h₂ (norm_nonneg _)
          (mul_nonneg (mul_nonneg (mul_nonneg hcount H.upper₁_nonneg)
            H.bound₁_nonneg) hX₁.le)) (inv_nonneg.mpr hroot.le)
    _ = H.absoluteConstant * (Q / Real.sqrt Q) := by
      rw [← hp]
      unfold absoluteConstant
      ring
    _ = _ := by rw [hd]

/-- The ordinary bound for the other centered factor uses two absolute
rectangles and introduces no second centered saving. -/
theorem rectangle_absolute (H : ExceptionalVolumeControl Ψ W₁ W₂)
    (R : Ideal (𝓞 F)) (t X₁ X₂ Y₁ Y₂ Q : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hpX : X₁ * X₂ = Q) (hpY : Y₁ * Y₂ = Q) :
    ‖normalizedMaskedRectangle Ψ R W₁ W₂ t X₁ X₂ Y₁ Y₂ Q‖ ≤
      (2 * H.absoluteConstant) * Real.sqrt Q := by
  unfold normalizedMaskedRectangle
  rw [mul_sub]
  exact (norm_sub_le _ _).trans (by
    have hx := H.normalized_product_absolute R t X₁ X₂ Q hX₁ hX₂ hpX
    have hy := H.normalized_product_absolute R t Y₁ Y₂ Q hY₁ hY₂ hpY
    linarith)

end ExceptionalVolumeControl

/-- Actual finite source data after a genuine allocation. The frequency
arguments are parameters, so they can be the literal extracted row.
All four profile fields are single-ideal dictionaries, not sum identities. -/
structure AllocatedExceptionalSource
    (Ψ : Ideal (𝓞 F) →* ℂ) (W₁ W₂ : ℝ → ℂ) (g h' : A.R) (k : ℕ) where
  allocation : ActualColumnAllocation F k
  characters : FixedChildCharacters F k
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ
  Zslot : ℝ
  length : Fin k → ℝ
  w₁ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ
  w₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ
  v₁ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ
  v₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ
  w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ
  x₁ : HeckeGeneral.Analysis.NonzeroIdeal F → V
  x₂ : HeckeGeneral.Analysis.NonzeroIdeal F → V
  x : Fin k → HeightOneSpectrum (𝓞 F) → V
  ξ : V
  mask : Ideal (𝓞 F)
  time : ℝ
  product : ℝ
  lower : ℝ
  lower_pos : 0 < lower
  X₁_lower : lower ≤ X₁ / idealNorm F (allocation.plainDivisor 0)
  X₂_lower : lower ≤ X₂ / idealNorm F (allocation.plainDivisor (Fin.succ 0))
  Y₁_lower : lower ≤ Y₁ / idealNorm F (allocation.plainDivisor 0)
  Y₂_lower : lower ≤ Y₂ / idealNorm F (allocation.plainDivisor (Fin.succ 0))
  productX : (X₁ / idealNorm F (allocation.plainDivisor 0)) *
    (X₂ / idealNorm F (allocation.plainDivisor (Fin.succ 0))) = product
  productY : (Y₁ / idealNorm F (allocation.plainDivisor 0)) *
    (Y₂ / idealNorm F (allocation.plainDivisor (Fin.succ 0))) = product
  chartX₁ : ExceptionalPlainChart (σ := σ) characters.plain characters.plainTwist characters.mask
    g h' Ψ mask W₁ time (X₁ / idealNorm F (allocation.plainDivisor 0)) allocation.childPlain₁
    (fun I => w₁ (allocation.plainDivisor 0 * I))
    (fun I => x₁ (allocation.plainDivisor 0 * I)) ξ
  chartX₂ : ExceptionalPlainChart (σ := σ) characters.plain characters.plainTwist characters.mask
    g h' Ψ mask W₂ time (X₂ / idealNorm F (allocation.plainDivisor (Fin.succ 0))) allocation.childPlain₂
    (fun I => w₂ (allocation.plainDivisor (Fin.succ 0) * I))
    (fun I => x₂ (allocation.plainDivisor (Fin.succ 0) * I)) ξ
  chartY₁ : ExceptionalPlainChart (σ := σ) characters.plain characters.plainTwist characters.mask
    g h' Ψ mask W₁ time (Y₁ / idealNorm F (allocation.plainDivisor 0)) allocation.childPlain₁
    (fun I => v₁ (allocation.plainDivisor 0 * I))
    (fun I => x₁ (allocation.plainDivisor 0 * I)) ξ
  chartY₂ : ExceptionalPlainChart (σ := σ) characters.plain characters.plainTwist characters.mask
    g h' Ψ mask W₂ time (Y₂ / idealNorm F (allocation.plainDivisor (Fin.succ 0))) allocation.childPlain₂
    (fun I => v₂ (allocation.plainDivisor (Fin.succ 0) * I))
    (fun I => x₂ (allocation.plainDivisor (Fin.succ 0) * I)) ξ

namespace AllocatedExceptionalSource

variable {Ψ : Ideal (𝓞 F) →* ℂ} {W₁ W₂ : ℝ → ℂ} {g h' : A.R} {k : ℕ}

def value (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h' k) : ℂ :=
  jointFourierColumn s.allocation.columns
    (fun y => rawSourceCoefficient (σ := σ) s.characters g h'
      s.X₁ s.X₂ s.Zslot s.length s.w₁ s.w₂ s.w y -
      rawSourceCoefficient (σ := σ) s.characters g h'
        s.Y₁ s.Y₂ s.Zslot s.length s.v₁ s.v₂ s.w y)
    (rawSourceLocation s.x₁ s.x₂ s.x) s.ξ

def slotMass (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h' k) : ℝ :=
  ∏ j, ∑ p ∈ s.allocation.childSlots j,
    ‖sourcePrimeTerm (σ := σ) ((s.characters.restrictSlots s.allocation.keep).slot j)
      ((s.characters.restrictSlots s.allocation.keep).slotTwist j)
      (s.characters.restrictSlots s.allocation.keep).mask g h'
      (s.w (SlotRestriction.index s.allocation.keep j))
      (s.Zslot ^ s.length (SlotRestriction.index s.allocation.keep j)) p‖

/-- Only the computed frozen norm, actual per-prime finite masses, and
the formal rectangle square root occur in this raw normalization. -/
def rawMass (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h' k) : ℝ :=
  ‖s.allocation.scalar (σ := σ) s.characters g h' s.Zslot s.length s.w‖ *
    s.slotMass * Real.sqrt s.product

theorem slotMass_nonneg (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h' k) :
    0 ≤ s.slotMass :=
  Finset.prod_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))

theorem rawMass_nonneg (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h' k) :
    0 ≤ s.rawMass :=
  mul_nonneg (mul_nonneg (norm_nonneg _) s.slotMass_nonneg) (Real.sqrt_nonneg _)

private theorem prime_card_le (S : Finset (HeightOneSpectrum (𝓞 F)))
    (X : ℝ) (hX : 1 ≤ X) (hnorm : ∀ p ∈ S, (Ideal.absNorm p.asIdeal : ℝ) ≤ X) :
    (S.card : ℝ) ≤ idealCountConstant F * X := by
  have hinj : Function.Injective (HeightOneSpectrum.asIdeal : HeightOneSpectrum (𝓞 F) → _) :=
    fun p q h => HeightOneSpectrum.ext h
  have hc := card_le_idealCountConstant F (S.image HeightOneSpectrum.asIdeal) X hX (by
    intro I hI
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI
    exact hnorm p hp)
  simpa only [Finset.card_image_of_injective _ hinj] using hc

/-- The raw normalization itself follows from individual prime norm
and coefficient windows and the ordinary ideal-count theorem. This
lemma introduces no whole slot-polynomial or energy estimate premise. -/
theorem rawMass_le_prime_windows
    (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h' k)
    (frozenBound rootBound : ℝ) (hfrozen : 0 ≤ frozenBound) (hroot : 0 ≤ rootBound)
    (hscalar : ‖s.allocation.scalar (σ := σ) s.characters g h' s.Zslot s.length s.w‖ ≤ frozenBound)
    (hproduct : Real.sqrt s.product ≤ rootBound)
    (normCutoff primeBound : Fin s.allocation.keep.card → ℝ)
    (hcutoff : ∀ j, 1 ≤ normCutoff j) (hbound : ∀ j, 0 ≤ primeBound j)
    (hprime : ∀ j, ∀ p ∈ s.allocation.childSlots j,
      (Ideal.absNorm p.asIdeal : ℝ) ≤ normCutoff j)
    (hterm : ∀ j, ∀ p ∈ s.allocation.childSlots j,
      ‖sourcePrimeTerm (σ := σ) ((s.characters.restrictSlots s.allocation.keep).slot j)
        ((s.characters.restrictSlots s.allocation.keep).slotTwist j)
        (s.characters.restrictSlots s.allocation.keep).mask g h'
        (s.w (SlotRestriction.index s.allocation.keep j))
        (s.Zslot ^ s.length (SlotRestriction.index s.allocation.keep j)) p‖ ≤ primeBound j) :
    s.rawMass ≤ frozenBound * rootBound *
      ∏ j, (idealCountConstant F * normCutoff j) * primeBound j := by
  have hcount : 0 ≤ idealCountConstant F := zero_le_one.trans (one_le_idealCountConstant F)
  have hp : s.slotMass ≤ ∏ j, (idealCountConstant F * normCutoff j) * primeBound j := by
    apply Finset.prod_le_prod₀
    · intro j hj
      exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    · intro j hj
      calc
        _ ≤ ∑ _p ∈ s.allocation.childSlots j, primeBound j :=
          Finset.sum_le_sum (fun p hp => hterm j p hp)
        _ = ((s.allocation.childSlots j).card : ℝ) * primeBound j := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (prime_card_le (s.allocation.childSlots j) (normCutoff j) (hcutoff j) (hprime j)) (hbound j)
  have hp0 : 0 ≤ ∏ j, (idealCountConstant F * normCutoff j) * primeBound j :=
    Finset.prod_nonneg (fun j _ => mul_nonneg
      (mul_nonneg hcount (zero_le_one.trans (hcutoff j))) (hbound j))
  have hm := mul_le_mul (mul_le_mul hscalar hp s.slotMass_nonneg hfrozen)
    hproduct (Real.sqrt_nonneg _) (mul_nonneg hfrozen hp0)
  convert hm using 1 <;> first | rfl | (dsimp only [rawMass]; ring) | ring

theorem identity (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h' k)
    (hΨ0 : Ψ ⊥ = 0) :
    s.value = s.allocation.scalar (σ := σ) s.characters g h' s.Zslot s.length s.w *
      jointPhase s.ξ (frozenSourceLocation s.allocation.keep s.allocation.witness.2 s.x) *
        (normalizedMaskedRectangle Ψ s.mask W₁ W₂ s.time
          (s.X₁ / idealNorm F (s.allocation.plainDivisor 0))
          (s.X₂ / idealNorm F (s.allocation.plainDivisor (Fin.succ 0)))
          (s.Y₁ / idealNorm F (s.allocation.plainDivisor 0))
          (s.Y₂ / idealNorm F (s.allocation.plainDivisor (Fin.succ 0))) s.product *
          actualSourceSlotPolynomial (σ := σ) (s.characters.restrictSlots s.allocation.keep)
            g h' s.Zslot (fun j => s.length (SlotRestriction.index s.allocation.keep j))
            s.allocation.childSlots (fun j => s.w (SlotRestriction.index s.allocation.keep j))
            (fun j => s.x (SlotRestriction.index s.allocation.keep j)) s.ξ) :=
  s.allocation.centered_source_rectangle s.characters g h' s.X₁ s.X₂ s.Y₁ s.Y₂
    s.Zslot s.length s.w₁ s.w₂ s.v₁ s.v₂ s.w s.x₁ s.x₂ s.x s.ξ Ψ hΨ0 s.mask W₁ W₂
    s.time s.product (s.lower_pos.le.trans s.X₁_lower) (s.lower_pos.le.trans s.Y₁_lower)
    s.productX s.productY s.chartX₁ s.chartX₂ s.chartY₁ s.chartY₂

theorem absolute (H : ExceptionalVolumeControl Ψ W₁ W₂)
    (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h' k) :
    ‖s.value‖ ≤ (1 + 2 * H.absoluteConstant) * s.rawMass := by
  have hr := H.rectangle_absolute s.mask s.time
    (s.X₁ / idealNorm F (s.allocation.plainDivisor 0))
    (s.X₂ / idealNorm F (s.allocation.plainDivisor (Fin.succ 0)))
    (s.Y₁ / idealNorm F (s.allocation.plainDivisor 0))
    (s.Y₂ / idealNorm F (s.allocation.plainDivisor (Fin.succ 0))) s.product
    (s.lower_pos.trans_le s.X₁_lower) (s.lower_pos.trans_le s.X₂_lower)
    (s.lower_pos.trans_le s.Y₁_lower) (s.lower_pos.trans_le s.Y₂_lower) s.productX s.productY
  have hs := norm_actualSourceSlotPolynomial_le (σ := σ) (s.characters.restrictSlots s.allocation.keep)
    g h' s.Zslot (fun j => s.length (SlotRestriction.index s.allocation.keep j))
    s.allocation.childSlots (fun j => s.w (SlotRestriction.index s.allocation.keep j))
    (fun j => s.x (SlotRestriction.index s.allocation.keep j)) s.ξ
  have hr0 : 0 ≤ (2 * H.absoluteConstant) * Real.sqrt s.product :=
    mul_nonneg (mul_nonneg (by norm_num) H.absoluteConstant_nonneg) (Real.sqrt_nonneg _)
  have hh : ‖s.value‖ ≤ (2 * H.absoluteConstant) * s.rawMass := by
    rw [s.identity H.coefficient_zero, norm_mul, norm_mul, norm_mul, norm_jointPhase, mul_one]
    have hm := mul_le_mul_of_nonneg_left
      (mul_le_mul hr hs (norm_nonneg _) hr0)
      (norm_nonneg (s.allocation.scalar (σ := σ) s.characters g h' s.Zslot s.length s.w))
    convert hm using 1 <;> dsimp only [rawMass, slotMass] <;> ring
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) s.rawMass_nonneg)

/-- This selects the centered constant before every actual source.
Only this one side receives the inverse lower-scale saving. -/
theorem centered_uniform (H : ExceptionalVolumeControl Ψ W₁ W₂)
    (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent) :
    ∃ J : ℕ, ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ {g h' : A.R} {k : ℕ}
        (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h' k),
      s.mask ≠ ⊥ → (Ideal.absNorm s.mask : ℝ) ≤ Z ^ maskExponent →
      ‖s.value‖ ≤ Cbound * Z ^ ε * (1 + ‖s.time‖) ^ J * (s.rawMass / s.lower) := by
  obtain ⟨J, Cbound, hCbound, hb⟩ := H.allocated_centered_amplitude (V := V) (σ := σ)
    ε maskExponent hε hmask
  refine ⟨J, Cbound, hCbound, ?_⟩
  intro Z hZ g h' k s hR hnorm
  have hs := hb Z hZ s.mask hR hnorm s.allocation s.characters g h'
    s.X₁ s.X₂ s.Y₁ s.Y₂ s.Zslot s.length s.w₁ s.w₂ s.v₁ s.v₂ s.w
    s.x₁ s.x₂ s.x s.ξ s.time s.product s.lower s.lower_pos
    s.X₁_lower s.X₂_lower s.Y₁_lower s.Y₂_lower s.productX s.productY
    s.chartX₁ s.chartX₂ s.chartY₁ s.chartY₂
  convert hs using 1 <;> dsimp only [value, rawMass, slotMass] <;> ring

/-- Formal plain scales are retained.  A positive lower length uses the
single centered saving; a nonpositive length uses the actual absolute
volume bound.  No clipping to one is imposed on an exceptional source. -/
theorem centered_or_absolute_uniform (H : ExceptionalVolumeControl Ψ W₁ W₂)
    (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent) :
    ∃ J : ℕ, ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ {g h' : A.R} {k : ℕ}
        (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h' k),
      s.mask ≠ ⊥ → (Ideal.absNorm s.mask : ℝ) ≤ Z ^ maskExponent →
      ∀ L : ℝ, Z ^ L ≤ s.lower →
      ‖s.value‖ ≤ Cbound * Z ^ ε * (1 + ‖s.time‖) ^ J * s.rawMass * Z ^ (-max L 0) := by
  obtain ⟨J, Ccenter, hCcenter, hc⟩ := centered_uniform (V := V) (σ := σ) H
    ε maskExponent hε hmask
  let Cabs := 1 + 2 * H.absoluteConstant
  have hCabs : 0 < Cabs := by
    dsimp only [Cabs]
    linarith [H.absoluteConstant_nonneg]
  let Cbound := Ccenter + Cabs
  have hCb : 0 < Cbound := add_pos hCcenter hCabs
  refine ⟨J, Cbound, hCb, ?_⟩
  intro Z hZ g h' k s hR hmasknorm L hLbound
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have htime : 0 ≤ (1 + ‖s.time‖) ^ J := pow_nonneg (by positivity) J
  by_cases hL : 0 ≤ L
  · rw [max_eq_left hL]
    have hinv : s.lower⁻¹ ≤ Z ^ (-L) := by
      simpa only [one_div, Real.rpow_neg hZpos.le] using
        one_div_le_one_div_of_le (Real.rpow_pos_of_pos hZpos L) hLbound
    have hcoeff : Ccenter * Z ^ ε * (1 + ‖s.time‖) ^ J ≤
        Cbound * Z ^ ε * (1 + ‖s.time‖) ^ J := by
      apply mul_le_mul_of_nonneg_right _ htime
      exact mul_le_mul_of_nonneg_right (by dsimp only [Cbound]; linarith)
        (Real.rpow_nonneg hZpos.le _)
    have hm := mul_le_mul hcoeff (mul_le_mul_of_nonneg_left hinv s.rawMass_nonneg)
      (mul_nonneg s.rawMass_nonneg (inv_nonneg.mpr s.lower_pos.le))
      (mul_nonneg (mul_nonneg hCb.le (Real.rpow_nonneg hZpos.le _)) htime)
    have hb := hc Z hZ s hR hmasknorm
    apply hb.trans
    simpa only [div_eq_mul_inv, mul_assoc] using hm
  · rw [max_eq_right (le_of_not_ge hL), neg_zero, Real.rpow_zero, mul_one]
    have hpow : 1 ≤ Z ^ ε := Real.one_le_rpow hZ hε.le
    have hheight : 1 ≤ (1 + ‖s.time‖) ^ J := one_le_pow₀ (by linarith [norm_nonneg s.time])
    have hprod : 1 ≤ Z ^ ε * (1 + ‖s.time‖) ^ J := by
      simpa only [one_mul] using mul_le_mul hpow hheight zero_le_one (zero_le_one.trans hpow)
    have hcoefficient : Cabs ≤ Cbound * Z ^ ε * (1 + ‖s.time‖) ^ J := by
      apply (show Cabs ≤ Cbound by dsimp only [Cbound]; linarith).trans
      simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hprod hCb.le
    exact (s.absolute H).trans (mul_le_mul_of_nonneg_right hcoefficient s.rawMass_nonneg)

end AllocatedExceptionalSource

private theorem positive_part_after_extraction (L r : ℝ) (hr : 0 ≤ r) :
    max (L - r) 0 = max (max L 0 - r) 0 := by
  rcases le_total 0 L with hL | hL
  · rw [max_eq_left hL]
  · have hLr : L - r ≤ 0 := by linarith
    have h0r : 0 - r ≤ 0 := by linarith
    simp only [max_eq_right hL, max_eq_right hLr, max_eq_right h0r]

variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- The actual normalized exceptional contribution. The count comes
from the original frequency valuations and its genuine residual ideal;
both amplitudes are actual allocated finite polynomials. The only size
premise on the source is the displayed raw normalization of frozen
scalars, finite prime masses, and formal square roots. The equal-multiplicity
radical length `v` and the centered extraction length `vStar` are distinct.
The final divisor dyad is retained as `Z ^ (slotError - divisorLower)`;
its actual carrier count is paid outside this per-dyad estimate.
The two literal source factors are independent parameters so that the
actual pair can use the extracted factor and its negative, and either
side may receive the single centered saving. -/
theorem actual_exceptional_paired_contribution
    {Ψleft Ψright : Ideal (𝓞 F) →* ℂ} {WL₁ WL₂ WR₁ WR₂ : ℝ → ℂ}
    (HL : ExceptionalVolumeControl Ψleft WL₁ WL₂)
    (HR : ExceptionalVolumeControl Ψright WR₁ WR₂)
    (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent) :
    ∃ J : ℕ, ∃ Cbound : ℝ, 0 < Cbound ∧
    ∀ {ι HRows : Type*} [Fintype ι] [DecidableEq ι]
      (C : A.GeneralArithmeticContext σ η hS)
      (p : ι → ExteriorPrime A) (hp : Function.Injective p)
      (mult₁ mult₂ : ι → ℕ)
      (rows : Finset HRows) (Ih : HRows → A.Exterior) (frequency : HRows → A.R)
      (r : ∀ x, ActualExceptionalRow C p mult₁ mult₂ (Ih x) (frequency x))
      (base : Ideal (𝓞 F))
      (leftFactor rightFactor : HRows → A.R)
      (Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v vStar
        r₁ r₂ divisorLower slotError sectors Cnormal height stepσ δ : ℝ),
    1 ≤ Z → 0 ≤ v → 0 ≤ r₁ → divisorLower - r₂ ≤ slotError →
    0 ≤ sectors → 0 ≤ Cnormal → 0 ≤ height →
    let a₀ := Aexp - c - w
    let K₀ := 2 * Aexp - c - d + R₀ + E₀ - m
    let mChild := 2 * a₀ - K - g - g₂ - V₀
    let qChild := q + R₀ + E₀ + wo + t₂ + V₀
    let Δ := b₂ - p₂ + w + Bcommon + ell
    let F₁ := firstSaving c (d + K₀ - K) w (q + R₀ + E₀) wo Bcommon g ell
    let F₂ := 2 * b₂ - 5 * g₂ / 6 - p₂ + t₂ + V₀ / 6 + (2 * v) / 6
    (∀ x ∈ rows, ∀ i ∈ multiplicityOneNonunitPrimes C p mult₁ mult₂ (frequency x),
      6 ∣ (normalizedFactors (Ih x).val).count (p i).val.asIdeal) →
    (∀ x ∈ rows, ∃ a : Ideal (𝓞 F), (r x).ideal.val = base * a ^ 6) →
    (∀ x ∈ rows, Z ^ v ≤
      A.exteriorNorm (multiplicityOneNonunitRadical C p mult₁ mult₂ (frequency x))) →
    (∀ x ∈ rows, A.exteriorNorm (Ih x) ≤
      ((Ideal.absNorm (gcd (primePowerProduct p mult₁).val (primePowerProduct p mult₂).val) : ℝ) *
        A.exteriorNorm (nonunitFrequencyRadical C p mult₁ mult₂ (frequency x))) * Z ^ mChild) →
    (∀ I ∈ rows.image (fun x => (r x).ideal.val),
      ((rows.filter (fun x => (r x).ideal.val = I)).card : ℝ) ≤ sectors) →
    2 * (c + w) / 3 - 3 * stepσ - 5 * δ / 6 ≤ F₁ →
    2 * b₂ / 3 ≤ F₂ → vStar ≤ c + w + b₂ →
    ∀ {kleft kright : ℕ}
      (left : ∀ x, AllocatedExceptionalSource (V := V) (σ := σ)
        Ψleft WL₁ WL₂ (leftFactor x) (r x).element kleft)
      (right : ∀ x, AllocatedExceptionalSource (V := V) (σ := σ)
        Ψright WR₁ WR₂ (rightFactor x) (r x).element kright),
    (∀ x ∈ rows, (left x).mask ≠ ⊥) →
    (∀ x ∈ rows, (Ideal.absNorm (left x).mask : ℝ) ≤ Z ^ maskExponent) →
    (∀ x ∈ rows, ‖(left x).time‖ ≤ height) →
    (∀ x ∈ rows, Z ^ ((m + q) / 4 - vStar - r₁) ≤ (left x).lower) →
    (∀ x ∈ rows, (left x).rawMass * (right x).rawMass ≤
      Cnormal * Z ^ (a₀ - b₂ - r₁ - r₂)) →
    Z ^ (-(mChild + qChild + Δ)) *
      (∑ x ∈ rows, ‖(left x).value‖ * ‖(right x).value‖) ≤
      (sectors * Cbound * Cnormal) * (1 + height) ^ J *
        Z ^ (max (Aexp - (m + q)) 0 + 3 * stepσ + 5 * δ / 6 + ε +
          slotError - divisorLower) := by
  obtain ⟨J, Cleft, hCleft, hleftBound⟩ :=
    AllocatedExceptionalSource.centered_or_absolute_uniform (V := V) (σ := σ)
      HL ε maskExponent hε hmask
  let Cright := 1 + 2 * HR.absoluteConstant
  have hCright : 0 < Cright := by
    dsimp only [Cright]
    linarith [HR.absoluteConstant_nonneg]
  have hcount : 0 < idealCountConstant F := zero_lt_one.trans_le (one_le_idealCountConstant F)
  let Cbound := Cleft * Cright * idealCountConstant F
  refine ⟨J, Cbound, mul_pos (mul_pos hCleft hCright) hcount, ?_⟩
  intro ι HRows instFintype instDecidableEq C p hp mult₁ mult₂ rows Ih frequency r base
    leftFactor rightFactor
    Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v vStar
    r₁ r₂ divisorLower slotError sectors Cnormal height stepσ δ
    hZ hv hr₁ hdivisor hsectors hCnormal hheight
  dsimp only
  intro hclass hfactor hwindow hcutoff hfiber hF₁ hF₂ hvsum kleft kright
    left right hmask0 hmasknorm htime hminimum hnormal
  let a₀ := Aexp - c - w
  let K₀ := 2 * Aexp - c - d + R₀ + E₀ - m
  let mChild := 2 * a₀ - K - g - g₂ - V₀
  let qChild := q + R₀ + E₀ + wo + t₂ + V₀
  let Δ := b₂ - p₂ + w + Bcommon + ell
  let normExp := mChild + qChild + Δ
  let rawExp := a₀ - b₂ - r₁ - r₂
  let rowExp := (mChild - 2 * v) / 6
  let saving := max ((m + q) / 4 - vStar - r₁) 0
  let F₁ := firstSaving c (d + K₀ - K) w (q + R₀ + E₀) wo Bcommon g ell
  let F₂ := 2 * b₂ - 5 * g₂ / 6 - p₂ + t₂ + V₀ / 6 + (2 * v) / 6
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hrows : (rows.card : ℝ) ≤ sectors * idealCountConstant F * Z ^ rowExp :=
    actual_exceptional_sector_count C p hp mult₁ mult₂ rows Ih frequency r base
      hclass hfactor Z mChild v sectors hZ hv hsectors hwindow hcutoff hfiber
  have hheightpow : 0 ≤ (1 + height) ^ J := pow_nonneg (by linarith) J
  let U := (Cleft * Cright * Cnormal) * (1 + height) ^ J * Z ^ (rawExp + ε - saving)
  have hU : 0 ≤ U := mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg hCleft.le hCright.le) hCnormal) hheightpow)
    (Real.rpow_nonneg hZpos.le _)
  have hpoint (x) (hx : x ∈ rows) : ‖(left x).value‖ * ‖(right x).value‖ ≤ U := by
    have hl := hleftBound Z hZ (left x) (hmask0 x hx) (hmasknorm x hx)
      ((m + q) / 4 - vStar - r₁) (hminimum x hx)
    have hr := (right x).absolute HR
    have hp : (1 + ‖(left x).time‖) ^ J ≤ (1 + height) ^ J :=
      pow_le_pow_left₀ (by positivity) (by linarith [htime x hx]) J
    have hl' : ‖(left x).value‖ ≤
        Cleft * Z ^ ε * (1 + height) ^ J * (left x).rawMass * Z ^ (-saving) :=
      hl.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp
            (mul_nonneg hCleft.le (Real.rpow_nonneg hZpos.le _)))
          (left x).rawMass_nonneg) (Real.rpow_nonneg hZpos.le _))
    have hl0 : 0 ≤ Cleft * Z ^ ε * (1 + height) ^ J *
        (left x).rawMass * Z ^ (-saving) :=
      mul_nonneg (mul_nonneg
        (mul_nonneg (mul_nonneg hCleft.le (Real.rpow_nonneg hZpos.le _)) hheightpow)
        (left x).rawMass_nonneg) (Real.rpow_nonneg hZpos.le _)
    have hraw := mul_le_mul_of_nonneg_right (hnormal x hx)
      (Real.rpow_nonneg hZpos.le (-saving))
    calc
      _ ≤ (Cleft * Z ^ ε * (1 + height) ^ J * (left x).rawMass * Z ^ (-saving)) *
          (Cright * (right x).rawMass) := mul_le_mul hl' hr (norm_nonneg _) hl0
      _ = (Cleft * Cright * Z ^ ε * (1 + height) ^ J) *
          (((left x).rawMass * (right x).rawMass) * Z ^ (-saving)) := by ring
      _ ≤ (Cleft * Cright * Z ^ ε * (1 + height) ^ J) *
          ((Cnormal * Z ^ rawExp) * Z ^ (-saving)) :=
        mul_le_mul_of_nonneg_left hraw
          (mul_nonneg (mul_nonneg (mul_nonneg hCleft.le hCright.le)
            (Real.rpow_nonneg hZpos.le _)) hheightpow)
      _ = U := by
        dsimp only [U]
        rw [show rawExp + ε - saving = ε + (rawExp + -saving) by ring,
          Real.rpow_add hZpos, Real.rpow_add hZpos]
        ring
  have hsum : (∑ x ∈ rows, ‖(left x).value‖ * ‖(right x).value‖) ≤ (rows.card : ℝ) * U := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hpoint
  have hid := exceptional_excess_identity
    Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ (2 * v)
  change (mChild - 2 * v) / 6 + a₀ - b₂ - normExp =
    Aexp - 5 * (m + q) / 6 - F₁ - F₂ at hid
  have hledger := exceptional_paired_exponent Aexp (m + q) c w b₂ vStar F₁ F₂ stepσ δ
    hF₁ hF₂ hvsum
  have hdiv := centered_divisor_saving divisorLower r₁ r₂
    (max ((m + q) / 4 - vStar) 0) slotError hdivisor
  rw [← positive_part_after_extraction ((m + q) / 4 - vStar) r₁ hr₁] at hdiv
  have he : -normExp + rowExp + (rawExp + ε - saving) ≤
      max (Aexp - (m + q)) 0 + 3 * stepσ + 5 * δ / 6 + ε +
        slotError - divisorLower := by
    dsimp only [rowExp, rawExp, saving]
    linarith [hid, hledger, hdiv]
  change Z ^ (-normExp) * (∑ x ∈ rows, ‖(left x).value‖ * ‖(right x).value‖) ≤ _
  calc
    _ ≤ Z ^ (-normExp) * ((rows.card : ℝ) * U) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hZpos.le _)
    _ ≤ Z ^ (-normExp) * ((sectors * idealCountConstant F * Z ^ rowExp) * U) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrows hU)
        (Real.rpow_nonneg hZpos.le _)
    _ = (sectors * Cbound * Cnormal) * (1 + height) ^ J *
        Z ^ (-normExp + rowExp + (rawExp + ε - saving)) := by
      simp only [Real.rpow_add hZpos]
      dsimp only [U, Cbound]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ he)
      (mul_nonneg (mul_nonneg (mul_nonneg hsectors
        (mul_nonneg (mul_nonneg hCleft.le hCright.le) hcount.le)) hCnormal) hheightpow)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.AllocatedExceptionalSource.centered_uniform
#print axioms HeckeSkeleton.Moments.EngineStep.AllocatedExceptionalSource.centered_or_absolute_uniform
#print axioms HeckeSkeleton.Moments.EngineStep.AllocatedExceptionalSource.absolute
#print axioms HeckeSkeleton.Moments.EngineStep.actual_exceptional_paired_contribution
