import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OrdinaryExceptionalAmplitude

/-!
# Exceptional amplitudes with constants before the moving profiles

The primitive volume factory supplies fixed support endpoints, a fixed
height order, and errors linear in the original profile bound.  This
file keeps that bound as an explicit square instead of selecting a new
constant after each moving profile.  The divisor constant is chosen
before every volume control, profile, mask, height and source.

The same numerical constant controls the literal centered rectangle and
its allocated source.  The centered saving is used once; a nonpositive
lower length uses the exact absolute estimate on the same source.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.Moments.Twist
open HeckePort.CenteredMomentVolume HeckePort.CenteredMomentMask
open HeckePort.CenteredMomentCancellation HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

namespace ExceptionalVolumeControl

variable {Ψ : Ideal (𝓞 K) →* ℂ} {W₁ W₂ : ℝ → ℂ}

/-- Only the individual fields filled by the original volume factory.
There is no rectangle, row sum or exceptional terminal estimate here. -/
structure UniformFields (H : ExceptionalVolumeControl Ψ W₁ W₂)
    (upper profileBound errorCoefficient : ℝ) (order : ℕ) : Prop where
  upper₁ : H.upper₁ = upper
  upper₂ : H.upper₂ = upper
  bound₁ : H.bound₁ = profileBound
  bound₂ : H.bound₂ = profileBound
  order₁ : H.order₁ = order
  order₂ : H.order₂ = order
  error₁ : H.error₁ = errorCoefficient * profileBound
  error₂ : H.error₂ = errorCoefficient * profileBound

theorem UniformFields.absoluteConstant_eq
    {H : ExceptionalVolumeControl Ψ W₁ W₂}
    {upper profileBound errorCoefficient : ℝ} {order : ℕ}
    (h : H.UniformFields upper profileBound errorCoefficient order) :
    H.absoluteConstant = (idealCountConstant K * upper) ^ 2 * profileBound ^ 2 := by
  simp only [absoluteConstant, h.upper₁, h.upper₂, h.bound₁, h.bound₂]
  ring

/-- The constant and order are uniform over the original profiles.
The explicit profile factor is quadratic, and independent of the mask
or of the four scales in the centered difference. -/
theorem exists_uniform_rectangle_constant
    (upper errorCoefficient ε maskExponent : ℝ) (order : ℕ)
    (hupper : 0 ≤ upper) (herror : 0 ≤ errorCoefficient)
    (hε : 0 < ε) (hmask : 0 ≤ maskExponent) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ψ : Ideal (𝓞 K) →* ℂ} {W₁ W₂ : ℝ → ℂ}
      (H : ExceptionalVolumeControl Ψ W₁ W₂) (P : ℝ), 0 ≤ P →
      H.UniformFields upper P errorCoefficient order →
    ∀ Z : ℝ, 1 ≤ Z → ∀ R : Ideal (𝓞 K), R ≠ ⊥ →
      (Ideal.absNorm R : ℝ) ≤ Z ^ maskExponent →
    ∀ t X₁ X₂ Y₁ Y₂ Q L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁ * X₂ = Q → Y₁ * Y₂ = Q →
      ‖normalizedMaskedRectangle Ψ R W₁ W₂ t X₁ X₂ Y₁ Y₂ Q‖ ≤
        C * P ^ 2 * Z ^ ε * (1 + ‖t‖) ^ order * (Real.sqrt Q / L) := by
  obtain ⟨D, hD, hdivisor⟩ := polynomial_mask_divisor_bound (K := K)
    ε maskExponent hε hmask
  have hcount : 0 ≤ idealCountConstant K := zero_le_one.trans (one_le_idealCountConstant K)
  let coefficient := 16 * D * errorCoefficient * idealCountConstant K * upper
  have hcoefficient : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  refine ⟨1 + coefficient, by linarith, ?_⟩
  intro Ψ W₁ W₂ H P hP fields Z hZ R hR hRnorm
    t X₁ X₂ Y₁ Y₂ Q L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hz : 0 ≤ Z ^ ε := Real.rpow_nonneg (zero_le_one.trans hZ) _
  have hheight : 0 ≤ (1 + ‖t‖) ^ order := pow_nonneg (by positivity) _
  have he₁ : H.volume.error (H.profile₁ t) ≤
      errorCoefficient * P * (1 + ‖t‖) ^ order := by
    simpa only [fields.error₁, fields.order₁] using H.error₁_bound t
  have he₂ : H.volume.error (H.profile₂ t) ≤
      errorCoefficient * P * (1 + ‖t‖) ^ order := by
    simpa only [fields.error₂, fields.order₂] using H.error₂_bound t
  have hm₁ : maskedError H.volume R (H.profile₁ t) ≤
      (D * Z ^ ε) * (errorCoefficient * P * (1 + ‖t‖) ^ order) := by
    unfold maskedError
    exact mul_le_mul (hdivisor Z hZ R hR hRnorm) he₁
      (H.volume.error_nonneg _) (mul_nonneg hD.le hz)
  have hm₂ : maskedError H.volume R (H.profile₂ t) ≤
      (D * Z ^ ε) * (errorCoefficient * P * (1 + ‖t‖) ^ order) := by
    unfold maskedError
    exact mul_le_mul (hdivisor Z hZ R hR hRnorm) he₂
      (H.volume.error_nonneg _) (mul_nonneg hD.le hz)
  let E := maskedError H.volume R (H.profile₁ t) + maskedError H.volume R (H.profile₂ t)
  have hE : E ≤ 2 * ((D * Z ^ ε) *
      (errorCoefficient * P * (1 + ‖t‖) ^ order)) := by
    dsimp only [E]
    linarith
  let Vc := idealCountConstant K * (upper * P + upper * P)
  have hVc : 0 ≤ Vc := by dsimp only [Vc]; positivity
  have hraw := twisted_rectangle_saving H.coefficient_norm H.coefficient_zero
    H.volume R hR W₁ W₂ H.lower₁ upper H.lower₂ upper P P
    H.lower₁_pos H.lower₂_pos hupper hupper hP hP
    (by simpa only [fields.upper₁] using H.support₁)
    (by simpa only [fields.upper₂] using H.support₂)
    H.profile₁ H.profile₂ H.profile₁_eq H.profile₂_eq
    (fun y => by simpa only [fields.bound₁] using H.norm₁ y)
    (fun y => by simpa only [fields.bound₂] using H.norm₂ y)
    t X₁ X₂ Y₁ Y₂ Q L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hQ : 0 < Q := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hn := HeckePort.CenteredMoment.normalized_centered_saving _ Q L Vc E hQ hraw
  have hratio : 0 ≤ Real.sqrt Q / L := div_nonneg (Real.sqrt_nonneg Q) hL.le
  calc
    _ ≤ 4 * E * Vc * (Real.sqrt Q / L) := hn
    _ ≤ 4 * (2 * ((D * Z ^ ε) *
        (errorCoefficient * P * (1 + ‖t‖) ^ order))) * Vc * (Real.sqrt Q / L) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by norm_num)) hVc) hratio
    _ = coefficient * P ^ 2 * Z ^ ε * (1 + ‖t‖) ^ order * (Real.sqrt Q / L) := by
      dsimp only [coefficient, Vc]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith : coefficient ≤ 1 + coefficient)
            (sq_nonneg P)) hz) hheight) hratio

end ExceptionalVolumeControl

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace AllocatedExceptionalSource

variable {Ψ : Ideal (𝓞 K) →* ℂ} {W₁ W₂ : ℝ → ℂ} {g h' : A.R} {k : ℕ}

private theorem value_bound_from_rectangle
    (H : ExceptionalVolumeControl Ψ W₁ W₂)
    (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h' k)
    (B : ℝ) (hB : 0 ≤ B)
    (hrectangle : ‖normalizedMaskedRectangle Ψ s.mask W₁ W₂ s.time
      (s.X₁ / idealNorm K (s.allocation.plainDivisor 0))
      (s.X₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0)))
      (s.Y₁ / idealNorm K (s.allocation.plainDivisor 0))
      (s.Y₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0))) s.product‖ ≤
        B * Real.sqrt s.product) : ‖s.value‖ ≤ B * s.rawMass := by
  have hs := norm_actualSourceSlotPolynomial_le (σ := σ) (s.characters.restrictSlots s.allocation.keep)
    g h' s.Zslot (fun j => s.length (SlotRestriction.index s.allocation.keep j))
    s.allocation.childSlots (fun j => s.w (SlotRestriction.index s.allocation.keep j))
    (fun j => s.x (SlotRestriction.index s.allocation.keep j)) s.ξ
  rw [s.identity H.coefficient_zero, norm_mul, norm_mul, norm_mul, norm_jointPhase, mul_one]
  have hm := mul_le_mul_of_nonneg_left
    (mul_le_mul hrectangle hs (norm_nonneg _)
      (mul_nonneg hB (Real.sqrt_nonneg _)))
    (norm_nonneg (s.allocation.scalar (σ := σ) s.characters g h' s.Zslot s.length s.w))
  convert hm using 1 <;> dsimp only [rawMass, slotMass] <;> ring

theorem uniform_absolute
    (H : ExceptionalVolumeControl Ψ W₁ W₂)
    (upper P errorCoefficient : ℝ) (order : ℕ)
    (fields : H.UniformFields upper P errorCoefficient order)
    (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h' k) :
    ‖s.ordinaryValue‖ ≤ (idealCountConstant K * upper) ^ 2 * P ^ 2 * s.rawMass ∧
    ‖s.value‖ ≤ (2 * (idealCountConstant K * upper) ^ 2) * P ^ 2 * s.rawMass := by
  constructor
  · simpa only [fields.absoluteConstant_eq] using s.ordinary_absolute H
  · have hr := H.rectangle_absolute s.mask s.time
      (s.X₁ / idealNorm K (s.allocation.plainDivisor 0))
      (s.X₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0)))
      (s.Y₁ / idealNorm K (s.allocation.plainDivisor 0))
      (s.Y₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0))) s.product
      (s.lower_pos.trans_le s.X₁_lower) (s.lower_pos.trans_le s.X₂_lower)
      (s.lower_pos.trans_le s.Y₁_lower) (s.lower_pos.trans_le s.Y₂_lower) s.productX s.productY
    have hb := value_bound_from_rectangle H s (2 * H.absoluteConstant)
      (mul_nonneg (by norm_num) H.absoluteConstant_nonneg) hr
    simpa only [fields.absoluteConstant_eq, mul_assoc] using hb

/-- A single earlier constant pays both the positive lower-length
case and the true absolute-volume alternative. The original profile
bound remains explicit, and no source is replaced in either case. -/
theorem exists_uniform_centered_constant
    (upper errorCoefficient ε maskExponent : ℝ) (order : ℕ)
    (hupper : 0 ≤ upper) (herror : 0 ≤ errorCoefficient)
    (hε : 0 < ε) (hmask : 0 ≤ maskExponent) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ψ : Ideal (𝓞 K) →* ℂ} {W₁ W₂ : ℝ → ℂ}
      (H : ExceptionalVolumeControl Ψ W₁ W₂) (P : ℝ), 0 ≤ P →
      H.UniformFields upper P errorCoefficient order →
    ∀ Z : ℝ, 1 ≤ Z → ∀ {g h' : A.R} {k : ℕ}
      (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h' k),
      s.mask ≠ ⊥ → (Ideal.absNorm s.mask : ℝ) ≤ Z ^ maskExponent →
    ∀ L : ℝ, Z ^ L ≤ s.lower →
      ‖s.value‖ ≤ C * P ^ 2 * Z ^ ε * (1 + ‖s.time‖) ^ order *
        s.rawMass * Z ^ (-max L 0) := by
  obtain ⟨Ccenter, hCcenter, hrectangle⟩ :=
    ExceptionalVolumeControl.exists_uniform_rectangle_constant (K := K)
      upper errorCoefficient ε maskExponent order hupper herror hε hmask
  let Cabs := 2 * (idealCountConstant K * upper) ^ 2
  have hCabs : 0 ≤ Cabs := mul_nonneg (by norm_num) (sq_nonneg _)
  let C := Ccenter + Cabs
  have hC : 0 < C := add_pos_of_pos_of_nonneg hCcenter hCabs
  refine ⟨C, hC, ?_⟩
  intro Ψ W₁ W₂ H P hP fields Z hZ g h' k s hR hRnorm L hL
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hheight : 1 ≤ (1 + ‖s.time‖) ^ order :=
    one_le_pow₀ (by linarith [norm_nonneg s.time])
  have hpower : 1 ≤ Z ^ ε := Real.one_le_rpow hZ hε.le
  have hfront : 0 ≤ C * P ^ 2 * Z ^ ε * (1 + ‖s.time‖) ^ order := by positivity
  by_cases hlength : 0 ≤ L
  · have hr := hrectangle H P hP fields Z hZ s.mask hR hRnorm s.time
      (s.X₁ / idealNorm K (s.allocation.plainDivisor 0))
      (s.X₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0)))
      (s.Y₁ / idealNorm K (s.allocation.plainDivisor 0))
      (s.Y₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0))) s.product s.lower
      s.lower_pos s.X₁_lower s.X₂_lower s.Y₁_lower s.Y₂_lower s.productX s.productY
    have hr' : ‖normalizedMaskedRectangle Ψ s.mask W₁ W₂ s.time
        (s.X₁ / idealNorm K (s.allocation.plainDivisor 0))
        (s.X₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0)))
        (s.Y₁ / idealNorm K (s.allocation.plainDivisor 0))
        (s.Y₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0))) s.product‖ ≤
      (Ccenter * P ^ 2 * Z ^ ε * (1 + ‖s.time‖) ^ order / s.lower) *
        Real.sqrt s.product := by convert hr using 1 <;> ring
    have hb := value_bound_from_rectangle H s _ (by positivity) hr'
    have hinv : s.lower⁻¹ ≤ Z ^ (-L) := by
      simpa only [one_div, Real.rpow_neg hz.le] using
        one_div_le_one_div_of_le (Real.rpow_pos_of_pos hz L) hL
    have hcoeff : Ccenter * P ^ 2 * Z ^ ε * (1 + ‖s.time‖) ^ order ≤
        C * P ^ 2 * Z ^ ε * (1 + ‖s.time‖) ^ order := by
      apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hheight)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg P)
      dsimp only [C]
      linarith
    rw [max_eq_left hlength]
    apply hb.trans
    have hm := mul_le_mul
      (mul_le_mul_of_nonneg_right hcoeff s.rawMass_nonneg) hinv
      (inv_nonneg.mpr s.lower_pos.le) (mul_nonneg hfront s.rawMass_nonneg)
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hm
  · rw [max_eq_right (le_of_not_ge hlength), neg_zero, Real.rpow_zero, mul_one]
    have habs := (uniform_absolute H upper P errorCoefficient order fields s).2
    have hCabsC : Cabs ≤ C := by dsimp only [C]; linarith
    have hcoeff : Cabs * P ^ 2 ≤
        C * P ^ 2 * Z ^ ε * (1 + ‖s.time‖) ^ order := by
      calc
        _ ≤ C * P ^ 2 := mul_le_mul_of_nonneg_right hCabsC (sq_nonneg P)
        _ ≤ (C * P ^ 2) * (Z ^ ε * (1 + ‖s.time‖) ^ order) := by
          apply le_mul_of_one_le_right (mul_nonneg hC.le (sq_nonneg P))
          exact one_le_mul_of_one_le_of_one_le hpower hheight
        _ = _ := by ring
    exact habs.trans (mul_le_mul_of_nonneg_right hcoeff s.rawMass_nonneg)

end AllocatedExceptionalSource
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ExceptionalVolumeControl.exists_uniform_rectangle_constant
#print axioms HeckeSkeleton.Moments.EngineStep.AllocatedExceptionalSource.uniform_absolute
#print axioms HeckeSkeleton.Moments.EngineStep.AllocatedExceptionalSource.exists_uniform_centered_constant
