import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalSourceBinding

/-!
# Ordinary exceptional columns from their original atoms

The ordinary column is identified with the actual pair of masked ideal
sums. Its bound uses only their absolute volume bounds. No quarter-scale
lower bound, subtraction or centered cancellation is used.

The auxiliary allocated record duplicates the original rectangle only
to reuse its raw frozen and live-slot normalization. The value estimated
below is the original single rectangle.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.Moments.Twist HeckePort.CenteredMomentVolume
open HeckePort.CenteredMomentCounting

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace ExceptionalVolumeControl

variable {Ψ : Ideal (𝓞 F) →* ℂ} {W₁ W₂ : ℝ → ℂ}

theorem product_absolute (H : ExceptionalVolumeControl Ψ W₁ W₂)
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


end ExceptionalVolumeControl

namespace AllocatedExceptionalSource

variable {Ψ : Ideal (𝓞 F) →* ℂ} {W₁ W₂ : ℝ → ℂ} {g h' : A.R} {k : ℕ}

def ordinaryValue (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h' k) : ℂ :=
  jointFourierColumn s.allocation.columns
    (rawSourceCoefficient (σ := σ) s.characters g h'
      s.X₁ s.X₂ s.Zslot s.length s.w₁ s.w₂ s.w)
    (rawSourceLocation s.x₁ s.x₂ s.x) s.ξ

/-- Only the two original plain charts enter this identity. -/
theorem ordinary_identity
    (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h' k)
    (hΨ0 : Ψ ⊥ = 0) :
    s.ordinaryValue = s.allocation.scalar (σ := σ) s.characters g h' s.Zslot s.length s.w *
      jointPhase s.ξ (frozenSourceLocation s.allocation.keep s.allocation.witness.2 s.x) *
        (((Real.sqrt s.product : ℂ)⁻¹ *
          (twistedMaskedSum Ψ s.mask W₁ s.time
              (s.X₁ / idealNorm F (s.allocation.plainDivisor 0)) *
            twistedMaskedSum Ψ s.mask W₂ s.time
              (s.X₂ / idealNorm F (s.allocation.plainDivisor (Fin.succ 0))))) *
          actualSourceSlotPolynomial (σ := σ) (s.characters.restrictSlots s.allocation.keep)
            g h' s.Zslot (fun j => s.length (SlotRestriction.index s.allocation.keep j))
            s.allocation.childSlots (fun j => s.w (SlotRestriction.index s.allocation.keep j))
            (fun j => s.x (SlotRestriction.index s.allocation.keep j)) s.ξ) := by
  rw [ordinaryValue, s.allocation.joint_polynomial]
  congr 1
  simp only [ActualColumnAllocation.childColumns, FixedChildCharacters.coefficient]
  rw [joint_cartesian_column_factorization]
  simp only [FixedChildCharacters.restrictSlots]
  rw [sourcePlain_sum_eq_twisted _ _ _ _ _ Ψ hΨ0 s.mask W₁ s.time
    (s.X₁ / idealNorm F (s.allocation.plainDivisor 0)) s.allocation.childPlain₁
    (fun I => s.w₁ (s.allocation.plainDivisor 0 * I))
    (fun I => s.x₁ (s.allocation.plainDivisor 0 * I)) s.ξ s.chartX₁]
  rw [sourcePlain_sum_eq_twisted _ _ _ _ _ Ψ hΨ0 s.mask W₂ s.time
    (s.X₂ / idealNorm F (s.allocation.plainDivisor (Fin.succ 0))) s.allocation.childPlain₂
    (fun I => s.w₂ (s.allocation.plainDivisor (Fin.succ 0) * I))
    (fun I => s.x₂ (s.allocation.plainDivisor (Fin.succ 0) * I)) s.ξ s.chartX₂]
  have hp :
      (Real.sqrt (s.X₁ / idealNorm F (s.allocation.plainDivisor 0)) : ℂ)⁻¹ *
        (Real.sqrt (s.X₂ / idealNorm F (s.allocation.plainDivisor (Fin.succ 0))) : ℂ)⁻¹ =
          (Real.sqrt s.product : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul,
      ← Real.sqrt_mul (s.lower_pos.le.trans s.X₁_lower), s.productX]
  dsimp only [actualSourceSlotPolynomial]
  rw [← hp]
  ring

theorem ordinary_absolute (H : ExceptionalVolumeControl Ψ W₁ W₂)
    (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h' k) :
    ‖s.ordinaryValue‖ ≤ H.absoluteConstant * s.rawMass := by
  have hr := H.product_absolute s.mask s.time
    (s.X₁ / idealNorm F (s.allocation.plainDivisor 0))
    (s.X₂ / idealNorm F (s.allocation.plainDivisor (Fin.succ 0))) s.product
    (s.lower_pos.trans_le s.X₁_lower) (s.lower_pos.trans_le s.X₂_lower) s.productX
  have hs := norm_actualSourceSlotPolynomial_le (σ := σ) (s.characters.restrictSlots s.allocation.keep)
    g h' s.Zslot (fun j => s.length (SlotRestriction.index s.allocation.keep j))
    s.allocation.childSlots (fun j => s.w (SlotRestriction.index s.allocation.keep j))
    (fun j => s.x (SlotRestriction.index s.allocation.keep j)) s.ξ
  rw [s.ordinary_identity H.coefficient_zero, norm_mul, norm_mul, norm_mul,
    norm_jointPhase, mul_one]
  have hm := mul_le_mul_of_nonneg_left
    (mul_le_mul hr hs (norm_nonneg _)
      (mul_nonneg H.absoluteConstant_nonneg (Real.sqrt_nonneg _)))
    (norm_nonneg (s.allocation.scalar (σ := σ) s.characters g h' s.Zslot s.length s.w))
  convert hm using 1 <;> dsimp only [rawMass, slotMass] <;> ring

end AllocatedExceptionalSource

namespace ActualAllocatedSource

variable {H : Type*} {k : ℕ}
variable (s : ActualAllocatedSource A V H k)
variable (Ψ : Ideal (𝓞 F) →* ℂ) (W₁ W₂ : ℝ → ℂ) (ξ : V) (h : H)

/-- The ordinary exceptional dictionary contains just the original two
single-ideal charts and positive formal scales. -/
structure OrdinaryExceptionalAt where
  mask : Ideal (𝓞 F)
  time : ℝ
  product : ℝ
  lower : ℝ
  lower_pos : 0 < lower
  X₁_lower : lower ≤ s.scale₁ / idealNorm F (s.allocation.plainDivisor 0)
  X₂_lower : lower ≤ s.scale₂ / idealNorm F (s.allocation.plainDivisor (Fin.succ 0))
  productX : (s.scale₁ / idealNorm F (s.allocation.plainDivisor 0)) *
    (s.scale₂ / idealNorm F (s.allocation.plainDivisor (Fin.succ 0))) = product
  chartX₁ : ExceptionalPlainChart (σ := σ)
    (s.characters h).plain (s.characters h).plainTwist (s.characters h).mask
    (s.extractedFactor h) (s.row h).element Ψ mask W₁ time
    (s.scale₁ / idealNorm F (s.allocation.plainDivisor 0)) s.allocation.childPlain₁
    (fun I => s.leftWeight h (s.allocation.plainDivisor 0 * I))
    (fun I => s.leftLocation h (s.allocation.plainDivisor 0 * I)) ξ
  chartX₂ : ExceptionalPlainChart (σ := σ)
    (s.characters h).plain (s.characters h).plainTwist (s.characters h).mask
    (s.extractedFactor h) (s.row h).element Ψ mask W₂ time
    (s.scale₂ / idealNorm F (s.allocation.plainDivisor (Fin.succ 0))) s.allocation.childPlain₂
    (fun I => s.rightWeight h (s.allocation.plainDivisor (Fin.succ 0) * I))
    (fun I => s.rightLocation h (s.allocation.plainDivisor (Fin.succ 0) * I)) ξ

namespace OrdinaryExceptionalAt

variable {s Ψ W₁ W₂ ξ h}

/-- The repeated rectangle is used only as a carrier of the common raw
normalization; ordinaryValue still reads the original first rectangle. -/
def source (T : s.OrdinaryExceptionalAt (σ := σ) Ψ W₁ W₂ ξ h) :
    AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂
      (s.extractedFactor h) (s.row h).element k where
  allocation := s.allocation
  characters := s.characters h
  X₁ := s.scale₁
  X₂ := s.scale₂
  Y₁ := s.scale₁
  Y₂ := s.scale₂
  Zslot := s.base
  length := s.length
  w₁ := s.leftWeight h
  w₂ := s.rightWeight h
  v₁ := s.leftWeight h
  v₂ := s.rightWeight h
  w := s.slotWeight h
  x₁ := s.leftLocation h
  x₂ := s.rightLocation h
  x := s.slotLocation h
  ξ := ξ
  mask := T.mask
  time := T.time
  product := T.product
  lower := T.lower
  lower_pos := T.lower_pos
  X₁_lower := T.X₁_lower
  X₂_lower := T.X₂_lower
  Y₁_lower := T.X₁_lower
  Y₂_lower := T.X₂_lower
  productX := T.productX
  productY := T.productX
  chartX₁ := T.chartX₁
  chartX₂ := T.chartX₂
  chartY₁ := T.chartX₁
  chartY₂ := T.chartX₂

theorem ordinary_value_eq (T : s.OrdinaryExceptionalAt (σ := σ) Ψ W₁ W₂ ξ h) :
    T.source.ordinaryValue = jointFourierColumn s.allocation.columns
      (rawSourceCoefficient (σ := σ) (s.characters h) (s.extractedFactor h) (s.row h).element
        s.scale₁ s.scale₂ s.base s.length (s.leftWeight h) (s.rightWeight h) (s.slotWeight h))
      (rawSourceLocation (s.leftLocation h) (s.rightLocation h) (s.slotLocation h)) ξ := rfl

end OrdinaryExceptionalAt
end ActualAllocatedSource
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.AllocatedExceptionalSource.ordinary_absolute
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.OrdinaryExceptionalAt.ordinary_value_eq

