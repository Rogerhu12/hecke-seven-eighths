import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocatedChildFamily
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalAmplitude
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Actual exceptional columns and the centered volume estimate

Only single-ideal character and profile identifications are supplied.
The finite plain sums are proved equal to the genuine masked ideal
series, and the two original rectangles remain one subtraction.
The allocation's computed frozen scalar and its exact live-slot product
remain explicit. No polynomial identity or exceptional energy estimate
is assumed.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.Moments.Twist HeckePort.CenteredMomentVolume
open HeckePort.CenteredMomentCounting

set_option maxHeartbeats 3000000

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The primitive exceptional identification is pointwise in one
original ideal. Support is required only where the actual coprimality
mask, multiplicative coefficient and radial profile can all contribute.
Thus the genuine support-extracted domain need not contain masked zeros. -/
structure ExceptionalPlainChart
    (χ θ : HeckeCharacter F) (M : Ideal (𝓞 F) →* ℂ) (g h' : A.R)
    (Ψ : Ideal (𝓞 F) →* ℂ) (R : Ideal (𝓞 F)) (W : ℝ → ℂ) (t N : ℝ)
    (S : Finset (HeckeGeneral.Analysis.NonzeroIdeal F))
    (w : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (x : HeckeGeneral.Analysis.NonzeroIdeal F → V) (ξ : V) : Prop where
  coefficient : ∀ I ∈ S,
    sourcePlainCoefficient χ θ M I *
      actualIdealResidue (A := A) (σ := σ) I.val (g * h') =
        (if IsCoprime I.val R then (1 : ℂ) else 0) * Ψ I.val
  profile : ∀ I ∈ S, w I * jointPhase ξ (x I) =
    (Ideal.absNorm I.val : ℂ) ^ (Complex.I * t) * W ((Ideal.absNorm I.val : ℝ) / N)
  support : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal F,
    IsCoprime I.val R → Ψ I.val ≠ 0 →
      W ((Ideal.absNorm I.val : ℝ) / N) ≠ 0 → I ∈ S

/-- A genuine finite-support series identity, including the zero ideal.
Its zero contribution vanishes through the original coefficient. -/
theorem finite_twistedMaskedSum
    (Ψ : Ideal (𝓞 F) →* ℂ) (hΨ0 : Ψ ⊥ = 0)
    (R : Ideal (𝓞 F)) (W : ℝ → ℂ) (t N : ℝ)
    (S : Finset (HeckeGeneral.Analysis.NonzeroIdeal F))
    (hS : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal F,
      IsCoprime I.val R → Ψ I.val ≠ 0 →
        W ((Ideal.absNorm I.val : ℝ) / N) ≠ 0 → I ∈ S) :
    (∑ I ∈ S, (if IsCoprime I.val R then (1 : ℂ) else 0) *
      (Ψ I.val * (Ideal.absNorm I.val : ℂ) ^ (Complex.I * t) *
        W ((Ideal.absNorm I.val : ℝ) / N))) = twistedMaskedSum Ψ R W t N := by
  let f : Ideal (𝓞 F) → ℂ := fun I =>
    (if IsCoprime I R then (1 : ℂ) else 0) *
      (Ψ I * (Ideal.absNorm I : ℂ) ^ (Complex.I * t) * W ((Ideal.absNorm I : ℝ) / N))
  have hz : ∀ I ∉ S.image Subtype.val, f I = 0 := by
    intro I hI
    by_cases hbot : I = ⊥
    · simp only [f, hbot, hΨ0, zero_mul, mul_zero]
    · let J : HeckeGeneral.Analysis.NonzeroIdeal F :=
        ⟨I, mem_nonZeroDivisors_of_ne_zero hbot⟩
      by_cases hcop : IsCoprime I R
      · by_cases hchar : Ψ I = 0
        · simp only [f, hchar, zero_mul, mul_zero]
        · have hW : W ((Ideal.absNorm I : ℝ) / N) = 0 := by
            by_contra hne
            exact hI (Finset.mem_image.mpr ⟨J, hS J hcop hchar hne, rfl⟩)
          simp only [f, hW, mul_zero]
      · simp only [f, if_neg hcop, zero_mul]
  change (∑ I ∈ S, f I.val) = ∑' I, f I
  symm
  rw [tsum_eq_sum hz, Finset.sum_image (fun I hI J hJ hIJ => Subtype.ext hIJ)]

/-- The one-ideal dictionaries imply the whole finite plain identity;
the caller supplies no equality between finite or infinite sums. -/
theorem sourcePlain_sum_eq_twisted
    (χ θ : HeckeCharacter F) (M : Ideal (𝓞 F) →* ℂ) (g h' : A.R)
    (Ψ : Ideal (𝓞 F) →* ℂ) (hΨ0 : Ψ ⊥ = 0)
    (R : Ideal (𝓞 F)) (W : ℝ → ℂ) (t N : ℝ)
    (S : Finset (HeckeGeneral.Analysis.NonzeroIdeal F))
    (w : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (x : HeckeGeneral.Analysis.NonzeroIdeal F → V) (ξ : V)
    (H : ExceptionalPlainChart (σ := σ) χ θ M g h' Ψ R W t N S w x ξ) :
    (∑ I ∈ S, sourcePlainTerm (σ := σ) χ θ M g h' w N I * jointPhase ξ (x I)) =
      (Real.sqrt N : ℂ)⁻¹ * twistedMaskedSum Ψ R W t N := by
  rw [← finite_twistedMaskedSum Ψ hΨ0 R W t N S H.support, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  unfold sourcePlainTerm
  calc
    _ = (Real.sqrt N : ℂ)⁻¹ *
        ((sourcePlainCoefficient χ θ M I * actualIdealResidue (σ := σ) I.val (g * h')) *
          (w I * jointPhase ξ (x I))) := by ring
    _ = _ := by rw [H.coefficient I hI, H.profile I hI]; ring

theorem jointFourierColumn_sub {ι : Type*} (S : Finset ι)
    (c d : ι → ℂ) (x : ι → V) (ξ : V) :
    jointFourierColumn S (fun i => c i - d i) x ξ =
      jointFourierColumn S c x ξ - jointFourierColumn S d x ξ := by
  simp only [jointFourierColumn, sub_mul, Finset.sum_sub_distrib]

/-- The literal product of every live slot, also valid with no slots. -/
def actualSourceSlotPolynomial {k : ℕ} (T : FixedChildCharacters F k)
    (g h' : A.R) (Z : ℝ) (length : Fin k → ℝ)
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 F)))
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (x : Fin k → HeightOneSpectrum (𝓞 F) → V) (ξ : V) : ℂ :=
  ∏ i, ∑ p ∈ S i,
    sourcePrimeTerm (σ := σ) (T.slot i) (T.slotTwist i) T.mask
      g h' (w i) (Z ^ length i) p * jointPhase ξ (x i p)

/-- Finite triangle bounds are used only for the live slots, after the
single centered rectangle has been retained intact. -/
theorem norm_actualSourceSlotPolynomial_le {k : ℕ} (T : FixedChildCharacters F k)
    (g h' : A.R) (Z : ℝ) (length : Fin k → ℝ)
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 F)))
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (x : Fin k → HeightOneSpectrum (𝓞 F) → V) (ξ : V) :
    ‖actualSourceSlotPolynomial (σ := σ) T g h' Z length S w x ξ‖ ≤
      ∏ i, ∑ p ∈ S i,
        ‖sourcePrimeTerm (σ := σ) (T.slot i) (T.slotTwist i) T.mask
          g h' (w i) (Z ^ length i) p‖ := by
  unfold actualSourceSlotPolynomial
  rw [norm_prod]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact norm_nonneg _
  · intro i hi
    simpa only [norm_mul, norm_jointPhase, mul_one] using
      (norm_sum_le (S i) (fun p =>
        sourcePrimeTerm (σ := σ) (T.slot i) (T.slotTwist i) T.mask
          g h' (w i) (Z ^ length i) p * jointPhase ξ (x i p)))

private theorem normalized_twisted_rectangle
    (Ψ : Ideal (𝓞 F) →* ℂ) (R : Ideal (𝓞 F)) (W₁ W₂ : ℝ → ℂ)
    (t X₁ X₂ Y₁ Y₂ Q : ℝ) (hX₁ : 0 ≤ X₁) (hY₁ : 0 ≤ Y₁)
    (hpX : X₁ * X₂ = Q) (hpY : Y₁ * Y₂ = Q) :
    ((Real.sqrt X₁ : ℂ)⁻¹ * twistedMaskedSum Ψ R W₁ t X₁) *
        ((Real.sqrt X₂ : ℂ)⁻¹ * twistedMaskedSum Ψ R W₂ t X₂) -
      ((Real.sqrt Y₁ : ℂ)⁻¹ * twistedMaskedSum Ψ R W₁ t Y₁) *
        ((Real.sqrt Y₂ : ℂ)⁻¹ * twistedMaskedSum Ψ R W₂ t Y₂) =
      normalizedMaskedRectangle Ψ R W₁ W₂ t X₁ X₂ Y₁ Y₂ Q := by
  have hx : (Real.sqrt X₁ : ℂ)⁻¹ * (Real.sqrt X₂ : ℂ)⁻¹ = (Real.sqrt Q : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, ← Real.sqrt_mul hX₁, hpX]
  have hy : (Real.sqrt Y₁ : ℂ)⁻¹ * (Real.sqrt Y₂ : ℂ)⁻¹ = (Real.sqrt Q : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, ← Real.sqrt_mul hY₁, hpY]
  calc
    _ = ((Real.sqrt X₁ : ℂ)⁻¹ * (Real.sqrt X₂ : ℂ)⁻¹) *
          (twistedMaskedSum Ψ R W₁ t X₁ * twistedMaskedSum Ψ R W₂ t X₂) -
        ((Real.sqrt Y₁ : ℂ)⁻¹ * (Real.sqrt Y₂ : ℂ)⁻¹) *
          (twistedMaskedSum Ψ R W₁ t Y₁ * twistedMaskedSum Ψ R W₂ t Y₂) := by ring
    _ = _ := by rw [hx, hy]; unfold normalizedMaskedRectangle; ring

/-- Exact exceptional identification of a whole centered Cartesian
polynomial. Its four raw plain charts precede all summation. -/
theorem fixed_centered_source_rectangle {k : ℕ}
    (T : FixedChildCharacters F k) (g h' : A.R)
    (X₁ X₂ Y₁ Y₂ Z : ℝ) (length : Fin k → ℝ)
    (S₁ S₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal F))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 F)))
    (w₁ w₂ v₁ v₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal F → V)
    (x : Fin k → HeightOneSpectrum (𝓞 F) → V) (ξ : V)
    (Ψ : Ideal (𝓞 F) →* ℂ) (hΨ0 : Ψ ⊥ = 0)
    (R : Ideal (𝓞 F)) (W₁ W₂ : ℝ → ℂ) (t Q : ℝ)
    (hX₁ : 0 ≤ X₁) (hY₁ : 0 ≤ Y₁)
    (hpX : X₁ * X₂ = Q) (hpY : Y₁ * Y₂ = Q)
    (HX₁ : ExceptionalPlainChart (σ := σ) T.plain T.plainTwist T.mask
      g h' Ψ R W₁ t X₁ S₁ w₁ x₁ ξ)
    (HX₂ : ExceptionalPlainChart (σ := σ) T.plain T.plainTwist T.mask
      g h' Ψ R W₂ t X₂ S₂ w₂ x₂ ξ)
    (HY₁ : ExceptionalPlainChart (σ := σ) T.plain T.plainTwist T.mask
      g h' Ψ R W₁ t Y₁ S₁ v₁ x₁ ξ)
    (HY₂ : ExceptionalPlainChart (σ := σ) T.plain T.plainTwist T.mask
      g h' Ψ R W₂ t Y₂ S₂ v₂ x₂ ξ) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (fun y => T.coefficient (σ := σ) g h' X₁ X₂ Z length w₁ w₂ w y -
        T.coefficient (σ := σ) g h' Y₁ Y₂ Z length v₁ v₂ w y)
      (childCartesianLocation x₁ x₂ x) ξ =
      normalizedMaskedRectangle Ψ R W₁ W₂ t X₁ X₂ Y₁ Y₂ Q *
        actualSourceSlotPolynomial (σ := σ) T g h' Z length S w x ξ := by
  rw [jointFourierColumn_sub]
  simp only [FixedChildCharacters.coefficient]
  rw [joint_cartesian_column_factorization, joint_cartesian_column_factorization]
  rw [sourcePlain_sum_eq_twisted _ _ _ _ _ Ψ hΨ0 R W₁ t X₁ S₁ w₁ x₁ ξ HX₁,
    sourcePlain_sum_eq_twisted _ _ _ _ _ Ψ hΨ0 R W₂ t X₂ S₂ w₂ x₂ ξ HX₂,
    sourcePlain_sum_eq_twisted _ _ _ _ _ Ψ hΨ0 R W₁ t Y₁ S₁ v₁ x₁ ξ HY₁,
    sourcePlain_sum_eq_twisted _ _ _ _ _ Ψ hΨ0 R W₂ t Y₂ S₂ v₂ x₂ ξ HY₂]
  rw [← sub_mul, normalized_twisted_rectangle Ψ R W₁ W₂ t X₁ X₂ Y₁ Y₂ Q
    hX₁ hY₁ hpX hpY] <;> rfl

/-- The actual allocation is transported before the exceptional
identification. Every frozen term and the common translation are the
ones computed by `ActualColumnAllocation.centered_joint_polynomial`. -/
theorem ActualColumnAllocation.centered_source_rectangle {k : ℕ}
    (B : ActualColumnAllocation F k) (T : FixedChildCharacters F k) (g h' : A.R)
    (X₁ X₂ Y₁ Y₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ v₁ v₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal F → V)
    (x : Fin k → HeightOneSpectrum (𝓞 F) → V) (ξ : V)
    (Ψ : Ideal (𝓞 F) →* ℂ) (hΨ0 : Ψ ⊥ = 0)
    (R : Ideal (𝓞 F)) (W₁ W₂ : ℝ → ℂ) (t Q : ℝ)
    (hX₁ : 0 ≤ X₁ / idealNorm F (B.plainDivisor 0))
    (hY₁ : 0 ≤ Y₁ / idealNorm F (B.plainDivisor 0))
    (hpX : (X₁ / idealNorm F (B.plainDivisor 0)) *
      (X₂ / idealNorm F (B.plainDivisor (Fin.succ 0))) = Q)
    (hpY : (Y₁ / idealNorm F (B.plainDivisor 0)) *
      (Y₂ / idealNorm F (B.plainDivisor (Fin.succ 0))) = Q)
    (HX₁ : ExceptionalPlainChart (σ := σ) T.plain T.plainTwist T.mask g h' Ψ R W₁ t
      (X₁ / idealNorm F (B.plainDivisor 0)) B.childPlain₁
      (fun I => w₁ (B.plainDivisor 0 * I)) (fun I => x₁ (B.plainDivisor 0 * I)) ξ)
    (HX₂ : ExceptionalPlainChart (σ := σ) T.plain T.plainTwist T.mask g h' Ψ R W₂ t
      (X₂ / idealNorm F (B.plainDivisor (Fin.succ 0))) B.childPlain₂
      (fun I => w₂ (B.plainDivisor (Fin.succ 0) * I))
      (fun I => x₂ (B.plainDivisor (Fin.succ 0) * I)) ξ)
    (HY₁ : ExceptionalPlainChart (σ := σ) T.plain T.plainTwist T.mask g h' Ψ R W₁ t
      (Y₁ / idealNorm F (B.plainDivisor 0)) B.childPlain₁
      (fun I => v₁ (B.plainDivisor 0 * I)) (fun I => x₁ (B.plainDivisor 0 * I)) ξ)
    (HY₂ : ExceptionalPlainChart (σ := σ) T.plain T.plainTwist T.mask g h' Ψ R W₂ t
      (Y₂ / idealNorm F (B.plainDivisor (Fin.succ 0))) B.childPlain₂
      (fun I => v₂ (B.plainDivisor (Fin.succ 0) * I))
      (fun I => x₂ (B.plainDivisor (Fin.succ 0) * I)) ξ) :
    jointFourierColumn B.columns
      (fun y => rawSourceCoefficient (σ := σ) T g h' X₁ X₂ Z length w₁ w₂ w y -
        rawSourceCoefficient (σ := σ) T g h' Y₁ Y₂ Z length v₁ v₂ w y)
      (rawSourceLocation x₁ x₂ x) ξ =
      B.scalar (σ := σ) T g h' Z length w *
        jointPhase ξ (frozenSourceLocation B.keep B.witness.2 x) *
          (normalizedMaskedRectangle Ψ R W₁ W₂ t
            (X₁ / idealNorm F (B.plainDivisor 0))
            (X₂ / idealNorm F (B.plainDivisor (Fin.succ 0)))
            (Y₁ / idealNorm F (B.plainDivisor 0))
            (Y₂ / idealNorm F (B.plainDivisor (Fin.succ 0))) Q *
            actualSourceSlotPolynomial (σ := σ) (T.restrictSlots B.keep) g h' Z
              (fun j => length (SlotRestriction.index B.keep j)) B.childSlots
              (fun j => w (SlotRestriction.index B.keep j))
              (fun j => x (SlotRestriction.index B.keep j)) ξ) := by
  rw [B.centered_joint_polynomial]
  congr 1
  rw [← jointFourierColumn_sub]
  exact fixed_centered_source_rectangle (T.restrictSlots B.keep) g h'
    (X₁ / idealNorm F (B.plainDivisor 0))
    (X₂ / idealNorm F (B.plainDivisor (Fin.succ 0)))
    (Y₁ / idealNorm F (B.plainDivisor 0))
    (Y₂ / idealNorm F (B.plainDivisor (Fin.succ 0))) Z
    (fun j => length (SlotRestriction.index B.keep j)) B.childPlain₁ B.childPlain₂ B.childSlots
    (fun I => w₁ (B.plainDivisor 0 * I))
    (fun I => w₂ (B.plainDivisor (Fin.succ 0) * I))
    (fun I => v₁ (B.plainDivisor 0 * I))
    (fun I => v₂ (B.plainDivisor (Fin.succ 0) * I))
    (fun j => w (SlotRestriction.index B.keep j))
    (fun I => x₁ (B.plainDivisor 0 * I))
    (fun I => x₂ (B.plainDivisor (Fin.succ 0) * I))
    (fun j => x (SlotRestriction.index B.keep j)) ξ Ψ hΨ0 R W₁ W₂ t Q
    hX₁ hY₁ hpX hpY HX₁ HX₂ HY₁ HY₂

/-- The original compact profiles and the genuine volume input, with
their explicit uniform error controls. These are fixed before a row,
Fourier parameter, scale, mask, or allocation is chosen. -/
structure ExceptionalVolumeControl
    (Ψ : Ideal (𝓞 F) →* ℂ) (W₁ W₂ : ℝ → ℂ) where
  coefficient_norm : ∀ I, ‖Ψ I‖ ≤ 1
  coefficient_zero : Ψ ⊥ = 0
  volume : IdealVolumeInput F Ψ
  lower₁ : ℝ
  upper₁ : ℝ
  lower₂ : ℝ
  upper₂ : ℝ
  bound₁ : ℝ
  bound₂ : ℝ
  lower₁_pos : 0 < lower₁
  lower₂_pos : 0 < lower₂
  upper₁_nonneg : 0 ≤ upper₁
  upper₂_nonneg : 0 ≤ upper₂
  bound₁_nonneg : 0 ≤ bound₁
  bound₂_nonneg : 0 ≤ bound₂
  support₁ : Function.support W₁ ⊆ Set.Icc lower₁ upper₁
  support₂ : Function.support W₂ ⊆ Set.Icc lower₂ upper₂
  profile₁ : ℝ → 𝓢(ℝ, ℂ)
  profile₂ : ℝ → 𝓢(ℝ, ℂ)
  profile₁_eq : ∀ t x, profile₁ t x = (x : ℂ) ^ (Complex.I * t) * W₁ x
  profile₂_eq : ∀ t x, profile₂ t x = (x : ℂ) ^ (Complex.I * t) * W₂ x
  norm₁ : ∀ y, ‖W₁ y‖ ≤ bound₁
  norm₂ : ∀ y, ‖W₂ y‖ ≤ bound₂
  order₁ : ℕ
  order₂ : ℕ
  error₁ : ℝ
  error₂ : ℝ
  error₁_nonneg : 0 ≤ error₁
  error₂_nonneg : 0 ≤ error₂
  error₁_bound : ∀ t : ℝ, volume.error (profile₁ t) ≤ error₁ * (1 + ‖t‖) ^ order₁
  error₂_bound : ∀ t : ℝ, volume.error (profile₂ t) ≤ error₂ * (1 + ‖t‖) ^ order₂

namespace ExceptionalVolumeControl

variable {Ψ : Ideal (𝓞 F) →* ℂ} {W₁ W₂ : ℝ → ℂ}

theorem rectangle_bound (H : ExceptionalVolumeControl Ψ W₁ W₂)
    (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent) :
    ∃ J : ℕ, ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal (𝓞 F), R ≠ ⊥ → (Ideal.absNorm R : ℝ) ≤ Z ^ maskExponent →
      ∀ t X₁ X₂ Y₁ Y₂ Q L : ℝ, 0 < L →
        L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁ * X₂ = Q → Y₁ * Y₂ = Q →
        ‖normalizedMaskedRectangle Ψ R W₁ W₂ t X₁ X₂ Y₁ Y₂ Q‖ ≤
          Cbound * Z ^ ε * (1 + ‖t‖) ^ J * (Real.sqrt Q / L) := by
  exact HeckePort.Moments.normalized_masked_rectangle_estimate
    H.coefficient_norm H.coefficient_zero H.volume W₁ W₂
    H.lower₁ H.upper₁ H.lower₂ H.upper₂ H.bound₁ H.bound₂ ε maskExponent
    H.lower₁_pos H.lower₂_pos H.upper₁_nonneg H.upper₂_nonneg
    H.bound₁_nonneg H.bound₂_nonneg hε hmask H.support₁ H.support₂
    H.profile₁ H.profile₂ H.profile₁_eq H.profile₂_eq H.norm₁ H.norm₂
    H.order₁ H.order₂ H.error₁ H.error₂ H.error₁_nonneg H.error₂_nonneg
    H.error₁_bound H.error₂_bound

/-- A genuine allocated original column has one centered saving. Its
computed frozen scalar and per-prime live-slot masses remain explicit,
so an outer paired estimate does not apply the centered saving twice. -/
theorem allocated_centered_amplitude
    (H : ExceptionalVolumeControl Ψ W₁ W₂)
    (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent) :
    ∃ J : ℕ, ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ Zbase : ℝ, 1 ≤ Zbase →
    ∀ R : Ideal (𝓞 F), R ≠ ⊥ → (Ideal.absNorm R : ℝ) ≤ Zbase ^ maskExponent →
    ∀ {k : ℕ} (B : ActualColumnAllocation F k) (T : FixedChildCharacters F k) (g h' : A.R)
      (X₁ X₂ Y₁ Y₂ Z : ℝ) (length : Fin k → ℝ)
      (w₁ w₂ v₁ v₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
      (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
      (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal F → V)
      (x : Fin k → HeightOneSpectrum (𝓞 F) → V) (ξ : V) (t Q L : ℝ),
    0 < L →
    L ≤ X₁ / idealNorm F (B.plainDivisor 0) →
    L ≤ X₂ / idealNorm F (B.plainDivisor (Fin.succ 0)) →
    L ≤ Y₁ / idealNorm F (B.plainDivisor 0) →
    L ≤ Y₂ / idealNorm F (B.plainDivisor (Fin.succ 0)) →
    (X₁ / idealNorm F (B.plainDivisor 0)) *
      (X₂ / idealNorm F (B.plainDivisor (Fin.succ 0))) = Q →
    (Y₁ / idealNorm F (B.plainDivisor 0)) *
      (Y₂ / idealNorm F (B.plainDivisor (Fin.succ 0))) = Q →
    ExceptionalPlainChart (σ := σ) T.plain T.plainTwist T.mask g h' Ψ R W₁ t
      (X₁ / idealNorm F (B.plainDivisor 0)) B.childPlain₁
      (fun I => w₁ (B.plainDivisor 0 * I)) (fun I => x₁ (B.plainDivisor 0 * I)) ξ →
    ExceptionalPlainChart (σ := σ) T.plain T.plainTwist T.mask g h' Ψ R W₂ t
      (X₂ / idealNorm F (B.plainDivisor (Fin.succ 0))) B.childPlain₂
      (fun I => w₂ (B.plainDivisor (Fin.succ 0) * I))
      (fun I => x₂ (B.plainDivisor (Fin.succ 0) * I)) ξ →
    ExceptionalPlainChart (σ := σ) T.plain T.plainTwist T.mask g h' Ψ R W₁ t
      (Y₁ / idealNorm F (B.plainDivisor 0)) B.childPlain₁
      (fun I => v₁ (B.plainDivisor 0 * I)) (fun I => x₁ (B.plainDivisor 0 * I)) ξ →
    ExceptionalPlainChart (σ := σ) T.plain T.plainTwist T.mask g h' Ψ R W₂ t
      (Y₂ / idealNorm F (B.plainDivisor (Fin.succ 0))) B.childPlain₂
      (fun I => v₂ (B.plainDivisor (Fin.succ 0) * I))
      (fun I => x₂ (B.plainDivisor (Fin.succ 0) * I)) ξ →
    ‖jointFourierColumn B.columns
      (fun y => rawSourceCoefficient (σ := σ) T g h' X₁ X₂ Z length w₁ w₂ w y -
        rawSourceCoefficient (σ := σ) T g h' Y₁ Y₂ Z length v₁ v₂ w y)
      (rawSourceLocation x₁ x₂ x) ξ‖ ≤
      ‖B.scalar (σ := σ) T g h' Z length w‖ *
        (∏ j, ∑ p ∈ B.childSlots j,
          ‖sourcePrimeTerm (σ := σ) ((T.restrictSlots B.keep).slot j)
            ((T.restrictSlots B.keep).slotTwist j) (T.restrictSlots B.keep).mask
            g h' (w (SlotRestriction.index B.keep j))
            (Z ^ length (SlotRestriction.index B.keep j)) p‖) *
        (Cbound * Zbase ^ ε * (1 + ‖t‖) ^ J * (Real.sqrt Q / L)) := by
  obtain ⟨J, Cbound, hCbound, hrect⟩ := H.rectangle_bound ε maskExponent hε hmask
  refine ⟨J, Cbound, hCbound, ?_⟩
  intro Zbase hZbase R hR hRnorm k B T g h' X₁ X₂ Y₁ Y₂ Z length
    w₁ w₂ v₁ v₂ w x₁ x₂ x ξ t Q L hL hX₁ hX₂ hY₁ hY₂ hpX hpY HX₁ HX₂ HY₁ HY₂
  have hvalue := B.centered_source_rectangle T g h' X₁ X₂ Y₁ Y₂ Z length
    w₁ w₂ v₁ v₂ w x₁ x₂ x ξ Ψ H.coefficient_zero R W₁ W₂ t Q
    (hL.le.trans hX₁) (hL.le.trans hY₁) hpX hpY HX₁ HX₂ HY₁ HY₂
  have hc := hrect Zbase hZbase R hR hRnorm t
    (X₁ / idealNorm F (B.plainDivisor 0))
    (X₂ / idealNorm F (B.plainDivisor (Fin.succ 0)))
    (Y₁ / idealNorm F (B.plainDivisor 0))
    (Y₂ / idealNorm F (B.plainDivisor (Fin.succ 0))) Q L
    hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hs := norm_actualSourceSlotPolynomial_le (σ := σ) (T.restrictSlots B.keep) g h' Z
    (fun j => length (SlotRestriction.index B.keep j)) B.childSlots
    (fun j => w (SlotRestriction.index B.keep j))
    (fun j => x (SlotRestriction.index B.keep j)) ξ
  have hbound : 0 ≤ Cbound * Zbase ^ ε * (1 + ‖t‖) ^ J * (Real.sqrt Q / L) := by
    have hz : 0 ≤ Zbase ^ ε := Real.rpow_nonneg (zero_le_one.trans hZbase) _
    positivity
  rw [hvalue, norm_mul, norm_mul, norm_mul, norm_jointPhase, mul_one]
  have hm := mul_le_mul_of_nonneg_left
    (mul_le_mul hc hs (norm_nonneg _) hbound)
    (norm_nonneg (B.scalar (σ := σ) T g h' Z length w))
  convert hm using 1 <;> ring

end ExceptionalVolumeControl

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.sourcePlain_sum_eq_twisted
#print axioms HeckeSkeleton.Moments.EngineStep.fixed_centered_source_rectangle
#print axioms HeckeSkeleton.Moments.EngineStep.ActualColumnAllocation.centered_source_rectangle
#print axioms HeckeSkeleton.Moments.EngineStep.ExceptionalVolumeControl.allocated_centered_amplitude
