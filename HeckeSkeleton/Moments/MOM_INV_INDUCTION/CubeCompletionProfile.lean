import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionCanonical
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionEnergy

/-!
# Exact cube-profile normalization

The normalized cube coefficient is independent of the moving row. Its
norm is at most one on the cube annulus. The complete common scalar is
restored explicitly, including the factor `2 H / X` in squared energy.
At the shifted column scale `s X / H^3`, both normalization factors
cancel to the fixed factor `2 cap^2 s`; the remaining output power then
contributes one further fixed factor `s`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionProfile

open scoped NumberField Classical BigOperators
open HeckeSkeleton.Moments.MOM_BASE
open HeckeSkeleton.Moments.MOM_INV_STEP.CommonKernel
open CubeCompletionEnergy

variable {K : Type} [Field K] [NumberField K]

def cubeAmplitude (H : ℝ) (b : Ideal (𝓞 K)) : ℂ :=
  (Real.sqrt (cubeIdealNorm b) : ℂ) / (Real.sqrt (2 * H) : ℂ)

theorem cubeAmplitude_norm_le (H : ℝ) (hH : 0 < H)
    (b : Ideal (𝓞 K)) (hb : cubeIdealNorm b ≤ 2 * H) :
    ‖cubeAmplitude H b‖ ≤ 1 := by
  rw [cubeAmplitude, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact (div_le_one (Real.sqrt_pos.mpr (by positivity))).mpr (Real.sqrt_le_sqrt hb)

def normalizedCubeBaseCoefficient (P : Ideal (𝓞 K) → Prop)
    (B : Finset (Ideal (𝓞 K))) (H : ℝ) (staticTau : Ideal (𝓞 K) →* ℂ)
    (b : Ideal (𝓞 K)) : ℂ :=
  cubeAmplitude H b * normalizedCubeCoefficient P B b * staticTau b ^ 3

theorem normalizedCubeBaseCoefficient_norm_le
    (P : Ideal (𝓞 K) → Prop) (B : Finset (Ideal (𝓞 K)))
    (H : ℝ) (hH : 0 < H) (staticTau : Ideal (𝓞 K) →* ℂ)
    (b : Ideal (𝓞 K)) (hbB : b ∈ B) (hb : cubeIdealNorm b ≤ 2 * H)
    (hstatic : ‖staticTau b‖ ≤ 1) :
    ‖normalizedCubeBaseCoefficient P B H staticTau b‖ ≤ 1 := by
  have hp : ‖staticTau b‖ ^ 3 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) hstatic 3
  rw [normalizedCubeBaseCoefficient, norm_mul, norm_mul, norm_pow]
  have ha := cubeAmplitude_norm_le H hH b hb
  have hc := normalizedCubeCoefficient_norm_le_one P B b hbB
  exact (mul_le_mul (mul_le_mul ha hc (norm_nonneg _) zero_le_one)
    hp (pow_nonneg (norm_nonneg _) _) (by norm_num)).trans_eq (by ring)

/-- This is the actual provider label weight after Mellin separation;
it remains independent of every moving row and squarefree column. -/
def normalizedCubeLabelWeight (P : Ideal (𝓞 K) → Prop)
    (B : Finset (Ideal (𝓞 K))) (H : ℝ) (staticTau : Ideal (𝓞 K) →* ℂ)
    (t : ℝ) (b : Ideal (𝓞 K)) : ℂ :=
  normalizedCubeBaseCoefficient P B H staticTau b *
    columnPhase t (Real.log (cubeIdealNorm b ^ 3))

theorem normalizedCubeLabelWeight_norm_le
    (P : Ideal (𝓞 K) → Prop) (B : Finset (Ideal (𝓞 K)))
    (H : ℝ) (hH : 0 < H) (staticTau : Ideal (𝓞 K) →* ℂ)
    (t : ℝ) (b : Ideal (𝓞 K)) (hbB : b ∈ B) (hb : cubeIdealNorm b ≤ 2 * H)
    (hstatic : ‖staticTau b‖ ≤ 1) :
    ‖normalizedCubeLabelWeight P B H staticTau t b‖ ≤ 1 := by
  rw [normalizedCubeLabelWeight, norm_mul, norm_columnPhase, mul_one]
  exact normalizedCubeBaseCoefficient_norm_le P B H hH staticTau b hbB hb hstatic

def sourceScale (B : Finset (Ideal (𝓞 K))) (H X : ℝ) : ℝ :=
  cubeCoefficientCap B * Real.sqrt (2 * H) / Real.sqrt X

theorem sourceScale_pos (B : Finset (Ideal (𝓞 K))) (H X : ℝ)
    (hH : 0 < H) (hX : 0 < X) : 0 < sourceScale B H X :=
  div_pos (mul_pos (cubeCoefficientCap_pos B) (Real.sqrt_pos.mpr (by positivity)))
    (Real.sqrt_pos.mpr hX)

/-- Exact restoration of the full coefficient before applying any
triangle inequality. -/
theorem sourceScale_mul_coefficient
    (P : Ideal (𝓞 K) → Prop) (B : Finset (Ideal (𝓞 K)))
    (H X : ℝ) (hH : 0 < H) (staticTau : Ideal (𝓞 K) →* ℂ)
    (b : Ideal (𝓞 K)) :
    (sourceScale B H X : ℂ) * normalizedCubeBaseCoefficient P B H staticTau b =
      (Real.sqrt (cubeIdealNorm b) : ℂ) / (Real.sqrt X : ℂ) *
        reopenedCubeCoefficient P b * staticTau b ^ 3 := by
  have hh : (Real.sqrt (2 * H) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show 0 < 2 * H by positivity)).ne'
  have hc : (cubeCoefficientCap B : ℂ) ≠ 0 := by
    exact_mod_cast (cubeCoefficientCap_pos B).ne'
  simp only [sourceScale, normalizedCubeBaseCoefficient, cubeAmplitude,
    normalizedCubeCoefficient, Complex.ofReal_div, Complex.ofReal_mul]
  field_simp [hh, hc] <;> ring

theorem sourceScale_sq (B : Finset (Ideal (𝓞 K))) (H X : ℝ)
    (hH : 0 ≤ H) (hX : 0 ≤ X) :
    sourceScale B H X ^ 2 = cubeCoefficientCap B ^ 2 * (2 * H / X) := by
  rw [sourceScale, div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hX]
  ring

/-- The actual finite reopened sum has the normalized row-independent
cube coefficient needed by the parent provider. All arithmetic factors
and the original joint profile remain inside the defined finite source. -/
theorem reopened_sum_eq_source
    (P : Ideal (𝓞 K) → Prop) (B N : Finset (Ideal (𝓞 K)))
    (H X : ℝ) (hH : 0 < H) (hX : 0 < X)
    (gamma : Ideal (𝓞 K) → ℂ) (staticTau rowTau : Ideal (𝓞 K) →* ℂ)
    (d : Ideal (𝓞 K) → ℂ) (W : SchwartzMap ℝ ℂ)
    (hb : ∀ b ∈ B, b ≠ ⊥) (hn : ∀ C ∈ N, C ≠ ⊥ ∧ Squarefree C) :
    (∑ b ∈ B, ∑ C ∈ N, reopenedCubeCoefficient P b *
      canonicalCompletedTerm gamma (staticTau * rowTau) d (canonicalVstar W) X (C, b)) =
      (sourceScale B H X : ℂ) * source B N cubeIdealNorm cubeIdealNorm
        (fun b C => normalizedCubeBaseCoefficient P B H staticTau b *
          rowTau b ^ 3 * gamma C * staticTau C * rowTau C * d (C * b ^ 3)) W X := by
  rw [source, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hbB
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C hCN
  rw [reopenedCubeTerm_vstar P gamma staticTau rowTau d W X C b
    (hn C hCN).1 (hb b hbB) hX, if_pos (hn C hCN).2]
  have hc := sourceScale_mul_coefficient P B H X hH staticTau b
  rw [mul_comm (cubeIdealNorm b ^ 3) (cubeIdealNorm C)]
  linear_combination -(rowTau b ^ 3 * gamma C * staticTau C * rowTau C *
    d (C * b ^ 3) * W (cubeIdealNorm C * cubeIdealNorm b ^ 3 / X)) * hc

/-- Cancellation against the provider's normalization at the genuine
shifted column scale. -/
theorem parent_normalization_cancel (cap H X L U s : ℝ)
    (hH : 0 < H) (hX : 0 < X) (hL : 0 < L)
    (hU : U = s * X / H ^ 3) :
    L⁻¹ * (cap ^ 2 * (2 * H / X)) * (U * H ^ 2 * L) = 2 * cap ^ 2 * s := by
  rw [hU]
  field_simp [hH.ne', hX.ne', hL.ne'] <;> ring

/-- The remaining shifted total-length factor contributes only one
more fixed scale, so the original total length is retained exactly. -/
theorem parent_output_scale_cancel (cap H X L U s : ℝ)
    (hH : 0 < H) (hX : 0 < X) (hL : 0 < L)
    (hU : U = s * X / H ^ 3) :
    L⁻¹ * (cap ^ 2 * (2 * H / X)) *
        (U * H ^ 2 * L) * (U * H ^ 3 * L) =
      2 * cap ^ 2 * s ^ 2 * (X * L) := by
  rw [parent_normalization_cancel cap H X L U s hH hX hL hU, hU]
  field_simp [hH.ne'] <;> ring

/-- At a bounded column scale, the actual cube count is proportional
to `H`. Its square cancels against the exact source factor whenever
the genuine source support gives `H^3 ≤ 2X`. What remains is the row
mass, with no power of the cube scale. -/
theorem bounded_column_normalization (cap H X L R C D : ℝ)
    (hX : 0 < X) (hL : 0 < L) (hR : 0 ≤ R) (hHX : H ^ 3 ≤ 2 * X) :
    L⁻¹ * (cap ^ 2 * (2 * H / X)) * (L * R * (C * H * D) ^ 2) ≤
      4 * cap ^ 2 * R * C ^ 2 * D ^ 2 := by
  have hh : H ^ 3 / X ≤ 2 := (div_le_iff₀ hX).mpr hHX
  calc
    _ = (2 * cap ^ 2 * R * C ^ 2 * D ^ 2) * (H ^ 3 / X) := by
      field_simp [hX.ne', hL.ne'] <;> ring
    _ ≤ (2 * cap ^ 2 * R * C ^ 2 * D ^ 2) * 2 :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionProfile
