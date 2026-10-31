module

public import HeckeSkeleton.Moments.MOM_INV_STEP.FixedTripleFibers
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Logarithmic geometry from the actual source ideals

These bounds start with the norm identities in `FixedTripleFibers.Valid`.
The annular hypotheses concern the original cube ideals, their active
conductor, the cube label, and the second common factor and divisor.
The child length and puncture inequalities are conclusions of those source
hypotheses. In particular, the sharper cube-quotient bound is used only for
counting distinct triples; the puncture bound uses the separate coarse bound.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOMInvStep.SourceLengths

open NumberField IsDedekindDomain FixedTripleFibers
open scoped Classical NumberField

variable {K : Type*} [Field K] [NumberField K] {Sector : Type*}
variable {sectorTransport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector)}

theorem one_le_norm_cap (I : Ideal (𝓞 K)) (hI : I ≠ 0) (X : ℝ)
    (hX : (Ideal.absNorm I : ℝ) ≤ X) : 1 ≤ X := by
  have hn : 1 ≤ Ideal.absNorm I := Nat.one_le_iff_ne_zero.mpr
    (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hnR : (1 : ℝ) ≤ Ideal.absNorm I := by exact_mod_cast hn
  exact hnR.trans hX

theorem norm_box_caps_one (γ : OuterTriple K) (Xq Xt Xr : ℝ)
    (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (hbox : (Ideal.absNorm γ.q0 : ℝ) ≤ Xq ∧
      (Ideal.absNorm γ.quotient : ℝ) ≤ Xt ∧
      (Ideal.absNorm γ.residual : ℝ) ≤ Xr) :
    1 ≤ Xq ∧ 1 ≤ Xt ∧ 1 ≤ Xr :=
  ⟨one_le_norm_cap _ hq _ hbox.1,
    one_le_norm_cap _ ht _ hbox.2.1, one_le_norm_cap _ hr _ hbox.2.2⟩

theorem cube_product_ne_zero {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector}
    (hx : Valid sectorTransport x γ f k) (hf : f ≠ 0) (hq : γ.q0 ≠ 0) :
    x.core 4 * x.secondCube ≠ 0 := by
  have hj : x.cubeResidual ≠ 0 := by
    intro hz
    have he := hx.j_split
    rw [hz, mul_zero] at he
    exact core_ne_zero hx hf hq 0 he.symm
  rw [hx.b_split]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hq) (pow_ne_zero 2 hj))
    (core_ne_zero hx hf hq 3)

/-- The second divisor divides the original common factor. Its two
annular errors account for precisely the allowed negative common gap. -/
theorem common_gap {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector}
    (hx : Valid sectorTransport x γ f k) (hg0 : x.extractedCommon ≠ 0)
    (Z g theta eta : ℝ) (hZ : 1 < Z)
    (hd : Z ^ (theta - eta) ≤ (Ideal.absNorm (x.core 2) : ℝ))
    (hg : (Ideal.absNorm x.extractedCommon : ℝ) ≤ Z ^ (g + eta)) :
    -2 * eta ≤ g - theta := by
  have hdiv : (Ideal.absNorm (x.core 2) : ℝ) ≤ Ideal.absNorm x.extractedCommon := by
    exact_mod_cast second_divisor_norm_le_common hx hg0
  have he := (Real.rpow_le_rpow_left_iff hZ).mp (hd.trans (hdiv.trans hg))
  linarith

/-- The residual common factor is bounded using its exact multiplicative
identity, before the triple range is enlarged. -/
theorem common_residual_bound {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector}
    (hx : Valid sectorTransport x γ f k)
    (Z g theta eta : ℝ) (hZ : 0 < Z)
    (hd : Z ^ (theta - eta) ≤ (Ideal.absNorm (x.core 2) : ℝ))
    (hg : (Ideal.absNorm x.extractedCommon : ℝ) ≤ Z ^ (g + eta)) :
    (Ideal.absNorm γ.residual : ℝ) ≤ Z ^ (g - theta + 2 * eta) := by
  calc
    _ ≤ Z ^ (g + eta) / Z ^ (theta - eta) := by
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hZ _)).mpr
      calc
        _ ≤ (Ideal.absNorm γ.residual : ℝ) * Ideal.absNorm (x.core 2) :=
          mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _)
        _ = (Ideal.absNorm x.extractedCommon : ℝ) := by
          rw [second_common_norm_eq hx, Nat.cast_mul]
          ring
        _ ≤ _ := hg
    _ = _ := by
      rw [← Real.rpow_sub hZ]
      congr 1
      ring

/-- The child cube label divides the actual product of the two original
cube ideals. The two upper errors and one lower error give `3 eta`. -/
theorem cube_label_length {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector}
    (hx : Valid sectorTransport x γ f k) (hf : f ≠ 0) (hq : γ.q0 ≠ 0)
    (Z ell j eta : ℝ) (hZ : 1 < Z)
    (hb1 : (Ideal.absNorm (x.core 4) : ℝ) ≤ Z ^ (ell + eta))
    (hb2 : (Ideal.absNorm x.secondCube : ℝ) ≤ Z ^ (ell + eta))
    (hJ : Z ^ (j - eta) ≤ (Ideal.absNorm (x.core 0) : ℝ)) :
    j ≤ 2 * ell + 3 * eta := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hprod : (Ideal.absNorm (x.core 0) : ℝ) ≤
      (Ideal.absNorm (x.core 4) : ℝ) * Ideal.absNorm x.secondCube := by
    exact_mod_cast cube_label_norm_le hx (cube_product_ne_zero hx hf hq)
  have hb := mul_le_mul hb1 hb2 (Nat.cast_nonneg _) (Real.rpow_nonneg hz.le _)
  have hh : Z ^ (j - eta) ≤ Z ^ (2 * ell + 2 * eta) := by
    calc
      _ ≤ (Ideal.absNorm (x.core 4) : ℝ) * Ideal.absNorm x.secondCube := hJ.trans hprod
      _ ≤ Z ^ (ell + eta) * Z ^ (ell + eta) := hb
      _ = _ := by rw [← Real.rpow_add hz]; congr 1 <;> ring
  have he := (Real.rpow_le_rpow_left_iff hZ).mp hh
  linarith

/-- The coarse cube-quotient bound used in the puncture budget. It does
not charge the active-conductor length or the averaged cube-label length. -/
theorem cube_quotient_bound {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector}
    (hx : Valid sectorTransport x γ f k) (hf : f ≠ 0) (hq : γ.q0 ≠ 0)
    (Z ell eta : ℝ) (hZ : 0 < Z)
    (hb1 : (Ideal.absNorm (x.core 4) : ℝ) ≤ Z ^ (ell + eta))
    (hb2 : (Ideal.absNorm x.secondCube : ℝ) ≤ Z ^ (ell + eta)) :
    (Ideal.absNorm γ.q0 : ℝ) ≤ Z ^ (ell + eta) := by
  apply (sq_le_sq₀ (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)).mp
  calc
    _ ≤ (Ideal.absNorm (x.core 4) : ℝ) * Ideal.absNorm x.secondCube := by
      exact_mod_cast cube_quotient_norm_sq_le hx hf hq
    _ ≤ Z ^ (ell + eta) * Z ^ (ell + eta) :=
      mul_le_mul hb1 hb2 (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
    _ = _ := (pow_two _).symm

/-- The odd cube support lies in the actual active conductor. Dividing
the resulting squared norm identity by the cube-label lower bound gives
the sharp frozen-triple counting length, including its `5 eta / 2` error. -/
theorem cube_quotient_sharp_bound {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector}
    (hx : Valid sectorTransport x γ f k) (R1 : Ideal (𝓞 K))
    (hR1 : R1 ≠ 0) (hs : x.core 3 ∣ R1)
    (Z ell R j eta : ℝ) (hZ : 0 < Z)
    (hb1 : (Ideal.absNorm (x.core 4) : ℝ) ≤ Z ^ (ell + eta))
    (hb2 : (Ideal.absNorm x.secondCube : ℝ) ≤ Z ^ (ell + eta))
    (hR : (Ideal.absNorm R1 : ℝ) ≤ Z ^ (R + eta))
    (hJ : Z ^ (j - eta) ≤ (Ideal.absNorm (x.core 0) : ℝ)) :
    (Ideal.absNorm γ.q0 : ℝ) ≤ Z ^ (ell + R / 2 - j + 5 * eta / 2) := by
  have hpair := mul_le_mul hb1 hb2 (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
  have hall := mul_le_mul hpair hR (Nat.cast_nonneg _)
    (mul_nonneg (Real.rpow_nonneg hZ.le _) (Real.rpow_nonneg hZ.le _))
  have hnorm : (Ideal.absNorm γ.q0 : ℝ) ^ 2 * (Ideal.absNorm (x.core 0) : ℝ) ^ 2 ≤
      (Ideal.absNorm (x.core 4) : ℝ) * Ideal.absNorm x.secondCube * Ideal.absNorm R1 := by
    exact_mod_cast cube_quotient_label_norm_le hx R1 hR1 hs
  have hsquare : ((Ideal.absNorm γ.q0 : ℝ) * Z ^ (j - eta)) ^ 2 ≤
      (Z ^ (ell + R / 2 + 3 * eta / 2)) ^ 2 := by
    calc
      _ = (Ideal.absNorm γ.q0 : ℝ) ^ 2 * (Z ^ (j - eta)) ^ 2 := mul_pow _ _ _
      _ ≤ (Ideal.absNorm γ.q0 : ℝ) ^ 2 * (Ideal.absNorm (x.core 0) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Real.rpow_nonneg hZ.le _) hJ 2) (sq_nonneg _)
      _ ≤ (Ideal.absNorm (x.core 4) : ℝ) * Ideal.absNorm x.secondCube * Ideal.absNorm R1 := hnorm
      _ ≤ Z ^ (ell + eta) * Z ^ (ell + eta) * Z ^ (R + eta) := hall
      _ = _ := by
        rw [← Real.rpow_add hZ, ← Real.rpow_add hZ,
          ← Real.rpow_mul_natCast hZ.le]
        congr 1
        ring
  have hroot := (sq_le_sq₀
    (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _))
    (Real.rpow_nonneg hZ.le _)).mp hsquare
  calc
    _ ≤ Z ^ (ell + R / 2 + 3 * eta / 2) / Z ^ (j - eta) :=
      (le_div_iff₀ (Real.rpow_pos_of_pos hZ _)).mpr hroot
    _ = _ := by
      rw [← Real.rpow_sub hZ]
      congr 1
      ring

theorem radical_ne_zero (I : Ideal (𝓞 K)) (hI : I ≠ 0) : I.radical ≠ 0 := by
  intro hz
  exact hI (le_bot_iff.mp (hz ▸ (Ideal.le_radical : I ≤ I.radical)))

/-- The common puncture uses only the old puncture and the frozen triple.
Every original source norm is charged once, with total error `4 eta`. -/
theorem puncture_norm_bound (Rho : Ideal (𝓞 K)) (γ : OuterTriple K)
    (hRho : Rho ≠ 0) (hq0 : γ.q0 ≠ 0) (ht0 : γ.quotient ≠ 0) (hr0 : γ.residual ≠ 0)
    (Z Q ell t g theta eta : ℝ) (hZ : 0 < Z)
    (hR : (Ideal.absNorm Rho.radical : ℝ) ≤ Z ^ Q)
    (hq : (Ideal.absNorm γ.q0 : ℝ) ≤ Z ^ (ell + eta))
    (ht : (Ideal.absNorm γ.quotient : ℝ) ≤ Z ^ (t + eta))
    (hr : (Ideal.absNorm γ.residual : ℝ) ≤ Z ^ (g - theta + 2 * eta)) :
    (Ideal.absNorm (childPuncture Rho γ).radical : ℝ) ≤
      Z ^ (Q + ell + t + g - theta + 4 * eta) := by
  have h01 := mul_le_mul hR hq (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
  have h012 := mul_le_mul h01 ht (Nat.cast_nonneg _)
    (mul_nonneg (Real.rpow_nonneg hZ.le _) (Real.rpow_nonneg hZ.le _))
  have h0123 := mul_le_mul h012 hr (Nat.cast_nonneg _)
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ.le _) (Real.rpow_nonneg hZ.le _))
      (Real.rpow_nonneg hZ.le _))
  calc
    _ ≤ (Ideal.absNorm Rho.radical : ℝ) * Ideal.absNorm γ.q0 *
        Ideal.absNorm γ.quotient * Ideal.absNorm γ.residual := by
      exact_mod_cast childPuncture_radical_norm_le Rho γ hRho hq0 ht0 hr0
    _ ≤ Z ^ Q * Z ^ (ell + eta) * Z ^ (t + eta) * Z ^ (g - theta + 2 * eta) := h0123
    _ = _ := by
      rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ]
      congr 1
      ring

/-- The logarithmic puncture budget has the exact form required by the
child margins. The nonnegative extracted length and old label length are
added only at the final inequality. -/
theorem puncture_length (Rho : Ideal (𝓞 K)) (γ : OuterTriple K)
    (hRho : Rho ≠ 0) (hq0 : γ.q0 ≠ 0) (ht0 : γ.quotient ≠ 0) (hr0 : γ.residual ≠ 0)
    (Z Q ell A t g theta V eta : ℝ) (hZ : 1 < Z) (hA : 0 ≤ A) (hV : 0 ≤ V)
    (hR : (Ideal.absNorm Rho.radical : ℝ) ≤ Z ^ Q)
    (hq : (Ideal.absNorm γ.q0 : ℝ) ≤ Z ^ (ell + eta))
    (ht : (Ideal.absNorm γ.quotient : ℝ) ≤ Z ^ (t + eta))
    (hr : (Ideal.absNorm γ.residual : ℝ) ≤ Z ^ (g - theta + 2 * eta)) :
    Real.logb Z (Ideal.absNorm (childPuncture Rho γ).radical : ℝ) ≤
      Q + (ell + A + t + g - theta + V) + 4 * eta := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hp : childPuncture Rho γ ≠ 0 :=
    mul_ne_zero hRho (radical_ne_zero _ (mul_ne_zero (mul_ne_zero hq0 ht0) hr0))
  have hn : 0 < (Ideal.absNorm (childPuncture Rho γ).radical : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (fun he => radical_ne_zero _ hp (Ideal.absNorm_eq_zero_iff.mp he))
  have hh := (Real.logb_le_iff_le_rpow hZ hn).mpr
    (puncture_norm_bound Rho γ hRho hq0 ht0 hr0 Z Q ell t g theta eta hz hR hq ht hr)
  linarith

/-- The complete puncture budget from original cube and second-common
annuli. The coarse quotient and residual bounds are proved internally. -/
theorem puncture_length_from_source {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector}
    (hx : Valid sectorTransport x γ f k) (hf : f ≠ 0)
    (Rho : Ideal (𝓞 K)) (hRho : Rho ≠ 0)
    (hq0 : γ.q0 ≠ 0) (ht0 : γ.quotient ≠ 0) (hr0 : γ.residual ≠ 0)
    (Z Q ell A t g theta V eta : ℝ) (hZ : 1 < Z) (hA : 0 ≤ A) (hV : 0 ≤ V)
    (hR : (Ideal.absNorm Rho.radical : ℝ) ≤ Z ^ Q)
    (hb1 : (Ideal.absNorm (x.core 4) : ℝ) ≤ Z ^ (ell + eta))
    (hb2 : (Ideal.absNorm x.secondCube : ℝ) ≤ Z ^ (ell + eta))
    (ht : (Ideal.absNorm γ.quotient : ℝ) ≤ Z ^ (t + eta))
    (hd : Z ^ (theta - eta) ≤ (Ideal.absNorm (x.core 2) : ℝ))
    (hg : (Ideal.absNorm x.extractedCommon : ℝ) ≤ Z ^ (g + eta)) :
    Real.logb Z (Ideal.absNorm (childPuncture Rho γ).radical : ℝ) ≤
      Q + (ell + A + t + g - theta + V) + 4 * eta :=
  puncture_length Rho γ hRho hq0 ht0 hr0 Z Q ell A t g theta V eta hZ hA hV hR
    (cube_quotient_bound hx hf hq0 Z ell eta (zero_lt_one.trans hZ) hb1 hb2) ht
    (common_residual_bound hx Z g theta eta (zero_lt_one.trans hZ) hd hg)

end HeckeSkeleton.Moments.MOMInvStep.SourceLengths

end
