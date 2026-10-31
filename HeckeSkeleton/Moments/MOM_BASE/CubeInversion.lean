import HeckeSkeleton.Moments.MOM_BASE.CubeMobius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Order.Compact

/-!
# The weighted canonical cube inversion

This is the exact coefficient identity in Lemma 4.3. All sums are over
actual integral ideals. The Möbius function is the ideal Möbius function,
the norm is the actual absolute ideal norm, and `tau` may include any
completely multiplicative original coprimality masks. The whole-index
weight is arbitrary: compact support of the test proves finiteness.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_BASE

open scoped NumberField Classical BigOperators
open UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]

def cubeIdealNorm (I : Ideal (𝓞 K)) : ℝ := I.absNorm

@[simp] theorem cubeIdealNorm_bot : cubeIdealNorm (⊥ : Ideal (𝓞 K)) = 0 := by
  simp [cubeIdealNorm]

@[simp] theorem cubeIdealNorm_top : cubeIdealNorm (⊤ : Ideal (𝓞 K)) = 1 := by
  simp [cubeIdealNorm]

@[simp] theorem cubeIdealNorm_mul (I J : Ideal (𝓞 K)) :
    cubeIdealNorm (I * J) = cubeIdealNorm I * cubeIdealNorm J := by
  simp [cubeIdealNorm, map_mul]

theorem cubeIdealNorm_one_le {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    1 ≤ cubeIdealNorm I := by
  have hN : I.absNorm ≠ 0 := by
    simpa only [Ideal.absNorm_eq_zero_iff] using hI
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN

theorem cubeIdealNorm_pos {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    0 < cubeIdealNorm I := lt_of_lt_of_le zero_lt_one (cubeIdealNorm_one_le hI)

/-- The literal squarefree/cube coefficient with its whole-index weight.
The denominator makes the summand zero if either ideal is zero. -/
def canonicalCompletedTerm (gamma : Ideal (𝓞 K) → ℂ)
    (tau : Ideal (𝓞 K) →* ℂ) (d : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (CB : Ideal (𝓞 K) × Ideal (𝓞 K)) : ℂ :=
  if Squarefree CB.1 then
    gamma CB.1 * tau (CB.1 * CB.2 ^ 3) /
      ((Real.sqrt (cubeIdealNorm CB.1) : ℂ) * (cubeIdealNorm CB.2 : ℂ)) *
      d (CB.1 * CB.2 ^ 3) * V (cubeIdealNorm CB.1 * cubeIdealNorm CB.2 ^ 3 / X)
  else 0

def canonicalCompletedSum (gamma : Ideal (𝓞 K) → ℂ)
    (tau : Ideal (𝓞 K) →* ℂ) (d : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' C : Ideal (𝓞 K), ∑' B : Ideal (𝓞 K),
    canonicalCompletedTerm gamma tau d V X (C, B)

@[simp] theorem canonicalCompletedTerm_bot_left (gamma : Ideal (𝓞 K) → ℂ)
    (tau : Ideal (𝓞 K) →* ℂ) (d : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (B : Ideal (𝓞 K)) :
    canonicalCompletedTerm gamma tau d V X (⊥, B) = 0 := by
  simp [canonicalCompletedTerm]

@[simp] theorem canonicalCompletedTerm_bot_right (gamma : Ideal (𝓞 K) → ℂ)
    (tau : Ideal (𝓞 K) →* ℂ) (d : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (C : Ideal (𝓞 K)) :
    canonicalCompletedTerm gamma tau d V X (C, ⊥) = 0 := by
  simp [canonicalCompletedTerm]

/-- A test bounded above in its positive support makes the completed
sum finite, even for unbounded whole-index coefficients `d`. -/
theorem canonicalCompletedTerm_finite_support (gamma : Ideal (𝓞 K) → ℂ)
    (tau : Ideal (𝓞 K) →* ℂ) (d : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X U : ℝ) (hX : 0 < X)
    (hV : Function.support V ⊆ Set.Iic U) :
    Function.HasFiniteSupport (canonicalCompletedTerm gamma tau d V X) := by
  classical
  have hfin := DedekindZetaZeroFree.LargeSieve.finite_ideals_absNorm_le K (U * X)
  apply (hfin.prod hfin).subset
  rintro ⟨C, B⟩ hCB
  have hC0 : C ≠ ⊥ := by
    intro hz
    exact hCB (by simpa only [hz] using canonicalCompletedTerm_bot_left gamma tau d V X B)
  have hB0 : B ≠ ⊥ := by
    intro hz
    exact hCB (by simpa only [hz] using canonicalCompletedTerm_bot_right gamma tau d V X C)
  have ht : V (cubeIdealNorm C * cubeIdealNorm B ^ 3 / X) ≠ 0 := by
    intro hz
    exact hCB (by simp [canonicalCompletedTerm, hz])
  have hprod : cubeIdealNorm C * cubeIdealNorm B ^ 3 ≤ U * X :=
    (div_le_iff₀ hX).mp (hV ht)
  have hC : 1 ≤ cubeIdealNorm C := cubeIdealNorm_one_le hC0
  have hB : 1 ≤ cubeIdealNorm B := cubeIdealNorm_one_le hB0
  have hB3 : 1 ≤ cubeIdealNorm B ^ 3 := one_le_pow₀ hB
  have hB2 : 1 ≤ cubeIdealNorm B ^ 2 := one_le_pow₀ hB
  have hCBound : cubeIdealNorm C ≤ U * X := by
    calc
      _ = cubeIdealNorm C * 1 := (mul_one _).symm
      _ ≤ cubeIdealNorm C * cubeIdealNorm B ^ 3 :=
        mul_le_mul_of_nonneg_left hB3 (zero_le_one.trans hC)
      _ ≤ U * X := hprod
  have hBBound : cubeIdealNorm B ≤ U * X := by
    calc
      _ = cubeIdealNorm B * 1 := (mul_one _).symm
      _ ≤ cubeIdealNorm B * cubeIdealNorm B ^ 2 :=
        mul_le_mul_of_nonneg_left hB2 (zero_le_one.trans hB)
      _ = cubeIdealNorm B ^ 3 := by ring
      _ = 1 * cubeIdealNorm B ^ 3 := (one_mul _).symm
      _ ≤ cubeIdealNorm C * cubeIdealNorm B ^ 3 :=
        mul_le_mul_of_nonneg_right hC (pow_nonneg (zero_le_one.trans hB) _)
      _ ≤ U * X := hprod
  constructor
  · exact hCBound
  · exact hBBound

theorem canonicalCompletedTerm_summable (gamma : Ideal (𝓞 K) → ℂ)
    (tau : Ideal (𝓞 K) →* ℂ) (d : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X U : ℝ) (hX : 0 < X)
    (hV : Function.support V ⊆ Set.Iic U) :
    Summable (canonicalCompletedTerm gamma tau d V X) :=
  summable_of_hasFiniteSupport (canonicalCompletedTerm_finite_support gamma tau d V X U hX hV)

theorem canonicalCompletedSum_eq_tsum (gamma : Ideal (𝓞 K) → ℂ)
    (tau : Ideal (𝓞 K) →* ℂ) (d : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X U : ℝ) (hX : 0 < X)
    (hV : Function.support V ⊆ Set.Iic U) :
    canonicalCompletedSum gamma tau d V X =
      ∑' CB : Ideal (𝓞 K) × Ideal (𝓞 K), canonicalCompletedTerm gamma tau d V X CB :=
  (canonicalCompletedTerm_summable gamma tau d V X U hX hV).tsum_prod.symm

/-- Extraction of an entire cube, including the original masks and the
unchanged whole-index weight. No nonvanishing of `tau` is used. -/
theorem canonicalCompletedTerm_cube_extract (gamma : Ideal (𝓞 K) → ℂ)
    (tau : Ideal (𝓞 K) →* ℂ) (d : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (H C B : Ideal (𝓞 K)) :
    tau H ^ 3 / (cubeIdealNorm H : ℂ) *
      canonicalCompletedTerm gamma tau (fun A => d (H ^ 3 * A))
        V (X / cubeIdealNorm H ^ 3) (C, B) =
      canonicalCompletedTerm gamma tau d V X (C, H * B) := by
  by_cases hC : Squarefree C
  · have hwhole : C * (H * B) ^ 3 = H ^ 3 * (C * B ^ 3) := by
      simp only [mul_pow]
      ac_rfl
    have harg : cubeIdealNorm C * cubeIdealNorm B ^ 3 /
          (X / cubeIdealNorm H ^ 3) =
        cubeIdealNorm C * (cubeIdealNorm H * cubeIdealNorm B) ^ 3 / X := by
      simp only [div_div_eq_mul_div, mul_pow]
      ring
    simp only [canonicalCompletedTerm, hC, if_true, cubeIdealNorm_mul, harg,
      hwhole, map_mul, map_pow, Complex.ofReal_mul, div_eq_mul_inv, mul_inv_rev]
    ring
  · simp [canonicalCompletedTerm, hC]

/-- The extracted outer ideal series is summable. Thus the inversion uses
ordinary finite sums, independently of the default value of a divergent
`tsum`. -/
theorem canonicalCubeInversion_summable (gamma : Ideal (𝓞 K) → ℂ)
    (tau : Ideal (𝓞 K) →* ℂ) (d : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X U : ℝ) (hX : 0 < X)
    (hV : Function.support V ⊆ Set.Iic U) :
    Summable (fun H : Ideal (𝓞 K) => (moebius H : ℂ) * tau H ^ 3 /
      (cubeIdealNorm H : ℂ) *
        canonicalCompletedSum gamma tau (fun A => d (H ^ 3 * A))
          V (X / cubeIdealNorm H ^ 3)) := by
  have hs := (cube_moebius_dilates_summable
    (canonicalCompletedTerm gamma tau d V X)
    (canonicalCompletedTerm_finite_support gamma tau d V X U hX hV)
    (canonicalCompletedTerm_bot_right gamma tau d V X)).prod
  apply hs.congr
  intro H
  simp_rw [← canonicalCompletedTerm_cube_extract gamma tau d V X H]
  simp only [tsum_mul_left, canonicalCompletedSum]
  ring

/-- Lemma 4.3, weighted cube Möbius inversion on actual ideals. The test
support condition is automatic for compactly supported tests. -/
theorem canonicalCubeInversion (gamma : Ideal (𝓞 K) → ℂ)
    (tau : Ideal (𝓞 K) →* ℂ) (d : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X U : ℝ) (hX : 0 < X)
    (hV : Function.support V ⊆ Set.Iic U) :
    (∑' C : Ideal (𝓞 K), if Squarefree C then
      gamma C * tau C / (Real.sqrt (cubeIdealNorm C) : ℂ) *
        d C * V (cubeIdealNorm C / X) else 0) =
      ∑' H : Ideal (𝓞 K), (moebius H : ℂ) * tau H ^ 3 /
        (cubeIdealNorm H : ℂ) *
          canonicalCompletedSum gamma tau (fun A => d (H ^ 3 * A))
            V (X / cubeIdealNorm H ^ 3) := by
  have hbase := tsum_moebius_cube_dilates
    (canonicalCompletedTerm gamma tau d V X)
    (canonicalCompletedTerm_finite_support gamma tau d V X U hX hV)
    (canonicalCompletedTerm_bot_right gamma tau d V X)
  have hone (C : Ideal (𝓞 K)) :
      canonicalCompletedTerm gamma tau d V X (C, ⊤) =
        if Squarefree C then gamma C * tau C /
          (Real.sqrt (cubeIdealNorm C) : ℂ) * d C * V (cubeIdealNorm C / X)
        else 0 := by
    simp [canonicalCompletedTerm, ← Ideal.one_eq_top]
  simp_rw [hone] at hbase
  rw [hbase]
  apply tsum_congr
  intro H
  simp_rw [← canonicalCompletedTerm_cube_extract gamma tau d V X H]
  rw [tsum_mul_left, tsum_mul_left]
  unfold canonicalCompletedSum
  ring

/-- The compact-support form of the canonical coefficient/cube theorem. -/
theorem canonicalCubeInversion_of_hasCompactSupport
    (gamma : Ideal (𝓞 K) → ℂ) (tau : Ideal (𝓞 K) →* ℂ)
    (d : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (hX : 0 < X) (hV : HasCompactSupport V) :
    (∑' C : Ideal (𝓞 K), if Squarefree C then
      gamma C * tau C / (Real.sqrt (cubeIdealNorm C) : ℂ) *
        d C * V (cubeIdealNorm C / X) else 0) =
      ∑' H : Ideal (𝓞 K), (moebius H : ℂ) * tau H ^ 3 /
        (cubeIdealNorm H : ℂ) *
          canonicalCompletedSum gamma tau (fun A => d (H ^ 3 * A))
            V (X / cubeIdealNorm H ^ 3) := by
  obtain ⟨U, hU⟩ := (show IsCompact (tsupport V) from hV).bddAbove
  exact canonicalCubeInversion gamma tau d V X U hX
    (fun y hy => hU (subset_tsupport V hy))

/-- The central test used to identify the squarefree terminal with theta. -/
def canonicalVstar (W : ℝ → ℂ) (y : ℝ) : ℂ := (Real.sqrt y : ℂ) * W y

theorem canonicalVstar_normalization (W : ℝ → ℂ) (N X : ℝ)
    (hN : 0 < N) (hX : 0 < X) :
    (Real.sqrt N : ℂ)⁻¹ * canonicalVstar W (N / X) =
      (Real.sqrt X : ℂ)⁻¹ * W (N / X) := by
  have hsN : (Real.sqrt N : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hN).ne'
  simp only [canonicalVstar, Real.sqrt_div hN.le, Complex.ofReal_div,
    div_eq_mul_inv]
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hsN, one_mul]

theorem canonicalVstar_ideal_normalization (W : ℝ → ℂ) (C : Ideal (𝓞 K))
    (hC : C ≠ ⊥) (X : ℝ) (hX : 0 < X) :
    (Real.sqrt (cubeIdealNorm C) : ℂ)⁻¹ *
        canonicalVstar W (cubeIdealNorm C / X) =
      (Real.sqrt X : ℂ)⁻¹ * W (cubeIdealNorm C / X) :=
  canonicalVstar_normalization W (cubeIdealNorm C) X (cubeIdealNorm_pos hC) hX

end HeckeSkeleton.Moments.MOM_BASE
