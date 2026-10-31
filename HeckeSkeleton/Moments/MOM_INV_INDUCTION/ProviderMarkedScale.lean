import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedSlots
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedPools
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact initial marked normalization and strict margins

For extracted total slot length `G`, the new inverse length is
`L = r + z - 2 G`, its extra puncture is the actual extracted prime
product, and its surviving slot length is `z - G`.  The original square
root normalization is exactly `Z^(-G) / sqrt(Z^L)`.  The strict margins
and the quotient profile are retained as equalities before estimates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedScale

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open ProviderMarkedSlots
open scoped Classical BigOperators nonZeroDivisors

def columnLength (r z G : ℝ) : ℝ := r + z - 2 * G

theorem inverse_sqrt_rpow (Z r : ℝ) (hZ : 0 < Z) :
    (Real.sqrt (Z ^ r))⁻¹ = Z ^ (-r / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ.le, ← Real.rpow_neg hZ.le]
  congr 1
  ring

/-- Exact normalization of the original inverse and all prime slots. -/
theorem normalization (Z r z G : ℝ) (hZ : 0 < Z) :
    (Real.sqrt (Z ^ r))⁻¹ * (Real.sqrt (Z ^ z))⁻¹ =
      Z ^ (-G) * (Real.sqrt (Z ^ columnLength r z G))⁻¹ := by
  simp_rw [inverse_sqrt_rpow Z _ hZ]
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  unfold columnLength
  ring

theorem slot_normalization {ι : Type*} (I : Finset ι) (z : ι → ℝ)
    (Z : ℝ) (hZ : 0 < Z) :
    (∏ i ∈ I, (Real.sqrt (Z ^ z i))⁻¹) =
      (Real.sqrt (Z ^ ∑ i ∈ I, z i))⁻¹ := by
  simp_rw [inverse_sqrt_rpow Z _ hZ]
  rw [← Real.rpow_sum_of_pos hZ]
  congr 1
  rw [Finset.sum_div, Finset.sum_neg_distrib]

theorem complete_normalization {ι : Type*} (I : Finset ι) (z : ι → ℝ)
    (Z r G : ℝ) (hZ : 0 < Z) :
    (Real.sqrt (Z ^ r))⁻¹ * (∏ i ∈ I, (Real.sqrt (Z ^ z i))⁻¹) =
      Z ^ (-G) * (Real.sqrt (Z ^ columnLength r (∑ i ∈ I, z i) G))⁻¹ := by
  rw [slot_normalization I z Z hZ]
  exact normalization Z r _ G hZ

/-- The original norm quotient is unchanged by the actual overlap
identity `N(j) N(c) = N(n) N(P₀)`. -/
theorem profile_argument (Z r z G n j P c : ℝ) (hZ : 0 < Z) (hP : P ≠ 0)
    (hn : j * c = n * P) :
    n / Z ^ r =
      (j / Z ^ G) * (c / Z ^ columnLength r z G) / (P / Z ^ (z - G)) := by
  have hbalance : Z ^ G * Z ^ columnLength r z G = Z ^ r * Z ^ (z - G) := by
    rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
    congr 1
    unfold columnLength
    ring
  symm
  calc
    _ = (j * c * Z ^ (z - G)) / (Z ^ G * Z ^ columnLength r z G * P) := by
      field_simp [(Real.rpow_pos_of_pos hZ G).ne',
        (Real.rpow_pos_of_pos hZ (columnLength r z G)).ne',
        (Real.rpow_pos_of_pos hZ (z - G)).ne', hP]
      <;> ring
    _ = (n * P * Z ^ (z - G)) / (Z ^ r * Z ^ (z - G) * P) := by rw [hn, hbalance]
    _ = n / Z ^ r := by
      field_simp [(Real.rpow_pos_of_pos hZ r).ne',
        (Real.rpow_pos_of_pos hZ (z - G)).ne', hP]

theorem first_margin (m r z G : ℝ) :
    m - columnLength r z G - G - (z - G) = m - r - 2 * z + 2 * G := by
  unfold columnLength
  ring

theorem second_margin (m r z G : ℝ) :
    3 * m - 2 * columnLength r z G - 6 * (z - G) =
      3 * m - 2 * r - 8 * z + 10 * G := by
  unfold columnLength
  ring

/-- Extracting genuine common slots improves both original margins. -/
theorem strict_margins (m r z G c : ℝ) (hG : 0 ≤ G)
    (hfirst : r + 2 * z ≤ m - c) (hsecond : 2 * r + 8 * z ≤ 3 * m - c) :
    columnLength r z G + G + (z - G) ≤ m - c ∧
      2 * columnLength r z G + 6 * (z - G) ≤ 3 * m - c := by
  unfold columnLength
  constructor <;> linarith

/-- Fixed support constants, the chosen annulus shift, and the actual
puncture norm are all charged explicitly to the initial strict margin. -/
theorem shifted_strict_margins (m r z G c s q : ℝ) (hG : 0 ≤ G)
    (hfirst : r + 2 * z ≤ m - c) (hsecond : 2 * r + 8 * z ≤ 3 * m - c)
    (hsq : s + q ≤ c / 2) (hs : 2 * s ≤ c / 2) :
    (columnLength r z G + s) + (G + q) + (z - G) ≤ m - c / 2 ∧
      2 * (columnLength r z G + s) + 6 * (z - G) ≤ 3 * m - c / 2 := by
  obtain ⟨h1, h2⟩ := strict_margins m r z G c hG hfirst hsecond
  constructor <;> linarith

variable {K : Type} [Field K] [NumberField K]
variable {ι : Type*} [DecidableEq ι]

/-- The normalized product is the product of the actual individual
normalized prime norms, rather than a new unconstrained coefficient. -/
theorem normalized_primeProduct (I : Finset ι)
    (p : ι → HeightOneSpectrum (𝓞 K)) (z : ι → ℝ) (Z : ℝ) (hZ : 0 < Z) :
    ProviderMarkedPools.norm (primeProduct I p) / Z ^ (∑ i ∈ I, z i) =
      ∏ i ∈ I, ProviderMarkedPools.norm (p i).asIdeal / Z ^ z i := by
  rw [Finset.prod_div_distrib, ← Real.rpow_sum_of_pos hZ]
  simp only [ProviderMarkedPools.norm, primeProduct, map_prod, Nat.cast_prod]

theorem normalized_primeProduct_bounds (I : Finset ι)
    (p : ι → HeightOneSpectrum (𝓞 K)) (z : ι → ℝ) (Z : ℝ) (hZ : 0 < Z)
    (hp : ∀ i ∈ I, Z ^ z i ≤ ProviderMarkedPools.norm (p i).asIdeal ∧
      ProviderMarkedPools.norm (p i).asIdeal ≤ 2 * Z ^ z i) :
    1 ≤ ProviderMarkedPools.norm (primeProduct I p) / Z ^ (∑ i ∈ I, z i) ∧
      ProviderMarkedPools.norm (primeProduct I p) / Z ^ (∑ i ∈ I, z i) ≤ (2 : ℝ) ^ I.card := by
  rw [normalized_primeProduct I p z Z hZ]
  have hlo (i : ι) (hi : i ∈ I) :
      1 ≤ ProviderMarkedPools.norm (p i).asIdeal / Z ^ z i :=
    (one_le_div (Real.rpow_pos_of_pos hZ _)).mpr (hp i hi).1
  have hhi (i : ι) (hi : i ∈ I) :
      ProviderMarkedPools.norm (p i).asIdeal / Z ^ z i ≤ 2 :=
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mpr (hp i hi).2
  constructor
  · exact Finset.one_le_prod fun i hi => hlo i hi
  · calc
      _ ≤ ∏ i ∈ I, (2 : ℝ) := Finset.prod_le_prod
        (fun i hi => (zero_le_one.trans (hlo i hi))) hhi
      _ = _ := by rw [Finset.prod_const]

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedScale
