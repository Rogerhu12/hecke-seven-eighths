import HeckeSkeleton.LowEnergy.ActualFrozenCharges
import HeckeSkeleton.LowEnergy.GeneralBlockPolynomial

/-!
# Conductor charges with a squarefree label and an arbitrary puncture

The frozen row is `R * label^4`.  The charged inequality is proved by
prime exponents of these actual ideals.  In particular the label is paid
once, even though its fourth power occurs in the theta frequency.  The
puncture is paid once, and the complete powerful part of R is restored
on the left.  No conductor comparison is an input to the result.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GeneralConductor

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.IdealRows
open HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualFrozenCube
open HeckeSkeleton.LowEnergy.ActualFrozenIndependence
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualFrozenCharges
open HeckeSkeleton.LowEnergy.LogGeometry
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem primeSetIdeal_exponent (T : Finset (ExteriorPrime K S)) (p : ExteriorPrime K S) :
    primeExponents (primeSetIdeal K S T).val p.val = if p ∈ T then 1 else 0 := by
  have hs : Squarefree (primeSetIdeal K S T).val.val :=
    HeckeGeneral.Arithmetic.IdealMobiusMask.squarefree_primeProduct _
  have hle := exponent_le_one_of_squarefree (primeSetIdeal K S T).val hs p.val
  have hiff := (exponent_ne_zero_iff_dvd (primeSetIdeal K S T).val p.val).trans
    (prime_dvd_primeSetIdeal_iff K S T p)
  by_cases hp : p ∈ T
  · rw [if_pos hp]
    have hn := hiff.mpr hp
    omega
  · rw [if_neg hp]
    by_contra hn
    exact hp (hiff.mp hn)

theorem exterior_exponent_zero {I : ExteriorIdeal K S} {p : HeightOneSpectrum (𝓞 K)}
    (hp : p ∈ S) : primeExponents I.val p = 0 := by
  by_contra he
  exact I.property p ((exponent_ne_zero_iff_dvd I.val p).mp he) hp

/-- The complete local conductor inequality, including the j=0 and j=4
small branches and the minimum cube branch. -/
theorem local_conductor (e l r m : ℕ) (hl : l ≤ 1) (hr : r ≤ 1)
    (hm : m = 0 ∨ m = 1 ∨ m = 3) (hactive : e + 4 * l ≠ 0 ∨ r ≠ 0) :
    2 + (if 2 ≤ e then e else 0) ≤
      (if m = 1 then 1 else 0) +
      (if m = 0 ∧ ((e + 4 * l) % 6 = 0 ∨ (e + 4 * l) % 6 = 4) then 1 else 0) +
      4 * (if m = 3 then 1 else 0) + 2 * e + l + r := by
  by_cases he : 2 ≤ e
  · rw [if_pos he]
    omega
  · have he' : e = 0 ∨ e = 1 := by omega
    have hl' : l = 0 ∨ l = 1 := by omega
    have hr' : r = 0 ∨ r = 1 := by omega
    rcases he' with rfl | rfl <;>
      rcases hl' with rfl | rfl <;>
      rcases hr' with rfl | rfl <;>
      rcases hm with rfl | rfl | rfl <;> norm_num at *

/-- An exact divisibility statement for the actual local charge ideals. -/
theorem conductor_charge_dvd (R label puncture : ExteriorIdeal K S)
    (hlabel : Squarefree label.val.val) (hpuncture : Squarefree puncture.val.val)
    (s : FrozenState K S (exteriorMul K S R (exteriorPower K S label 4)) puncture) :
    (primeSetIdeal K S s.active).val.val ^ 2 * (powerfulPart R.val).val ∣
      (minimumLinearIdeal K S s).val.val * (minimumSmallIdeal K S s).val.val *
      (minimumCubeIdeal K S s).val.val ^ 4 * R.val.val ^ 2 * label.val.val * puncture.val.val := by
  let L := (primeSetIdeal K S s.active).val ^ 2 * powerfulPart R.val
  let B := (minimumLinearIdeal K S s).val * (minimumSmallIdeal K S s).val *
    (minimumCubeIdeal K S s).val ^ 4 * R.val ^ 2 * label.val * puncture.val
  change L.val ∣ B.val
  apply dvd_of_exponents_le L B
  intro p
  dsimp only [L, B]
  simp only [primeExponents_mul, Finsupp.add_apply, exponent_pow, exponent_powerfulPart]
  by_cases hpS : p ∈ S
  · simp only [exterior_exponent_zero K S hpS]
    norm_num
  · let ep : ExteriorPrime K S := ⟨p, hpS⟩
    have hA := primeSetIdeal_exponent K S s.active ep
    have hN := primeSetIdeal_exponent K S (minimumLinearPrimes K S s) ep
    have hS := primeSetIdeal_exponent K S (minimumSmallPrimes K S s) ep
    have hB := primeSetIdeal_exponent K S (minimumCubePrimes K S s) ep
    change primeExponents (minimumLinearIdeal K S s).val p = _ at hN
    change primeExponents (minimumSmallIdeal K S s).val p = _ at hS
    change primeExponents (minimumCubeIdeal K S s).val p = _ at hB
    change primeExponents (primeSetIdeal K S s.active).val p = _ at hA
    rw [hA, hN, hS, hB]
    by_cases hp : ep ∈ s.active
    · have hs := s.active_subset hp
      have hactive : primeExponents R.val p + 4 * primeExponents label.val p ≠ 0 ∨
          primeExponents puncture.val p ≠ 0 := by
        rcases Finset.mem_union.mp hs with hF | hR
        · left
          have he := (exponent_ne_zero_iff_dvd
            (exteriorMul K S R (exteriorPower K S label 4)).val p).mpr
            ((mem_exteriorSupport_iff K S _ ep).mp hF)
          simpa only [exteriorMul, exteriorPower, primeExponents_mul, Finsupp.add_apply,
            exponent_pow] using he
        · right
          exact (exponent_ne_zero_iff_dvd puncture.val p).mpr
            ((mem_exteriorSupport_iff K S puncture ep).mp hR)
      have hdigit : (frozenDigit K S (exteriorMul K S R (exteriorPower K S label 4)) ep).val =
          (primeExponents R.val p + 4 * primeExponents label.val p) % 6 := by
        simp only [frozenDigit, exteriorMul, exteriorPower, primeExponents_mul,
          Finsupp.add_apply, exponent_pow, ep]
      have hNmem : ep ∈ minimumLinearPrimes K S s ↔ primeExponents s.minimum.val p = 1 := by
        simp only [minimumLinearPrimes, FrozenChargeCore.linearPrimes,
          Finset.mem_filter, hp, true_and, ep]
      have hBmem : ep ∈ minimumCubePrimes K S s ↔ primeExponents s.minimum.val p = 3 := by
        simp only [minimumCubePrimes, FrozenChargeCore.cubePrimes,
          Finset.mem_filter, hp, true_and, ep]
      have hSmem : ep ∈ minimumSmallPrimes K S s ↔ primeExponents s.minimum.val p = 0 ∧
          ((primeExponents R.val p + 4 * primeExponents label.val p) % 6 = 0 ∨
            (primeExponents R.val p + 4 * primeExponents label.val p) % 6 = 4) := by
        unfold minimumSmallPrimes FrozenChargeCore.smallPrimes
        rw [Finset.mem_filter]
        change (ep ∈ s.active ∧ (primeExponents s.minimum.val p = 0 ∧
          ((frozenDigit K S (exteriorMul K S R (exteriorPower K S label 4)) ep).val = 0 ∨
            (frozenDigit K S (exteriorMul K S R (exteriorPower K S label 4)) ep).val = 4))) ↔ _
        rw [hdigit]
        simp only [hp, true_and]
      simpa only [hp, if_true, hNmem, hSmem, hBmem, mul_one] using
        local_conductor (primeExponents R.val p) (primeExponents label.val p)
          (primeExponents puncture.val p) (primeExponents s.minimum.val p)
          (exponent_le_one_of_squarefree label.val hlabel p)
          (exponent_le_one_of_squarefree puncture.val hpuncture p)
          (s.minimum_values p) hactive
    · have hNnot : ep ∉ minimumLinearPrimes K S s := by
        simp only [minimumLinearPrimes, FrozenChargeCore.linearPrimes, Finset.mem_filter]
        exact fun h => hp h.1
      have hSnot : ep ∉ minimumSmallPrimes K S s := by
        simp only [minimumSmallPrimes, FrozenChargeCore.smallPrimes, Finset.mem_filter]
        exact fun h => hp h.1
      have hBnot : ep ∉ minimumCubePrimes K S s := by
        simp only [minimumCubePrimes, FrozenChargeCore.cubePrimes, Finset.mem_filter]
        exact fun h => hp h.1
      simp only [hp, hNnot, hSnot, hBnot, if_false, mul_zero, zero_add, add_zero]
      split_ifs <;> omega

/-- Norm form of the preceding literal ideal divisibility. -/
theorem conductor_charge_norm (R label puncture : ExteriorIdeal K S)
    (hlabel : Squarefree label.val.val) (hpuncture : Squarefree puncture.val.val)
    (s : FrozenState K S (exteriorMul K S R (exteriorPower K S label 4)) puncture) :
    exteriorNorm K S (primeSetIdeal K S s.active) ^ 2 *
        exteriorNorm K S (exteriorPowerfulPart K S R) ≤
      exteriorNorm K S (minimumLinearIdeal K S s) * exteriorNorm K S (minimumSmallIdeal K S s) *
        exteriorNorm K S (minimumCubeIdeal K S s) ^ 4 * exteriorNorm K S R ^ 2 *
        exteriorNorm K S label * exteriorNorm K S puncture := by
  have hd := conductor_charge_dvd K S R label puncture hlabel hpuncture s
  have hn := map_dvd Ideal.absNorm hd
  have hpos : 0 < Ideal.absNorm
      ((minimumLinearIdeal K S s).val.val * (minimumSmallIdeal K S s).val.val *
        (minimumCubeIdeal K S s).val.val ^ 4 * R.val.val ^ 2 * label.val.val * puncture.val.val) := by
    rw [map_mul, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow]
    have hN := Ideal.absNorm_pos_of_nonZeroDivisors (minimumLinearIdeal K S s).val
    have hS := Ideal.absNorm_pos_of_nonZeroDivisors (minimumSmallIdeal K S s).val
    have hB := Ideal.absNorm_pos_of_nonZeroDivisors (minimumCubeIdeal K S s).val
    have hR := Ideal.absNorm_pos_of_nonZeroDivisors R.val
    have hL := Ideal.absNorm_pos_of_nonZeroDivisors label.val
    have hP := Ideal.absNorm_pos_of_nonZeroDivisors puncture.val
    positivity
  have hle := Nat.le_of_dvd hpos hn
  have hreal := (Nat.cast_le (α := ℝ)).mpr hle
  simpa only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow,
    exteriorNorm, exteriorPowerfulPart] using hreal

/-- The exact logarithmic conductor comparison for the actual moving row.
Replacing either norm by its fixed support endpoint gives only log C/log Z. -/
theorem conductor_charge_width (R label puncture moving : ExteriorIdeal K S)
    (hlabel : Squarefree label.val.val) (hpuncture : Squarefree puncture.val.val)
    (s : FrozenState K S (exteriorMul K S R (exteriorPower K S label 4)) puncture)
    {Z : ℝ} (hZ : 1 < Z) :
    2 * scale Z (exteriorNorm K S moving) +
      2 * scale Z (exteriorNorm K S (primeSetIdeal K S s.active)) -
      scale Z (exteriorNorm K S (minimumLinearIdeal K S s)) -
      scale Z (exteriorNorm K S (minimumSmallIdeal K S s)) -
      4 * scale Z (exteriorNorm K S (minimumCubeIdeal K S s)) ≤
      2 * scale Z (exteriorNorm K S (exteriorMul K S moving R)) -
      scale Z (exteriorNorm K S (exteriorPowerfulPart K S R)) +
      scale Z (exteriorNorm K S label) + scale Z (exteriorNorm K S puncture) := by
  have hA := exteriorNorm_pos K S (primeSetIdeal K S s.active)
  have hN := exteriorNorm_pos K S (minimumLinearIdeal K S s)
  have hS := exteriorNorm_pos K S (minimumSmallIdeal K S s)
  have hB := exteriorNorm_pos K S (minimumCubeIdeal K S s)
  have hR := exteriorNorm_pos K S R
  have hL := exteriorNorm_pos K S label
  have hP := exteriorNorm_pos K S puncture
  have hPow := exteriorNorm_pos K S (exteriorPowerfulPart K S R)
  have hnorm := conductor_charge_norm K S R label puncture hlabel hpuncture s
  have h := scale_mono hZ
    (mul_pos (sq_pos_of_pos (exteriorNorm_pos K S (primeSetIdeal K S s.active)))
      (exteriorNorm_pos K S (exteriorPowerfulPart K S R))) hnorm
  rw [scale_mul Z (by positivity) (exteriorNorm_pos K S (exteriorPowerfulPart K S R)),
    scale_mul Z (by positivity) (exteriorNorm_pos K S puncture),
    scale_mul Z (by positivity) (exteriorNorm_pos K S label),
    scale_mul Z (by positivity) (by positivity),
    scale_mul Z (by positivity) (by positivity),
    scale_mul Z (exteriorNorm_pos K S (minimumLinearIdeal K S s))
      (exteriorNorm_pos K S (minimumSmallIdeal K S s)),
    scale_pow, scale_pow, scale_pow] at h
  have hprod : exteriorNorm K S (exteriorMul K S moving R) =
      exteriorNorm K S moving * exteriorNorm K S R := by
    simp only [exteriorNorm, exteriorMul, Submonoid.coe_mul, map_mul, Nat.cast_mul]
  rw [hprod, scale_mul Z (exteriorNorm_pos K S moving) (exteriorNorm_pos K S R)]
  norm_num at h
  linarith

#print axioms conductor_charge_dvd
#print axioms conductor_charge_norm
#print axioms conductor_charge_width

end HeckeSkeleton.LowEnergy.GeneralConductor
