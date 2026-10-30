import HeckeSkeleton.HighBinSupport.ActualNormFormFullCorrection

/-!
The detector cap for the complete actual correction slot.

The summable regular error, valuation-one terms and repeated-row-prime
terms are included in the slot itself. This is the upper cap needed to
bin actual full-slot maxima. The resulting amplitude therefore measures
the repeated-prime terms as well as the regular terms; the separate
tuplewise radical-allocation identities remain available in
ActualNormFormRepeatedTuples.
-/

set_option autoImplicit false
noncomputable section
namespace HighBinVerified.NormFormSlotCap

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler
open NormFormActual NormFormFullCorrection
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The actual full slot, with every ramified and regular correction
included, satisfies the same prime-scale amplitude cap. The small row
and height powers remain explicit until the analysis-height ceiling is
chosen. No slot bound is an input. -/
theorem exists_actualFullCorrectionSlot_power_cap
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (hcomp : (1 : HeckeCharacter K) ∈ companions)
    (P : ProbeData K S) (g : PrimeWindowGeometry)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
    (hpsi : ∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val)
    {e eps eta kappa : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (heps : 0 < eps) (heta : 0 < eta) (hkappa : 0 < kappa) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧
      ∀ Z T : ℝ, Z0 ≤ Z → ∀ d : ℝ, (1 / 16 : ℝ) ≤ d →
      ∀ u : FrequencyRow K S, Z ^ d ≤ frequencyRowNorm K S u →
      ∀ a U : ℝ, 51 / 100 ≤ a → a ≤ 1 →
      ∀ s w z : ℂ, s.re = a + 16 * e → w.re = 1 - a - 6 * e → z.re = 17 / 50 →
      NormForm.internalHeight Z T kappa + |z.im| + 2 ≤ U →
      rowZeroBelow K S psi companions P (arithmeticHighEulerData K S P psi) u U (a + 2 * e) →
      ∀ i : Fin g.slots,
        ‖actualFullCorrectionSlot K S P psi g ∅ u Z s w z i‖ ≤
          C * frequencyRowNorm K S u ^ (eps + eta) *
            (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) *
            (primeScale g Z) ^ (a - 33 / 50 + 8 * e + eta) := by
  obtain ⟨C, Z0, hC, hZ0, hslot⟩ := exists_actualFullCorrectionSlot_bound
    K S psi companions hcomp P g hcal hpsi he he1 heps heta hkappa
  obtain ⟨Z1, hZ1, hscale⟩ := NormFormPrimeCap.exists_primeScale_cutoff g
  let D : ℝ := 2 * repeatedTupleConstant 1 eta
  have hD : 0 < D := mul_pos (by norm_num) (repeatedTupleConstant_pos 1 heta)
  refine ⟨C * (2 + D), max Z0 Z1, mul_pos hC (by linarith),
    hZ0.trans (le_max_left _ _), ?_⟩
  intro Z T hZ d hd u hu a U ha ha1 s w z hs hw hz hU hbelow i
  have hZZ0 : Z0 ≤ Z := (le_max_left _ _).trans hZ
  have hZZ1 : Z1 ≤ Z := (le_max_right _ _).trans hZ
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZ0.trans hZZ0)
  have hP1 : 1 ≤ primeScale g Z := (by norm_num : (1 : ℝ) ≤ 2).trans (hscale Z hZZ1)
  have hP0 : 0 < primeScale g Z := zero_lt_one.trans_le hP1
  have hN1 : 1 ≤ frequencyRowNorm K S u := one_le_idealNorm K u.ideal.val
  have hN0 : 0 < frequencyRowNorm K S u := zero_lt_one.trans_le hN1
  have hRle : (u.ideal.val.val.radical.absNorm : ℝ) ≤ frequencyRowNorm K S u := by
    simpa only [Finset.prod_empty, one_mul] using
      actual_selected_repeated_product_mul_radicalNorm_le K u.ideal.val ∅ (by simp)
  have hheight0 : 0 ≤ NormForm.internalHeight Z T kappa :=
    (Real.rpow_nonneg hZpos.le kappa).trans (le_max_right _ _)
  have hU1 : 1 ≤ 2 + U := by linarith [abs_nonneg z.im]
  let L : ℝ := (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps)
  have hL1 : 1 ≤ L := Real.one_le_rpow hU1 (mul_nonneg (Nat.cast_nonneg _) heps.le)
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have hNeps : 1 ≤ frequencyRowNorm K S u ^ eps := Real.one_le_rpow hN1 heps.le
  have hNeta : 1 ≤ frequencyRowNorm K S u ^ eta := Real.one_le_rpow hN1 heta.le
  let B : ℝ := frequencyRowNorm K S u ^ (eps + eta) * L
  have hB0 : 0 ≤ B := mul_nonneg (Real.rpow_nonneg hN0.le _) hL0
  have hNB : frequencyRowNorm K S u ^ eta ≤ B := by
    dsimp only [B]
    calc
      _ ≤ frequencyRowNorm K S u ^ eps * frequencyRowNorm K S u ^ eta :=
        le_mul_of_one_le_left (Real.rpow_nonneg hN0.le _) hNeps
      _ = frequencyRowNorm K S u ^ (eps + eta) := (Real.rpow_add hN0 _ _).symm
      _ ≤ _ := le_mul_of_one_le_right (Real.rpow_nonneg hN0.le _) hL1
  have hRB : (u.ideal.val.val.radical.absNorm : ℝ) ^ eps * L ≤ B := by
    apply mul_le_mul_of_nonneg_right _ hL0
    calc
      _ ≤ frequencyRowNorm K S u ^ eps := Real.rpow_le_rpow (Nat.cast_nonneg _) hRle heps.le
      _ ≤ frequencyRowNorm K S u ^ eps * frequencyRowNorm K S u ^ eta :=
        le_mul_of_one_le_right (Real.rpow_nonneg hN0.le _) hNeta
      _ = frequencyRowNorm K S u ^ (eps + eta) := (Real.rpow_add hN0 _ _).symm
  let b : ℝ := a - 33 / 50 + 8 * e + eta
  have hmain : (u.ideal.val.val.radical.absNorm : ℝ) ^ eps * L *
      (primeScale g Z) ^ (a - 33 / 50 + 8 * e) ≤ B * (primeScale g Z) ^ b :=
    mul_le_mul hRB (Real.rpow_le_rpow_of_exponent_le hP1 (by dsimp only [b]; linarith))
      (Real.rpow_nonneg hP0.le _) hB0
  have herr : frequencyRowNorm K S u ^ eta *
      (primeScale g Z) ^ (-(4 / 25 : ℝ) + eta) ≤ B * (primeScale g Z) ^ b :=
    mul_le_mul hNB (Real.rpow_le_rpow_of_exponent_le hP1 (by dsimp only [b]; linarith))
      (Real.rpow_nonneg hP0.le _) hB0
  have hlam : 0 ≤ a - 1 / 2 + 6 * e := by linarith
  have hlam1 : a - 1 / 2 + 6 * e ≤ 1 := by linarith
  have hrepeat := repeatedPrimeWindow_power_sum_le K S u g ∅ Z i hlam hlam1 heta hP0
  have hrepeat' : (primeScale g Z) ^ (-(4 / 25 : ℝ)) *
      (∑ p ∈ repeatedPrimeWindow K S u g ∅ Z i,
        (p.val.asIdeal.absNorm : ℝ) ^ (a - 1 / 2 + 6 * e)) ≤
      D * (B * (primeScale g Z) ^ b) := by
    calc
      _ ≤ (primeScale g Z) ^ (-(4 / 25 : ℝ)) *
          (D * frequencyRowNorm K S u ^ eta * (primeScale g Z) ^ (a - 1 / 2 + 6 * e)) :=
        mul_le_mul_of_nonneg_left hrepeat (Real.rpow_nonneg hP0.le _)
      _ = D * (frequencyRowNorm K S u ^ eta *
          (primeScale g Z) ^ (a - 33 / 50 + 6 * e)) := by
        rw [show a - 33 / 50 + 6 * e = -(4 / 25 : ℝ) + (a - 1 / 2 + 6 * e) by ring,
          Real.rpow_add hP0]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul hNB (Real.rpow_le_rpow_of_exponent_le hP1 (by dsimp only [b]; linarith))
          (Real.rpow_nonneg hP0.le _) hB0) hD.le
  have hb := hslot Z T hZZ0 d hd u hu a U ha ha1 s w z hs hw hz hU hbelow i
  apply hb.trans
  calc
    _ ≤ C * (B * (primeScale g Z) ^ b + B * (primeScale g Z) ^ b +
        D * (B * (primeScale g Z) ^ b)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hmain herr) hrepeat') hC.le
    _ = _ := by dsimp only [B, L, b]; ring

end HighBinVerified.NormFormSlotCap

#print axioms HighBinVerified.NormFormSlotCap.exists_actualFullCorrectionSlot_power_cap
