import HeckeSkeleton.HighBinSupport.ActualNormFormFullCorrection
import HeckeSkeleton.HighBinSupport.HighNormFormSlots
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Full correction products on the physical amplitude labels

The physical source labels the main prime polynomial.  Repeated row primes
therefore have to be allocated against the conductor radical before the
full correction product is bounded.  The estimates here sum every subset
of repeated slots, including the empty subset; no repeated-prime factor is
discarded and no amplitude of the complete correction is substituted for
the physical source amplitude.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinPhysicalNorm

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HighBinVerified.NormFormActual HighBinVerified.NormFormFullCorrection
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The literal positive mass of the repeated choices in one original slot. -/
def repeatedSlotMass (u : FrequencyRow K S) (g : PrimeWindowGeometry)
    (ray : Finset (HeckeCharacter K)) (Z lam : ℝ) (i : Fin g.slots) : ℝ :=
  ∑ p ∈ repeatedPrimeWindow K S u g ray Z i,
    (p.val.asIdeal.absNorm : ℝ) ^ lam

theorem repeatedSlotMass_nonneg (u : FrequencyRow K S) (g : PrimeWindowGeometry)
    (ray : Finset (HeckeCharacter K)) (Z lam : ℝ) (i : Fin g.slots) :
    0 ≤ repeatedSlotMass K S u g ray Z lam i :=
  Finset.sum_nonneg (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Fixed slots give a fixed sum of tuple constants, chosen before rows,
scales, labels, contour coordinates and the height exponent. -/
def repeatedProductConstant (J : ℕ) (eta : ℝ) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset (Fin J)).powerset,
    repeatedTupleConstant A.card eta

theorem repeatedProductConstant_pos (J : ℕ) {eta : ℝ} (heta : 0 < eta) :
    0 < repeatedProductConstant J eta := by
  apply Finset.sum_pos
  · intro A _
    exact repeatedTupleConstant_pos A.card heta
  · exact Finset.powerset_nonempty _

/-- Every product of repeated-slot masses is a sum over the actual
distinct-prime tuples.  The radical is absorbed before taking that sum. -/
theorem repeatedSlotMass_selected_conductor_bound
    (u : FrequencyRow K S) (g : PrimeWindowGeometry)
    (ray : Finset (HeckeCharacter K)) (Z : ℝ) (A : Finset (Fin g.slots))
    {lam eta : ℝ} (hlam : 0 ≤ lam) (heta : 0 < eta) :
    (u.ideal.val.val.radical.absNorm : ℝ) ^ lam *
        (∏ i ∈ A, repeatedSlotMass K S u g ray Z lam i) ≤
      repeatedTupleConstant A.card eta * frequencyRowNorm K S u ^ (lam + eta) := by
  let F := repeatedPrimeTuples K S u g ray Z A
  let term := fun p : A → ExteriorPrime K S =>
    ∏ i : A, ((p i).val.asIdeal.absNorm : ℝ) ^ lam
  have hprod : (∏ i ∈ A, repeatedSlotMass K S u g ray Z lam i) =
      ∑ p ∈ F, term p := by
    rw [← Finset.prod_coe_sort]
    exact Finset.prod_univ_sum
      (fun i : A => repeatedPrimeWindow K S u g ray Z i.val)
      (fun _ p => (p.val.asIdeal.absNorm : ℝ) ^ lam)
  have hterm (p : A → ExteriorPrime K S) (hp : p ∈ F) :
      (u.ideal.val.val.radical.absNorm : ℝ) ^ lam * term p ≤
        frequencyRowNorm K S u ^ lam := by
    have halloc := repeatedPrimeTuple_conductor_allocation K S u g ray Z A p hp
    have hpow := Real.rpow_le_rpow
      (mul_nonneg (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _))
        (Nat.cast_nonneg _)) halloc hlam
    rw [Real.mul_rpow (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _))
      (Nat.cast_nonneg _), ← Real.finsetProd_rpow _ _ (fun i _ => Nat.cast_nonneg _) lam]
      at hpow
    simpa only [term, mul_comm] using hpow
  have hN := idealNorm_pos K u.ideal.val
  calc
    _ = ∑ p ∈ F, (u.ideal.val.val.radical.absNorm : ℝ) ^ lam * term p := by
      rw [hprod, Finset.mul_sum]
    _ ≤ ∑ _p ∈ F, frequencyRowNorm K S u ^ lam := Finset.sum_le_sum hterm
    _ = (F.card : ℝ) * frequencyRowNorm K S u ^ lam := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (repeatedTupleConstant A.card eta * frequencyRowNorm K S u ^ eta) *
        frequencyRowNorm K S u ^ lam :=
      mul_le_mul_of_nonneg_right
        (repeatedPrimeTuples_card_subpower K S u g ray Z A heta)
        (Real.rpow_nonneg hN.le _)
    _ = _ := by
      rw [Real.rpow_add hN]
      ring

/-- The complete repeated-slot product retains all ordinary/repeated
choices while costing an arbitrarily small power of the actual row norm. -/
theorem repeatedSlotMass_product_conductor_bound
    (u : FrequencyRow K S) (g : PrimeWindowGeometry)
    (ray : Finset (HeckeCharacter K)) (Z : ℝ)
    {lam eta : ℝ} (hlam : 0 ≤ lam) (heta : 0 < eta) :
    (u.ideal.val.val.radical.absNorm : ℝ) ^ lam *
        (∏ i : Fin g.slots, (1 + repeatedSlotMass K S u g ray Z lam i)) ≤
      repeatedProductConstant g.slots eta * frequencyRowNorm K S u ^ (lam + eta) := by
  rw [Finset.prod_one_add, Finset.mul_sum]
  calc
    _ ≤ ∑ A ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
        repeatedTupleConstant A.card eta * frequencyRowNorm K S u ^ (lam + eta) := by
      apply Finset.sum_le_sum
      intro A _
      exact repeatedSlotMass_selected_conductor_bound K S u g ray Z A hlam heta
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- A pointwise product estimate using the amplitudes of the original
main prime slots.  The positive per-slot error factor is uniform and the
same conductor deficit handles every repeated subset simultaneously. -/
theorem fullSlot_product_of_physical_bounds
    (u : FrequencyRow K S) (g : PrimeWindowGeometry)
    (ray : Finset (HeckeCharacter K)) (Z C width lam eta : ℝ)
    (amplitude : Fin g.slots → ℝ) (slot : Fin g.slots → ℂ)
    (hZ : 0 < Z) (hC : 0 ≤ C) (hlam : 0 ≤ lam) (heta : 0 < eta)
    (hslot : ∀ i, ‖slot i‖ ≤
      C * frequencyRowNorm K S u ^ eta *
        (primeScale g Z) ^ (-(4 / 25 : ℝ) + amplitude i + width) *
          (1 + repeatedSlotMass K S u g ray Z lam i)) :
    (u.ideal.val.val.radical.absNorm : ℝ) ^ lam * ‖∏ i, slot i‖ ≤
      (C ^ g.slots * repeatedProductConstant g.slots eta) *
        frequencyRowNorm K S u ^ (lam + (g.slots + 1) * eta) *
        Z ^ (-2 / 75 + ((∑ i, amplitude i) / g.slots) / 6 + width / 6) := by
  have hN := idealNorm_pos K u.ideal.val
  let scale := Z ^ (-2 / 75 + ((∑ i, amplitude i) / g.slots) / 6 + width / 6)
  have hp := HighBinVerified.NormForm.weighted_slot_product_bound
    (Finset.univ : Finset (Fin g.slots)) Z width
    (fun _ => (1 / 6 : ℝ) / g.slots) amplitude
    (fun i => C * frequencyRowNorm K S u ^ eta *
      (1 + repeatedSlotMass K S u g ray Z lam i)) slot hZ
    (fun i _ => by simpa only [primeScale] using (hslot i).trans_eq (by ring))
  have hJ : (g.slots : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt g.slots_pos
  have hlength : (∑ _i : Fin g.slots, (1 / 6 : ℝ) / g.slots) = 1 / 6 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hweight : (∑ i : Fin g.slots, ((1 / 6 : ℝ) / g.slots) * amplitude i) =
      ((∑ i, amplitude i) / g.slots) / 6 := by rw [← Finset.mul_sum]; ring
  rw [hlength, hweight] at hp
  have he : (-4 / 25 + width) * (1 / 6) + ((∑ i, amplitude i) / g.slots) / 6 =
      -2 / 75 + ((∑ i, amplitude i) / g.slots) / 6 + width / 6 := by ring
  rw [he, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN.le] at hp
  have hmass := repeatedSlotMass_product_conductor_bound K S u g ray Z hlam heta
  calc
    _ ≤ (u.ideal.val.val.radical.absNorm : ℝ) ^ lam *
        ((C ^ g.slots * frequencyRowNorm K S u ^ (eta * g.slots)) *
          (∏ i : Fin g.slots, (1 + repeatedSlotMass K S u g ray Z lam i)) * scale) :=
      mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = (C ^ g.slots * frequencyRowNorm K S u ^ (eta * g.slots) * scale) *
        ((u.ideal.val.val.radical.absNorm : ℝ) ^ lam *
          ∏ i : Fin g.slots, (1 + repeatedSlotMass K S u g ray Z lam i)) := by ring
    _ ≤ (C ^ g.slots * frequencyRowNorm K S u ^ (eta * g.slots) * scale) *
        (repeatedProductConstant g.slots eta * frequencyRowNorm K S u ^ (lam + eta)) :=
      mul_le_mul_of_nonneg_left hmass (by dsimp only [scale]; positivity)
    _ = _ := by
      rw [show lam + (g.slots + 1) * eta = eta * g.slots + (lam + eta) by ring,
        Real.rpow_add hN]
      ring

end HeckeSkeleton.HighBinPhysicalNorm

#print axioms HeckeSkeleton.HighBinPhysicalNorm.repeatedSlotMass_product_conductor_bound
#print axioms HeckeSkeleton.HighBinPhysicalNorm.fullSlot_product_of_physical_bounds
