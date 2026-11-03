import HeckeSkeleton.HighBinSupport.HighNormFormDeficit
import HeckeGeneral.Analysis.PhysicalProbeRows
import Mathlib.RingTheory.Coprime.Lemmas
/-!
Actual prime windows and the conductor deficit of a frequency row.

The support, multiplicities, radical and row norm below are the project's
actual ideals.  The radical product identity is proved from ideal
factorization; it is not an input assumption.  The final selected-slot
inequality uses the actual disjoint smooth windows to prevent a prime
from being charged twice.

This file intentionally has project imports and is excluded from the
Mathlib-only aggregate verification module.
-/

noncomputable section

namespace HighBinVerified.NormFormActual

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical BigOperators nonZeroDivisors

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- A finite product of positive powers of distinct prime ideals has the
literal product of those prime ideals as its radical. -/
theorem radical_primePowerProduct (support : Finset (HeightOneSpectrum R))
    (m : HeightOneSpectrum R → ℕ) (hm : ∀ p ∈ support, m p ≠ 0) :
    (∏ p ∈ support, p.asIdeal ^ m p).radical = ∏ p ∈ support, p.asIdeal := by
  revert hm
  induction support using Finset.induction_on with
  | empty =>
      intro hm
      simp [Ideal.one_eq_top, Ideal.radical_top]
  | @insert p support hp ih =>
      intro hm
      have hcop : IsCoprime p.asIdeal (∏ q ∈ support, q.asIdeal) := by
        apply IsCoprime.prod_right
        intro q hq
        apply Ideal.isCoprime_of_isMaximal
        intro heq
        have hpq : p = q := HeightOneSpectrum.asIdeal_injective heq
        exact hp (hpq.symm ▸ hq)
      simp only [Finset.prod_insert hp]
      rw [Ideal.radical_mul,
        Ideal.radical_pow _ (hm p (Finset.mem_insert_self p support)),
        p.isPrime.isRadical.radical,
        ih (fun q hq => hm q (Finset.mem_insert_of_mem hq))]
      exact (Ideal.mul_eq_inf_of_isCoprime hcop).symm

theorem actual_primePower_reconstruction (I : (Ideal R)⁰) :
    (∏ p ∈ (primeExponents I).support, p.asIdeal ^ primeExponents I p) = I.val := by
  exact congrArg Subtype.val (idealOfPrimeExponents_primeExponents I)

/-- The support used here is the actual ideal factorization support. -/
theorem actual_radical_eq_primeSupport_product (I : (Ideal R)⁰) :
    I.val.radical = ∏ p ∈ (primeExponents I).support, p.asIdeal := by
  calc
    I.val.radical =
        (∏ p ∈ (primeExponents I).support, p.asIdeal ^ primeExponents I p).radical :=
      congrArg Ideal.radical (actual_primePower_reconstruction I).symm
    _ = _ := radical_primePowerProduct _ _
      (fun p hp => Finsupp.mem_support_iff.mp hp)

end Dedekind

variable (K : Type) [Field K] [NumberField K]

theorem actual_idealNorm_eq_primeSupport_product (I : NonzeroIdeal K) :
    idealNorm K I = ∏ p ∈ (primeExponents I).support,
      (p.asIdeal.absNorm : ℝ) ^ primeExponents I p := by
  have h := congrArg (fun J : Ideal (𝓞 K) => (J.absNorm : ℝ))
    (actual_primePower_reconstruction I)
  simpa only [idealNorm, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow] using h.symm

theorem actual_radicalNorm_eq_primeSupport_product (I : NonzeroIdeal K) :
    (I.val.radical.absNorm : ℝ) =
      ∏ p ∈ (primeExponents I).support, (p.asIdeal.absNorm : ℝ) := by
  rw [actual_radical_eq_primeSupport_product I, map_prod, Nat.cast_prod]

theorem actual_selected_repeated_product_mul_radicalNorm_le
    (I : NonzeroIdeal K) (selected : Finset (HeightOneSpectrum (𝓞 K)))
    (hrepeated : ∀ p ∈ selected, 2 ≤ primeExponents I p) :
    (∏ p ∈ selected, (p.asIdeal.absNorm : ℝ)) * (I.val.radical.absNorm : ℝ) ≤
      idealNorm K I := by
  have hsupport : selected ⊆ (primeExponents I).support := by
    intro p hp
    apply Finsupp.mem_support_iff.mpr
    exact ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) (hrepeated p hp))
  have hnorm : ∀ p ∈ (primeExponents I).support, 1 ≤ (p.asIdeal.absNorm : ℝ) := by
    intro p hp
    exact one_le_idealNorm K
      ⟨p.asIdeal, mem_nonZeroDivisors_of_ne_zero p.ne_bot⟩
  have hpositive : ∀ p ∈ (primeExponents I).support, 1 ≤ primeExponents I p := by
    intro p hp
    exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
  rw [actual_radicalNorm_eq_primeSupport_product,
    actual_idealNorm_eq_primeSupport_product]
  exact NormForm.selected_repeated_product_mul_radical_le
    (primeExponents I).support selected (fun p => (p.asIdeal.absNorm : ℝ))
    (primeExponents I) hsupport hnorm hpositive hrepeated

/-- The joint selected-prime/conductor allocation for the actual ideal,
with no free radical or row-norm parameters. -/
theorem actual_repeated_conductor_factor_absorbed
    (I : NonzeroIdeal K) (selected : Finset (HeightOneSpectrum (𝓞 K)))
    (hrepeated : ∀ p ∈ selected, 2 ≤ primeExponents I p)
    (lam eta : ℝ) (hlam : 0 ≤ lam) (heta : 0 ≤ eta) :
    (∏ p ∈ selected, (p.asIdeal.absNorm : ℝ)) ^ lam *
      ((I.val.radical.absNorm : ℝ) / idealNorm K I) ^ (lam + eta) ≤ 1 := by
  have hsupport : selected ⊆ (primeExponents I).support := by
    intro p hp
    apply Finsupp.mem_support_iff.mpr
    exact ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) (hrepeated p hp))
  rw [actual_radicalNorm_eq_primeSupport_product,
    actual_idealNorm_eq_primeSupport_product]
  apply NormForm.repeated_table_absorbed _ _ _ _ hsupport
  · intro p hp
    exact one_le_idealNorm K
      ⟨p.asIdeal, mem_nonZeroDivisors_of_ne_zero p.ne_bot⟩
  · intro p hp
    exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
  · exact hrepeated
  · exact hlam
  · exact heta

variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- Membership in the literal filtered prime window implies nonzero
value of its fixed annular profile, regardless of the ray filter. -/
theorem actual_primeWindow_weight_ne_zero (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (i : Fin g.slots)
    (p : ExteriorPrime K S) (hp : p ∈ primeWindow K S g T Z i) :
    (g.weight i).toFun ((p.val.asIdeal.absNorm : ℝ) / primeScale g Z) ≠ 0 := by
  obtain ⟨q, _hq, heq⟩ := Finset.mem_image.mp hp
  have hq := Finset.mem_filter.mp q.property
  have hv : q.val = p.val := congrArg Subtype.val heq
  rw [hv] at hq
  exact hq.2.2.2

/-- Literal support in (1,2) gives the actual norm window. Nonemptiness
also forces a positive scale, so no separate Z hypothesis is needed. -/
theorem actual_primeWindow_norm_range (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (i : Fin g.slots)
    (p : ExteriorPrime K S) (hp : p ∈ primeWindow K S g T Z i) :
    0 < primeScale g Z ∧ primeScale g Z < (p.val.asIdeal.absNorm : ℝ) ∧
      (p.val.asIdeal.absNorm : ℝ) < 2 * primeScale g Z := by
  have hy := g.support_annular i (actual_primeWindow_weight_ne_zero K S g T Z i p hp)
  have hq : 0 < (p.val.asIdeal.absNorm : ℝ) :=
    idealNorm_pos K ⟨p.val.asIdeal, mem_nonZeroDivisors_of_ne_zero p.val.ne_bot⟩
  have hP : 0 < primeScale g Z := by
    by_contra hn
    have hbad := div_nonpos_of_nonneg_of_nonpos hq.le (le_of_not_gt hn)
    linarith [hy.1]
  exact ⟨hP, by simpa only [one_mul] using (lt_div_iff₀ hP).mp hy.1,
    (div_lt_iff₀ hP).mp hy.2⟩

theorem actual_primeWindows_disjoint (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (i j : Fin g.slots) (hij : i ≠ j) :
    Disjoint (primeWindow K S g T Z i) (primeWindow K S g T Z j) := by
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  exact Set.disjoint_left.mp (g.disjoint i j hij)
    (actual_primeWindow_weight_ne_zero K S g T Z i p hpi)
    (actual_primeWindow_weight_ne_zero K S g T Z j p hpj)

theorem actual_primeWindow_tuple_injective (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (p : Fin g.slots → ExteriorPrime K S)
    (hp : ∀ i, p i ∈ primeWindow K S g T Z i) : Function.Injective p := by
  intro i j heq
  by_contra hij
  have hd := actual_primeWindows_disjoint K S g T Z i j hij
  exact Finset.disjoint_left.mp hd (hp i) (heq.symm ▸ hp j)

variable [Fintype S]

/-- In a genuine prime tuple every repeated row prime is charged at most
once, even though different slots may require different local bounds. -/
theorem actual_frequencyRow_selected_slots_deficit
    (u : FrequencyRow K S) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (p : Fin g.slots → ExteriorPrime K S)
    (hp : ∀ i, p i ∈ primeWindow K S g T Z i)
    (selectedSlots : Finset (Fin g.slots))
    (hrepeated : ∀ i ∈ selectedSlots, 2 ≤ primeExponents u.ideal.val (p i).val) :
    (∏ i ∈ selectedSlots, ((p i).val.asIdeal.absNorm : ℝ)) *
      (u.ideal.val.val.radical.absNorm : ℝ) ≤ frequencyRowNorm K S u := by
  let selected : Finset (HeightOneSpectrum (𝓞 K)) :=
    selectedSlots.image (fun i => (p i).val)
  have hselected : ∀ q ∈ selected, 2 ≤ primeExponents u.ideal.val q := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact hrepeated i hi
  have hinj : Function.Injective (fun i => (p i).val) :=
    Subtype.val_injective.comp (actual_primeWindow_tuple_injective K S g T Z p hp)
  have hprod : (∏ q ∈ selected, (q.asIdeal.absNorm : ℝ)) =
      ∏ i ∈ selectedSlots, ((p i).val.asIdeal.absNorm : ℝ) :=
    Finset.prod_image hinj.injOn
  have hbound := actual_selected_repeated_product_mul_radicalNorm_le K
    u.ideal.val selected hselected
  rw [hprod] at hbound
  exact hbound

end HighBinVerified.NormFormActual

#print axioms HighBinVerified.NormFormActual.actual_radical_eq_primeSupport_product
#print axioms HighBinVerified.NormFormActual.actual_selected_repeated_product_mul_radicalNorm_le
#print axioms HighBinVerified.NormFormActual.actual_repeated_conductor_factor_absorbed
#print axioms HighBinVerified.NormFormActual.actual_primeWindow_norm_range
#print axioms HighBinVerified.NormFormActual.actual_primeWindow_tuple_injective
#print axioms HighBinVerified.NormFormActual.actual_frequencyRow_selected_slots_deficit
