import HeckeSkeleton.HighBinSupport.ActualPrimeExponentIndex
import HeckeSkeleton.HighBinSupport.PrimeBlockEuler

/-!
# Euler rearrangement of the original four-ideal series

All coefficients below are the original `initialRowEulerTerm`. Its coprime
factorization comes from the actual finite CRT theorem, and its absolute
convergence comes from the literal finite-sum majorant. The marked prime
blocks keep the whole completed index c*n^3 and all four exponents.

This module proves the global rearrangement before evaluating the local
prime-block series. It does not assume an initial Euler calibration or
replace the original series with a product definition.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinActualInitial

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualAbsolute
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- A local block is a specialization of the original unmarked term. -/
def primeBlockBase (P : ProbeData K S) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) (p : ExteriorPrime K S) (n : FourExponent) : ℂ :=
  initialRowEulerTerm K S P ψ ∅ u s w z (primeFourIdealIndex K S p n)

/-- A mark deletes precisely the completed-unit local index. -/
def primeBlockTerm (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (s w z : ℂ)
    (p : ExteriorPrime K S) (n : FourExponent) : ℂ :=
  if p ∈ Q ∧ n.1.1 + 3 * n.1.2 = 0 then 0
  else primeBlockBase K S P ψ u s w z p n

@[simp] theorem primeBlockBase_zero (P : ProbeData K S) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) (p : ExteriorPrime K S) :
    primeBlockBase K S P ψ u s w z p 0 = 1 := by
  rw [primeBlockBase, ← fourIdealOfPrimeExponents_single, Finsupp.single_zero,
    fourIdealOfPrimeExponents_zero, initialRowEulerTerm_empty_one]

theorem primeBlockTerm_zero_of_not_mem (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (s w z : ℂ)
    (p : ExteriorPrime K S) (hp : p ∉ Q) : primeBlockTerm K S P ψ Q u s w z p 0 = 1 := by
  simp only [primeBlockTerm, hp, false_and, if_false, primeBlockBase_zero]

/-- The actual unmarked coefficient is the product of its disjoint prime
blocks, including the original unit term. -/
theorem initialRowEulerTerm_empty_finite_product (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) (e : ExteriorPrime K S →₀ FourExponent) :
    initialRowEulerTerm K S P ψ ∅ u s w z (fourIdealOfPrimeExponents K S e) =
      e.prod (primeBlockBase K S P ψ u s w z) := by
  induction e using Finsupp.induction with
  | zero =>
    rw [fourIdealOfPrimeExponents_zero, initialRowEulerTerm_empty_one,
      Finsupp.prod_zero_index]
  | @single_add p n e hp hn ih =>
    have hd : Disjoint (Finsupp.single p n).support e.support := by
      apply Finset.disjoint_left.mpr
      intro q hq hqe
      have hqp : q = p := Finset.mem_singleton.mp (Finsupp.support_single_subset hq)
      exact hp (hqp ▸ hqe)
    rw [fourIdealOfPrimeExponents_add,
      initialRowEulerTerm_empty_coprime_mul K S P hP ψ u s w z _ _
        (fourIdealSupport_single_coprime K S p n e hp), ih,
      fourIdealOfPrimeExponents_single]
    change primeBlockBase K S P ψ u s w z p n *
      e.prod (primeBlockBase K S P ψ u s w z) = _
    rw [Finsupp.prod_add_index_of_disjoint hd,
      Finsupp.prod_single_index (primeBlockBase_zero K S P ψ u s w z p)]

/-- Whole-index marks are imposed once, at their own prime blocks. -/
theorem initialRowEulerTerm_finite_product (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (s w z : ℂ)
    (e : ExteriorPrime K S →₀ FourExponent) :
    initialRowEulerTerm K S P ψ Q u s w z (fourIdealOfPrimeExponents K S e) =
      HighBin.PrimeBlockEuler.weight (primeBlockTerm K S P ψ Q u s w z) Q e := by
  rw [initialRowEulerTerm_eq_exponent_filter]
  have hmask :
      (∀ p ∈ Q, 0 < primeExponents (fourIdealOfPrimeExponents K S e).1.1.val p.val +
        3 * primeExponents (fourIdealOfPrimeExponents K S e).1.2.val p.val) ↔
      (∀ p ∈ Q, 0 < (e p).1.1 + 3 * (e p).1.2) := by
    simp only [fourIdealOfPrimeExponents, primeExponents_exteriorIdealOfPrimeExponents,
      Finsupp.mapRange_apply]
  simp only [hmask]
  by_cases hQ : ∀ p ∈ Q, 0 < (e p).1.1 + 3 * (e p).1.2
  · rw [if_pos hQ, initialRowEulerTerm_empty_finite_product K S P hP]
    unfold HighBin.PrimeBlockEuler.weight HighBin.PrimeBlockEuler.finiteWeight
    have hbase : e.prod (primeBlockBase K S P ψ u s w z) =
        ∏ p ∈ e.support ∪ Q, primeBlockBase K S P ψ u s w z p (e p) := by
      apply Finset.prod_subset Finset.subset_union_left
      intro p _ hp
      rw [Finsupp.notMem_support_iff.mp hp, primeBlockBase_zero]
    rw [hbase]
    apply Finset.prod_congr rfl
    intro p _
    symm
    apply if_neg
    rintro ⟨hpQ, hz⟩
    have hpos := hQ p hpQ
    omega
  · rw [if_neg hQ]
    push_neg at hQ
    obtain ⟨p, hpQ, hp⟩ := hQ
    have hz : (e p).1.1 + 3 * (e p).1.2 = 0 := by omega
    symm
    unfold HighBin.PrimeBlockEuler.weight HighBin.PrimeBlockEuler.finiteWeight
    exact Finset.prod_eq_zero (Finset.mem_union_right e.support hpQ)
      (by simp only [primeBlockTerm, hpQ, hz, true_and, if_true])

/-- Absolute convergence is obtained directly for norms of the original
four-ideal term, before either prime reindexing or local summation. -/
theorem initial_absolute_norm (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (s w z : ℂ)
    (hs : 4 < s.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    Summable (fun I : FourIdealIndex K S => ‖initialRowEulerTerm K S P ψ Q u s w z I‖) := by
  have hmajor := summable_initialMajorant K S s.re w.re z.re
    (by linarith) (by linarith) (by linarith)
  exact hmajor.of_nonneg_of_le (fun I => norm_nonneg _)
    (norm_initialRowEulerTerm_le K S P ψ Q u s w z)

theorem primeBlockTerm_norm_le_base (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (s w z : ℂ)
    (p : ExteriorPrime K S) (n : FourExponent) :
    ‖primeBlockTerm K S P ψ Q u s w z p n‖ ≤ ‖primeBlockBase K S P ψ u s w z p n‖ := by
  unfold primeBlockTerm
  split_ifs
  · exact (norm_zero : ‖(0 : ℂ)‖ = 0).le.trans (norm_nonneg _)
  · exact le_rfl

theorem primeBlockTerm_absolute (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (s w z : ℂ)
    (hs : 4 < s.re) (hw : 4 < w.re) (hz : 2 < z.re) (p : ExteriorPrime K S) :
    Summable (fun n : FourExponent => ‖primeBlockTerm K S P ψ Q u s w z p n‖) := by
  have hsub := (initial_absolute_norm K S P ψ ∅ u s w z hs hw hz).comp_injective
    ((fourIdealOfPrimeExponents_injective K S).comp (Finsupp.single_injective p))
  have hbase : Summable (fun n : FourExponent => ‖primeBlockBase K S P ψ u s w z p n‖) := by
    simpa only [Function.comp_def, fourIdealOfPrimeExponents_single, primeBlockBase] using hsub
  exact hbase.of_nonneg_of_le (fun n => norm_nonneg _)
    (primeBlockTerm_norm_le_base K S P ψ Q u s w z p)

/-- The literal initial four-ideal sum is the convergent Euler product of
its actual local four-exponent sums. Every whole-index mark is retained. -/
theorem initialRowEulerSeries_hasProd_primeBlocks (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (s w z : ℂ)
    (hs : 4 < s.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    HasProd (fun p : ExteriorPrime K S =>
      ∑' n : FourExponent, primeBlockTerm K S P ψ Q u s w z p n)
      (initialRowEulerSeries K S P ψ Q u s w z) := by
  have habs := (initial_absolute_norm K S P ψ Q u s w z hs hw hz).comp_injective
    (fourIdealOfPrimeExponents_injective K S)
  have h := HighBin.PrimeBlockEuler.hasProd_of_term_factorization
    (primeBlockTerm K S P ψ Q u s w z) Q
    (fun e => initialRowEulerTerm K S P ψ Q u s w z (fourIdealOfPrimeExponents K S e))
    (initialRowEulerTerm_finite_product K S P hP ψ Q u s w z)
    (primeBlockTerm_zero_of_not_mem K S P ψ Q u s w z)
    (primeBlockTerm_absolute K S P ψ Q u s w z hs hw hz) habs
  have heq : (∑' e : ExteriorPrime K S →₀ FourExponent,
      initialRowEulerTerm K S P ψ Q u s w z (fourIdealOfPrimeExponents K S e)) =
      initialRowEulerSeries K S P ψ Q u s w z :=
    (fourPrimeExponentEquiv K S).symm.tsum_eq (initialRowEulerTerm K S P ψ Q u s w z)
  rwa [heq] at h

theorem initialRowEulerSeries_eq_primeBlock_tprod (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (s w z : ℂ)
    (hs : 4 < s.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    initialRowEulerSeries K S P ψ Q u s w z =
      ∏' p : ExteriorPrime K S, ∑' n : FourExponent, primeBlockTerm K S P ψ Q u s w z p n :=
  (initialRowEulerSeries_hasProd_primeBlocks K S P hP ψ Q u s w z hs hw hz).tprod_eq.symm

#print axioms initialRowEulerTerm_finite_product
#print axioms initialRowEulerSeries_hasProd_primeBlocks
#print axioms initialRowEulerSeries_eq_primeBlock_tprod

end HeckeSkeleton.HighBinActualInitial
