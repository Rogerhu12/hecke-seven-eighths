import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedOverlap
import HeckeSkeleton.Moments.MOM_INV_STEP.AssignedMarkSource

/-!
# Actual selected slots and the residual canonical divisor mark

The common slot set is computed from the original selected prime tuple.
Its product is proved to be the actual gcd.  After the squarefree column
change, the remaining tuples are exactly the prime choices in the
repository's `divisorMark`.  Their Mobius factors are absorbed by changing
each individual residual coefficient to its negative.  No arbitrary
whole-column coefficient replaces the original slots.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedSlots

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments
open HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP AssignedMarkSource
open ProviderMarkedOverlap
open scoped Classical BigOperators nonZeroDivisors Function

variable {K : Type} [Field K] [NumberField K]
variable {ι : Type*} [DecidableEq ι]

def primeProduct (I : Finset ι) (p : ι → HeightOneSpectrum (𝓞 K)) : Ideal (𝓞 K) :=
  ∏ i ∈ I, (p i).asIdeal

def commonSlots (I : Finset ι) (p : ι → HeightOneSpectrum (𝓞 K))
    (n : Ideal (𝓞 K)) : Finset ι := I.filter fun i => (p i).asIdeal ∣ n

theorem primeProduct_squarefree (I : Finset ι) (p : ι → HeightOneSpectrum (𝓞 K))
    (hinj : Set.InjOn p I) : Squarefree (primeProduct I p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    exact ((p i).isCoprime_of_ne (p j) (fun h => hij (hinj hi hj h))).isRelPrime
  · intro i hi
    exact (p i).prime.squarefree

theorem primeProduct_split (I J : Finset ι) (hJ : J ⊆ I)
    (p : ι → HeightOneSpectrum (𝓞 K)) :
    primeProduct I p = primeProduct J p * primeProduct (I \ J) p := by
  rw [mul_comm]
  exact (Finset.prod_sdiff hJ).symm

theorem commonSlots_product_dvd (I : Finset ι) (p : ι → HeightOneSpectrum (𝓞 K))
    (hinj : Set.InjOn p I) (n : Ideal (𝓞 K)) :
    primeProduct (commonSlots I p n) p ∣ n := by
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    exact (p i).isCoprime_of_ne (p j) (fun heq => hij
      (hinj (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 heq))
  · intro i hi
    exact (Finset.mem_filter.mp hi).2

theorem residual_product_coprime (I : Finset ι) (p : ι → HeightOneSpectrum (𝓞 K))
    (n : Ideal (𝓞 K)) :
    IsCoprime n (primeProduct (I \ commonSlots I p n) p) := by
  apply IsCoprime.prod_right
  intro i hi
  have hnot : ¬ (p i).asIdeal ∣ n := by
    intro hdvd
    exact (Finset.mem_sdiff.mp hi).2
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hi).1, hdvd⟩)
  exact (ideal_coprime_of_relPrime ((p i).irreducible.isRelPrime_iff_not_dvd.mpr
    hnot)).symm

/-- The common subset is not a new label choice: its product is the
gcd of the original inverse column and original selected slot product. -/
theorem commonSlots_product_eq_gcd (I : Finset ι)
    (p : ι → HeightOneSpectrum (𝓞 K)) (hinj : Set.InjOn p I)
    (n : Ideal (𝓞 K)) :
    primeProduct (commonSlots I p n) p = gcd n (primeProduct I p) := by
  let J := commonSlots I p n
  let j := primeProduct J p
  let P := primeProduct (I \ J) p
  have hJ : J ⊆ I := Finset.filter_subset _ _
  have hj : Squarefree j := primeProduct_squarefree J p (hinj.mono hJ)
  have hjn : j ∣ n := commonSlots_product_dvd I p hinj n
  have htotal : primeProduct I p = j * P := primeProduct_split I J hJ p
  have hq : IsCoprime (idealQuotient j n) P := by
    have hdiv : idealQuotient j n ∣ n :=
      (dvd_mul_left (idealQuotient j n) j).trans (dvd_of_eq (idealQuotient_mul hjn))
    exact (residual_product_coprime I p n).of_isCoprime_of_dvd_left hdiv
  symm
  rw [htotal]
  apply (gcd_eq_iff_quotient_coprime j n (j * P) hj.ne_zero hjn
    (dvd_mul_right _ _)).mpr
  simpa only [idealQuotient_self_mul hj.ne_zero] using hq

/-- Every actual squarefree source term enters its constructed gcd
fiber, with the selected and surviving original slots displayed. -/
def sourceOfTuple (I : Finset ι) (p : ι → HeightOneSpectrum (𝓞 K))
    (hinj : Set.InjOn p I) (n : Ideal (𝓞 K)) (hn : Squarefree n) :
    Source (primeProduct (commonSlots I p n) p)
      (primeProduct (I \ commonSlots I p n) p) := by
  refine ⟨n, hn, ?_⟩
  rw [← primeProduct_split I (commonSlots I p n) (Finset.filter_subset _ _) p]
  exact (commonSlots_product_eq_gcd I p hinj n).symm

theorem primeProduct_moebius (I : Finset ι) (p : ι → HeightOneSpectrum (𝓞 K))
    (hinj : Set.InjOn p I) :
    moebius (primeProduct I p) = (-1 : ℤ) ^ I.card := by
  revert hinj
  induction I using Finset.induction_on with
  | empty =>
    intro hinj
    simpa only [primeProduct, Finset.prod_empty, Finset.card_empty, pow_zero] using
      (moebius_one : moebius (1 : Ideal (𝓞 K)) = 1)
  | @insert i I hi ih =>
    intro hinj
    have hrest : Set.InjOn p I := hinj.mono (Finset.subset_insert _ _)
    have hcop : IsRelPrime (p i).asIdeal (primeProduct I p) := by
      apply IsRelPrime.prod_right
      intro j hj
      apply IsCoprime.isRelPrime
      apply (p i).isCoprime_of_ne (p j)
      intro heq
      have hij := hinj (Finset.mem_insert_self i I) (Finset.mem_insert_of_mem hj) heq
      exact hi (hij.symm ▸ hj)
    have hprod : primeProduct (insert i I) p = (p i).asIdeal * primeProduct I p :=
      Finset.prod_insert hi
    rw [hprod, hcop.moebius_mul,
      (p i).irreducible.moebius_eq, ih hrest, Finset.card_insert_of_notMem hi,
      pow_succ]
    ring

variable {J : ℕ}

theorem primeChoices_injective
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists)) (c : Ideal (𝓞 K))
    (p : Fin J → HeightOneSpectrum (𝓞 K)) (hp : p ∈ primeChoices lists c) :
    Function.Injective p := by
  intro i j heq
  by_contra hij
  have hmem := (mem_primeChoices lists c p).mp hp
  exact Finset.disjoint_left.mp (hdis hij) (hmem i).1 (by simpa [heq] using (hmem j).1)

theorem primeChoices_product_dvd
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists)) (c : Ideal (𝓞 K))
    (p : Fin J → HeightOneSpectrum (𝓞 K)) (hp : p ∈ primeChoices lists c) :
    primeProduct Finset.univ p ∣ c := by
  have hinj := primeChoices_injective lists hdis c p hp
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    exact (p i).isCoprime_of_ne (p j) (fun heq => hij (hinj heq))
  · intro i hi
    exact ((mem_primeChoices lists c p).mp hp i).2

/-- The residual Mobius factor is still a product of the individual
original coefficients. It becomes the literal canonical divisor mark. -/
theorem signed_choices_eq_divisorMark
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists))
    (a : Fin J → Ideal (𝓞 K) → ℂ) (c : Ideal (𝓞 K)) :
    (∑ p ∈ primeChoices lists c,
      (moebius (primeProduct Finset.univ p) : ℂ) * choiceWeight a p) =
      divisorMark Finset.univ (fun i => (lists i).image HeightOneSpectrum.asIdeal)
        (fun i P => -a i P) c := by
  rw [divisorMark_eq_primeChoices]
  apply Finset.sum_congr rfl
  intro p hp
  have hμ := primeProduct_moebius Finset.univ p
    (fun _ _ _ _ heq => primeChoices_injective lists hdis c p hp heq)
  rw [hμ]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, Finset.card_univ, Fintype.card_fin,
    choiceWeight, neg_eq_neg_one_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- Fixed `j`, fixed new column: summing the actual old inverse terms
over all surviving original choices gives exactly `μ(c) χ(c)` times
the residual divisor mark. The moving character square remains outside. -/
theorem original_choices_eq_canonical_mark
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists)) (a : Fin J → Ideal (𝓞 K) → ℂ)
    (j c : Ideal (𝓞 K)) (hj : Squarefree j) (hc : Squarefree c)
    (hcj : IsCoprime c j) (χ : HeckeCharacter K) :
    (∑ p ∈ primeChoices lists c,
      (moebius (backward j (primeProduct Finset.univ p) c) : ℂ) *
        idealCoefficient (primeCoefficient K χ) (backward j (primeProduct Finset.univ p) c) *
        idealCoefficient (primeCoefficient K χ) (j * primeProduct Finset.univ p) *
        choiceWeight a p) =
      (moebius j : ℂ) * idealCoefficient (primeCoefficient K χ) j ^ 2 *
        (moebius c : ℂ) * idealCoefficient (primeCoefficient K χ) c *
        divisorMark Finset.univ (fun i => (lists i).image HeightOneSpectrum.asIdeal)
          (fun i P => -a i P) c := by
  rw [← signed_choices_eq_divisorMark lists hdis a c, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  let P := primeProduct Finset.univ p
  have hPc : P ∣ c := primeChoices_product_dvd lists hdis c p hp
  have hP : Squarefree P := hc.squarefree_of_dvd hPc
  have hjP : Squarefree (j * P) := squarefree_mul_iff.mpr
    ⟨(hcj.of_isCoprime_of_dvd_left hPc).symm.isRelPrime, hj, hP⟩
  let c' : Target j P := ⟨c, hc, hPc, hcj⟩
  let n : Source j P := (columnEquiv j P hjP).symm c'
  have heq := coefficient_identity j P hjP n χ
  change (moebius (backward j P c) : ℂ) *
      idealCoefficient (primeCoefficient K χ) (backward j P c) *
      idealCoefficient (primeCoefficient K χ) (j * P) = _ at heq
  have hf : forward j P n.val = c := forward_backward j P hj.ne_zero c'
  rw [hf] at heq
  rw [heq]
  ring

theorem signed_weight_norm_le (a : Fin J → Ideal (𝓞 K) → ℂ)
    (i : Fin J) (P : Ideal (𝓞 K)) (ha : ‖a i P‖ ≤ 1) : ‖-a i P‖ ≤ 1 := by
  simpa only [norm_neg] using ha

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedSlots
