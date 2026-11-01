import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedSlots
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedPools

/-!
# Exact finite residual-slot reindexing of a fixed initial overlap

The target column envelope is common to all original surviving prime
tuples.  Its divisibility fibers are proved to be the repository's
actual `primeChoices`, so the next Mellin step can sum those choices as
the literal residual `divisorMark`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedReindex

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeSkeleton.Moments.MOM_INV_STEP AssignedMarkSource
open ProviderMarkedOverlap ProviderMarkedSlots ProviderMarkedPools
open scoped Classical BigOperators nonZeroDivisors Function

variable {K : Type} [Field K] [NumberField K] {J : ℕ}

def tuples (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K))) :=
  Fintype.piFinset lists

theorem tuple_injective (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists))
    (p : Fin J → HeightOneSpectrum (𝓞 K)) (hp : p ∈ tuples lists) :
    Function.Injective p := by
  intro i j heq
  by_contra hij
  have hmem := Fintype.mem_piFinset.mp hp
  exact Finset.disjoint_left.mp (hdis hij) (hmem i) (by simpa only [heq] using hmem j)

theorem tuple_product_squarefree (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists))
    (p : Fin J → HeightOneSpectrum (𝓞 K)) (hp : p ∈ tuples lists) :
    Squarefree (primeProduct Finset.univ p) :=
  primeProduct_squarefree Finset.univ p
    (fun _ _ _ _ heq => tuple_injective lists hdis p hp heq)

theorem primeChoices_eq_filter (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists)) (c : Ideal (𝓞 K)) :
    primeChoices lists c = (tuples lists).filter fun p => primeProduct Finset.univ p ∣ c := by
  ext p
  constructor
  · intro hp
    refine Finset.mem_filter.mpr ⟨?_, primeChoices_product_dvd lists hdis c p hp⟩
    exact Fintype.mem_piFinset.mpr fun i => ((mem_primeChoices lists c p).mp hp i).1
  · intro hp
    obtain ⟨hp, hprod⟩ := Finset.mem_filter.mp hp
    apply (mem_primeChoices lists c p).mpr
    intro i
    exact ⟨Fintype.mem_piFinset.mp hp i,
      (Finset.dvd_prod_of_mem (fun i => (p i).asIdeal) (Finset.mem_univ i)).trans hprod⟩

def columns (Y : ℝ) (j : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  (pool Y).filter fun c => Squarefree c ∧ IsCoprime c j

theorem targetPool_eq_filter (Y : ℝ) (j P : Ideal (𝓞 K)) :
    targetPool Y j P = (columns Y j).filter fun c => P ∣ c := by
  ext c
  simp only [targetPool, columns, Finset.mem_filter]
  exact ⟨fun h => ⟨⟨h.1, h.2.1, h.2.2.2⟩, h.2.2.1⟩,
    fun h => ⟨h.1.1, h.1.2.1, h.2, h.1.2.2⟩⟩

/-- Exact finite Fubini over the new column and the surviving original
prime choices. All divisibility conditions are preserved. -/
theorem sum_target_fibers (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists)) (Y : ℝ) (j : Ideal (𝓞 K))
    (f : (Fin J → HeightOneSpectrum (𝓞 K)) → Ideal (𝓞 K) → ℂ) :
    (∑ p ∈ tuples lists, ∑ c ∈ targetPool Y j (primeProduct Finset.univ p), f p c) =
      ∑ c ∈ columns Y j, ∑ p ∈ primeChoices lists c, f p c := by
  simp_rw [targetPool_eq_filter, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [primeChoices_eq_filter lists hdis c, Finset.sum_filter]

/-- Reindex the actual complete original inverse envelope and every
remaining original prime tuple. The inverse profile alone kills all
extra inverse columns introduced by the common target envelope. -/
theorem fixed_selected_reindex
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists))
    (j : Ideal (𝓞 K)) (hj : Squarefree j)
    (hcop : ∀ p ∈ tuples lists, IsCoprime j (primeProduct Finset.univ p))
    (X Pcap : ℝ) (hX : 0 < X)
    (hPcap : ∀ p ∈ tuples lists, ProviderMarkedPools.norm (primeProduct Finset.univ p) ≤ Pcap)
    (a : (Fin J → HeightOneSpectrum (𝓞 K)) → Ideal (𝓞 K) → ℂ)
    (W : ℝ → ℂ) (hW : Function.support W ⊆ Set.Iic 2) :
    (∑ p ∈ tuples lists, ∑ n ∈ sourcePool X j (primeProduct Finset.univ p),
      a p n * W (ProviderMarkedPools.norm n / X)) =
      ∑ c ∈ columns (X * Pcap / ProviderMarkedPools.norm j) j,
        ∑ p ∈ primeChoices lists c,
          a p (backward j (primeProduct Finset.univ p) c) *
            W (ProviderMarkedPools.norm j * ProviderMarkedPools.norm c /
              (ProviderMarkedPools.norm (primeProduct Finset.univ p) * X)) := by
  calc
    _ = ∑ p ∈ tuples lists,
        ∑ c ∈ targetPool (X * Pcap / ProviderMarkedPools.norm j) j
          (primeProduct Finset.univ p),
          a p (backward j (primeProduct Finset.univ p) c) *
            W (ProviderMarkedPools.norm j * ProviderMarkedPools.norm c /
              (ProviderMarkedPools.norm (primeProduct Finset.univ p) * X)) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply sum_sourcePool_eq_targetPool j _ _ hX (hPcap p hp) (a p) W hW
      exact squarefree_mul_iff.mpr
        ⟨(hcop p hp).isRelPrime, hj, tuple_product_squarefree lists hdis p hp⟩
    _ = _ := sum_target_fibers lists hdis _ j _

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedReindex
