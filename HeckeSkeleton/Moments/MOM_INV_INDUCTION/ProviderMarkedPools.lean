import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedOverlap
import HeckeGeneral.Analysis.SIntegerSexticDyadicAmplification

/-!
# Complete finite pools for the initial marked column change

The original finite norm envelope is changed to a single complete
envelope for the residual column.  Only the actual profile support is
used to discard newly inserted terms.  In particular the residual pool
is not an assumed finite reconstruction of an energy.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedPools

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckePort.Moments ProviderMarkedOverlap
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

def norm (I : Ideal (𝓞 K)) : ℝ := I.absNorm

theorem norm_pos {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : 0 < norm I :=
  idealNorm_pos K ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩

@[simp] theorem norm_mul (I J : Ideal (𝓞 K)) : norm (I * J) = norm I * norm J := by
  simp only [norm, map_mul, Nat.cast_mul]

def pool (X : ℝ) : Finset (Ideal (𝓞 K)) :=
  (dyadicIdealSupport K X).image fun I => I.val

theorem mem_pool {X : ℝ} (hX : 0 ≤ X) (I : Ideal (𝓞 K)) :
    I ∈ pool (K := K) X ↔ I ≠ ⊥ ∧ norm I ≤ 2 * X := by
  constructor
  · intro hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact ⟨nonZeroDivisors.coe_ne_zero J,
      (mem_dyadicIdealSupport_iff K hX J).mp hJ⟩
  · rintro ⟨hI, hn⟩
    let J : NonzeroIdeal K := ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩
    exact Finset.mem_image.mpr
      ⟨J, (mem_dyadicIdealSupport_iff K hX J).mpr hn, rfl⟩

def sourcePool (X : ℝ) (j P : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  (pool X).filter fun n => Squarefree n ∧ gcd n (j * P) = j

def targetPool (Y : ℝ) (j P : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  (pool Y).filter fun c => Squarefree c ∧ P ∣ c ∧ IsCoprime c j

theorem source_of_mem {X : ℝ} {j P n : Ideal (𝓞 K)}
    (hn : n ∈ sourcePool X j P) : Squarefree n ∧ gcd n (j * P) = j :=
  (Finset.mem_filter.mp hn).2

theorem target_of_mem {Y : ℝ} {j P c : Ideal (𝓞 K)}
    (hc : c ∈ targetPool Y j P) : Squarefree c ∧ P ∣ c ∧ IsCoprime c j :=
  (Finset.mem_filter.mp hc).2

theorem backward_norm (j P : Ideal (𝓞 K)) (hjP : Squarefree (j * P))
    (c : Target j P) :
    norm (backward j P c.val) = norm j * norm c.val / norm P := by
  let n : Source j P := (columnEquiv j P hjP).symm c
  have hf : forward j P n.val = c.val :=
    forward_backward j P (squarefree_mul_iff.mp hjP).2.1.ne_zero c
  have hn := forward_norm j P n
  rw [hf] at hn
  change norm j * norm c.val = norm (backward j P c.val) * norm P at hn
  exact (eq_div_iff (norm_pos (squarefree_mul_iff.mp hjP).2.2.ne_zero).ne').mpr hn.symm

theorem forward_mem_targetPool (j P : Ideal (𝓞 K)) (hjP : Squarefree (j * P))
    {X Pcap : ℝ} (hX : 0 < X) (hPcap : norm P ≤ Pcap)
    (n : Ideal (𝓞 K)) (hn : n ∈ sourcePool X j P) :
    forward j P n ∈ targetPool (X * Pcap / norm j) j P := by
  let n' : Source j P := ⟨n, source_of_mem hn⟩
  have htarget := forward_mem j P hjP n'
  have hjpos := norm_pos (squarefree_mul_iff.mp hjP).2.1.ne_zero
  have hPpos := norm_pos (squarefree_mul_iff.mp hjP).2.2.ne_zero
  have hcap : 0 < Pcap := hPpos.trans_le hPcap
  have hY : 0 < X * Pcap / norm j := div_pos (mul_pos hX hcap) hjpos
  refine Finset.mem_filter.mpr ⟨(mem_pool hY.le _).mpr ⟨htarget.1.ne_zero, ?_⟩,
    htarget⟩
  have hnorm := forward_norm j P n'
  change norm j * norm (forward j P n) = norm n * norm P at hnorm
  have hnX := ((mem_pool hX.le n).mp (Finset.mem_filter.mp hn).1).2
  apply (le_div_iff₀ hjpos).mpr
  calc
    norm (forward j P n) * norm j = norm n * norm P := by
      rw [mul_comm, hnorm]
    _ ≤ (2 * X) * Pcap := mul_le_mul hnX hPcap hPpos.le (by positivity)
    _ = _ := by ring

/-- Exact finite change of the actual source profile. The new complete
pool is uniform over all residual prime products with `N(P) ≤ Pcap`.
Its additional columns vanish by the original profile support. -/
theorem sum_sourcePool_eq_targetPool (j P : Ideal (𝓞 K))
    (hjP : Squarefree (j * P)) {X Pcap : ℝ}
    (hX : 0 < X) (hPcap : norm P ≤ Pcap)
    (a : Ideal (𝓞 K) → ℂ) (W : ℝ → ℂ)
    (hW : Function.support W ⊆ Set.Iic 2) :
    (∑ n ∈ sourcePool X j P, a n * W (norm n / X)) =
      ∑ c ∈ targetPool (X * Pcap / norm j) j P,
        a (backward j P c) * W (norm j * norm c / (norm P * X)) := by
  let f : Ideal (𝓞 K) → ℂ := fun n => a n * W (norm n / X)
  let g : Ideal (𝓞 K) → ℂ := fun c => f (backward j P c)
  have hgeneric : (∑ n ∈ sourcePool X j P, f n) =
      ∑ c ∈ targetPool (X * Pcap / norm j) j P, g c := by
    apply Finset.sum_bij_ne_zero (fun n _ _ => forward j P n)
    · intro n hn hne
      exact forward_mem_targetPool j P hjP hX hPcap n hn
    · intro n hn hne m hm hme heq
      have h := congrArg (backward j P) heq
      rw [backward_forward j P (squarefree_mul_iff.mp hjP).2.2.ne_zero
        (⟨n, source_of_mem hn⟩ : Source j P),
        backward_forward j P (squarefree_mul_iff.mp hjP).2.2.ne_zero
          (⟨m, source_of_mem hm⟩ : Source j P)] at h
      exact h
    · intro c hc hne
      let c' : Target j P := ⟨c, target_of_mem hc⟩
      have hsource := backward_mem j P hjP c'
      have hWlive : W (norm (backward j P c) / X) ≠ 0 := by
        intro hz
        exact hne (by simp only [g, f, hz, mul_zero])
      have hback : backward j P c ∈ sourcePool X j P := by
        refine Finset.mem_filter.mpr
          ⟨(mem_pool hX.le _).mpr ⟨hsource.1.ne_zero, ?_⟩, hsource⟩
        exact (div_le_iff₀ hX).mp (hW hWlive)
      refine ⟨backward j P c, hback, hne, ?_⟩
      exact forward_backward j P (squarefree_mul_iff.mp hjP).2.1.ne_zero c'
    · intro n hn hne
      dsimp only [g]
      rw [backward_forward j P (squarefree_mul_iff.mp hjP).2.2.ne_zero
        (⟨n, source_of_mem hn⟩ : Source j P)]
  change (∑ n ∈ sourcePool X j P, f n) = _
  rw [hgeneric]
  apply Finset.sum_congr rfl
  intro c hc
  dsimp only [g, f]
  rw [backward_norm j P hjP (⟨c, target_of_mem hc⟩ : Target j P), div_div]

/-- The fixed-fiber coefficient identity inside the complete target
pool, with the original profile evaluated at its exact quotient. -/
theorem character_source_eq_target (j P : Ideal (𝓞 K))
    (hjP : Squarefree (j * P)) {X Pcap : ℝ}
    (hX : 0 < X) (hPcap : norm P ≤ Pcap) (χ : HeckeCharacter K)
    (W : ℝ → ℂ) (hW : Function.support W ⊆ Set.Iic 2) :
    (∑ n ∈ sourcePool X j P,
      (moebius n : ℂ) * idealCoefficient (primeCoefficient K χ) n *
        idealCoefficient (primeCoefficient K χ) (j * P) * W (norm n / X)) =
      (moebius j : ℂ) * (moebius P : ℂ) *
        idealCoefficient (primeCoefficient K χ) j ^ 2 *
        ∑ c ∈ targetPool (X * Pcap / norm j) j P,
          (moebius c : ℂ) * idealCoefficient (primeCoefficient K χ) c *
            W (norm j * norm c / (norm P * X)) := by
  rw [sum_sourcePool_eq_targetPool j P hjP hX hPcap _ W hW, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  let c' : Target j P := ⟨c, target_of_mem hc⟩
  let n : Source j P := (columnEquiv j P hjP).symm c'
  have heq := coefficient_identity j P hjP n χ
  have hf : forward j P n.val = c :=
    forward_backward j P (squarefree_mul_iff.mp hjP).2.1.ne_zero c'
  rw [hf] at heq
  change (moebius (backward j P c) : ℂ) *
      idealCoefficient (primeCoefficient K χ) (backward j P c) *
      idealCoefficient (primeCoefficient K χ) (j * P) = _ at heq
  rw [heq]
  ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedPools
