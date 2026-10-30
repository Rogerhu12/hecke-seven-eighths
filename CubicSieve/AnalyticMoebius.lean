import CubicSieve.AnalyticDivisors
import DedekindZetaZeroFree.Arithmetic.Ideals.MoebiusCoprimality

/-!
Pointwise Möbius removal of the true common-prime mask.  The radical proof
below is the finite divisor argument used by MoebiusCoprimality, exposed at
the pointwise interface needed for the actual cubic Gram decomposition.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.AnalyticGcd

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CubicSieve.ExteriorKernel
open DedekindZetaZeroFree.LargeSieve
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

private theorem sum_mu (a : Ideal (𝓞 K)) (ha : a ≠ ⊥) :
    (∑ d ∈ idealDivisors a, (moebius d : ℂ)) = if a = ⊤ then 1 else 0 := by
  let r := UniqueFactorizationMonoid.radical a
  have hr : r ≠ ⊥ := radical_ne_zero
  obtain ⟨hp, hprod, hd, hi, hmu, hmem⟩ :=
    Vendor.CutoffDifference.squarefree_divisor_dictionary r hr squarefree_radical
  have heq : idealDivisors r = Vendor.CutoffDifference.SplitData.divisors r := by
    ext d
    rw [mem_idealDivisors hr, hmem]
  have hsub : idealDivisors r ⊆ idealDivisors a := by
    intro d hd
    exact (mem_idealDivisors ha).mpr
      (((mem_idealDivisors hr).mp hd).trans radical_dvd_self)
  have hz : ∀ d ∈ idealDivisors a, d ∉ idealDivisors r → (moebius d : ℂ) = 0 := by
    intro d hd hdr
    have hns : ¬ Squarefree d := by
      intro hs
      exact hdr ((mem_idealDivisors hr).mpr
        ((dvd_radical_iff hs.isRadical ha).mpr ((mem_idealDivisors ha).mp hd)))
    simp [moebius_of_not_squarefree hns]
  rw [← Finset.sum_subset hsub hz, heq, hd]
  trans ∑ T ∈ (factors r).toFinset.powerset, (moebius (∏ p ∈ T, p) : ℂ)
  · exact Finset.sum_image hi
  have he : (∑ T ∈ (factors r).toFinset.powerset, (moebius (∏ p ∈ T, p) : ℂ)) =
      ∑ T ∈ (factors r).toFinset.powerset, (-1 : ℂ) ^ T.card := by
    apply Finset.sum_congr rfl
    intro T hT
    rw [hmu T hT]
    push_cast
    rfl
  rw [he]
  have heprod : (∑ T ∈ (factors r).toFinset.powerset, (-1 : ℂ) ^ T.card) =
      ∏ p ∈ (factors r).toFinset, (1 + (-1 : ℂ)) := by
    rw [Finset.prod_one_add]
    simp
  rw [heprod]
  have hP : (factors r).toFinset = ∅ ↔ a = ⊤ := by
    constructor
    · intro h
      have hr1 : r = 1 := hprod.symm.trans
        ((congrArg (fun T : Finset (Ideal (𝓞 K)) => ∏ p ∈ T, p) h).trans (by simp))
      exact Ideal.isUnit_iff.mp ((radical_eq_one_iff.mp hr1).resolve_left ha)
    · intro h
      subst a
      have hr1 : r = 1 := radical_of_isUnit (Ideal.isUnit_iff.mpr rfl)
      rw [hr1]
      simp only [factors_one, Multiset.toFinset_zero]
  by_cases h : a = ⊤
  · rw [hP.mpr h, Finset.prod_empty, if_pos h]
  · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr (fun he => h (hP.mp he))
    rw [if_neg h]
    simp only [add_neg_cancel]
    exact Finset.prod_eq_zero hp rfl

theorem ideal_coprime_mask (m I : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    (∑ d ∈ idealDivisors m, if d ∣ I then (moebius d : ℂ) else 0) =
      if IsCoprime I m then 1 else 0 := by
  have hsup : I ⊔ m ≠ ⊥ := fun h => hm (le_bot_iff.mp (h ▸ le_sup_right))
  have heq : (idealDivisors m).filter (fun d => d ∣ I) = idealDivisors (I ⊔ m) := by
    ext d
    simp only [Finset.mem_filter, mem_idealDivisors hm, mem_idealDivisors hsup,
      Ideal.dvd_iff_le, sup_le_iff]
    exact and_comm
  rw [← Finset.sum_filter, heq, sum_mu K _ hsup]
  congr 1
  exact propext Ideal.isCoprime_iff_sup_eq.symm

theorem coprime_mask (R d : ExteriorIdeal K S) :
    (if IsCoprime R.val.val d.val.val then (1 : ℂ) else 0) =
      ∑ e ∈ divisors K S d, if e.val.val ∣ R.val.val then (moebius e.val.val : ℂ) else 0 := by
  have he := ideal_coprime_mask K d.val.val R.val.val (nonZeroDivisors.coe_ne_zero d.val)
  rw [← divisors_image K S d, Finset.sum_image] at he
  · exact he.symm
  · intro I hI J hJ h
    exact Subtype.ext (Subtype.ext h)

theorem moebius_norm_le_one (d : ExteriorIdeal K S) : ‖(moebius d.val.val : ℂ)‖ ≤ 1 := by
  by_cases hs : Squarefree d.val.val
  · rw [hs.moebius_eq]
    push_cast
    simp
  · simp [moebius_of_not_squarefree hs]

/-- Exact finite removal, keeping the signed Möbius coefficient and every divisor. -/
theorem common_mask_sum (R d : ExteriorIdeal K S) (f : ExteriorIdeal K S → ℂ) :
    (if IsCoprime R.val.val d.val.val then (1 : ℂ) else 0) * f R =
      ∑ e ∈ divisors K S d, (moebius e.val.val : ℂ) *
        (if e.val.val ∣ R.val.val then f R else 0) := by
  rw [coprime_mask K S R d, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  by_cases h : e.val.val ∣ R.val.val <;> simp [h]

end CubicSieve.AnalyticGcd
