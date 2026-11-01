import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedMellin
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedMask

/-!
# The original common mask in the actual marked Mellin source

The original exterior exclusions and row coprimality mask are carried
through the fixed-overlap finite change of variables.  Their extracted
part is a row contraction; their remaining part stays on the literal
canonical column.  No cancellation of a ramification zero is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedMaskedMellin

open NumberField IsDedekindDomain UniqueFactorizationMonoid MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP AssignedMarkSource
open CommonKernel MellinSeparation
open ProviderMarkedOverlap ProviderMarkedSlots ProviderMarkedReindex ProviderMarkedMellin
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] {J : ℕ}

def weightedCanonicalColumn (χ : HeckeCharacter K)
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (a : Fin J → Ideal (𝓞 K) → ℂ) (mark : Ideal (𝓞 K) → ℂ)
    (C : Finset (Ideal (𝓞 K))) (U t : ℝ) : ℂ :=
  ∑ c ∈ C, (moebius c : ℂ) * idealCoefficient (primeCoefficient K χ) c * mark c *
    divisorMark Finset.univ (fun i => (lists i).image HeightOneSpectrum.asIdeal)
      (primeWeight a t) c * test t (ProviderMarkedPools.norm c / U)

theorem weighted_residual_source_eq_integral
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists)) (a : Fin J → Ideal (𝓞 K) → ℂ)
    (j : Ideal (𝓞 K)) (hj : Squarefree j) (χ : HeckeCharacter K)
    (mark : Ideal (𝓞 K) → ℂ) (C : Finset (Ideal (𝓞 K)))
    (hc : ∀ c ∈ C, Squarefree c ∧ IsCoprime c j)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (X U : ℝ) (hX : 0 < X) (hU : 0 < U) :
    (∑ c ∈ C, ∑ p ∈ primeChoices lists c,
      (mark c * originalCoefficient χ a j p (backward j (primeProduct Finset.univ p) c)) *
        W (ProviderMarkedPools.norm j * ProviderMarkedPools.norm c /
          (ProviderMarkedPools.norm (primeProduct Finset.univ p) * X)) *
        Expansion.Dyadic.annularProfile (ProviderMarkedPools.norm c / U)) =
      extractedScalar χ j *
        ∫ t : ℝ, density W hW t * columnPhase t (Real.log (ProviderMarkedPools.norm j)) *
          columnPhase t (-Real.log X) * columnPhase t (Real.log U) *
            weightedCanonicalColumn χ lists a mark C U t := by
  have hnormc (c : Ideal (𝓞 K)) (hcC : c ∈ C) : 0 < ProviderMarkedPools.norm c :=
    ProviderMarkedPools.norm_pos (hc c hcC).1.ne_zero
  have hnormp (c : Ideal (𝓞 K)) (hcC : c ∈ C)
      (p : Fin J → HeightOneSpectrum (𝓞 K)) (hp : p ∈ primeChoices lists c) :
      0 < ProviderMarkedPools.norm (primeProduct Finset.univ p) :=
    ProviderMarkedPools.norm_pos (primeProduct_squarefree Finset.univ p
      (fun _ _ _ _ heq => primeChoices_injective lists hdis c p hp heq)).ne_zero
  rw [finite_quotient_inverse C (primeChoices lists) ProviderMarkedPools.norm
    (fun p => ProviderMarkedPools.norm (primeProduct Finset.univ p))
    (fun c p => mark c * originalCoefficient χ a j p
      (backward j (primeProduct Finset.univ p) c))
    W hW (ProviderMarkedPools.norm j) X U (ProviderMarkedPools.norm_pos hj.ne_zero)
    hX hU hnormc hnormp, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    have hsum :
        (∑ c ∈ C, ∑ p ∈ primeChoices lists c,
          (mark c * originalCoefficient χ a j p (backward j (primeProduct Finset.univ p) c)) *
            columnPhase t (-Real.log (ProviderMarkedPools.norm (primeProduct Finset.univ p))) *
            test t (ProviderMarkedPools.norm c / U)) =
          extractedScalar χ j * weightedCanonicalColumn χ lists a mark C U t := by
      rw [weightedCanonicalColumn, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hcC
      calc
        _ = mark c *
            (∑ p ∈ primeChoices lists c,
              originalCoefficient χ a j p (backward j (primeProduct Finset.univ p) c) *
                columnPhase t (-Real.log (ProviderMarkedPools.norm (primeProduct Finset.univ p)))) *
            test t (ProviderMarkedPools.norm c / U) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro p hp
          ring
        _ = _ := by
          rw [original_twisted_choices lists hdis a j c hj (hc c hcC).1 (hc c hcC).2 χ t]
          ring
    rw [hsum]
    ring

/-- The complete fixed-overlap source with every original mask. Its
output has the additional coprime puncture `j` in the target column
pool, and retains the original common mask on that column. -/
theorem fixed_selected_masked_annular_eq_integral
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists)) (a : Fin J → Ideal (𝓞 K) → ℂ)
    (good : HeightOneSpectrum (𝓞 K) → Prop) (u j : Ideal (𝓞 K))
    (hj : Squarefree j)
    (hcop : ∀ p ∈ tuples lists, IsCoprime j (primeProduct Finset.univ p))
    (χ : HeckeCharacter K) (X U Pcap : ℝ) (hX : 0 < X) (hU : 0 < U)
    (hPcap : ∀ p ∈ tuples lists,
      ProviderMarkedPools.norm (primeProduct Finset.univ p) ≤ Pcap)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) :
    (∑ p ∈ tuples lists, ∑ n ∈ ProviderMarkedPools.sourcePool X j (primeProduct Finset.univ p),
      originalCoefficient χ a j p n * ProviderMarkedMask.value good u n *
        ProviderMarkedMask.value good u (j * primeProduct Finset.univ p) *
        Expansion.Dyadic.annularProfile
          (ProviderMarkedPools.norm (forward j (primeProduct Finset.univ p) n) / U) *
        W (ProviderMarkedPools.norm n / X)) =
      (ProviderMarkedMask.value good u j * extractedScalar χ j) *
        ∫ t : ℝ, density W hW t * columnPhase t (Real.log (ProviderMarkedPools.norm j)) *
          columnPhase t (-Real.log X) * columnPhase t (Real.log U) *
            weightedCanonicalColumn χ lists a (ProviderMarkedMask.value good u)
              (columns (X * Pcap / ProviderMarkedPools.norm j) j) U t := by
  have hsupport : Function.support W ⊆ Set.Iic 2 := by
    intro x hx
    exact (hW (subset_closure hx)).2
  rw [fixed_selected_reindex lists hdis j hj hcop X Pcap hX hPcap
    (fun p n => originalCoefficient χ a j p n * ProviderMarkedMask.value good u n *
      ProviderMarkedMask.value good u (j * primeProduct Finset.univ p) *
      Expansion.Dyadic.annularProfile
        (ProviderMarkedPools.norm (forward j (primeProduct Finset.univ p) n) / U)) W hsupport]
  let C := columns (X * Pcap / ProviderMarkedPools.norm j) j
  have hcolumns (c : Ideal (𝓞 K)) (hc : c ∈ C) : Squarefree c ∧ IsCoprime c j :=
    (Finset.mem_filter.mp hc).2
  calc
    _ = ProviderMarkedMask.value good u j *
        (∑ c ∈ C, ∑ p ∈ primeChoices lists c,
          (ProviderMarkedMask.value good u c * originalCoefficient χ a j p
            (backward j (primeProduct Finset.univ p) c)) *
            W (ProviderMarkedPools.norm j * ProviderMarkedPools.norm c /
              (ProviderMarkedPools.norm (primeProduct Finset.univ p) * X)) *
            Expansion.Dyadic.annularProfile (ProviderMarkedPools.norm c / U)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      let P := primeProduct Finset.univ p
      have hPc : P ∣ c := primeChoices_product_dvd lists hdis c p hp
      have hP : Squarefree P := (hcolumns c hc).1.squarefree_of_dvd hPc
      have hjP : Squarefree (j * P) := squarefree_mul_iff.mpr
        ⟨((hcolumns c hc).2.of_isCoprime_of_dvd_left hPc).symm.isRelPrime, hj, hP⟩
      let c' : Target j P := ⟨c, (hcolumns c hc).1, hPc, (hcolumns c hc).2⟩
      let n : Source j P := (columnEquiv j P hjP).symm c'
      have hf : forward j P n.val = c := forward_backward j P hj.ne_zero c'
      have hm := ProviderMarkedMask.overlap_value good u j P n
      rw [hf] at hm
      change ProviderMarkedMask.value good u (backward j P c) *
        ProviderMarkedMask.value good u (j * P) =
        ProviderMarkedMask.value good u j * ProviderMarkedMask.value good u c at hm
      change _ = ProviderMarkedMask.value good u j *
        ((ProviderMarkedMask.value good u c * originalCoefficient χ a j p (backward j P c)) *
          W (ProviderMarkedPools.norm j * ProviderMarkedPools.norm c /
            (ProviderMarkedPools.norm P * X)) *
          Expansion.Dyadic.annularProfile (ProviderMarkedPools.norm c / U))
      rw [show forward j P (backward j P c) = c from hf]
      calc
        _ = originalCoefficient χ a j p (backward j P c) *
            (ProviderMarkedMask.value good u (backward j P c) *
              ProviderMarkedMask.value good u (j * P)) *
            Expansion.Dyadic.annularProfile (ProviderMarkedPools.norm c / U) *
            W (ProviderMarkedPools.norm j * ProviderMarkedPools.norm c /
              (ProviderMarkedPools.norm P * X)) := by ring
        _ = _ := by rw [hm]; ring
    _ = _ := by
      rw [weighted_residual_source_eq_integral lists hdis a j hj χ
        (ProviderMarkedMask.value good u) C hcolumns W hW X U hX hU]
      ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedMaskedMellin
