import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedMaskedMellin
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SourceFourierControl

/-!
# Actual logarithmic profiles in the marked overlap source

Fourier inversion is applied directly to the original logarithmic
Schwartz profile.  No replacement of its cutoff or rowwise parameters
is made.  The same fixed annular column test carries the moving ideal;
the only row-dependent analytic factor is the genuine Fourier density.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedLogMellin

open NumberField IsDedekindDomain UniqueFactorizationMonoid MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP
open CommonKernel MellinSeparation
open ProviderMarkedOverlap ProviderMarkedSlots ProviderMarkedReindex ProviderMarkedMellin
  ProviderMarkedMaskedMellin
open scoped Classical BigOperators nonZeroDivisors FourierTransform Function

def profile (F : SchwartzMap ℝ ℂ) (y : ℝ) : ℂ := F (Real.log y)

theorem quotient_inverse (F : SchwartzMap ℝ ℂ)
    (j c P X : ℝ) (hj : 0 < j) (hc : 0 < c) (hP : 0 < P) (hX : 0 < X) :
    profile F (j * c / (P * X)) =
      ∫ t : ℝ, (𝓕 F) t * columnPhase t (Real.log j) *
        columnPhase t (Real.log c) * columnPhase t (-Real.log P) *
          columnPhase t (-Real.log X) := by
  change F (Real.log (j * c / (P * X))) = _
  rw [fourier_inverse F]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    rw [Real.log_div (mul_ne_zero hj.ne' hc.ne') (mul_ne_zero hP.ne' hX.ne'),
      Real.log_mul hj.ne' hc.ne', Real.log_mul hP.ne' hX.ne']
    rw [show Real.log j + Real.log c - (Real.log P + Real.log X) =
      ((Real.log j + Real.log c) + -Real.log P) + -Real.log X by ring]
    simp only [MellinWeightedTests.columnPhase_add]
    ring

theorem quotient_integrable (F : SchwartzMap ℝ ℂ) (j c P X : ℝ) :
    Integrable (fun t : ℝ => (𝓕 F) t * columnPhase t (Real.log j) *
      columnPhase t (Real.log c) * columnPhase t (-Real.log P) *
        columnPhase t (-Real.log X)) := by
  apply ((𝓕 F)).integrable.norm.mono'
    ((((((𝓕 F)).continuous.mul (continuous_columnPhase _)).mul
      (continuous_columnPhase _)).mul (continuous_columnPhase _)).mul
        (continuous_columnPhase _) |>.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun t => by
    change ‖(𝓕 F) t * columnPhase t (Real.log j) *
      columnPhase t (Real.log c) * columnPhase t (-Real.log P) *
        columnPhase t (-Real.log X)‖ ≤ ‖(𝓕 F) t‖
    simpa only [norm_mul, norm_columnPhase, mul_one] using
      (le_rfl : ‖(𝓕 F) t‖ ≤ ‖(𝓕 F) t‖)

/-- The same actual column annulus is used for every residual tuple;
the inverse profile is separated without replacing its argument. -/
theorem quotient_annular_inverse (F : SchwartzMap ℝ ℂ)
    (j c P X U : ℝ) (hj : 0 < j) (hc : 0 < c) (hP : 0 < P)
    (hX : 0 < X) (hU : 0 < U) :
    profile F (j * c / (P * X)) * Expansion.Dyadic.annularProfile (c / U) =
      ∫ t : ℝ, (𝓕 F) t * columnPhase t (Real.log j) *
        columnPhase t (-Real.log X) * columnPhase t (Real.log U) *
          columnPhase t (-Real.log P) * test t (c / U) := by
  rw [quotient_inverse F j c P X hj hc hP hX, ← integral_mul_const]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    have hs := test_phase t c U hc hU
    calc
      _ = (𝓕 F) t * columnPhase t (Real.log j) *
          columnPhase t (-Real.log X) * columnPhase t (-Real.log P) *
            (Expansion.Dyadic.annularProfile (c / U) * columnPhase t (Real.log c)) := by ring
      _ = _ := by rw [← hs]; ring

theorem quotient_annular_integrable (F : SchwartzMap ℝ ℂ)
    (j c P X U : ℝ) (hc : 0 < c) (hU : 0 < U) :
    Integrable (fun t : ℝ => (𝓕 F) t * columnPhase t (Real.log j) *
      columnPhase t (-Real.log X) * columnPhase t (Real.log U) *
        columnPhase t (-Real.log P) * test t (c / U)) := by
  apply ((quotient_integrable F j c P X).mul_const
    (Expansion.Dyadic.annularProfile (c / U))).congr
  exact Filter.Eventually.of_forall fun t => by
    have hs := test_phase t c U hc hU
    calc
      _ = (𝓕 F) t * columnPhase t (Real.log j) *
          columnPhase t (-Real.log X) * columnPhase t (-Real.log P) *
            (Expansion.Dyadic.annularProfile (c / U) * columnPhase t (Real.log c)) := by ring
      _ = _ := by rw [← hs]; ring

/-- Genuine finite Fubini, including the dependent residual prime
choices for each new column. -/
theorem finite_quotient_inverse {α β : Type*} (C : Finset α) (P : α → Finset β)
    (cNorm : α → ℝ) (pNorm : β → ℝ) (w : α → β → ℂ)
    (F : SchwartzMap ℝ ℂ)
    (j X U : ℝ) (hj : 0 < j) (hX : 0 < X) (hU : 0 < U)
    (hc : ∀ c ∈ C, 0 < cNorm c) (hp : ∀ c ∈ C, ∀ p ∈ P c, 0 < pNorm p) :
    (∑ c ∈ C, ∑ p ∈ P c,
      w c p * profile F (j * cNorm c / (pNorm p * X)) *
        Expansion.Dyadic.annularProfile (cNorm c / U)) =
      ∫ t : ℝ, (𝓕 F) t * columnPhase t (Real.log j) *
        columnPhase t (-Real.log X) * columnPhase t (Real.log U) *
          ∑ c ∈ C, ∑ p ∈ P c,
            w c p * columnPhase t (-Real.log (pNorm p)) * test t (cNorm c / U) := by
  let integrand : α → β → ℝ → ℂ := fun c p t => w c p *
    ((𝓕 F) t * columnPhase t (Real.log j) *
      columnPhase t (-Real.log X) * columnPhase t (Real.log U) *
        columnPhase t (-Real.log (pNorm p)) * test t (cNorm c / U))
  have hF (c : α) (hcC : c ∈ C) (p : β) : Integrable (integrand c p) :=
    (quotient_annular_integrable F j (cNorm c) (pNorm p) X U
      (hc c hcC) hU).const_mul _
  calc
    _ = ∑ c ∈ C, ∑ p ∈ P c, ∫ t : ℝ, integrand c p t := by
      apply Finset.sum_congr rfl
      intro c hcC
      apply Finset.sum_congr rfl
      intro p hpP
      rw [mul_assoc, quotient_annular_inverse F j (cNorm c) (pNorm p) X U
        hj (hc c hcC) (hp c hcC p hpP) hX hU, integral_const_mul]
    _ = ∫ t : ℝ, ∑ c ∈ C, ∑ p ∈ P c, integrand c p t := by
      symm
      rw [integral_finsetSum C (fun c hcC =>
        integrable_finsetSum (P c) (fun p hpP => hF c hcC p))]
      apply Finset.sum_congr rfl
      intro c hcC
      exact integral_finsetSum (P c) (fun p hpP => hF c hcC p)
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        dsimp only
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c hcC
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hpP
        dsimp only [integrand]
        ring

variable {K : Type} [Field K] [NumberField K] {J : ℕ}

theorem weighted_residual_source_eq_integral
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists)) (a : Fin J → Ideal (𝓞 K) → ℂ)
    (j : Ideal (𝓞 K)) (hj : Squarefree j) (χ : HeckeCharacter K)
    (mark : Ideal (𝓞 K) → ℂ) (C : Finset (Ideal (𝓞 K)))
    (hc : ∀ c ∈ C, Squarefree c ∧ IsCoprime c j)
    (F : SchwartzMap ℝ ℂ) (hF : Function.support (profile F) ⊆ Set.Iic 2)
    (X U : ℝ) (hX : 0 < X) (hU : 0 < U) :
    (∑ c ∈ C, ∑ p ∈ primeChoices lists c,
      (mark c * originalCoefficient χ a j p (backward j (primeProduct Finset.univ p) c)) *
        profile F (ProviderMarkedPools.norm j * ProviderMarkedPools.norm c /
          (ProviderMarkedPools.norm (primeProduct Finset.univ p) * X)) *
        Expansion.Dyadic.annularProfile (ProviderMarkedPools.norm c / U)) =
      extractedScalar χ j *
        ∫ t : ℝ, (𝓕 F) t * columnPhase t (Real.log (ProviderMarkedPools.norm j)) *
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
    F (ProviderMarkedPools.norm j) X U (ProviderMarkedPools.norm_pos hj.ne_zero)
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
    dsimp only
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
    (F : SchwartzMap ℝ ℂ) (hF : Function.support (profile F) ⊆ Set.Iic 2) :
    (∑ p ∈ tuples lists, ∑ n ∈ ProviderMarkedPools.sourcePool X j (primeProduct Finset.univ p),
      originalCoefficient χ a j p n * ProviderMarkedMask.value good u n *
        ProviderMarkedMask.value good u (j * primeProduct Finset.univ p) *
        Expansion.Dyadic.annularProfile
          (ProviderMarkedPools.norm (forward j (primeProduct Finset.univ p) n) / U) *
        profile F (ProviderMarkedPools.norm n / X)) =
      (ProviderMarkedMask.value good u j * extractedScalar χ j) *
        ∫ t : ℝ, (𝓕 F) t * columnPhase t (Real.log (ProviderMarkedPools.norm j)) *
          columnPhase t (-Real.log X) * columnPhase t (Real.log U) *
            weightedCanonicalColumn χ lists a (ProviderMarkedMask.value good u)
              (columns (X * Pcap / ProviderMarkedPools.norm j) j) U t := by
  have hsupport : Function.support (profile F) ⊆ Set.Iic 2 := hF
  rw [fixed_selected_reindex lists hdis j hj hcop X Pcap hX hPcap
    (fun p n => originalCoefficient χ a j p n * ProviderMarkedMask.value good u n *
      ProviderMarkedMask.value good u (j * primeProduct Finset.univ p) *
      Expansion.Dyadic.annularProfile
        (ProviderMarkedPools.norm (forward j (primeProduct Finset.univ p) n) / U)) (profile F) hsupport]
  let C := columns (X * Pcap / ProviderMarkedPools.norm j) j
  have hcolumns (c : Ideal (𝓞 K)) (hc : c ∈ C) : Squarefree c ∧ IsCoprime c j :=
    (Finset.mem_filter.mp hc).2
  calc
    _ = ProviderMarkedMask.value good u j *
        (∑ c ∈ C, ∑ p ∈ primeChoices lists c,
          (ProviderMarkedMask.value good u c * originalCoefficient χ a j p
            (backward j (primeProduct Finset.univ p) c)) *
            profile F (ProviderMarkedPools.norm j * ProviderMarkedPools.norm c /
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
          profile F (ProviderMarkedPools.norm j * ProviderMarkedPools.norm c /
            (ProviderMarkedPools.norm P * X)) *
          Expansion.Dyadic.annularProfile (ProviderMarkedPools.norm c / U))
      rw [show forward j P (backward j P c) = c from hf]
      calc
        _ = originalCoefficient χ a j p (backward j P c) *
            (ProviderMarkedMask.value good u (backward j P c) *
              ProviderMarkedMask.value good u (j * P)) *
            Expansion.Dyadic.annularProfile (ProviderMarkedPools.norm c / U) *
            profile F (ProviderMarkedPools.norm j * ProviderMarkedPools.norm c /
              (ProviderMarkedPools.norm P * X)) := by ring
        _ = _ := by rw [hm]; ring
    _ = _ := by
      rw [weighted_residual_source_eq_integral lists hdis a j hj χ
        (ProviderMarkedMask.value good u) C hcolumns F hF X U hX hU]
      ring


end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedLogMellin
