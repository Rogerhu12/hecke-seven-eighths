import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedReindex
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceAnnularTests

/-!
# The actual residual divisor mark after common Mellin separation

The inverse profile still has its original quotient argument
`N(j) N(c) / (N(P) X)`.  Genuine Mellin inversion separates the individual
surviving prime norms.  Their phases have modulus one and multiply their
original individual coefficients; summing the choices gives the actual
canonical divisor mark.  The column test is common to every prime tuple,
row, and extracted ideal on a fixed column annulus.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedMellin

open NumberField IsDedekindDomain UniqueFactorizationMonoid MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP AssignedMarkSource
open CommonKernel MellinSeparation
open ProviderMarkedOverlap ProviderMarkedSlots ProviderMarkedReindex
open scoped Classical BigOperators nonZeroDivisors Function

/-- The common column test on the actual smooth dyadic annulus. -/
def test (t : ℝ) : SchwartzMap ℝ ℂ :=
  SourceAnnularTests.testCLM (FinalMellinTests.weightedTest 0 t)

theorem test_apply (t x : ℝ) :
    test t x = Expansion.Dyadic.annularProfile x *
      FinalMellinTests.weightedTest 0 t x :=
  SchwartzMap.smulLeftCLM_apply_apply SourceAnnularTests.annulus.hasTemperateGrowth _ _

theorem test_support (t : ℝ) : tsupport (test t) ⊆ Set.Icc (1 / 2 : ℝ) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  apply Expansion.Dyadic.annularProfile_support
  intro hz
  exact hx (by rw [test_apply, hz, zero_mul])

theorem test_phase (t c U : ℝ) (hc : 0 < c) (hU : 0 < U) :
    columnPhase t (Real.log U) * test t (c / U) =
      Expansion.Dyadic.annularProfile (c / U) * columnPhase t (Real.log c) := by
  by_cases hz : Expansion.Dyadic.annularProfile (c / U) = 0
  · rw [test_apply, hz, zero_mul, mul_zero, zero_mul]
  · have hs := Expansion.Dyadic.annularProfile_support hz
    have h := FinalMellinTests.scaled_weighted_phase 0 t c U hc hU
      (by linarith [hs.1]) (by linarith [hs.2])
    simp only [Real.rpow_zero, Complex.ofReal_one, one_mul] at h
    rw [test_apply, h]
    ring

/-- One finite seminorm estimate is selected before the frequency,
the source, the overlap ideal, and the actual column annulus. -/
theorem test_polynomial_seminorm (q : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) (test t) ≤ C * (1 + |t|) ^ J := by
  let p : Seminorm ℝ (SchwartzMap ℝ ℂ) :=
    (q.sup (schwartzSeminormFamily ℝ ℝ ℂ)).comp SourceAnnularTests.testCLM.toLinearMap
  have hq : Continuous (fun F : SchwartzMap ℝ ℂ =>
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) F) :=
    Seminorm.continuous_finsetSup (fun i hi =>
      (schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm i)
  obtain ⟨v, A, hA, hmul⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ ℝ ℂ) p (hq.comp SourceAnnularTests.testCLM.continuous)
  obtain ⟨J, C, hC, htest⟩ := FinalMellinTests.finite_seminorm_polynomial_bound 0 v
  refine ⟨J, (A : ℝ) * C, by positivity, ?_⟩
  intro t
  have hm := Seminorm.le_def.mp hmul (FinalMellinTests.weightedTest 0 t)
  change q.sup (schwartzSeminormFamily ℝ ℝ ℂ) (test t) ≤
    (A : ℝ) * v.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (FinalMellinTests.weightedTest 0 t) at hm
  exact hm.trans ((mul_le_mul_of_nonneg_left (htest t) A.property).trans_eq (by ring))

theorem quotient_inverse (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (j c P X : ℝ) (hj : 0 < j) (hc : 0 < c) (hP : 0 < P) (hX : 0 < X) :
    W (j * c / (P * X)) =
      ∫ t : ℝ, density W hW t * columnPhase t (Real.log j) *
        columnPhase t (Real.log c) * columnPhase t (-Real.log P) *
          columnPhase t (-Real.log X) := by
  rw [mellin_inverse W hW _ (div_pos (mul_pos hj hc) (mul_pos hP hX))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    rw [Real.log_div (mul_ne_zero hj.ne' hc.ne') (mul_ne_zero hP.ne' hX.ne'),
      Real.log_mul hj.ne' hc.ne', Real.log_mul hP.ne' hX.ne']
    rw [show Real.log j + Real.log c - (Real.log P + Real.log X) =
      ((Real.log j + Real.log c) + -Real.log P) + -Real.log X by ring]
    simp only [MellinWeightedTests.columnPhase_add]
    ring

theorem quotient_integrable (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (j c P X : ℝ) :
    Integrable (fun t : ℝ => density W hW t * columnPhase t (Real.log j) *
      columnPhase t (Real.log c) * columnPhase t (-Real.log P) *
        columnPhase t (-Real.log X)) := by
  apply (density W hW).integrable.norm.mono'
    (((((density W hW).continuous.mul (continuous_columnPhase _)).mul
      (continuous_columnPhase _)).mul (continuous_columnPhase _)).mul
        (continuous_columnPhase _) |>.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun t => by
    simp only [norm_mul, norm_columnPhase, mul_one]
    exact le_rfl

/-- The same actual column annulus is used for every residual tuple;
the inverse profile is separated without replacing its argument. -/
theorem quotient_annular_inverse (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (j c P X U : ℝ) (hj : 0 < j) (hc : 0 < c) (hP : 0 < P)
    (hX : 0 < X) (hU : 0 < U) :
    W (j * c / (P * X)) * Expansion.Dyadic.annularProfile (c / U) =
      ∫ t : ℝ, density W hW t * columnPhase t (Real.log j) *
        columnPhase t (-Real.log X) * columnPhase t (Real.log U) *
          columnPhase t (-Real.log P) * test t (c / U) := by
  rw [quotient_inverse W hW j c P X hj hc hP hX, ← integral_mul_const]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    have hs := test_phase t c U hc hU
    calc
      _ = density W hW t * columnPhase t (Real.log j) *
          columnPhase t (-Real.log X) * columnPhase t (-Real.log P) *
            (Expansion.Dyadic.annularProfile (c / U) * columnPhase t (Real.log c)) := by ring
      _ = _ := by rw [← hs]; ring

theorem quotient_annular_integrable (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (j c P X U : ℝ) (hc : 0 < c) (hU : 0 < U) :
    Integrable (fun t : ℝ => density W hW t * columnPhase t (Real.log j) *
      columnPhase t (-Real.log X) * columnPhase t (Real.log U) *
        columnPhase t (-Real.log P) * test t (c / U)) := by
  apply ((quotient_integrable W hW j c P X).mul_const
    (Expansion.Dyadic.annularProfile (c / U))).congr
  exact Filter.Eventually.of_forall fun t => by
    have hs := test_phase t c U hc hU
    calc
      _ = density W hW t * columnPhase t (Real.log j) *
          columnPhase t (-Real.log X) * columnPhase t (-Real.log P) *
            (Expansion.Dyadic.annularProfile (c / U) * columnPhase t (Real.log c)) := by ring
      _ = _ := by rw [← hs]; ring

/-- Genuine finite Fubini, including the dependent residual prime
choices for each new column. -/
theorem finite_quotient_inverse {α β : Type*} (C : Finset α) (P : α → Finset β)
    (cNorm : α → ℝ) (pNorm : β → ℝ) (w : α → β → ℂ)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (j X U : ℝ) (hj : 0 < j) (hX : 0 < X) (hU : 0 < U)
    (hc : ∀ c ∈ C, 0 < cNorm c) (hp : ∀ c ∈ C, ∀ p ∈ P c, 0 < pNorm p) :
    (∑ c ∈ C, ∑ p ∈ P c,
      w c p * W (j * cNorm c / (pNorm p * X)) *
        Expansion.Dyadic.annularProfile (cNorm c / U)) =
      ∫ t : ℝ, density W hW t * columnPhase t (Real.log j) *
        columnPhase t (-Real.log X) * columnPhase t (Real.log U) *
          ∑ c ∈ C, ∑ p ∈ P c,
            w c p * columnPhase t (-Real.log (pNorm p)) * test t (cNorm c / U) := by
  let F : α → β → ℝ → ℂ := fun c p t => w c p *
    (density W hW t * columnPhase t (Real.log j) *
      columnPhase t (-Real.log X) * columnPhase t (Real.log U) *
        columnPhase t (-Real.log (pNorm p)) * test t (cNorm c / U))
  have hF (c : α) (hcC : c ∈ C) (p : β) : Integrable (F c p) :=
    (quotient_annular_integrable W hW j (cNorm c) (pNorm p) X U
      (hc c hcC) hU).const_mul _
  calc
    _ = ∑ c ∈ C, ∑ p ∈ P c, ∫ t : ℝ, F c p t := by
      apply Finset.sum_congr rfl
      intro c hcC
      apply Finset.sum_congr rfl
      intro p hpP
      rw [mul_assoc, quotient_annular_inverse W hW j (cNorm c) (pNorm p) X U
        hj (hc c hcC) (hp c hcC p hpP) hX hU, integral_const_mul]
    _ = ∫ t : ℝ, ∑ c ∈ C, ∑ p ∈ P c, F c p t := by
      symm
      rw [integral_finsetSum C (fun c hcC =>
        integrable_finsetSum (P c) (fun p hpP => hF c hcC p))]
      apply Finset.sum_congr rfl
      intro c hcC
      exact integral_finsetSum (P c) (fun p hpP => hF c hcC p)
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c hcC
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hpP
        dsimp only [F]
        ring

variable {K : Type} [Field K] [NumberField K] {J : ℕ}

theorem phase_sum {ι : Type*} (I : Finset ι) (x : ι → ℝ) (t : ℝ) :
    columnPhase t (∑ i ∈ I, x i) = ∏ i ∈ I, columnPhase t (x i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [columnPhase]
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi,
      MellinWeightedTests.columnPhase_add, ih]

theorem product_norm_phase (p : Fin J → HeightOneSpectrum (𝓞 K)) (t : ℝ) :
    columnPhase t (-Real.log (ProviderMarkedPools.norm (primeProduct Finset.univ p))) =
      ∏ i, columnPhase t (-Real.log (ProviderMarkedPools.norm (p i).asIdeal)) := by
  have hN (i : Fin J) : 0 < ProviderMarkedPools.norm (p i).asIdeal :=
    ProviderMarkedPools.norm_pos (p i).ne_bot
  simp only [ProviderMarkedPools.norm, primeProduct, map_prod, Nat.cast_prod]
  rw [Real.log_prod (fun i hi => (hN i).ne'), ← Finset.sum_neg_distrib, phase_sum]

def primeWeight (a : Fin J → Ideal (𝓞 K) → ℂ) (t : ℝ)
    (i : Fin J) (P : Ideal (𝓞 K)) : ℂ :=
  -(a i P * columnPhase t (-Real.log (ProviderMarkedPools.norm P)))

theorem primeWeight_norm_le (a : Fin J → Ideal (𝓞 K) → ℂ) (t : ℝ)
    (i : Fin J) (P : Ideal (𝓞 K)) (ha : ‖a i P‖ ≤ 1) :
    ‖primeWeight a t i P‖ ≤ 1 := by
  simpa only [primeWeight, norm_neg, norm_mul, norm_columnPhase, mul_one] using ha

/-- Every surviving original prime keeps its own coefficient. The
only changes are the exact Mobius sign and its unit Mellin phase. -/
theorem twisted_choices_eq_mark
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists)) (a : Fin J → Ideal (𝓞 K) → ℂ)
    (t : ℝ) (c : Ideal (𝓞 K)) :
    (∑ p ∈ primeChoices lists c,
      (moebius (primeProduct Finset.univ p) : ℂ) * choiceWeight a p *
        columnPhase t (-Real.log (ProviderMarkedPools.norm (primeProduct Finset.univ p)))) =
      divisorMark Finset.univ (fun i => (lists i).image HeightOneSpectrum.asIdeal)
        (primeWeight a t) c := by
  rw [← signed_choices_eq_divisorMark lists hdis
    (fun i P => a i P * columnPhase t (-Real.log (ProviderMarkedPools.norm P))) c]
  apply Finset.sum_congr rfl
  intro p hp
  rw [product_norm_phase, choiceWeight, choiceWeight, Finset.prod_mul_distrib]
  ring

def originalCoefficient (χ : HeckeCharacter K) (a : Fin J → Ideal (𝓞 K) → ℂ)
    (j : Ideal (𝓞 K)) (p : Fin J → HeightOneSpectrum (𝓞 K))
    (n : Ideal (𝓞 K)) : ℂ :=
  (moebius n : ℂ) * idealCoefficient (primeCoefficient K χ) n *
    idealCoefficient (primeCoefficient K χ) (j * primeProduct Finset.univ p) *
      choiceWeight a p

def extractedScalar (χ : HeckeCharacter K) (j : Ideal (𝓞 K)) : ℂ :=
  (moebius j : ℂ) * idealCoefficient (primeCoefficient K χ) j ^ 2

def canonicalColumn (χ : HeckeCharacter K)
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (a : Fin J → Ideal (𝓞 K) → ℂ) (C : Finset (Ideal (𝓞 K)))
    (U t : ℝ) : ℂ :=
  ∑ c ∈ C, (moebius c : ℂ) * idealCoefficient (primeCoefficient K χ) c *
    divisorMark Finset.univ (fun i => (lists i).image HeightOneSpectrum.asIdeal)
      (primeWeight a t) c * test t (ProviderMarkedPools.norm c / U)

theorem original_twisted_choices
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists)) (a : Fin J → Ideal (𝓞 K) → ℂ)
    (j c : Ideal (𝓞 K)) (hj : Squarefree j) (hc : Squarefree c)
    (hcj : IsCoprime c j) (χ : HeckeCharacter K) (t : ℝ) :
    (∑ p ∈ primeChoices lists c,
      originalCoefficient χ a j p (backward j (primeProduct Finset.univ p) c) *
        columnPhase t (-Real.log (ProviderMarkedPools.norm (primeProduct Finset.univ p)))) =
      extractedScalar χ j * (moebius c : ℂ) * idealCoefficient (primeCoefficient K χ) c *
        divisorMark Finset.univ (fun i => (lists i).image HeightOneSpectrum.asIdeal)
          (primeWeight a t) c := by
  let b : Fin J → Ideal (𝓞 K) → ℂ := fun i P =>
    a i P * columnPhase t (-Real.log (ProviderMarkedPools.norm P))
  calc
    _ = ∑ p ∈ primeChoices lists c,
        (moebius (backward j (primeProduct Finset.univ p) c) : ℂ) *
          idealCoefficient (primeCoefficient K χ)
            (backward j (primeProduct Finset.univ p) c) *
          idealCoefficient (primeCoefficient K χ) (j * primeProduct Finset.univ p) *
          choiceWeight b p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [originalCoefficient, product_norm_phase]
      dsimp only [choiceWeight, b]
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := original_choices_eq_canonical_mark lists hdis b j c hj hc hcj χ

/-- Every term still has its original inverse coefficient and original
prime-slot coefficient. The output is a common integral of the actual
canonical squarefree column with the residual product-form mark. -/
theorem residual_source_eq_canonical_integral
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists)) (a : Fin J → Ideal (𝓞 K) → ℂ)
    (j : Ideal (𝓞 K)) (hj : Squarefree j) (χ : HeckeCharacter K)
    (C : Finset (Ideal (𝓞 K)))
    (hc : ∀ c ∈ C, Squarefree c ∧ IsCoprime c j)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (X U : ℝ) (hX : 0 < X) (hU : 0 < U) :
    (∑ c ∈ C, ∑ p ∈ primeChoices lists c,
      originalCoefficient χ a j p (backward j (primeProduct Finset.univ p) c) *
        W (ProviderMarkedPools.norm j * ProviderMarkedPools.norm c /
          (ProviderMarkedPools.norm (primeProduct Finset.univ p) * X)) *
        Expansion.Dyadic.annularProfile (ProviderMarkedPools.norm c / U)) =
      extractedScalar χ j *
        ∫ t : ℝ, density W hW t * columnPhase t (Real.log (ProviderMarkedPools.norm j)) *
          columnPhase t (-Real.log X) * columnPhase t (Real.log U) *
            canonicalColumn χ lists a C U t := by
  have hnormc (c : Ideal (𝓞 K)) (hcC : c ∈ C) : 0 < ProviderMarkedPools.norm c :=
    ProviderMarkedPools.norm_pos (hc c hcC).1.ne_zero
  have hnormp (c : Ideal (𝓞 K)) (hcC : c ∈ C)
      (p : Fin J → HeightOneSpectrum (𝓞 K)) (hp : p ∈ primeChoices lists c) :
      0 < ProviderMarkedPools.norm (primeProduct Finset.univ p) :=
    ProviderMarkedPools.norm_pos (primeProduct_squarefree Finset.univ p
      (fun _ _ _ _ heq => primeChoices_injective lists hdis c p hp heq)).ne_zero
  rw [finite_quotient_inverse C (primeChoices lists) ProviderMarkedPools.norm
    (fun p => ProviderMarkedPools.norm (primeProduct Finset.univ p))
    (fun c p => originalCoefficient χ a j p (backward j (primeProduct Finset.univ p) c))
    W hW (ProviderMarkedPools.norm j) X U (ProviderMarkedPools.norm_pos hj.ne_zero)
    hX hU hnormc hnormp, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    have hsum :
        (∑ c ∈ C, ∑ p ∈ primeChoices lists c,
          originalCoefficient χ a j p (backward j (primeProduct Finset.univ p) c) *
            columnPhase t (-Real.log (ProviderMarkedPools.norm (primeProduct Finset.univ p))) *
            test t (ProviderMarkedPools.norm c / U)) =
          extractedScalar χ j * canonicalColumn χ lists a C U t := by
      rw [canonicalColumn, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hcC
      rw [← Finset.sum_mul, original_twisted_choices lists hdis a j c hj
        (hc c hcC).1 (hc c hcC).2 χ t]
      ring
    rw [hsum]
    ring

/-- Full fixed-overlap bridge starting on the actual original inverse
norm envelope.  The only inserted factor is the displayed smooth
annulus of the actual changed column.  The output is the literal
canonical residual mark and a common finite-seminorm test family. -/
theorem fixed_selected_annular_eq_canonical_integral
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists)) (a : Fin J → Ideal (𝓞 K) → ℂ)
    (j : Ideal (𝓞 K)) (hj : Squarefree j)
    (hcop : ∀ p ∈ tuples lists, IsCoprime j (primeProduct Finset.univ p))
    (χ : HeckeCharacter K) (X U Pcap : ℝ) (hX : 0 < X) (hU : 0 < U)
    (hPcap : ∀ p ∈ tuples lists,
      ProviderMarkedPools.norm (primeProduct Finset.univ p) ≤ Pcap)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) :
    (∑ p ∈ tuples lists, ∑ n ∈ ProviderMarkedPools.sourcePool X j (primeProduct Finset.univ p),
      originalCoefficient χ a j p n *
        Expansion.Dyadic.annularProfile
          (ProviderMarkedPools.norm (forward j (primeProduct Finset.univ p) n) / U) *
        W (ProviderMarkedPools.norm n / X)) =
      extractedScalar χ j *
        ∫ t : ℝ, density W hW t * columnPhase t (Real.log (ProviderMarkedPools.norm j)) *
          columnPhase t (-Real.log X) * columnPhase t (Real.log U) *
            canonicalColumn χ lists a
              (columns (X * Pcap / ProviderMarkedPools.norm j) j) U t := by
  have hsupport : Function.support W ⊆ Set.Iic 2 := by
    intro x hx
    exact (hW (subset_closure hx)).2
  rw [fixed_selected_reindex lists hdis j hj hcop X Pcap hX hPcap
    (fun p n => originalCoefficient χ a j p n *
      Expansion.Dyadic.annularProfile
        (ProviderMarkedPools.norm (forward j (primeProduct Finset.univ p) n) / U)) W hsupport]
  have hcolumns (c : Ideal (𝓞 K))
      (hc : c ∈ columns (X * Pcap / ProviderMarkedPools.norm j) j) :
      Squarefree c ∧ IsCoprime c j := (Finset.mem_filter.mp hc).2
  calc
    _ = ∑ c ∈ columns (X * Pcap / ProviderMarkedPools.norm j) j,
        ∑ p ∈ primeChoices lists c,
          originalCoefficient χ a j p (backward j (primeProduct Finset.univ p) c) *
            W (ProviderMarkedPools.norm j * ProviderMarkedPools.norm c /
              (ProviderMarkedPools.norm (primeProduct Finset.univ p) * X)) *
            Expansion.Dyadic.annularProfile (ProviderMarkedPools.norm c / U) := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro p hp
      have hPc := primeChoices_product_dvd lists hdis c p hp
      have hf := forward_backward j (primeProduct Finset.univ p) hj.ne_zero
        (⟨c, (hcolumns c hc).1, hPc, (hcolumns c hc).2⟩ :
          Target j (primeProduct Finset.univ p))
      rw [hf]
      ring
    _ = _ := residual_source_eq_canonical_integral lists hdis a j hj χ _ hcolumns
      W hW X U hX hU

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedMellin
