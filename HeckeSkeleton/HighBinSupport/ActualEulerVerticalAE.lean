import HeckeSkeleton.HighBinSupport.ActualEulerUniqueness
import HeckeSkeleton.HighBinSupport.ActualEulerRegularNonvanishing
import HeckeSkeleton.HighBinSupport.EntireQuotientVerticalAE

/-!
# Calibrated finite tables on vertical contours

The original initial-series calibration identifies the finite exceptional
product after the common, nonzero regular product is cancelled in the
initial domain. That finite product is a quotient of entire functions.
Its equality therefore continues almost everywhere on every vertical
real parameter space, including negative real parts of the w-coordinate.

All exceptional zero factors and identically-zero denominators remain in
the literal finite product. No equality of provider records is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinEulerUniqueness

open NumberField IsDedekindDomain Set Filter MeasureTheory Complex
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinContinuation
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def finiteExceptionalProduct (P : ProbeData K S) (E : RowEulerData K S P)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (v : ℂ × ℂ × ℂ) : ℂ :=
  ∏ p : rowExceptionalPrimes K S Q u,
    finiteEulerRationalValue (E.exceptionalFactor Q u p)
      (p.val.val.asIdeal.absNorm : ℝ) v.1 v.2.1 v.2.2

def finiteExceptionalNumerator (P : ProbeData K S) (E : RowEulerData K S P)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (v : ℂ × ℂ × ℂ) : ℂ :=
  ∏ p : rowExceptionalPrimes K S Q u,
    finiteEulerPolynomialValue (E.exceptionalFactor Q u p).numerator
      (p.val.val.asIdeal.absNorm : ℝ) v.1 v.2.1 v.2.2

def finiteExceptionalDenominator (P : ProbeData K S) (E : RowEulerData K S P)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (v : ℂ × ℂ × ℂ) : ℂ :=
  ∏ p : rowExceptionalPrimes K S Q u,
    finiteEulerPolynomialValue (E.exceptionalFactor Q u p).denominator
      (p.val.val.asIdeal.absNorm : ℝ) v.1 v.2.1 v.2.2

theorem finiteExceptionalProduct_eq_div (P : ProbeData K S) (E : RowEulerData K S P)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (v : ℂ × ℂ × ℂ) :
    finiteExceptionalProduct K S P E Q u v =
      finiteExceptionalNumerator K S P E Q u v /
        finiteExceptionalDenominator K S P E Q u v := by
  simp only [finiteExceptionalProduct, finiteExceptionalNumerator,
    finiteExceptionalDenominator, finiteEulerRationalValue, Finset.prod_div_distrib]

theorem finiteExceptionalNumerator_entire (P : ProbeData K S) (E : RowEulerData K S P)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) :
    AnalyticOnNhd ℂ (finiteExceptionalNumerator K S P E Q u) univ := by
  intro v _
  unfold finiteExceptionalNumerator
  apply Finset.analyticAt_fun_prod
  intro p _
  have hq : (0 : ℝ) < p.val.val.asIdeal.absNorm :=
    lt_of_lt_of_le (by norm_num) (exteriorPrime_norm_two_le K S p.val)
  exact finiteEulerPolynomialValue_entire _ hq v (mem_univ _)

theorem finiteExceptionalDenominator_entire (P : ProbeData K S) (E : RowEulerData K S P)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) :
    AnalyticOnNhd ℂ (finiteExceptionalDenominator K S P E Q u) univ := by
  intro v _
  unfold finiteExceptionalDenominator
  apply Finset.analyticAt_fun_prod
  intro p _
  have hq : (0 : ℝ) < p.val.val.asIdeal.absNorm :=
    lt_of_lt_of_le (by norm_num) (exteriorPrime_norm_two_le K S p.val)
  exact finiteEulerPolynomialValue_entire _ hq v (mem_univ _)

/-- Only the common regular part needs a convergence hypothesis in this
finite/infinite product identity. Finite exceptional zero factors are
never divided out. -/
theorem rowCorrection_eq_finiteExceptional_mul_regular
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E : RowEulerData K S P)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (v : ℂ × ℂ × ℂ)
    (hregular : Multipliable (fun p : {p : ExteriorPrime K S //
      p ∉ rowExceptionalPrimes K S Q u} =>
        localRowCorrection K S P ψ (E.rows.character u) p.val v.1 v.2.1 v.2.2)) :
    rowCorrection K S P ψ E Q u v.1 v.2.1 v.2.2 =
      finiteExceptionalProduct K S P E Q u v *
        ∏' p : {p : ExteriorPrime K S // p ∉ rowExceptionalPrimes K S Q u},
          localRowCorrection K S P ψ (E.rows.character u) p.val v.1 v.2.1 v.2.2 := by
  let F := rowExceptionalPrimes K S Q u
  let f : ExteriorPrime K S → ℂ := fun p =>
    if hp : p ∈ F then finiteEulerRationalValue (E.exceptionalFactor Q u ⟨p, hp⟩)
      (p.val.asIdeal.absNorm : ℝ) v.1 v.2.1 v.2.2
    else localRowCorrection K S P ψ (E.rows.character u) p v.1 v.2.1 v.2.2
  have hfin : Multipliable (f ∘ (↑) : (F : Set (ExteriorPrime K S)) → ℂ) :=
    Multipliable.of_finite
  have htail : Multipliable (f ∘ (↑) : (F : Set (ExteriorPrime K S))ᶜ → ℂ) := by
    apply hregular.congr
    intro p
    simp only [Function.comp_def, f, dif_neg p.property]
  have hprod := hfin.tprod_mul_tprod_compl htail
  have hfinval : (∏' p : (F : Set (ExteriorPrime K S)), f p.val) =
      finiteExceptionalProduct K S P E Q u v := by
    rw [tprod_fintype]
    apply Finset.prod_congr rfl
    intro p _
    simp only [f, dif_pos p.property]
  have htailval : (∏' p : (F : Set (ExteriorPrime K S))ᶜ, f p.val) =
      ∏' p : {p : ExteriorPrime K S // p ∉ rowExceptionalPrimes K S Q u},
        localRowCorrection K S P ψ (E.rows.character u) p.val v.1 v.2.1 v.2.2 := by
    apply tprod_congr
    intro p
    simp only [f, dif_neg p.property]
  rw [hfinval, htailval] at hprod
  exact hprod.symm

private theorem regular_compl_multipliable_initial
    (P : ProbeData K S) (ψ χ : HeckeCharacter K)
    (F : Finset (ExteriorPrime K S)) (s w z : ℂ)
    (hs : 4 < s.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    Multipliable (fun p : {p : ExteriorPrime K S // p ∉ F} =>
      localRowCorrection K S P ψ χ p.val s w z) := by
  have hnorm := (summable_localRowCorrection_norm_initial K S P ψ χ s w z hs hw hz).subtype
    (fun p : ExteriorPrime K S => p ∉ F)
  exact (multipliable_one_add_of_summable hnorm).congr fun p => by ring

/-- Cancelling the actual nonzero regular product on the initial domain
identifies the complete finite exceptional products of any two calibrated
providers. Neither provider's finite product is assumed nonzero. -/
theorem finiteExceptionalProduct_eq_initial_of_calibrated
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E₁ E₂ : RowEulerData K S P)
    (h₁ : RowEulerCalibrationInput K S P ψ E₁)
    (h₂ : RowEulerCalibrationInput K S P ψ E₂)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (s w z : ℂ) (hs : 4 < s.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    finiteExceptionalProduct K S P E₁ Q u (s, w, z) =
      finiteExceptionalProduct K S P E₂ Q u (s, w, z) := by
  have hchar := rowCharacterInput_character_unique K S P E₁.rows E₂.rows u
  have hm₁ := regular_compl_multipliable_initial K S P ψ (E₁.rows.character u)
    (rowExceptionalPrimes K S Q u) s w z hs hw hz
  have hm₂ := regular_compl_multipliable_initial K S P ψ (E₂.rows.character u)
    (rowExceptionalPrimes K S Q u) s w z hs hw hz
  have heq := rowCorrection_eq_initial_of_calibrated K S P ψ E₁ E₂ h₁ h₂ Q u s w z hs hw hz
  rw [rowCorrection_eq_finiteExceptional_mul_regular K S P ψ E₁ Q u (s, w, z) hm₁,
    rowCorrection_eq_finiteExceptional_mul_regular K S P ψ E₂ Q u (s, w, z) hm₂,
    hchar] at heq
  exact mul_right_cancel₀
    (localRowCorrection_tprod_compl_ne_zero_initial K S P ψ (E₂.rows.character u)
      (rowExceptionalPrimes K S Q u) s w z hs hw hz) heq

/-- The original calibration, with all possible zeros retained, determines
the finite exceptional product almost everywhere on every vertical box. -/
theorem finiteExceptionalProduct_ae_eq_vertical_of_calibrated
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E₁ E₂ : RowEulerData K S P)
    (h₁ : RowEulerCalibrationInput K S P ψ E₁)
    (h₂ : RowEulerCalibrationInput K S P ψ E₂)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (σ : ℝ × ℝ × ℝ) :
    ∀ᵐ t : ℝ × (ℝ × ℝ),
      finiteExceptionalProduct K S P E₁ Q u
        ((σ.1 : ℂ) + (t.1 : ℂ) * I,
          (σ.2.1 : ℂ) + (t.2.1 : ℂ) * I,
          (σ.2.2 : ℂ) + (t.2.2 : ℂ) * I) =
      finiteExceptionalProduct K S P E₂ Q u
        ((σ.1 : ℂ) + (t.1 : ℂ) * I,
          (σ.2.1 : ℂ) + (t.2.1 : ℂ) * I,
          (σ.2.2 : ℂ) + (t.2.2 : ℂ) * I) := by
  let U : Set (ℂ × ℂ × ℂ) := {v | 4 < v.1.re ∧ 4 < v.2.1.re ∧ 2 < v.2.2.re}
  have hU : IsOpen U := by
    apply IsOpen.inter
    · exact isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)
    · exact (isOpen_lt continuous_const
        (Complex.continuous_re.comp (continuous_fst.comp continuous_snd))).inter
        (isOpen_lt continuous_const
          (Complex.continuous_re.comp (continuous_snd.comp continuous_snd)))
  have hUne : U.Nonempty := ⟨(5, 5, 5), by norm_num [U]⟩
  have hdiv : EqOn
      (fun v => finiteExceptionalNumerator K S P E₁ Q u v /
        finiteExceptionalDenominator K S P E₁ Q u v)
      (fun v => finiteExceptionalNumerator K S P E₂ Q u v /
        finiteExceptionalDenominator K S P E₂ Q u v) U := by
    intro v hv
    rw [← finiteExceptionalProduct_eq_div, ← finiteExceptionalProduct_eq_div]
    exact finiteExceptionalProduct_eq_initial_of_calibrated K S P ψ E₁ E₂
      h₁ h₂ Q u v.1 v.2.1 v.2.2 hv.1 hv.2.1 hv.2.2
  have h := entire_quotients_ae_eq_vertical
    (finiteExceptionalNumerator_entire K S P E₁ Q u)
    (finiteExceptionalDenominator_entire K S P E₁ Q u)
    (finiteExceptionalNumerator_entire K S P E₂ Q u)
    (finiteExceptionalDenominator_entire K S P E₂ Q u) hU hUne hdiv σ
  simpa only [← finiteExceptionalProduct_eq_div] using h

private theorem regular_compl_multipliable_sweptTube
    (P : ProbeData K S) (ψ χ : HeckeCharacter K)
    (F : Finset (ExteriorPrime K S)) {a e : ℝ}
    (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (v : ℂ × ℂ × ℂ) (hv : v ∈ sweptTube a e) :
    Multipliable (fun p : {p : ExteriorPrime K S // p ∉ F} =>
      localRowCorrection K S P ψ χ p.val v.1 v.2.1 v.2.2) := by
  have hmajor := (summable_exteriorPrime_swept_error K S he).mul_left
    (11 / sweptTubeEulerMargin)
  have hnorm : Summable (fun p : ExteriorPrime K S =>
      ‖localRowCorrection K S P ψ χ p v.1 v.2.1 v.2.2 - 1‖) :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) fun p =>
      localRowCorrection_sweptTube_bound K S P ψ χ p ha ha1 he.le he1 v hv
  have htail := hnorm.subtype (fun p : ExteriorPrime K S => p ∉ F)
  exact (multipliable_one_add_of_summable htail).congr fun p => by ring

/-- The actual correction products agree almost everywhere on every
vertical real space whose fixed real parts lie in the high-bin tube.
This includes the negative w-lines, without assuming analytic extension
of an arbitrary provider at its removable exceptional denominator zeros. -/
theorem rowCorrection_ae_eq_vertical_of_calibrated
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E₁ E₂ : RowEulerData K S P)
    (h₁ : RowEulerCalibrationInput K S P ψ E₁)
    (h₂ : RowEulerCalibrationInput K S P ψ E₂)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (σ : ℝ × ℝ × ℝ)
    (hσ : ((σ.1 : ℂ), (σ.2.1 : ℂ), (σ.2.2 : ℂ)) ∈ sweptTube a e) :
    ∀ᵐ t : ℝ × (ℝ × ℝ),
      rowCorrection K S P ψ E₁ Q u
        ((σ.1 : ℂ) + (t.1 : ℂ) * I) ((σ.2.1 : ℂ) + (t.2.1 : ℂ) * I)
        ((σ.2.2 : ℂ) + (t.2.2 : ℂ) * I) =
      rowCorrection K S P ψ E₂ Q u
        ((σ.1 : ℂ) + (t.1 : ℂ) * I) ((σ.2.1 : ℂ) + (t.2.1 : ℂ) * I)
        ((σ.2.2 : ℂ) + (t.2.2 : ℂ) * I) := by
  have hchar := rowCharacterInput_character_unique K S P E₁.rows E₂.rows u
  filter_upwards [finiteExceptionalProduct_ae_eq_vertical_of_calibrated
    K S P ψ E₁ E₂ h₁ h₂ Q u σ] with t ht
  let v : ℂ × ℂ × ℂ :=
    ((σ.1 : ℂ) + (t.1 : ℂ) * I, (σ.2.1 : ℂ) + (t.2.1 : ℂ) * I,
      (σ.2.2 : ℂ) + (t.2.2 : ℂ) * I)
  have hv : v ∈ sweptTube a e := by
    simpa [v, sweptTube, Complex.mul_re] using hσ
  have hm₁ := regular_compl_multipliable_sweptTube K S P ψ (E₁.rows.character u)
    (rowExceptionalPrimes K S Q u) ha ha1 he he1 v hv
  have hm₂ := regular_compl_multipliable_sweptTube K S P ψ (E₂.rows.character u)
    (rowExceptionalPrimes K S Q u) ha ha1 he he1 v hv
  change rowCorrection K S P ψ E₁ Q u v.1 v.2.1 v.2.2 =
    rowCorrection K S P ψ E₂ Q u v.1 v.2.1 v.2.2
  rw [rowCorrection_eq_finiteExceptional_mul_regular K S P ψ E₁ Q u v hm₁,
    rowCorrection_eq_finiteExceptional_mul_regular K S P ψ E₂ Q u v hm₂,
    ht, hchar]

theorem rowEulerContinuation_ae_eq_vertical_of_calibrated
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E₁ E₂ : RowEulerData K S P)
    (h₁ : RowEulerCalibrationInput K S P ψ E₁)
    (h₂ : RowEulerCalibrationInput K S P ψ E₂)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (σ : ℝ × ℝ × ℝ)
    (hσ : ((σ.1 : ℂ), (σ.2.1 : ℂ), (σ.2.2 : ℂ)) ∈ sweptTube a e) :
    ∀ᵐ t : ℝ × (ℝ × ℝ),
      rowEulerContinuation K S P ψ E₁ Q u
        ((σ.1 : ℂ) + (t.1 : ℂ) * I) ((σ.2.1 : ℂ) + (t.2.1 : ℂ) * I)
        ((σ.2.2 : ℂ) + (t.2.2 : ℂ) * I) =
      rowEulerContinuation K S P ψ E₂ Q u
        ((σ.1 : ℂ) + (t.1 : ℂ) * I) ((σ.2.1 : ℂ) + (t.2.1 : ℂ) * I)
        ((σ.2.2 : ℂ) + (t.2.2 : ℂ) * I) := by
  have hchar := rowCharacterInput_character_unique K S P E₁.rows E₂.rows u
  filter_upwards [rowCorrection_ae_eq_vertical_of_calibrated
    K S P ψ E₁ E₂ h₁ h₂ Q u ha ha1 he he1 σ hσ] with t ht
  simp only [rowEulerContinuation, hchar, ht]

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S) → Measure (p.val.adicCompletion K))
variable [∀ p : S, (μ p).IsAddHaarMeasure]

/-- Finite slot and subset sums preserve the almost-everywhere identity.
Every mark set appearing in the original compensated kernel is included. -/
theorem compensatedRowMellinKernel_ae_eq_vertical_of_calibrated
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E₁ E₂ : RowEulerData K S P)
    (h₁ : RowEulerCalibrationInput K S P ψ E₁)
    (h₂ : RowEulerCalibrationInput K S P ψ E₂)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z : ℝ)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (σ : ℝ × ℝ × ℝ)
    (hσ : ((σ.1 : ℂ), (σ.2.1 : ℂ), (σ.2.2 : ℂ)) ∈ sweptTube a e) :
    ∀ᵐ t : ℝ × (ℝ × ℝ),
      compensatedRowMellinKernel K S μ P ψ E₁ g T u Z
        ((σ.1 : ℂ) + (t.1 : ℂ) * I) ((σ.2.1 : ℂ) + (t.2.1 : ℂ) * I)
        ((σ.2.2 : ℂ) + (t.2.2 : ℂ) * I) =
      compensatedRowMellinKernel K S μ P ψ E₂ g T u Z
        ((σ.1 : ℂ) + (t.1 : ℂ) * I) ((σ.2.1 : ℂ) + (t.2.1 : ℂ) * I)
        ((σ.2.2 : ℂ) + (t.2.2 : ℂ) * I) := by
  have hcont : ∀ᵐ t : ℝ × (ℝ × ℝ),
      ∀ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
        ∀ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
          rowEulerContinuation K S P ψ E₁ ((Finset.univ \ J).image p) u
            ((σ.1 : ℂ) + (t.1 : ℂ) * I) ((σ.2.1 : ℂ) + (t.2.1 : ℂ) * I)
            ((σ.2.2 : ℂ) + (t.2.2 : ℂ) * I) =
          rowEulerContinuation K S P ψ E₂ ((Finset.univ \ J).image p) u
            ((σ.1 : ℂ) + (t.1 : ℂ) * I) ((σ.2.1 : ℂ) + (t.2.1 : ℂ) * I)
            ((σ.2.2 : ℂ) + (t.2.2 : ℂ) * I) := by
    apply (Filter.eventually_all_finset _).mpr
    intro p _
    apply (Filter.eventually_all_finset _).mpr
    intro J _
    exact rowEulerContinuation_ae_eq_vertical_of_calibrated
      K S P ψ E₁ E₂ h₁ h₂ ((Finset.univ \ J).image p) u ha ha1 he he1 σ hσ
  filter_upwards [hcont] with t ht
  unfold compensatedRowMellinKernel
  congr 3
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  rw [ht p hp J hJ]

/-- The literal three nested integrals, including `(2π)^(-3)`, agree.
Almost-everywhere product equality suffices: no integrability premise is
added for the arbitrary finite-table provider. -/
theorem rowContourBox_eq_of_calibrated_sweptTube
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E₁ E₂ : RowEulerData K S P)
    (h₁ : RowEulerCalibrationInput K S P ψ E₁)
    (h₂ : RowEulerCalibrationInput K S P ψ E₂)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z height σ ν zLine : ℝ)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hσ : ((σ : ℂ), (ν : ℂ), (zLine : ℂ)) ∈ sweptTube a e) :
    rowContourBox K S μ P ψ E₁ g T u Z height σ ν zLine =
      rowContourBox K S μ P ψ E₂ g T u Z height σ ν zLine := by
  have h := compensatedRowMellinKernel_ae_eq_vertical_of_calibrated
    K S μ P ψ E₁ E₂ h₁ h₂ g T u Z ha ha1 he he1 (σ, ν, zLine) hσ
  unfold rowContourBox
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (s := Icc (-height) height)
    (Measure.ae_ae_of_ae_prod h)] with ts hts
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (s := Icc (-height) height)
    (Measure.ae_ae_of_ae_prod hts)] with tw htw
  exact integral_congr_ae (ae_restrict_of_ae htw)

#print axioms finiteExceptionalProduct_eq_div
#print axioms finiteExceptionalProduct_eq_initial_of_calibrated
#print axioms finiteExceptionalProduct_ae_eq_vertical_of_calibrated
#print axioms rowCorrection_ae_eq_vertical_of_calibrated
#print axioms compensatedRowMellinKernel_ae_eq_vertical_of_calibrated
#print axioms rowContourBox_eq_of_calibrated_sweptTube

end HeckeSkeleton.HighBinEulerUniqueness
