import HeckeSkeleton.HighBinSupport.ActualBoundaryEstimate
import HeckeGeneral.Analysis.HeckeNormPole
import HeckeGeneral.Analysis.HeckeFunctionalEquation

/-!
# Integrability of the actual final contour at every positive scale

The numerator line has real part below one and hence misses every norm
pole. For a norm-character denominator, the chosen continuation retains
the literal formula `Q(s)/(s-p)`. Its reciprocal is `(s-p)/Q(s)`, including
at the pole. The genuine simple-pole theorem and entire uniqueness prove
`Q(p) ≠ 0`; the original upper-zero detector excludes all other zeros
on the retained contour. Thus the actual reciprocal is analytic there.

The resulting compact-box integrability uses no high-row cutoff, row
norm bound, prime-normalizer estimate or norm-form conclusion.
-/

set_option autoImplicit false
noncomputable section

namespace HighBinBoundary.ActualFinalIntegrability

open NumberField IsDedekindDomain MeasureTheory Set Complex Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HeckeBufferedReciprocal
open ActualIntegrability
open scoped Classical BigOperators Topology ComplexConjugate

variable (K : Type) [Field K] [NumberField K]

/-- All actual unitary Hecke continuations are analytic off the line
containing their only possible norm pole. -/
theorem analyticAt_heckeContinuation_re_ne_one (χ : HeckeCharacter K)
    (s : ℂ) (hs : s.re ≠ 1) : AnalyticAt ℂ (heckeContinuation K χ) s := by
  by_cases hχ : ∃ t : ℝ, χ = heckeNormTwist K t
  · obtain ⟨t, _, ha⟩ := heckeContinuation_normBranch_analyticAwayPole K χ hχ
    apply ha s
    intro h
    apply hs
    simpa only [heckeNormPole, Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero] using congrArg Complex.re h
  · exact (differentiable_heckeContinuation_of_nonNorm K χ
      (fun t ht => hχ ⟨t, ht⟩)).analyticAt s

/-- The numerator retained by the chosen norm branch is the genuine
nonvanishing pole-cleared numerator, by uniqueness of entire functions. -/
private theorem normBranch_numerator_ne_zero
    (χ : HeckeCharacter K) (t : ℝ) (Q : ℂ → ℂ)
    (ht : χ = heckeNormTwist K t) (hQ : Differentiable ℂ Q)
    (hL : heckeContinuation K χ = fun s => Q s / (s - heckeNormPole t)) :
    Q (heckeNormPole t) ≠ 0 := by
  obtain ⟨Q₀, hQ₀, hQ₀ne, hQ₀eq⟩ := exists_nonzero_poleCleared_normTwist K t
  have hsame : Q = Q₀ := entire_eq_of_eq_rightHalfPlane Q Q₀ hQ hQ₀ (by
    intro s hs
    have hLs := heckeContinuation_eq_series K χ hs
    rw [hL, ht] at hLs
    rw [hQ₀eq s hs]
    simpa only [mul_comm] using (div_eq_iff (sub_heckeNormPole_ne_zero hs t)).mp hLs)
  rw [hsame]
  exact hQ₀ne

/-- The actual reciprocal extends analytically through a norm pole.
No non-norm assumption is needed above the actual zero detector. -/
theorem analyticAt_hecke_reciprocal_of_upper
    (χ : HeckeCharacter K) (H α : ℝ) (hα : 1 / 2 ≤ α)
    (hupper : ZeroUpperBound K χ H α)
    (s : ℂ) (hs : α < s.re) (hheight : |s.im| ≤ H) :
    AnalyticAt ℂ (fun z => (heckeContinuation K χ z)⁻¹) s := by
  by_cases hχ : ∃ t : ℝ, χ = heckeNormTwist K t
  · obtain ⟨t, Q, ht, hQ, hL⟩ := heckeContinuation_normBranch K χ hχ
    have hQp := normBranch_numerator_ne_zero K χ t Q ht hQ hL
    have hQs : Q s ≠ 0 := by
      by_cases hsp : s = heckeNormPole t
      · simpa only [hsp] using hQp
      intro hzero
      have hLzero : heckeContinuation K χ s = 0 := by simp only [hL, hzero, zero_div]
      by_cases hright : 1 < s.re
      · exact heckeContinuation_ne_zero K χ hright hLzero
      have ha : AnalyticAt ℂ (heckeContinuation K χ) s := by
        rw [hL]
        exact (hQ.analyticAt s).div (analyticAt_id.sub analyticAt_const)
          (sub_ne_zero.mpr hsp)
      have hlim : Tendsto (heckeContinuation K χ) (𝓝[≠] s) (𝓝 0) := by
        simpa only [hLzero] using ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have horder : 0 < meromorphicOrderAt (heckeContinuation K χ) s :=
        (tendsto_zero_iff_meromorphicOrderAt_pos ha.meromorphicAt).mp hlim
      exact (not_le_of_gt hs) (hupper s horder (hα.trans hs.le)
        (le_of_not_gt hright) hheight)
    rw [hL]
    simpa only [inv_div] using
      ((analyticAt_id.sub analyticAt_const).div (hQ.analyticAt s) hQs)
  · have hn : ∀ t : ℝ, χ ≠ heckeNormTwist K t := fun t ht => hχ ⟨t, ht⟩
    exact ((differentiable_heckeContinuation_of_nonNorm K χ hn).analyticAt s).inv
      (continuation_ne_zero_of_upper K χ hn H α hα hupper s hs hheight)

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Finite Euler deletion introduces no zero in this positive-real-part
region, so it preserves the analyticity of the actual reciprocal. -/
theorem analyticAt_deleted_reciprocal_of_upper
    (χ : HeckeCharacter K) (H α : ℝ) (hα : 1 / 2 ≤ α)
    (hupper : ZeroUpperBound K χ H α)
    (s : ℂ) (hs : α < s.re) (hheight : |s.im| ≤ H) :
    AnalyticAt ℂ (fun z =>
      (heckeDeletedContinuation K χ (exceptionalPrimes K S) z)⁻¹) s := by
  have hp := (heckeEulerDeletionPolynomial_analyticAt K χ
    (exceptionalPrimes K S) s).inv
      (heckeEulerDeletionPolynomial_ne_zero K χ (exceptionalPrimes K S) (by linarith))
  have hL := analyticAt_hecke_reciprocal_of_upper K χ H α hα hupper s hs hheight
  simpa only [heckeDeletedContinuation, mul_inv] using hp.mul hL

end HighBinBoundary.ActualFinalIntegrability

namespace HighBinBoundary.ActualFinalIntegrability

open NumberField IsDedekindDomain MeasureTheory Set Complex
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HeckeBufferedReciprocal
open ActualIntegrability
open scoped Classical BigOperators Topology ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S₀" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [MeasurableSpace (sLocalNormOneGroup K S₀)] [BorelSpace (sLocalNormOneGroup K S₀)]
variable [∀ p : S₀, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S₀, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S₀) → Measure (p.val.adicCompletion K))
variable [∀ p : S₀, (μ p).IsAddHaarMeasure]

/-- Continuity of the literal final kernel for every positive scale.
The numerator line avoids all norm poles; the denominator's reciprocal
extends through its norm pole. No background-row exclusion is required. -/
theorem compensatedRowMellinKernel_continuousOn_final_heightBox
    (P : ProbeData K S₀) (ψ : HeckeCharacter K) (g : PrimeWindowGeometry)
    (T Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ) (u : FrequencyRow K S₀)
    (Z a e H U : ℝ) (hZ : 0 < Z) (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1)
    (he : 0 < e) (he1 : e ≤ 1 / 10000) (hHU : H ≤ U)
    (hbelow : rowZeroBelow K S₀ ψ Θ P (arithmeticHighEulerData K S₀ P ψ)
      u U (a + 2 * e)) :
    ContinuousOn (fun q => compensatedRowMellinKernel K S₀ μ P ψ
      (arithmeticHighEulerData K S₀ P ψ) g T u Z
      (sLine (a + 16 * e) q) (wLine (1 - a - 6 * e) q) (zLine q)) (heightBox H) := by
  let E := arithmeticHighEulerData K S₀ P ψ
  let α := a + 2 * e
  let σ := a + 16 * e
  let ν := 1 - a - 6 * e
  have hα : 1 / 2 ≤ α := by dsimp [α]; linarith
  have hσ : α < σ := by dsimp [α, σ]; linarith
  have hν : ν < 1 := by dsimp [ν]; linarith
  have hcorr (Q : Finset (ExteriorPrime K S₀)) :
      ContinuousOn (fun q => rowCorrection K S₀ P ψ E Q u
        (sLine σ q) (wLine ν q) (zLine q)) (heightBox H) :=
    ActualEstimate.correction_continuousOn_heightBox K S₀ P ψ Q u a e H σ
      ha ha1 he he1 le_rfl
  letI : IsTotallyComplex K :=
    ⟨HeckeSkeleton.HeckeFiniteBackgroundControl.all_complex_of_primitive12
      K P.arithmetic.primitive12⟩
  have hs := continuous_sLine σ
  have hw := continuous_wLine ν
  have hz := continuous_zLine
  have hadd : Continuous (fun q : ℝ × (ℝ × ℝ) =>
      additiveMellin K S₀ μ P.additive (zLine q)) := by
    have hline := ActualAdditiveBorel.additiveMellin_continuous_line_actualBorel K S
      (fun p => inferInstance) (fun p => inferInstance) μ (fun p => inferInstance)
      P.additive (17 / 50) (by norm_num) (by norm_num)
    simpa [zLine, Function.comp_def] using hline.comp (continuous_snd.comp continuous_snd)
  have hdenMellin : Continuous (fun q : ℝ × (ℝ × ℝ) =>
      mellin P.denominator.toFun (wLine ν q)) :=
    (ActualDenominator.differentiable_mellin P.denominator.toSmoothAnnularTest).continuous.comp hw
  have hzeta : Continuous (fun q : ℝ × (ℝ × ℝ) =>
      heckeDeletedContinuation K 1 (exceptionalPrimes K S₀) (6 * zLine q)) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    have hre : 1 < (6 * zLine q).re := by norm_num [zLine, Complex.mul_re]
    have hL := (analyticAt_heckeContinuation K (1 : HeckeCharacter K) hre).differentiableAt
    have hD := (heckeEulerDeletionPolynomial_analyticAt
      K (1 : HeckeCharacter K) (exceptionalPrimes K S₀) (6 * zLine q)).differentiableAt
    exact (hD.mul hL).continuousAt.comp (hz.const_mul 6).continuousAt
  have hnum : Continuous (fun q : ℝ × (ℝ × ℝ) =>
      heckeDeletedContinuation K (E.rows.character u) (exceptionalPrimes K S₀)
        (wLine ν q)) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    have hne : (wLine ν q).re ≠ 1 := by
      simpa only [wLine, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        sub_zero, add_zero] using ne_of_lt hν
    have hL := (analyticAt_heckeContinuation_re_ne_one K (E.rows.character u)
      (wLine ν q) hne).differentiableAt
    have hD := (heckeEulerDeletionPolynomial_analyticAt K (E.rows.character u)
      (exceptionalPrimes K S₀) (wLine ν q)).differentiableAt
    exact (hD.mul hL).continuousAt.comp hw.continuousAt
  have hmem := HeckeSkeleton.HeckeBufferedReciprocal.denominator_mem_physicalRowFamily K S₀ ψ Θ P E u hΘ
  have hupper : HeckeSkeleton.HeckeBufferedReciprocal.ZeroUpperBound K
      (ψ * conjugate (E.rows.character u)) U α := hbelow _ hmem
  have hrecip : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      (heckeDeletedContinuation K (ψ * conjugate (E.rows.character u))
        (exceptionalPrimes K S₀) (sLine σ q))⁻¹) (heightBox H) := by
    intro q hq
    have hqi : |(sLine σ q).im| ≤ U := by
      have ht : |q.1| ≤ H := abs_le.mpr hq.1
      simpa only [sLine, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
        zero_add, add_zero] using ht.trans hHU
    have hi := analyticAt_deleted_reciprocal_of_upper K S₀
      (ψ * conjugate (E.rows.character u)) U α hα hupper
      (sLine σ q) (by simpa [sLine] using hσ) hqi
    exact (hi.differentiableAt.continuousAt.comp hs.continuousAt).continuousWithinAt
  have hrow (Q : Finset (ExteriorPrime K S₀)) :
      ContinuousOn (fun q => rowEulerContinuation K S₀ P ψ E Q u
        (sLine σ q) (wLine ν q) (zLine q)) (heightBox H) := by
    simpa only [rowEulerContinuation, div_eq_mul_inv] using
      (((hzeta.mul hnum).continuousOn.mul hrecip).mul (hcorr Q))
  have hpow (b : ℝ) (hb : 0 < b) (f : ℝ × (ℝ × ℝ) → ℂ)
      (hf : Continuous f) : Continuous (fun q => (b : ℂ) ^ f q) :=
    hf.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hb.ne'))
  have hfreq : Continuous (fun q : ℝ × (ℝ × ℝ) =>
      (frequencyRowNorm K S₀ u : ℂ) ^ (-zLine q)) :=
    hpow _ (idealNorm_pos K u.ideal.val) _ hz.neg
  have hsum : ContinuousOn
      (fun q : ℝ × (ℝ × ℝ) =>
        ∑ p ∈ Fintype.piFinset (fun i => primeWindow K S₀ g T Z i),
          (∏ i : Fin g.slots, windowWeight K S₀ g Z i (p i)) *
          ∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
            let selected := subsetPrimeIdeal K S₀ p J
            let marked := subsetPrimeIdeal K S₀ p (Finset.univ \ J)
            (-1 : ℂ) ^ J.card * (exteriorNorm K S₀ selected : ℂ) ^ (-(3 / 2 : ℂ)) *
              conj (heckeIdealCoefficient K ψ marked.val) *
              ((Z ^ (17 / 48 : ℝ) / exteriorNorm K S₀ selected : ℝ) : ℂ) ^ (1 / 2 - zLine q) *
              ((Z * exteriorNorm K S₀ marked : ℝ) : ℂ) ^ (sLine σ q + zLine q - 1) *
              ((Z ^ (23 / 48 : ℝ) / exteriorNorm K S₀ selected : ℝ) : ℂ) ^ (wLine ν q - 1) *
              rowEulerContinuation K S₀ P ψ E ((Finset.univ \ J).image p) u
                (sLine σ q) (wLine ν q) (zLine q)) (heightBox H) := by
    apply continuousOn_finsetSum
    intro p _
    apply ContinuousOn.const_mul
    apply continuousOn_finsetSum
    intro J _
    dsimp only
    have hsel : 0 < exteriorNorm K S₀ (subsetPrimeIdeal K S₀ p J) :=
      idealNorm_pos K _
    have hmark : 0 < exteriorNorm K S₀ (subsetPrimeIdeal K S₀ p (Finset.univ \ J)) :=
      idealNorm_pos K _
    have h1 := hpow (Z ^ (17 / 48 : ℝ) / exteriorNorm K S₀ (subsetPrimeIdeal K S₀ p J))
      (div_pos (Real.rpow_pos_of_pos hZ _) hsel) _ (continuous_const.sub hz)
    have h2 := hpow (Z * exteriorNorm K S₀ (subsetPrimeIdeal K S₀ p (Finset.univ \ J)))
      (mul_pos hZ hmark) _ ((hs.add hz).sub (continuous_const (y := (1 : ℂ))))
    have h3 := hpow (Z ^ (23 / 48 : ℝ) / exteriorNorm K S₀ (subsetPrimeIdeal K S₀ p J))
      (div_pos (Real.rpow_pos_of_pos hZ _) hsel) _ (hw.sub (continuous_const (y := (1 : ℂ))))
    exact (((h1.const_mul _).mul h2).mul h3).continuousOn.mul
      (hrow ((Finset.univ \ J).image p))
  exact (((((hs.add hz).sub (continuous_const (y := (1 : ℂ)))).pow 2).cexp.mul hadd).mul hdenMellin).mul hfreq
    |>.continuousOn.mul hsum |>.const_mul (physicalPoissonScalar K : ℂ) |>.div_const _

/-- Compact-box integrability of the final arithmetic kernel, with no
large-scale cutoff or row-norm premise. -/
theorem compensatedRowMellinKernel_integrableOn_final_heightBox
    (P : ProbeData K S₀) (ψ : HeckeCharacter K) (g : PrimeWindowGeometry)
    (T Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ) (u : FrequencyRow K S₀)
    (Z a e H U : ℝ) (hZ : 0 < Z) (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1)
    (he : 0 < e) (he1 : e ≤ 1 / 10000) (hHU : H ≤ U)
    (hbelow : rowZeroBelow K S₀ ψ Θ P (arithmeticHighEulerData K S₀ P ψ)
      u U (a + 2 * e)) :
    IntegrableOn (fun q => compensatedRowMellinKernel K S₀ μ P ψ
      (arithmeticHighEulerData K S₀ P ψ) g T u Z
      (sLine (a + 16 * e) q) (wLine (1 - a - 6 * e) q) (zLine q)) (heightBox H) :=
  (compensatedRowMellinKernel_continuousOn_final_heightBox K S μ P ψ g T Θ hΘ u
    Z a e H U hZ ha ha1 he he1 hHU hbelow).integrableOn_compact (heightBox_isCompact H)

end HighBinBoundary.ActualFinalIntegrability

#print axioms HighBinBoundary.ActualFinalIntegrability.analyticAt_hecke_reciprocal_of_upper
#print axioms HighBinBoundary.ActualFinalIntegrability.compensatedRowMellinKernel_integrableOn_final_heightBox
