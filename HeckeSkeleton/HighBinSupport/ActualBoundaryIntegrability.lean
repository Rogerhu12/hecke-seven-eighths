import HeckeSkeleton.HighBinSupport.ActualBoundaryHolomorphy
import HeckeSkeleton.HighBinSupport.ActualAdditiveMellinRapidDecay
import HeckeSkeleton.HighBinSupport.ActualDenominatorMellin
import HeckeSkeleton.HighBinSupport.BoundaryBox
import Mathlib.MeasureTheory.Function.LocallyIntegrable
/-!
Finite-box integrability of the literal compensated physical kernel.

The only product regularity input is joint continuity of the actual marked
Euler correction on this finite box. All other continuity, nonvanishing,
Mellin-profile and compactness inputs are proved for the original factors.
This supplies the Bochner/Fubini premises of the verified rectangle theorem;
no contour estimate or high-bin conclusion occurs among its hypotheses.
-/

set_option autoImplicit false
noncomputable section
namespace HighBinBoundary.ActualIntegrability

open NumberField IsDedekindDomain MeasureTheory Set Complex
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators Topology ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S₀" => (S : Set (HeightOneSpectrum (𝓞 K)))

variable [MeasurableSpace (sLocalNormOneGroup K S₀)]
  [BorelSpace (sLocalNormOneGroup K S₀)]
variable [∀ p : S₀, MeasurableSpace (p.val.adicCompletion K)]
  [∀ p : S₀, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S₀) → Measure (p.val.adicCompletion K))
variable [∀ p : S₀, (μ p).IsAddHaarMeasure]

def heightBox (H : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  Icc (-H) H ×ˢ (Icc (-H) H ×ˢ Icc (-H) H)

def sLine (σ : ℝ) (q : ℝ × (ℝ × ℝ)) : ℂ := (σ : ℂ) + q.1 * I
def wLine (ν : ℝ) (q : ℝ × (ℝ × ℝ)) : ℂ := (ν : ℂ) + q.2.1 * I
def zLine (q : ℝ × (ℝ × ℝ)) : ℂ := (17 / 50 : ℂ) + q.2.2 * I

theorem continuous_sLine (σ : ℝ) : Continuous (sLine σ) :=
  continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul_const I)

theorem continuous_wLine (ν : ℝ) : Continuous (wLine ν) :=
  continuous_const.add
    ((Complex.continuous_ofReal.comp (continuous_fst.comp continuous_snd)).mul_const I)

theorem continuous_zLine : Continuous zLine :=
  continuous_const.add
    ((Complex.continuous_ofReal.comp (continuous_snd.comp continuous_snd)).mul_const I)

theorem heightBox_isCompact (H : ℝ) : IsCompact (heightBox H) :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

/-- All actual factors are continuous on the closed three-height box.
The zero detector is used for the denominator alone; finite-S deletion in
the numerator is permitted to vanish at zero or negative real part. -/
theorem compensatedRowMellinKernel_continuousOn_heightBox
    (P : ProbeData K S₀) (ψ : HeckeCharacter K) (E : RowEulerData K S₀ P)
    (g : PrimeWindowGeometry) (T Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ)
    (u : FrequencyRow K S₀)
    (hχ : ∀ t : ℝ, E.rows.character u ≠ heckeNormTwist K t)
    (hβ : ∀ t : ℝ, ψ * conjugate (E.rows.character u) ≠ heckeNormTwist K t)
    (H U α σ ν Z : ℝ) (hHU : H ≤ U) (hα : 1 / 2 ≤ α)
    (hσ : α < σ) (hZ : 0 < Z)
    (hbelow : rowZeroBelow K S₀ ψ Θ P E u U α)
    (hcorr : ∀ Q : Finset (ExteriorPrime K S₀),
      ContinuousOn (fun q => rowCorrection K S₀ P ψ E Q u
        (sLine σ q) (wLine ν q) (zLine q)) (heightBox H)) :
    ContinuousOn (fun q => compensatedRowMellinKernel K S₀ μ P ψ E g T u Z
      (sLine σ q) (wLine ν q) (zLine q)) (heightBox H) := by
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
    simpa [zLine] using hline.comp (continuous_snd.comp continuous_snd)
  have hdenMellin : Continuous (fun q : ℝ × (ℝ × ℝ) =>
      mellin P.denominator.toFun (wLine ν q)) :=
    (ActualDenominator.differentiable_mellin P.denominator).continuous.comp hw
  have hzeta : Continuous (fun q : ℝ × (ℝ × ℝ) =>
      heckeDeletedContinuation K 1 (exceptionalPrimes K S₀) (6 * zLine q)) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    have hre : 1 < (6 * zLine q).re := by norm_num [zLine, Complex.mul_re]
    have hL := (analyticAt_heckeContinuation K (1 : HeckeCharacter K) hre).differentiableAt
    have hD := (heckeEulerDeletionPolynomial_analyticAt
      K (1 : HeckeCharacter K) (exceptionalPrimes K S₀) (6 * zLine q)).differentiableAt
    exact (hD.mul hL).continuousAt.comp q (hz.const_mul 6).continuousAt
  have hnum : Continuous (fun q : ℝ × (ℝ × ℝ) =>
      heckeDeletedContinuation K (E.rows.character u) (exceptionalPrimes K S₀)
        (wLine ν q)) := by
    have hL := (differentiable_heckeContinuation_of_nonNorm K (E.rows.character u) hχ).continuous
    have hD : Continuous (heckeEulerDeletionPolynomial
        K (E.rows.character u) (exceptionalPrimes K S₀)) := by
      apply continuous_iff_continuousAt.mpr
      intro w
      exact (heckeEulerDeletionPolynomial_analyticAt
        K (E.rows.character u) (exceptionalPrimes K S₀) w).continuousAt
    exact (hD.mul hL).comp hw
  have hmem := denominator_mem_physicalRowFamily K S₀ ψ Θ P E u hΘ
  have hupper : HeckeSkeleton.HeckeBufferedReciprocal.ZeroUpperBound K
      (ψ * conjugate (E.rows.character u)) U α := hbelow _ hmem
  have hden : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      heckeDeletedContinuation K (ψ * conjugate (E.rows.character u))
        (exceptionalPrimes K S₀) (sLine σ q)) (heightBox H) := by
    intro q hq
    have hqi : |(sLine σ q).im| ≤ U := by
      have ht : |q.1| ≤ H := abs_le.mpr hq.1
      simpa only [sLine, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
        zero_add, add_zero] using ht.trans hHU
    have hd := (ActualHolomorphy.deleted_denominator_regular K S₀
      (ψ * conjugate (E.rows.character u)) hβ U α hα hupper (sLine σ q)
      (by simpa [sLine] using hσ) hqi).1
    exact (hd.continuousAt.comp q hs.continuousAt).continuousWithinAt
  have hn : ∀ q ∈ heightBox H,
      heckeDeletedContinuation K (ψ * conjugate (E.rows.character u))
        (exceptionalPrimes K S₀) (sLine σ q) ≠ 0 := by
    intro q hq
    have hqi : |(sLine σ q).im| ≤ U := by
      have ht : |q.1| ≤ H := abs_le.mpr hq.1
      simpa only [sLine, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
        zero_add, add_zero] using ht.trans hHU
    exact (ActualHolomorphy.deleted_denominator_regular K S₀
      (ψ * conjugate (E.rows.character u)) hβ U α hα hupper (sLine σ q)
      (by simpa [sLine] using hσ) hqi).2
  have hrow (Q : Finset (ExteriorPrime K S₀)) :
      ContinuousOn (fun q => rowEulerContinuation K S₀ P ψ E Q u
        (sLine σ q) (wLine ν q) (zLine q)) (heightBox H) :=
    ((hzeta.mul hnum).continuousOn.div hden hn).mul (hcorr Q)
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
      (mul_pos hZ hmark) _ ((hs.add hz).sub_const 1)
    have h3 := hpow (Z ^ (23 / 48 : ℝ) / exteriorNorm K S₀ (subsetPrimeIdeal K S₀ p J))
      (div_pos (Real.rpow_pos_of_pos hZ _) hsel) _ (hw.sub_const 1)
    exact (((h1.const_mul _).mul h2).mul h3).continuousOn.mul
      (hrow ((Finset.univ \ J).image p))
  exact (((((hs.add hz).sub_const 1).pow 2).cexp.mul hadd).mul hdenMellin).mul hfreq
    |>.continuousOn.mul hsum |>.div_const _

/-- Literal product-measure integrability needed by parameterBox/Fubini. -/
theorem compensatedRowMellinKernel_integrable_heightBox
    (P : ProbeData K S₀) (ψ : HeckeCharacter K) (E : RowEulerData K S₀ P)
    (g : PrimeWindowGeometry) (T Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ)
    (u : FrequencyRow K S₀)
    (hχ : ∀ t : ℝ, E.rows.character u ≠ heckeNormTwist K t)
    (hβ : ∀ t : ℝ, ψ * conjugate (E.rows.character u) ≠ heckeNormTwist K t)
    (H U α σ ν Z : ℝ) (hHU : H ≤ U) (hα : 1 / 2 ≤ α)
    (hσ : α < σ) (hZ : 0 < Z)
    (hbelow : rowZeroBelow K S₀ ψ Θ P E u U α)
    (hcorr : ∀ Q : Finset (ExteriorPrime K S₀),
      ContinuousOn (fun q => rowCorrection K S₀ P ψ E Q u
        (sLine σ q) (wLine ν q) (zLine q)) (heightBox H)) :
    Integrable (fun q : ℝ × (ℝ × ℝ) =>
      compensatedRowMellinKernel K S₀ μ P ψ E g T u Z
        (sLine σ q) (wLine ν q) (zLine q))
      ((volume.restrict (Icc (-H) H)).prod (twoHeightMeasure H)) := by
  have hc := compensatedRowMellinKernel_continuousOn_heightBox K S μ P ψ E g T Θ hΘ u
    hχ hβ H U α σ ν Z hHU hα hσ hZ hbelow hcorr
  have hi := hc.integrableOn_compact (heightBox_isCompact H) (μ := volume)
  simpa only [IntegrableOn, heightBox, twoHeightMeasure, Measure.prod_restrict] using hi

#print axioms compensatedRowMellinKernel_continuousOn_heightBox
#print axioms compensatedRowMellinKernel_integrable_heightBox

/-- Actual whole-character uniqueness supplies the finite fibers, so the
high-row integrability endpoint requires no separate norm-pole or fiber
assumption. One cutoff works for both the row and denominator background. -/
theorem eventually_compensatedRowMellinKernel_integrable_heightBox
    (P : ProbeData K S₀) (ψ : HeckeCharacter K) (E : RowEulerData K S₀ P)
    (g : PrimeWindowGeometry) (T Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → ∀ u : FrequencyRow K S₀,
      Z ^ d ≤ frequencyRowNorm K S₀ u →
      ∀ H U α σ ν : ℝ, H ≤ U → 1 / 2 ≤ α → α < σ →
      rowZeroBelow K S₀ ψ Θ P E u U α →
      (∀ Q : Finset (ExteriorPrime K S₀),
        ContinuousOn (fun q => rowCorrection K S₀ P ψ E Q u
          (sLine σ q) (wLine ν q) (zLine q)) (heightBox H)) →
      Integrable (fun q : ℝ × (ℝ × ℝ) =>
        compensatedRowMellinKernel K S₀ μ P ψ E g T u Z
          (sLine σ q) (wLine ν q) (zLine q))
        ((volume.restrict (Icc (-H) H)).prod (twoHeightMeasure H)) := by
  have hFib := HeckeSkeleton.ActualCanonicalRowConsumers.rowCharacter_fiber_finite K S₀ P E
  let v : InfinitePlace K := Classical.choice inferInstance
  obtain ⟨Z₀, hZ₀, hnon⟩ :=
    HeckeSkeleton.HighNormBackgroundExclusion.high_rows_exclude_background_norm_twists
      K S₀ P E.rows hFib v ({1, ψ} : Finset (HeckeCharacter K))
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZ d hd u hu H U α σ ν hHU hα hσ hbelow hcorr
  have hχ : ∀ t : ℝ, E.rows.character u ≠ heckeNormTwist K t := by
    simpa only [one_mul] using (hnon Z hZ d hd u hu 1 (by simp)).1
  have hβ := (hnon Z hZ d hd u hu ψ (by simp)).2
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one (hZ₀.trans hZ)
  exact compensatedRowMellinKernel_integrable_heightBox K S μ P ψ E g T Θ hΘ u
    hχ hβ H U α σ ν Z hHU hα hσ hZpos hbelow hcorr

#print axioms eventually_compensatedRowMellinKernel_integrable_heightBox

end HighBinBoundary.ActualIntegrability
