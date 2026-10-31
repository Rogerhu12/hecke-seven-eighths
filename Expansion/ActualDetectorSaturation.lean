import HeckeGeneral.Analysis.ExpansionCutoffPolynomials
import HeckeGeneral.Analysis.ExpansionScaleBounds
import HeckeGeneral.Analysis.ExpansionPolynomialSupport
import Expansion.NormalizedContourBudget

/-!
# Actual normalized detector bounds from buffered zero control

The estimates below apply the existing finite-height Mellin theorems to the
literal deleted ideal coefficients, then normalize the same polynomials
used by the shared witness recipe. The hypotheses contain zero control,
fixed infinity type, conductor/norm bounds and height geometry. No
polynomial upper estimate or saturation statement is assumed.

The ordinary reflected main term keeps its sharp conductor exponent; the
coarse rectangle exponent occurs only in a negligible horizontal term.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.ActualDetectorSaturation

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ExpansionBufferedPolynomials
open HeckeGeneral.Analysis.ExpansionReflectedPolynomials
open HeckeGeneral.Analysis.ExpansionDeletedControl
open HeckeGeneral.Analysis.ExpansionScaleBounds
open HeckeSkeleton.HeckeBufferedReciprocal HeckeSkeleton.HeckeConductorNorm
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open ExpansionInterfaces.Mellin ExpansionDetector.Fourier ExpansionDetector.PowerBudget
open Expansion.NormalizedContourBudget
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]

/-- The same constant works for inverse and ordinary coefficients, all
cutoff ratios, all rows and all lengths. Only physical zero control is
required in the retained rectangle. -/
theorem exists_actual_normalized_buffered_scale_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε)
    (W : AnnularProfile) (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (R θ τ : ℝ) (hR : 1 ≤ R) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (reciprocal : Bool) (χ : HeckeCharacter K)
      (I : Ideal (𝓞 K)) (E : Finset (HeightOneSpectrum (𝓞 K)))
      (U a H Hupper r β ν ratio : ℝ),
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = arch → heckeArchWeight K χ = weight →
      I ≠ 0 → (∀ p ∈ E, p.asIdeal ∣ I) →
      1 ≤ U → 1 / 2 ≤ a → a ≤ 1 → 0 ≤ r → 0 ≤ ratio →
      1 / 2 ≤ β → β ≤ 1 →
      (Ideal.absNorm I : ℝ) ≤ R * U → heckeConductorScale K χ ≤ R * U →
      2 + Hupper ≤ R * U ^ θ → U ^ τ ≤ H →
      |ν| + H + 3 / 2 ≤ Hupper → ZeroUpperBound K χ Hupper (a + 2 * e) →
      ∀ S : Finset (NonzeroIdeal K),
      (∀ J, idealNorm K J ≤ W.upper * U ^ r → J ∈ S) →
      let b := 2 * ε + heightDegree K * ε * θ
      ‖normalizedPolynomial S (deletedAnnularCoefficient K reciprocal χ E)
        (idealNorm K) (W.cutoffFamily V hV ratio).function (U ^ r) β ν‖ ≤
          C * (U ^ ((a - 1 / 2 + 6 * e) * r + b) +
            U ^ (3 / 2 * r + b - τ * N) + U ^ (3 / 2 * r - τ * N)) := by
  obtain ⟨Cbase, hCbase, hbound⟩ :=
    exists_actual_buffered_cutoff_annular_upper K hcomplex arch weight he he' hε
  let A := bufferedScaleConstant Cbase R ε (heightDegree K)
  let CW := W.cutoffContourConstant V hV hone hzero (-2) 2 N
  have hRzero : 0 ≤ R := zero_le_one.trans hR
  have hA : 0 ≤ A := by unfold A bufferedScaleConstant; positivity
  have hCW : 0 ≤ CW := (W.cutoffContourConstant_spec V hV hone hzero (-2) 2 N).1
  let C := (1 / (2 * Real.pi)) * CW * (A + 6 * A + initialMass K)
  have hC : 0 ≤ C := by
    have hm := initialMass_nonneg K
    unfold C
    positivity
  refine ⟨C, hC, ?_⟩
  intro reciprocal χ I E U a H Hupper r β ν ratio hχ harch hweight hI hE
    hU ha ha' hr hratio hβ hβ' hnorm hconductor hheight hHlower hpadding hupper S hS
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hH : 0 < H := (Real.rpow_pos_of_pos hUpos τ).trans_le hHlower
  have hHU : 0 ≤ Hupper := by linarith [abs_nonneg ν]
  let B := bufferedCost K χ I Cbase ε Hupper
  have hB : 0 ≤ B := by
    have hQ := conductorScale_pos K χ
    unfold B bufferedCost
    positivity
  have hscale : B ≤ A * U ^ (2 * ε + heightDegree K * ε * θ) :=
    bufferedCost_le_scale K χ I Cbase R ε U θ Hupper hCbase.le hRzero hε.le
      hUpos hHU hnorm hconductor hheight
  have hraw := hbound reciprocal W V hV hone hzero N ratio hratio χ I E
    a H Hupper (U ^ r) (centralShift β ν) hχ harch hweight hI hE ha ha' hH
    (by simpa only [centralShift_im, abs_neg] using hpadding) hupper
    (Real.one_le_rpow hU hr) (by simpa using hβ) (by simpa using hβ') S hS
  dsimp only at hraw ⊢
  rw [actual_normalized_norm_eq_annular K reciprocal χ E (W.cutoffFamily V hV ratio)
    S (U ^ r) β ν (by positivity)]
  have hnormalized := mul_le_mul_of_nonneg_left hraw
    (Real.rpow_nonneg (Real.rpow_nonneg hUpos.le r) (β - 1 / 2))
  have hbudget := contourMajorant_le_scale
    (U := U) (H := H) (τ := τ) (r := r) (bL := 2 * ε + heightDegree K * ε * θ)
    (bR := 2 * ε + heightDegree K * ε * θ) (BL := B) (BR := B) (A := A) (B := A)
    (mass := initialMass K) (CW := CW) (width := 2 - a - 6 * e)
    (β := β) (σ := a + 6 * e) (N := N)
    hU hB hB hA hA (initialMass_nonneg K) hCW
    (by linarith) (by linarith) hscale hscale hHlower
  have hraw' :
      (U ^ r) ^ (β - 1 / 2) *
        ‖∑ J ∈ S, smoothedTerm (W.cutoffFamily V hV ratio)
          (deletedAnnularCoefficient K reciprocal χ E) (idealNorm K)
          (centralShift β ν) (U ^ r) J‖ ≤
      (U ^ r) ^ (β - 1 / 2) *
        contourMajorant B B (initialMass K) CW (2 - a - 6 * e)
          (U ^ r) β (a + 6 * e) H N := by
    simpa only [centralShift_re, contourMajorant, B, CW] using hnormalized
  convert hraw'.trans hbudget using 1 <;> dsimp only [C] <;> congr 2 <;> ring

/-- The plain polynomial also has the reflected exponent. Its constant is
chosen before the abscissa, so the gain remains uniform over buffered bins. -/
theorem exists_actual_normalized_reflected_scale_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε)
    (W : AnnularProfile) (R θ τ : ℝ) (hR : 1 ≤ R) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χ : HeckeCharacter K)
      (I : Ideal (𝓞 K)) (E : Finset (HeightOneSpectrum (𝓞 K)))
      (U a H Hupper r β ν : ℝ),
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = arch → heckeArchWeight K χ = weight →
      I ≠ 0 → (∀ p ∈ E, p.asIdeal ∣ I) →
      1 ≤ U → 1 / 2 ≤ a → a ≤ 1 → 0 ≤ r → 1 / 2 ≤ β → β ≤ 1 →
      (Ideal.absNorm I : ℝ) ≤ R * U → heckeConductorScale K χ ≤ R * U →
      2 + Hupper ≤ R * U ^ θ → U ^ τ ≤ H →
      |ν| + H + 3 / 2 ≤ Hupper → ZeroUpperBound K χ Hupper (a + 2 * e) →
      ∀ S : Finset (NonzeroIdeal K),
      (∀ J, idealNorm K J ≤ W.upper * U ^ r → J ∈ S) →
      ‖normalizedPolynomial S (deletedAnnularCoefficient K false χ E)
        (idealNorm K) W.function (U ^ r) β ν‖ ≤
          C * (U ^ ((a - 1 / 2) * (1 - r) + 12 * e - 6 * e * r + 2 * ε +
              heightDegree K * θ * (1 + ε)) +
            U ^ (3 / 2 * r + (3 / 4 + ε + heightDegree K * θ) - τ * N) +
            U ^ (3 / 2 * r - τ * N)) := by
  obtain ⟨CL, CR, hCL, hCR, hbound⟩ :=
    exists_actual_reflected_annular_upper K hcomplex arch weight he he' hε
  let A := reflectedScaleConstant CL R e ε (heightDegree K)
  let B := coarseScaleConstant CR R ε (heightDegree K)
  let CW := W.contourConstant (-2) 2 N
  have hRzero : 0 ≤ R := zero_le_one.trans hR
  have hA : 0 ≤ A := by unfold A reflectedScaleConstant; positivity
  have hB : 0 ≤ B := by unfold B coarseScaleConstant; positivity
  have hCW : 0 ≤ CW := (W.contourConstant_spec (-2) 2 N).1
  let C := (1 / (2 * Real.pi)) * CW * (A + 6 * B + initialMass K)
  have hC : 0 ≤ C := by
    have hm := initialMass_nonneg K
    unfold C
    positivity
  refine ⟨C, hC, ?_⟩
  intro χ I E U a H Hupper r β ν hχ harch hweight hI hE hU ha ha' hr hβ hβ'
    hnorm hconductor hheight hHlower hpadding hupper S hS
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hH : 0 < H := (Real.rpow_pos_of_pos hUpos τ).trans_le hHlower
  have hHU : 0 ≤ Hupper := by linarith [abs_nonneg ν]
  let BL := reflectedCost K χ I CL e ε a Hupper
  let BR := coarseRectangleCost K χ I CR ε Hupper
  have hBL : 0 ≤ BL := by
    have hQ := conductorScale_pos K χ
    unfold BL reflectedCost
    positivity
  have hBR : 0 ≤ BR := by
    have hQ := conductorScale_pos K χ
    unfold BR coarseRectangleCost
    positivity
  have hscaleL : BL ≤ A * U ^
      (a - 1 / 2 + 12 * e + 2 * ε + heightDegree K * θ * (1 + ε)) :=
    reflectedCost_le_scale K χ I CL R e ε U θ a Hupper hCL.le hR he.le
      (by linarith) hε.le hUpos hHU hnorm hconductor hheight ha ha'
  have hscaleR : BR ≤ B * U ^ (3 / 4 + ε + heightDegree K * θ) :=
    coarseRectangleCost_le_scale K χ I CR R ε U θ Hupper hCR.le hRzero hε.le
      hUpos hHU hnorm hconductor hheight
  have hraw := hbound W N χ I E a H Hupper (U ^ r) (centralShift β ν)
    hχ harch hweight hI hE ha ha' hH
    (by simpa only [centralShift_im, abs_neg] using hpadding) hupper
    (Real.one_le_rpow hU hr) (by simpa using hβ) (by simpa using hβ') S hS
  dsimp only at hraw ⊢
  rw [actual_normalized_norm_eq_annular K false χ E W S (U ^ r) β ν (by positivity)]
  have hnormalized := mul_le_mul_of_nonneg_left hraw
    (Real.rpow_nonneg (Real.rpow_nonneg hUpos.le r) (β - 1 / 2))
  have hbudget := contourMajorant_le_scale
    (U := U) (H := H) (τ := τ) (r := r)
    (bL := a - 1 / 2 + 12 * e + 2 * ε + heightDegree K * θ * (1 + ε))
    (bR := 3 / 4 + ε + heightDegree K * θ) (BL := BL) (BR := BR) (A := A) (B := B)
    (mass := initialMass K) (CW := CW) (width := 1 + a + 6 * e)
    (β := β) (σ := 1 - a - 6 * e) (N := N)
    hU hBL hBR hA hB (initialMass_nonneg K) hCW
    (by linarith) (by linarith) hscaleL hscaleR hHlower
  have hraw' :
      (U ^ r) ^ (β - 1 / 2) *
        ‖∑ J ∈ S, smoothedTerm W (deletedAnnularCoefficient K false χ E)
          (idealNorm K) (centralShift β ν) (U ^ r) J‖ ≤
      (U ^ r) ^ (β - 1 / 2) *
        contourMajorant BL BR (initialMass K) CW (1 + a + 6 * e)
          (U ^ r) β (1 - a - 6 * e) H N := by
    simpa only [centralShift_re, contourMajorant, BL, BR, CW] using hnormalized
  convert hraw'.trans hbudget using 1 <;> dsimp only [C] <;> congr 2 <;> ring

/-- Uniform squared bounds for the actual inverse and plain detector
polynomials. The displayed small-loss conditions are purely numerical;
the polynomial estimates are derived from the actual zero upper bound.
The plain factor retains the minimum of its forward and reflected powers.

The common cutoff precedes every row, zero real part, frequency, cutoff
ratio and dyadic length. No separate thresholds are selected per row. -/
theorem exists_actual_normalized_square_bounds
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε)
    (W : AnnularProfile) (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (R θ τ η : ℝ) (hR : 1 ≤ R) (hθ : 0 ≤ θ) (hτ : 0 < τ) (hη : 0 < η)
    (hforward : 132 * e + 2 * ε + heightDegree K * ε * θ ≤ η / 4)
    (hreflected : 12 * e + 2 * ε + heightDegree K * θ * (1 + ε) ≤ η / 4) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ (χ : HeckeCharacter K)
      (I : Ideal (𝓞 K)) (E : Finset (HeightOneSpectrum (𝓞 K)))
      (U a H Hupper r β ν ratio : ℝ),
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = arch → heckeArchWeight K χ = weight →
      I ≠ 0 → (∀ p ∈ E, p.asIdeal ∣ I) →
      U₀ ≤ U → 1 / 2 ≤ a → a ≤ 1 → 0 ≤ r → r ≤ 22 → 0 ≤ ratio →
      1 / 2 ≤ β → β ≤ 1 →
      (Ideal.absNorm I : ℝ) ≤ R * U → heckeConductorScale K χ ≤ R * U →
      2 + Hupper ≤ R * U ^ θ → U ^ τ ≤ H →
      |ν| + H + 3 / 2 ≤ Hupper → ZeroUpperBound K χ Hupper (a + 2 * e) →
      ∀ S : Finset (NonzeroIdeal K),
      (∀ J, idealNorm K J ≤ W.upper * U ^ r → J ∈ S) →
      ‖normalizedPolynomial S (deletedAnnularCoefficient K true χ E)
        (idealNorm K) (W.cutoffFamily V hV ratio).function (U ^ r) β ν‖ ^ 2 ≤
          U ^ ((2 * a - 1) * r + η) ∧
      ‖normalizedPolynomial S (deletedAnnularCoefficient K false χ E)
        (idealNorm K) W.function (U ^ r) β ν‖ ^ 2 ≤
          U ^ ((2 * a - 1) * min r (1 - r) + η) := by
  let b := 2 * ε + heightDegree K * ε * θ
  let κ := 3 / 4 + ε + heightDegree K * θ
  obtain ⟨N, hN⟩ := exists_uniform_contour_order τ 22 b κ hτ
  obtain ⟨CF, hCF, hF⟩ := exists_actual_normalized_buffered_scale_bound K
    hcomplex arch weight he he' hε W V hV hone hzero R θ τ hR N
  obtain ⟨CR, hCR, hRef⟩ := exists_actual_normalized_reflected_scale_bound K
    hcomplex arch weight he he' hε W R θ τ hR N
  obtain ⟨U₀, hU₀, hsq⟩ := exists_absorb_contour_remainder_square (max CF CR) η
    (hCF.trans (le_max_left _ _)) hη
  refine ⟨U₀, hU₀, ?_⟩
  intro χ I E U a H Hupper r β ν ratio hχ harch hweight hI hE
    hU ha ha' hr hr' hratio hβ hβ' hnorm hconductor hheight hHlower hpadding hupper S hS
  have hUtwo : 2 ≤ U := hU₀.trans hU
  have hUone : 1 ≤ U := by linarith
  have hk : 0 ≤ heightDegree K := by unfold heightDegree; positivity
  have hb : 0 ≤ b := by unfold b; positivity
  have hnumeric := contour_exponent_budget a r 22 e ε θ τ η (heightDegree K) N
    hr hr' he.le hk hθ (by nlinarith [hforward]) hreflected hN
  have htail : 3 / 2 * r - τ * N ≤ -100 := by
    have hh := hnumeric.2.2.1
    change 3 / 2 * r + b - τ * N ≤ -100 at hh
    linarith
  have hforwardexp :
      (a - 1 / 2 + 6 * e) * r + (2 * ε + heightDegree K * ε * θ) ≤
        (a - 1 / 2) * r + η / 4 := by
    nlinarith [hnumeric.1]
  have hreflectedexp :
      (a - 1 / 2) * (1 - r) + 12 * e - 6 * e * r + 2 * ε +
          heightDegree K * θ * (1 + ε) ≤
        (a - 1 / 2) * (1 - r) + η / 4 := by
    nlinarith [hnumeric.2.1]
  have hinverse := hF true χ I E U a H Hupper r β ν ratio hχ harch hweight hI hE
    hUone ha ha' hr hratio hβ hβ' hnorm hconductor hheight hHlower hpadding hupper S hS
  have hplain := hF false χ I E U a H Hupper r β ν 0 hχ harch hweight hI hE
    hUone ha ha' hr (by norm_num) hβ hβ' hnorm hconductor hheight hHlower hpadding hupper S hS
  have hplainRef := hRef χ I E U a H Hupper r β ν hχ harch hweight hI hE
    hUone ha ha' hr hβ hβ' hnorm hconductor hheight hHlower hpadding hupper S hS
  dsimp only at hinverse hplain
  have hzeroProfile : (W.cutoffFamily V hV 0).function = W.function := by
    funext x
    simp only [AnnularProfile.cutoffFamily_apply, zero_mul, hone 0 (by norm_num), mul_one]
  rw [hzeroProfile] at hplain
  have hforwardMajorant := three_power_majorant_mono hUone hCF (le_max_left CF CR)
    hforwardexp hnumeric.2.2.1 htail
  have hreflectedMajorant := three_power_majorant_mono hUone hCR (le_max_right CF CR)
    hreflectedexp hnumeric.2.2.2 htail
  have har : 0 ≤ (a - 1 / 2) * r := mul_nonneg (by linarith) hr
  have har' : (a - 1 / 2) * r ≤ (1 / 2 : ℝ) * 22 :=
    mul_le_mul (by linarith) hr' hr (by norm_num)
  have hx : -30 ≤ (a - 1 / 2) * r := by linarith
  have hy : -30 ≤ (a - 1 / 2) * (1 - r) := by nlinarith
  have hIsq := hsq U hU ((a - 1 / 2) * r) hx _ (hinverse.trans hforwardMajorant)
  have hPsq := hsq U hU ((a - 1 / 2) * r) hx _ (hplain.trans hforwardMajorant)
  have hRsq := hsq U hU ((a - 1 / 2) * (1 - r)) hy _
    (hplainRef.trans hreflectedMajorant)
  have heq₁ : 2 * ((a - 1 / 2) * r) + η = (2 * a - 1) * r + η := by ring
  have heq₂ : 2 * ((a - 1 / 2) * (1 - r)) + η =
      (2 * a - 1) * (1 - r) + η := by ring
  rw [heq₁] at hIsq hPsq
  rw [heq₂] at hRsq
  exact ⟨hIsq, min_power_upper hUone (by linarith) hPsq hRsq⟩

end Expansion.ActualDetectorSaturation
