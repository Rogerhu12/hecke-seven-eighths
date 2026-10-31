import HeckeGeneral.Analysis.ExpansionBufferedPolynomials
import ExpansionDetector.HeckeFixedTypeReflection

/-!
# The sharp reflected line for the actual ordinary polynomial

The left boundary retains the functional equation's conductor exponent
`a - 1/2 + 6e`. A different, deliberately coarse rectangle estimate is used
only for the two horizontal errors. Thus the conductor exponent `5/8`
from uniform strip growth never replaces the sharp main term.
-/

noncomputable section
namespace HeckeGeneral.Analysis.ExpansionReflectedPolynomials

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Bridge ExpansionDetectorInitial ExpansionDeletedControl ExpansionBufferedPolynomials
open HeckeSkeleton.HeckeBufferedReciprocal HeckeSkeleton.HeckeConductorNorm
open HeckeSkeleton.HeckeUniformBufferedControl HeckeSkeleton.HeckeUniformStripGrowth
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open ExpansionInterfaces.Mellin
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

def reflectedCost (χ : HeckeCharacter K) (I : Ideal (𝓞 K))
    (C e ε a Hupper : ℝ) : ℝ :=
  C * (Ideal.absNorm I : ℝ) ^ (6 * e + ε) *
    heckeConductorScale K χ ^ (a - 1 / 2 + 6 * e) * heckeConductorScale K χ ^ ε *
    (2 + Hupper) ^ (2 * Fintype.card (InfinitePlace K)) *
    (2 + Hupper) ^ ((2 * Fintype.card (InfinitePlace K) : ℕ) * ε)

def coarseRectangleCost (χ : HeckeCharacter K) (I : Ideal (𝓞 K))
    (C ε Hupper : ℝ) : ℝ :=
  C * (Ideal.absNorm I : ℝ) ^ (1 / 8 + ε) *
    heckeConductorScale K χ ^ (5 / 8 : ℝ) *
    (2 + Hupper) ^ (2 * Fintype.card (InfinitePlace K))

/-- A coarse fixed-type bound covering the negative real part needed by
the reflected contour and its absolutely convergent right edge. -/
theorem exists_coarse_fixedType_rectangle_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : HeckeCharacter K),
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = τ → heckeArchWeight K χ = m →
      ∀ s : ℂ, -(1 / 8 : ℝ) ≤ s.re → s.re ≤ 2 →
        ‖heckeContinuation K χ s‖ ≤ C * heckeConductorScale K χ ^ (5 / 8 : ℝ) *
          (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
  obtain ⟨C, hC, hstrip⟩ := exists_uniform_fixedType_strip_bound K hcomplex τ m
    (1 / 8) (by norm_num) (by norm_num)
  obtain ⟨D, hD, hright⟩ := exists_uniform_rightHalfPlane_bound K (9 / 8) (by norm_num)
  refine ⟨C + D, add_pos hC hD, ?_⟩
  intro χ hχ hτ hm s hs hs'
  have hQ := conductorScale_pos K χ
  have hQone := one_le_conductorScale_of_pos K χ hQ
  have hheight : 1 ≤ (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K)) :=
    one_le_pow₀ (by linarith [abs_nonneg s.im])
  by_cases hleft : s.re ≤ 9 / 8
  · have hb := hstrip χ hχ hτ hm s ⟨hs, by linarith⟩
    norm_num only [show (1 / 2 + 1 / 8 : ℝ) = 5 / 8 by norm_num] at hb
    exact hb.trans (by gcongr; linarith)
  · have hb := hright χ s (lt_of_not_ge hleft).le
    have hfactor : 1 ≤ heckeConductorScale K χ ^ (5 / 8 : ℝ) *
        (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K)) :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hQone (by norm_num)) hheight
    calc
      _ ≤ D := hb
      _ ≤ D * (heckeConductorScale K χ ^ (5 / 8 : ℝ) *
          (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K))) :=
        le_mul_of_one_le_right hD.le hfactor
      _ ≤ _ := by
        have hp : 0 ≤ C * (heckeConductorScale K χ ^ (5 / 8 : ℝ) *
            (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K))) := by positivity
        nlinarith

/-- The actual functional equation and the actual dual zero upper bound
give the sharp reflected left-line estimate. -/
theorem exists_actual_deleted_reflected_control
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : HeckeCharacter K) (I : Ideal (𝓞 K))
      (E : Finset (HeightOneSpectrum (𝓞 K))) (a H Hupper : ℝ),
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = τ → heckeArchWeight K χ = m →
      I ≠ 0 → (∀ p ∈ E, p.asIdeal ∣ I) →
      1 / 2 ≤ a → a ≤ 1 → 0 ≤ H → H + 3 / 2 ≤ Hupper →
      ZeroUpperBound K χ Hupper (a + 2 * e) →
      ∀ s : ℂ, s.re = 1 - a - 6 * e → |s.im| ≤ H →
        ‖heckeDeletedContinuation K χ E s‖ ≤ reflectedCost K χ I C e ε a Hupper := by
  obtain ⟨D, hD, hdual⟩ := exists_uniform_fixedType_buffered_control K hcomplex (-τ) (-m)
    he he' hε
  obtain ⟨G, hG, hreflection⟩ :=
    ExpansionDetector.Hecke.exists_fixedType_reflected_ordinary_bound K hcomplex τ m
  obtain ⟨F, hF, hdeletion⟩ := exists_deleted_euler_negative_subpower K
    (η := 6 * e) (by positivity) hε
  refine ⟨F * G * D, by positivity, ?_⟩
  intro χ I E a H Hupper hχ hτ hm hI hE ha ha' hH hpadding hupper s hs hh
  have hQ := conductorScale_pos K χ
  have hHU : 0 ≤ Hupper := by linarith
  obtain ⟨hτdual, hmdual⟩ := fixedType_inv K hcomplex χ τ m hτ hm
  have hdualpoint := hdual χ⁻¹ a H Hupper (nonNorm_inv K χ hχ) hτdual hmdual
    ha ha' hH hpadding (zeroUpperBound_inv K χ hupper) (1 - s)
      (by simp only [Complex.sub_re, Complex.one_re]; linarith)
      (by simp only [Complex.sub_re, Complex.one_re]; linarith)
      (by simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using hh)
  rw [conductorScale_inv] at hdualpoint
  have hdualnorm : ‖heckeContinuation K χ⁻¹ (1 - s)‖ ≤
      D * heckeConductorScale K χ ^ ε *
        (2 + Hupper) ^ ((2 * Fintype.card (InfinitePlace K) : ℕ) * ε) :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans hdualpoint
  have hreflectionpoint := hreflection χ hχ hτ hm s ⟨by linarith, by linarith⟩
  have hpow : 1 / 2 - s.re = a - 1 / 2 + 6 * e := by linarith
  rw [hpow] at hreflectionpoint
  have hheight : (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K)) ≤
      (2 + Hupper) ^ (2 * Fintype.card (InfinitePlace K)) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hL : ‖heckeContinuation K χ s‖ ≤
      (G * heckeConductorScale K χ ^ (a - 1 / 2 + 6 * e) *
        (2 + Hupper) ^ (2 * Fintype.card (InfinitePlace K))) *
      (D * heckeConductorScale K χ ^ ε *
        (2 + Hupper) ^ ((2 * Fintype.card (InfinitePlace K) : ℕ) * ε)) := by
    apply hreflectionpoint.trans
    apply mul_le_mul _ hdualnorm (norm_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left hheight (by positivity)
  have hP := hdeletion I hI E hE χ s (by linarith)
  rw [heckeDeletedContinuation, norm_mul]
  exact (mul_le_mul hP hL (norm_nonneg _) (by positivity)).trans_eq (by
    unfold reflectedCost
    ring)

theorem exists_actual_deleted_coarse_rectangle_control
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : HeckeCharacter K) (I : Ideal (𝓞 K))
      (E : Finset (HeightOneSpectrum (𝓞 K))) (Hupper : ℝ),
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = τ → heckeArchWeight K χ = m →
      I ≠ 0 → (∀ p ∈ E, p.asIdeal ∣ I) → 0 ≤ Hupper →
      ∀ s : ℂ, -(1 / 8 : ℝ) ≤ s.re → s.re ≤ 2 → |s.im| ≤ Hupper →
        ‖heckeDeletedContinuation K χ E s‖ ≤ coarseRectangleCost K χ I C ε Hupper := by
  obtain ⟨D, hD, hrectangle⟩ := exists_coarse_fixedType_rectangle_bound K hcomplex τ m
  obtain ⟨F, hF, hdeletion⟩ := exists_deleted_euler_negative_subpower K
    (η := 1 / 8) (by norm_num) hε
  refine ⟨F * D, mul_pos hF hD, ?_⟩
  intro χ I E Hupper hχ hτ hm hI hE hHU s hs hs' hh
  have hQ := conductorScale_pos K χ
  have hP := hdeletion I hI E hE χ s hs
  have hL := hrectangle χ hχ hτ hm s hs hs'
  have hheight : (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K)) ≤
      (2 + Hupper) ^ (2 * Fintype.card (InfinitePlace K)) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hL' := hL.trans (mul_le_mul_of_nonneg_left hheight
    (mul_nonneg hD.le (Real.rpow_nonneg hQ.le _)))
  rw [heckeDeletedContinuation, norm_mul]
  exact (mul_le_mul hP hL' (norm_nonneg _) (by positivity)).trans_eq (by
    unfold coarseRectangleCost
    ring)

/-- Reflected finite-polynomial upper bound for the actual ordinary
deleted coefficients. `CL` controls only the sharp left line; `CR` controls
only the finite horizontal sides. Both are chosen before every row. -/
theorem exists_actual_reflected_annular_upper
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε) :
    ∃ CL CR : ℝ, 0 < CL ∧ 0 < CR ∧ ∀ (W : AnnularProfile) (order : ℕ)
      (χ : HeckeCharacter K) (I : Ideal (𝓞 K))
      (E : Finset (HeightOneSpectrum (𝓞 K))) (a H Hupper X : ℝ) (s : ℂ),
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = τ → heckeArchWeight K χ = m →
      I ≠ 0 → (∀ p ∈ E, p.asIdeal ∣ I) →
      1 / 2 ≤ a → a ≤ 1 → 0 < H → |s.im| + H + 3 / 2 ≤ Hupper →
      ZeroUpperBound K χ Hupper (a + 2 * e) →
      1 ≤ X → 1 / 2 ≤ s.re → s.re ≤ 1 →
      ∀ S : Finset (NonzeroIdeal K), (∀ J, idealNorm K J ≤ W.upper * X → J ∈ S) →
      let BL := reflectedCost K χ I CL e ε a Hupper
      let BR := coarseRectangleCost K χ I CR ε Hupper
      let CW := W.contourConstant (-2) 2 order
      ‖∑ J ∈ S, smoothedTerm W (deletedAnnularCoefficient K false χ E)
        (idealNorm K) s X J‖ ≤ (1 / (2 * Real.pi)) *
        ((BL * X ^ (1 - a - 6 * e - s.re)) * CW +
          2 * (CW / (1 + H) ^ order) * BR * X ^ (2 - s.re) * (1 + a + 6 * e) +
          (initialMass K * X ^ (2 - s.re)) * (CW / H ^ order)) := by
  obtain ⟨CL, hCL, hleftbound⟩ := exists_actual_deleted_reflected_control K hcomplex τ m he he' hε
  obtain ⟨CR, hCR, hrectbound⟩ := exists_actual_deleted_coarse_rectangle_control K hcomplex τ m hε
  refine ⟨CL, CR, hCL, hCR, ?_⟩
  intro W order χ I E a H Hupper X s hχ hτ hm hI hE ha ha' hH hpadding hupper hX hs hs' S hS
  let BL := reflectedCost K χ I CL e ε a Hupper
  let BR := coarseRectangleCost K χ I CR ε Hupper
  let CW := W.contourConstant (-2) 2 order
  have hHU : 0 ≤ Hupper := by linarith [abs_nonneg s.im]
  have hQ := conductorScale_pos K χ
  have hBL : 0 ≤ BL := by unfold BL reflectedCost; positivity
  have hBR : 0 ≤ BR := by unfold BR coarseRectangleCost; positivity
  have hrect : ∀ z ∈ closedRectangle (1 - a - 6 * e - s.re) (2 - s.re) H,
      ‖deletedFunction K false χ E (s + z)‖ ≤ BR := by
    intro z hz
    apply hrectbound χ I E Hupper hχ hτ hm hI hE hHU (s + z)
    · simp only [Complex.add_re]
      linarith [hz.1]
    · simp only [Complex.add_re]
      linarith [hz.2.1]
    · have hh := abs_add_le s.im z.im
      change |s.im + z.im| ≤ Hupper
      linarith [hz.2.2]
  have hleft : ∀ t : ℝ, |t| ≤ H →
      ‖deletedFunction K false χ E (s + vertical (1 - a - 6 * e - s.re) t)‖ ≤ BL := by
    intro t ht
    apply hleftbound χ I E a (|s.im| + H) Hupper hχ hτ hm hI hE ha ha'
      (by positivity) hpadding hupper
    · simp only [Complex.add_re, vertical_re]
      ring
    · simp only [Complex.add_im, vertical_im]
      exact (abs_add_le _ _).trans (add_le_add_left ht _)
  have hsum : Summable (fun J => ‖deletedAnnularCoefficient K false χ E J‖ *
      idealNorm K J ^ (-(s.re + (2 - s.re)))) := by
    simpa only [show s.re + (2 - s.re) = (2 : ℝ) by ring] using
      (deletedAnnularCoefficient_summable K false χ E (σ := 2) (by norm_num))
  have hline : ∀ t : ℝ, deletedFunction K false χ E (s + vertical (2 - s.re) t) =
      ExpansionInterfaces.Mellin.dirichletSeries (deletedAnnularCoefficient K false χ E)
        (idealNorm K) (s + vertical (2 - s.re) t) := by
    intro t
    apply deletedFunction_initial_series K false χ E
    simp only [Complex.add_re, vertical_re]
    linarith
  have hdiff : DifferentiableOn ℂ (fun z => deletedFunction K false χ E (s + z))
      (closedRectangle (1 - a - 6 * e - s.re) (2 - s.re) H) :=
    ((heckeDeletedContinuation_entire K χ hχ E).comp
      ((differentiable_const s).add differentiable_id)).differentiableOn
  have hb := annular_polynomial_uniform_upper W (-2) 2 order
    (deletedAnnularCoefficient K false χ E) (idealNorm K) (idealNorm_pos K)
    (deletedFunction K false χ E) s (X := X) (a := 1 - a - 6 * e - s.re)
    (b := 2 - s.re) (H := H) (Mleft := BL) (M := BR)
    hX (by linarith) (by linarith) (by linarith) hH
    hBL hBR hsum hline hdiff hrect hleft S hS
  have hmass : (∑' J, ‖deletedAnnularCoefficient K false χ E J‖ *
      idealNorm K J ^ (-(s.re + (2 - s.re)))) ≤ initialMass K := by
    simpa only [show s.re + (2 - s.re) = (2 : ℝ) by ring] using
      (deleted_initial_mass_le K false χ E)
  have hCW : 0 ≤ CW := (W.contourConstant_spec (-2) 2 order).1
  dsimp only at hb ⊢
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 1 / (2 * Real.pi))
  have htail := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg (zero_le_one.trans hX) (2 - s.re)))
    (div_nonneg hCW (pow_nonneg hH.le order))
  have hwidth : (2 - s.re) - (1 - a - 6 * e - s.re) = 1 + a + 6 * e := by ring
  rw [hwidth]
  exact add_le_add_left htail _

end HeckeGeneral.Analysis.ExpansionReflectedPolynomials
