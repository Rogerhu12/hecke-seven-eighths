import HeckeSkeleton.ThetaKernel.Multiplier
import HeckeSkeleton.ThetaKernel.TestMellin
import HeckeSkeleton.ThetaKernel.Shift

/-! The kernel integrand `fz`, its pointwise strip bound, integrability and the
contour shift (with a polynomial weight `(-z)^h`). -/

noncomputable section
namespace HeckeSkeleton.ThetaKernel
open NumberField IsDedekindDomain MeasureTheory Set Filter
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.Characters
open scoped Classical BigOperators ComplexConjugate Topology

variable {K : Type} [Field K] [NumberField K]
variable {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]

/-- Number of complex places, as a real. -/
def ncx (K : Type) [Field K] [NumberField K] : ℝ :=
  (Fintype.card {v : InfinitePlace K // v.IsComplex} : ℝ)

theorem ncx_nonneg : 0 ≤ ncx K := Nat.cast_nonneg _

/-- The weighted holomorphic integrand `(-z)^h M(-z) m(z) y^{-z}`. -/
def fz (F : FiniteMellinData K S) (θ : HeckeCharacter K) (u : SixthUnitClasses K S)
    (κ : SixthLocalClasses K S) (V : SmoothAnnularTest) (h : ℕ) (y : ℝ) (z : ℂ) : ℂ :=
  (-z) ^ h * mellin V.toFun (-z) * reflectionMultiplier K S F θ u κ z * (y : ℂ) ^ (-z)

theorem kernelIntegrand_eq_fz (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (V : SmoothAnnularTest) (σ y t : ℝ) :
    kernelIntegrand K S F θ u κ V.toFun σ y t =
      fz F θ u κ V 0 y ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  unfold kernelIntegrand fz
  simp only [pow_zero, one_mul]

variable {F : FiniteMellinData K S}

theorem differentiableAt_fz (hF : FiniteMellinAdmissible K S F) (θ : HeckeCharacter K)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (V : SmoothAnnularTest) (h : ℕ)
    {y : ℝ} (hy : 0 < y) {z : ℂ} (hz : -(1 / 3 : ℝ) < z.re) :
    DifferentiableAt ℂ (fz F θ u κ V h y) z := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (-z) ^ h) z := by fun_prop
  have h2 : DifferentiableAt ℂ (fun z : ℂ => mellin V.toFun (-z)) z :=
    (differentiable_mellin_neg V) z
  have h3 := differentiableAt_reflectionMultiplier hF θ u κ hz
  have h4 : DifferentiableAt ℂ (fun z : ℂ => (y : ℂ) ^ (-z)) z :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl hy')
  unfold fz
  exact ((h1.mul h2).mul h3).mul h4

theorem continuous_fz_line (hF : FiniteMellinAdmissible K S F) (θ : HeckeCharacter K)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (V : SmoothAnnularTest) (h : ℕ)
    {y : ℝ} (hy : 0 < y) {σ : ℝ} (hσ : -(1 / 3 : ℝ) < σ) :
    Continuous (fun t : ℝ => fz F θ u κ V h y ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (differentiableAt_fz hF θ u κ V h hy (by simpa using hσ)).continuousAt.comp
    (by fun_prop : ContinuousAt (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) t)

/-- Pointwise bound on a vertical line from a multiplier strip bound. -/
theorem fz_pointwise_bound (θ : HeckeCharacter K)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (V : SmoothAnnularTest)
    {σlo Λ CM : ℝ} (hCM : 0 ≤ CM)
    (hM : ∀ s : ℂ, σlo ≤ s.re → s.re ≤ Λ →
      ‖reflectionMultiplier K S F θ u κ s‖ ≤ CM * (1 + |s.im|) ^ (4 * ncx K * s.re))
    {h J : ℕ} (hhJ : h ≤ J) {y : ℝ} (hy : 0 < y) {σ : ℝ} (h0 : σlo ≤ σ) (h1 : σ ≤ Λ) (t : ℝ) :
    ‖fz F θ u κ V h y ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      CM * (2 ^ J * (Iint V 0 σ + Iint V J σ)) * y ^ (-σ) *
        (1 + |t|) ^ (4 * ncx K * σ + (h : ℝ) - J) := by
  set w : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hw
  have hwre : w.re = σ := by simp [hw]
  have hwim : w.im = t := by simp [hw]
  set T : ℝ := 1 + |t| with hT
  have hT1 : 1 ≤ T := by rw [hT]; linarith [abs_nonneg t]
  have hTpos : 0 < T := by linarith
  set X : ℝ := 1 + ‖w‖ with hX
  have hTX : T ≤ X := by
    rw [hT, hX]
    have : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
    rw [hwim] at this
    linarith
  have hXpos : 0 < X := by linarith
  set B : ℝ := 2 ^ J * (Iint V 0 σ + Iint V J σ) with hB
  have hm : X ^ J * ‖mellin V.toFun (-w)‖ ≤ B := pow_mul_norm_mellin_le V J σ t
  have hnorm : ‖fz F θ u κ V h y w‖ = ‖w‖ ^ h * ‖mellin V.toFun (-w)‖ *
      ‖reflectionMultiplier K S F θ u κ w‖ * y ^ (-σ) := by
    unfold fz
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp [hwre]
  have hw1 : ‖w‖ ^ h ≤ X ^ h := pow_le_pow_left₀ (norm_nonneg _) (by rw [hX]; linarith) h
  have hXh : X ^ h * ‖mellin V.toFun (-w)‖ ≤ T ^ ((h : ℝ) - J) * B := by
    have e : X ^ h = X ^ ((h : ℝ) - J) * X ^ J := by
      rw [← Real.rpow_natCast X J, ← Real.rpow_add hXpos, ← Real.rpow_natCast X h]
      congr 1; ring
    have h2 : X ^ ((h : ℝ) - J) ≤ T ^ ((h : ℝ) - J) :=
      Real.rpow_le_rpow_of_nonpos hTpos hTX (by
        have : (h : ℝ) ≤ J := by exact_mod_cast hhJ
        linarith)
    calc X ^ h * ‖mellin V.toFun (-w)‖ = X ^ ((h : ℝ) - J) * (X ^ J * ‖mellin V.toFun (-w)‖) := by
          rw [e]; ring
      _ ≤ T ^ ((h : ℝ) - J) * B :=
          mul_le_mul h2 hm (by positivity) (by positivity)
  have hMw : ‖reflectionMultiplier K S F θ u κ w‖ ≤ CM * T ^ (4 * ncx K * σ) := by
    have := hM w (by rw [hwre]; exact h0) (by rw [hwre]; exact h1)
    rw [hwre, hwim] at this
    exact this
  have hyp : 0 ≤ y ^ (-σ) := by positivity
  have hA : ‖w‖ ^ h * ‖mellin V.toFun (-w)‖ ≤ T ^ ((h : ℝ) - J) * B :=
    (mul_le_mul_of_nonneg_right hw1 (norm_nonneg _)).trans hXh
  rw [hnorm]
  calc ‖w‖ ^ h * ‖mellin V.toFun (-w)‖ * ‖reflectionMultiplier K S F θ u κ w‖ * y ^ (-σ)
      ≤ (T ^ ((h : ℝ) - J) * B) * (CM * T ^ (4 * ncx K * σ)) * y ^ (-σ) := by
        apply mul_le_mul_of_nonneg_right _ hyp
        have hB0 : 0 ≤ B := by
          rw [hB]; have := Iint_nonneg V 0 σ; have := Iint_nonneg V J σ; positivity
        exact mul_le_mul hA hMw (norm_nonneg _) (mul_nonneg (by positivity) hB0)
    _ = CM * B * y ^ (-σ) * (T ^ ((h : ℝ) - J) * T ^ (4 * ncx K * σ)) := by ring
    _ = CM * B * y ^ (-σ) * T ^ (4 * ncx K * σ + (h : ℝ) - J) := by
        rw [← Real.rpow_add hTpos]; congr 2; ring

theorem rpow_neg_strip_le {y : ℝ} (hy : 0 < y) {σ a b : ℝ} (h1 : a ≤ σ) (h2 : σ ≤ b) :
    y ^ (-σ) ≤ y ^ (-a) + y ^ (-b) := by
  rcases le_or_gt 1 y with hy1 | hy1
  · have := Real.rpow_le_rpow_of_exponent_le hy1 (show -σ ≤ -a by linarith)
    have := Real.rpow_nonneg hy.le (-b)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hy hy1.le (show -b ≤ -σ by linarith)
    have := Real.rpow_nonneg hy.le (-a)
    linarith

theorem exists_exponent (K : Type) [Field K] [NumberField K] (b : ℝ) (h : ℕ) :
    ∃ J : ℕ, h + 2 ≤ J ∧ 4 * ncx K * max b 0 + h + 1 < J := by
  refine ⟨⌈4 * ncx K * max b 0⌉₊ + h + 2, by omega, ?_⟩
  have := Nat.le_ceil (4 * ncx K * max b 0)
  push_cast
  linarith

theorem fz_strip_bound (θ : HeckeCharacter K)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (V : SmoothAnnularTest)
    {a b CM : ℝ} (hab : a ≤ b) (hCM : 0 ≤ CM)
    (hM : ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖reflectionMultiplier K S F θ u κ s‖ ≤ CM * (1 + |s.im|) ^ (4 * ncx K * s.re))
    {h J : ℕ} (hhJ : h ≤ J) {y : ℝ} (hy : 0 < y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖fz F θ u κ V h y ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (1 + |t|) ^ (-((J : ℝ) - h - 4 * ncx K * max b 0)) := by
  refine ⟨CM * (2 ^ J * (Iint V 0 a + Iint V 0 b + (Iint V J a + Iint V J b))) *
    (y ^ (-a) + y ^ (-b)), by
      have := Iint_nonneg V 0 a; have := Iint_nonneg V 0 b
      have := Iint_nonneg V J a; have := Iint_nonneg V J b
      positivity, ?_⟩
  intro σ hσ t
  have hp := fz_pointwise_bound (F := F) θ u κ V hCM hM hhJ hy hσ.1 hσ.2 t
  refine hp.trans ?_
  have i0 := Iint_strip_le V 0 hσ.1 hσ.2
  have iJ := Iint_strip_le V J hσ.1 hσ.2
  have yy := rpow_neg_strip_le hy hσ.1 hσ.2
  have hT1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hexp : (1 + |t|) ^ (4 * ncx K * σ + (h : ℝ) - J) ≤
      (1 + |t|) ^ (-((J : ℝ) - h - 4 * ncx K * max b 0)) := by
    apply Real.rpow_le_rpow_of_exponent_le hT1
    have : σ ≤ max b 0 := hσ.2.trans (le_max_left _ _)
    have := ncx_nonneg (K := K)
    nlinarith
  have hQ : 0 ≤ Iint V 0 a + Iint V 0 b + (Iint V J a + Iint V J b) := by
    have := Iint_nonneg V 0 a; have := Iint_nonneg V 0 b
    have := Iint_nonneg V J a; have := Iint_nonneg V J b
    linarith
  have hPQ : Iint V 0 σ + Iint V J σ ≤ Iint V 0 a + Iint V 0 b + (Iint V J a + Iint V J b) := by
    linarith
  have hyp : 0 ≤ y ^ (-σ) := by positivity
  have hT0 : 0 ≤ (1 + |t|) ^ (4 * ncx K * σ + (h : ℝ) - J) := by positivity
  have h1 : CM * (2 ^ J * (Iint V 0 σ + Iint V J σ)) ≤
      CM * (2 ^ J * (Iint V 0 a + Iint V 0 b + (Iint V J a + Iint V J b))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPQ (by positivity)) hCM
  have hnn : 0 ≤ CM * (2 ^ J * (Iint V 0 a + Iint V 0 b + (Iint V J a + Iint V J b))) *
      (y ^ (-a) + y ^ (-b)) := by positivity
  calc CM * (2 ^ J * (Iint V 0 σ + Iint V J σ)) * y ^ (-σ) *
        (1 + |t|) ^ (4 * ncx K * σ + (h : ℝ) - J)
      ≤ CM * (2 ^ J * (Iint V 0 a + Iint V 0 b + (Iint V J a + Iint V J b))) *
          (y ^ (-a) + y ^ (-b)) * (1 + |t|) ^ (4 * ncx K * σ + (h : ℝ) - J) :=
        mul_le_mul_of_nonneg_right (mul_le_mul h1 yy hyp (by positivity)) hT0
    _ ≤ CM * (2 ^ J * (Iint V 0 a + Iint V 0 b + (Iint V J a + Iint V J b))) *
          (y ^ (-a) + y ^ (-b)) * (1 + |t|) ^ (-((J : ℝ) - h - 4 * ncx K * max b 0)) :=
        mul_le_mul_of_nonneg_left hexp hnn

theorem fz_integrable (hF : FiniteMellinAdmissible K S F) (θ : HeckeCharacter K)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (V : SmoothAnnularTest) (h : ℕ)
    {y : ℝ} (hy : 0 < y) {σ : ℝ} (hσ : -(1 / 3 : ℝ) < σ) :
    Integrable (fun t : ℝ => fz F θ u κ V h y ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  obtain ⟨CM, hCM, hM⟩ := reflectionMultiplier_bound_pt hF θ u κ hσ le_rfl
  obtain ⟨J, hJ1, hJ2⟩ := exists_exponent K σ h
  obtain ⟨C, hC0, hC⟩ := fz_strip_bound (F := F) θ u κ V (a := σ) (b := σ) le_rfl hCM
    (fun s h0 h1 => hM s h0 h1) (h := h) (J := J) (by omega) hy
  refine ((integrable_one_add_abs_rpow_neg (e := (J : ℝ) - h - 4 * ncx K * max σ 0)
    (by linarith)).const_mul C).mono' (continuous_fz_line hF θ u κ V h hy hσ).aestronglyMeasurable
    (ae_of_all _ (fun t => hC σ ⟨le_rfl, le_rfl⟩ t))

theorem fz_shift (hF : FiniteMellinAdmissible K S F) (θ : HeckeCharacter K)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (V : SmoothAnnularTest) (h : ℕ)
    {y : ℝ} (hy : 0 < y) {a b : ℝ} (ha : -(1 / 3 : ℝ) < a) (hab : a ≤ b) :
    (∫ t : ℝ, fz F θ u κ V h y ((a : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t : ℝ, fz F θ u κ V h y ((b : ℂ) + (t : ℂ) * Complex.I) := by
  obtain ⟨CM, hCM, hM⟩ := reflectionMultiplier_bound_pt hF θ u κ ha hab
  obtain ⟨J, hJ1, hJ2⟩ := exists_exponent K b h
  obtain ⟨C, hC0, hC⟩ := fz_strip_bound (F := F) θ u κ V hab hCM
    (fun s h0 h1 => hM s h0 h1) (h := h) (J := J) (by omega) hy
  refine verticalIntegral_eq_of_poly_strip hab (C := C) (e := (J : ℝ) - h - 4 * ncx K * max b 0)
    (by linarith) (fun z hz1 hz2 => differentiableAt_fz hF θ u κ V h hy (by linarith)) ?_
  intro σ hσ t
  exact hC σ hσ t

end HeckeSkeleton.ThetaKernel
