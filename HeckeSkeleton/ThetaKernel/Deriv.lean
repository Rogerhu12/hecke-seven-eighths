import HeckeSkeleton.ThetaKernel.Core

/-! Differentiation of the kernel in the scale variable: `y d/dy` raises the
polynomial weight by one. -/

noncomputable section
namespace HeckeSkeleton.ThetaKernel
open NumberField IsDedekindDomain MeasureTheory Set Filter
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.Characters
open scoped Classical BigOperators ComplexConjugate Topology

variable {K : Type} [Field K] [NumberField K]
variable {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
variable {F : FiniteMellinData K S}

theorem hasDerivAt_ofReal_cpow_all (r : ℂ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ r) (r * (y : ℂ) ^ (r - 1)) y := by
  by_cases hr : r = 0
  · subst hr; simpa using hasDerivAt_const y (1 : ℂ)
  · exact hasDerivAt_ofReal_cpow_const hy.ne' hr

theorem hasDerivAt_fz_y (θ : HeckeCharacter K) (u : SixthUnitClasses K S)
    (κ : SixthLocalClasses K S) (V : SmoothAnnularTest) (h : ℕ) (z : ℂ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y' : ℝ => fz F θ u κ V h y' z)
      ((y : ℂ)⁻¹ * fz F θ u κ V (h + 1) y z) y := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hd := (hasDerivAt_ofReal_cpow_all (-z) hy).const_mul
    ((-z) ^ h * mellin V.toFun (-z) * reflectionMultiplier K S F θ u κ z)
  simp only [fz]
  refine hd.congr_deriv ?_
  rw [Complex.cpow_sub _ _ hy', Complex.cpow_one]
  field_simp
  ring

theorem rpow_between_le {y p q : ℝ} (hp : 0 < p) (hpy : p ≤ y) (hyq : y ≤ q) (c : ℝ) :
    y ^ c ≤ p ^ c + q ^ c := by
  have hy : 0 < y := lt_of_lt_of_le hp hpy
  have hq : 0 < q := lt_of_lt_of_le hy hyq
  rcases le_or_gt 0 c with h | h
  · have := Real.rpow_le_rpow hy.le hyq h
    have := Real.rpow_nonneg hp.le c
    linarith
  · have := Real.rpow_le_rpow_of_nonpos hp hpy h.le
    have := Real.rpow_nonneg hq.le c
    linarith

/-- The kernel as a function of the scale, on the line `Re w = σ`. -/
def Gc (F : FiniteMellinData K S) (θ : HeckeCharacter K) (u : SixthUnitClasses K S)
    (κ : SixthLocalClasses K S) (V : SmoothAnnularTest) (h : ℕ) (σ y : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ, fz F θ u κ V h y ((σ : ℂ) + (t : ℂ) * Complex.I)

theorem mellinReflectionKernel_eq_Gc (θ : HeckeCharacter K) (u : SixthUnitClasses K S)
    (κ : SixthLocalClasses K S) (V : SmoothAnnularTest) (σ y : ℝ) :
    mellinReflectionKernel K S F θ u κ V.toFun σ y = Gc F θ u κ V 0 σ y := by
  unfold mellinReflectionKernel Gc
  simp only [kernelIntegrand_eq_fz]

theorem hasDerivAt_Gc (hF : FiniteMellinAdmissible K S F) (θ : HeckeCharacter K)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (V : SmoothAnnularTest) (h : ℕ)
    {σ : ℝ} (hσ : -(1 / 3 : ℝ) < σ) {y0 : ℝ} (hy0 : 0 < y0) :
    HasDerivAt (fun y => Gc F θ u κ V h σ y)
      ((y0 : ℂ)⁻¹ * Gc F θ u κ V (h + 1) σ y0) y0 := by
  obtain ⟨CM, hCM, hM⟩ := reflectionMultiplier_bound_pt hF θ u κ hσ le_rfl
  obtain ⟨J, hJ1, hJ2⟩ := exists_exponent K σ (h + 1)
  set e : ℝ := (J : ℝ) - ((h + 1 : ℕ) : ℝ) - 4 * ncx K * max σ 0 with he
  have he1 : 1 < e := by rw [he]; push_cast at hJ2 ⊢; linarith
  set Bc : ℝ := CM * (2 ^ J * (Iint V 0 σ + Iint V J σ)) with hBc
  have hBc0 : 0 ≤ Bc := by
    have := Iint_nonneg V 0 σ; have := Iint_nonneg V J σ
    positivity
  set Yb : ℝ := (y0 / 2) ^ (-σ - 1) + (3 * y0 / 2) ^ (-σ - 1) with hYb
  have hYb0 : 0 ≤ Yb := by positivity
  set s : Set ℝ := Ioo (y0 / 2) (3 * y0 / 2) with hs
  have hsn : s ∈ 𝓝 y0 := Ioo_mem_nhds (by linarith) (by linarith)
  have hint := fz_integrable hF θ u κ V h hy0 hσ
  have hF' : ∀ y : ℝ, 0 < y →
      Continuous (fun t : ℝ => (y : ℂ)⁻¹ * fz F θ u κ V (h + 1) y ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    fun y hy => continuous_const.mul (continuous_fz_line hF θ u κ V (h + 1) hy hσ)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y t => fz F θ u κ V h y ((σ : ℂ) + (t : ℂ) * Complex.I))
    (F' := fun y t => (y : ℂ)⁻¹ * fz F θ u κ V (h + 1) y ((σ : ℂ) + (t : ℂ) * Complex.I))
    (bound := fun t => (Bc * Yb) * (1 + |t|) ^ (-e)) (x₀ := y0) (μ := volume) hsn
    (by
      filter_upwards [hsn] with y hy
      have : 0 < y := by have := hy.1; linarith
      exact (continuous_fz_line hF θ u κ V h this hσ).aestronglyMeasurable)
    hint (hF' y0 hy0).aestronglyMeasurable
    (by
      refine ae_of_all _ (fun t y hy => ?_)
      have hypos : 0 < y := by have := hy.1; linarith
      have hp := fz_pointwise_bound (F := F) θ u κ V (σlo := σ) (Λ := σ) (CM := CM) hCM
        (fun s h0 h1 => hM s h0 h1) (h := h + 1) (J := J) (by omega) hypos
        le_rfl le_rfl t
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hypos]
      have hyy : y ^ (-σ - 1) ≤ Yb := rpow_between_le (by linarith) hy.1.le hy.2.le _
      have hT1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
      have hTe : (1 + |t|) ^ (4 * ncx K * σ + ((h + 1 : ℕ) : ℝ) - J) ≤ (1 + |t|) ^ (-e) := by
        apply Real.rpow_le_rpow_of_exponent_le hT1
        rw [he]
        have : σ ≤ max σ 0 := le_max_left _ _
        have := ncx_nonneg (K := K)
        nlinarith
      have hpow : y⁻¹ * y ^ (-σ) = y ^ (-σ - 1) := by
        rw [Real.rpow_sub_one hypos.ne']; field_simp
      calc y⁻¹ * ‖fz F θ u κ V (h + 1) y ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ y⁻¹ * (Bc * y ^ (-σ) * (1 + |t|) ^ (4 * ncx K * σ + ((h + 1 : ℕ) : ℝ) - J)) := by
            apply mul_le_mul_of_nonneg_left hp (by positivity)
        _ = Bc * (y⁻¹ * y ^ (-σ)) * (1 + |t|) ^ (4 * ncx K * σ + ((h + 1 : ℕ) : ℝ) - J) := by ring
        _ ≤ Bc * Yb * (1 + |t|) ^ (-e) := by
            rw [hpow]
            gcongr)
    (((integrable_one_add_abs_rpow_neg he1).const_mul (Bc * Yb)))
    (by
      refine ae_of_all _ (fun t y hy => ?_)
      have hypos : 0 < y := by have := hy.1; linarith
      exact hasDerivAt_fz_y θ u κ V h _ hypos)
  have := key.2
  unfold Gc
  convert this.const_mul ((2 * (Real.pi : ℂ))⁻¹) using 1
  rw [integral_const_mul]
  ring

end HeckeSkeleton.ThetaKernel
