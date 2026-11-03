import ExpansionDetector.GammaWeightedZeroShift

/-!
# A fixed-line zero detector for the full range beta >= 51/100

The Gamma contour is moved to Re(w)=-1/2. The zero of L at rho removes
the Gamma pole, while L(rho+w) stays in Re(s)>=1/100. This avoids the
near-one restriction of the older detector using Re(w)=1/2-beta.

The theorem assumes ordinary entire continuation and a polynomial strip
bound for L; it proves a decaying bound for the actual detector integral.
Neither witness existence nor a spike inequality is a premise.
-/

noncomputable section
namespace ExpansionDetector.Analytic
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology

def vertical (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I

@[simp] lemma vertical_re (σ t : ℝ) : (vertical σ t).re = σ := by simp [vertical]
@[simp] lemma vertical_im (σ t : ℝ) : (vertical σ t).im = t := by simp [vertical]

def gammaDetector (L M : ℂ → ℂ) (ρ : ℂ) (X : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ, Complex.Gamma (vertical 2 t) *
      (L (ρ + vertical 2 t) * M (ρ + vertical 2 t)) *
      (X : ℂ) ^ vertical 2 t

/-- Uniform contour estimate at any zero of an entire function. The same
constant works for all X, rho, and the two entire functions. -/
theorem gammaDetector_bound_at_zero (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L M : ℂ → ℂ) (ρ : ℂ) (X B : ℝ),
      Differentiable ℂ L → Differentiable ℂ M → L ρ = 0 →
      0 < X → 0 ≤ B →
      (∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ t : ℝ,
        ‖L (ρ + vertical σ t) * M (ρ + vertical σ t)‖ ≤
          B * (2 + |ρ.im + t|) ^ A) →
      ‖gammaDetector L M ρ X‖ ≤ C * B * X ^ (-1 / 2 : ℝ) * (2 + |ρ.im|) ^ A := by
  obtain ⟨G, hG, hg⟩ := detector_sz_gamma_moments A hA
  refine ⟨(1 / (2 * Real.pi)) * G, by positivity, ?_⟩
  intro L M ρ X B hL hM hz hX hB hbound
  let f : ℂ → ℂ := fun v => L (ρ + v) * M (ρ + v)
  have hf : Differentiable ℂ f :=
    (hL.comp ((differentiable_const ρ).add differentiable_id)).mul
      (hM.comp ((differentiable_const ρ).add differentiable_id))
  have hf0 : f 0 = 0 := by simp [f, hz]
  have hGrowth : ∃ C B' : ℝ, 0 < C ∧ 0 ≤ B' ∧
      ∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ t : ℝ,
        ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (2 + |t|) ^ B' := by
    refine ⟨(B + 1) * (2 + |ρ.im|) ^ A, A, by positivity, hA, ?_⟩
    intro σ hσ t
    have htri : 2 + |ρ.im + t| ≤ (2 + |ρ.im|) * (2 + |t|) := by
      nlinarith [abs_add_le ρ.im t, abs_nonneg ρ.im, abs_nonneg t,
        mul_nonneg (abs_nonneg ρ.im) (abs_nonneg t)]
    calc
      _ ≤ B * (2 + |ρ.im + t|) ^ A := hbound σ hσ t
      _ ≤ B * ((2 + |ρ.im|) * (2 + |t|)) ^ A :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) htri hA) hB
      _ = B * ((2 + |ρ.im|) ^ A * (2 + |t|) ^ A) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
      _ ≤ ((B + 1) * (2 + |ρ.im|) ^ A) * (2 + |t|) ^ A := by
        nlinarith [Real.rpow_nonneg (by positivity : 0 ≤ 2 + |ρ.im|) A,
          Real.rpow_nonneg (by positivity : 0 ≤ 2 + |t|) A,
          mul_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 2 + |ρ.im|) A)
            (Real.rpow_nonneg (by positivity : 0 ≤ 2 + |t|) A)]
  obtain ⟨hia, hi2, heq⟩ := gamma_zero_shift (-1 / 2) X f (by norm_num)
    hX hf.differentiableOn hf0 hGrowth
  obtain ⟨hgi, hgb⟩ := hg (-1 / 2) (Or.inl (by norm_num)) ρ.im
  let W : ℝ → ℝ := fun t =>
    ‖Complex.Gamma (vertical (-1 / 2) t)‖ * (2 + |ρ.im + t|) ^ A
  have hmajor (t : ℝ) :
      ‖Complex.Gamma (vertical (-1 / 2) t) * f (vertical (-1 / 2) t) *
          (X : ℂ) ^ vertical (-1 / 2) t‖ ≤
        (B * X ^ (-1 / 2 : ℝ)) * W t := by
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX, vertical_re]
    calc
      _ ≤ ‖Complex.Gamma (vertical (-1 / 2) t)‖ *
          (B * (2 + |ρ.im + t|) ^ A) * X ^ (-1 / 2 : ℝ) := by
        gcongr
        exact hbound (-1 / 2) ⟨le_rfl, by norm_num⟩ t
      _ = _ := by dsimp [W]; ring
  have hint : ‖∫ t : ℝ, Complex.Gamma (vertical (-1 / 2) t) *
      f (vertical (-1 / 2) t) * (X : ℂ) ^ vertical (-1 / 2) t‖ ≤
      (B * X ^ (-1 / 2 : ℝ)) * (G * (2 + |ρ.im|) ^ A) := by
    calc
      _ ≤ ∫ t : ℝ, ‖Complex.Gamma (vertical (-1 / 2) t) *
          f (vertical (-1 / 2) t) * (X : ℂ) ^ vertical (-1 / 2) t‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, (B * X ^ (-1 / 2 : ℝ)) * W t :=
        integral_mono hia.norm (hgi.const_mul _) hmajor
      _ = (B * X ^ (-1 / 2 : ℝ)) * ∫ t : ℝ, W t := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hgb (by positivity)
  have hn : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  unfold gammaDetector
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ, Complex.Gamma (vertical 2 t) * f (vertical 2 t) *
      (X : ℂ) ^ vertical 2 t‖ ≤ _
  rw [norm_mul, hn]
  have heq' : (∫ t : ℝ, Complex.Gamma (vertical 2 t) * f (vertical 2 t) *
      (X : ℂ) ^ vertical 2 t) =
      ∫ t : ℝ, Complex.Gamma (vertical (-1 / 2) t) * f (vertical (-1 / 2) t) *
        (X : ℂ) ^ vertical (-1 / 2) t := by simpa [vertical] using heq
  rw [heq']
  calc
    _ ≤ (1 / (2 * Real.pi)) *
        ((B * X ^ (-1 / 2 : ℝ)) * (G * (2 + |ρ.im|) ^ A)) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by ring

/-- An actual finite Dirichlet polynomial, not an arbitrary witness value. -/
def dirichletPolynomial {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (N : ι → ℝ) (s : ℂ) : ℂ :=
  ∑ i ∈ S, c i * (N i : ℂ) ^ (-s)

theorem dirichletPolynomial_entire {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (N : ι → ℝ) (hN : ∀ i ∈ S, 0 < N i) :
    Differentiable ℂ (dirichletPolynomial S c N) := by
  apply Differentiable.fun_sum
  intro i hi
  exact (Differentiable.const_cpow differentiable_id.neg
    (Or.inl (Complex.ofReal_ne_zero.mpr (hN i hi).ne'))).const_mul (c i)

/-- A crude bound sufficient for the initial detector: the sum of N^-2
is uniformly bounded for actual ideals, and D is the support ceiling. -/
theorem dirichletPolynomial_norm_bound {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (N : ι → ℝ) (D C : ℝ)
    (hN : ∀ i ∈ S, 1 ≤ N i ∧ N i ≤ D)
    (hc : ∀ i ∈ S, ‖c i‖ ≤ 1)
    (hC : (∑ i ∈ S, (N i) ^ (-2 : ℝ)) ≤ C)
    (s : ℂ) (hs : 0 ≤ s.re) :
    ‖dirichletPolynomial S c N s‖ ≤ D ^ 2 * C := by
  have hterm (i : ι) (hi : i ∈ S) :
      ‖c i * (N i : ℂ) ^ (-s)‖ ≤ D ^ 2 * (N i) ^ (-2 : ℝ) := by
    have hNi : 0 < N i := zero_lt_one.trans_le (hN i hi).1
    have hpow : ‖(N i : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hNi, Complex.neg_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos (hN i hi).1 (neg_nonpos.mpr hs)
    have hnorm : ‖c i * (N i : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [norm_mul]
      exact (mul_le_mul (hc i hi) hpow (norm_nonneg _) (by norm_num)).trans_eq (by ring)
    apply hnorm.trans
    rw [Real.rpow_neg hNi.le, Real.rpow_two]
    have hD : 0 ≤ D := hNi.le.trans (hN i hi).2
    have hsq : (N i) ^ 2 ≤ D ^ 2 := sq_le_sq₀ hNi.le hD |>.mpr (hN i hi).2
    calc
      (1 : ℝ) = (N i) ^ 2 * ((N i) ^ 2)⁻¹ := (mul_inv_cancel₀ (pow_ne_zero _ hNi.ne')).symm
      _ ≤ D ^ 2 * ((N i) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr (sq_nonneg _))
  calc
    _ ≤ ∑ i ∈ S, ‖c i * (N i : ℂ) ^ (-s)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S, D ^ 2 * (N i) ^ (-2 : ℝ) := Finset.sum_le_sum hterm
    _ = D ^ 2 * ∑ i ∈ S, (N i) ^ (-2 : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hC (sq_nonneg D)

end ExpansionDetector.Analytic
