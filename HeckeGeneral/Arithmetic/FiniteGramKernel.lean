import HeckeGeneral.Arithmetic.FiniteFourierConvolution

/-!
# Exact positive Gram kernels on a finite quotient

The kernel is defined by actual vectors and finite sums. Its quadratic
form is exactly the energy of their linear combination. Fourier
Plancherel relates the two actual Gram matrices. In the translation
specialization, the common spectral weight is the squared norm of one
Fourier coefficient, rather than a supplied positivity axiom.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic.PeriodicFourier

open scoped BigOperators ComplexConjugate Classical

variable {A ι : Type*} [Fintype A]

def gram (v : ι → A → ℂ) (i j : ι) : ℂ := ∑ a : A, v i a * conj (v j a)

def linearCombination [Fintype ι] (c : ι → ℂ) (v : ι → A → ℂ) (a : A) : ℂ :=
  ∑ i : ι, c i * v i a

def quadraticForm [Fintype ι] (G : ι → ι → ℂ) (c : ι → ℂ) : ℂ :=
  ∑ i : ι, ∑ j : ι, c i * conj (c j) * G i j

theorem gram_hermitian (v : ι → A → ℂ) (i j : ι) :
    gram v i j = conj (gram v j i) := by
  simp [gram, map_sum, map_mul, mul_comm]

theorem gram_diagonal (v : ι → A → ℂ) (i : ι) :
    gram v i i = (energy (v i) : ℂ) := by
  simp [gram, energy, Complex.mul_conj', ← Complex.ofReal_pow]

theorem gram_diagonal_nonneg (v : ι → A → ℂ) (i : ι) : 0 ≤ (gram v i i).re := by
  rw [gram_diagonal]
  exact energy_nonneg (v i)

theorem gram_diagonal_im (v : ι → A → ℂ) (i : ι) : (gram v i i).im = 0 := by
  rw [gram_diagonal]
  simp

theorem gram_diagonal_eq_zero_iff (v : ι → A → ℂ) (i : ι) :
    gram v i i = 0 ↔ ∀ a, v i a = 0 := by
  rw [gram_diagonal, Complex.ofReal_eq_zero, energy_eq_zero_iff]

theorem gram_const_mul (v : ι → A → ℂ) (c : ι → ℂ) (i j : ι) :
    gram (fun k a => c k * v k a) i j = c i * conj (c j) * gram v i j := by
  simp only [gram, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem norm_gram_le (v : ι → A → ℂ) (i j : ι) :
    ‖gram v i j‖ ≤ l2Norm (v i) * l2Norm (v j) := by
  calc
    ‖gram v i j‖ ≤ ∑ a : A, ‖v i a‖ * ‖v j a‖ := by
      simpa [gram] using norm_sum_le Finset.univ (fun a => v i a * conj (v j a))
    _ ≤ l2Norm (v i) * l2Norm (v j) := by
      simpa [l2Norm, energy] using
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun a => ‖v i a‖) (fun a => ‖v j a‖)

theorem norm_gram_sq_le (v : ι → A → ℂ) (i j : ι) :
    ‖gram v i j‖ ^ 2 ≤ energy (v i) * energy (v j) := by
  have h := (sq_le_sq₀ (norm_nonneg (gram v i j))
    (mul_nonneg (l2Norm_nonneg _) (l2Norm_nonneg _))).mpr (norm_gram_le v i j)
  simpa only [mul_pow, l2Norm_sq] using h

section FiniteFamily

variable [Fintype ι]

theorem quadraticForm_gram (v : ι → A → ℂ) (c : ι → ℂ) :
    quadraticForm (gram v) c = (energy (linearCombination c v) : ℂ) := by
  unfold quadraticForm gram
  simp only [Finset.mul_sum]
  have hswap (i : ι) :
      (∑ j : ι, ∑ a : A, c i * conj (c j) * (v i a * conj (v j a))) =
        ∑ a : A, ∑ j : ι, c i * conj (c j) * (v i a * conj (v j a)) := Finset.sum_comm
  simp only [hswap]
  rw [Finset.sum_comm]
  apply Eq.trans _ (gram_diagonal (fun _ : Unit => linearCombination c v) ())
  change (∑ a : A, ∑ i : ι, ∑ j : ι, c i * conj (c j) * (v i a * conj (v j a))) =
    ∑ a : A, linearCombination c v a * conj (linearCombination c v a)
  apply Finset.sum_congr rfl
  intro a _
  simp only [linearCombination, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadraticForm_gram_nonneg (v : ι → A → ℂ) (c : ι → ℂ) :
    0 ≤ (quadraticForm (gram v) c).re := by
  rw [quadraticForm_gram]
  exact energy_nonneg _

theorem quadraticForm_gram_im (v : ι → A → ℂ) (c : ι → ℂ) :
    (quadraticForm (gram v) c).im = 0 := by
  rw [quadraticForm_gram]
  simp

theorem quadraticForm_gram_eq_zero_iff (v : ι → A → ℂ) (c : ι → ℂ) :
    quadraticForm (gram v) c = 0 ↔ ∀ a, ∑ i : ι, c i * v i a = 0 := by
  rw [quadraticForm_gram, Complex.ofReal_eq_zero, energy_eq_zero_iff]
  rfl

theorem trace_gram (v : ι → A → ℂ) :
    ∑ i : ι, gram v i i = ((∑ i : ι, energy (v i)) : ℝ) := by
  simp [gram_diagonal]

end FiniteFamily

variable {R : Type*} [CommRing R] [Fintype R]

theorem gram_fourier (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (v : ι → R → ℂ) (i j : ι) :
    gram (fun k => fourier ψ (v k)) i j = (Fintype.card R : ℂ) * gram v i j :=
  (parseval_pairing ψ hψ (v i) (v j)).symm

def translationVectors (f : R → ℂ) (b : R) : R → ℂ := translate b f

def translationGram (f : R → ℂ) (b c : R) : ℂ := gram (translationVectors f) b c

theorem translationGram_eq_correlation (f : R → ℂ) (b c : R) :
    translationGram f b c = correlation f f (b - c) := by
  unfold translationGram gram translationVectors translate correlation
  refine Fintype.sum_bijective _ (Equiv.addRight c).bijective _ _ (fun a => ?_)
  change f (a + b) * conj (f (a + c)) = f (a + c + (b - c)) * conj (f (a + c))
  congr 2
  ring

theorem translationGram_hermitian (f : R → ℂ) (b c : R) :
    translationGram f b c = conj (translationGram f c b) :=
  gram_hermitian _ b c

theorem translationGram_diagonal (f : R → ℂ) (b : R) :
    translationGram f b b = (energy f : ℂ) := by
  rw [translationGram, gram_diagonal]
  simp only [translationVectors, energy_translate]

theorem translationGram_spectral (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (f : R → ℂ) (b c : R) :
    (Fintype.card R : ℂ) * translationGram f b c =
      ∑ h : R, (‖fourier ψ f h‖ ^ 2 : ℝ) * ψ (h * (c - b)) := by
  unfold translationGram
  rw [← gram_fourier ψ hψ (translationVectors f) b c]
  unfold gram translationVectors
  simp only [fourier_translate, map_mul]
  apply Finset.sum_congr rfl
  intro h _
  rw [← ψ.map_neg_eq_conj]
  have hsq := Complex.mul_conj' (fourier ψ f h)
  have hc : ψ (-(h * b)) * ψ (- (-(h * c))) = ψ (h * (c - b)) := by
    rw [← ψ.map_add_eq_mul]
    congr 1
    ring
  calc
    _ = (fourier ψ f h * conj (fourier ψ f h)) *
        (ψ (-(h * b)) * ψ (- (-(h * c)))) := by ring
    _ = _ := by rw [hsq, hc]; simp

theorem translationGram_quadratic_nonneg (f c : R → ℂ) :
    0 ≤ (quadraticForm (translationGram f) c).re := quadraticForm_gram_nonneg _ _

theorem translationGram_quadratic_eq_energy (f c : R → ℂ) :
    quadraticForm (translationGram f) c =
      (energy (fun a => ∑ b : R, c b * f (a + b)) : ℂ) :=
  quadraticForm_gram _ _

end HeckeGeneral.Arithmetic.PeriodicFourier
