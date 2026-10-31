import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondAllocatedSource

/-!
# Exact positive normalization of the actual original Gauss factors

These are the extra normalizers of the original plain and prime
occurrences.  They are separate from the normalization inside the child
coefficient.  Their product supplies one inverse total scale in the
actual source energy and one inverse square root on each Cauchy side.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

variable {k : ℕ}

def extraGaussScale (N₁ N₂ : ℝ) (P : Fin k → ℝ) : ℝ := N₁ * N₂ * ∏ i, P i

def extraGaussNormalizer (N₁ N₂ : ℝ) (P : Fin k → ℝ) : ℂ :=
  SecondCoefficientTermDictionary.centralNormalizer
    (Real.sqrt N₁ : ℂ)⁻¹ (Real.sqrt N₂ : ℂ)⁻¹
    (fun i => (Real.sqrt (P i) : ℂ)⁻¹)

theorem extraGaussScale_pos (N₁ N₂ : ℝ) (P : Fin k → ℝ)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hP : ∀ i, 0 < P i) :
    0 < extraGaussScale N₁ N₂ P :=
  mul_pos (mul_pos hN₁ hN₂) (Finset.prod_pos (fun i _ => hP i))

theorem extraGaussNormalizer_norm_sq (N₁ N₂ : ℝ) (P : Fin k → ℝ)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hP : ∀ i, 0 < P i) :
    ‖extraGaussNormalizer N₁ N₂ P‖ ^ 2 = (extraGaussScale N₁ N₂ P)⁻¹ := by
  have hterm (N : ℝ) (hN : 0 < N) : ‖(Real.sqrt N : ℂ)⁻¹‖ ^ 2 = N⁻¹ := by
    simp only [norm_inv, Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg _),
      inv_pow, Real.sq_sqrt hN.le]
  simp only [extraGaussNormalizer, SecondCoefficientTermDictionary.centralNormalizer,
    norm_mul, norm_prod, mul_pow, ← Finset.prod_pow]
  rw [hterm N₁ hN₁, hterm N₂ hN₂]
  have hslot (i : Fin k) : ‖(Real.sqrt (P i) : ℂ)⁻¹‖ ^ 2 = (P i)⁻¹ := hterm (P i) (hP i)
  simp_rw [hslot]
  simp only [extraGaussScale, mul_inv_rev, Finset.prod_inv_distrib]
  ring

theorem extraGaussNormalizer_norm_pos (N₁ N₂ : ℝ) (P : Fin k → ℝ)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hP : ∀ i, 0 < P i) :
    0 < ‖extraGaussNormalizer N₁ N₂ P‖ := by
  have hp := inv_pos.mpr (extraGaussScale_pos N₁ N₂ P hN₁ hN₂ hP)
  rw [← extraGaussNormalizer_norm_sq N₁ N₂ P hN₁ hN₂ hP] at hp
  nlinarith [norm_nonneg (extraGaussNormalizer N₁ N₂ P)]

theorem extraGaussNormalizer_norm (N₁ N₂ : ℝ) (P : Fin k → ℝ)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hP : ∀ i, 0 < P i) :
    ‖extraGaussNormalizer N₁ N₂ P‖ = (Real.sqrt (extraGaussScale N₁ N₂ P))⁻¹ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))).mp
  rw [extraGaussNormalizer_norm_sq N₁ N₂ P hN₁ hN₂ hP, inv_pow,
    Real.sq_sqrt (extraGaussScale_pos N₁ N₂ P hN₁ hN₂ hP).le]

/-- There is only one pair of extra Gauss denominators. -/
theorem extraGaussNormalizer_pair_norm {l : ℕ}
    (N₁ N₂ M₁ M₂ : ℝ) (P : Fin k → ℝ) (Q : Fin l → ℝ)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hP : ∀ i, 0 < P i)
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hQ : ∀ i, 0 < Q i) :
    ‖extraGaussNormalizer N₁ N₂ P‖ * ‖extraGaussNormalizer M₁ M₂ Q‖ =
      1 / (Real.sqrt (extraGaussScale N₁ N₂ P) *
        Real.sqrt (extraGaussScale M₁ M₂ Q)) := by
  rw [extraGaussNormalizer_norm N₁ N₂ P hN₁ hN₂ hP,
    extraGaussNormalizer_norm M₁ M₂ Q hM₁ hM₂ hQ]
  ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.extraGaussNormalizer_norm_sq
#print axioms HeckeSkeleton.Moments.EngineStep.extraGaussNormalizer_pair_norm
