import FiniteAffineCorrelation

/-! SOURCE ONLY, UNRUN. The genuine congruence sum has cardinality bound
on unimodular residual columns. An explicit Bezout parametrization gives
exactly one residue-ring parameter. This does not bound the genuine sum
on arbitrary noncoprime columns, nor define the artificial extension. -/
noncomputable section
namespace HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical BigOperators ComplexConjugate
variable {R : Type*} [CommRing R] [Fintype R]

/-- The entire affine fibre, parametrized using actual Bezout coefficients. -/
def affineCorrelationFibreEquiv (n₁ n₂ a b : R)
    (hab : a * n₂ - b * n₁ = 1) (k : R) :
    R ≃ {p : R × R // n₂ * p.1 - n₁ * p.2 = k} where
  toFun t := ⟨(a * k + n₁ * t, b * k + n₂ * t), by
    change n₂ * (a * k + n₁ * t) - n₁ * (b * k + n₂ * t) = k
    calc
      _ = (a * n₂ - b * n₁) * k := by ring
      _ = k := by rw [hab, one_mul]⟩
  invFun p := a * p.val.2 - b * p.val.1
  left_inv t := by
    change a * (b * k + n₂ * t) - b * (a * k + n₁ * t) = t
    calc
      _ = (a * n₂ - b * n₁) * t := by ring
      _ = t := by rw [hab, one_mul]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change a * k + n₁ * (a * p.val.2 - b * p.val.1) = p.val.1
      linear_combination p.val.1 * hab - a * p.property
    · change b * k + n₂ * (a * p.val.2 - b * p.val.1) = p.val.2
      linear_combination p.val.2 * hab - b * p.property

theorem affineCorrelation_eq_sum_fibre (f : R → ℂ) (n₁ n₂ k : R) :
    affineCorrelation f n₁ n₂ k =
      ∑ p : {p : R × R // n₂ * p.1 - n₁ * p.2 = k},
        f p.val.1 * conj (f p.val.2) := by
  unfold affineCorrelation
  rw [← Finset.sum_filter]
  simpa only [Finset.subtype_univ] using
    (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
      (p := fun p : R × R => n₂ * p.1 - n₁ * p.2 = k)
      (fun p : R × R => f p.1 * conj (f p.2))).symm

theorem affineCorrelation_eq_sum_parameter (f : R → ℂ) (n₁ n₂ a b : R)
    (hab : a * n₂ - b * n₁ = 1) (k : R) :
    affineCorrelation f n₁ n₂ k =
      ∑ t : R, f (a * k + n₁ * t) * conj (f (b * k + n₂ * t)) := by
  rw [affineCorrelation_eq_sum_fibre]
  symm
  exact Fintype.sum_equiv (affineCorrelationFibreEquiv n₁ n₂ a b hab k)
    _ _ (fun _ => rfl)

/-- Cardinality bound on the genuine coprime residual locus. -/
theorem norm_affineCorrelation_le_card (f : R → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (n₁ n₂ : R) (hn : IsCoprime n₁ n₂) (k : R) :
    ‖affineCorrelation f n₁ n₂ k‖ ≤ (Fintype.card R : ℝ) := by
  obtain ⟨a, b, hab⟩ := hn
  have hbezout : b * n₂ - (-a) * n₁ = 1 := by
    calc
      _ = a * n₁ + b * n₂ := by ring
      _ = 1 := hab
  rw [affineCorrelation_eq_sum_parameter f n₁ n₂ b (-a) hbezout]
  calc
    _ ≤ ∑ t : R, ‖f (b * k + n₁ * t) * conj (f (-a * k + n₂ * t))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ : R, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t _
      simpa only [norm_mul, Complex.norm_conj, one_mul] using
        mul_le_mul (hf (b * k + n₁ * t)) (hf (-a * k + n₂ * t))
          (norm_nonneg (f (-a * k + n₂ * t))) (zero_le_one : (0 : ℝ) ≤ 1)
    _ = _ := by simp

end HeckeGeneral.Arithmetic.PeriodicFourier
