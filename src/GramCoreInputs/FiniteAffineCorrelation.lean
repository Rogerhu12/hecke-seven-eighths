import HeckeGeneral.Arithmetic.FiniteFourierConvolution

/-! SOURCE ONLY, UNRUN. The unnormalized finite congruence sum in Q,
quasi-riemann.tex:7105-7108. The linear constraint retains its literal
minus sign and all pairs, including nonunit columns. The artificial local
product extension used away from coprime residual columns is a different
function. In particular no cardinality bound for arbitrary columns is
asserted here. Actual sextic specialization is in a separate consumer. -/

noncomputable section
namespace HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical BigOperators ComplexConjugate

variable {R : Type*} [CommRing R] [Fintype R]

/-- The genuine affine correlation on the entire finite residue ring. -/
def affineCorrelation (f : R → ℂ) (n₁ n₂ k : R) : ℂ :=
  ∑ p : R × R, if n₂ * p.1 - n₁ * p.2 = k then
    f p.1 * conj (f p.2) else 0

/-- Two independent residue-unit substitutions. The supplied invariances
are discharged for the actual sextic quotient function by the consumer. -/
theorem affineCorrelation_unit_covariance (f : R → ℂ) (u v : Rˣ)
    (hu : ∀ x, f ((u : R) * x) = f x)
    (hv : ∀ x, f ((v : R) * x) = f x) (n₁ n₂ k : R) :
    affineCorrelation f ((u : R) * n₁) ((v : R) * n₂)
      (((u * v : Rˣ) : R) * k) = affineCorrelation f n₁ n₂ k := by
  unfold affineCorrelation
  symm
  refine Fintype.sum_bijective _
    ((Units.mulLeft u).prodCongr (Units.mulLeft v)).bijective _ _ (fun p => ?_)
  change (if n₂ * p.1 - n₁ * p.2 = k then f p.1 * conj (f p.2) else 0) =
    if (v : R) * n₂ * ((u : R) * p.1) -
        (u : R) * n₁ * ((v : R) * p.2) = ((u * v : Rˣ) : R) * k then
      f ((u : R) * p.1) * conj (f ((v : R) * p.2)) else 0
  have hfactor : (v : R) * n₂ * ((u : R) * p.1) -
      (u : R) * n₁ * ((v : R) * p.2) =
        ((u * v : Rˣ) : R) * (n₂ * p.1 - n₁ * p.2) := by
    simp only [Units.val_mul]
    ring
  rw [hfactor, Units.mul_right_inj, hu, hv]

/-- Frequency invariance is a separate substitution, with columns fixed.
It is not inferred from joint covariance. -/
theorem affineCorrelation_frequency_unit_invariant (f : R → ℂ) (u : Rˣ)
    (hu : ∀ x, f ((u : R) * x) = f x) (n₁ n₂ k : R) :
    affineCorrelation f n₁ n₂ ((u : R) * k) =
      affineCorrelation f n₁ n₂ k := by
  unfold affineCorrelation
  symm
  refine Fintype.sum_bijective _
    ((Units.mulLeft u).prodCongr (Units.mulLeft u)).bijective _ _ (fun p => ?_)
  change (if n₂ * p.1 - n₁ * p.2 = k then f p.1 * conj (f p.2) else 0) =
    if n₂ * ((u : R) * p.1) - n₁ * ((u : R) * p.2) = (u : R) * k then
      f ((u : R) * p.1) * conj (f ((u : R) * p.2)) else 0
  have hfactor : n₂ * ((u : R) * p.1) - n₁ * ((u : R) * p.2) =
      (u : R) * (n₂ * p.1 - n₁ * p.2) := by ring
  rw [hfactor, Units.mul_right_inj, hu, hu]

/-- Exact Fourier factorization in the frequency variable. No primitivity,
coprimality, normalization factor, or discarded zero fibre is needed. -/
theorem fourier_affineCorrelation (ψ : AddChar R ℂ) (f : R → ℂ)
    (n₁ n₂ h : R) :
    fourier ψ (affineCorrelation f n₁ n₂) h =
      fourier ψ f (h * n₂) * conj (fourier ψ f (h * n₁)) := by
  unfold fourier affineCorrelation
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hfibre (p : R × R) :
      (∑ k : R, (if n₂ * p.1 - n₁ * p.2 = k then
        f p.1 * conj (f p.2) else 0) * ψ (h * k)) =
      f p.1 * conj (f p.2) * ψ (h * (n₂ * p.1 - n₁ * p.2)) := by
    simp [ite_mul]
  simp_rw [hfibre]
  rw [Fintype.sum_prod_type]
  simp only [map_sum, Finset.mul_sum, Finset.sum_mul, map_mul]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [show h * (n₂ * x - n₁ * y) =
    (h * n₂) * x + -((h * n₁) * y) by ring,
    ψ.map_add_eq_mul, ψ.map_neg_eq_conj]
  ring

end HeckeGeneral.Arithmetic.PeriodicFourier
