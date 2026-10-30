import HeckeGeneral.Arithmetic.FiniteFourierConvolution

/-! SOURCE ONLY, UNRUN. Mixed-domain finite correlation with the installed
positive-sign unnormalized Fourier convention. The maps into the finite
ring need not be injective, surjective, linear, or unit multipliers.
Inverse normalization uses exactly card Q and an actual primitive AddChar;
no trace-character constructor or Gauss normalization is assumed. -/
noncomputable section
namespace HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical BigOperators ComplexConjugate
variable {Q X Y : Type*} [CommRing Q] [Fintype Q] [Fintype X] [Fintype Y]

/-- The genuine mixed-domain congruence sum, with all fibres retained. -/
def mixedCorrelation (α : X → Q) (β : Y → Q) (f : X → ℂ) (g : Y → ℂ)
    (j : Q) : ℂ :=
  ∑ p : X × Y, if α p.1 - β p.2 = j then f p.1 * conj (g p.2) else 0

theorem mixedCorrelation_eq_sum_fibre
    (α : X → Q) (β : Y → Q) (f : X → ℂ) (g : Y → ℂ) (j : Q) :
    mixedCorrelation α β f g j =
      ∑ p : {p : X × Y // α p.1 - β p.2 = j}, f p.val.1 * conj (g p.val.2) := by
  unfold mixedCorrelation
  rw [← Finset.sum_filter]
  simpa only [Finset.subtype_univ] using
    (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
      (p := fun p : X × Y => α p.1 - β p.2 = j)
      (fun p : X × Y => f p.1 * conj (g p.2))).symm

/-- Actual transforms of the two weighted maps, with the minus sign in
the second fibre coordinate converted to complex conjugation. -/
theorem fourier_mixedCorrelation
    (ψ : AddChar Q ℂ) (α : X → Q) (β : Y → Q)
    (f : X → ℂ) (g : Y → ℂ) (t : Q) :
    fourier ψ (mixedCorrelation α β f g) t =
      (∑ x : X, f x * ψ (t * α x)) *
        conj (∑ y : Y, g y * ψ (t * β y)) := by
  unfold fourier mixedCorrelation
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hfibre (p : X × Y) :
      (∑ j : Q, (if α p.1 - β p.2 = j then f p.1 * conj (g p.2) else 0) *
        ψ (t * j)) = f p.1 * conj (g p.2) * ψ (t * (α p.1 - β p.2)) := by
    simp [ite_mul]
  simp_rw [hfibre]
  rw [Fintype.sum_prod_type]
  simp only [map_sum, Finset.mul_sum, Finset.sum_mul, map_mul]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [show t * (α x - β y) = t * α x + -(t * β y) by ring,
    ψ.map_add_eq_mul, ψ.map_neg_eq_conj]
  ring

/-- Unnormalized inverse identity: the factor is card Q, not card X,
card Y, or their square root. It remains valid for the zero ring. -/
theorem mixedCorrelation_inversion_sum
    (ψ : AddChar Q ℂ) (hψ : ψ.IsPrimitive)
    (α : X → Q) (β : Y → Q) (f : X → ℂ) (g : Y → ℂ) (j : Q) :
    (∑ t : Q, ((∑ x : X, f x * ψ (t * α x)) *
      conj (∑ y : Y, g y * ψ (t * β y))) * ψ (-(t * j))) =
        (Fintype.card Q : ℂ) * mixedCorrelation α β f g j := by
  simpa only [fourier_mixedCorrelation] using
    inversion_sum ψ hψ (mixedCorrelation α β f g) j

/-- The normalized inverse, with the opposite additive sign. -/
theorem mixedCorrelation_eq_inverse_sum
    (ψ : AddChar Q ℂ) (hψ : ψ.IsPrimitive)
    (α : X → Q) (β : Y → Q) (f : X → ℂ) (g : Y → ℂ) (j : Q) :
    mixedCorrelation α β f g j =
      (Fintype.card Q : ℂ)⁻¹ *
        ∑ t : Q, ((∑ x : X, f x * ψ (t * α x)) *
          conj (∑ y : Y, g y * ψ (t * β y))) * ψ (-(t * j)) := by
  simpa only [inverse, fourier_mixedCorrelation] using
    (inverse_fourier ψ hψ (mixedCorrelation α β f g) j).symm
end HeckeGeneral.Arithmetic.PeriodicFourier
