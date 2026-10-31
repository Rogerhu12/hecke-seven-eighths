import FiniteAffineCorrelationBound
import Mathlib.GroupTheory.Coset.Basic

/-! Source-only, uncompiled. Surjective quotient transport of the genuine
affine correlation. Every additive fibre contributes its actual kernel size. -/
noncomputable section
namespace HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical BigOperators ComplexConjugate

variable {R T : Type*} [CommRing R] [CommRing T] [Fintype R] [Fintype T]

/-- Surjectivity identifies every additive fibre with the actual kernel;
no equal-fibre-cardinality hypothesis is needed. -/
theorem sum_comp_surjective_ringHom (π : R →+* T) (hπ : Function.Surjective π)
    (g : T → ℂ) :
    (∑ x : R, g (π x)) =
      (Nat.card π.toAddMonoidHom.ker : ℂ) * ∑ y : T, g y := by
  have hcard (y : T) : Fintype.card {x : R // π x = y} =
      Nat.card π.toAddMonoidHom.ker := by
    let e : {x : R // π x = y} ≃ π.toAddMonoidHom.ker :=
      AddMonoidHom.fiberEquivKerOfSurjective (f := π.toAddMonoidHom) hπ y
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr e
  rw [← Fintype.sum_fiberwise' π g]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  rw [Finset.mul_sum]

/-- Map the same Bezout coefficients on both sides. This works for zero
frequency, zero rings, nonunit columns and arbitrary zero-extended weights. -/
theorem affineCorrelation_comp_surjective_ringHom
    (π : R →+* T) (hπ : Function.Surjective π) (f : T → ℂ)
    (n₁ n₂ k : R) (hn : IsCoprime n₁ n₂) :
    affineCorrelation (fun x => f (π x)) n₁ n₂ k =
      (Nat.card π.toAddMonoidHom.ker : ℂ) *
        affineCorrelation f (π n₁) (π n₂) (π k) := by
  obtain ⟨a, b, hab⟩ := hn
  have hbez : b * n₂ - (-a) * n₁ = 1 := by
    calc
      _ = a * n₁ + b * n₂ := by ring
      _ = 1 := hab
  have hmap : π b * π n₂ - π (-a) * π n₁ = 1 := by
    simpa only [map_sub, map_mul, map_one] using congrArg π hbez
  rw [affineCorrelation_eq_sum_parameter _ n₁ n₂ b (-a) hbez k,
    affineCorrelation_eq_sum_parameter f (π n₁) (π n₂) (π b) (π (-a)) hmap (π k)]
  simpa only [map_add, map_mul] using
    sum_comp_surjective_ringHom π hπ
      (fun t => f (π b * π k + π n₁ * t) *
        conj (f (π (-a) * π k + π n₂ * t)))

end HeckeGeneral.Arithmetic.PeriodicFourier
