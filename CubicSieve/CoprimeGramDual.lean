import CubicSieve.CoprimeGram
import CubicSieve.AnalyticDualNorm

/-! The actual all-ideal dual norm controls the coprime-column Gram mass.
Only the proved finite support epsilon loss is added.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.CoprimeGramDual

open NumberField IsDedekindDomain
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CubicSieve.ExteriorKernel CubicSieve.AnalyticDualNorm
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem subtype_family_bound (M N : ℝ) (R T : Finset (ExteriorIdeal K S))
    (hR : ∀ I ∈ R, exteriorNorm K S I ≤ M)
    (hT : ∀ J ∈ T, Squarefree J.val.val ∧ exteriorNorm K S J ≤ N)
    (x : ↥T → ℂ) :
    (∑ i : R, ‖∑ j : T, positiveKernel K S D i.val j.val * x j‖ ^ 2) ≤
      U K S D M N * ∑ j : T, ‖x j‖ ^ 2 := by
  let z : ExteriorIdeal K S → ℂ := fun J => if hJ : J ∈ T then x ⟨J, hJ⟩ else 0
  have hh := family_bound K S D M N R T hR hT z
  have he (I : ExteriorIdeal K S) :
      (∑ J ∈ T, positiveKernel K S D I J * z J) =
        ∑ j : T, positiveKernel K S D I j.val * x j := by
    rw [← Finset.sum_coe_sort T (fun J => positiveKernel K S D I J * z J)]
    apply Finset.sum_congr rfl
    intro j _
    simp only [z, dif_pos j.property]
  have henergy : (∑ J ∈ T, ‖z J‖ ^ 2) = ∑ j : T, ‖x j‖ ^ 2 := by
    rw [← Finset.sum_coe_sort T (fun J => ‖z J‖ ^ 2)]
    apply Finset.sum_congr rfl
    intro j _
    simp only [z, dif_pos j.property]
  simp only [FiniteKernel.HasBound, FiniteKernel.form, FiniteKernel.energy] at hh
  rw [henergy] at hh
  simp_rw [he] at hh
  rw [Finset.sum_coe_sort R
    (fun I => ‖∑ j : T, positiveKernel K S D I j.val * x j‖ ^ 2)]
  exact hh

theorem coprime_family_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ N →
      ∀ R T : Finset (ExteriorIdeal K S),
      (∀ I ∈ R, exteriorNorm K S I ≤ M) →
      (∀ J ∈ T, Squarefree J.val.val ∧ exteriorNorm K S J ≤ N) →
      ∀ z : ↥T → ℂ,
        (∑ i : R, ‖CoprimeGram.pairRow K S D
          (fun i : R => i.val) (fun j : T => j.val) z i‖) ≤
            U K S D M N * C * N ^ ε * ∑ j : T, ‖z j‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := CoprimeGram.pairRow_bound K S D ε hε
  refine ⟨C, hC, ?_⟩
  intro M N hN R T hR hT z
  exact hb (fun i : R => i.val) (fun j : T => j.val) N (U K S D M N)
    hN (U_nonneg K S D M N) (fun j => (hT j.val j.property).2)
    (subtype_family_bound K S D M N R T hR hT) z

end CubicSieve.CoprimeGramDual
