import CubicSieve.OrbitKernel
import CubicSieve.AnalyticDualNorm

/-! The all-sector orbital operator is controlled by the actual ideal dual
operator, with exactly one fixed finite sixth-unit-class cost.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.OrbitDualNorm

open NumberField IsDedekindDomain
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.Arithmetic
open CubicSieve.OrbitRows CubicSieve.OrbitKernel CubicSieve.ExteriorKernel
open CubicSieve.AnalyticDualNorm
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

local instance classesFintype : Fintype (SixthUnitClasses K S) := Fintype.ofFinite _

theorem orbital_family_bound (M N : ℝ) (R : Finset (Orbits K S))
    (T : Finset (ExteriorIdeal K S))
    (hR : ∀ q ∈ R, (sIntegerOrbitNorm K S (Γ K S) q).val ≤ M)
    (hT : ∀ J ∈ T, Squarefree J.val.val ∧ exteriorNorm K S J ≤ N)
    (z : ExteriorIdeal K S → ℂ) :
    (∑ q ∈ R, ‖∑ J ∈ T, coefficient K S D J q * z J‖ ^ 2) ≤
      (Nat.card (SixthUnitClasses K S) : ℝ) * U K S D M N * ∑ J ∈ T, ‖z J‖ ^ 2 := by
  let e := orbitEquiv K S D
  let F : ExteriorIdeal K S × SixthUnitClasses K S → ℝ := fun p =>
    ‖∑ J ∈ T, positiveKernel K S D p.1 J * (unitPhase K S D p.2 J * z J)‖ ^ 2
  have hF (p) : 0 ≤ F p := sq_nonneg _
  have hsub : R.image e.symm ⊆ (fullCutoff K S M).product Finset.univ := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    apply Finset.mem_product.mpr
    refine ⟨(mem_fullCutoff K S M _).mpr ?_, Finset.mem_univ _⟩
    have he : q = scalarOrbit K S D (e.symm q).1 (e.symm q).2.out :=
      (e.apply_symm_apply q).symm
    have hn := hR q hq
    rw [he, scalarOrbit_norm] at hn
    exact hn
  have hsum : (∑ q ∈ R, ‖∑ J ∈ T, coefficient K S D J q * z J‖ ^ 2) =
      ∑ p ∈ R.image e.symm, F p := by
    rw [Finset.sum_image (fun q _ q' _ h => e.symm.injective h)]
    apply Finset.sum_congr rfl
    intro q hq
    rcases hp : e.symm q with ⟨I, l⟩
    have he : q = classOrbit K S D (I, l) := by
      have hh := e.apply_symm_apply q
      rw [hp] at hh
      exact hh.symm
    conv_lhs => rw [he]
    simp only [coefficient_classOrbit]
    dsimp only [F]
    congr 2
    apply Finset.sum_congr rfl
    intro J _
    ring
  have hsector (l : SixthUnitClasses K S) :
      (∑ I ∈ fullCutoff K S M, F (I, l)) ≤ U K S D M N * ∑ J ∈ T, ‖z J‖ ^ 2 := by
    have hh := family_bound K S D M N (fullCutoff K S M) T
      (fun I hI => (mem_fullCutoff K S M I).mp hI) hT
      (fun J => unitPhase K S D l J * z J)
    simpa only [FiniteKernel.HasBound, FiniteKernel.form, FiniteKernel.energy,
      F, norm_mul, unitPhase_norm, one_mul] using hh
  calc
    _ = ∑ p ∈ R.image e.symm, F p := hsum
    _ ≤ ∑ p ∈ (fullCutoff K S M).product Finset.univ, F p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hF p)
    _ = ∑ l : SixthUnitClasses K S, ∑ I ∈ fullCutoff K S M, F (I, l) := by
      exact (Finset.sum_product (fullCutoff K S M)
        (Finset.univ : Finset (SixthUnitClasses K S)) F).trans Finset.sum_comm
    _ ≤ ∑ _l : SixthUnitClasses K S, U K S D M N * ∑ J ∈ T, ‖z J‖ ^ 2 :=
      Finset.sum_le_sum (fun l _ => hsector l)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.card_eq_fintype_card]; ring

end CubicSieve.OrbitDualNorm
