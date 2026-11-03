import HeckeGeneral.Analysis.HeckeContinuation
import HeckeGeneral.Analysis.HeckeEulerProduct
import HeckeGeneral.Arithmetic.IdealMobiusMask
import HeckeGeneral.Analysis.IdealSquarefreeSupport

/-!
The actual ideal Moebius--Hecke series on Re(s)>1.
This module proves its Euler identity rather than assuming it.
No assertion about continuation to Re(s)<=1 is made.
-/

noncomputable section

namespace HeckeGeneral.Analysis.IdealMobiusReciprocal

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Arithmetic.IdealMobiusMask
open scoped BigOperators Classical nonZeroDivisors Topology

variable (K : Type) [Field K] [NumberField K]

abbrev squarefreeIdeal := SquarefreeAmplification.squarefreeIdeal K

theorem squarefreeIdeal_injective : Function.Injective (squarefreeIdeal K) := by
  exact SquarefreeAmplification.squarefreeIdeal_injective K

theorem exists_squarefreeIdeal (I : NonzeroIdeal K) (hI : Squarefree I.val) :
    ∃ S, squarefreeIdeal K S = I := by
  exact ⟨SquarefreeAmplification.idealPrimeSupport K I,
    SquarefreeAmplification.squarefreeIdeal_primeSupport K I hI⟩

def coefficient (a : HeightOneSpectrum (𝓞 K) → ℂ) (I : NonzeroIdeal K) : ℂ :=
  (moebius I.val : ℂ) * nonzeroIdealCoefficient a I

def term (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) (I : NonzeroIdeal K) : ℂ :=
  dirichletTerm (idealNorm K) (coefficient K a) s I

theorem norm_moebius_le_one (I : NonzeroIdeal K) : ‖(moebius I.val : ℂ)‖ ≤ 1 := by
  by_cases hI : Squarefree I.val
  · rw [hI.moebius_eq, Int.cast_pow]
    simp
  · rw [moebius_of_not_squarefree hI]
    norm_num

theorem norm_coefficient_le_one (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) (I : NonzeroIdeal K) : ‖coefficient K a I‖ ≤ 1 := by
  rw [coefficient, norm_mul]
  calc
    _ ≤ 1 * 1 := mul_le_mul (norm_moebius_le_one K I)
      (norm_nonzeroIdealCoefficient_le_one a ha I) (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

theorem absolutelySummable (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I => ‖term K a s I‖) :=
  absolutelySummable_idealDirichlet K _ (norm_coefficient_le_one K a ha) hs

theorem term_squarefreeIdeal (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    term K a s (squarefreeIdeal K S) = ∏ p ∈ S, -primeIdealRatio K a s p := by
  have hw : idealEulerWeight K a s (primeProduct S) = ∏ p ∈ S, primeIdealRatio K a s p := by
    change idealEulerWeightHom K a s (∏ p ∈ S, p.asIdeal) = _
    rw [map_prod]
    exact Finset.prod_congr rfl (fun p _ => idealEulerWeight_prime K a s p)
  rw [Finset.prod_neg, ← hw]
  change (moebius (primeProduct S) : ℂ) *
      nonzeroIdealCoefficient a (squarefreeIdeal K S) *
      (idealNorm K (squarefreeIdeal K S) : ℂ) ^ (-s) = _
  rw [moebius_primeProduct, Int.cast_pow]
  simp only [Int.cast_neg, Int.cast_one]
  rw [mul_assoc]
  congr 1

/-- Every finite Euler polynomial equals the actual squarefree-ideal sum. -/
theorem finite_euler_polynomial (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (∏ p ∈ S, (1 - primeIdealRatio K a s p)) =
      ∑ T ∈ S.powerset, term K a s (squarefreeIdeal K T) := by
  simp_rw [term_squarefreeIdeal, sub_eq_add_neg]
  exact Finset.prod_one_add S

theorem term_eq_zero_outside (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ)
    (I : NonzeroIdeal K) (hI : I ∉ Set.range (squarefreeIdeal K)) : term K a s I = 0 := by
  have hns : ¬Squarefree I.val := by
    intro hs
    obtain ⟨S, hS⟩ := exists_squarefreeIdeal K I hs
    exact hI ⟨S, hS⟩
  simp [term, coefficient, dirichletTerm, moebius_of_not_squarefree hns]

theorem hasProd_moebius_series (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p => 1 - primeIdealRatio K a s p) (∑' I, term K a s I) := by
  have hsum :
      HasSum (fun S => term K a s (squarefreeIdeal K S)) (∑' I, term K a s I) ↔
      HasSum (term K a s) (∑' I, term K a s I) :=
    (squarefreeIdeal_injective K).hasSum_iff
    (fun I hI => term_eq_zero_outside K a s I hI)
  have h : HasSum (fun S => ∏ p ∈ S, -primeIdealRatio K a s p)
      (∑' I, term K a s I) := by
    apply HasSum.congr_fun ((hsum).mpr (absolutelySummable K a ha hs).of_norm.hasSum)
    intro S
    exact (term_squarefreeIdeal K a s S).symm
  simpa only [sub_eq_add_neg] using hasProd_one_add_of_hasSum_prod h

theorem moebius_series_eq_inverse (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    (∑' I, term K a s I) =
      (idealDirichletSeries K (nonzeroIdealCoefficient a) s)⁻¹ := by
  have h := (hasProd_idealDirichletSeries K a ha hs).inv₀
    (idealDirichletSeries_ne_zero K a ha hs)
  simp only [inv_inv] at h
  exact (hasProd_moebius_series K a ha hs).unique h

/-- The actual Moebius--Hecke ideal series equals the reciprocal of the
genuine meromorphic continuation on its convergence half-plane. -/
theorem hecke_moebius_series_eq_reciprocal (χ : HeckeCharacter K)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' I : NonzeroIdeal K,
      (moebius I.val : ℂ) * heckeIdealCoefficient K χ I *
        (idealNorm K I : ℂ) ^ (-s)) = (heckeContinuation K χ s)⁻¹ := by
  rw [heckeContinuation_eq_series K χ hs]
  exact moebius_series_eq_inverse K (primeCoefficient K χ)
    (norm_primeCoefficient_le_one K χ) hs

end HeckeGeneral.Analysis.IdealMobiusReciprocal
