import HeckeGeneral.Analysis.HeckeEulerDeletion
import HeckeGeneral.Analysis.HeckeSeries
import Mathlib.Tactic

/-!
Uniform bounds for actual fixed finite Hecke Euler deletions.
The coefficients are the actual primeCoefficient, including ramified zeros,
and the norms are the actual residueCard. Every continuous unitary character
is allowed. A numerator deletion polynomial may vanish at Re(w)=0; it is
never inverted there. Only the positive-half-plane denominator is inverted.

The final transfer is an identity/bound for the existing deleted continuation
definition. It does not assert its equality with an initial physical Euler
series or calibrate a moving finite correction table.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HeckeDeletedEulerControl

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

def deletionUpperConstant (S : Finset (HeightOneSpectrum (𝓞 K))) : ℝ :=
  ∏ p ∈ S, (1 + (residueCard K p : ℝ) ^ (1 / 1000 : ℝ))

def deletionInverseConstant (S : Finset (HeightOneSpectrum (𝓞 K))) : ℝ :=
  ∏ p ∈ S, (1 - (residueCard K p : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹

private theorem residueCard_gt_one (p : HeightOneSpectrum (𝓞 K)) :
    (1 : ℝ) < residueCard K p := by exact_mod_cast one_lt_residueCard K p

private theorem local_margin_pos (p : HeightOneSpectrum (𝓞 K)) :
    0 < 1 - (residueCard K p : ℝ) ^ (-(1 / 2 : ℝ)) := by
  exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg
    (residueCard_gt_one K p) (by norm_num))

theorem deletionUpperConstant_pos (S : Finset (HeightOneSpectrum (𝓞 K))) :
    0 < deletionUpperConstant K S := by
  apply Finset.prod_pos
  intro p _
  have hq : 0 < (residueCard K p : ℝ) := zero_lt_one.trans (residueCard_gt_one K p)
  exact add_pos_of_pos_of_nonneg zero_lt_one (Real.rpow_nonneg hq.le _)

theorem deletionInverseConstant_pos (S : Finset (HeightOneSpectrum (𝓞 K))) :
    0 < deletionInverseConstant K S := by
  exact Finset.prod_pos (fun p _ => inv_pos.mpr (local_margin_pos K p))

private theorem norm_actual_primeTerm_le
    (χ : HeckeCharacter K) (p : HeightOneSpectrum (𝓞 K))
    (σ : ℝ) (s : ℂ) (hs : σ ≤ s.re) :
    ‖primeCoefficient K χ p * (residueCard K p : ℂ) ^ (-s)‖ ≤
      (residueCard K p : ℝ) ^ (-σ) := by
  have hq := residueCard_gt_one K p
  have hqpos : 0 < (residueCard K p : ℝ) := zero_lt_one.trans hq
  have hcast : (residueCard K p : ℂ) = ((residueCard K p : ℝ) : ℂ) := by simp
  rw [norm_mul, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hqpos, Complex.neg_re]
  calc
    ‖primeCoefficient K χ p‖ * (residueCard K p : ℝ) ^ (-s.re) ≤
        1 * (residueCard K p : ℝ) ^ (-s.re) :=
      mul_le_mul_of_nonneg_right (norm_primeCoefficient_le_one K χ p)
        (Real.rpow_nonneg hqpos.le _)
    _ ≤ (residueCard K p : ℝ) ^ (-σ) := by
      simpa only [one_mul] using
        Real.rpow_le_rpow_of_exponent_le hq.le (neg_le_neg hs)

/-- The actual numerator local polynomial needs only a lower real bound.
In particular no nonvanishing assertion is imposed at w=0. -/
theorem norm_actual_eulerPolynomial_le
    (χ : HeckeCharacter K) (p : HeightOneSpectrum (𝓞 K)) (w : ℂ)
    (hw : -(1 / 1000 : ℝ) ≤ w.re) :
    ‖eulerPolynomial (residueCard K p) (primeCoefficient K χ p) w‖ ≤
      1 + (residueCard K p : ℝ) ^ (1 / 1000 : ℝ) := by
  have ht := norm_actual_primeTerm_le K χ p (-(1 / 1000 : ℝ)) w hw
  simp only [neg_neg] at ht
  have hn := norm_sub_le (1 : ℂ)
    (primeCoefficient K χ p * (residueCard K p : ℂ) ^ (-w))
  rw [norm_one] at hn
  simpa only [eulerPolynomial, Complex.ofReal_natCast] using
    hn.trans (add_le_add (le_refl 1) ht)

/-- The genuine local Euler factor is uniformly bounded on Re(s)>=1/2. -/
theorem norm_actual_localEulerFactor_le
    (χ : HeckeCharacter K) (p : HeightOneSpectrum (𝓞 K)) (s : ℂ)
    (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖heckeLocalEulerFactor K χ p s‖ ≤
      (1 - (residueCard K p : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ := by
  have ht := norm_actual_primeTerm_le K χ p (1 / 2) s hs
  have hn := norm_sub_norm_le (1 : ℂ)
    (primeCoefficient K χ p * (residueCard K p : ℂ) ^ (-s))
  rw [norm_one] at hn
  have hlow : 1 - (residueCard K p : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      ‖eulerPolynomial (residueCard K p) (primeCoefficient K χ p) s‖ := by
    simp only [eulerPolynomial, Complex.ofReal_natCast]
    linarith
  rw [heckeLocalEulerFactor, norm_inv]
  exact inv_anti₀ (local_margin_pos K p) hlow

theorem norm_heckeEulerDeletionPolynomial_le
    (S : Finset (HeightOneSpectrum (𝓞 K))) (χ : HeckeCharacter K)
    (w : ℂ) (hw : -(1 / 1000 : ℝ) ≤ w.re) :
    ‖heckeEulerDeletionPolynomial K χ S w‖ ≤ deletionUpperConstant K S := by
  unfold heckeEulerDeletionPolynomial finiteEulerPolynomial deletionUpperConstant
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun p _ => norm_actual_eulerPolynomial_le K χ p w hw)

/-- This is an exact identity of the existing actual local factors. -/
theorem deletionPolynomial_inv_eq_prod_localEulerFactors
    (S : Finset (HeightOneSpectrum (𝓞 K))) (χ : HeckeCharacter K) (s : ℂ) :
    (heckeEulerDeletionPolynomial K χ S s)⁻¹ =
      ∏ p ∈ S, heckeLocalEulerFactor K χ p s := by
  unfold heckeEulerDeletionPolynomial finiteEulerPolynomial heckeLocalEulerFactor
  rw [← Finset.prod_inv_distrib]

theorem norm_heckeEulerDeletionPolynomial_inv_le
    (S : Finset (HeightOneSpectrum (𝓞 K))) (χ : HeckeCharacter K)
    (s : ℂ) (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖(heckeEulerDeletionPolynomial K χ S s)⁻¹‖ ≤ deletionInverseConstant K S := by
  rw [deletionPolynomial_inv_eq_prod_localEulerFactors, norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun p _ => norm_actual_localEulerFactor_le K χ p s hs)

/-- The requested constants are chosen before both actual characters and
both arguments; the numerator strip includes the zero real-part line. -/
theorem exists_uniform_fixedDeletion_bounds
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ η : HeckeCharacter K) (w s : ℂ),
      (-(1 / 1000 : ℝ) ≤ w.re ∧ w.re ≤ 1 / 2) → (1 / 2 : ℝ) ≤ s.re →
      ‖heckeEulerDeletionPolynomial K χ S w‖ ≤ C ∧
      ‖(heckeEulerDeletionPolynomial K η S s)⁻¹‖ ≤ C := by
  refine ⟨max (deletionUpperConstant K S) (deletionInverseConstant K S),
    (deletionUpperConstant_pos K S).trans_le (le_max_left _ _), ?_⟩
  intro χ η w s hw hs
  exact ⟨(norm_heckeEulerDeletionPolynomial_le K S χ w hw.1).trans (le_max_left _ _),
    (norm_heckeEulerDeletionPolynomial_inv_le K S η s hs).trans (le_max_right _ _)⟩

/-- Transfer an actual full-L ratio bound to its existing fixed-S deleted
continuations. No initial-series or moving Euler-table calibration is used. -/
theorem exists_uniform_deletedL_ratio_transfer
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ η : HeckeCharacter K) (w s : ℂ),
      (-(1 / 1000 : ℝ) ≤ w.re ∧ w.re ≤ 1 / 2) → (1 / 2 : ℝ) ≤ s.re →
      ‖heckeDeletedContinuation K χ S w‖ * ‖(heckeDeletedContinuation K η S s)⁻¹‖ ≤
        C * (‖heckeContinuation K χ w‖ * ‖(heckeContinuation K η s)⁻¹‖) := by
  refine ⟨deletionUpperConstant K S * deletionInverseConstant K S,
    mul_pos (deletionUpperConstant_pos K S) (deletionInverseConstant_pos K S), ?_⟩
  intro χ η w s hw hs
  simp only [heckeDeletedContinuation, mul_inv, norm_mul]
  calc
    _ = (‖heckeEulerDeletionPolynomial K χ S w‖ *
          ‖(heckeEulerDeletionPolynomial K η S s)⁻¹‖) *
        (‖heckeContinuation K χ w‖ * ‖(heckeContinuation K η s)⁻¹‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul (norm_heckeEulerDeletionPolynomial_le K S χ w hw.1)
        (norm_heckeEulerDeletionPolynomial_inv_le K S η s hs)
        (norm_nonneg _) (deletionUpperConstant_pos K S).le)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))

end HeckeSkeleton.HeckeDeletedEulerControl
