import HeckeGeneral.Analysis.GlobalThetaData
import HeckeSkeleton.LowEnergy.GaussianReconstruction
import HeckeSkeleton.LowEnergy.GaussianSeminorm
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Gaussian annuli for the literal completed theta series

This adapter uses the original project types and definitions.  Its imports
are the actual global theta data and the independently checked Gaussian
partition and Euler-seminorm proofs.

The only analytic hypothesis is absolute convergence of the original
Gaussian completed series. The target project proves this in
ActualProbeThetaAbsolute. No reflected-energy inequality is assumed here.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GaussianTheta

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.Gaussian
open scoped BigOperators Classical ContDiff

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

def annulusTest (k : ℤ) : SmoothAnnularTest where
  toFun := annulus k
  smooth := annulus_smooth k
  lower := Real.exp (-1)
  upper := Real.exp 1
  lower_pos := Real.exp_pos _
  upper_ge := Real.exp_le_exp.mpr (by norm_num)
  support := annulus_support k

/-- The verified seminorm is definitionally the project's actual Euler
seminorm. No replacement seminorm or comparison hypothesis is introduced. -/
theorem testIntegral_annulus (k : ℤ) (j : ℕ) (A : ℝ) :
    testIntegral (annulusTest k).toFun j A =
      GaussianSeminorm.integralSeminorm k j A := rfl

theorem testSeminorm_annulus (k : ℤ) (J : ℕ) (A : ℝ) :
    testSeminorm (annulusTest k).toFun J A =
      GaussianSeminorm.seminorm k J A := rfl

/-- Every fixed exponential weight of the actual annular test seminorm
is summable, including all Gaussian annuli outside any central range. -/
theorem summable_exp_mul_testSeminorm (J : ℕ) (A E : ℝ) :
    Summable (fun k : ℤ => Real.exp (E * |(k : ℝ)|) *
      testSeminorm (annulusTest k).toFun J A) :=
  GaussianSeminorm.summable_exp_mul_seminorm J A E

theorem exteriorNorm_positive (I : ExteriorIdeal K S) : 0 < exteriorNorm K S I := by
  change (0 : ℝ) < (I.val.val.absNorm : ℝ)
  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I.val

theorem completedTerm_annulus (θ : HeckeCharacter K) (m : S.integer K)
    (r : ExteriorIdeal K S) (Q : Finset (ExteriorPrime K S))
    {X : ℝ} (hX : 0 < X) (k : ℤ) (cn : ExteriorIdeal K S × ExteriorIdeal K S) :
    completedTerm K S D θ m r Q (annulusTest k).toFun (X * Real.exp (k : ℝ)) cn =
      completedTerm K S D θ m r Q logGaussianProfile X cn *
        (fixedIntegerCutoff
          (Real.log (exteriorNorm K S (completedIdeal K S cn.1 cn.2) / X) - k) : ℂ) := by
  have hscale : exteriorNorm K S (completedIdeal K S cn.1 cn.2) /
      (X * Real.exp (k : ℝ)) =
        (exteriorNorm K S (completedIdeal K S cn.1 cn.2) / X) / Real.exp (k : ℝ) := by
    ring
  have hratio : 0 < exteriorNorm K S (completedIdeal K S cn.1 cn.2) / X :=
    div_pos (exteriorNorm_positive K S _) hX
  simp only [completedTerm, annulusTest]
  split_ifs
  · rw [hscale, annulus_rescale k hratio]
    ring
  · simp

/-- Absolute convergence of the original series supplies convergence of
the annular outer series; no extra Fubini assumption is needed. -/
theorem completedThetaSum_annuli_summable (θ : HeckeCharacter K) (m : S.integer K)
    (r : ExteriorIdeal K S) (Q : Finset (ExteriorPrime K S))
    {X : ℝ} (hX : 0 < X)
    (habs : Summable (completedTerm K S D θ m r Q logGaussianProfile X)) :
    Summable (fun k : ℤ =>
      completedThetaSum K S D θ m r Q (annulusTest k).toFun (X * Real.exp (k : ℝ))) := by
  let x (cn : ExteriorIdeal K S × ExteriorIdeal K S) :=
    Real.log (exteriorNorm K S (completedIdeal K S cn.1 cn.2) / X)
  have h := split_outer_summable
    (completedTerm K S D θ m r Q logGaussianProfile X) x habs.norm
  simpa only [completedThetaSum, completedTerm_annulus K S D θ m r Q hX] using h

/-- Exact reconstruction of the literal theta sum from fixed-support
smooth annuli, with the genuine completed scale `X * exp(k)`. -/
theorem completedThetaSum_gaussian_annuli (θ : HeckeCharacter K) (m : S.integer K)
    (r : ExteriorIdeal K S) (Q : Finset (ExteriorPrime K S))
    {X : ℝ} (hX : 0 < X)
    (habs : Summable (completedTerm K S D θ m r Q logGaussianProfile X)) :
    completedThetaSum K S D θ m r Q logGaussianProfile X =
      ∑' k : ℤ, completedThetaSum K S D θ m r Q
        (annulusTest k).toFun (X * Real.exp (k : ℝ)) := by
  let x (cn : ExteriorIdeal K S × ExteriorIdeal K S) :=
    Real.log (exteriorNorm K S (completedIdeal K S cn.1 cn.2) / X)
  have h := split_series_tsum
    (completedTerm K S D θ m r Q logGaussianProfile X) x habs.norm
  simpa only [completedThetaSum, completedTerm_annulus K S D θ m r Q hX] using h

/-- Surviving marks are kept inside the row before the outer annular sum.
The completed scale may depend on the actual prime tuple. -/
theorem finite_marked_gaussian_annuli {ι : Type*} (tuples : Finset ι)
    (weight : ι → ℂ) (θ : HeckeCharacter K) (m : S.integer K)
    (r : ExteriorIdeal K S) (marks : ι → Finset (ExteriorPrime K S)) (X : ι → ℝ)
    (hX : ∀ p ∈ tuples, 0 < X p)
    (habs : ∀ p ∈ tuples,
      Summable (completedTerm K S D θ m r (marks p) logGaussianProfile (X p))) :
    (∑ p ∈ tuples, weight p *
      completedThetaSum K S D θ m r (marks p) logGaussianProfile (X p)) =
      ∑' k : ℤ, ∑ p ∈ tuples, weight p *
        completedThetaSum K S D θ m r (marks p)
          (annulusTest k).toFun (X p * Real.exp (k : ℝ)) := by
  calc
    _ = ∑ p ∈ tuples, ∑' k : ℤ, weight p *
        completedThetaSum K S D θ m r (marks p)
          (annulusTest k).toFun (X p * Real.exp (k : ℝ)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [completedThetaSum_gaussian_annuli K S D θ m r (marks p) (hX p hp) (habs p hp),
        tsum_mul_left]
    _ = _ := by
      symm
      apply Summable.tsum_finsetSum
      intro p hp
      exact (completedThetaSum_annuli_summable K S D θ m r (marks p)
        (hX p hp) (habs p hp)).mul_left (weight p)

end HeckeSkeleton.LowEnergy.GaussianTheta
