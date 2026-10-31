import HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceAssembly
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalFirstEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.WideMellinTests

/-!
# The genuine second conductor contributes its square-root norm weights

These factors are the exact primitive conductor norm, not unit phases.
They will be absorbed into a fixed positive-window Schwartz power test
with the corresponding scale normalization written explicitly.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondNormWeights

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
  HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CanonicalFirstEnergy PrimitivePoissonSource ConductorMasks FirstInversePoisson
  SecondSourceGauss
open HeckeSkeleton.Moments.MOMInvStep
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "e" => unitIdeal K S

theorem primitive_sqrt_inverse (x₁ x₂ : Ext) :
    (Real.sqrt ((primitiveIdeal (pairSupport K S D x₁ x₂ e e).support
      (pairExponent K S x₁ x₂ e e)).absNorm : ℝ) : ℂ)⁻¹ =
      normWeight K (ActualInverseFactors.residual K Sset x₁ x₂).val *
        normWeight K (ActualInverseFactors.residual K Sset x₂ x₁).val := by
  rw [primitive_conductor, Ideal.absNorm_mul, Nat.cast_mul,
    Real.sqrt_mul (by positivity)]
  simp only [normWeight, Complex.ofReal_mul, mul_inv]


theorem normWeight_eq_rpow (z : Ext) :
    normWeight K z.val = (((z.val.val.absNorm : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  rw [normWeight, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Complex.ofReal_inv]

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable {σ : Type*} [DecidableEq σ]

/-- The inverse square-root norm supplied by the true Poisson factor
is absorbed into an actual Schwartz test, with X^(-1/2) outside. -/
theorem sourceTerm_normWeight (Λ ν : HeckeCharacter K) (g j d₂ I : Ext) (ξ : Sector)
    (R : Ideal (𝓞 K)) (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 2 : ℝ) (5 / 2))
    (X : ℝ) (hX : 0 < X) (z : Ext) :
    normWeight K z.val *
      SecondCanonicalEnergy.sourceTerm K S Γ D Λ ν g j d₂ I ξ R slots lists a W X z =
      ((X ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        SecondCanonicalEnergy.sourceTerm K S Γ D Λ ν g j d₂ I ξ R slots lists a
          (WideMellinTests.powerTest W (-(1 / 2 : ℝ))) X z := by
  have hs : tsupport W ⊆ Set.Icc (1 / 4 : ℝ) (5 / 2) := by
    intro x hx
    have hb := hW hx
    exact ⟨by linarith [hb.1], hb.2⟩
  have hp := WideMellinTests.scaled_powerTest W (-(1 / 2 : ℝ))
    (z.val.val.absNorm : ℝ) X
    (by exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors z.val) hX hs
  rw [normWeight_eq_rpow]
  unfold SecondCanonicalEnergy.sourceTerm
  calc
    _ = (SecondOverlapColumns.forwardCoefficient K S Γ D Λ ν z
          (exteriorMul K Sset j d₂) I ξ *
        HeckeSkeleton.Moments.MOMInvStep.FixedTripleFibers.idealCoprimeMask
          (R * g.val.val) z.val.val *
        divisorMark slots lists a (g.val.val * z.val.val)) *
      (W ((z.val.val.absNorm : ℝ) / X) *
        (((z.val.val.absNorm : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by ring
    _ = _ := by rw [hp]; ring

theorem powerTest_support (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 2 : ℝ) (5 / 2)) :
    tsupport (WideMellinTests.powerTest W (-(1 / 2 : ℝ))) ⊆
      Set.Icc (1 / 2 : ℝ) (5 / 2) :=
  (WideMellinTests.powerTest_support W _).trans hW
end HeckeSkeleton.Moments.MOM_INV_STEP.SecondNormWeights

end
