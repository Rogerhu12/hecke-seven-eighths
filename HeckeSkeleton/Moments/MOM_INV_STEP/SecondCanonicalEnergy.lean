import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalMarkRestoration
import HeckeSkeleton.Moments.MOM_INV_STEP.FullMobius

/-!
# The actual fixed-common second source

The original common ideal stays fixed when mutual residual coprimality
is expanded. The source term below retains its literal forward
coefficient, original mark weights, puncture and norm cutoff.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondCanonicalEnergy

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
  HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers SecondOverlapColumns CommonKernel FullMobius
open scoped Classical BigOperators FourierTransform nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

variable {σ : Type*} [DecidableEq σ]

def sourceTerm (Λ ν : HeckeCharacter K) (g j d₂ I : Ext) (ξ : Sector)
    (R : Ideal (𝓞 K)) (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (W : ℝ → ℂ) (X : ℝ) (z : Ext) : ℂ :=
  forwardCoefficient K S Γ D Λ ν z (exteriorMul K Sset j d₂) I ξ *
    idealCoprimeMask (R * g.val.val) z.val.val *
    divisorMark slots lists a (g.val.val * z.val.val) *
    W ((z.val.val.absNorm : ℝ) / X)

theorem sourceTerm_zero (Λ ν : HeckeCharacter K) (g j d₂ I : Ext) (ξ : Sector)
    (R : Ideal (𝓞 K)) (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (W : ℝ → ℂ) (X : ℝ) (z : Ext)
    (hc : ¬IsCoprime g.val.val z.val.val) :
    sourceTerm K S Γ D Λ ν g j d₂ I ξ R slots lists a W X z = 0 := by
  have hbad : ¬IsCoprime z.val.val (R * g.val.val) := by
    intro h
    exact hc ((IsCoprime.mul_right_iff.mp h).2.symm)
  simp only [sourceTerm, idealCoprimeMask, if_neg hbad, mul_zero, zero_mul]

/-- The full mutual-gcd extension and both positive columns are proved
for the actual source coefficients. The normalized log kernel is one
Schwartz function shared by the two columns before Cauchy. -/
theorem full_source_energy (Λ ν : HeckeCharacter K) (g j d₂ I : Ext) (ξ : Sector)
    (R : Ideal (𝓞 K)) (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (W : ℝ → ℂ) (X : ℝ)
    (T : Finset Ext) (F : SchwartzMap LogPlane ℂ) :
    ‖∑ z₁ ∈ T, ∑ z₂ ∈ T, if IsCoprime z₁.val.val z₂.val.val then
      star (sourceTerm K S Γ D Λ ν g j d₂ I ξ R slots lists a W X z₁) *
        sourceTerm K S Γ D Λ ν g j d₂ I ξ R slots lists a W X z₂ *
        F (logPoint (Real.log ((z₁.val.val.absNorm : ℝ) / X))
          (Real.log ((z₂.val.val.absNorm : ℝ) / X))) else 0‖ ≤
      Real.sqrt (∑ v ∈ divisorPool T (fun z => z.val.val),
        ‖(UniqueFactorizationMonoid.moebius v : ℂ)‖ *
          ∫ τ : LogPlane, ‖(𝓕 F) τ‖ *
            ‖∑ z ∈ T with v ∣ z.val.val,
              star (sourceTerm K S Γ D Λ ν g j d₂ I ξ R slots lists a W X z) *
                columnPhase τ.fst (Real.log ((z.val.val.absNorm : ℝ) / X))‖ ^ 2) *
      Real.sqrt (∑ v ∈ divisorPool T (fun z => z.val.val),
        ‖(UniqueFactorizationMonoid.moebius v : ℂ)‖ *
          ∫ τ : LogPlane, ‖(𝓕 F) τ‖ *
            ‖∑ z ∈ T with v ∣ z.val.val,
              sourceTerm K S Γ D Λ ν g j d₂ I ξ R slots lists a W X z *
                columnPhase τ.snd (Real.log ((z.val.val.absNorm : ℝ) / X))‖ ^ 2) := by
  exact full_mobius_energy T T (fun z => z.val.val) (fun z => z.val.val)
    (fun z _ => nonZeroDivisors.coe_ne_zero z.val) F
    (fun z => Real.log ((z.val.val.absNorm : ℝ) / X))
    (fun z => Real.log ((z.val.val.absNorm : ℝ) / X))
    (fun z => star (sourceTerm K S Γ D Λ ν g j d₂ I ξ R slots lists a W X z))
    (sourceTerm K S Γ D Λ ν g j d₂ I ξ R slots lists a W X)

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondCanonicalEnergy

end
