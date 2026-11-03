import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalGaussScaleProduction

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N4: one original occurrence extraction retains its scale product

This base-only module retains the complete frozen ideal and the original
upper annulus. The original occurrence and packet constructions are
consumed only by the separate two-extraction module.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

section OneExtraction

variable {k : ℕ} {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {P : Finset (Ideal (𝓞 K))}

/-- The same exact cancellation as the base lower bound, now using
the original upper annulus. Repeated frozen primes are retained. -/
theorem residualGaussScale_mul_frozenNorm_le
    (b : SupportCartesianBranch S₁ S₂ S P)
    (Z : ℝ) (length : Fin k → ℝ) (X₁ X₂ B : ℝ) (cap : ℕ)
    (hZ : 0 < Z) (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂)
    (hB : 1 ≤ B) (hcap : k ≤ cap)
    (hprime : ∀ i ∈ Finset.univ \ b.keep,
      (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ) ≤ B * Z ^ length i) :
    b.residualGaussScale Z length X₁ X₂ *
        (Ideal.absNorm (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂
          b.keep b.witness.2) : ℝ) ≤
      B ^ cap * (X₁ * X₂ * ∏ i, Z ^ length i) := by
  have hcardKeep : (Finset.univ \ b.keep).card ≤ k := by
    simpa only [Fintype.card_fin] using
      (Finset.card_le_univ (Finset.univ \ b.keep))
  have hcard : (Finset.univ \ b.keep).card ≤ cap := hcardKeep.trans hcap
  have hfrozen :
      (∏ i ∈ Finset.univ \ b.keep, (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ)) ≤
        B ^ cap * ∏ i ∈ Finset.univ \ b.keep, Z ^ length i := by
    calc
      _ ≤ ∏ i ∈ Finset.univ \ b.keep, B * Z ^ length i :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) hprime
      _ = B ^ (Finset.univ \ b.keep).card *
          ∏ i ∈ Finset.univ \ b.keep, Z ^ length i := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB hcard)
        (Finset.prod_nonneg (fun _ _ => Real.rpow_nonneg hZ.le _))
  rw [b.residualGaussScale_mul_frozenNorm, b.originalScale_product]
  have hfactor : 0 ≤ X₁ * X₂ * ∏ j, Z ^ length (SlotRestriction.index b.keep j) :=
    mul_nonneg (mul_nonneg hX₁ hX₂)
      (Finset.prod_nonneg (fun _ _ => Real.rpow_nonneg hZ.le _))
  convert mul_le_mul_of_nonneg_left hfrozen hfactor using 1 <;> ring

end OneExtraction

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.residualGaussScale_mul_frozenNorm_le
