module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryNormPower
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralTerms

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Exact norm-power multiplication at the original single atoms

The new normalized profile multiplies each original atom by its own
normalized norm power. These factors recombine to the power of the
whole ideal, with exactly the explicit scale product outside. No
profile value is divided out, so every arithmetic or profile zero is
preserved throughout the calculation.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryNormProfile

open HeckeSkeleton.Moments.EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

/-- Separate any multiplicative factor at each original occurrence,
without changing its character, mask or normalization. -/
theorem bare_mul_weights (T : FixedChildCharacters K k)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ g₁ g₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w g : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) :
    rawBareSourceCoefficient T N₁ N₂ Z length
        (fun I => w₁ I * g₁ I) (fun I => w₂ I * g₂ I)
        (fun j q => w j q * g j q) i =
      rawBareSourceCoefficient T N₁ N₂ Z length w₁ w₂ w i *
        (g₁ (sourceMomentIdeal i.1.1) * g₂ (sourceMomentIdeal i.1.2) *
          ∏ j, g j (i.2 j)) := by
  simp only [rawBareSourceCoefficient, FixedChildCharacters.bareCoefficient,
    childCartesianCoefficient, Finset.prod_mul_distrib]
  ring

theorem normalized_bare (T : FixedChildCharacters K k)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ) (e : ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) (hleft : i.1.1 ≠ 0) (hright : i.1.2 ≠ 0)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hZ : 0 < Z) :
    (((N₁ * N₂ * ∏ j, Z ^ length j) ^ e : ℝ) : ℂ) *
        rawBareSourceCoefficient T N₁ N₂ Z length
          (fun I => w₁ I * (((idealNorm K I / N₁) ^ e : ℝ) : ℂ))
          (fun I => w₂ I * (((idealNorm K I / N₂) ^ e : ℝ) : ℂ))
          (fun j q => w j q *
            ((((Ideal.absNorm q.asIdeal : ℝ) / Z ^ length j) ^ e : ℝ) : ℂ)) i =
      (((Ideal.absNorm (allocationColumnIdeal i) : ℝ) ^ e : ℝ) : ℂ) *
        rawBareSourceCoefficient T N₁ N₂ Z length w₁ w₂ w i := by
  have h₁ : idealNorm K (sourceMomentIdeal i.1.1) = (Ideal.absNorm i.1.1 : ℝ) := by
    change (Ideal.absNorm (sourceMomentIdeal i.1.1).val : ℝ) = _
    rw [sourceMomentIdeal_val_of_ne_zero _ hleft]
  have h₂ : idealNorm K (sourceMomentIdeal i.1.2) = (Ideal.absNorm i.1.2 : ℝ) := by
    change (Ideal.absNorm (sourceMomentIdeal i.1.2).val : ℝ) = _
    rw [sourceMomentIdeal_val_of_ne_zero _ hright]
  rw [bare_mul_weights]
  simp only [h₁, h₂]
  calc
    _ =
        ((((N₁ * N₂ * ∏ j, Z ^ length j) ^ e : ℝ) : ℂ) *
          (((((Ideal.absNorm i.1.1 : ℝ) / N₁) ^ e : ℝ) : ℂ) *
            ((((Ideal.absNorm i.1.2 : ℝ) / N₂) ^ e : ℝ) : ℂ) *
            ∏ j, ((((Ideal.absNorm (i.2 j).asIdeal : ℝ) / Z ^ length j) ^ e : ℝ) : ℂ))) *
          rawBareSourceCoefficient T N₁ N₂ Z length w₁ w₂ w i := by ring
    _ = _ := by
      rw [OrdinaryNormPower.allocation_normalized_product_complex i N₁ N₂ Z length e
        hN₁ hN₂ hZ]

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryNormProfile

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryNormProfile.bare_mul_weights
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryNormProfile.normalized_bare
