import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NestedHilbertPhase
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondResidualSource

/-!
# Actual second residual kernels under the first Fourier integral

The real residual divisor pool and its finite reciprocity phases remain
inside the formula. Fixed whole coefficients carry the first Fourier
phase. The complete finite columns give integrability, and exact Fubini
combines the two Fourier parameters without a frequency cutoff.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree

open MeasureTheory NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckePort.Moments HeckePort.Moments.MobiusRegroup

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem kernelDivisorCoefficient_first_phase {H ι : Type*}
    (ideal : ι → Ideal (𝓞 K)) (L : Ideal (𝓞 K)) (c phase : ι → ℂ)
    (χ : ι → H → ℂ) (x : ι → U) (ξ : U) (h : H) (i : ι) :
    kernelDivisorCoefficient ideal L (fun i => c i * jointPhase ξ (x i)) phase χ h i =
      kernelDivisorCoefficient ideal L c phase χ h i * jointPhase ξ (x i) := by
  unfold kernelDivisorCoefficient
  split_ifs <;> ring

theorem kernelDivisorCoefficient_star_first_phase {H ι : Type*}
    (ideal : ι → Ideal (𝓞 K)) (L : Ideal (𝓞 K)) (c phase : ι → ℂ)
    (χ : ι → H → ℂ) (x : ι → U) (ξ : U) (h : H) (i : ι) :
    star (kernelDivisorCoefficient ideal L (fun i => c i * jointPhase ξ (x i)) phase χ h i) =
      star (kernelDivisorCoefficient ideal L c phase χ h i) * jointPhase ξ (-x i) := by
  rw [kernelDivisorCoefficient_first_phase, star_mul', jointPhase_neg]

private theorem kernelDivisorCoefficient_first_phase_function {H ι : Type*}
    (ideal : ι → Ideal (𝓞 K)) (L : Ideal (𝓞 K)) (c phase : ι → ℂ)
    (χ : ι → H → ℂ) (x : ι → U) (ξ : U) :
    kernelDivisorCoefficient ideal L (fun i => c i * jointPhase ξ (x i)) phase χ =
      (fun h i => kernelDivisorCoefficient ideal L c phase χ h i *
        jointPhase ξ (x i)) := by
  funext h i
  exact kernelDivisorCoefficient_first_phase ideal L c phase χ x ξ h i

variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]
local instance nestedSecondResidualCircleCharacterFintype : Fintype ((Ray × Ray) →* Circle) := Fintype.ofFinite _
variable {H ι κ : Type*}
variable (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(V, ℂ))
variable (rows : Finset H) (frequency : H → A.R)
variable (left : Finset ι) (right : Finset κ)
variable (ID IE : A.Exterior) (IA : ι → A.Exterior) (IB : κ → A.Exterior)
variable (d e : A.R) (hd : A.Generates ID d) (he : A.Generates IE e)
variable (rayLeft : ι → Ray) (rayRight : κ → Ray) (phaseTable : Ray × Ray → Circle)
variable (q : H → ℂ) (c : ι → ℂ) (f : κ → ℂ)
variable (x₁ : ι → U) (y₁ : κ → U) (x₂ : H → ι → V) (y₂ : H → κ → V)

/-- This is the actual second residual cost with both complete phase
locations fixed before the two continuous variables. -/
def nestedSecondResidualKernelCost : ℝ :=
  ∑ L ∈ divisorPool right (fun j => (IB j).val), ‖(moebius L : ℂ)‖ *
    ∑ χ : (Ray × Ray) →* Circle, ‖fixedPhaseCoefficient Ray phaseTable χ‖ *
      ∫ z, Real.sqrt (jointColumnEnergy rows left
        (fun h => q h * generatedIdealCorrelation (σ := σ) ID IE d e hd he (frequency h))
        (kernelDivisorCoefficient (fun i => (IA i).val) L c
          (fun i => (fixedLeftPhase Ray χ (rayLeft i) : ℂ))
          (fun i h => σ (A.sexticResidue (IA i) (frequency h))))
        (fun h i => WithLp.toLp 2 (x₁ i, x₂ h i)) (WithLp.toLp 2 z)) *
      Real.sqrt (jointColumnEnergy rows right
        (fun h => q h * generatedIdealCorrelation (σ := σ) ID IE d e hd he (frequency h))
        (fun h j => star (kernelDivisorCoefficient (fun j => (IB j).val) L f
          (fun j => (fixedRightPhase Ray χ (rayRight j) : ℂ))
          (fun j h => σ (A.sexticResidue (IB j) (-frequency h))) h j))
        (fun h j => WithLp.toLp 2 (-y₁ j, y₂ h j)) (WithLp.toLp 2 z))
        ∂nestedFourierMeasure F₁ F₂

theorem actual_second_residual_first_phase_integrable :
    Integrable (fun ξ => secondResidualKernelCost (σ := σ) Ray F₂ rows frequency left right
      ID IE IA IB d e hd he rayLeft rayRight phaseTable q
      (fun i => c i * jointPhase ξ (x₁ i))
      (fun j => f j * jointPhase ξ (y₁ j)) x₂ y₂) (actualFourierMeasure F₁) := by
  unfold secondResidualKernelCost
  simp only [kernelDivisorCoefficient_first_phase_function, star_mul', ← jointPhase_neg]
  apply integrable_finsetSum
  intro L hL
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro χ hχ
  apply Integrable.const_mul
  exact iterated_joint_cauchy_integrable rows left right _ _ _
    (fun _ i => x₁ i) x₂ (fun _ j => -y₁ j) y₂ F₁ F₂

/-- Both integrability and the exact product-kernel formula are proved
from the actual finite residual source, not assumed by the producer. -/
theorem actual_second_residual_nested_integral :
    (∫ ξ, secondResidualKernelCost (σ := σ) Ray F₂ rows frequency left right
      ID IE IA IB d e hd he rayLeft rayRight phaseTable q
      (fun i => c i * jointPhase ξ (x₁ i))
      (fun j => f j * jointPhase ξ (y₁ j)) x₂ y₂ ∂actualFourierMeasure F₁) =
      nestedSecondResidualKernelCost (σ := σ) Ray F₁ F₂ rows frequency left right
        ID IE IA IB d e hd he rayLeft rayRight phaseTable q c f x₁ y₁ x₂ y₂ := by
  let weight := fun h => q h * generatedIdealCorrelation (σ := σ) ID IE d e hd he (frequency h)
  have hi (L : Ideal (𝓞 K)) (χ : (Ray × Ray) →* Circle) :=
    iterated_joint_cauchy_integrable rows left right weight
      (kernelDivisorCoefficient (fun i => (IA i).val) L c
        (fun i => (fixedLeftPhase Ray χ (rayLeft i) : ℂ))
        (fun i h => σ (A.sexticResidue (IA i) (frequency h))))
      (fun h j => star (kernelDivisorCoefficient (fun j => (IB j).val) L f
        (fun j => (fixedRightPhase Ray χ (rayRight j) : ℂ))
        (fun j h => σ (A.sexticResidue (IB j) (-frequency h))) h j))
      (fun _ i => x₁ i) x₂ (fun _ j => -y₁ j) y₂ F₁ F₂
  unfold secondResidualKernelCost nestedSecondResidualKernelCost
  simp only [kernelDivisorCoefficient_first_phase_function, star_mul', ← jointPhase_neg]
  rw [integral_finsetSum _ (fun L _ =>
    (integrable_finsetSum _ (fun χ _ => (hi L χ).const_mul _)).const_mul _)]
  apply Finset.sum_congr rfl
  intro L hL
  rw [integral_const_mul, integral_finsetSum _ (fun χ _ => (hi L χ).const_mul _)]
  congr 1
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [integral_const_mul, nested_joint_cauchy_fubini]

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_second_residual_first_phase_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.actual_second_residual_nested_integral
