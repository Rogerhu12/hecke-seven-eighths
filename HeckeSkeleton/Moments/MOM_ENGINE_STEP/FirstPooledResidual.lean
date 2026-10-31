import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstGaussPoolKernel
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCharacterSource

/-!
# The complete first residual cost enters the same pool

The finite common-support source has already retained its literal
principal mask, active character, reciprocal phase, and two whole
residual polynomials. This module compares its actual `firstResidualKernelCost`
with explicit main/1/6/7 pool energies. Both sides use one common Fourier
integral; every divisor and finite-ray label uses the same earlier pool.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters MeasureTheory
open HeckePort.Moments HeckePort.Moments.MobiusRegroup

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Integral comparison for the two whole residual Gauss energies.
Injectivity is required only on the actual finite row set. -/
theorem first_gauss_pool_integral_bound {H ι κ : Type*}
    (F : 𝓢(V, ℂ)) (left : FirstGaussPoolData C P ι) (right : FirstGaussPoolData C P κ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → localDifferentExponent K v = 0)
    (rows : Finset H) (frequencyLeft frequencyRight : H → A.R)
    (hleft_inj : Set.InjOn frequencyLeft (rows : Set H))
    (hright_inj : Set.InjOn frequencyRight (rows : Set H))
    (hleft_rows : rows.image frequencyLeft ⊆ left.rows)
    (hright_rows : rows.image frequencyRight ⊆ right.rows)
    (q : H → ℂ) (W : ℝ) (hW : 0 ≤ W) (hq : ∀ h ∈ rows, ‖q h‖ ≤ W)
    (c : ι → ℂ) (d : κ → ℂ) (x : ι → V) (y : κ → V) :
    (∫ ξ : V, ‖(𝓕 F) ξ‖ *
      (Real.sqrt (weightedEnergy rows (fun h => ‖q h‖)
        (fun h => wholePolynomial left.columns
          (fun i => c i * jointPhase ξ (x i)) (left.gaussColumn hDiff) (frequencyLeft h))) *
       Real.sqrt (weightedEnergy rows (fun h => ‖q h‖)
        (fun h => wholePolynomial right.columns
          (fun j => d j * star (jointPhase ξ (y j))) (right.gaussColumn hDiff)
            (frequencyRight h))))) ≤
      ∫ ξ : V, ‖(𝓕 F) ξ‖ *
        (Real.sqrt (W * left.energy (FirstGaussPoolData.twistedCoefficient c x ξ)) *
          Real.sqrt (W * right.energy
            (FirstGaussPoolData.twistedCoefficient d (fun j => -y j) ξ))) := by
  have hold := joint_kernel_energy_integrable F rows left.columns right.columns q
    (fun h i => c i * left.gaussColumn hDiff i (frequencyLeft h))
    (fun h j => star (d j * right.gaussColumn hDiff j (frequencyRight h)))
    (fun (_ : H) i => (0 : V) + x i) (fun _ j => y j)
  simp_rw [joint_energy_gauss_rows, joint_energy_conjugate_gauss_rows,
    ← jointPhase_neg] at hold
  simp_rw [← jointPhase_neg]
  apply integral_mono hold
    (first_gauss_pool_kernel_integrable F left right c d x (fun j => -y j) W hW)
  intro ξ
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply mul_le_mul
  · exact Real.sqrt_le_sqrt (left.weighted_energy_bound hDiff rows frequencyLeft
      hleft_inj hleft_rows q W hW hq (FirstGaussPoolData.twistedCoefficient c x ξ))
  · exact Real.sqrt_le_sqrt (right.weighted_energy_bound hDiff rows frequencyRight
      hright_inj hright_rows q W hW hq
        (FirstGaussPoolData.twistedCoefficient d (fun j => -y j) ξ))
  · exact Real.sqrt_nonneg _
  · exact Real.sqrt_nonneg _

variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]
local instance : Fintype ((Ray × Ray) →* Circle) := Fintype.ofFinite _

/-- The whole exact divisor and phase sum, with its two actual pooled
energies. Only the coefficient varies across divisor/Fourier labels. -/
def firstPooledResidualCost {ι κ : Type*}
    (F : 𝓢(V, ℂ)) (left : FirstGaussPoolData C P ι) (right : FirstGaussPoolData C P κ)
    (rayLeft : ι → Ray) (rayRight : κ → Ray) (phaseTable : Ray × Ray → Circle)
    (W : ℝ) (c : ι → ℂ) (d : κ → ℂ) (x : ι → V) (y : κ → V) : ℝ :=
  let c₁ := fun D χ i => if D ∣ (left.ideal i).val then
    c i * (fixedLeftPhase Ray χ (rayLeft i) : ℂ) else 0
  let c₂ := fun D χ j => if D ∣ (right.ideal j).val then
    d j * (fixedRightPhase Ray χ (rayRight j) : ℂ) else 0
  ∑ D ∈ divisorPool right.columns (fun j => (right.ideal j).val), ‖(moebius D : ℂ)‖ *
    ∑ χ : (Ray × Ray) →* Circle, ‖fixedPhaseCoefficient Ray phaseTable χ‖ *
      ∫ ξ : V, ‖(𝓕 F) ξ‖ *
        (Real.sqrt (W * left.energy (FirstGaussPoolData.twistedCoefficient (c₁ D χ) x ξ)) *
          Real.sqrt (W * right.energy
            (FirstGaussPoolData.twistedCoefficient (c₂ D χ) (fun j => -y j) ξ)))

variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)

/-- Directly consumes the actual cost produced by the first common-support
source. All Möbius terms, including nonunit divisors, and all fixed finite
phase coefficients remain in the output. -/
theorem first_residual_cost_le_pool {H ι κ : Type*}
    (F : 𝓢(V, ℂ)) (left : FirstGaussPoolData C P ι) (right : FirstGaussPoolData C P κ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → localDifferentExponent K v = 0)
    (rows : Finset H) (frequency : H → A.R)
    (hinj : Set.InjOn frequency (rows : Set H))
    (hleft_rows : rows.image frequency ⊆ left.rows)
    (hright_rows : rows.image (fun h => -frequency h) ⊆ right.rows)
    (rayLeft : ι → Ray) (rayRight : κ → Ray) (phaseTable : Ray × Ray → Circle)
    (common q : H → ℂ) (W : ℝ) (hW : 0 ≤ W)
    (hq : ∀ h ∈ rows, ‖q h * common h‖ ≤ W)
    (c : ι → ℂ) (d : κ → ℂ) (x : ι → V) (y : κ → V) :
    firstResidualKernelCost hDiff Ray F rows frequency left.columns right.columns
      (fun i => (left.ideal i).val) (fun j => (right.ideal j).val)
      (fun i => generatedOriginalColumn (σ := σ) hΓ
        (left.ideal i) (left.generator i) (left.generates i))
      (fun j => generatedOriginalColumn (σ := σ) hΓ
        (right.ideal j) (right.generator j) (right.generates j))
      rayLeft rayRight phaseTable common q c d x y ≤
        firstPooledResidualCost Ray F left right rayLeft rayRight phaseTable W c d x y := by
  unfold firstResidualKernelCost firstPooledResidualCost
  dsimp only
  apply Finset.sum_le_sum
  intro D hD
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro χ hχ
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact first_gauss_pool_integral_bound F left right hDiff rows frequency
    (fun h => -frequency h) hinj
    (fun h hh h' hh' he => hinj hh hh' (neg_injective he))
    hleft_rows hright_rows (fun h => q h * common h) W hW hq
    (fun i => if D ∣ (left.ideal i).val then
      c i * (fixedLeftPhase Ray χ (rayLeft i) : ℂ) else 0)
    (fun j => if D ∣ (right.ideal j).val then
      d j * (fixedRightPhase Ray χ (rayRight j) : ℂ) else 0) x y

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.first_gauss_pool_integral_bound
#print axioms HeckeSkeleton.Moments.EngineStep.first_residual_cost_le_pool
