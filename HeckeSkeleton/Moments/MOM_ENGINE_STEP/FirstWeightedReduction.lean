import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDivisorPool
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFamilyIntegrability
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Weighted first-stage reduction under one positive Fourier measure

The allowances are fixed before the continuous parameter.  The actual
left and right pooled energies are divided by their own allowances, and
the arithmetic geometric mean inequality puts them under the same
original Fourier measure.  Their integrability is proved from the
existing continuous, bounded finite Gauss polynomials.

The final sum uses the literal internal Möbius divisors and finite phase
characters of \`FirstDivisorPoolData\`.  No aggregate first-kernel bound is
a premise: the genuine first residual theorem supplies that comparison.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters MeasureTheory
open HeckePort.Moments HeckePort.Moments.MobiusRegroup UniqueFactorizationMonoid

theorem weighted_sqrt_normalized_average (W EL ER NL NR : ℝ)
    (hW : 0 ≤ W) (hEL : 0 ≤ EL) (hER : 0 ≤ ER) (hNL : 0 < NL) (hNR : 0 < NR) :
    Real.sqrt (W * EL) * Real.sqrt (W * ER) ≤
      W * Real.sqrt NL * Real.sqrt NR / 2 * (EL / NL + ER / NR) := by
  have hl : 0 ≤ EL / NL := div_nonneg hEL hNL.le
  have hr : 0 ≤ ER / NR := div_nonneg hER hNR.le
  have hmean : Real.sqrt (EL / NL) * Real.sqrt (ER / NR) ≤
      (EL / NL + ER / NR) / 2 := by
    nlinarith [Real.sq_sqrt hl, Real.sq_sqrt hr,
      sq_nonneg (Real.sqrt (EL / NL) - Real.sqrt (ER / NR))]
  have hleft : Real.sqrt EL = Real.sqrt NL * Real.sqrt (EL / NL) := by
    rw [← Real.sqrt_mul hNL.le]
    congr 1
    field_simp [ne_of_gt hNL]
  have hright : Real.sqrt ER = Real.sqrt NR * Real.sqrt (ER / NR) := by
    rw [← Real.sqrt_mul hNR.le]
    congr 1
    field_simp [ne_of_gt hNR]
  have hw : Real.sqrt W * Real.sqrt W = W := by nlinarith [Real.sq_sqrt hW]
  rw [Real.sqrt_mul hW, Real.sqrt_mul hW, hleft, hright]
  calc
    _ = (W * Real.sqrt NL * Real.sqrt NR) *
        (Real.sqrt (EL / NL) * Real.sqrt (ER / NR)) := by
      calc
        _ = (Real.sqrt W * Real.sqrt W) *
            (Real.sqrt NL * Real.sqrt NR) *
            (Real.sqrt (EL / NL) * Real.sqrt (ER / NR)) := by ring
        _ = _ := by rw [hw]; ring
    _ ≤ (W * Real.sqrt NL * Real.sqrt NR) * ((EL / NL + ER / NR) / 2) :=
      mul_le_mul_of_nonneg_left hmean
        (mul_nonneg (mul_nonneg hW (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    _ = _ := by ring

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem actualFourierMeasure_integral_eq (F : 𝓢(V, ℂ)) (G : V → ℝ) :
    (∫ ξ, G ξ ∂actualFourierMeasure F) = ∫ ξ : V, ‖(𝓕 F) ξ‖ * G ξ := by
  have hm : Measurable (fun ξ : V => ENNReal.ofReal ‖(𝓕 F) ξ‖) := by fun_prop
  simpa only [actualFourierMeasure, ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul] using
    integral_withDensity_eq_integral_toReal_smul hm
      (Filter.Eventually.of_forall (fun ξ : V => ENNReal.ofReal_lt_top)) G

theorem FirstGaussPoolData.twisted_integrable {ι : Type*}
    (d : FirstGaussPoolData C P ι) (F : 𝓢(V, ℂ)) (c : ι → ℂ) (x : ι → V) :
    Integrable (fun ξ => d.energy (FirstGaussPoolData.twistedCoefficient c x ξ))
      (actualFourierMeasure F) := by
  have hi : Integrable (fun ξ : V => ‖(𝓕 F) ξ‖ *
      d.energy (FirstGaussPoolData.twistedCoefficient c x ξ)) := by
    apply ((𝓕 F).integrable (μ := (volume : Measure V))).norm.mul_bdd (c := d.mass c)
      (d.continuous_energy_twisted c x).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (d.energy_nonneg _)]
      exact d.energy_twisted_le_mass c x ξ
  have hm : Measurable (fun ξ : V => ENNReal.ofReal ‖(𝓕 F) ξ‖) := by fun_prop
  apply (integrable_withDensity_iff_integrable_smul' hm
    (Filter.Eventually.of_forall (fun ξ : V => ENNReal.ofReal_lt_top))).mpr
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul] using hi

theorem FirstGaussPoolData.normalized_twisted_integrable {ι : Type*}
    (d : FirstGaussPoolData C P ι) (F : 𝓢(V, ℂ)) (c : ι → ℂ) (x : ι → V) (N : ℝ) :
    Integrable (fun ξ => d.energy (FirstGaussPoolData.twistedCoefficient c x ξ) / N)
      (actualFourierMeasure F) :=
  (d.twisted_integrable F c x).div_const N

/-- The bounded finite pooled polynomials are linearized only after
normalization, under their one original positive Fourier measure. -/
theorem first_pool_pair_weighted_linearization {ι κ : Type*}
    (F : 𝓢(V, ℂ)) (left : FirstGaussPoolData C P ι) (right : FirstGaussPoolData C P κ)
    (c : ι → ℂ) (d : κ → ℂ) (x : ι → V) (y : κ → V)
    (W NL NR : ℝ) (hW : 0 ≤ W) (hNL : 0 < NL) (hNR : 0 < NR) :
    (∫ ξ : V, ‖(𝓕 F) ξ‖ *
      (Real.sqrt (W * left.energy (FirstGaussPoolData.twistedCoefficient c x ξ)) *
        Real.sqrt (W * right.energy (FirstGaussPoolData.twistedCoefficient d y ξ)))) ≤
      (W * Real.sqrt NL * Real.sqrt NR / 2) *
        ((∫ ξ, left.energy (FirstGaussPoolData.twistedCoefficient c x ξ) / NL
          ∂actualFourierMeasure F) +
        ∫ ξ, right.energy (FirstGaussPoolData.twistedCoefficient d y ξ) / NR
          ∂actualFourierMeasure F) := by
  have hleft := left.normalized_twisted_integrable F c x NL
  have hright := right.normalized_twisted_integrable F d y NR
  have hm : Measurable (fun ξ : V => ENNReal.ofReal ‖(𝓕 F) ξ‖) := by fun_prop
  have hsqrt : Integrable (fun ξ : V =>
      Real.sqrt (W * left.energy (FirstGaussPoolData.twistedCoefficient c x ξ)) *
        Real.sqrt (W * right.energy (FirstGaussPoolData.twistedCoefficient d y ξ)))
      (actualFourierMeasure F) := by
    apply (integrable_withDensity_iff_integrable_smul' hm
      (Filter.Eventually.of_forall (fun ξ : V => ENNReal.ofReal_lt_top))).mpr
    simpa only [ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul] using
      first_gauss_pool_kernel_integrable F left right c d x y W hW
  calc
    _ = ∫ ξ : V,
        Real.sqrt (W * left.energy (FirstGaussPoolData.twistedCoefficient c x ξ)) *
          Real.sqrt (W * right.energy (FirstGaussPoolData.twistedCoefficient d y ξ))
        ∂actualFourierMeasure F := (actualFourierMeasure_integral_eq F _).symm
    _ ≤ ∫ ξ : V, (W * Real.sqrt NL * Real.sqrt NR / 2) *
        (left.energy (FirstGaussPoolData.twistedCoefficient c x ξ) / NL +
          right.energy (FirstGaussPoolData.twistedCoefficient d y ξ) / NR)
        ∂actualFourierMeasure F := by
      apply integral_mono hsqrt
        (by simpa only [Pi.add_apply] using
          (hleft.add hright).const_mul (W * Real.sqrt NL * Real.sqrt NR / 2))
      intro ξ
      exact weighted_sqrt_normalized_average W _ _ NL NR hW
        (left.energy_nonneg _) (right.energy_nonneg _) hNL hNR
    _ = _ := by
      rw [integral_const_mul, integral_add hleft hright]

variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]
local instance firstWeightedReductionCircleCharacterFintype : Fintype ((Ray × Ray) →* Circle) := Fintype.ofFinite _

/-- Explicit normalized left/right pooled integrals for every actual
internal divisor and finite phase character.  All allowances are chosen
before the continuous variable. -/
def firstDivisorLinearizedCost {ι κ : Type*}
    (F : 𝓢(V, ℂ)) (left : FirstGaussPoolData C P ι) (right : FirstGaussPoolData C P κ)
    (p : FirstDivisorPoolData left right)
    (rayLeft : ι → Ray) (rayRight : κ → Ray) (phaseTable : Ray × Ray → Circle)
    (W : ℝ)
    (NL NR : (divisorPool right.columns (fun j => (right.ideal j).val)) →
      ((Ray × Ray) →* Circle) → ℝ)
    (c : ι → ℂ) (d : κ → ℂ) (x : ι → V) (y : κ → V) : ℝ :=
  ∑ S : divisorPool right.columns (fun j => (right.ideal j).val), ‖(moebius S.val : ℂ)‖ *
    ∑ χ : (Ray × Ray) →* Circle, ‖fixedPhaseCoefficient Ray phaseTable χ‖ *
      (W * Real.sqrt (NL S χ) * Real.sqrt (NR S χ) / 2) *
      ((∫ ξ, (p.leftData S).energy
        (FirstGaussPoolData.twistedCoefficient
          (fun i => if S.val ∣ (left.ideal i).val then
            c i * (fixedLeftPhase Ray χ (rayLeft i) : ℂ) else 0) x ξ) / NL S χ
          ∂actualFourierMeasure F) +
       ∫ ξ, (p.rightData S).energy
        (FirstGaussPoolData.twistedCoefficient
          (fun j => if S.val ∣ (right.ideal j).val then
            d j * (fixedRightPhase Ray χ (rayRight j) : ℂ) else 0) (fun j => -y j) ξ) / NR S χ
          ∂actualFourierMeasure F)

theorem first_divisor_pool_le_linearized {ι κ : Type*}
    (F : 𝓢(V, ℂ)) (left : FirstGaussPoolData C P ι) (right : FirstGaussPoolData C P κ)
    (p : FirstDivisorPoolData left right)
    (rayLeft : ι → Ray) (rayRight : κ → Ray) (phaseTable : Ray × Ray → Circle)
    (W : ℝ) (hW : 0 ≤ W)
    (NL NR : (divisorPool right.columns (fun j => (right.ideal j).val)) →
      ((Ray × Ray) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)
    (c : ι → ℂ) (d : κ → ℂ) (x : ι → V) (y : κ → V) :
    firstDivisorPooledResidualCost Ray F left right p rayLeft rayRight phaseTable W c d x y ≤
      firstDivisorLinearizedCost Ray F left right p rayLeft rayRight phaseTable W NL NR c d x y := by
  unfold firstDivisorPooledResidualCost firstDivisorLinearizedCost
  apply Finset.sum_le_sum
  intro S _
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro χ _
  have he := first_pool_pair_weighted_linearization F (p.leftData S) (p.rightData S)
    (fun i => if S.val ∣ (left.ideal i).val then
      c i * (fixedLeftPhase Ray χ (rayLeft i) : ℂ) else 0)
    (fun j => if S.val ∣ (right.ideal j).val then
      d j * (fixedRightPhase Ray χ (rayRight j) : ℂ) else 0)
    x (fun j => -y j) W (NL S χ) (NR S χ) hW (hNL S χ) (hNR S χ)
  exact (mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans_eq (by ring)

variable {Γ : Subgroup A.U}

/-- Starts from the actual residual kernel, uses the actual fixed pool,
and outputs explicit normalized left/right energy integrals. -/
theorem first_residual_cost_le_weighted_reduction {H ι κ : Type*}
    (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
    (F : 𝓢(V, ℂ)) (left : FirstGaussPoolData C P ι) (right : FirstGaussPoolData C P κ)
    (p : FirstDivisorPoolData left right)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (rows : Finset H) (frequency : H → A.R)
    (hinj : Set.InjOn frequency (rows : Set H))
    (hleft_rows : rows.image frequency ⊆ left.rows)
    (hright_rows : rows.image (fun h => -frequency h) ⊆ right.rows)
    (rayLeft : ι → Ray) (rayRight : κ → Ray) (phaseTable : Ray × Ray → Circle)
    (common q : H → ℂ) (W : ℝ) (hW : 0 ≤ W)
    (hq : ∀ h ∈ rows, ‖q h * common h‖ ≤ W)
    (NL NR : (divisorPool right.columns (fun j => (right.ideal j).val)) →
      ((Ray × Ray) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)
    (c : ι → ℂ) (d : κ → ℂ) (x : ι → V) (y : κ → V) :
    firstResidualKernelCost hDiff Ray F rows frequency left.columns right.columns
      (fun i => (left.ideal i).val) (fun j => (right.ideal j).val)
      (fun i => generatedOriginalColumn (σ := σ) hΓ
        (left.ideal i) (left.generator i) (left.generates i))
      (fun j => generatedOriginalColumn (σ := σ) hΓ
        (right.ideal j) (right.generator j) (right.generates j))
      rayLeft rayRight phaseTable common q c d x y ≤
        firstDivisorLinearizedCost Ray F left right p rayLeft rayRight phaseTable
          W NL NR c d x y := by
  exact (first_residual_cost_le_divisor_pool Ray hΓ F left right p hDiff rows frequency
    hinj hleft_rows hright_rows rayLeft rayRight phaseTable common q W hW hq c d x y).trans
      (first_divisor_pool_le_linearized Ray F left right p rayLeft rayRight phaseTable
        W hW NL NR hNL hNR c d x y)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.weighted_sqrt_normalized_average
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.normalized_twisted_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.first_divisor_pool_le_linearized
#print axioms HeckeSkeleton.Moments.EngineStep.first_residual_cost_le_weighted_reduction

