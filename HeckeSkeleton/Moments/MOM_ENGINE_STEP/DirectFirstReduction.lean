import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectOriginalData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstLinearizedSource

/-!
# Direct first reduction under the original common Fourier measure

The complete first residual divisor and finite phase expansion can be
linearized using the original Gauss rows directly. This is the direct
enlargement entrance used when the slot count is zero. It retains the
same original row profile, whole coefficients and positive allowances;
there is no pool average in its conclusion.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters MeasureTheory
open HeckePort.Moments HeckePort.Moments.MobiusRegroup UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Actual Cauchy rows are enlarged directly, then the two positive
normalizations are applied before integration. -/
theorem first_gauss_direct_integral_bound {H ι κ : Type*}
    (F : 𝓢(V, ℂ)) (left : DirectGaussData C ι) (right : DirectGaussData C κ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (rows : Finset H) (frequencyLeft frequencyRight : H → A.R)
    (hleft_inj : Set.InjOn frequencyLeft (rows : Set H))
    (hright_inj : Set.InjOn frequencyRight (rows : Set H))
    (hleft_rows : rows.image frequencyLeft ⊆ left.rows)
    (hright_rows : rows.image frequencyRight ⊆ right.rows)
    (q : H → ℂ) (W NL NR : ℝ) (hW : 0 ≤ W) (hNL : 0 < NL) (hNR : 0 < NR)
    (hq : ∀ h ∈ rows, ‖q h‖ ≤ W)
    (c : ι → ℂ) (d : κ → ℂ) (x : ι → V) (y : κ → V) :
    (∫ ξ : V, ‖(𝓕 F) ξ‖ *
      (Real.sqrt (weightedEnergy rows (fun h => ‖q h‖)
        (fun h => wholePolynomial left.columns
          (fun i => c i * jointPhase ξ (x i)) (left.gaussColumn hDiff) (frequencyLeft h))) *
       Real.sqrt (weightedEnergy rows (fun h => ‖q h‖)
        (fun h => wholePolynomial right.columns
          (fun j => d j * star (jointPhase ξ (y j))) (right.gaussColumn hDiff)
            (frequencyRight h))))) ≤
      (W * Real.sqrt NL * Real.sqrt NR / 2) *
        ((∫ ξ, (left.directSource
            (FirstGaussPoolData.twistedCoefficient c x ξ)).energy hDiff / NL
          ∂actualFourierMeasure F) +
        ∫ ξ, (right.directSource
            (FirstGaussPoolData.twistedCoefficient d (fun j => -y j) ξ)).energy hDiff / NR
          ∂actualFourierMeasure F) := by
  borelize V
  have hold := joint_kernel_energy_integrable F rows left.columns right.columns q
    (fun h i => c i * left.gaussColumn hDiff i (frequencyLeft h))
    (fun h j => star (d j * right.gaussColumn hDiff j (frequencyRight h)))
    (fun (_ : H) i => (0 : V) + x i) (fun _ j => y j)
  simp_rw [joint_energy_gauss_rows, joint_energy_conjugate_gauss_rows,
    ← jointPhase_neg] at hold
  simp_rw [← jointPhase_neg]
  let L : V → ℝ := fun ξ =>
    (left.directSource (FirstGaussPoolData.twistedCoefficient c x ξ)).energy hDiff / NL
  let R : V → ℝ := fun ξ =>
    (right.directSource (FirstGaussPoolData.twistedCoefficient d (fun j => -y j) ξ)).energy hDiff / NR
  have hL : Integrable L (actualFourierMeasure F) :=
    (left.direct_twisted_integrable (hDiff := hDiff) F c x).div_const NL
  have hR : Integrable R (actualFourierMeasure F) :=
    (right.direct_twisted_integrable (hDiff := hDiff) F d (fun j => -y j)).div_const NR
  have hm : Measurable (fun ξ : V => ENNReal.ofReal ‖(𝓕 F) ξ‖) := by fun_prop
  have hold' : Integrable (fun ξ =>
      Real.sqrt (weightedEnergy rows (fun h => ‖q h‖)
        (fun h => wholePolynomial left.columns
          (fun i => c i * jointPhase ξ (x i)) (left.gaussColumn hDiff) (frequencyLeft h))) *
      Real.sqrt (weightedEnergy rows (fun h => ‖q h‖)
        (fun h => wholePolynomial right.columns
          (fun j => d j * jointPhase ξ (-y j)) (right.gaussColumn hDiff) (frequencyRight h))))
      (actualFourierMeasure F) := by
    apply (integrable_withDensity_iff_integrable_smul' hm
      (Filter.Eventually.of_forall (fun ξ : V => ENNReal.ofReal_lt_top))).mpr
    simpa only [ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul] using hold
  calc
    _ = ∫ ξ, Real.sqrt (weightedEnergy rows (fun h => ‖q h‖)
        (fun h => wholePolynomial left.columns
          (fun i => c i * jointPhase ξ (x i)) (left.gaussColumn hDiff) (frequencyLeft h))) *
      Real.sqrt (weightedEnergy rows (fun h => ‖q h‖)
        (fun h => wholePolynomial right.columns
          (fun j => d j * jointPhase ξ (-y j)) (right.gaussColumn hDiff) (frequencyRight h)))
        ∂actualFourierMeasure F := (actualFourierMeasure_integral_eq F _).symm
    _ ≤ ∫ ξ, (W * Real.sqrt NL * Real.sqrt NR / 2) * (L ξ + R ξ)
        ∂actualFourierMeasure F := by
      apply integral_mono hold'
        (by simpa only [Pi.add_apply] using
          (hL.add hR).const_mul (W * Real.sqrt NL * Real.sqrt NR / 2))
      intro ξ
      have hleft := left.weighted_direct_energy_bound (hDiff := hDiff) rows frequencyLeft
        hleft_inj hleft_rows q W hW hq (FirstGaussPoolData.twistedCoefficient c x ξ)
      have hright := right.weighted_direct_energy_bound (hDiff := hDiff) rows frequencyRight
        hright_inj hright_rows q W hW hq
        (FirstGaussPoolData.twistedCoefficient d (fun j => -y j) ξ)
      apply (mul_le_mul (Real.sqrt_le_sqrt hleft) (Real.sqrt_le_sqrt hright)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans
      exact weighted_sqrt_normalized_average W _ _ NL NR hW
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hNL hNR
    _ = _ := by
      rw [integral_const_mul, integral_add hL hR]

variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]
local instance directFirstReductionCircleCharacterFintype : Fintype ((Ray × Ray) →* Circle) := Fintype.ofFinite _

/-- Exact first Möbius and phase labels, now with the direct original
Gauss energies and their original positive normalizations. -/
def firstDirectLinearizedCost {ι κ : Type*}
    (F : 𝓢(V, ℂ)) (left : DirectGaussData C ι) (right : DirectGaussData C κ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (rayLeft : ι → Ray) (rayRight : κ → Ray) (phaseTable : Ray × Ray → Circle)
    (W : ℝ)
    (NL NR : (divisorPool right.columns (fun j => (right.ideal j).val)) →
      ((Ray × Ray) →* Circle) → ℝ)
    (c : ι → ℂ) (d : κ → ℂ) (x : ι → V) (y : κ → V) : ℝ :=
  ∑ S : divisorPool right.columns (fun j => (right.ideal j).val), ‖(moebius S.val : ℂ)‖ *
    ∑ χ : (Ray × Ray) →* Circle, ‖fixedPhaseCoefficient Ray phaseTable χ‖ *
      (W * Real.sqrt (NL S χ) * Real.sqrt (NR S χ) / 2) *
      ((∫ ξ, (left.directSource
        (FirstGaussPoolData.twistedCoefficient
          (fun i => if S.val ∣ (left.ideal i).val then
            c i * (fixedLeftPhase Ray χ (rayLeft i) : ℂ) else 0) x ξ)).energy hDiff / NL S χ
          ∂actualFourierMeasure F) +
       ∫ ξ, (right.directSource
        (FirstGaussPoolData.twistedCoefficient
          (fun j => if S.val ∣ (right.ideal j).val then
            d j * (fixedRightPhase Ray χ (rayRight j) : ℂ) else 0) (fun j => -y j) ξ)).energy hDiff / NR S χ
          ∂actualFourierMeasure F)

variable {Γ : Subgroup A.U}

/-- Both complete finite coprimality factors enter the original direct
sources. The result is derived from the literal first residual kernel. -/
theorem first_residual_cost_le_direct_linearized {H ι κ : Type*}
    (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
    (F : 𝓢(V, ℂ)) (left : DirectGaussData C ι) (right : DirectGaussData C κ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
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
        firstDirectLinearizedCost Ray F left right hDiff rayLeft rayRight phaseTable
          W NL NR c d x y := by
  unfold firstResidualKernelCost firstDirectLinearizedCost
  dsimp only
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_le_sum
  intro S hS
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro χ hχ
  have he := first_gauss_direct_integral_bound F left right hDiff rows frequency
    (fun h => -frequency h) hinj
    (fun h hh h' hh' he => hinj hh hh' (neg_injective he)) hleft_rows hright_rows
    (fun h => q h * common h) W (NL S χ) (NR S χ) hW (hNL S χ) (hNR S χ) hq
    (fun i => if S.val ∣ (left.ideal i).val then
      c i * (fixedLeftPhase Ray χ (rayLeft i) : ℂ) else 0)
    (fun j => if S.val ∣ (right.ideal j).val then
      d j * (fixedRightPhase Ray χ (rayRight j) : ℂ) else 0) x y
  dsimp only [wholePolynomial, DirectGaussData.gaussColumn,
    generatedOriginalColumn] at he ⊢
  exact (mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans_eq (by ring)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.first_gauss_direct_integral_bound
#print axioms HeckeSkeleton.Moments.EngineStep.first_residual_cost_le_direct_linearized
