import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstWeightedReduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GaussStagePhaseTransport

/-!
# The original Gauss source before any prime amplification

The direct source retains the original rows and whole coefficients.
Its coefficient phases are taken under the same first Fourier measure
as in the amplified construction. All convergence statements follow
from the actual finite polynomials. No prime density or amplification
factor occurs in the direct energy.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  localDifferentExponent K v = 0}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*}

namespace ActualGaussSource

def phaseEnergy (G : ActualGaussSource C ι) (x : ι → V) (ξ : V) : ℝ :=
  (G.withMultiplier (fun i => jointPhase ξ (x i))).energy hDiff

theorem phaseEnergy_nonneg (G : ActualGaussSource C ι) (x : ι → V) (ξ : V) :
    0 ≤ G.phaseEnergy (hDiff := hDiff) x ξ :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem phaseEnergy_eq_joint (G : ActualGaussSource C ι) (x : ι → V) (ξ : V) :
    G.phaseEnergy (hDiff := hDiff) x ξ =
      jointColumnEnergy G.rows G.columns (fun _ => 1)
        (fun h i => G.coefficient i *
          actualSIntegerGauss K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hDiff
            (G.generator i) (G.generates i).1
            (generatedIdealCharacter (σ := σ) (G.ideal i) (G.generator i) (G.generates i)) h)
        (fun _ => x) ξ := by
  unfold phaseEnergy energy withMultiplier jointColumnEnergy jointFourierColumn
  simp only [norm_one, one_mul]
  apply Finset.sum_congr rfl
  intro h hh
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  ring

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Every direct Fourier family is the original finite polynomial,
so integrability does not require a child or source-energy bound. -/
theorem phaseEnergy_integrable (G : ActualGaussSource C ι)
    (F : 𝓢(V, ℂ)) (x : ι → V) :
    Integrable (G.phaseEnergy (hDiff := hDiff) x) (actualFourierMeasure F) := by
  let c : A.R → ι → ℂ := fun h i => G.coefficient i *
    actualSIntegerGauss K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hDiff
      (G.generator i) (G.generates i).1
      (generatedIdealCharacter (σ := σ) (G.ideal i) (G.generator i) (G.generates i)) h
  have he : G.phaseEnergy (hDiff := hDiff) x =
      fun ξ => jointColumnEnergy G.rows G.columns (fun _ => 1) c (fun _ => x) ξ := by
    funext ξ
    exact G.phaseEnergy_eq_joint x ξ
  rw [he]
  have hi : Integrable (fun ξ : V => ‖(𝓕 F) ξ‖ *
      jointColumnEnergy G.rows G.columns (fun _ => 1) c (fun _ => x) ξ) := by
    apply ((𝓕 F).integrable (μ := (volume : Measure V))).norm.mul_bdd
      (c := jointColumnMass G.rows G.columns (fun _ => 1) c)
      (continuous_jointColumnEnergy _ _ _ _ _).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (jointColumnEnergy_nonneg _ _ _ _ _ _)]
      exact jointColumnEnergy_le_mass _ _ _ _ _ _
  have hm : Measurable (fun ξ : V => ENNReal.ofReal ‖(𝓕 F) ξ‖) := by fun_prop
  apply (integrable_withDensity_iff_integrable_smul' hm
    (Filter.Eventually.of_forall (fun ξ : V => ENNReal.ofReal_lt_top))).mpr
  simpa only [actualFourierMeasure, ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul] using hi

end ActualGaussSource

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

namespace FirstGaussPoolData

/-- Forget the unused prime-pool fields and retain the actual original
whole Gauss polynomial. Its row set is not amplified. -/
def directSource (d : FirstGaussPoolData C P ι) (c : ι → ℂ) : ActualGaussSource C ι where
  rows := d.rows
  row_nonzero h hh := (d.row_generates h hh).1
  columns := d.columns
  ideal := d.ideal
  generator := d.generator
  generates := d.generates
  allowed := d.allowed
  coefficient := c

theorem directSource_energy (d : FirstGaussPoolData C P ι) (c : ι → ℂ) :
    (d.directSource c).energy hDiff =
      ∑ h ∈ d.rows, ‖wholePolynomial d.columns c (d.gaussColumn hDiff) h‖ ^ 2 := rfl

theorem directSource_twisted (d : FirstGaussPoolData C P ι)
    (c : ι → ℂ) (x : ι → V) (ξ : V) :
    d.directSource (twistedCoefficient c x ξ) =
      (d.directSource c).withMultiplier (fun i => jointPhase ξ (x i)) := by
  unfold directSource ActualGaussSource.withMultiplier
  congr 1
  funext i
  exact mul_comm _ _

theorem directSource_phaseEnergy (d : FirstGaussPoolData C P ι)
    (c : ι → ℂ) (x : ι → V) (ξ : V) :
    (d.directSource c).phaseEnergy (hDiff := hDiff) x ξ =
      (d.directSource (twistedCoefficient c x ξ)).energy hDiff := by
  rw [directSource_twisted]
  rfl

/-- The original injective row map embeds directly into its original
row set, with exactly the supplied individual profile multiplier. -/
theorem weighted_direct_energy_bound {H : Type*}
    (d : FirstGaussPoolData C P ι)
    (rows : Finset H) (frequency : H → A.R)
    (hinj : Set.InjOn frequency (rows : Set H))
    (hrows : rows.image frequency ⊆ d.rows)
    (q : H → ℂ) (W : ℝ) (hW : 0 ≤ W)
    (hq : ∀ h ∈ rows, ‖q h‖ ≤ W) (c : ι → ℂ) :
    weightedEnergy rows (fun h => ‖q h‖)
      (fun h => wholePolynomial d.columns c (d.gaussColumn hDiff) (frequency h)) ≤
        W * (d.directSource c).energy hDiff := by
  rw [d.directSource_energy c]
  calc
    _ ≤ W * ∑ h ∈ rows,
        ‖wholePolynomial d.columns c (d.gaussColumn hDiff) (frequency h)‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun h hh => mul_le_mul_of_nonneg_right (hq h hh) (sq_nonneg _)
    _ = W * ∑ h ∈ rows.image frequency,
        ‖wholePolynomial d.columns c (d.gaussColumn hDiff) h‖ ^ 2 := by
      rw [Finset.sum_image hinj]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg hrows (fun h _ _ => sq_nonneg _)) hW

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem direct_twisted_integrable (d : FirstGaussPoolData C P ι)
    (F : 𝓢(V, ℂ)) (c : ι → ℂ) (x : ι → V) :
    Integrable (fun ξ => (d.directSource (twistedCoefficient c x ξ)).energy hDiff)
      (actualFourierMeasure F) := by
  simpa only [d.directSource_phaseEnergy c x] using
    (d.directSource c).phaseEnergy_integrable (hDiff := hDiff) F x

end FirstGaussPoolData

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussSource.phaseEnergy_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.weighted_direct_energy_bound
