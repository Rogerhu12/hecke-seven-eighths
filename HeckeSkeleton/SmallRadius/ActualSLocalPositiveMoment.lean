import HeckeSkeleton.SmallRadius.FinitePositiveMomentCompactSupport
import HeckeSkeleton.SmallRadius.MixedMultiplicativePositiveMoment
import HeckeSkeleton.SmallRadius.SLocalRadialHaarComparison
/-!
Actual positive-Mellin absolute tensor integrals,
first on the genuine local product Haar, then on the actual radial measure.
The archimedean Schwartz input need not factor by place. The finite test
may approach zero. Constants and original seminorm indices precede phi.
The positive radial Haar comparison scalar is explicitly retained.
-/

noncomputable section

namespace HeckeGeneral.Analysis.ActualSLocalPositiveMomentDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic MeasureTheory
open SLocalRadialHaarDraft SmallPositiveFiniteMomentDraft MixedPositiveHaarDraft
open NumberField.AdelicFourier
open scoped Classical BigOperators NNReal

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
  LanglandsTunnell.TateLocal.borelSpace_localBorel

variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : S, MeasurableSpace (v.val.adicCompletion K)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion K)ˣ]

local instance : SecondCountableTopology (mixedEmbedding.mixedSpace K)ˣ := by
  letI : SecondCountableTopology (mixedEmbedding.mixedSpace K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

local instance (v : S) : SecondCountableTopology (v.val.adicCompletion K)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
set_option quotPrecheck false in
local notation "A" => ((v : S) → v.val.adicCompletion K)
local notation "G" => sLocalMultiplicativeGroup K S

def weightedArchAbsolute (φ : SchwartzMap V ℂ) (σ : ℝ)
    (u : (mixedEmbedding.mixedSpace K)ˣ) : ℝ :=
  ‖φ ((traceToMixed K).symm (u : mixedEmbedding.mixedSpace K))‖ *
    (mixedEmbedding.norm (u : mixedEmbedding.mixedSpace K)) ^ σ

/-- Literal absolute value of the original tensor, with the actual product
norm Mellin weight. This definition changes no test or Haar measure. -/
def weightedTensorAbsolute (φ : SchwartzMap V ℂ) (ψ : A → ℂ)
    (σ : ℝ) (x : G) : ℝ :=
  ‖sLocalTensorTestFunction K S φ ψ x‖ * (sLocalProductNorm K S x) ^ σ

theorem weightedTensorAbsolute_nonneg (φ : SchwartzMap V ℂ) (ψ : A → ℂ)
    (σ : ℝ) (x : G) : 0 ≤ weightedTensorAbsolute K S φ ψ σ x :=
  mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (sLocalProductNorm_pos K S x).le _)

theorem weightedTensorAbsolute_eq_product (φ : SchwartzMap V ℂ) (ψ : A → ℂ)
    (σ : ℝ) (x : G) :
    weightedTensorAbsolute K S φ ψ σ x =
      weightedArchAbsolute K φ σ x.1 * finiteWeightedAbsoluteTest K S ψ σ x.2 := by
  have hp : (∏ v : S, ‖(x.2 v).val‖) ^ σ =
      ∏ v : S, ‖(x.2 v).val‖ ^ σ :=
    (Real.finsetProd_rpow Finset.univ (fun v : S => ‖(x.2 v).val‖)
      (fun v _ => norm_nonneg _) σ).symm
  unfold weightedTensorAbsolute weightedArchAbsolute finiteWeightedAbsoluteTest
    sLocalTensorTestFunction sLocalProductNorm
  rw [norm_mul, Real.mul_rpow (mixedEmbedding.norm_nonneg _)
    (Finset.prod_nonneg fun v _ => norm_nonneg _), hp]
  ring

/-- A true product-Haar absolute integral and its uniform original-Schwartz
seminorm bound. There are no unproved local integrability premises. -/
theorem exists_productHaar_positive_moment_bound (ψ : A → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ φ : SchwartzMap V ℂ,
      Integrable (weightedTensorAbsolute K S φ ψ σ) (sLocalProductMultiplicativeHaar K S) ∧
      (∫ x : G, weightedTensorAbsolute K S φ ψ σ x
        ∂sLocalProductMultiplicativeHaar K S) ≤
        C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
  obtain ⟨s, Ca, hCa, harch⟩ :=
    exists_mixed_multiplicative_positive_moment_seminorm_bound K σ hσ hσ1
  obtain ⟨Cf, hCf, hfin, hfinbound⟩ :=
    exists_finite_compactSupport_weightedL1_bound K S ψ hψ hψsupport σ hσ
  refine ⟨s, Ca * Cf, mul_pos hCa hCf, fun φ => ?_⟩
  have ha : Integrable (weightedArchAbsolute K φ σ) (mixedMultiplicativeHaar K) :=
    (harch φ).1
  have hp : Integrable (weightedTensorAbsolute K S φ ψ σ)
      (sLocalProductMultiplicativeHaar K S) :=
    (ha.mul_prod hfin).congr (Filter.Eventually.of_forall fun x =>
      (weightedTensorAbsolute_eq_product K S φ ψ σ x).symm)
  refine ⟨hp, ?_⟩
  have hfinpos : 0 ≤ ∫ u, finiteWeightedAbsoluteTest K S ψ σ u
      ∂finiteMultiplicativeHaar K S :=
    integral_nonneg fun u => mul_nonneg (norm_nonneg _)
      (Finset.prod_nonneg fun v _ => Real.rpow_nonneg (norm_nonneg _) _)
  calc
    _ = (∫ u, weightedArchAbsolute K φ σ u ∂mixedMultiplicativeHaar K) *
        ∫ u, finiteWeightedAbsoluteTest K S ψ σ u ∂finiteMultiplicativeHaar K S := by
      simp_rw [weightedTensorAbsolute_eq_product K S φ ψ σ]
      exact integral_prod_mul _ _
    _ ≤ (Ca * s.sup (schwartzSeminormFamily ℝ V ℂ) φ) * Cf :=
      mul_le_mul (harch φ).2 hfinbound hfinpos (mul_nonneg hCa.le (apply_nonneg _ _))
    _ = _ := by ring

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]

/-- The same literal absolute tensor integral on the actual radial measure.
The scalar from norm-one Haar times log-Lebesgue to product Haar is retained
in C. It is not asserted to equal one. -/
theorem exists_radial_positive_moment_bound (ψ : A → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ φ : SchwartzMap V ℂ,
      Integrable (weightedTensorAbsolute K S φ ψ σ) (sLocalRadialMeasure K S) ∧
      (∫ x : G, weightedTensorAbsolute K S φ ψ σ x ∂sLocalRadialMeasure K S) ≤
        C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
  obtain ⟨s, C, hC, hb⟩ :=
    exists_productHaar_positive_moment_bound K S ψ hψ hψsupport σ hσ hσ1
  let a : ℝ≥0 := radialHaarScalar K S (sLocalProductMultiplicativeHaar K S)
  have ha : 0 < (a : ℝ) := by
    exact_mod_cast radialProductHaarScalar_pos K S
  refine ⟨s, (a : ℝ) * C, mul_pos ha hC, fun φ => ?_⟩
  constructor
  · rw [radialMeasure_eq_positiveScalar_productHaar K S]
    exact (hb φ).1.smul_measure_nnreal
  · rw [radialMeasure_eq_positiveScalar_productHaar K S,
      integral_smul_nnreal_measure, NNReal.smul_def]
    change (a : ℝ) * (∫ x : G, weightedTensorAbsolute K S φ ψ σ x
      ∂sLocalProductMultiplicativeHaar K S) ≤ _
    exact (mul_le_mul_of_nonneg_left (hb φ).2 ha.le).trans_eq (mul_assoc _ _ _).symm

end HeckeGeneral.Analysis.ActualSLocalPositiveMomentDraft
