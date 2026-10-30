import HeckeSkeleton.SmallRadius.ComplexMultiplicativeHaarDensity
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
Ported from the old repository cache candidate of 2026-10-12; compiled in this project.
The actual mixed ring of a totally complex number field has no real
coordinates. The literal second projection is a topological multiplicative
equivalence, and hence its units are the finite product of complex units.
The Haar comparison has a strictly positive scalar, retained explicitly.
No Fourier/Riesz or tensor factorization statement is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.Analysis.SLocalRadialHaarDraft.TotallyComplexHaarDraft

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open IsDedekindDomain MeasureTheory MeasureTheory.Measure
open HeckeGeneral.Arithmetic HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical BigOperators NNReal

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]

abbrev ComplexPlace := {v : InfinitePlace K // v.IsComplex}

local instance realPlace_isEmpty : IsEmpty {v : InfinitePlace K // v.IsReal} :=
  ⟨fun v => (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v.val)) v.prop⟩

/-- This forgets only the literally empty real coordinate family. -/
def mixedComplexRingEquiv : mixedSpace K ≃+* (ComplexPlace K → ℂ) where
  toFun := Prod.snd
  invFun z := (0, z)
  left_inv x := by
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

def mixedComplexMulEquiv : mixedSpace K ≃ₜ* (ComplexPlace K → ℂ) where
  __ := (mixedComplexRingEquiv K).toMulEquiv
  continuous_toFun := continuous_snd
  continuous_invFun := continuous_const.prodMk continuous_id

def mixedComplexUnitsEquiv : (mixedSpace K)ˣ ≃ₜ* (ComplexPlace K → ℂˣ) :=
  (Units.mapContinuousMulEquiv (mixedComplexMulEquiv K)).trans
    ContinuousMulEquiv.piUnits

@[simp] theorem mixedComplexUnitsEquiv_apply (u : (mixedSpace K)ˣ) (v : ComplexPlace K) :
    (mixedComplexUnitsEquiv K u v : ℂ) = (u : mixedSpace K).2 v := rfl

@[simp] theorem mixedComplexUnitsEquiv_symm_coe (t : ComplexPlace K → ℂˣ)
    (v : ComplexPlace K) :
    ((mixedComplexUnitsEquiv K).symm t : mixedSpace K).2 v = (t v : ℂ) := rfl

def allPlacesComplexEquiv : InfinitePlace K ≃ ComplexPlace K where
  toFun v := ⟨v, IsTotallyComplex.isComplex v⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl

/-- The multiplicative norm becomes the product of squared complex norms. -/
theorem mixedNorm_symm_complexUnits (t : ComplexPlace K → ℂˣ) :
    mixedEmbedding.norm ((mixedComplexUnitsEquiv K).symm t : mixedSpace K) =
      ∏ v : ComplexPlace K, ‖(t v : ℂ)‖ ^ 2 := by
  rw [mixedEmbedding.norm_apply]
  refine Fintype.prod_equiv (allPlacesComplexEquiv K) _ _ ?_
  intro v
  rw [IsTotallyComplex.mult_eq,
    normAtPlace_apply_of_isComplex (IsTotallyComplex.isComplex v),
    mixedComplexUnitsEquiv_symm_coe]
  rfl

variable [MeasurableSpace ℂˣ] [BorelSpace ℂˣ]
variable [MeasurableSpace (mixedSpace K)ˣ] [BorelSpace (mixedSpace K)ˣ]

local instance : SecondCountableTopology (mixedSpace K)ˣ := by
  letI : SecondCountableTopology (mixedSpace K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

local instance : SecondCountableTopology ℂˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

def complexUnitsProductHaar : Measure (ComplexPlace K → ℂˣ) :=
  Measure.pi (fun _ : ComplexPlace K => (Measure.haar : Measure ℂˣ))

instance complexUnitsProductHaar_isHaar : IsHaarMeasure (complexUnitsProductHaar K) := by
  unfold complexUnitsProductHaar
  infer_instance

def mixedComplexProductHaar : Measure (mixedSpace K)ˣ :=
  Measure.map (mixedComplexUnitsEquiv K).symm (complexUnitsProductHaar K)

instance mixedComplexProductHaar_isHaar : IsHaarMeasure (mixedComplexProductHaar K) := by
  unfold mixedComplexProductHaar
  infer_instance

def mixedComplexHaarScalar : ℝ≥0 :=
  haarScalarFactor (mixedMultiplicativeHaar K) (mixedComplexProductHaar K)

theorem mixedComplexHaarScalar_pos : 0 < mixedComplexHaarScalar K :=
  haarScalarFactor_pos_of_isHaarMeasure _ _

theorem mixedMultiplicativeHaar_eq_complexProduct :
    mixedMultiplicativeHaar K = mixedComplexHaarScalar K • mixedComplexProductHaar K :=
  isMulLeftInvariant_eq_smul _ _

theorem integral_mixedMultiplicativeHaar_eq_complexProduct (f : (mixedSpace K)ˣ → ℂ) :
    (∫ u, f u ∂mixedMultiplicativeHaar K) =
      ((mixedComplexHaarScalar K : ℝ) : ℂ) *
        ∫ t, f ((mixedComplexUnitsEquiv K).symm t) ∂complexUnitsProductHaar K := by
  rw [mixedMultiplicativeHaar_eq_complexProduct K, integral_smul_nnreal_measure,
    NNReal.smul_def, Complex.real_smul]
  congr 1
  exact (mixedComplexUnitsEquiv K).symm.toHomeomorph.measurableEmbedding.integral_map f

theorem integrable_mixedMultiplicativeHaar_of_complexProduct
    (f : (mixedSpace K)ˣ → ℂ)
    (hf : Integrable (fun t => f ((mixedComplexUnitsEquiv K).symm t))
      (complexUnitsProductHaar K)) :
    Integrable f (mixedMultiplicativeHaar K) := by
  rw [mixedMultiplicativeHaar_eq_complexProduct K]
  apply Integrable.smul_measure_nnreal
  exact ((mixedComplexUnitsEquiv K).symm.toHomeomorph.measurableEmbedding.integrable_map_iff).mpr hf

/-- This is the literal original mixed Fourier factor, transported to all complex places. -/
theorem integral_weightedMixedFourierFactor_eq_complexProduct
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (W : AdditiveProbeTest K S) (z : ℂ) :
    (∫ u, weightedMixedFourierFactor K S W z u ∂mixedMultiplicativeHaar K) =
      ((mixedComplexHaarScalar K : ℝ) : ℂ) *
        ∫ t, weightedMixedFourierFactor K S W z ((mixedComplexUnitsEquiv K).symm t)
          ∂complexUnitsProductHaar K :=
  integral_mixedMultiplicativeHaar_eq_complexProduct K _

end HeckeGeneral.Analysis.SLocalRadialHaarDraft.TotallyComplexHaarDraft
