module

public import DedekindZetaZeroFree.Adeles.Haar.PolarProduct
public import Mathlib.Analysis.MellinTransform
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-!
# Radial integrals for the actual archimedean Haar measure

The source stores a product of the positive-axis Haar measure and an
arbitrary angular Haar measure, transported by its actual polar map.
This module retains the angular mass when integrating a radial profile.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ThetaGlobal.LocalArchHaar

open MeasureTheory NumberField DedekindZetaZeroFree
open ThetaPositiveSheetMellin ThetaProfileHaarSheets
open scoped ENNReal

variable {F : Type} [Field F] [NumberField F]

def normSq (w : InfinitePlace F) (z : w.Completionˣ) : ℝ := ‖z.val‖ ^ 2

theorem normSq_continuous (w : InfinitePlace F) : Continuous (normSq w) :=
  Units.continuous_val.norm.pow 2

theorem normSq_pos (w : InfinitePlace F) (z : w.Completionˣ) : 0 < normSq w z :=
  sq_pos_of_pos (norm_pos_iff.mpr z.ne_zero)

theorem normSq_polarUnit (A : SArithmeticData F) (w : InfinitePlace F)
    (p : PositiveAxis × Circle) : normSq w (polarUnit A w p) = p.1.val := by
  rw [← polarEquiv_eq]
  change ‖(InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (A.complex_place w)).symm (complexPolar p).val‖ ^ 2 = _
  rw [(InfinitePlace.Completion.isometryEquivComplexOfIsComplex
    (A.complex_place w)).symm.isometry.norm_map_of_map_zero
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (A.complex_place w)).symm.map_zero) (complexPolar p).val]
  exact congrArg (fun q : PositiveAxis × Circle => q.1.val) (complexPolar_left_inv p)

theorem polarUnit_continuous (A : SArithmeticData F) (w : InfinitePlace F) :
    Continuous (polarUnit A w) := by
  have he : polarUnit A w = polarEquiv A w :=
    funext fun p => (polarEquiv_eq A w p).symm
  rw [he]
  exact (polarEquiv A w).continuous

/-- The radial measure retains the mass of the actual angular factor. -/
theorem map_normSq_archHaar (A : SArithmeticData F) (w : InfinitePlace F)
    (ν : Measure Circle) [IsFiniteMeasure ν] :
    Measure.map (normSq w) (archHaar A w ν) =
      (ν Set.univ) • Measure.map (Subtype.val : PositiveAxis → ℝ) positiveHaar := by
  unfold archHaar
  rw [Measure.map_map (normSq_continuous w).measurable
    (polarUnit_continuous A w).measurable]
  have he : normSq w ∘ polarUnit A w =
      (Subtype.val : PositiveAxis → ℝ) ∘ Prod.fst := by
    funext p
    exact normSq_polarUnit A w p
  rw [he, ← Measure.map_map measurable_subtype_coe measurable_fst,
    Measure.map_fst_prod,
    Measure.map_smul _ measurable_subtype_coe.aemeasurable]

theorem radial_integrable (A : SArithmeticData F) (w : InfinitePlace F)
    (ν : Measure Circle) [IsFiniteMeasure ν] (f : ℝ → ℂ)
    (hf : Integrable (fun t : PositiveAxis => f t.val) positiveHaar) :
    Integrable (fun z : w.Completionˣ => f (normSq w z)) (archHaar A w ν) := by
  have he : MeasurableEmbedding (Subtype.val : PositiveAxis → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ioi
  have hi : Integrable f (Measure.map (Subtype.val : PositiveAxis → ℝ) positiveHaar) :=
    he.integrable_map_iff.mpr hf
  have hi' := hi.smul_measure (measure_ne_top ν Set.univ)
  rw [← map_normSq_archHaar A w ν] at hi'
  exact hi'.comp_aemeasurable (normSq_continuous w).measurable.aemeasurable

theorem radial_integral (A : SArithmeticData F) (w : InfinitePlace F)
    (ν : Measure Circle) [IsFiniteMeasure ν] (f : ℝ → ℂ)
    (hf : Integrable (fun t : PositiveAxis => f t.val) positiveHaar) :
    (∫ z : w.Completionˣ, f (normSq w z) ∂archHaar A w ν) =
      ((ν Set.univ).toReal : ℂ) * ∫ t : PositiveAxis, f t.val ∂positiveHaar := by
  have he : MeasurableEmbedding (Subtype.val : PositiveAxis → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ioi
  have hi : Integrable f (Measure.map (Subtype.val : PositiveAxis → ℝ) positiveHaar) :=
    he.integrable_map_iff.mpr hf
  have hi' := hi.smul_measure (measure_ne_top ν Set.univ)
  rw [← map_normSq_archHaar A w ν] at hi'
  calc
    _ = ∫ t : ℝ, f t ∂Measure.map (normSq w) (archHaar A w ν) :=
      (integral_map (normSq_continuous w).measurable.aemeasurable
        hi'.aestronglyMeasurable).symm
    _ = _ := by
      rw [map_normSq_archHaar A w ν, integral_smul_measure, he.integral_map]
      rw [Complex.real_smul]

private theorem weighted_density (f : ℝ → ℂ) (s : ℂ) (t : ℝ) (ht : 0 < t) :
    (ENNReal.ofReal t⁻¹).toReal • (f t * (t : ℂ) ^ s) =
      (t : ℂ) ^ (s - 1) * f t := by
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr ht.le), Complex.real_smul,
    Complex.cpow_sub s 1 (Complex.ofReal_ne_zero.mpr ht.ne')]
  simp only [Complex.cpow_one, Complex.ofReal_inv]
  ring

/-- The repository's positive-axis Haar measure is exactly the `dt/t`
measure required by the ordinary Mellin integral. -/
theorem positive_integrable_of_mellin (f : ℝ → ℂ) (s : ℂ)
    (hf : MellinConvergent f s) :
    Integrable (fun t : PositiveAxis => f t.val * (t.val : ℂ) ^ s) positiveHaar := by
  have he : MeasurableEmbedding (Subtype.val : PositiveAxis → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ioi
  have hi : Integrable (fun t : ℝ => (t : ℂ) ^ (s - 1) * f t)
      (volume.restrict (Set.Ioi 0)) := by
    simpa only [MellinConvergent, IntegrableOn, smul_eq_mul] using hf
  change Integrable ((fun t : ℝ => f t * (t : ℂ) ^ s) ∘ Subtype.val) positiveHaar
  rw [← he.integrable_map_iff, positiveHaar_map_val,
    restrict_withDensity measurableSet_Ioi,
    integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (weighted_density f s t ht).symm

theorem positive_integral_eq_mellin (f : ℝ → ℂ) (s : ℂ) :
    (∫ t : PositiveAxis, f t.val * (t.val : ℂ) ^ s ∂positiveHaar) = mellin f s := by
  have he : MeasurableEmbedding (Subtype.val : PositiveAxis → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ioi
  change (∫ t : PositiveAxis, (fun r : ℝ => f r * (r : ℂ) ^ s) t.val
    ∂positiveHaar) = _
  rw [← he.integral_map, positiveHaar_map_val,
    restrict_withDensity measurableSet_Ioi,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  unfold mellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact weighted_density f s t ht

/-- A one-variable Mellin formula gives an integral on the source's
literal completion-unit Haar measure, with its angular mass intact. -/
theorem radial_hasMellin (A : SArithmeticData F) (w : InfinitePlace F)
    (ν : Measure Circle) [IsFiniteMeasure ν] (f : ℝ → ℂ) (s m : ℂ)
    (hf : HasMellin f s m) :
    Integrable (fun z : w.Completionˣ =>
      f (normSq w z) * (normSq w z : ℂ) ^ s) (archHaar A w ν) ∧
      (∫ z : w.Completionˣ, f (normSq w z) * (normSq w z : ℂ) ^ s
        ∂archHaar A w ν) = ((ν Set.univ).toReal : ℂ) * m := by
  have hi := positive_integrable_of_mellin f s hf.1
  refine ⟨radial_integrable A w ν (fun t => f t * (t : ℂ) ^ s) hi, ?_⟩
  rw [radial_integral A w ν (fun t => f t * (t : ℂ) ^ s) hi,
    positive_integral_eq_mellin, hf.2]

end ThetaGlobal.LocalArchHaar

#print axioms ThetaGlobal.LocalArchHaar.map_normSq_archHaar
#print axioms ThetaGlobal.LocalArchHaar.radial_integrable
#print axioms ThetaGlobal.LocalArchHaar.radial_integral
#print axioms ThetaGlobal.LocalArchHaar.positive_integrable_of_mellin
#print axioms ThetaGlobal.LocalArchHaar.positive_integral_eq_mellin
#print axioms ThetaGlobal.LocalArchHaar.radial_hasMellin
