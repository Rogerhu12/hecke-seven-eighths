import Expansion.PhysicalRecipePresentation
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The norm bound survives the actual finite-pattern transport

Each receiving row carries at most one original row kernel at each
physical point.  Consequently the finite collection of row patterns costs
no cardinality factor.  The only integration loss is the volume `8T³` of
the original three-dimensional contour box.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinPhysicalNorm

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open Expansion.Project ExpansionInterfaces Expansion.CommonSampleTransport
open scoped Classical BigOperators

theorem physicalHeightBox_measure_lt_top (T : ℝ) (hT : 0 ≤ T) :
    physicalHeightVolume {p : Fin 3 → ℝ | ‖p‖ ≤ T} < ⊤ := by
  rw [physicalHeightVolume, physicalHeightEquiv.map_apply,
    physicalHeightEquiv_preimage_box T hT]
  change ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume))
    (Icc (-T) T ×ˢ (Icc (-T) T ×ˢ Icc (-T) T)) < ⊤
  exact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).measure_lt_top

theorem physicalHeightBox_volume_real (T : ℝ) (hT : 0 ≤ T) :
    physicalHeightVolume.real {p : Fin 3 → ℝ | ‖p‖ ≤ T} = 8 * T ^ 3 := by
  have hm : physicalHeightVolume {p : Fin 3 → ℝ | ‖p‖ ≤ T} =
      rowHeightVolume (rowRetainedHeightBox T) := by
    rw [physicalHeightVolume, physicalHeightEquiv.map_apply,
      physicalHeightEquiv_preimage_box T hT]
  rw [Measure.real, hm]
  change ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume)).real
    (Icc (-T) T ×ˢ (Icc (-T) T ×ˢ Icc (-T) T)) = _
  rw [measureReal_prod_prod, measureReal_prod_prod]
  simp only [Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal (show 0 ≤ T - -T by linarith)]
  ring

variable {K : Type} [Field K] [NumberField K]
variable {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
variable {P : ProbeData K S} {R : RowCharacterInput K S P}
variable {omega psi : HeckeCharacter K} {g : PrimeWindowGeometry}
variable {F : RecipeFamily K psi g} {N : ℕ}

/-- A transported contribution obeys the common bound for the actual
moving fiber, independently of the number of possible row patterns. -/
theorem physicalBlockLabelIntegrand_norm_le
    (width cap Z : ℝ) (rows : Finset (FrequencyRow K S))
    (b : RecipeBlockData K S psi g F N)
    (hcard : Fintype.card (AmplitudeLabels g.slots width cap) ≤ N)
    (kernel : FrequencyRow K S → (Fin 3 → ℝ) → ℂ)
    (label : AmplitudeLabels g.slots width cap) (p : Fin 3 → ℝ)
    (hmax : (recipeAmplitudeRows K S P R omega psi g F width cap Z rows p label).card ≤
      (physicalBlockLabelRows (P := P) (R := R) (ω := omega) width cap Z rows b hcard label).card)
    {C : ℝ} (hC : 0 ≤ C)
    (hkernel : ∀ u ∈ recipeAmplitudeRows K S P R omega psi g F width cap Z rows p label,
      ‖kernel u p‖ ≤ C) (u : FrequencyRow K S) :
    ‖physicalBlockLabelIntegrand (P := P) (R := R) (ω := omega)
      width cap Z rows b hcard kernel label u p‖ ≤ C := by
  dsimp only [physicalBlockLabelIntegrand]
  split_ifs with hu
  · apply movingPiece_norm_le _ _ _ kernel p _ C hC hkernel
    exact mem_patterns.mpr
      ⟨recipeAmplitudeRows_subset K S P R omega psi g F width cap Z rows p label, hmax⟩
  · simpa only [norm_zero] using hC

/-- The exact physical integral costs only the actual box volume.
The original recipe's absolute-integrability theorem justifies its exact
integral identities; this norm inequality uses the uniform pointwise bound. -/
theorem physicalBlockShiftedPiece_norm_le
    (width cap Z T U : ℝ) (hT : 0 ≤ T)
    (rows : Finset (FrequencyRow K S)) (sector : SixthUnitClasses K S)
    (b : RecipeBlockData K S psi g F N)
    (hcard : Fintype.card (AmplitudeLabels g.slots width cap) ≤ N)
    (kernel : FrequencyRow K S → (Fin 3 → ℝ) → ℂ)
    (label : AmplitudeLabels g.slots width cap)
    (horigin : PhysicalAmplitudeOrigin K S P R omega psi g F width cap Z T U rows sector label
      (b.amplitude (physicalAmplitudeLabelEmbedding g.slots width cap hcard label)))
    {C : ℝ} (hC : 0 ≤ C)
    (hkernel : ∀ p : Fin 3 → ℝ, ‖p‖ ≤ T →
      ∀ u ∈ recipeAmplitudeRows K S P R omega psi g F width cap Z rows p label,
        ‖kernel u p‖ ≤ C) (u : FrequencyRow K S) :
    ‖physicalBlockShiftedPiece (P := P) (R := R) (ω := omega)
      width cap Z T rows b hcard physicalHeightVolume kernel
        (physicalAmplitudeLabelEmbedding g.slots width cap hcard label) u‖ ≤ C * (8 * T ^ 3) := by
  rw [physicalBlockShiftedPiece_embed]
  have hp (p : Fin 3 → ℝ) (hp : p ∈ {q : Fin 3 → ℝ | ‖q‖ ≤ T}) :
      ‖physicalBlockLabelIntegrand (P := P) (R := R) (ω := omega)
        width cap Z rows b hcard kernel label u p‖ ≤ C := by
    apply physicalBlockLabelIntegrand_norm_le width cap Z rows b hcard kernel label p _ hC
      (hkernel p hp) u
    have hm := horigin.2.2.2.2 p hp
    rw [horigin.2.2.2.1] at hm
    exact hm
  simpa only [physicalHeightBox_volume_real T hT] using
    norm_setIntegral_le_of_norm_le_const (physicalHeightBox_measure_lt_top T hT) hp

end HeckeSkeleton.HighBinPhysicalNorm

#print axioms HeckeSkeleton.HighBinPhysicalNorm.physicalHeightBox_volume_real
#print axioms HeckeSkeleton.HighBinPhysicalNorm.physicalBlockShiftedPiece_norm_le
