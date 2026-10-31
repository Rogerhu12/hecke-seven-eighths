import Expansion.PhysicalAmplitudeSource
import Expansion.CommonSampleTransport
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Measurable actual amplitude fibers and their exact transported integrals

The physical prime windows have fixed support. Only their complex power
depends on the common physical point. Consequently the actual finite slot
polynomials, their rounded labels, and every row-membership predicate are
measurable. The original kernel on a moving label can therefore be
transported to its common sampled rows without changing its integral.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Classical BigOperators

namespace ExpansionInterfaces

theorem measurable_amplitudeCode (width cap : ℝ) :
    Measurable (amplitudeCode width cap) := by
  let clip : ℕ → AmplitudeCode width cap := fun n =>
    ⟨min (Nat.floor (cap / width) + 1) n,
      Nat.lt_of_le_of_lt (min_le_left _ _) (by omega)⟩
  exact (measurable_of_countable clip).comp (measurable_id.div_const width).nat_floor

theorem measurable_slotCode (width cap P : ℝ) :
    Measurable (slotCode width cap P) := by
  unfold slotCode
  apply Measurable.ite (measurableSet_eq_fun measurable_id measurable_const)
    measurable_const
  exact (measurable_amplitudeCode width cap).comp
    ((Real.measurable_log.comp measurable_norm).div_const (Real.log P))

end ExpansionInterfaces

namespace Expansion.Project

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open ExpansionInterfaces
open Expansion.CommonSampleTransport

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)
variable (ω ψ : HeckeCharacter K) (g : PrimeWindowGeometry)

/-- The literal physical slots are measurable in the common physical point.
The original window support is independent of `slotTime`. -/
theorem measurable_recipePhysicalSlots (F : RecipeFamily K ψ g)
    (hF : ∀ j, Measurable (F.slotPower j)) (Z : ℝ)
    (j : Fin g.slots) (u : FrequencyRow K S) :
    Measurable (fun p => recipePhysicalSlots K S P R ω ψ g F Z p j u) := by
  let X := physicalSlotBase g.slots Z
  let d := F.slotModel K S P R ω ψ g 0 u.sector
  change Measurable (fun p : Fin 3 → ℝ =>
    (Real.sqrt X : ℂ)⁻¹ * ∑ q ∈ analyticPrimeSupport K (g.weight j).toFun X,
      primeCoefficient K (d.rowCharacter u.ideal.val * F.slotCoefficient j) q *
        ((g.weight j).toFun ((Ideal.absNorm q.asIdeal : ℝ) / X) *
          profilePower (F.slotPower j p) ((Ideal.absNorm q.asIdeal : ℝ) / X)) *
        maskValue d u.ideal.val q.asIdeal)
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro q _hq
  exact (measurable_const.mul (measurable_const.mul
    (Complex.measurable_exp.comp (measurable_const.mul (hF j))))).mul measurable_const

/-- Membership in each actual rounded amplitude fiber is measurable. -/
theorem measurableSet_recipeAmplitudeRows_mem (F : RecipeFamily K ψ g)
    (hF : ∀ j, Measurable (F.slotPower j)) (width cap Z : ℝ)
    (rows : Finset (FrequencyRow K S))
    (label : AmplitudeLabels g.slots width cap) (u : FrequencyRow K S) :
    MeasurableSet {p | u ∈ recipeAmplitudeRows K S P R ω ψ g F width cap Z rows p label} := by
  by_cases hu : u ∈ rows
  · have hcode : Measurable (fun p : Fin 3 → ℝ => fun j : Fin g.slots =>
        slotCode width cap (physicalSlotBase g.slots Z)
          (recipePhysicalSlots K S P R ω ψ g F Z p j u)) :=
      measurable_pi_iff.mpr fun j =>
        (measurable_slotCode width cap (physicalSlotBase g.slots Z)).comp
          (measurable_recipePhysicalSlots K S P R ω ψ g F hF Z j u)
    simpa only [recipeAmplitudeRows, rowPiece, Finset.mem_filter, hu, true_and]
      using measurableSet_eq_fun hcode (measurable_const (c := label))
  · simp only [recipeAmplitudeRows, rowPiece, Finset.mem_filter, hu, false_and,
      Set.setOf_false, MeasurableSet.empty]

/-- No independent measurability assumption on a chosen row pattern is
needed: the finite actual slot fibers supply it. -/
theorem measurableSet_recipeAmplitudeRows_eq (F : RecipeFamily K ψ g)
    (hF : ∀ j, Measurable (F.slotPower j)) (width cap Z : ℝ)
    (rows : Finset (FrequencyRow K S))
    (label : AmplitudeLabels g.slots width cap)
    (A : Finset (FrequencyRow K S)) (hA : A ⊆ rows) :
    MeasurableSet {p | recipeAmplitudeRows K S P R ω ψ g F width cap Z rows p label = A} :=
  measurableSet_rows_eq rows
    (fun p => recipeAmplitudeRows K S P R ω ψ g F width cap Z rows p label)
    (fun p => recipeAmplitudeRows_subset K S P R ω ψ g F width cap Z rows p label)
    (fun u _ => measurableSet_recipeAmplitudeRows_mem K S P R ω ψ g F hF
      width cap Z rows label u) A hA

/-- The transported contributions integrate the unchanged original kernel
on one actual label. The common sample is precisely the one supplied by
the physical amplitude source; its sole role here is the proved count bound. -/
theorem recipeAmplitude_exact_integral (F : RecipeFamily K ψ g)
    (hF : ∀ j, Measurable (F.slotPower j)) (width cap Z T : ℝ)
    (rows : Finset (FrequencyRow K S))
    (label : AmplitudeLabels g.slots width cap) (sample : Fin 3 → ℝ)
    (hmax : ∀ p : Fin 3 → ℝ, ‖p‖ ≤ T →
      (recipeAmplitudeRows K S P R ω ψ g F width cap Z rows p label).card ≤
        (recipeAmplitudeRows K S P R ω ψ g F width cap Z rows sample label).card)
    (μ : Measure (Fin 3 → ℝ)) (kernel : FrequencyRow K S → (Fin 3 → ℝ) → ℂ)
    (hkernel : ∀ u ∈ rows, IntegrableOn (kernel u) {p | ‖p‖ ≤ T} μ) :
    let target := recipeAmplitudeRows K S P R ω ψ g F width cap Z rows sample label
    let moving := fun p => recipeAmplitudeRows K S P R ω ψ g F width cap Z rows p label
    (∑ v : target, ∫ p in {p : Fin 3 → ℝ | ‖p‖ ≤ T},
      movingPiece rows target moving kernel v p ∂μ) =
        ∫ p in {p : Fin 3 → ℝ | ‖p‖ ≤ T}, ∑ u ∈ moving p, kernel u p ∂μ := by
  dsimp only
  apply exact_integral_identity μ {p : Fin 3 → ℝ | ‖p‖ ≤ T}
    (measurableSet_le measurable_norm measurable_const) rows _ _ kernel hkernel
  · intro A hA
    exact measurableSet_recipeAmplitudeRows_eq K S P R ω ψ g F hF
      width cap Z rows label A (mem_patterns.mp hA).1
  · intro p _
    exact recipeAmplitudeRows_subset K S P R ω ψ g F width cap Z rows p label
  · exact hmax

/-- All actual amplitude labels together preserve the complete fixed-row
integral. The sample may vary with the finite label, but the original
kernel, physical domain, and arithmetic row set remain the same. -/
theorem recipeAmplitude_full_integral (F : RecipeFamily K ψ g)
    (hF : ∀ j, Measurable (F.slotPower j)) (width cap Z T : ℝ)
    (rows : Finset (FrequencyRow K S))
    (sample : AmplitudeLabels g.slots width cap → (Fin 3 → ℝ))
    (hmax : ∀ label, ∀ p : Fin 3 → ℝ, ‖p‖ ≤ T →
      (recipeAmplitudeRows K S P R ω ψ g F width cap Z rows p label).card ≤
        (recipeAmplitudeRows K S P R ω ψ g F width cap Z rows (sample label) label).card)
    (μ : Measure (Fin 3 → ℝ)) (kernel : FrequencyRow K S → (Fin 3 → ℝ) → ℂ)
    (hkernel : ∀ u ∈ rows, IntegrableOn (kernel u) {p | ‖p‖ ≤ T} μ) :
    (∑ label : AmplitudeLabels g.slots width cap,
      let target := recipeAmplitudeRows K S P R ω ψ g F width cap Z rows
        (sample label) label
      let moving := fun p => recipeAmplitudeRows K S P R ω ψ g F width cap Z rows p label
      ∑ v : target, ∫ p in {p : Fin 3 → ℝ | ‖p‖ ≤ T},
        movingPiece rows target moving kernel v p ∂μ) =
      ∫ p in {p : Fin 3 → ℝ | ‖p‖ ≤ T}, ∑ u ∈ rows, kernel u p ∂μ := by
  let D : Set (Fin 3 → ℝ) := {p | ‖p‖ ≤ T}
  have hD : MeasurableSet D := measurableSet_le measurable_norm measurable_const
  let moving := fun label p =>
    recipeAmplitudeRows K S P R ω ψ g F width cap Z rows p label
  let target := fun label => moving label (sample label)
  have hsets (label : AmplitudeLabels g.slots width cap)
      (A : Finset (FrequencyRow K S)) (hA : A ∈ patterns rows (target label)) :
      MeasurableSet {p | moving label p = A} :=
    measurableSet_recipeAmplitudeRows_eq K S P R ω ψ g F hF width cap Z rows label A
      (mem_patterns.mp hA).1
  have hintegrable (label : AmplitudeLabels g.slots width cap) :
      IntegrableOn (fun p => ∑ u ∈ moving label p, kernel u p) D μ := by
    have ht : IntegrableOn
        (fun p => ∑ v : target label, movingPiece rows (target label) (moving label) kernel v p)
        D μ := integrable_finsetSum Finset.univ (fun v _ =>
          movingPiece_integrable μ D rows (target label) (moving label) kernel hkernel
            (hsets label) v)
    apply ht.congr
    filter_upwards [ae_restrict_mem hD] with p hp
    exact sum_movingPiece rows (target label) (moving label) kernel p
      (mem_patterns.mpr
        ⟨recipeAmplitudeRows_subset K S P R ω ψ g F width cap Z rows p label,
          hmax label p hp⟩)
  calc
    _ = ∑ label : AmplitudeLabels g.slots width cap,
        ∫ p in D, ∑ u ∈ moving label p, kernel u p ∂μ := by
      apply Finset.sum_congr rfl
      intro label _
      exact recipeAmplitude_exact_integral K S P R ω ψ g F hF width cap Z T rows label
        (sample label) (hmax label) μ kernel hkernel
    _ = ∫ p in D, ∑ label : AmplitudeLabels g.slots width cap,
        ∑ u ∈ moving label p, kernel u p ∂μ :=
      (integral_finsetSum Finset.univ (fun label _ => hintegrable label)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p =>
        sum_rowPiece rows (fun u j => slotCode width cap (physicalSlotBase g.slots Z)
          (recipePhysicalSlots K S P R ω ψ g F Z p j u)) (fun u => kernel u p))

end Expansion.Project

#print axioms ExpansionInterfaces.measurable_slotCode
#print axioms Expansion.Project.measurable_recipePhysicalSlots
#print axioms Expansion.Project.recipeAmplitude_exact_integral
#print axioms Expansion.Project.recipeAmplitude_full_integral
