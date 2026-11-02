import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MellinPreprocessing
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.StepOutputAdapter

/-!
# Apply the strict output inside the actual Mellin preprocessing integral

The Mellin models have the parent's width and are not recursive calls.
For each fixed Mellin frequency the canonical strict output is consumed
first, using bounds only for its actual ordinary children.  The output's
terminal and mass conclusions then give one scalar bound, which is
integrated in the already constructed outer Mellin measure.

No measurability of a frequency-dependent engine kernel, no measurable
space on whole models, and no bind of engine measures are requested.
The strict child's width decrease remains the canonical output's own
`left_width` and `right_width` conclusion; the explicit child bounds in
this consumer are the usual induction hypotheses, not parent estimates.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Set
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical BigOperators

universe u

variable {K : Type} [Field K] [NumberField K]
variable {omegaCharacter psiCharacter : HeckeCharacter K}
variable {Ω : Type u} [MeasurableSpace Ω]

/-- A single genuine output, after applying the ordinary induction
hypothesis to its strictly smaller actual children.  Its original
positive kernels and four terminal terms are used unchanged. -/
theorem engineOutput_bound_of_children
    {n : Node K omegaCharacter psiCharacter} {U sigma delta beta C control D : ℝ}
    {admissible : MomentData K omegaCharacter psiCharacter → RealParameters → Prop}
    (out : n.EngineOutput (Ω := Ω) U sigma delta beta C control admissible)
    (hU : 0 < U) (hD : 0 ≤ D)
    (hleft : ∀ branch parameter,
      (Node.ordinary (out.leftData branch parameter) (out.leftParameters branch)).normalizedEnergy
        U 0 ≤ D)
    (hright : ∀ branch parameter,
      (Node.ordinary (out.rightData branch parameter) (out.rightParameters branch)).normalizedEnergy
        U 0 ≤ D) :
    n.normalizedEnergy U 0 ≤ C * control * (U ^ beta + U ^ delta * D) := by
  have hbound (branch : Fin out.branches) (value : Ω → ℝ)
      (hi : Integrable value (out.kernel branch)) (hb : ∀ parameter, value parameter ≤ D) :
      (∫ parameter, value parameter ∂out.kernel branch) ≤
        (out.kernel branch).real Set.univ * D := by
    letI : IsFiniteMeasure (out.kernel branch) := out.finite_kernel branch
    simpa only [integral_const, smul_eq_mul] using
      integral_mono hi (integrable_const D) hb
  have hlinear := out.linearized hU
  change n.normalizedEnergy U 0 ≤ _ at hlinear
  calc
    n.normalizedEnergy U 0 ≤ C * control * U ^ beta +
        ∑ branch, ((∫ parameter, EngineStep.normalizedPairedEnergy
          (out.leftData branch parameter) (out.leftParameters branch) U
            (out.leftTwist branch parameter) ∂out.kernel branch) +
          ∫ parameter, EngineStep.normalizedPairedEnergy
            (out.rightData branch parameter) (out.rightParameters branch) U
              (out.rightTwist branch parameter) ∂out.kernel branch) / 2 := hlinear
    _ ≤ C * control * U ^ beta +
        ∑ branch, (out.kernel branch).real Set.univ * D := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro branch _
      have hl := hbound branch _ (out.left_integrable branch) (fun parameter => by
        simpa only [ordinary_normalizedEnergy, out.leftTwist_zero] using hleft branch parameter)
      have hr := hbound branch _ (out.right_integrable branch) (fun parameter => by
        simpa only [ordinary_normalizedEnergy, out.rightTwist_zero] using hright branch parameter)
      exact (div_le_div_of_nonneg_right (add_le_add hl hr)
        (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
    _ = C * control * U ^ beta + (∑ branch, (out.kernel branch).real Set.univ) * D := by
      rw [Finset.sum_mul]
    _ ≤ C * control * U ^ beta + (C * control * U ^ delta) * D :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right out.mass hD)
    _ = C * control * (U ^ beta + U ^ delta * D) := by ring

/-- Uniform actual Mellin preprocessing followed by the canonical strict
output at each frequency.  The outer constant and window normalization
are chosen before the parent profile budget, the model, and the scale.
The same-width intermediate models are handled only by the strict
theorem; induction is used solely for its genuine smaller children. -/
theorem exists_centeredMellin_strict_transfer
    (cap J : ℕ) (A a b : ℝ) (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b) :
    ∃ E : ℝ, ∃ hE : 1 ≤ E, ∃ Cm : ℝ, 0 ≤ Cm ∧
      ∀ (P : ℝ) (hP : 1 ≤ P),
      let hP₂ : 1 ≤ 2 * P := by linarith
      let B := annularPlateau a b ha hab
      ∀ (n : Node K omegaCharacter psiCharacter) (U : ℝ), 0 < U →
        n.data.geometry.slotCount ≤ cap →
        ModelProfileControl n.data (J + 2) A P 0 a b 0 →
        let child := fun frequency : ℝ × ℝ =>
          (n.freezeTime 0).normalizedMellinPlain B B (2 * P) hP₂ E hE J frequency
        (∀ frequency : ℝ × ℝ,
          ProfileTimeIndependent (child frequency).data ∧
          ModelProfileControl (child frequency).data J A 1 0 (a / 2) (2 * b) 0) ∧
        ∀ sigma delta beta C control D : ℝ, 0 ≤ D →
        ∀ admissible : (ℝ × ℝ) →
          MomentData K omegaCharacter psiCharacter → RealParameters → Prop,
        ∀ outputs : ∀ frequency : ℝ × ℝ,
          (child frequency).EngineOutput (Ω := Ω) U sigma delta beta C control
            (admissible frequency),
        (∀ frequency branch parameter,
          (Node.ordinary ((outputs frequency).leftData branch parameter)
            ((outputs frequency).leftParameters branch)).normalizedEnergy U 0 ≤ D) →
        (∀ frequency branch parameter,
          (Node.ordinary ((outputs frequency).rightData branch parameter)
            ((outputs frequency).rightParameters branch)).normalizedEnergy U 0 ≤ D) →
        n.normalizedEnergy U 0 ≤
          Cm * P ^ (2 * (cap + 2)) * (C * control * (U ^ beta + U ^ delta * D)) := by
  obtain ⟨E, hE, Cm, hCm, hpre⟩ := exists_centeredMellin_preprocessing
    (K := K) (omegaCharacter := omegaCharacter) (psiCharacter := psiCharacter)
      cap J A a b hA ha hab
  refine ⟨E, hE, Cm, hCm, ?_⟩
  intro P hP
  dsimp only
  intro n U hU hcap hprofile
  have hP₂ : 1 ≤ 2 * P := by linarith
  let B := annularPlateau a b ha hab
  let child := fun frequency : ℝ × ℝ =>
    (n.freezeTime 0).normalizedMellinPlain B B (2 * P) hP₂ E hE J frequency
  let μ := rowEnergyKernel ((volume : Measure ℝ).prod volume)
    (mellinPairEnvelope cap J (2 * P) E)
  obtain ⟨hfinite, hmass, hunit, hint, hparent⟩ := hpre P hP n U hU hcap hprofile
  refine ⟨hunit, ?_⟩
  intro sigma delta beta C control D hD admissible outputs hleft hright
  letI : IsFiniteMeasure μ := hfinite
  have hwidth (frequency : ℝ × ℝ) : (child frequency).width = n.width := rfl
  have hnormalized : Integrable
      (fun frequency : ℝ × ℝ => (child frequency).normalizedEnergy U 0) μ := by
    simpa only [Node.normalizedEnergy, hwidth] using hint.div_const (U ^ n.width)
  have hscalar (frequency : ℝ × ℝ) :
      (child frequency).normalizedEnergy U 0 ≤ C * control * (U ^ beta + U ^ delta * D) :=
    engineOutput_bound_of_children (outputs frequency) hU hD
      (hleft frequency) (hright frequency)
  have hpreNormalized : n.normalizedEnergy U 0 ≤
      ∫ frequency : ℝ × ℝ, (child frequency).normalizedEnergy U 0 ∂μ := by
    simp_rw [Node.normalizedEnergy, hwidth]
    rw [integral_div]
    exact div_le_div_of_nonneg_right hparent (Real.rpow_pos_of_pos hU n.width).le
  have houter := integral_mono hnormalized
    (integrable_const (C * control * (U ^ beta + U ^ delta * D))) hscalar
  simp only [integral_const, smul_eq_mul] at houter
  rw [hmass] at houter
  exact hpreNormalized.trans houter

end HeckeSkeleton.Moments.EngineInduction
