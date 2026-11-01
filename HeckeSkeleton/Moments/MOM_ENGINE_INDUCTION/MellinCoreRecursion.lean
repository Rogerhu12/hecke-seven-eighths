import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MellinScalarStep
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ScalarRecursion

/-!
# Core strong induction after actual Mellin and strict production

The geometric cases are the same as the original core recursion. Base
leaves use their genuine terminal components. Both reflection branches
keep their original positive kernels and apply induction only to their
actual earlier labels. A strict branch first calls the canonical output
at each literal Mellin frequency and integrates its scalar consequence;
there is no same-rank induction call or assumed measurable kernel bind.

Quarter centering substitutes a centered strict scalar estimate and a
real short-comparison reflection locally. The two factors of two cost
exactly 4 in the common coefficient. The resulting finite-rank theorem
uses the unchanged rank, terminal exponent, edge exponent and height
formula. Its scalar local estimate is proved below, never a field of
this producer-facing primitive input.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters MeasureTheory
open HeckeGeneral.Analysis.ConditionalMoments
open scoped BigOperators Classical

universe u

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {Ω : Type u} [MeasurableSpace Ω] {σ W : ℝ}

/-- Actual inputs on their original geometric domains. The engine field
contains original profile control, the selected Mellin template, its
pure coefficient budget, and canonical outputs with genuine labelled
children. There is no parent moment or scalar-recurrence field. -/
structure MellinCoreRecursionInput (S : PolynomialSystem.{u} K ω ψ σ W)
    (U T C H β δ floor padding boundary originalControl : ℝ)
    (admissible : MomentData K ω ψ → RealParameters → Prop) where
  geometry : CoreNodeGeometry S padding
  scale : 1 < U
  coefficient_nonneg : 0 ≤ C
  height_nonneg : 0 ≤ T
  floor_nonneg : 0 ≤ floor
  padding_nonneg : 0 ≤ padding
  boundary_nonneg : 0 ≤ boundary
  boundary_le_floor : boundary ≤ floor / 15
  terminal_budget : terminalBudget floor padding σ boundary ≤ β
  original_profile_bound : originalControl ≤ (1 + T) ^ H
  node_admissible : ∀ x, admissible (S.node x).data (S.node x).parameters
  engine : ∀ x, admissible (S.node x).data (S.node x).parameters →
    EngineStep.PairedEngineDomain (S.node x).centered (S.node x).data
    (S.node x).parameters U (U ^ (S.node x).comparison₁)
      (U ^ (S.node x).comparison₂) floor padding →
        MellinStrictBranchAt (Ω := Ω) S x U T C H β δ admissible
  baseComponents : ∀ x, (S.node x).width ≤ floor →
    (S.node x).parameters.n₁ + (S.node x).parameters.n₂ +
      (S.node x).data.geometry.totalLength ≤ floor + padding + floor / 6 →
        TerminalComponents.{u} ((S.node x).normalizedEnergy U 0)
          U T C H floor padding σ boundary
  shortReflection : ∀ x, floor < (S.node x).width →
    (S.node x).totalLength ≤ (S.node x).width + padding →
    (S.node x).centered = false →
    5 * (S.node x).width / 6 < (S.node x).totalLength →
    ((S.node x).parameters.n₁ ≤ (S.node x).width / 4 ∨
      (S.node x).parameters.n₂ ≤ (S.node x).width / 4) →
        ShortReflectionBranchAt (Ω := Ω) S x U boundary δ β C originalControl
  outerReflection : ∀ x, (S.node x).width + padding < (S.node x).totalLength →
    (S.node x).parameters.z = 0 → (S.node x).centered = false →
      OuterReflectionBranchAt (Ω := Ω) S x U padding δ β C originalControl
  quarterLabels : ∀ x, floor < (S.node x).width →
    (S.node x).totalLength ≤ (S.node x).width + padding →
    (S.node x).centered = false →
    5 * (S.node x).width / 6 < (S.node x).totalLength →
    (S.node x).width / 4 < (S.node x).parameters.n₁ →
    (S.node x).width / 4 < (S.node x).parameters.n₂ → QuarterLabels S x

namespace MellinCoreRecursionInput

variable {S : PolynomialSystem.{u} K ω ψ σ W}
variable {U T C H β δ floor padding boundary originalControl : ℝ}
variable {admissible : MomentData K ω ψ → RealParameters → Prop}

private theorem bound_nonneg
    (input : MellinCoreRecursionInput (Ω := Ω) S U T C H β δ floor padding boundary
      originalControl admissible) (e : ℝ) :
    0 ≤ C * (1 + T) ^ H * U ^ e := by
  have hU : 0 ≤ U := (zero_lt_one.trans input.scale).le
  have hT : 0 ≤ 1 + T := by linarith [input.height_nonneg]
  exact mul_nonneg (mul_nonneg input.coefficient_nonneg (Real.rpow_nonneg hT H))
    (Real.rpow_nonneg hU e)

private theorem profile_scale_bound
    (input : MellinCoreRecursionInput (Ω := Ω) S U T C H β δ floor padding boundary
      originalControl admissible) (e : ℝ) :
    C * originalControl * U ^ e ≤ C * (1 + T) ^ H * U ^ e :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left input.original_profile_bound input.coefficient_nonneg)
    (Real.rpow_nonneg (zero_lt_one.trans input.scale).le e)

private theorem base_bound
    (input : MellinCoreRecursionInput (Ω := Ω) S U T C H β δ floor padding boundary
      originalControl admissible) (x : S.Label)
    (hcore : (S.node x).totalLength ≤ (S.node x).width + padding)
    (hwidth : (S.node x).width ≤ floor) (D : ℝ) (hD : 0 ≤ D) :
    (S.node x).normalizedEnergy U 0 ≤
      C * (1 + T) ^ H * U ^ β + C * (1 + T) ^ H * U ^ δ * D := by
  have hlength : (S.node x).parameters.n₁ + (S.node x).parameters.n₂ +
      (S.node x).data.geometry.totalLength ≤ floor + padding + floor / 6 := by
    rw [← input.geometry.length x]
    change (S.node x).totalLength ≤ floor + padding + floor / 6
    linarith [input.floor_nonneg]
  have hbase := (input.baseComponents x hwidth hlength).bound input.scale.le
    input.floor_nonneg input.padding_nonneg S.sigma_pos.le input.boundary_nonneg
    input.terminal_budget
  exact hbase.trans (le_add_of_nonneg_right (mul_nonneg (input.bound_nonneg δ) hD))

private theorem strict_bound
    (input : MellinCoreRecursionInput (Ω := Ω) S U T C H β δ floor padding boundary
      originalControl admissible) (x : S.Label)
    (hwidth : floor < (S.node x).width)
    (hcore : (S.node x).totalLength ≤ (S.node x).width + padding)
    (hordinary : (S.node x).centered = false →
      (S.node x).totalLength ≤ 5 * (S.node x).width / 6)
    (D : ℝ) (hD : 0 ≤ D)
    (hchildren : ∀ y, ((S.withCoreStages padding).schedule y).Earlier
      ((S.withCoreStages padding).schedule x) → (S.node y).normalizedEnergy U 0 ≤ D) :
    (S.node x).normalizedEnergy U 0 ≤
      C * (1 + T) ^ H * U ^ β + C * (1 + T) ^ H * U ^ δ * D := by
  let branch := input.engine x (input.node_admissible x)
    (input.geometry.engineDomain x input.scale hwidth hcore hordinary)
  exact branch.bound (zero_lt_one.trans input.scale) (input.geometry.length x) D hD hchildren

private theorem short_bound
    (input : MellinCoreRecursionInput (Ω := Ω) S U T C H β δ floor padding boundary
      originalControl admissible) (x : S.Label)
    (hwidth : floor < (S.node x).width)
    (hcore : (S.node x).totalLength ≤ (S.node x).width + padding)
    (hordinary : (S.node x).centered = false)
    (hlarge : 5 * (S.node x).width / 6 < (S.node x).totalLength)
    (hshort : (S.node x).parameters.n₁ ≤ (S.node x).width / 4 ∨
      (S.node x).parameters.n₂ ≤ (S.node x).width / 4)
    (D : ℝ) (hD : 0 ≤ D)
    (hchildren : ∀ y, ((S.withCoreStages padding).schedule y).Earlier
      ((S.withCoreStages padding).schedule x) → (S.node y).normalizedEnergy U 0 ≤ D) :
    (S.node x).normalizedEnergy U 0 ≤
      C * (1 + T) ^ H * U ^ β + C * (1 + T) ^ H * U ^ δ * D := by
  let branch := input.shortReflection x hwidth hcore hordinary hlarge hshort
  have hz := (S.node x).slot_nonneg (input.geometry.length x)
  have hboundary : boundary ≤ (S.node x).width / 15 := by
    linarith [input.boundary_le_floor]
  let localStep := branch.output.toCoreAt padding input.padding_nonneg hz
    (input.geometry.kappa_lower x) (input.geometry.capacity x) hlarge hboundary rfl
  have hterminal : localStep.remainder ≤ C * (1 + T) ^ H * U ^ β :=
    branch.terminal.trans (input.profile_scale_bound β)
  have hmass : (∑ b, (localStep.kernel b).real Set.univ) ≤ C * (1 + T) ^ H * U ^ δ :=
    (branch.output.toCoreAt_mass padding input.padding_nonneg hz
      (input.geometry.kappa_lower x) (input.geometry.capacity x) hlarge hboundary rfl).le.trans
        (branch.mass.trans (input.profile_scale_bound δ))
  exact localStep.bound_of_children hD hterminal hmass hchildren

private theorem outer_bound
    (input : MellinCoreRecursionInput (Ω := Ω) S U T C H β δ floor padding boundary
      originalControl admissible) (x : S.Label)
    (hnoncore : (S.node x).width + padding < (S.node x).totalLength)
    (D : ℝ) (hD : 0 ≤ D)
    (hchildren : ∀ y, ((S.withCoreStages padding).schedule y).Earlier
      ((S.withCoreStages padding).schedule x) → (S.node y).normalizedEnergy U 0 ≤ D) :
    (S.node x).normalizedEnergy U 0 ≤
      C * (1 + T) ^ H * U ^ β + C * (1 + T) ^ H * U ^ δ * D := by
  let branch := input.outerReflection x hnoncore
    (input.geometry.noncore_zero input.padding_nonneg x hnoncore)
    (input.geometry.noncore_ordinary x hnoncore)
  let localStep := branch.output.toAt hnoncore
  have hterminal : localStep.remainder ≤ C * (1 + T) ^ H * U ^ β :=
    branch.terminal.trans (input.profile_scale_bound β)
  have hmass : (∑ b, (localStep.kernel b).real Set.univ) ≤ C * (1 + T) ^ H * U ^ δ :=
    (branch.output.toAt_mass hnoncore).le.trans
      (branch.mass.trans (input.profile_scale_bound δ))
  exact localStep.bound_of_children hD hterminal hmass hchildren

private theorem normalizedEnergy_ordinary_of_false (n : Node K ω ψ)
    (hordinary : n.centered = false) (U t : ℝ) :
    n.normalizedEnergy U t = (Node.ordinary n.data n.parameters).normalizedEnergy U t := by
  have he : n.energy U t = pairedEnergy n.data n.parameters U t := by
    simp only [Node.energy, Node.plainPair, hordinary, Bool.false_eq_true, if_false,
      sub_zero, pairedEnergy]
  change n.energy U t / U ^ n.width =
    (Node.ordinary n.data n.parameters).energy U t / U ^ n.width
  rw [he, Node.ordinary_energy]

private theorem centered_bound
    (input : MellinCoreRecursionInput (Ω := Ω) S U T C H β δ floor padding boundary
      originalControl admissible) (x : S.Label)
    (hwidth : floor < (S.node x).width)
    (hcore : (S.node x).totalLength ≤ (S.node x).width + padding)
    (hordinary : (S.node x).centered = false)
    (hlarge : 5 * (S.node x).width / 6 < (S.node x).totalLength)
    (h₁ : (S.node x).width / 4 < (S.node x).parameters.n₁)
    (h₂ : (S.node x).width / 4 < (S.node x).parameters.n₂)
    (D : ℝ) (hD : 0 ≤ D)
    (hchildren : ∀ y, ((S.withCoreStages padding).schedule y).Earlier
      ((S.withCoreStages padding).schedule x) → (S.node y).normalizedEnergy U 0 ≤ D) :
    (S.node x).normalizedEnergy U 0 ≤
      (4 * C) * (1 + T) ^ H * U ^ β + (4 * C) * (1 + T) ^ H * U ^ δ * D := by
  let labels := input.quarterLabels x hwidth hcore hordinary hlarge h₁ h₂
  let c := labels.center
  let q := labels.comparison
  have hc : S.node c = (S.node x).quarterCentered := labels.center_eq
  have hq : S.node q = (S.node c).comparisonOrdinary := labels.comparison_eq
  have hcwidth : (S.node c).width = (S.node x).width := by
    simpa only [hc] using (S.node x).quarterCentered_width
  have hctotal : (S.node c).totalLength = (S.node x).totalLength := by
    simpa only [hc] using (S.node x).quarterCentered_totalLength
  have hcslots : (S.node c).parameters.z = (S.node x).parameters.z := by
    simp only [hc, Node.quarterCentered_parameters]
  have hcentered : (S.node c).centered = true := by
    simp only [hc, Node.quarterCentered_centered]
  have hcabove : floor < (S.node c).width := by rw [hcwidth]; exact hwidth
  have hccore : (S.node c).totalLength ≤ (S.node c).width + padding := by
    rw [hctotal, hcwidth]
    exact hcore
  have hcordinary : (S.node c).centered = false →
      (S.node c).totalLength ≤ 5 * (S.node c).width / 6 := by
    intro hf
    have hbad : true = false := hcentered.symm.trans hf
    cases hbad
  have hqwidth : (S.node q).width = (S.node x).width := by
    rw [hq, Node.comparison_width, hcwidth]
  have hqtotal : (S.node q).totalLength = (S.node x).totalLength := by
    rw [hq, Node.comparison_totalLength, hctotal]
  have hqslots : (S.node q).parameters.z = (S.node x).parameters.z := by
    rw [hq, Node.comparison_slots, hcslots]
  have hqabove : floor < (S.node q).width := by rw [hqwidth]; exact hwidth
  have hqcore : (S.node q).totalLength ≤ (S.node q).width + padding := by
    rw [hqtotal, hqwidth]
    exact hcore
  have hqordinary : (S.node q).centered = false := by
    rw [hq, Node.comparison_centered]
  have hqlarge : 5 * (S.node q).width / 6 < (S.node q).totalLength := by
    rw [hqwidth, hqtotal]
    exact hlarge
  have hqfirst : (S.node q).parameters.n₁ = (S.node x).width / 4 := by
    simp only [hq, hc, Node.comparisonOrdinary, Node.ordinary,
      Node.comparisonParameters, Node.quarterCentered]
  have hqshort : (S.node q).parameters.n₁ ≤ (S.node q).width / 4 ∨
      (S.node q).parameters.n₂ ≤ (S.node q).width / 4 := by
    left
    simpa only [hqfirst, hqwidth] using
      (le_rfl : (S.node x).width / 4 ≤ (S.node x).width / 4)
  have hcstate := S.same_core_schedule padding c x hcslots hcwidth hctotal
  have hqstate := S.same_core_schedule padding q x hqslots hqwidth hqtotal
  have hcenter := input.strict_bound c hcabove hccore hcordinary D hD (fun y hy =>
    hchildren y (by simpa only [hcstate] using hy))
  have hcomparison := input.short_bound q hqabove hqcore hqordinary hqlarge hqshort D hD
    (fun y hy => hchildren y (by simpa only [hqstate] using hy))
  have hdecomposition : (S.node x).normalizedEnergy U 0 ≤
      2 * (S.node c).normalizedEnergy U 0 + 2 * (S.node q).normalizedEnergy U 0 := by
    have hparentEnergy : (S.node x).normalizedEnergy U 0 =
        (Node.ordinary (S.node c).data (S.node c).parameters).normalizedEnergy U 0 := by
      rw [hc]
      exact normalizedEnergy_ordinary_of_false (S.node x) hordinary U 0
    rw [hparentEnergy, hq]
    exact (S.node c).normalizedEnergy_le_centered_add_comparison hcentered U 0
      (zero_lt_one.trans input.scale)
  calc
    (S.node x).normalizedEnergy U 0 ≤
        2 * (S.node c).normalizedEnergy U 0 + 2 * (S.node q).normalizedEnergy U 0 := hdecomposition
    _ ≤ 2 * (C * (1 + T) ^ H * U ^ β + C * (1 + T) ^ H * U ^ δ * D) +
        2 * (C * (1 + T) ^ H * U ^ β + C * (1 + T) ^ H * U ^ δ * D) :=
      add_le_add (mul_le_mul_of_nonneg_left hcenter (by norm_num))
        (mul_le_mul_of_nonneg_left hcomparison (by norm_num))
    _ = (4 * C) * (1 + T) ^ H * U ^ β +
        (4 * C) * (1 + T) ^ H * U ^ δ * D := by ring

/-- Construct the local scalar consequence by the original geometric
cases. Its only scalar child premise is the current induction
hypothesis on genuinely earlier labels. -/
theorem local_bound
    (input : MellinCoreRecursionInput (Ω := Ω) S U T C H β δ floor padding boundary
      originalControl admissible) (x : S.Label) (D : ℝ) (hD : 0 ≤ D)
    (hchildren : ∀ y, ((S.withCoreStages padding).schedule y).Earlier
      ((S.withCoreStages padding).schedule x) → (S.node y).normalizedEnergy U 0 ≤ D) :
    (S.node x).normalizedEnergy U 0 ≤
      (4 * C) * (1 + T) ^ H * U ^ β + (4 * C) * (1 + T) ^ H * U ^ δ * D := by
  have enlarge (h : (S.node x).normalizedEnergy U 0 ≤
      C * (1 + T) ^ H * U ^ β + C * (1 + T) ^ H * U ^ δ * D) :
      (S.node x).normalizedEnergy U 0 ≤
        (4 * C) * (1 + T) ^ H * U ^ β + (4 * C) * (1 + T) ^ H * U ^ δ * D := by
    have ht := input.bound_nonneg β
    have hm := mul_nonneg (input.bound_nonneg δ) hD
    nlinarith
  by_cases hnoncore : (S.node x).width + padding < (S.node x).totalLength
  · exact enlarge (input.outer_bound x hnoncore D hD hchildren)
  have hcore : (S.node x).totalLength ≤ (S.node x).width + padding := le_of_not_gt hnoncore
  by_cases hbase : (S.node x).width ≤ floor
  · exact enlarge (input.base_bound x hcore hbase D hD)
  have hwidth : floor < (S.node x).width := lt_of_not_ge hbase
  by_cases hcentered : (S.node x).centered = true
  · have hord : (S.node x).centered = false →
        (S.node x).totalLength ≤ 5 * (S.node x).width / 6 := by
      intro hf
      have hbad : true = false := hcentered.symm.trans hf
      cases hbad
    exact enlarge (input.strict_bound x hwidth hcore hord D hD hchildren)
  have hordinary : (S.node x).centered = false := by
    cases hb : (S.node x).centered <;> simp_all
  by_cases hsmall : (S.node x).totalLength ≤ 5 * (S.node x).width / 6
  · exact enlarge (input.strict_bound x hwidth hcore (fun _ => hsmall) D hD hchildren)
  have hlarge : 5 * (S.node x).width / 6 < (S.node x).totalLength := lt_of_not_ge hsmall
  by_cases hshort : (S.node x).parameters.n₁ ≤ (S.node x).width / 4 ∨
      (S.node x).parameters.n₂ ≤ (S.node x).width / 4
  · exact enlarge (input.short_bound x hwidth hcore hordinary hlarge hshort D hD hchildren)
  have h₁ : (S.node x).width / 4 < (S.node x).parameters.n₁ := by
    apply lt_of_not_ge
    intro h
    exact hshort (Or.inl h)
  have h₂ : (S.node x).width / 4 < (S.node x).parameters.n₂ := by
    apply lt_of_not_ge
    intro h
    exact hshort (Or.inr h)
  exact input.centered_bound x hwidth hcore hordinary hlarge h₁ h₂ D hD hchildren

/-- Strong induction now closes the actual node family. No joint
frequency-dependent engine kernel is needed, and the original loss
and height propagation formula is unchanged. -/
theorem energy_bound
    (input : MellinCoreRecursionInput (Ω := Ω) S U T C H β δ floor padding boundary
      originalControl admissible) (hH : 0 ≤ H) (hδ : 0 ≤ δ) :
    ∀ x : S.Label, (S.node x).normalizedEnergy U 0 ≤
      ((4 * C) * (1 + 4 * C) ^ (6 * (widthBand σ W + 1))) *
        U ^ (β + (6 * (widthBand σ W + 1) : ℕ) * δ) *
        (1 + T) ^ (H * ((6 * (widthBand σ W + 1) : ℕ) + 1)) := by
  exact scalarRecursion_power_bound (fun x : S.Label => (S.node x).normalizedEnergy U 0)
    (S.withCoreStages padding).schedule (4 * C) U T H β δ
    (by linarith [input.coefficient_nonneg]) input.scale.le input.height_nonneg hH hδ
    input.local_bound

end MellinCoreRecursionInput

end HeckeSkeleton.Moments.EngineInduction

