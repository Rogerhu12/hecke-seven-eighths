import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CoreGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CoreStages
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.BaseBranch
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.BranchAssembly
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ReflectionBranch
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.StepOutputAdapter

/-!
# Construct the actual local recursion by geometric cases

The engine is called only in its canonical domain. Ordinary zero-slot
nodes outside the padded core first use their genuine ordinary reflection.
Core nodes below the width floor use actual absolute-counting components.
The remaining ordinary nodes use the strict step, short-factor reflection,
or quarter centering followed by substitution of two local reductions.
Neither the centered rectangle nor its raw comparison is recursively
called at the parent's state.

The single `originalControl` is a bound from the original profile input,
common to all genuine engine and reflection outputs. Producing those
outputs with this uniform control, including all descendant profiles and
moving masks, is an explicit analytic obligation. It is not a consequence
of evaluating the original source's profile predicate on its original box.
The assumptions contain no final moment estimate or all-node reduction.
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

/-- Structural invariants of the actual family. Ordinary zero-slot nodes
are allowed outside the padded core. Centered nodes are the real quarter
rectangles constructed within the core. -/
structure CoreNodeGeometry (S : PolynomialSystem.{u} K ω ψ σ W)
    (padding : ℝ) : Prop where
  length : ∀ x, (S.node x).parameters.z = (S.node x).data.geometry.totalLength
  plain_left_nonneg : ∀ x, 0 ≤ (S.node x).parameters.n₁
  plain_right_nonneg : ∀ x, 0 ≤ (S.node x).parameters.n₂
  kappa_lower : ∀ x, 3 / 4 ≤ (S.node x).parameters.κ
  kappa_upper : ∀ x, (S.node x).parameters.κ ≤ 1
  capacity : ∀ x, (S.node x).parameters.z = 0 ∨
    (S.node x).parameters.n₁ + (S.node x).parameters.n₂ +
      6 * (S.node x).parameters.κ * (S.node x).parameters.z ≤ (S.node x).width
  centered_core : ∀ x, (S.node x).centered = true →
    (S.node x).totalLength ≤ (S.node x).width + padding
  centered_left : ∀ x, (S.node x).centered = true →
    (S.node x).width / 4 ≤ (S.node x).parameters.n₁
  centered_right : ∀ x, (S.node x).centered = true →
    (S.node x).width / 4 ≤ (S.node x).parameters.n₂
  comparison_left : ∀ x, (S.node x).centered = true →
    (S.node x).comparison₁ = (S.node x).width / 4
  comparison_right : ∀ x, (S.node x).centered = true →
    (S.node x).comparison₂ =
      (S.node x).parameters.n₁ + (S.node x).parameters.n₂ - (S.node x).width / 4

namespace CoreNodeGeometry

variable {S : PolynomialSystem.{u} K ω ψ σ W} {padding : ℝ}

theorem noncore_zero (g : CoreNodeGeometry S padding) (hpadding : 0 ≤ padding)
    (x : S.Label) (hnoncore : (S.node x).width + padding < (S.node x).totalLength) :
    (S.node x).parameters.z = 0 := by
  rcases g.capacity x with hzero | hcap
  · exact hzero
  · have hcore := (S.node x).totalLength_le_width_of_capacity
      (g.length x) (g.kappa_lower x) hcap
    linarith

theorem noncore_ordinary (g : CoreNodeGeometry S padding)
    (x : S.Label) (hnoncore : (S.node x).width + padding < (S.node x).totalLength) :
    (S.node x).centered = false := by
  cases hcentered : (S.node x).centered with
  | false => rfl
  | true =>
    have hcore := g.centered_core x hcentered
    exact False.elim ((not_le_of_gt hnoncore) hcore)

/-- Assemble the provider's actual domain from geometric facts. The
ordinary small-length condition is supplied only in the branch using it. -/
def engineDomain (g : CoreNodeGeometry S padding) (x : S.Label)
    {U floor : ℝ} (hU : 1 < U) (hwidth : floor < (S.node x).width)
    (hcore : (S.node x).totalLength ≤ (S.node x).width + padding)
    (hordinary : (S.node x).centered = false →
      (S.node x).totalLength ≤ 5 * (S.node x).width / 6) :
    EngineStep.PairedEngineDomain (S.node x).centered (S.node x).data
      (S.node x).parameters U (U ^ (S.node x).comparison₁)
        (U ^ (S.node x).comparison₂) floor padding where
  scale := hU
  width_floor := hwidth
  width_nonneg := S.width_nonneg x
  plain_left_nonneg := g.plain_left_nonneg x
  plain_right_nonneg := g.plain_right_nonneg x
  total_length := g.length x
  kappa_lower := g.kappa_lower x
  kappa_upper := g.kappa_upper x
  capacity := g.capacity x
  padded_core := hcore
  ordinary := hordinary
  centered_left := g.centered_left x
  centered_right := g.centered_right x
  comparison_left h := congrArg (fun e : ℝ => U ^ e) (g.comparison_left x h)
  comparison_right h := congrArg (fun e : ℝ => U ^ e) (g.comparison_right x h)

end CoreNodeGeometry

/-- The exact public engine output and labels for its genuine children.
Freezing the profiles preserves each actual child energy at time zero. -/
structure EngineBranchAt (S : PolynomialSystem.{u} K ω ψ σ W) (x : S.Label)
    (U δ β C originalControl : ℝ)
    (admissible : MomentData K ω ψ → RealParameters → Prop) where
  output : (S.node x).EngineOutput (Ω := Ω) U σ δ β C originalControl admissible
  left : Fin output.branches → Ω → S.Label
  right : Fin output.branches → Ω → S.Label
  left_eq : ∀ b ξ, S.node (left b ξ) =
    Node.ordinary (freezeMomentTime (output.leftData b ξ) (output.leftTwist b ξ))
      (output.leftParameters b)
  right_eq : ∀ b ξ, S.node (right b ξ) =
    Node.ordinary (freezeMomentTime (output.rightData b ξ) (output.rightTwist b ξ))
      (output.rightParameters b)

/-- Only the legal centering case asks that these two intermediate
rectangles have labels. They are substituted locally, not recursive calls. -/
structure QuarterLabels (S : PolynomialSystem.{u} K ω ψ σ W) (x : S.Label) where
  center : S.Label
  comparison : S.Label
  center_eq : S.node center = (S.node x).quarterCentered
  comparison_eq : S.node comparison = (S.node center).comparisonOrdinary

/-- A proved short-factor reflection output with its own terminal and
complete kernel-mass estimates, before any child moment is estimated. -/
structure ShortReflectionBranchAt (S : PolynomialSystem.{u} K ω ψ σ W)
    (x : S.Label) (U boundary δ β C originalControl : ℝ) where
  output : ReflectedComparisonData (Ω := Ω) S x x U 0 boundary
  terminal : output.remainder ≤ C * originalControl * U ^ β
  mass : output.kernel.real Set.univ ≤ C * originalControl * U ^ δ

/-- Ordinary reflection of a genuine noncore zero-slot node. Its exact
same-width core children are part of the analytic output. -/
structure OuterReflectionBranchAt (S : PolynomialSystem.{u} K ω ψ σ W)
    (x : S.Label) (U padding δ β C originalControl : ℝ) where
  output : CoreReflectionData (Ω := Ω) S x U 0 padding
  terminal : output.remainder ≤ C * originalControl * U ^ β
  mass : output.kernel.real Set.univ ≤ C * originalControl * U ^ δ

/-- The distinct analytic inputs on their actual domains. The common
profile scalar is fixed before the node, branch and continuous child
parameter. There is no assumed final energy bound or all-node local step. -/
structure CoreRecursionInput (S : PolynomialSystem.{u} K ω ψ σ W)
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
        EngineBranchAt (Ω := Ω) S x U δ β C originalControl admissible
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

/-- An output of case assembly. This structure is constructed below and
is never an input premise for the induction theorem. -/
structure CoreLocalResult (S : PolynomialSystem.{u} K ω ψ σ W)
    (padding U T C H β δ : ℝ) (x : S.Label) where
  step : BranchedIntegralAt (Ω := Ω) (fun y => (S.node y).normalizedEnergy U 0)
    (S.withCoreStages padding).schedule x
  terminal : step.remainder ≤ C * (1 + T) ^ H * U ^ β
  mass : (∑ b, (step.kernel b).real Set.univ) ≤ C * (1 + T) ^ H * U ^ δ

namespace CoreLocalResult

variable {S : PolynomialSystem.{u} K ω ψ σ W} {padding U T C H β δ : ℝ}
variable {x : S.Label}

/-- Ordinary branches share the same coefficient as the centering branch,
whose two terms each carry the actual factor two. -/
def enlarge (r : CoreLocalResult (Ω := Ω) S padding U T C H β δ x)
    (hβ : 0 ≤ C * (1 + T) ^ H * U ^ β)
    (hδ : 0 ≤ C * (1 + T) ^ H * U ^ δ) :
    CoreLocalResult (Ω := Ω) S padding U T (4 * C) H β δ x where
  step := r.step
  terminal := r.terminal.trans (by nlinarith)
  mass := r.mass.trans (by nlinarith)

end CoreLocalResult

namespace CoreRecursionInput

variable {S : PolynomialSystem.{u} K ω ψ σ W}
variable {U T C H β δ floor padding boundary originalControl : ℝ}
variable {admissible : MomentData K ω ψ → RealParameters → Prop}

private theorem bound_nonneg
    (input : CoreRecursionInput (Ω := Ω) S U T C H β δ floor padding boundary
      originalControl admissible) (e : ℝ) :
    0 ≤ C * (1 + T) ^ H * U ^ e := by
  have hU : 0 ≤ U := (zero_lt_one.trans input.scale).le
  have hT : 0 ≤ 1 + T := by linarith [input.height_nonneg]
  exact mul_nonneg (mul_nonneg input.coefficient_nonneg (Real.rpow_nonneg hT H))
    (Real.rpow_nonneg hU e)

private theorem profile_scale_bound
    (input : CoreRecursionInput (Ω := Ω) S U T C H β δ floor padding boundary
      originalControl admissible) (e : ℝ) :
    C * originalControl * U ^ e ≤ C * (1 + T) ^ H * U ^ e :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left input.original_profile_bound input.coefficient_nonneg)
    (Real.rpow_nonneg (zero_lt_one.trans input.scale).le e)

/-- The width-floor leaf is closed from its actual absolute-counting
components. Its remainder remains the true node energy. -/
def baseBranch
    (input : CoreRecursionInput (Ω := Ω) S U T C H β δ floor padding boundary
      originalControl admissible) (x : S.Label)
    (hcore : (S.node x).totalLength ≤ (S.node x).width + padding)
    (hwidth : (S.node x).width ≤ floor) :
    CoreLocalResult (Ω := Ω) S padding U T C H β δ x := by
  have hlength : (S.node x).parameters.n₁ + (S.node x).parameters.n₂ +
      (S.node x).data.geometry.totalLength ≤ floor + padding + floor / 6 := by
    rw [← input.geometry.length x]
    change (S.node x).totalLength ≤ floor + padding + floor / 6
    linarith [input.floor_nonneg]
  let components := input.baseComponents x hwidth hlength
  refine ⟨(S.withCoreStages padding).baseBranch (Ω := Ω) U 0 x, ?_, ?_⟩
  · exact components.bound input.scale.le input.floor_nonneg input.padding_nonneg
      S.sigma_pos.le input.boundary_nonneg input.terminal_budget
  · exact ((S.withCoreStages padding).baseBranch_mass (Ω := Ω) U 0 x).le.trans
      (input.bound_nonneg δ)

/-- Call the canonical two-transform theorem on its proved domain. -/
def engineBranch
    (input : CoreRecursionInput (Ω := Ω) S U T C H β δ floor padding boundary
      originalControl admissible) (x : S.Label)
    (hwidth : floor < (S.node x).width)
    (hcore : (S.node x).totalLength ≤ (S.node x).width + padding)
    (hordinary : (S.node x).centered = false →
      (S.node x).totalLength ≤ 5 * (S.node x).width / 6) :
    CoreLocalResult (Ω := Ω) S padding U T C H β δ x := by
  let branch := input.engine x (input.node_admissible x)
    (input.geometry.engineDomain x input.scale hwidth hcore hordinary)
  let localStep := engineOutputToBranchedAt (S.withCoreStages padding) x branch.output
    (zero_lt_one.trans input.scale) branch.left branch.right
    branch.left_eq branch.right_eq (input.geometry.length x)
  refine ⟨localStep, ?_, ?_⟩
  · change branch.output.firstZero + branch.output.secondZero + branch.output.exceptional +
      branch.output.tail ≤ C * (1 + T) ^ H * U ^ β
    exact branch.output.terminals.trans (input.profile_scale_bound β)
  · change (∑ b, (branch.output.kernel b).real Set.univ) ≤
      C * (1 + T) ^ H * U ^ δ
    exact branch.output.mass.trans (input.profile_scale_bound δ)

/-- Equality at the quarter threshold belongs to reflection. This
includes the raw comparison's first length, exactly `M/4`. -/
def shortBranch
    (input : CoreRecursionInput (Ω := Ω) S U T C H β δ floor padding boundary
      originalControl admissible) (x : S.Label)
    (hwidth : floor < (S.node x).width)
    (hcore : (S.node x).totalLength ≤ (S.node x).width + padding)
    (hordinary : (S.node x).centered = false)
    (hlarge : 5 * (S.node x).width / 6 < (S.node x).totalLength)
    (hshort : (S.node x).parameters.n₁ ≤ (S.node x).width / 4 ∨
      (S.node x).parameters.n₂ ≤ (S.node x).width / 4) :
    CoreLocalResult (Ω := Ω) S padding U T C H β δ x := by
  let branch := input.shortReflection x hwidth hcore hordinary hlarge hshort
  have hz := (S.node x).slot_nonneg (input.geometry.length x)
  have hboundary : boundary ≤ (S.node x).width / 15 := by
    linarith [input.boundary_le_floor]
  let localStep := branch.output.toCoreAt padding input.padding_nonneg hz
    (input.geometry.kappa_lower x) (input.geometry.capacity x) hlarge hboundary rfl
  refine ⟨localStep, ?_, ?_⟩
  · exact branch.terminal.trans (input.profile_scale_bound β)
  · rw [ReflectedComparisonData.toCoreAt_mass]
    exact branch.mass.trans (input.profile_scale_bound δ)

/-- Noncore nodes are genuinely zero-slot ordinary nodes, and their
actual reflection enters an earlier same-width core stage. -/
def outerBranch
    (input : CoreRecursionInput (Ω := Ω) S U T C H β δ floor padding boundary
      originalControl admissible) (x : S.Label)
    (hnoncore : (S.node x).width + padding < (S.node x).totalLength) :
    CoreLocalResult (Ω := Ω) S padding U T C H β δ x := by
  let branch := input.outerReflection x hnoncore
    (input.geometry.noncore_zero input.padding_nonneg x hnoncore)
    (input.geometry.noncore_ordinary x hnoncore)
  refine ⟨branch.output.toAt hnoncore, ?_, ?_⟩
  · exact branch.terminal.trans (input.profile_scale_bound β)
  · rw [CoreReflectionData.toAt_mass]
    exact branch.mass.trans (input.profile_scale_bound δ)

private theorem normalizedEnergy_ordinary_of_false (n : Node K ω ψ)
    (hordinary : n.centered = false) (U t : ℝ) :
    n.normalizedEnergy U t = (Node.ordinary n.data n.parameters).normalizedEnergy U t := by
  have he : n.energy U t = pairedEnergy n.data n.parameters U t := by
    simp only [Node.energy, Node.plainPair, hordinary, Bool.false_eq_true, if_false,
      sub_zero, pairedEnergy]
  change n.energy U t / U ^ n.width =
    (Node.ordinary n.data n.parameters).energy U t / U ^ n.width
  rw [he, Node.ordinary_energy]

/-- Substitute the strict centered step and the real reflected
comparison locally. The equal-state intermediate nodes are not children. -/
def centeredBranch
    (input : CoreRecursionInput (Ω := Ω) S U T C H β δ floor padding boundary
      originalControl admissible) (x : S.Label)
    (hwidth : floor < (S.node x).width)
    (hcore : (S.node x).totalLength ≤ (S.node x).width + padding)
    (hordinary : (S.node x).centered = false)
    (hlarge : 5 * (S.node x).width / 6 < (S.node x).totalLength)
    (h₁ : (S.node x).width / 4 < (S.node x).parameters.n₁)
    (h₂ : (S.node x).width / 4 < (S.node x).parameters.n₂) :
    CoreLocalResult (Ω := Ω) S padding U T (4 * C) H β δ x := by
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
  let centerResult := input.engineBranch c hcabove hccore hcordinary
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
  let comparisonResult := input.shortBranch q hqabove hqcore hqordinary hqlarge hqshort
  have hcstate := S.same_core_schedule padding c x hcslots hcwidth hctotal
  have hqstate := S.same_core_schedule padding q x hqslots hqwidth hqtotal
  have hdecomposition : (S.node x).normalizedEnergy U 0 ≤
      2 * (S.node c).normalizedEnergy U 0 + 2 * (S.node q).normalizedEnergy U 0 := by
    have hparentEnergy : (S.node x).normalizedEnergy U 0 =
        (Node.ordinary (S.node c).data (S.node c).parameters).normalizedEnergy U 0 := by
      rw [hc]
      exact normalizedEnergy_ordinary_of_false (S.node x) hordinary U 0
    rw [hparentEnergy, hq]
    exact (S.node c).normalizedEnergy_le_centered_add_comparison hcentered U 0
      (zero_lt_one.trans input.scale)
  let localStep := centerResult.step.combine comparisonResult.step hcstate hqstate hdecomposition
  refine ⟨localStep, ?_, ?_⟩
  · change 2 * centerResult.step.remainder + 2 * comparisonResult.step.remainder ≤
      (4 * C) * (1 + T) ^ H * U ^ β
    nlinarith [centerResult.terminal, comparisonResult.terminal]
  · have hmass := BranchedIntegralAt.combine_mass centerResult.step comparisonResult.step
      hcstate hqstate hdecomposition
    exact hmass.le.trans (by nlinarith [centerResult.mass, comparisonResult.mass])

/-- The complete per-node case split. The noncore reflection is handled
before the width-floor base case, so no zero-slot core condition is added
to the engine's genuine children. -/
def branch
    (input : CoreRecursionInput (Ω := Ω) S U T C H β δ floor padding boundary
      originalControl admissible) (x : S.Label) :
    CoreLocalResult (Ω := Ω) S padding U T (4 * C) H β δ x := by
  by_cases hnoncore : (S.node x).width + padding < (S.node x).totalLength
  · exact (input.outerBranch x hnoncore).enlarge (input.bound_nonneg β) (input.bound_nonneg δ)
  have hcore : (S.node x).totalLength ≤ (S.node x).width + padding := le_of_not_gt hnoncore
  by_cases hbase : (S.node x).width ≤ floor
  · exact (input.baseBranch x hcore hbase).enlarge (input.bound_nonneg β) (input.bound_nonneg δ)
  have hwidth : floor < (S.node x).width := lt_of_not_ge hbase
  by_cases hcentered : (S.node x).centered = true
  · have hord : (S.node x).centered = false →
        (S.node x).totalLength ≤ 5 * (S.node x).width / 6 := by
      intro hf
      have hbad : true = false := hcentered.symm.trans hf
      cases hbad
    exact (input.engineBranch x hwidth hcore hord).enlarge
      (input.bound_nonneg β) (input.bound_nonneg δ)
  have hordinary : (S.node x).centered = false := by
    cases hb : (S.node x).centered <;> simp_all
  by_cases hsmall : (S.node x).totalLength ≤ 5 * (S.node x).width / 6
  · exact (input.engineBranch x hwidth hcore (fun _ => hsmall)).enlarge
      (input.bound_nonneg β) (input.bound_nonneg δ)
  have hlarge : 5 * (S.node x).width / 6 < (S.node x).totalLength := lt_of_not_ge hsmall
  by_cases hshort : (S.node x).parameters.n₁ ≤ (S.node x).width / 4 ∨
      (S.node x).parameters.n₂ ≤ (S.node x).width / 4
  · exact (input.shortBranch x hwidth hcore hordinary hlarge hshort).enlarge
      (input.bound_nonneg β) (input.bound_nonneg δ)
  have h₁ : (S.node x).width / 4 < (S.node x).parameters.n₁ := by
    apply lt_of_not_ge
    intro h
    exact hshort (Or.inl h)
  have h₂ : (S.node x).width / 4 < (S.node x).parameters.n₂ := by
    apply lt_of_not_ge
    intro h
    exact hshort (Or.inr h)
  exact input.centeredBranch x hwidth hcore hordinary hlarge h₁ h₂

/-- A closed parent reduction is now a conclusion of the geometric case
assembly, with only the two centering factors enlarging its coefficient. -/
def toClosedParentReduction
    (input : CoreRecursionInput (Ω := Ω) S U T C H β δ floor padding boundary
      originalControl admissible) :
    ClosedParentReduction K (S.withCoreStages padding) U T 0 (4 * C) H β δ where
  reduction := .branched Ω inferInstance
    (BranchedIntegralStep.ofLocal fun x => (input.branch x).step)
  terminal x := (input.branch x).terminal
  mass x := (input.branch x).mass

end CoreRecursionInput

end HeckeSkeleton.Moments.EngineInduction
