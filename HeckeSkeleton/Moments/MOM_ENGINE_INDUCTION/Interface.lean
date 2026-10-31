import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Family
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Reduction
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Terminal
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.TerminalCertificate

/-!
# The parent reduction required by the finite induction

This assembly contract concerns the actual `MomentData` polynomials.  A state contains both
rectangles, the common original row set, both profiles, the whole slot
product and the common mask.  The same data are used in a centered
difference, and its comparison lengths have the same sum.

The contract gives a positive local inequality and earlier children, together
with the normalized terminal remainder and weight mass. Children may form
a finite weighted sum or a finite positive measure, allowing the genuine
continuous Fourier parameters to remain inside the recursion. It contains no
`UniformMomentBound`, `SectorBound`, final root estimate or recursive
estimate as an assumed field.  Uniform constants are chosen before the
moving scale, source index and sector.

The published `EngineStep.paired_child_step` at commit
`04cc5c645c7f79bb19439b6f8fddbc7fd820882e` supplies a narrower conclusion:
strict child width, capacity repair and the actual slot-removal inequality.
`ChildStepCompatibility.lean` records that precise interface.  It leaves
the parent's norm decomposition, terminal component masses and
uniform common-kernel tail budget to be assembled.  The newer orbital
transform and kernel modules supply exact identities and quantitative
truncation with an explicit coefficient mass; that mass still needs its
uniform bound over the recursive profile family.  Those additional obligations are
explicit here and require more than the published child theorem alone.

The producer must prove this contract for its actual two-transform output.
In particular, it must supply the recursively masked prime-subproduct
removal inequality; an average for only the original prime product does
not suffice.  The finite induction consumes this assembly contract.
The endpoint uses exactly the same contract with `kappa = 1`.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open scoped BigOperators Classical

universe u v w

variable (K : Type) [Field K] [NumberField K]

/-- The entire paired coefficient is preserved in a node. -/
structure Node (ω ψ : HeckeCharacter K) where
  data : MomentData K ω ψ
  parameters : RealParameters
  centered : Bool
  comparison₁ : ℝ
  comparison₂ : ℝ
  comparison_sum : comparison₁ + comparison₂ = parameters.n₁ + parameters.n₂

namespace Node

variable {K} {ω ψ : HeckeCharacter K}

def width (n : Node K ω ψ) : ℝ := n.parameters.m + n.parameters.q

def ordinary (d : MomentData K ω ψ) (a : RealParameters) : Node K ω ψ :=
  ⟨d, a, false, a.n₁, a.n₂, rfl⟩

/-- Both rectangles use the identical two tests, character, norm phase,
and original common mask through the same `MomentData`. -/
def plainPair (n : Node K ω ψ) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (U t : ℝ) : ℂ :=
  plainPolynomial n.data n.data.plainTest₁ u (U ^ n.parameters.n₁) t *
    plainPolynomial n.data n.data.plainTest₂ u (U ^ n.parameters.n₂) t -
      if n.centered then
        plainPolynomial n.data n.data.plainTest₁ u (U ^ n.comparison₁) t *
          plainPolynomial n.data n.data.plainTest₂ u (U ^ n.comparison₂) t
      else 0

/-- A literal finite polynomial energy; there is no arbitrary energy field. -/
def energy (n : Node K ω ψ) (U t : ℝ) : ℝ :=
  ∑ u ∈ pairedRows n.data n.parameters U,
    ‖n.plainPair u U t * slotProduct n.data u U t‖ ^ 2

def normalizedEnergy (n : Node K ω ψ) (U t : ℝ) : ℝ :=
  n.energy U t / U ^ n.width

theorem energy_nonneg (n : Node K ω ψ) (U t : ℝ) : 0 ≤ n.energy U t :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

@[simp] theorem ordinary_energy (d : MomentData K ω ψ) (a : RealParameters)
    (U t : ℝ) : (ordinary d a).energy U t = pairedEnergy d a U t := by
  simp only [energy, ordinary, plainPair, Bool.false_eq_true, if_false, sub_zero,
    pairedEnergy]

/-- The two scale products agree before absolute values are taken. -/
theorem comparison_product (n : Node K ω ψ) {U : ℝ} (hU : 0 < U) :
    U ^ n.comparison₁ * U ^ n.comparison₂ =
      U ^ n.parameters.n₁ * U ^ n.parameters.n₂ := by
  rw [← Real.rpow_add hU, ← Real.rpow_add hU, n.comparison_sum]

end Node

/-- The actual polynomial family on which a single two-transform step
acts, at one fixed base and height.  Only width bounds enter its order. -/
structure PolynomialSystem (ω ψ : HeckeCharacter K) (σ W : ℝ) where
  Label : Type u
  node : Label → Node K ω ψ
  /-- The proof stage is independent of whether a coefficient is centered.
  In particular, an ordinary large-parameter root can occupy the later stage. -/
  proofStage : Label → Fin 2
  sigma_pos : 0 < σ
  width_nonneg : ∀ x, 0 ≤ (node x).width
  width_le : ∀ x, (node x).width ≤ W

namespace PolynomialSystem

variable {K} {ω ψ : HeckeCharacter K} {σ W : ℝ}

def schedule (S : PolynomialSystem.{u} K ω ψ σ W) (x : S.Label) :
    State (widthBand σ W) where
  slots := if (S.node x).parameters.z = 0 then 0 else 1
  band := boundedBand σ (S.node x).width W S.sigma_pos (S.width_le x)
  stage := S.proofStage x

/-- The decrease guaranteed after all actual boundary errors is sufficient
for the smaller-width recursive call. -/
theorem strict_child_earlier (S : PolynomialSystem.{u} K ω ψ σ W)
    (child parent : S.Label)
    (hmode : (S.schedule child).slots = (S.schedule parent).slots)
    (hdrop : (S.node child).width + σ / 2 ≤ (S.node parent).width) :
    (S.schedule child).Earlier (S.schedule parent) :=
  EngineInduction.strict_child_earlier S.sigma_pos (S.width_nonneg child)
    hdrop hmode rfl rfl

end PolynomialSystem

/-- A normalized local inequality at fixed scales.  Its weights already
include the one amplifier use, all divisor allocations, paired Cauchy and
the one slot-removal overshoot. -/
structure ClosedParentReduction {ω ψ : HeckeCharacter K} {σ W : ℝ}
    (S : PolynomialSystem.{u} K ω ψ σ W)
    (U T t C H β δ : ℝ) where
  reduction : Reduction (fun x => (S.node x).normalizedEnergy U t) S.schedule
  terminal : ∀ x, reduction.remainder x ≤ C * (1 + T) ^ H * U ^ β
  mass : ∀ x, reduction.mass x ≤ C * (1 + T) ^ H * U ^ δ

/-- The producer-facing contract keeps the raw terminal components.  The
exceptional exponent and the aggregate terminal bound are proved by this
task, rather than assumed as the final bound for a remainder. -/
structure RawParentReduction {ω ψ : HeckeCharacter K} {σ W : ℝ}
    (S : PolynomialSystem.{u} K ω ψ σ W)
    (U T t C H β δ : ℝ) where
  reduction : Reduction (fun x => (S.node x).normalizedEnergy U t) S.schedule
  floor : ℝ
  padding : ℝ
  boundary : ℝ
  floor_nonneg : 0 ≤ floor
  padding_nonneg : 0 ≤ padding
  boundary_nonneg : 0 ≤ boundary
  terminal_budget : terminalBudget floor padding σ boundary ≤ β
  components : ∀ x,
    TerminalComponents.{u} (reduction.remainder x) U T C H floor padding σ boundary
  mass : ∀ x, reduction.mass x ≤ C * (1 + T) ^ H * U ^ δ

/-- Close the raw terminal ledgers before running the recursion. -/
def RawParentReduction.closeTerminals {ω ψ : HeckeCharacter K} {σ W : ℝ}
    {S : PolynomialSystem.{u} K ω ψ σ W} {U T t C H β δ : ℝ}
    (raw : RawParentReduction K S U T t C H β δ) (hU : 1 ≤ U) :
    ClosedParentReduction K S U T t C H β δ where
  reduction := raw.reduction
  terminal := fun x => (raw.components x).bound hU raw.floor_nonneg
    raw.padding_nonneg S.sigma_pos.le raw.boundary_nonneg raw.terminal_budget
  mass := raw.mass

variable {K}

/-- The certificate at one original source index and one original sector.
The root is an equality of complete polynomial data, not just an equality
of numerical widths. -/
structure RootCertificate {ω ψ : HeckeCharacter K}
    {Index : ℝ → ℝ → Type v} {Sector : Type w}
    (F : SourceFamily K ω ψ Index Sector)
    (indexMap : ∀ Z T, Index Z T → Index Z T)
    (σ W C H β δ : ℝ) {Z T : ℝ} (i : Index Z T) (s : Sector) where
  system : PolynomialSystem.{u} K ω ψ σ W
  root : system.Label
  root_eq : system.node root =
    Node.ordinary (F.model Z T (indexMap Z T i) s) (F.parameters (indexMap Z T i))
  base_one_le : 1 ≤ F.base i
  step : RawParentReduction K system (F.base i) T 0 C H β δ

/-- The uniform parent-assembly hypothesis.  All numerical controls and
the height ceiling precede `tau`.  A common scalar and threshold precede
all source indices, sectors and recursively generated nodes. -/
structure ParentReductionInput {ω ψ : HeckeCharacter K}
    {Index : ℝ → ℝ → Type v} {Sector : Type w}
    (F : SourceFamily K ω ψ Index Sector)
    (indexMap : ∀ Z T, Index Z T → Index Z T)
    (eligible : ∀ Z T, Index Z T → Prop) where
  sigma : ℝ
  widthLimit : ℝ
  heightDegree : ℝ
  terminalLoss : ℝ
  edgeLoss : ℝ
  ceiling : ℝ
  sigma_pos : 0 < sigma
  heightDegree_nonneg : 0 ≤ heightDegree
  edgeLoss_nonneg : 0 ≤ edgeLoss
  ceiling_pos : 0 < ceiling
  loss_budget : terminalLoss + (4 * (widthBand sigma widthLimit + 1) : ℕ) *
    edgeLoss ≤ F.loss
  base_at : ∀ Z T (i : Index Z T), F.base (indexMap Z T i) = F.base i
  certificates : ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
    ∃ Z₀ C : ℝ, 1 ≤ Z₀ ∧ 0 ≤ C ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ∀ i : Index Z (Z ^ τ),
        51 / 100 < F.bin Z (Z ^ τ) i → eligible Z (Z ^ τ) i →
          ∀ s : Sector, Nonempty (RootCertificate.{u} F indexMap sigma widthLimit C
            heightDegree terminalLoss edgeLoss i s)

end HeckeSkeleton.Moments.EngineInduction
