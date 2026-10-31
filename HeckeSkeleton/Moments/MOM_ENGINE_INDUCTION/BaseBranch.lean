import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.BaseUniformity
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.BranchedIntegralRecursion

/-!
# Actual absolute base leaves for the local branched recursion

A width-floor leaf keeps the actual normalized polynomial energy as its
remainder and has no children.  The profile estimates of `BaseUniformity`
provide its raw terminal certificate, and `TerminalComponents.bound`
closes that certificate with the same budget as the active branches.

The common coefficient and height degree are selected before the moving
height, the polynomial system, and the particular node.  A base leaf is
not classified as a transform zero term or as a truncation tail.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open scoped BigOperators Classical

universe u v

variable {K : Type} [Field K] [NumberField K]
variable {Ω : Type v} [MeasurableSpace Ω]

namespace PolynomialSystem

variable {ω ψ : HeckeCharacter K} {σ W : ℝ}

/-- The base alternative in the same actual polynomial family as the
active engine alternatives. Its local remainder is the unchanged energy. -/
def baseBranch (S : PolynomialSystem.{u} K ω ψ σ W) (U t : ℝ) (x : S.Label) :
    BranchedIntegralAt (Ω := Ω)
      (fun y => (S.node y).normalizedEnergy U t) S.schedule x :=
  BranchedIntegralAt.terminal _ _ _

@[simp] theorem baseBranch_remainder (S : PolynomialSystem.{u} K ω ψ σ W)
    (U t : ℝ) (x : S.Label) :
    (S.baseBranch (Ω := Ω) U t x).remainder = (S.node x).normalizedEnergy U t := rfl

/-- A base leaf contributes exactly zero to the full kernel mass of the
branched recursion, irrespective of the parameter measure space. -/
@[simp] theorem baseBranch_mass (S : PolynomialSystem.{u} K ω ψ σ W)
    (U t : ℝ) (x : S.Label) :
    (∑ b, ((S.baseBranch (Ω := Ω) U t x).kernel b).real Set.univ) = 0 := by
  simp [baseBranch, BranchedIntegralAt.terminal]

/-- Close the genuine base certificate through the common terminal
ledger. The inputs are raw components, not a completed moment bound. -/
theorem baseBranch_bound (S : PolynomialSystem.{u} K ω ψ σ W)
    (U t : ℝ) (x : S.Label) (T C H ρ padding boundary β : ℝ)
    (components : TerminalComponents.{u} ((S.node x).normalizedEnergy U t)
      U T C H ρ padding σ boundary)
    (hU : 1 ≤ U) (hρ : 0 ≤ ρ) (hp : 0 ≤ padding) (hb : 0 ≤ boundary)
    (hbudget : terminalBudget ρ padding σ boundary ≤ β) :
    (S.baseBranch (Ω := Ω) U t x).remainder ≤ C * (1 + T) ^ H * U ^ β :=
  components.bound hU hρ hp S.sigma_pos.le hb hbudget

end PolynomialSystem

/-- Uniform profile control gives actual local base leaves with a single
coefficient and height degree. Each leaf retains its raw certificate for
assembly with active branches, its proved budget, and its zero kernel mass.
The scale exponent of the absolute slot estimate remains `totalLength`. -/
theorem uniform_polynomial_height_base_branch (cap : ℕ)
    (B₁ B₂ Bslots H₁ H₂ Hslots ρ padding σ boundary β : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hBslots : 0 ≤ Bslots)
    (hH₁ : 0 ≤ H₁) (hH₂ : 0 ≤ H₂) (hHslots : 0 ≤ Hslots)
    (hρ : 0 ≤ ρ) (hp : 0 ≤ padding) (hb : 0 ≤ boundary)
    (hbudget : terminalBudget ρ padding σ boundary ≤ β) :
    ∃ C H : ℝ,
      C = uniformBaseConstant K cap B₁ B₂ Bslots ∧
      H = baseHeightDegree cap H₁ H₂ Hslots ∧ 0 ≤ C ∧ 0 ≤ H ∧
      ∀ T : ℝ, 0 ≤ T → ∀ {ω ψ : HeckeCharacter K} (W : ℝ)
        (S : PolynomialSystem.{u} K ω ψ σ W) (U t : ℝ) (x : S.Label),
        1 ≤ U → (S.node x).data.geometry.slotCount ≤ cap →
        (∀ r ∈ pairedRows (S.node x).data (S.node x).parameters U,
          Function.support ((S.node x).data.plainTest₁.profile r t) ⊆ Set.Iic (2 : ℝ)) →
        (∀ r ∈ pairedRows (S.node x).data (S.node x).parameters U,
          Function.support ((S.node x).data.plainTest₂.profile r t) ⊆ Set.Iic (2 : ℝ)) →
        (∀ r ∈ pairedRows (S.node x).data (S.node x).parameters U, ∀ y,
          ‖(S.node x).data.plainTest₁.profile r t y‖ ≤ B₁ * (1 + T) ^ H₁) →
        (∀ r ∈ pairedRows (S.node x).data (S.node x).parameters U, ∀ y,
          ‖(S.node x).data.plainTest₂.profile r t y‖ ≤ B₂ * (1 + T) ^ H₂) →
        (∀ i, Function.support (((S.node x).data.geometry.slots i).profile t) ⊆
          Set.Ioo (1 : ℝ) 2) →
        (∀ i y, ‖((S.node x).data.geometry.slots i).profile t y‖ ≤
          Bslots * (1 + T) ^ Hslots) →
        (S.node x).parameters.n₁ + (S.node x).parameters.n₂ +
          (S.node x).data.geometry.totalLength ≤ ρ + padding + ρ / 6 →
        let leaf := S.baseBranch (Ω := Ω) U t x
        Nonempty (TerminalComponents.{u} leaf.remainder U T C H ρ padding σ boundary) ∧
          leaf.remainder ≤ C * (1 + T) ^ H * U ^ β ∧
          (∑ b, (leaf.kernel b).real Set.univ) = 0 := by
  obtain ⟨C, H, hCeq, hHeq, hC, hH, hcomponents⟩ :=
    uniform_polynomial_height_base_components.{u} (K := K) cap
      B₁ B₂ Bslots H₁ H₂ Hslots ρ padding σ boundary
      hB₁ hB₂ hBslots hH₁ hH₂ hHslots
  refine ⟨C, H, hCeq, hHeq, hC, hH, ?_⟩
  intro T hT ω ψ W S U t x hU hcount hann₁ hann₂ hprof₁ hprof₂ hannSlots hprofSlots hbase
  obtain ⟨components⟩ := hcomponents T hT (S.node x) U t hU hcount
    hann₁ hann₂ hprof₁ hprof₂ hannSlots hprofSlots hbase
  refine ⟨⟨components⟩, ?_, S.baseBranch_mass (Ω := Ω) U t x⟩
  exact S.baseBranch_bound (Ω := Ω) U t x T C H ρ padding boundary β
    components hU hρ hp hb hbudget

end HeckeSkeleton.Moments.EngineInduction
