import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalActiveColumnLower

set_option linter.unusedSectionVars false

/-!
# Fixed positive lower annuli on the actual original coefficient support

The original lower endpoint need not be one. Its complete occurrence
power is kept first, then paid by one threshold chosen from the fixed
lower endpoint, original slot cap and positive loss. Comparison scales
are still used only through their actual product.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

namespace ParentConstantAtoms

section LiteralRectangle

variable {Q : Type*} {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable (atoms : ParentConstantAtoms Q d a Z t)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window orders d amplitude)

include profiles

/-- The original support lower endpoint is used separately for every
occurrence. No comparison scale is bounded coordinatewise. -/
theorem original_active_rectangle_column_norm_lower_annulus
    (lower : ℝ) (hlower : 0 ≤ lower) (hZ : 0 < Z) (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Ici lower)
    (comparison : Bool)
    (hleftScale : 0 < (if comparison then Y₁ else Z ^ a.n₁))
    (hrightScale : 0 < (if comparison then Y₂ else Z ^ a.n₂))
    (hscaleProduct : (if comparison then Y₁ else Z ^ a.n₁) *
      (if comparison then Y₂ else Z ^ a.n₂) = Z ^ (a.n₁ + a.n₂))
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).columns)
    (hrectangle : (atoms.values Y₁ Y₂).rectangle comparison v ≠ 0) :
    lower ^ (d.geometry.slotCount + 2) * Z ^ (a.n₁ + a.n₂ + d.geometry.totalLength) ≤
      (Ideal.absNorm ((atoms.raw Y₁ Y₂).columnIdeal v) : ℝ) := by
  sorry

end LiteralRectangle

section ActualExteriorCarrier

variable {A : SArithmeticData K} {Γ : Subgroup A.U}
variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ}
variable {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable (atoms : ParentConstantAtoms
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window orders d amplitude)

include profiles

/-- Both centered rectangles give exactly the same whole lower scale.
The implication is only on the support of the actual coefficient. -/
theorem original_active_column_norm_lower_annulus
    (lower : ℝ) (hlower : 0 ≤ lower) (hZ : 0 < Z) (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Ici lower)
    (centered : Bool) (hY₁ : centered = true → 0 ≤ Y₁)
    (hcomparison : centered = true → Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂))
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).exteriorColumns)
    (hcoefficient : (atoms.values Y₁ Y₂).coefficient centered v ≠ 0) :
    lower ^ (d.geometry.slotCount + 2) * Z ^ (a.n₁ + a.n₂ + d.geometry.totalLength) ≤
      (Ideal.absNorm ((atoms.raw Y₁ Y₂).columnExterior v).val : ℝ) := by
  sorry

theorem original_active_column_norm_lower_annulus_of_domain
    (lower : ℝ) (hlower : 0 ≤ lower)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Ici lower)
    {centered : Bool} {floor padding : ℝ}
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).exteriorColumns)
    (hcoefficient : (atoms.values Y₁ Y₂).coefficient centered v ≠ 0) :
    lower ^ (d.geometry.slotCount + 2) * Z ^ (a.n₁ + a.n₂ + d.geometry.totalLength) ≤
      (Ideal.absNorm ((atoms.raw Y₁ Y₂).columnExterior v).val : ℝ) := by
  sorry

/-- A fixed threshold pays the complete lower-annulus cost, before
any moving original source is chosen. -/
theorem original_active_column_norm_lower_power
    (cap : ℕ) (lower loss : ℝ) (hlower : 0 < lower) (hlowerOne : lower ≤ 1)
    (hcap : d.geometry.slotCount ≤ cap)
    (hthreshold : (lower ^ (cap + 2))⁻¹ ≤ Z ^ loss) (hZ : 0 < Z)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Ici lower)
    (centered : Bool) (hY₁ : centered = true → 0 ≤ Y₁)
    (hcomparison : centered = true → Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂))
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).exteriorColumns)
    (hcoefficient : (atoms.values Y₁ Y₂).coefficient centered v ≠ 0) :
    Z ^ (a.n₁ + a.n₂ + d.geometry.totalLength - loss) ≤
      (Ideal.absNorm ((atoms.raw Y₁ Y₂).columnExterior v).val : ℝ) := by
  sorry

end ActualExteriorCarrier
/-- The lower-window threshold is independent of all original
columns, coefficients, common ideals and comparison scales. -/
theorem original_lower_annulus_power_threshold
    (cap : ℕ) (lower loss : ℝ) (hloss : 0 < loss) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → (lower ^ (cap + 2))⁻¹ ≤ Z ^ loss := by
  sorry

end ParentConstantAtoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.original_active_rectangle_column_norm_lower_annulus
#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.original_active_column_norm_lower_annulus
#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.original_active_column_norm_lower_annulus_of_domain

#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.original_active_column_norm_lower_power
#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.original_lower_annulus_power_threshold
