import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedOutputConditions
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FiniteKernelFamily

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The literal normalized family, with one side index

The active labels, retained slots, normalized profiles, frozen heights and
positive kernels are those computed by `ActualNormalizedPairFamily`.
The two sides share this label and measure.  Finite enumeration changes
only the label, after the arithmetic construction has been completed.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField MeasureTheory HeckeGeneral.Characters DedekindZetaZeroFree
open HeckeGeneral.Analysis.ConditionalMoments EngineStep

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}

namespace NormalizedFamilyAdapter

variable {Λ V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Z : ℝ}
variable (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z) (labels : Finset Λ)

/-- A side projection never replaces the actual normalized frozen data. -/
def data (side : Bool) : family.active labels → V → MomentData K ω ψ :=
  match side with
  | false => family.leftData labels
  | true => family.rightData labels

def parameters (side : Bool) : family.active labels → RealParameters :=
  match side with
  | false => family.leftParameters labels
  | true => family.rightParameters labels

variable {d : MomentData K ω ψ} {a : RealParameters} {step : ℝ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}
variable (geometry : family.OutputGeometry labels d a step rowDomain window seminorms)
variable {admissible : MomentData K ω ψ → RealParameters → Prop}
variable (actual_admissible : ∀ side b ξ,
  admissible (data family labels side b ξ) (parameters family labels side b))

/-- Output fields are proved for these very children, including the exact
recipe invariant supplied by the caller.  There is no child selection here. -/
def children : ChildFamily (family.active labels) V d a step admissible where
  data := data family labels
  parameters := parameters family labels
  width side := by
    cases side
    · exact geometry.left_width
    · exact geometry.right_width
  width_nonneg side := by
    cases side
    · exact geometry.left_width_nonneg
    · exact geometry.right_width_nonneg
  plain_left_nonneg side := by
    cases side
    · exact geometry.left_plain_left_nonneg
    · exact geometry.right_plain_left_nonneg
  plain_right_nonneg side := by
    cases side
    · exact geometry.left_plain_right_nonneg
    · exact geometry.right_plain_right_nonneg
  length side := by
    cases side
    · exact geometry.left_length
    · exact geometry.right_length
  kappa side := by
    cases side
    · exact geometry.left_kappa
    · exact geometry.right_kappa
  slots side := by
    cases side
    · exact geometry.left_slots
    · exact geometry.right_slots
  theta side := by
    cases side
    · exact geometry.left_theta
    · exact geometry.right_theta
  slot_characters side := by
    cases side
    · exact geometry.left_slot_characters
    · exact geometry.right_slot_characters
  admissible_data := actual_admissible
  capacity side := by
    cases side
    · exact geometry.left_capacity
    · exact geometry.right_capacity

/-- This is a finite enumeration of the active physical labels. -/
def labelEquiv : Fin (Fintype.card (family.active labels)) ≃ family.active labels :=
  (Fintype.equivFin (family.active labels)).symm

def finChildren : ChildFamily (Fin (Fintype.card (family.active labels))) V d a step admissible :=
  (children family labels geometry actual_admissible).reindex (labelEquiv family labels)

end NormalizedFamilyAdapter

namespace NormalizedFamilyAdapter

variable {Λ U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (WithLp 2 (U × E))] [BorelSpace (WithLp 2 (U × E))]
variable {Z : ℝ}
variable (family : ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) Λ ω ψ Z)
variable (labels : Finset Λ)
variable {d : MomentData K ω ψ} {a : RealParameters} {step : ℝ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}
variable (geometry : family.OutputGeometry labels d a step rowDomain window seminorms)
variable {admissible : MomentData K ω ψ → RealParameters → Prop}
variable (actual_admissible : ∀ side b ξ,
  admissible (data family labels side b ξ) (parameters family labels side b))
variable (F₁ : Λ → SchwartzMap U ℂ) (F₂ : Λ → SchwartzMap E ℂ) (outer : Λ → ℝ)
variable (convergence : family.OutputIntegrability labels
  (family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) (a.m + a.q)))

/-- The envelope is applied to the original nested Fourier measure once,
including the original outer scalar.  Both child energies use this kernel. -/
def kernels : FiniteKernelFamily
    (children family labels geometry actual_admissible) Z where
  kernel := family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) (a.m + a.q)
  finite_kernel := convergence.finite_kernel
  integrable side := by
    cases side
    · exact convergence.left_integrable
    · exact convergence.right_integrable
  cauchy_integrable := convergence.cauchy_integrable

def finKernels : FiniteKernelFamily
    (finChildren family labels geometry actual_admissible) Z :=
  (kernels family labels geometry actual_admissible F₁ F₂ outer convergence).reindex
    (labelEquiv family labels)

@[simp] theorem finKernels_mass :
    (finKernels family labels geometry actual_admissible F₁ F₂ outer convergence).mass =
      (kernels family labels geometry actual_admissible F₁ F₂ outer convergence).mass :=
  FiniteKernelFamily.mass_reindex _ (labelEquiv family labels)

@[simp] theorem finKernels_pairIntegral :
    (finKernels family labels geometry actual_admissible F₁ F₂ outer convergence).pairIntegral =
      (kernels family labels geometry actual_admissible F₁ F₂ outer convergence).pairIntegral :=
  FiniteKernelFamily.pairIntegral_reindex _ (labelEquiv family labels)

end NormalizedFamilyAdapter
end HeckeSkeleton.Moments.EngineStepV2

#print axioms HeckeSkeleton.Moments.EngineStepV2.NormalizedFamilyAdapter.children
#print axioms HeckeSkeleton.Moments.EngineStepV2.NormalizedFamilyAdapter.kernels
