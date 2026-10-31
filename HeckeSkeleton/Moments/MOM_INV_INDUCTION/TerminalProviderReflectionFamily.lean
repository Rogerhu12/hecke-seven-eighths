import HeckeSkeleton.Moments.MOM_INV_INDUCTION.GeneralReflectedEnergy
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderBackgrounds
import HeckeSkeleton.Theta

/-!
# Actual reflection sources for the fixed finite period inventory

Every period has its own projected source, local high K-type vectors,
and finite Mellin table. These are constructed from the same arithmetic
recipe by the existing generic theta source constructors. In particular
the table for the target period is not silently reused for its finite
twists.

The only conditions on a period are the original exterior unramified
condition and nonzero angular weight. The global coefficient reflection,
its two convergence assertions, and its kernel are proved from that
period's actual source. No moment estimate is supplied or asserted here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalReflectionFamily

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

local notation "Sf" => places K c
local notation "D" => arithmeticData K c
local notation "R" => thetaRecipe K c

def source (θ : HeckeCharacter K) : FiniteFixedSource.Source R θ :=
  FiniteFixedSource.source R (thetaRecipe_aligned K c) θ

def localInput (θ : HeckeCharacter K) : FiniteLocalHighK.Input R θ (source K c θ) :=
  LocalArchInput.input R θ (source K c θ)

def mellinData (θ : HeckeCharacter K) : FiniteMellinData K Sf :=
  FiniteLocalHighK.finiteMellinData R θ (source K c θ) (localInput K c θ)

theorem mellin_admissible (θ : HeckeCharacter K) :
    FiniteMellinAdmissible K Sf (mellinData K c θ) :=
  ProjectedFiniteMellin.targetFiniteMellinData_admissible
    R (source K c θ).projected.base.factorization (source K c θ).transport
    (FiniteLocalHighK.C₀ R θ (source K c θ) (localInput K c θ))
    (FiniteLocalHighK.C₀_ne_zero R θ (source K c θ) (localInput K c θ))
    (FiniteLocalHighK.A₀ R θ (source K c θ) (localInput K c θ))
    (FiniteLocalHighK.A₀_pos R θ (source K c θ) (localInput K c θ)) θ

theorem kernel (θ : HeckeCharacter K) : MellinKernelInput K Sf (mellinData K c θ) θ where
  finite_admissible := mellin_admissible K c θ
  integrable := HeckeSkeleton.ThetaKernel.kernel_integrable K Sf (mellinData K c θ) θ
    (mellin_admissible K c θ)
  line_independent := HeckeSkeleton.ThetaKernel.kernel_line_independent K Sf
    (mellinData K c θ) θ (mellin_admissible K c θ)
  derivative_bound := HeckeSkeleton.ThetaKernel.kernel_derivative_bound K Sf
    (mellinData K c θ) θ (mellin_admissible K c θ)

theorem exterior_digits (θ : HeckeCharacter K) :
    GlobalProjectLocalDigitTables.Input R (source K c θ).projected.base.factorization D := by
  have h := LocalDigitInput.input R (source K c θ).projected.base
    (axiomChoice K c).different
  rw [thetaRecipe_arithmeticData K c] at h
  exact h

/-- The reflection certificate belongs to this period's constructed
Mellin data. The original source's single-period theorem is generalized
through its actual generic constructor, not through a twist assertion. -/
theorem reflection (θ : HeckeCharacter K)
    (hu : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sf → UnramifiedAt K θ p)
    (ha : ∃ (v : InfinitePlace K) (hv : v.IsComplex),
      heckeComplexWeight K v hv θ ≠ 0) :
    MarkedCoefficientReflectionInput K Sf D (mellinData K c θ) θ where
  allowed_generators := allowedGenerators K c
  exterior_unramified := hu
  angular_nonzero := ha
  kernel := kernel K c θ
  completed_absolute := by
    intro d V X hX
    exact HeckeSkeleton.MarkedAnnularSupport.completedTerm_summable_of_annular
      K Sf D θ (rowElement K Sf D d) d.puncture d.marks V X hX
  reflected_absolute := by
    intro d V X hX
    exact ThetaGlobal.ReflectedAbsoluteProject.marked_reflected_absolute
      K Sf D d (mellinData K c θ) θ (kernel K c θ) V hX
  reflection := by
    intro d V X hX
    have hS : conductorPlaces K θ ⊆ R.A.Sf := by
      intro p hp
      by_contra hnot
      exact ((mem_conductorPlaces K θ p).mp hp) (hu p hnot)
    obtain ⟨w, hw, hk⟩ := ha
    exact thetaRecipe_marked_reflection K c θ (source K c θ) (localInput K c θ)
      (exterior_digits K c θ) (allowedGenerators K c) hS w hk d V hX

/-- The family is selected once for the fixed finite inventory. Its
two genuine source conditions are arithmetic properties of its periods. -/
def actualFamily (backgrounds : Finset (HeckeCharacter K))
    (hu : ∀ θ ∈ backgrounds, ∀ p : HeightOneSpectrum (𝓞 K),
      p ∉ Sf → UnramifiedAt K θ p)
    (ha : ∀ θ ∈ backgrounds, ∃ (v : InfinitePlace K) (hv : v.IsComplex),
      heckeComplexWeight K v hv θ ≠ 0) :
    GeneralReflectedEnergy.ReflectionFamily K Sf D backgrounds where
  data := mellinData K c
  reflection := fun θ hθ => reflection K c θ (hu θ hθ) (ha θ hθ)

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalReflectionFamily

end
