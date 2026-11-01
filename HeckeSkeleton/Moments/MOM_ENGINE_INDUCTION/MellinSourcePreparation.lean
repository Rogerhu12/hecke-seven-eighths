import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CompleteSourceBudgets
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CompleteSourceReflection
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.StrictProfileOrder

/-!
# All primitive inputs of the actual per-frequency source

The model here is the literal normalized Mellin intermediate. Its two
plain profiles are row independent by construction. Localizing to its
exact paired rows preserves the complete parent energy and gives the
full allowed-row budget required by the original engine constructor.

The finite Schwartz profile window is derived from the true Mellin
normalization theorem at every frequency. Its amplitude, derivative
orders and positive annulus were selected before that frequency.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical SchwartzMap

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis MeasureTheory
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.UniformAmplify EngineStep

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The strict domain only uses unchanged parameters and slot lengths.
Both comparison exponents are retained by the actual Mellin model. -/
def Node.mellinStrictModel_domain
    (n : Node K ω ψ) (cap J : ℕ) (A lower upper : ℝ)
    (hA : 0 ≤ A) (hlower : 0 < lower) (hinterval : lower ≤ upper)
    (P : ℝ) (hP : 1 ≤ P) (frequency : ℝ × ℝ)
    {U floor padding : ℝ}
    (domain : PairedEngineDomain n.centered n.data n.parameters U
      (U ^ n.comparison₁) (U ^ n.comparison₂) floor padding) :
    PairedEngineDomain
      (n.mellinStrictModel (Ω := Ω) cap J A lower upper hA hlower hinterval P hP frequency).centered
      (n.mellinStrictModel (Ω := Ω) cap J A lower upper hA hlower hinterval P hP frequency).data
      n.parameters U (U ^ n.comparison₁) (U ^ n.comparison₂) floor padding :=
  { domain with total_length := domain.total_length }

/-- The same current-slot mesh is available before the engine allocates
or removes any slots. No source parameter is reduced here. -/
theorem Node.mellinStrictModel_fitsMesh_of
    (n : Node K ω ψ) (cap J : ℕ) (A lower upper : ℝ)
    (hA : 0 ≤ A) (hlower : 0 < lower) (hinterval : lower ≤ upper)
    (P : ℝ) (hP : 1 ≤ P) (frequency : ℝ × ℝ) {mesh : ℝ}
    (hmesh : n.data.geometry.fitsMesh mesh) :
    (n.mellinStrictModel (Ω := Ω) cap J A lower upper hA hlower hinterval P hP frequency).
      data.geometry.fitsMesh mesh := hmesh

/-- The source window is actually constructed from the normalized
profiles; it is not a callback requesting their regularity. -/
theorem mellinStrictModel_rawWindow
    (r : StrictProfileRange) (extraOrders : Finset (ℕ × ℕ)) (childOrder : ℕ)
    (n : Node K ω ψ) (cap : ℕ) (A lower upper : ℝ)
    (hA : 0 ≤ A) (hlower : 0 < lower) (hinterval : lower ≤ upper)
    (hwide : Set.Icc (lower / 2) (2 * upper) ⊆
      Set.Icc r.expanded.lower r.expanded.upper)
    (P : ℝ) (hP : 1 ≤ P) (U : ℝ) (hU : 0 < U)
    (hcap : n.data.geometry.slotCount ≤ cap)
    (hprofile : ModelProfileControl n.data
      (r.engineOrder (K := K) (ω := ω) (ψ := ψ) extraOrders A childOrder)
      A P 0 lower upper 0) (frequency : ℝ × ℝ) :
    Nonempty (RawProfileWindow Set.univ Set.univ (Set.Icc (lower / 2) (2 * upper))
      (r.inputOrders (K := K) (ω := ω) (ψ := ψ) extraOrders childOrder A)
      (n.mellinStrictModel (Ω := Ω) cap
        (r.mellinOrder (K := K) (ω := ω) (ψ := ψ) extraOrders childOrder A)
        A lower upper hA hlower hinterval P hP frequency).data
      (r.amplitude (K := K) (ω := ω) (ψ := ψ) extraOrders childOrder A)) := by
  have hunit := (mellinStrictTransfer_chosen (Ω := Ω) cap
    (r.mellinOrder (K := K) (ω := ω) (ψ := ψ) extraOrders childOrder A)
    A lower upper hA hlower hinterval P hP n U hU hcap hprofile).1 frequency
  exact r.rawWindow extraOrders childOrder A (lower / 2) (2 * upper) hA hwide
    _ hunit.1 hunit.2

namespace CompleteSourceBudgetData

variable {c : TargetContext K} {theta : Finset (HeckeCharacter K)} {U : ℝ}
variable (n : Node K c.family.omega (targetCharacter K c))
variable (D : CompleteSourceBudgetData c theta U n.data (pairedInvariantParameters n.parameters))

/-- Every strict call uses the original complete recipe on its exact
current parent rows. Both arithmetic budgets are carried by this same
recipe, not reconstructed from equality of Boolean masks. -/
def localizedMellinSource
    (cap J : ℕ) (A lower upper : ℝ) (hA : 0 ≤ A) (hlower : 0 < lower)
    (hinterval : lower ≤ upper) (P : ℝ) (hP : 1 ≤ P) (frequency : ℝ × ℝ) :
    CompleteSourceBudgetData c theta U
      (localizeOriginalParent
        (n.mellinStrictModel (Ω := Ω) cap J A lower upper hA hlower hinterval P hP frequency).data
        n.parameters U) (pairedInvariantParameters n.parameters) :=
  (D.mellinStrictModel (Ω := Ω) n cap J A lower upper hA hlower hinterval P hP frequency).localized

theorem localizedMellinSource_fullJointBudget
    (cap J : ℕ) (A lower upper : ℝ) (hA : 0 ≤ A) (hlower : 0 < lower)
    (hinterval : lower ≤ upper) (P : ℝ) (hP : 1 ≤ P) (frequency : ℝ × ℝ) :
    (D.localizedMellinSource (Ω := Ω) n cap J A lower upper
      hA hlower hinterval P hP frequency).source.recipe.FullJointBudget
      U (n.parameters.m + n.parameters.q) :=
  (D.mellinStrictModel (Ω := Ω) n cap J A lower upper hA hlower hinterval P hP frequency).
    localizedFullJointBudget

end CompleteSourceBudgetData

variable {c : TargetContext K}

/-- The actual row-independent Mellin profiles provide the norm recipe
on exactly the localized singleton family consumed by the engine. -/
def Node.localizedMellinNormProfileRecipe
    (n : Node K c.family.omega (targetCharacter K c))
    (cap J : ℕ) (A lower upper : ℝ) (hA : 0 ≤ A) (hlower : 0 < lower)
    (hinterval : lower ≤ upper) (P : ℝ) (hP : 1 ≤ P) (frequency : ℝ × ℝ) (U : ℝ) :
    NormProfileRecipe (fun _ : PUnit => localizeOriginalParent
      (n.mellinStrictModel (Ω := Ω) cap J A lower upper hA hlower hinterval P hP frequency).data
      n.parameters U) :=
  localizedNormProfileRecipe
    ((n.mellinStrictModel_normProfileRecipe (Ω := Ω) cap J A lower upper
      hA hlower hinterval P hP).at frequency) n.parameters U

end HeckeSkeleton.Moments.EngineInduction

#print axioms HeckeSkeleton.Moments.EngineInduction.Node.mellinStrictModel_domain
#print axioms HeckeSkeleton.Moments.EngineInduction.mellinStrictModel_rawWindow
#print axioms HeckeSkeleton.Moments.EngineInduction.CompleteSourceBudgetData.localizedMellinSource_fullJointBudget
