import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ReductionOutput

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# One side-indexed family of actual child data

`false` and `true` select the two Cauchy sides.  Every invariant is stated
once and is carried by the original child, before the common Fourier
variable is evaluated.  Reindexing changes labels only.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open EngineStep

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

structure ChildFamily (I Ω : Type*) (d : MomentData K ω ψ) (a : RealParameters)
    (σ : ℝ) (admissible : MomentData K ω ψ → RealParameters → Prop) where
  data : Bool → I → Ω → MomentData K ω ψ
  parameters : Bool → I → RealParameters
  width : ∀ side b, (parameters side b).m + (parameters side b).q ≤ a.m + a.q - σ / 2
  width_nonneg : ∀ side b, 0 ≤ (parameters side b).m + (parameters side b).q
  plain_left_nonneg : ∀ side b, 0 ≤ (parameters side b).n₁
  plain_right_nonneg : ∀ side b, 0 ≤ (parameters side b).n₂
  length : ∀ side b ξ, (parameters side b).z = (data side b ξ).geometry.totalLength
  kappa : ∀ side b, (parameters side b).κ = a.κ
  slots : ∀ side b ξ, (data side b ξ).geometry.slotCount ≤ d.geometry.slotCount
  theta : ∀ side b ξ, (data side b ξ).theta = d.theta
  slot_characters : ∀ side b ξ i, (data side b ξ).slotCoefficient i ∈ d.theta
  admissible_data : ∀ side b ξ, admissible (data side b ξ) (parameters side b)
  capacity : ∀ side b, (parameters side b).z = 0 ∨
    (parameters side b).n₁ + (parameters side b).n₂ +
      6 * (parameters side b).κ * (parameters side b).z ≤
        (parameters side b).m + (parameters side b).q

namespace ChildFamily

variable {I J Ω : Type*} {d : MomentData K ω ψ} {a : RealParameters} {σ : ℝ}
variable {admissible : MomentData K ω ψ → RealParameters → Prop}

def energy (f : ChildFamily I Ω d a σ admissible)
    (side : Bool) (b : I) (Z : ℝ) (ξ : Ω) : ℝ :=
  normalizedPairedEnergy (f.data side b ξ) (f.parameters side b) Z 0

theorem energy_nonneg (f : ChildFamily I Ω d a σ admissible)
    (side : Bool) (b : I) (Z : ℝ) (ξ : Ω) (hZ : 0 < Z) :
    0 ≤ f.energy side b Z ξ := by
  sorry

def pair (f : ChildFamily I Ω d a σ admissible) (b : I) (Z : ℝ) (ξ : Ω) : ℝ :=
  Real.sqrt (f.energy false b Z ξ) * Real.sqrt (f.energy true b Z ξ)

theorem pair_nonneg (f : ChildFamily I Ω d a σ admissible)
    (b : I) (Z : ℝ) (ξ : Ω) : 0 ≤ f.pair b Z ξ := by
  sorry

theorem pair_le_average (f : ChildFamily I Ω d a σ admissible)
    (b : I) (Z : ℝ) (ξ : Ω) (hZ : 0 < Z) :
    f.pair b Z ξ ≤ (f.energy false b Z ξ + f.energy true b Z ξ) / 2 := by
  sorry

def reindex (f : ChildFamily I Ω d a σ admissible) (e : J → I) :
    ChildFamily J Ω d a σ admissible where
  data side b := f.data side (e b)
  parameters side b := f.parameters side (e b)
  width side b := f.width side (e b)
  width_nonneg side b := f.width_nonneg side (e b)
  plain_left_nonneg side b := f.plain_left_nonneg side (e b)
  plain_right_nonneg side b := f.plain_right_nonneg side (e b)
  length side b := f.length side (e b)
  kappa side b := f.kappa side (e b)
  slots side b := f.slots side (e b)
  theta side b := f.theta side (e b)
  slot_characters side b := f.slot_characters side (e b)
  admissible_data side b := f.admissible_data side (e b)
  capacity side b := f.capacity side (e b)

@[simp] theorem reindex_energy (f : ChildFamily I Ω d a σ admissible)
    (e : J → I) (side : Bool) (b : J) (Z : ℝ) (ξ : Ω) :
    (f.reindex e).energy side b Z ξ = f.energy side (e b) Z ξ := by
  sorry

@[simp] theorem reindex_pair (f : ChildFamily I Ω d a σ admissible)
    (e : J → I) (b : J) (Z : ℝ) (ξ : Ω) :
    (f.reindex e).pair b Z ξ = f.pair (e b) Z ξ := by
  sorry

def sigma {J : Type*} {I : J → Type*}
    (f : ∀ j, ChildFamily (I j) Ω d a σ admissible) :
    ChildFamily (Sigma I) Ω d a σ admissible where
  data side b := (f b.1).data side b.2
  parameters side b := (f b.1).parameters side b.2
  width side b := (f b.1).width side b.2
  width_nonneg side b := (f b.1).width_nonneg side b.2
  plain_left_nonneg side b := (f b.1).plain_left_nonneg side b.2
  plain_right_nonneg side b := (f b.1).plain_right_nonneg side b.2
  length side b := (f b.1).length side b.2
  kappa side b := (f b.1).kappa side b.2
  slots side b := (f b.1).slots side b.2
  theta side b := (f b.1).theta side b.2
  slot_characters side b := (f b.1).slot_characters side b.2
  admissible_data side b := (f b.1).admissible_data side b.2
  capacity side b := (f b.1).capacity side b.2

theorem strict_width (f : ChildFamily I Ω d a σ admissible)
    (hσ : 0 < σ) (side : Bool) (b : I) :
    (f.parameters side b).m + (f.parameters side b).q < a.m + a.q := by
  sorry

theorem zero_slots (f : ChildFamily I Ω d a σ admissible)
    (hzero : d.geometry.slotCount = 0) (side : Bool) (b : I) (ξ : Ω) :
    (f.data side b ξ).geometry.slotCount = 0 := by
  sorry

end ChildFamily
end HeckeSkeleton.Moments.EngineStepV2

#print axioms HeckeSkeleton.Moments.EngineStepV2.ChildFamily.pair_le_average
#print axioms HeckeSkeleton.Moments.EngineStepV2.ChildFamily.strict_width
#print axioms HeckeSkeleton.Moments.EngineStepV2.ChildFamily.zero_slots
