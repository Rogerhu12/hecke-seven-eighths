import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocatedCapacityProvider

/-!
# Constructing one actual capacity child from primitive inputs

The input contains the original length ledger, annulus windows and
individual prime bounds.  The output fixes a real slot deletion and
contains the exact clipped and restricted MomentData.  Its source bound,
strict width decrease and all induction invariants are proved by the
engine, rather than supplied as fields of an input certificate.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField DedekindZetaZeroFree HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ω ψ : HeckeCharacter F} {k : ℕ}
variable {s : ActualAllocatedSource A V H k}

namespace ActualAllocatedSource.Calibration

variable (D : s.Calibration (σ := σ) ω ψ)

structure CapacityInput where
  skeleton : NominalChildGeometry
  b₂ : ℝ
  p₂ : ℝ
  boundary : ℝ
  ell : ℝ
  gap : ℝ
  delta : ℝ
  mesh : ℝ
  supportError : ℝ
  rawClipError : ℝ
  widthError : ℝ
  leftAnnulus : ℝ
  rightAnnulus : ℝ
  leftAnnulus_one : 1 ≤ leftAnnulus
  rightAnnulus_one : 1 ≤ rightAnnulus
  left_window : ∀ ξ, ∀ u ∈ pairedRows (D.data ξ) D.parameters s.base, ∀ x,
    (D.data ξ).plainTest₁.profile u (D.height ξ) x ≠ 0 → x ≤ leftAnnulus
  right_window : ∀ ξ, ∀ u ∈ pairedRows (D.data ξ) D.parameters s.base, ∀ x,
    (D.data ξ).plainTest₂.profile u (D.height ξ) x ≠ 0 → x ≤ rightAnnulus
  gap_pos : 0 < gap
  kappa_pos : 0 < D.parameters.κ
  mesh_nonneg : 0 ≤ mesh
  mesh_bound : ∀ i, s.length i ≤ mesh
  enlargement : skeleton.enlargementJ + gap ≤ skeleton.g
  unit_part : skeleton.t₂ ≤ skeleton.g₂
  actual_width : D.parameters.m + D.parameters.q ≤ skeleton.nominalWidth + delta
  delta_bound : delta ≤ gap / 2
  principal_part : p₂ ≤ b₂
  boundary_nonneg : 0 ≤ boundary
  parent_capacity : s.allocation.keep.card = 0 ∨
    skeleton.A + (6 * D.parameters.κ - 1) * s.beforeLength ≤ skeleton.parentWidth
  common_part : skeleton.g₂ - skeleton.t₂ ≤ skeleton.c₂
  paid_shift : s.allocation.keep.card = 0 ∨
    skeleton.paidShift ≤ 6 * (skeleton.w + ell) + supportError
  raw_degree : D.parameters.n₁ + D.parameters.n₂ + D.parameters.z ≤
    skeleton.rawDegree - s.allocatedLength + rawClipError
  width_error : skeleton.nominalWidth - (D.parameters.m + D.parameters.q) ≤ widthError
  budget_nonneg : 0 ≤ 6 * (skeleton.w + ell) + supportError + rawClipError + widthError
  charge_nonneg : 0 ≤ (b₂ - p₂ + skeleton.w + boundary + ell) +
    (supportError + rawClipError + widthError) / 6 + D.parameters.κ * mesh
  primeBound : V → Fin s.allocation.keep.card → ℝ
  primeBound_nonneg : ∀ ξ i, 0 ≤ primeBound ξ i
  prime_bound : ∀ ξ, ∀ u ∈ pairedRows (D.data ξ) D.parameters s.base,
    ∀ i : Fin s.allocation.keep.card,
    ‖primePolynomial (D.data ξ)
      (lengthSlot (D.data ξ) s.allocation.keep.card (D.count ξ) i) u s.base (D.height ξ)‖ ^ 2 ≤
        primeBound ξ i * s.base ^ (D.parameters.κ * s.childLength i)

namespace CapacityInput

variable {D} (I : D.CapacityInput)

def exponent : ℝ :=
  (I.b₂ - I.p₂ + I.skeleton.w + I.boundary + I.ell) +
    (I.supportError + (I.rawClipError +
      (Real.log I.leftAnnulus + Real.log I.rightAnnulus) / Real.log s.base) +
        I.widthError) / 6 + D.parameters.κ * I.mesh

def allowance (removed : Finset (Fin s.allocation.keep.card)) (ξ : V) : ℝ :=
  (∏ i ∈ removed, I.primeBound ξ i) * s.base ^ I.exponent

theorem allowance_nonneg (removed : Finset (Fin s.allocation.keep.card)) (ξ : V) :
    0 ≤ I.allowance removed ξ :=
  mul_nonneg (Finset.prod_nonneg (fun i _ => I.primeBound_nonneg ξ i))
    (Real.rpow_nonneg (zero_le_one.trans s.base_gt_one.le) _)

end CapacityInput

/-- A constructed output.  The data and parameters are determined by
the original source and the single finite deletion. -/
structure CapacityChild (I : D.CapacityInput) where
  removed : Finset (Fin s.allocation.keep.card)
  width_nonneg : 0 ≤ D.parameters.m + D.parameters.q
  width_le : D.parameters.m + D.parameters.q ≤ I.skeleton.parentWidth - I.gap / 2
  width_lt : D.parameters.m + D.parameters.q < I.skeleton.parentWidth
  left_nonneg : 0 ≤ (D.restrictedParameters (Finset.univ \ removed)).n₁
  right_nonneg : 0 ≤ (D.restrictedParameters (Finset.univ \ removed)).n₂
  kappa_eq : (D.restrictedParameters (Finset.univ \ removed)).κ = D.parameters.κ
  width_eq : (D.restrictedParameters (Finset.univ \ removed)).m +
    (D.restrictedParameters (Finset.univ \ removed)).q = D.parameters.m + D.parameters.q
  z_nonneg : 0 ≤ (D.restrictedParameters (Finset.univ \ removed)).z
  z_le : (D.restrictedParameters (Finset.univ \ removed)).z ≤ D.parameters.z
  capacity : let a := D.restrictedParameters (Finset.univ \ removed)
    a.z = 0 ∨ a.n₁ + a.n₂ + 6 * a.κ * a.z ≤ a.m + a.q
  zero_inherited : s.beforeLength = 0 → (D.restrictedParameters (Finset.univ \ removed)).z = 0
  slot_count : ∀ ξ, (D.restrictedClippedData (Finset.univ \ removed) ξ).geometry.slotCount ≤ k
  actual_z : ∀ ξ, (D.restrictedParameters (Finset.univ \ removed)).z =
    (D.restrictedClippedData (Finset.univ \ removed) ξ).geometry.totalLength
  mesh : ∀ ξ, (D.restrictedClippedData (Finset.univ \ removed) ξ).geometry.fitsMesh I.mesh
  theta : ∀ ξ i, (D.restrictedClippedData (Finset.univ \ removed) ξ).slotCoefficient i ∈
    (D.restrictedClippedData (Finset.univ \ removed) ξ).theta
  energy_bound : ∀ ξ, s.energy (σ := σ) ξ ≤ D.mass * I.allowance removed ξ *
    pairedEnergy (D.restrictedClippedData (Finset.univ \ removed) ξ)
      (D.restrictedParameters (Finset.univ \ removed)) s.base (D.height ξ)

namespace CapacityChild

variable {D} {I : D.CapacityInput} (c : D.CapacityChild I)

def data (ξ : V) : MomentData F ω ψ := D.restrictedClippedData (Finset.univ \ c.removed) ξ

def parameters : RealParameters := D.restrictedParameters (Finset.univ \ c.removed)

def cost (ξ : V) : ℝ := D.mass * I.allowance c.removed ξ

theorem cost_nonneg (ξ : V) : 0 ≤ c.cost ξ :=
  mul_nonneg D.mass_nonneg (I.allowance_nonneg c.removed ξ)

theorem source_bound (ξ : V) :
    s.energy (σ := σ) ξ ≤ c.cost ξ * pairedEnergy (c.data ξ) c.parameters s.base (D.height ξ) :=
  c.energy_bound ξ

end CapacityChild

/-- This is the producing theorem: all inequalities in CapacityChild
are derived from raw arithmetic/profile/geometry inputs. -/
theorem produce_capacity_child (I : D.CapacityInput) :
    (∀ ξ, s.energy (σ := σ) ξ = 0) ∨ Nonempty (D.CapacityChild I) := by
  rcases D.zero_or_capacity_provider I.skeleton I.b₂ I.p₂ I.boundary I.ell I.gap
      I.delta I.mesh I.supportError I.rawClipError I.widthError
      I.leftAnnulus I.rightAnnulus I.leftAnnulus_one I.rightAnnulus_one
      I.left_window I.right_window I.gap_pos I.kappa_pos I.mesh_nonneg I.mesh_bound
      I.enlargement I.unit_part I.actual_width I.delta_bound I.principal_part
      I.boundary_nonneg I.parent_capacity I.common_part I.paid_shift I.raw_degree
      I.width_error I.budget_nonneg I.charge_nonneg
      I.primeBound I.primeBound_nonneg I.prime_bound with hzero | hchild
  · exact Or.inl hzero
  · right
    rcases hchild with ⟨hw, hle, hlt, removed, hchild⟩
    dsimp only at hchild
    rcases hchild with ⟨h₁, h₂, hκ, hwidth, hz, hzle, hcap, hzero, hfamily⟩
    exact ⟨{
      removed := removed
      width_nonneg := hw
      width_le := hle
      width_lt := hlt
      left_nonneg := h₁
      right_nonneg := h₂
      kappa_eq := hκ
      width_eq := hwidth
      z_nonneg := hz
      z_le := hzle
      capacity := hcap
      zero_inherited := hzero
      slot_count := fun ξ => (hfamily ξ).1
      actual_z := fun ξ => (hfamily ξ).2.1
      mesh := fun ξ => (hfamily ξ).2.2.1
      theta := fun ξ => (hfamily ξ).2.2.2.1
      energy_bound := fun ξ => (hfamily ξ).2.2.2.2 }⟩

end ActualAllocatedSource.Calibration
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.produce_capacity_child
