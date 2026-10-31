import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocatedChildFamily
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualScaleClipping
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildInvariants

/-!
# A calibrated actual allocation supplies its child family

The source fixes its actual allocated columns, whole coefficient factors,
row scalars, and Fourier locations before the Fourier parameter.  The
calibration below contains only single-ideal/single-prime arithmetic and
profile dictionaries, actual row membership, and row fibers.  Its energy
comparison is a theorem, never a field of the calibration.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum WholeAllocation

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ω ψ : HeckeCharacter F} {k : ℕ}

/-- A nonempty branch of the literal finite allocation family supplies
the witness needed for its actual quotient and live-slot supports. -/
def actualAllocationOfNonempty
    (D : Ideal (𝓞 F)) (a : primeSupport D → Finset (Fin (k + 2)))
    (S₁ S₂ : Finset (Ideal (𝓞 F)))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 F)))
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ J ∈ S₂, J ≠ 0)
    (hne : (pairedAllocatedColumns D a S₁ S₂ S id id HeightOneSpectrum.asIdeal).Nonempty) :
    ActualColumnAllocation F k where
  divisor := D
  selection := a
  plain₁ := S₁
  plain₂ := S₂
  slots := S
  plain₁_nonzero := hS₁
  plain₂_nonzero := hS₂
  witness := hne.choose
  witness_mem := hne.choose_spec

/-- Empty branches of the true allocation family contribute exactly
zero before any child calibration is requested. -/
theorem allocated_energy_zero_of_empty
    (D : Ideal (𝓞 F)) (a : primeSupport D → Finset (Fin (k + 2)))
    (S₁ S₂ : Finset (Ideal (𝓞 F)))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 F)))
    (rows : Finset H) (q : H → ℂ)
    (c : H → (Ideal (𝓞 F) × Ideal (𝓞 F)) × (Fin k → HeightOneSpectrum (𝓞 F)) → ℂ)
    (x : H → (Ideal (𝓞 F) × Ideal (𝓞 F)) × (Fin k → HeightOneSpectrum (𝓞 F)) → V)
    (ξ : V)
    (hempty : ¬(pairedAllocatedColumns D a S₁ S₂ S id id HeightOneSpectrum.asIdeal).Nonempty) :
    jointColumnEnergy rows
      (pairedAllocatedColumns D a S₁ S₂ S id id HeightOneSpectrum.asIdeal) q c x ξ = 0 := by
  rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
  simp only [jointColumnEnergy, jointFourierColumn, Finset.sum_empty,
    norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero]

/-- Everything in this record is the actual fixed finite source. -/
structure ActualAllocatedSource (A : SArithmeticData F) (V H : Type*) (k : ℕ) where
  allocation : ActualColumnAllocation F k
  rows : Finset H
  weight : H → ℂ
  originalIdeal : H → A.Exterior
  frequency : H → A.R
  extractedFactor : H → A.R
  normFactor : H → ℝ
  row : ∀ h, ActualChildRow (originalIdeal h) (frequency h) (extractedFactor h) (normFactor h)
  characters : H → FixedChildCharacters F k
  scale₁ : ℝ
  scale₂ : ℝ
  base : ℝ
  base_gt_one : 1 < base
  length : Fin k → ℝ
  length_pos : ∀ i, 0 < length i
  leftWeight : H → HeckeGeneral.Analysis.NonzeroIdeal F → ℂ
  rightWeight : H → HeckeGeneral.Analysis.NonzeroIdeal F → ℂ
  slotWeight : H → Fin k → HeightOneSpectrum (𝓞 F) → ℂ
  leftLocation : H → HeckeGeneral.Analysis.NonzeroIdeal F → V
  rightLocation : H → HeckeGeneral.Analysis.NonzeroIdeal F → V
  slotLocation : H → Fin k → HeightOneSpectrum (𝓞 F) → V

namespace ActualAllocatedSource

variable (s : ActualAllocatedSource A V H k)

def childLength (i : Fin s.allocation.keep.card) : ℝ :=
  s.length (SlotRestriction.index s.allocation.keep i)

def frozenScalar (h : H) : ℂ :=
  s.allocation.scalar (σ := σ) (s.characters h) (s.extractedFactor h) (s.row h).element
    s.base s.length (s.slotWeight h)

def childWeight (h : H) : ℂ := s.weight h * s.frozenScalar (σ := σ) h *
  star (s.frozenScalar (σ := σ) h)

def energy (ξ : V) : ℝ :=
  jointColumnEnergy s.rows s.allocation.columns s.weight
    (fun h => rawSourceCoefficient (σ := σ) (s.characters h)
      (s.extractedFactor h) (s.row h).element s.scale₁ s.scale₂ s.base s.length
      (s.leftWeight h) (s.rightWeight h) (s.slotWeight h))
    (fun h => rawSourceLocation (s.leftLocation h) (s.rightLocation h) (s.slotLocation h)) ξ

theorem energy_nonneg (ξ : V) : 0 ≤ s.energy (σ := σ) ξ :=
  jointColumnEnergy_nonneg _ _ _ _ _ _

/-- Raw source calibration: no whole polynomial identity and no moment
comparison occurs among these fields. -/
structure Calibration (ω ψ : HeckeCharacter F) where
  data : V → MomentData F ω ψ
  parameters : RealParameters
  height : V → ℝ
  count : ∀ ξ, (data ξ).geometry.slotCount = s.allocation.keep.card
  lengths : ∀ ξ i, ((data ξ).geometry.slots i).length = s.childLength (Fin.cast (count ξ) i)
  left_scale : s.base ^ parameters.n₁ =
    s.scale₁ / HeckeGeneral.Analysis.idealNorm F (s.allocation.plainDivisor 0)
  right_scale : s.base ^ parameters.n₂ =
    s.scale₂ / HeckeGeneral.Analysis.idealNorm F (s.allocation.plainDivisor (Fin.succ 0))
  slot_sum : parameters.z = ∑ i, s.childLength i
  dictionary : ∀ ξ h, ((s.characters h).restrictSlots s.allocation.keep).Calibration
    (σ := σ) (data ξ) (count ξ) (s.row h).momentIdeal
      (s.extractedFactor h) (s.row h).element
  left_support : ∀ ξ, ∀ h ∈ s.rows,
    (data ξ).plainTest₁.support (s.row h).momentIdeal (height ξ) (s.base ^ parameters.n₁) ⊆
      s.allocation.childPlain₁
  right_support : ∀ ξ, ∀ h ∈ s.rows,
    (data ξ).plainTest₂.support (s.row h).momentIdeal (height ξ) (s.base ^ parameters.n₂) ⊆
      s.allocation.childPlain₂
  slot_support : ∀ ξ i, ((data ξ).geometry.slots i).support (height ξ)
    (s.base ^ ((data ξ).geometry.slots i).length) ⊆
      s.allocation.childSlots (Fin.cast (count ξ) i)
  left_profile : ∀ ξ, ∀ h ∈ s.rows, ∀ I ∈ s.allocation.childPlain₁,
    s.leftWeight h (s.allocation.plainDivisor 0 * I) *
      jointPhase ξ (s.leftLocation h (s.allocation.plainDivisor 0 * I)) =
      (data ξ).plainTest₁.profile (s.row h).momentIdeal (height ξ)
        (HeckeGeneral.Analysis.idealNorm F I / s.base ^ parameters.n₁)
  right_profile : ∀ ξ, ∀ h ∈ s.rows, ∀ I ∈ s.allocation.childPlain₂,
    s.rightWeight h (s.allocation.plainDivisor (Fin.succ 0) * I) *
      jointPhase ξ (s.rightLocation h (s.allocation.plainDivisor (Fin.succ 0) * I)) =
      (data ξ).plainTest₂.profile (s.row h).momentIdeal (height ξ)
        (HeckeGeneral.Analysis.idealNorm F I / s.base ^ parameters.n₂)
  slot_profile : ∀ ξ, ∀ h ∈ s.rows, ∀ i,
    ∀ p ∈ s.allocation.childSlots (Fin.cast (count ξ) i),
      s.slotWeight h (SlotRestriction.index s.allocation.keep (Fin.cast (count ξ) i)) p *
        jointPhase ξ
          (s.slotLocation h (SlotRestriction.index s.allocation.keep (Fin.cast (count ξ) i)) p) =
          ((data ξ).geometry.slots i).profile (height ξ)
            ((Ideal.absNorm p.asIdeal : ℝ) / s.base ^ ((data ξ).geometry.slots i).length)
  allowed : ∀ ξ, ∀ h ∈ s.rows, (data ξ).allowedRow (s.row h).momentIdeal
  cutoff : ∀ h ∈ s.rows,
    A.exteriorNorm (s.originalIdeal h) ≤ s.normFactor h * s.base ^ (parameters.m + parameters.q)
  nonexceptional : ∀ ξ, ∀ h ∈ s.rows,
    if parameters.z = 0 then (data ξ).plainBackground * (data ξ).rowCharacter (s.row h).momentIdeal ≠ 1
    else (data ξ).rowCharacter (s.row h).momentIdeal ∉ (data ξ).theta
  rowBound : ℝ
  rowBound_nonneg : 0 ≤ rowBound
  row_bound : ∀ h ∈ s.rows, ‖s.weight h‖ ≤ rowBound
  scalarBound : ℝ
  scalarBound_nonneg : 0 ≤ scalarBound
  scalar_bound : ∀ h ∈ s.rows, ‖s.frozenScalar (σ := σ) h‖ ^ 2 ≤ scalarBound
  fiberBound : ℕ
  fibers : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal F,
    (s.rows.filter (fun h => (s.row h).momentIdeal = I)).card ≤ fiberBound
  principal_in_theta : ∀ ξ, ∀ u : HeckeGeneral.Analysis.NonzeroIdeal F,
    (data ξ).plainBackground * (data ξ).rowCharacter u = 1 →
      (data ξ).rowCharacter u ∈ (data ξ).theta
  slot_in_theta : ∀ ξ i, (data ξ).slotCoefficient i ∈ (data ξ).theta

namespace Calibration

variable {s} (D : s.Calibration (σ := σ) ω ψ)

def mass : ℝ := D.rowBound * D.scalarBound * (D.fiberBound : ℝ)

theorem mass_nonneg : 0 ≤ D.mass :=
  mul_nonneg (mul_nonneg D.rowBound_nonneg D.scalarBound_nonneg) (Nat.cast_nonneg _)

theorem child_weight_bound (h : H) (hh : h ∈ s.rows) :
    ‖s.childWeight (σ := σ) h‖ ≤ D.rowBound * D.scalarBound := by
  simp only [childWeight, norm_mul, norm_star]
  calc
    _ = ‖s.weight h‖ * ‖s.frozenScalar (σ := σ) h‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul (D.row_bound h hh) (D.scalar_bound h hh)
      (sq_nonneg _) D.rowBound_nonneg

/-- Every allocated source energy is compared to its actual child from
the raw term dictionaries and the actual row map. -/
theorem energy_le (ξ : V) :
    s.energy (σ := σ) ξ ≤ D.mass * pairedEnergy (D.data ξ) D.parameters s.base (D.height ξ) := by
  have hb := fixed_child_family_energy_from_terms s.rows s.originalIdeal s.frequency
    s.extractedFactor s.normFactor s.row
    (fun h => (s.characters h).restrictSlots s.allocation.keep)
    D.data D.parameters s.base D.height D.count s.childLength D.lengths D.dictionary
    s.allocation.childPlain₁ s.allocation.childPlain₂ s.allocation.childSlots
    D.left_support D.right_support D.slot_support
    (fun h I => s.leftWeight h (s.allocation.plainDivisor 0 * I))
    (fun h I => s.rightWeight h (s.allocation.plainDivisor (Fin.succ 0) * I))
    (fun h i => s.slotWeight h (SlotRestriction.index s.allocation.keep i))
    (fun h I => s.leftLocation h (s.allocation.plainDivisor 0 * I))
    (fun h I => s.rightLocation h (s.allocation.plainDivisor (Fin.succ 0) * I))
    (fun h i => s.slotLocation h (SlotRestriction.index s.allocation.keep i))
    D.left_profile D.right_profile D.slot_profile
    (s.childWeight (σ := σ)) (D.rowBound * D.scalarBound) D.fiberBound
    (mul_nonneg D.rowBound_nonneg D.scalarBound_nonneg) D.child_weight_bound
    D.allowed D.cutoff D.nonexceptional D.fibers ξ
  unfold energy
  rw [s.allocation.joint_energy]
  rw [← D.left_scale, ← D.right_scale]
  exact hb

def clippedParameters : RealParameters := clipPlainParameters D.parameters

def clippedData (ξ : V) : MomentData F ω ψ :=
  clipPlainData (D.data ξ) D.parameters s.base (zero_lt_one.trans s.base_gt_one)

theorem energy_le_clipped (ξ : V) :
    s.energy (σ := σ) ξ ≤
      D.mass * pairedEnergy (D.clippedData ξ) D.clippedParameters s.base (D.height ξ) := by
  rw [clippedData, clippedParameters, pairedEnergy_clipped]
  exact D.energy_le ξ

theorem clipped_width_nonneg_of_source_nonzero (ξ : V)
    (hne : s.energy (σ := σ) ξ ≠ 0) :
    0 ≤ D.clippedParameters.m + D.clippedParameters.q := by
  have hE : pairedEnergy (D.data ξ) D.parameters s.base (D.height ξ) ≠ 0 := by
    intro hz
    have hb := D.energy_le ξ
    rw [hz, mul_zero] at hb
    exact hne (le_antisymm hb (s.energy_nonneg (σ := σ) ξ))
  exact paired_width_nonneg_of_energy_ne_zero (D.data ξ) D.parameters s.base
    (D.height ξ) s.base_gt_one hE

end Calibration
end ActualAllocatedSource

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.energy_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.energy_le_clipped
