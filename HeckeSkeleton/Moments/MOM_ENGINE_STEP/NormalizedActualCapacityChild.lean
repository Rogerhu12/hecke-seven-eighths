import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ProfileNormalizationInput
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondBranchProduction

/-!
# Normalizing the actual child after its one fixed capacity deletion

The primitive capacity producer is called internally. Its raw bound for
a removed prime is A(ξ)² Bᵢ. The remaining actual profiles are divided by
the same positive A(ξ). The two factors combine to exactly
A(ξ)^(2(n+2)), with n the slot count before capacity removal. Thus the
choice of removed slots stays outside both Fourier parameters and the
degree is retained even when every slot is removed.

The profile input is a literal single-profile window for the original
clipped data. Restriction only selects its prime representatives, and
normalization proves membership in the fixed unit ball. No input
contains an aggregate energy estimate or admissibility of the output.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField DedekindZetaZeroFree HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F] {ω ψ : HeckeCharacter F}

namespace ProfileNormalizationInput

theorem paired_energy_recover (P : ProfileNormalizationInput F ω ψ)
    (d : MomentData F ω ψ) (a : RealParameters) (A : ℝ) (hA : 0 < A) (Z t : ℝ) :
    pairedEnergy d a Z t =
      A ^ ((d.geometry.slotCount + 2) * 2) *
        pairedEnergy (P.normalizeData d A hA) a Z t := by
  change pairedEnergy d a Z t =
    A ^ ((d.geometry.slotCount + 2) * 2) *
      pairedEnergy (P.scaleData d A⁻¹ (inv_pos.mpr hA)) a Z t
  rw [P.energy_scale, inv_pow, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ hA.ne'), one_mul]

end ProfileNormalizationInput

/-- Restricting actual slots retains the original profile window. -/
def RawProfileWindow.restrictSlots
    {rowDomain : Set (NonzeroIdeal F)} {heightDomain window : Set ℝ}
    {seminorms : Finset (ℕ × ℕ)} {d : MomentData F ω ψ} {A : ℝ}
    (raw : RawProfileWindow rowDomain heightDomain window seminorms d A)
    (keep : Finset (Fin d.geometry.slotCount)) :
    RawProfileWindow rowDomain heightDomain window seminorms (d.restrictSlots keep) A where
  inverseRep := raw.inverseRep
  leftRep := raw.leftRep
  rightRep := raw.rightRep
  primeRep := fun i => raw.primeRep (selectedSlotIndex keep i)
  inverse_eq := raw.inverse_eq
  left_eq := raw.left_eq
  right_eq := raw.right_eq
  prime_eq := fun i => raw.prime_eq (selectedSlotIndex keep i)
  inverse_support := raw.inverse_support
  left_support := raw.left_support
  right_support := raw.right_support
  prime_support := fun i => raw.prime_support (selectedSlotIndex keep i)
  inverse_bound := raw.inverse_bound
  left_bound := raw.left_bound
  right_bound := raw.right_bound
  prime_bound := fun i => raw.prime_bound (selectedSlotIndex keep i)

variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {s : ActualAllocatedSource A V H k}

namespace ActualAllocatedSource.Calibration.CapacityChild

variable {cal : s.Calibration (σ := σ) ω ψ} {input : cal.CapacityInput}
variable (c : cal.CapacityChild input)

theorem data_count (ξ : V) :
    (c.data ξ).geometry.slotCount = (Finset.univ \ c.removed).card :=
  cal.restricted_count _ ξ

theorem count_partition :
    c.removed.card + (Finset.univ \ c.removed).card = s.allocation.keep.card := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ c.removed)
  simpa only [Finset.card_univ, Fintype.card_fin, add_comm] using h

def normalizedData (P : ProfileNormalizationInput F ω ψ)
    (amplitude : V → ℝ) (hpos : ∀ ξ, 0 < amplitude ξ) (ξ : V) : MomentData F ω ψ :=
  P.normalizeData (c.data ξ) (amplitude ξ) (hpos ξ)

/-- The raw Fourier envelope has been factored out, not estimated. -/
def envelopeFreeCost (bounds : Fin s.allocation.keep.card → ℝ) : ℝ :=
  cal.mass * ((∏ i ∈ c.removed, bounds i) * s.base ^ input.exponent)

theorem envelopeFreeCost_nonneg (bounds : Fin s.allocation.keep.card → ℝ)
    (hbounds : ∀ i, 0 ≤ bounds i) : 0 ≤ c.envelopeFreeCost bounds :=
  mul_nonneg cal.mass_nonneg (mul_nonneg (Finset.prod_nonneg fun i _ => hbounds i)
    (Real.rpow_nonneg (zero_le_one.trans s.base_gt_one.le) _))

/-- All geometric and arithmetic invariants of the real child survive
the positive profile scaling. The child parameters themselves are fixed. -/
theorem normalized_invariants (P : ProfileNormalizationInput F ω ψ)
    (amplitude : V → ℝ) (hpos : ∀ ξ, 0 < amplitude ξ) (ξ : V) :
    (c.normalizedData P amplitude hpos ξ).geometry.slotCount =
        (Finset.univ \ c.removed).card ∧
    (c.normalizedData P amplitude hpos ξ).geometry.slotCount ≤ k ∧
    c.parameters.z = (c.normalizedData P amplitude hpos ξ).geometry.totalLength ∧
    (c.normalizedData P amplitude hpos ξ).geometry.fitsMesh input.mesh ∧
    (∀ i, (c.normalizedData P amplitude hpos ξ).slotCoefficient i ∈
      (c.normalizedData P amplitude hpos ξ).theta) := by
  have hc := P.normalized_count (c.data ξ) (amplitude ξ) (hpos ξ)
  refine ⟨hc.trans (c.data_count ξ), hc.le.trans (c.slot_count ξ), ?_, ?_, ?_⟩
  · exact (c.actual_z ξ).trans
      (P.totalLength (c.data ξ) (amplitude ξ)⁻¹ (inv_pos.mpr (hpos ξ))).symm
  · exact (P.fitsMesh (c.data ξ) (amplitude ξ)⁻¹
      (inv_pos.mpr (hpos ξ)) input.mesh).mpr (c.mesh ξ)
  · intro i
    change (P.scaleData (c.data ξ) (amplitude ξ)⁻¹
      (inv_pos.mpr (hpos ξ))).slotCoefficient i ∈
        (P.scaleData (c.data ξ) (amplitude ξ)⁻¹ (inv_pos.mpr (hpos ξ))).theta
    rw [P.slotCoefficient, P.theta]
    exact c.theta ξ _

theorem normalized_in_fixed_window
    (P : ProfileNormalizationInput F ω ψ)
    (amplitude : V → ℝ) (hpos : ∀ ξ, 0 < amplitude ξ)
    (rowDomain : Set (NonzeroIdeal F)) (heightDomain window : Set ℝ)
    (seminorms : Finset (ℕ × ℕ))
    (raw : ∀ ξ, RawProfileWindow rowDomain heightDomain window seminorms
      (cal.clippedData ξ) (amplitude ξ)) (ξ : V) :
    InFixedProfileWindow rowDomain heightDomain window seminorms
      (c.normalizedData P amplitude hpos ξ) := by
  apply P.normalized_in_fixed_window (hpos ξ)
  exact (raw ξ).restrictSlots
    (lengthSelection (cal.clippedData ξ) s.allocation.keep.card
      (cal.count ξ) (Finset.univ \ c.removed))

/-- Exact cancellation of the removed-slot envelope and the live-child
homogeneity. No factor from frozen allocation slots is counted here. -/
theorem normalized_cost_energy
    (P : ProfileNormalizationInput F ω ψ)
    (amplitude : V → ℝ) (hpos : ∀ ξ, 0 < amplitude ξ)
    (bounds : Fin s.allocation.keep.card → ℝ)
    (hfactor : ∀ ξ i, input.primeBound ξ i = amplitude ξ ^ 2 * bounds i) (ξ : V) :
    c.cost ξ * pairedEnergy (c.data ξ) c.parameters s.base (cal.height ξ) =
      c.envelopeFreeCost bounds * amplitude ξ ^ ((s.allocation.keep.card + 2) * 2) *
        pairedEnergy (c.normalizedData P amplitude hpos ξ) c.parameters s.base (cal.height ξ) := by
  rw [P.paired_energy_recover (c.data ξ) c.parameters (amplitude ξ)
    (hpos ξ) s.base (cal.height ξ), c.data_count ξ]
  have he := removed_profile_envelope_degree c.removed bounds (amplitude ξ)
    (Finset.univ \ c.removed).card s.allocation.keep.card c.count_partition
  change
    (cal.mass * ((∏ i ∈ c.removed, input.primeBound ξ i) * s.base ^ input.exponent)) *
      (amplitude ξ ^ (((Finset.univ \ c.removed).card + 2) * 2) *
        pairedEnergy (c.normalizedData P amplitude hpos ξ) c.parameters s.base (cal.height ξ)) =
      c.envelopeFreeCost bounds * amplitude ξ ^ ((s.allocation.keep.card + 2) * 2) *
        pairedEnergy (c.normalizedData P amplitude hpos ξ) c.parameters s.base (cal.height ξ)
  simp_rw [hfactor ξ]
  calc
    _ = (cal.mass * s.base ^ input.exponent) *
        ((∏ i ∈ c.removed, amplitude ξ ^ 2 * bounds i) *
          amplitude ξ ^ (((Finset.univ \ c.removed).card + 2) * 2)) *
        pairedEnergy (c.normalizedData P amplitude hpos ξ) c.parameters s.base (cal.height ξ) := by ring
    _ = _ := by rw [he]; unfold envelopeFreeCost; ring

theorem normalized_source_bound
    (P : ProfileNormalizationInput F ω ψ)
    (amplitude : V → ℝ) (hpos : ∀ ξ, 0 < amplitude ξ)
    (bounds : Fin s.allocation.keep.card → ℝ)
    (hfactor : ∀ ξ i, input.primeBound ξ i = amplitude ξ ^ 2 * bounds i) (ξ : V) :
    s.energy (σ := σ) ξ ≤
      c.envelopeFreeCost bounds * amplitude ξ ^ ((s.allocation.keep.card + 2) * 2) *
        pairedEnergy (c.normalizedData P amplitude hpos ξ) c.parameters s.base (cal.height ξ) :=
  (c.source_bound ξ).trans_eq (c.normalized_cost_energy P amplitude hpos bounds hfactor ξ)

theorem normalized_sqrt_source_bound
    (P : ProfileNormalizationInput F ω ψ)
    (amplitude : V → ℝ) (hpos : ∀ ξ, 0 < amplitude ξ)
    (bounds : Fin s.allocation.keep.card → ℝ) (hbounds : ∀ i, 0 ≤ bounds i)
    (hfactor : ∀ ξ i, input.primeBound ξ i = amplitude ξ ^ 2 * bounds i) (ξ : V) :
    Real.sqrt (s.energy (σ := σ) ξ) ≤
      Real.sqrt (c.envelopeFreeCost bounds) * amplitude ξ ^ (s.allocation.keep.card + 2) *
        Real.sqrt (pairedEnergy (c.normalizedData P amplitude hpos ξ)
          c.parameters s.base (cal.height ξ)) := by
  apply (Real.sqrt_le_sqrt (c.normalized_source_bound P amplitude hpos bounds hfactor ξ)).trans_eq
  rw [mul_assoc, Real.sqrt_mul (c.envelopeFreeCost_nonneg bounds hbounds), pow_mul,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg (hpos ξ).le _)]
  ring

end ActualAllocatedSource.Calibration.CapacityChild

namespace ActualAllocatedSource.Calibration

/-- The actual primitive capacity producer and normalization are
composed here, with the one deletion chosen before all Fourier values. -/
theorem produce_normalized_capacity_child
    (cal : s.Calibration (σ := σ) ω ψ) (input : cal.CapacityInput)
    (P : ProfileNormalizationInput F ω ψ)
    (amplitude : V → ℝ) (hpos : ∀ ξ, 0 < amplitude ξ)
    (bounds : Fin s.allocation.keep.card → ℝ)
    (hfactor : ∀ ξ i, input.primeBound ξ i = amplitude ξ ^ 2 * bounds i)
    (rowDomain : Set (NonzeroIdeal F)) (heightDomain window : Set ℝ)
    (seminorms : Finset (ℕ × ℕ))
    (raw : ∀ ξ, RawProfileWindow rowDomain heightDomain window seminorms
      (cal.clippedData ξ) (amplitude ξ)) :
    (∀ ξ, s.energy (σ := σ) ξ = 0) ∨
      ∃ c : cal.CapacityChild input, ∀ ξ,
        InFixedProfileWindow rowDomain heightDomain window seminorms
          (c.normalizedData P amplitude hpos ξ) ∧
        s.energy (σ := σ) ξ ≤
          c.envelopeFreeCost bounds * amplitude ξ ^ ((s.allocation.keep.card + 2) * 2) *
            pairedEnergy (c.normalizedData P amplitude hpos ξ) c.parameters s.base (cal.height ξ) := by
  rcases cal.produce_capacity_child input with hzero | hchild
  · exact Or.inl hzero
  · obtain ⟨c⟩ := hchild
    exact Or.inr ⟨c, fun ξ => ⟨c.normalized_in_fixed_window P amplitude hpos
      rowDomain heightDomain window seminorms raw ξ,
      c.normalized_source_bound P amplitude hpos bounds hfactor ξ⟩⟩

end ActualAllocatedSource.Calibration

/-- The actual second allocated kernel produces normalized real children.
Its two independent original Gauss normalizers stay in the denominator;
capacity removal contributes exactly the pre-removal profile degrees. -/
theorem actual_second_pair_produces_normalized_children
    {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : A.GeneralArithmeticContext σ η hS}
    {R : ActualSecondCorrelationRows A σ H ι}
    {Ray : Type*} [CommGroup Ray] [Fintype Ray] {l : ℕ}
    (left : SecondSideFrame (V := V) C R Ray .left k)
    (right : SecondSideFrame (V := V) C R Ray .right l)
    (lc : left.source.Calibration (σ := σ) ω ψ)
    (rc : right.source.Calibration (σ := σ) ω ψ)
    (li : lc.CapacityInput) (ri : rc.CapacityInput)
    (P : ProfileNormalizationInput F ω ψ)
    (AL AR : V → ℝ) (hAL : ∀ ξ, 0 < AL ξ) (hAR : ∀ ξ, 0 < AR ξ)
    (BL : Fin left.source.allocation.keep.card → ℝ)
    (BR : Fin right.source.allocation.keep.card → ℝ)
    (hBL : ∀ i, 0 ≤ BL i) (hBR : ∀ i, 0 ≤ BR i)
    (hleft : ∀ ξ i, li.primeBound ξ i = AL ξ ^ 2 * BL i)
    (hright : ∀ ξ i, ri.primeBound ξ i = AR ξ ^ 2 * BR i)
    (rowDomain : Set (NonzeroIdeal F)) (heightDomain window : Set ℝ)
    (seminorms : Finset (ℕ × ℕ))
    (rawL : ∀ ξ, RawProfileWindow rowDomain heightDomain window seminorms (lc.clippedData ξ) (AL ξ))
    (rawR : ∀ ξ, RawProfileWindow rowDomain heightDomain window seminorms (rc.clippedData ξ) (AR ξ)) :
    (∀ ξ, Real.sqrt (left.energy ξ) * Real.sqrt (right.energy ξ) = 0) ∨
      ∃ lchild : lc.CapacityChild li, ∃ rchild : rc.CapacityChild ri, ∀ ξ,
        InFixedProfileWindow rowDomain heightDomain window seminorms
          (lchild.normalizedData P AL hAL ξ) ∧
        InFixedProfileWindow rowDomain heightDomain window seminorms
          (rchild.normalizedData P AR hAR ξ) ∧
        Real.sqrt (left.energy ξ) * Real.sqrt (right.energy ξ) ≤
          (Real.sqrt (lchild.envelopeFreeCost BL) * Real.sqrt (rchild.envelopeFreeCost BR) /
            (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale)) *
          (AL ξ ^ (left.source.allocation.keep.card + 2) *
            AR ξ ^ (right.source.allocation.keep.card + 2)) *
          (Real.sqrt (pairedEnergy (lchild.normalizedData P AL hAL ξ) lchild.parameters
              left.source.base (lc.height ξ)) *
            Real.sqrt (pairedEnergy (rchild.normalizedData P AR hAR ξ) rchild.parameters
              right.source.base (rc.height ξ))) := by
  rcases lc.produce_normalized_capacity_child li P AL hAL BL hleft
      rowDomain heightDomain window seminorms rawL with hzero | ⟨lchild, hlchild⟩
  · left
    intro ξ
    rw [left.energy_eq_div_scale, hzero ξ, zero_div, Real.sqrt_zero, zero_mul]
  rcases rc.produce_normalized_capacity_child ri P AR hAR BR hright
      rowDomain heightDomain window seminorms rawR with hzero | ⟨rchild, hrchild⟩
  · left
    intro ξ
    rw [right.energy_eq_div_scale, hzero ξ, zero_div, Real.sqrt_zero, mul_zero]
  right
  refine ⟨lchild, rchild, fun ξ => ⟨(hlchild ξ).1, (hrchild ξ).1, ?_⟩⟩
  have hALξ := hAL ξ
  have hARξ := hAR ξ
  have hl := div_le_div_of_nonneg_right
    (lchild.normalized_sqrt_source_bound P AL hAL BL hBL hleft ξ)
    (Real.sqrt_nonneg left.normalizationScale)
  have hr := div_le_div_of_nonneg_right
    (rchild.normalized_sqrt_source_bound P AR hAR BR hBR hright ξ)
    (Real.sqrt_nonneg right.normalizationScale)
  rw [left.energy_eq_div_scale, right.energy_eq_div_scale,
    Real.sqrt_div (left.source.energy_nonneg (σ := σ) ξ),
    Real.sqrt_div (right.source.energy_nonneg (σ := σ) ξ)]
  apply (mul_le_mul hl hr
    (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity)).trans_eq
  ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.CapacityChild.normalized_cost_energy
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.CapacityChild.normalized_invariants
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.produce_normalized_capacity_child
#print axioms HeckeSkeleton.Moments.EngineStep.actual_second_pair_produces_normalized_children

