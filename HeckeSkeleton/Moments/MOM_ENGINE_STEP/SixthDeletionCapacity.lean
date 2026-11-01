import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SixthDeletionGeometry

/-!
# Producing capacity data for the same complete-deletion calibration

The supplied calibration already has its actual support parameter,
including the complete second sixth-root mask.  Its original scale
window is therefore recorded at `q - r₆`, not falsely at `q`.

The internal capacity ledger increases the support coordinate `t₂` by
the literal `r₆` and decreases the half-common allowance by the same
amount.  Original prime multiplicities prove all new unit and radical
inequalities.  Parent capacity, raw degree, paid shift, slot dictionary,
profiles, calibration and Fourier parameters are preserved.

The produced `CapacityInput` and `NormalizedCapacityData` refer to the
same supplied calibration.  Their mass bridge is an explicit paid-root
identity; no old `ActualCapacityNormLengths` record with incorrect unit
or half-common fields is asserted.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open CommonSupportMass

namespace NominalChildGeometry

/-- An internal capacity ledger for the additional support factor.
The original arithmetic unit radical remains in the original geometry. -/
def sixthDeletionSkeleton (s : NominalChildGeometry) (rootLength : ℝ) :
    NominalChildGeometry :=
  { s with t₂ := s.t₂ + rootLength }

@[simp] theorem sixthDeletionSkeleton_parentWidth (s : NominalChildGeometry)
    (rootLength : ℝ) :
    (s.sixthDeletionSkeleton rootLength).parentWidth = s.parentWidth := rfl

@[simp] theorem sixthDeletionSkeleton_rawDegree (s : NominalChildGeometry)
    (rootLength : ℝ) :
    (s.sixthDeletionSkeleton rootLength).rawDegree = s.rawDegree := rfl

@[simp] theorem sixthDeletionSkeleton_enlargementJ (s : NominalChildGeometry)
    (rootLength : ℝ) :
    (s.sixthDeletionSkeleton rootLength).enlargementJ = s.enlargementJ := rfl

@[simp] theorem sixthDeletionSkeleton_paidShift (s : NominalChildGeometry)
    (rootLength : ℝ) :
    (s.sixthDeletionSkeleton rootLength).paidShift = s.paidShift := rfl

theorem sixthDeletionSkeleton_nominalWidth (s : NominalChildGeometry)
    (rootLength : ℝ) :
    (s.sixthDeletionSkeleton rootLength).nominalWidth = s.nominalWidth + rootLength := by
  dsimp only [sixthDeletionSkeleton, nominalWidth, nominalRow, nominalSupport]
  ring

end NominalChildGeometry

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {s : ActualAllocatedSource A V H k}

namespace ActualAllocatedSource.Calibration

variable (D : s.Calibration (σ := σ) ω ψ)
variable (parent : MomentData K ω ψ) (a : RealParameters) (step : ℝ)
variable (G : OriginalNominalGeometry (K := K) a s.base step)

/-- Raw identities for this already constructed complete-deletion
calibration.  The capacity constructor below fixes `rootLength` to the
actual original sixth-root ideal, rather than taking its slack as input. -/
structure OriginalSixthLengthBinding (rootLength : ℝ) where
  slots : OriginalSlotDictionary parent s.length
  parent_z : a.z = parent.geometry.totalLength
  parent_region : 3 / 4 ≤ a.κ ∧ a.κ ≤ 1 ∧
    (a.z = 0 ∨ a.n₁ + a.n₂ + 6 * a.κ * a.z ≤ a.m + a.q)
  kappa : D.parameters.κ = a.κ
  direct_slots : G.tag = .direct → k = 0
  scales : G.ScaleWindows D.parameters.m (D.parameters.q - rootLength)
  rawScaleError : ℝ
  rawScaleError_nonneg : 0 ≤ rawScaleError
  original_scale_product : s.scale₁ * s.scale₂ * s.base ^ s.beforeLength ≤
    s.base ^ (G.skeleton.rawDegree + rawScaleError)

def OriginalSixthLengthBinding.ofDomain
    {centered : Bool} {Y₁ Y₂ floor padding : ℝ}
    (domain : PairedEngineDomain centered parent a s.base Y₁ Y₂ floor padding)
    (rootLength : ℝ) (slots : OriginalSlotDictionary parent s.length)
    (kappa : D.parameters.κ = a.κ)
    (direct_slots : G.tag = .direct → k = 0)
    (scales : G.ScaleWindows D.parameters.m (D.parameters.q - rootLength))
    (rawScaleError : ℝ) (herr : 0 ≤ rawScaleError)
    (hproduct : s.scale₁ * s.scale₂ * s.base ^ s.beforeLength ≤
      s.base ^ (G.skeleton.rawDegree + rawScaleError)) :
    D.OriginalSixthLengthBinding parent a step G rootLength where
  slots := slots
  parent_z := domain.total_length
  parent_region := ⟨domain.kappa_lower, domain.kappa_upper, domain.capacity⟩
  kappa := kappa
  direct_slots := direct_slots
  scales := scales
  rawScaleError := rawScaleError
  rawScaleError_nonneg := herr
  original_scale_product := hproduct

namespace OriginalSixthLengthBinding

variable {D parent a step G} {rootLength : ℝ}
variable (B : D.OriginalSixthLengthBinding parent a step G rootLength)

include B

theorem before_length : s.beforeLength ≤ a.z := by
  rw [B.parent_z]
  exact B.slots.totalLength_le

theorem kappa_pos : 0 < D.parameters.κ := by
  rw [B.kappa]
  linarith [B.parent_region.1]

theorem parent_capacity : s.allocation.keep.card = 0 ∨
    G.skeleton.A + (6 * D.parameters.κ - 1) * s.beforeLength ≤
      G.skeleton.parentWidth := by
  rcases B.parent_region.2.2 with hz | hcap
  · left
    have hb : s.beforeLength ≤ 0 := by simpa only [hz] using B.before_length
    have hk : k = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hk
      let i : Fin k := ⟨0, hk⟩
      have hi : s.length i ≤ s.beforeLength :=
        Finset.single_le_sum (fun j _ => (s.length_pos j).le) (Finset.mem_univ i)
      exact (not_le_of_gt (s.length_pos i)) (hi.trans hb)
    have hcard := s.allocation.keep_card_le
    omega
  · right
    have hk : 0 ≤ 6 * a.κ - 1 := by linarith [B.parent_region.1]
    have hlen := mul_le_mul_of_nonneg_left B.before_length hk
    rw [B.kappa]
    change (a.n₁ + a.n₂ + a.z) + (6 * a.κ - 1) * s.beforeLength ≤ a.m + a.q
    linarith

theorem paid_shift : s.allocation.keep.card = 0 ∨
    G.skeleton.paidShift ≤
      6 * (G.skeleton.w + G.tag.poolLength step) + G.supportError := by
  by_cases hd : G.tag = .direct
  · left
    have hk := B.direct_slots hd
    have hcard := s.allocation.keep_card_le
    omega
  · exact Or.inr (G.paid_shift s.base_gt_one hd)

/-- The original product of the two plain scales and pre-allocation
slots proves the raw degree on the same calibration. -/
theorem raw_degree : D.parameters.n₁ + D.parameters.n₂ + D.parameters.z ≤
    G.skeleton.rawDegree - s.allocatedLength + B.rawScaleError := by
  have hz : 0 < s.base := zero_lt_one.trans s.base_gt_one
  have hN₁ := actual_momentIdeal_norm_one_le (s.allocation.plainDivisor 0)
  have hN₂ := actual_momentIdeal_norm_one_le (s.allocation.plainDivisor (Fin.succ 0))
  have hN₁pos := lt_of_lt_of_le zero_lt_one hN₁
  have hN₂pos := lt_of_lt_of_le zero_lt_one hN₂
  have hleft : s.base ^ D.parameters.n₁ ≤ s.scale₁ := by
    have he := (eq_div_iff hN₁pos.ne').mp D.left_scale
    calc
      _ = s.base ^ D.parameters.n₁ * 1 := (mul_one _).symm
      _ ≤ s.base ^ D.parameters.n₁ *
          HeckeGeneral.Analysis.idealNorm K (s.allocation.plainDivisor 0) :=
        mul_le_mul_of_nonneg_left hN₁ (Real.rpow_nonneg hz.le _)
      _ = _ := he
  have hright : s.base ^ D.parameters.n₂ ≤ s.scale₂ := by
    have he := (eq_div_iff hN₂pos.ne').mp D.right_scale
    calc
      _ = s.base ^ D.parameters.n₂ * 1 := (mul_one _).symm
      _ ≤ s.base ^ D.parameters.n₂ *
          HeckeGeneral.Analysis.idealNorm K (s.allocation.plainDivisor (Fin.succ 0)) :=
        mul_le_mul_of_nonneg_left hN₂ (Real.rpow_nonneg hz.le _)
      _ = _ := he
  have hp : s.base ^ (D.parameters.n₁ + D.parameters.n₂ + s.beforeLength) ≤
      s.base ^ (G.skeleton.rawDegree + B.rawScaleError) := by
    apply le_trans _ B.original_scale_product
    rw [Real.rpow_add hz, Real.rpow_add hz]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hleft hright (Real.rpow_nonneg hz.le _)
        ((Real.rpow_nonneg hz.le _).trans hleft)) (Real.rpow_nonneg hz.le _)
  have hn := (Real.rpow_le_rpow_left_iff s.base_gt_one).mp hp
  have hred := D.actual_length_reduction
  linarith

/-- Both width inequalities follow from the original q-minus-root
window and the exact internal ledger update. -/
theorem width_bounds :
    D.parameters.m + D.parameters.q ≤
        (G.skeleton.sixthDeletionSkeleton rootLength).nominalWidth + B.scales.error ∧
      (G.skeleton.sixthDeletionSkeleton rootLength).nominalWidth -
        (D.parameters.m + D.parameters.q) ≤ B.scales.error := by
  have hw := B.scales.width_bounds s.base_gt_one
  simp only [NominalChildGeometry.sixthDeletionSkeleton_nominalWidth]
  constructor <;> linarith [hw.1, hw.2]

/-- The original annuli, mesh and width errors, with no root charge
hidden inside their values. -/
def massSlack (mesh : ℝ) (atoms : D.OriginalCapacityAtoms) : ℝ :=
  G.boundary +
    (G.supportError + (B.rawScaleError +
      (Real.log atoms.leftAnnulus + Real.log atoms.rightAnnulus) / Real.log s.base) +
        B.scales.error) / 6 + D.parameters.κ * mesh + B.scales.error

end OriginalSixthLengthBinding

section ActualRoot

variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {Row ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : ActualSecondCorrelationRows A σ Row ι}
variable {C : A.GeneralArithmeticContext σ η hS} {kLeft kRight : ℕ}

namespace OriginalSixthLengthBinding

variable {D parent a step G}
variable (B : D.OriginalSixthLengthBinding parent a step G
  (idealLogLength s.base
    (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val))
variable (W : ActualSecondRowMass R C kLeft kRight)

/-- All new numerical inequalities are derived from the actual root
and the unchanged original calibration's primitive identities. -/
def capacityInput
    (hn : ∀ i, 0 < R.rightMultiplicity i) (h : R.rows)
    (hsecond : G.ideals.second.val = W.leftIdeal)
    (hopposite : G.ideals.secondOpposite.val = W.rightIdeal)
    (hunit : G.ideals.unitPart.val = W.unitIdeal.val)
    (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
    (hfit : parent.geometry.fitsMesh mesh) (atoms : D.OriginalCapacityAtoms) :
    D.CapacityInput := by
  have hslack := G.sixthDeletion_slack_of_rowMass W s.base_gt_one hn h
    hsecond hopposite hunit
  dsimp only at hslack
  exact {
    skeleton := G.skeleton.sixthDeletionSkeleton (idealLogLength s.base
      (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val)
    b₂ := G.halfSecond - idealLogLength s.base
      (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val
    p₂ := G.secondRadical
    boundary := G.boundary
    ell := G.tag.poolLength step
    gap := step
    delta := B.scales.error
    mesh := mesh
    supportError := G.supportError
    rawClipError := B.rawScaleError
    widthError := B.scales.error
    leftAnnulus := atoms.leftAnnulus
    rightAnnulus := atoms.rightAnnulus
    leftAnnulus_one := atoms.leftAnnulus_one
    rightAnnulus_one := atoms.rightAnnulus_one
    left_window := atoms.left_window
    right_window := atoms.right_window
    gap_pos := hstep
    kappa_pos := B.kappa_pos
    mesh_nonneg := hmesh
    mesh_bound := B.slots.fitsMesh hfit
    enlargement := G.enlargement_bound hstep.le
    unit_part := hslack.2.1
    actual_width := B.width_bounds.1
    delta_bound := B.scales.error_le_half_step
    principal_part := by linarith [hslack.2.2]
    boundary_nonneg := G.boundary_nonneg
    parent_capacity := B.parent_capacity
    common_part := by
      change G.skeleton.g₂ - (G.skeleton.t₂ + idealLogLength s.base
        (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val) ≤
          G.skeleton.c₂
      have hc := G.common_length s.base_gt_one
      linarith [hslack.1]
    paid_shift := B.paid_shift
    raw_degree := B.raw_degree
    width_error := B.width_bounds.2
    budget_nonneg := by
      have hw := G.tag.removedLength_nonneg s.base s.base_gt_one
      have he := G.tag.poolLength_nonneg step hstep.le
      change 0 ≤ 6 * (G.tag.removedLength s.base + G.tag.poolLength step) +
        G.supportError + B.rawScaleError + B.scales.error
      exact add_nonneg
        (add_nonneg
          (add_nonneg (mul_nonneg (by norm_num) (add_nonneg hw he))
            G.supportError_nonneg) B.rawScaleError_nonneg) B.scales.error_nonneg
    charge_nonneg := by
      have hbp : 0 ≤ (G.halfSecond - idealLogLength s.base
          (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val) -
          G.secondRadical := by linarith [hslack.2.2]
      have hw := G.tag.removedLength_nonneg s.base s.base_gt_one
      have he := G.tag.poolLength_nonneg step hstep.le
      change 0 ≤ ((G.halfSecond - idealLogLength s.base
        (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val) -
        G.secondRadical + G.tag.removedLength s.base + G.boundary + G.tag.poolLength step) +
        (G.supportError + B.rawScaleError + B.scales.error) / 6 + D.parameters.κ * mesh
      exact add_nonneg
        (add_nonneg (add_nonneg (add_nonneg (add_nonneg hbp hw) G.boundary_nonneg) he)
          (div_nonneg
            (add_nonneg (add_nonneg G.supportError_nonneg B.rawScaleError_nonneg)
              B.scales.error_nonneg) (by norm_num)))
        (mul_nonneg B.kappa_pos.le hmesh)
    primeBound := atoms.primeBound
    primeBound_nonneg := atoms.primeBound_nonneg
    prime_bound := atoms.prime_bound }

variable (hn : ∀ i, 0 < R.rightMultiplicity i) (h : R.rows)
variable (hsecond : G.ideals.second.val = W.leftIdeal)
variable (hopposite : G.ideals.secondOpposite.val = W.rightIdeal)
variable (hunit : G.ideals.unitPart.val = W.unitIdeal.val)
variable (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
variable (hfit : parent.geometry.fitsMesh mesh) (atoms : D.OriginalCapacityAtoms)

@[simp] theorem capacityInput_parentWidth :
    (B.capacityInput W hn h hsecond hopposite hunit hstep mesh hmesh hfit atoms)
      .skeleton.parentWidth = a.m + a.q := rfl

@[simp] theorem capacityInput_gap :
    (B.capacityInput W hn h hsecond hopposite hunit hstep mesh hmesh hfit atoms).gap =
      step := rfl

/-- This identity replaces the old norm-length record's unchanged
unit-coordinate assertion. -/
theorem capacityInput_nominalWidth_eq :
    (B.capacityInput W hn h hsecond hopposite hunit hstep mesh hmesh hfit atoms)
      .skeleton.nominalWidth =
      secondSixthDeletionChildWidth s.base
        (G.skeleton.A - G.skeleton.c - G.skeleton.w)
        (G.skeleton.q + G.skeleton.R + G.skeleton.E) G.skeleton.wo
        G.skeleton.Krow G.skeleton.g G.ideals.second.val G.ideals.secondOpposite.val
        G.ideals.unitPart.val G.ideals.nonunitPart.val
        (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val := by
  change (G.skeleton.sixthDeletionSkeleton (idealLogLength s.base
    (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val)).nominalWidth = _
  rw [NominalChildGeometry.sixthDeletionSkeleton_nominalWidth]
  exact G.sixthDeletionWidth_eq _

/-- The actual capacity exponent pays the root once by subtracting
its exact logarithmic norm from the original allowance. -/
theorem capacityInput_allowance_eq :
    (B.capacityInput W hn h hsecond hopposite hunit hstep mesh hmesh hfit atoms).exponent +
        (B.capacityInput W hn h hsecond hopposite hunit hstep mesh hmesh hfit atoms).delta =
      secondSixthDeletionChildAllowance s.base G.skeleton.w (B.massSlack mesh atoms)
        (G.tag.poolLength step) G.ideals.second.val G.ideals.secondOpposite.val
        (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val := by
  change ((G.halfSecond - idealLogLength s.base
      (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val) -
      G.secondRadical + G.skeleton.w + G.boundary + G.tag.poolLength step) +
      (G.supportError + (B.rawScaleError +
        (Real.log atoms.leftAnnulus + Real.log atoms.rightAnnulus) / Real.log s.base) +
          B.scales.error) / 6 + D.parameters.κ * mesh + B.scales.error = _
  unfold secondSixthDeletionChildAllowance secondCommonChildAllowance massSlack
  dsimp only [OriginalNominalGeometry.halfSecond, OriginalNominalGeometry.secondRadical]
  ring

/-- The same actual child budget returns to the original second
scalar identity after the paid-root width and allowance cancel. -/
theorem child_budget
    (child : D.CapacityChild
      (B.capacityInput W hn h hsecond hopposite hunit hstep mesh hmesh hfit atoms)) :
    child.parameters.m + child.parameters.q +
        (B.capacityInput W hn h hsecond hopposite hunit hstep mesh hmesh hfit atoms).exponent ≤
      secondCommonChildWidth s.base
        (G.skeleton.A - G.skeleton.c - G.skeleton.w)
        (G.skeleton.q + G.skeleton.R + G.skeleton.E) G.skeleton.wo
        G.skeleton.Krow G.skeleton.g G.ideals.second.val G.ideals.secondOpposite.val
        G.ideals.unitPart.val G.ideals.nonunitPart.val +
      secondCommonChildAllowance s.base G.skeleton.w (B.massSlack mesh atoms)
        (G.tag.poolLength step) G.ideals.second.val G.ideals.secondOpposite.val := by
  have hw := (B.capacityInput W hn h hsecond hopposite hunit hstep mesh hmesh hfit atoms)
    .actual_width
  have hc := child.width_eq
  change child.parameters.m + child.parameters.q = D.parameters.m + D.parameters.q at hc
  have hnw := B.capacityInput_nominalWidth_eq W hn h hsecond hopposite hunit
    hstep mesh hmesh hfit atoms
  have hal := B.capacityInput_allowance_eq W hn h hsecond hopposite hunit
    hstep mesh hmesh hfit atoms
  have htotal := secondSixthDeletion_total s.base
    (G.skeleton.A - G.skeleton.c - G.skeleton.w)
    (G.skeleton.q + G.skeleton.R + G.skeleton.E) G.skeleton.wo
    G.skeleton.w (B.massSlack mesh atoms) G.skeleton.Krow G.skeleton.g
    (G.tag.poolLength step) G.ideals.second.val G.ideals.secondOpposite.val
    G.ideals.unitPart.val G.ideals.nonunitPart.val
    (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val
  linarith

/-- The existing profile normalization acts on this same calibration
and the newly proved capacity input.  No second source is constructed. -/
def normalizedCapacityData
    (amplitude : V → ℝ) (hpos : ∀ ξ, 0 < amplitude ξ)
    (bounds : Fin s.allocation.keep.card → ℝ) (hbound : ∀ i, 0 ≤ bounds i)
    (hfactor : ∀ ξ i, atoms.primeBound ξ i = amplitude ξ ^ 2 * bounds i) :
    D.NormalizedCapacityData :=
  (B.capacityInput W hn h hsecond hopposite hunit hstep mesh hmesh hfit atoms)
    .normalized amplitude hpos bounds hbound hfactor

@[simp] theorem normalizedCapacityData_parentWidth
    (amplitude : V → ℝ) (hpos : ∀ ξ, 0 < amplitude ξ)
    (bounds : Fin s.allocation.keep.card → ℝ) (hbound : ∀ i, 0 ≤ bounds i)
    (hfactor : ∀ ξ i, atoms.primeBound ξ i = amplitude ξ ^ 2 * bounds i) :
    (B.normalizedCapacityData W hn h hsecond hopposite hunit hstep mesh hmesh hfit atoms
      amplitude hpos bounds hbound hfactor).geometry.parentWidth = a.m + a.q := rfl

@[simp] theorem normalizedCapacityData_gap
    (amplitude : V → ℝ) (hpos : ∀ ξ, 0 < amplitude ξ)
    (bounds : Fin s.allocation.keep.card → ℝ) (hbound : ∀ i, 0 ≤ bounds i)
    (hfactor : ∀ ξ i, atoms.primeBound ξ i = amplitude ξ ^ 2 * bounds i) :
    (B.normalizedCapacityData W hn h hsecond hopposite hunit hstep mesh hmesh hfit atoms
      amplitude hpos bounds hbound hfactor).gap = step := rfl

end OriginalSixthLengthBinding
end ActualRoot

end ActualAllocatedSource.Calibration
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.OriginalSixthLengthBinding.capacityInput
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.OriginalSixthLengthBinding.child_budget
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.OriginalSixthLengthBinding.normalizedCapacityData
