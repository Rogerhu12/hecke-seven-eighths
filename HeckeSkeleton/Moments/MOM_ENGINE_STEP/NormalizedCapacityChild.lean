import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondAllocatedSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocatedCapacityProvider
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedSlotRemoval

/-!
# Normalize every live profile before the single slot removal

The original allocated source and its raw term dictionary remain fixed.
The whole actual child is normalized before invoking the prime estimate.
Its exact amplitude is paid with the number of slots before removal, so
both retained and deleted profiles are counted.  The removed set depends
only on the original length ledger and precedes the Fourier parameter.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ω ψ : HeckeCharacter F} {k : ℕ}

namespace ActualAllocatedSource.Calibration

variable {s : ActualAllocatedSource A V H k} (D : s.Calibration (σ := σ) ω ψ)

structure NormalizedCapacityData where
  geometry : NominalChildGeometry
  b₂ : ℝ
  p₂ : ℝ
  boundary : ℝ
  ell : ℝ
  gap : ℝ
  δ : ℝ
  mesh : ℝ
  supportError : ℝ
  rawClipError : ℝ
  widthError : ℝ
  leftAnnulus : ℝ
  rightAnnulus : ℝ
  leftAnnulus_one : 1 ≤ leftAnnulus
  rightAnnulus_one : 1 ≤ rightAnnulus
  left_annulus : ∀ ξ, ∀ u ∈ pairedRows (D.data ξ) D.parameters s.base, ∀ x,
    (D.data ξ).plainTest₁.profile u (D.height ξ) x ≠ 0 → x ≤ leftAnnulus
  right_annulus : ∀ ξ, ∀ u ∈ pairedRows (D.data ξ) D.parameters s.base, ∀ x,
    (D.data ξ).plainTest₂.profile u (D.height ξ) x ≠ 0 → x ≤ rightAnnulus
  gap_pos : 0 < gap
  kappa_pos : 0 < D.parameters.κ
  mesh_nonneg : 0 ≤ mesh
  fits_mesh : ∀ i, s.length i ≤ mesh
  enlargement : geometry.enlargementJ + gap ≤ geometry.g
  unit_length : geometry.t₂ ≤ geometry.g₂
  actual_width : D.parameters.m + D.parameters.q ≤ geometry.nominalWidth + δ
  boundary_width : δ ≤ gap / 2
  radical_length : p₂ ≤ b₂
  boundary_nonneg : 0 ≤ boundary
  parent_capacity : s.allocation.keep.card = 0 ∨
    geometry.A + (6 * D.parameters.κ - 1) * s.beforeLength ≤ geometry.parentWidth
  common_length : geometry.g₂ - geometry.t₂ ≤ geometry.c₂
  paid_shift : s.allocation.keep.card = 0 ∨
    geometry.paidShift ≤ 6 * (geometry.w + ell) + supportError
  raw_length : D.parameters.n₁ + D.parameters.n₂ + D.parameters.z ≤
    geometry.rawDegree - s.allocatedLength + rawClipError
  width_error : geometry.nominalWidth - (D.parameters.m + D.parameters.q) ≤ widthError
  budget_nonneg : 0 ≤ 6 * (geometry.w + ell) + supportError + rawClipError + widthError
  charge_nonneg : 0 ≤ (b₂ - p₂ + geometry.w + boundary + ell) +
    (supportError + rawClipError + widthError) / 6 + D.parameters.κ * mesh
  radius : V → ℝ
  radius_pos : ∀ ξ, 0 < radius ξ
  primeBound : Fin s.allocation.keep.card → ℝ
  primeBound_nonneg : ∀ i, 0 ≤ primeBound i
  prime_bound : ∀ ξ, ∀ u ∈ pairedRows (D.data ξ) D.parameters s.base,
    ∀ i : Fin s.allocation.keep.card,
    ‖primePolynomial (normalizedMomentProfiles (D.data ξ) (radius ξ) (radius_pos ξ))
      (lengthSlot (D.data ξ) s.allocation.keep.card (D.count ξ) i) u s.base (D.height ξ)‖ ^ 2 ≤
        primeBound i * s.base ^ (D.parameters.κ * s.childLength i)

namespace NormalizedCapacityData

variable {D} (G : D.NormalizedCapacityData)

def normalizedData (ξ : V) : MomentData F ω ψ :=
  normalizedMomentProfiles (D.clippedData ξ) (G.radius ξ) (G.radius_pos ξ)

def childData (keep : Finset (Fin s.allocation.keep.card)) (ξ : V) : MomentData F ω ψ :=
  (G.normalizedData ξ).restrictSlots
    (lengthSelection (G.normalizedData ξ) s.allocation.keep.card (D.count ξ) keep)

def exponent : ℝ :=
  (G.b₂ - G.p₂ + G.geometry.w + G.boundary + G.ell) +
    (G.supportError + (G.rawClipError +
      (Real.log G.leftAnnulus + Real.log G.rightAnnulus) / Real.log s.base) +
        G.widthError) / 6 + D.parameters.κ * G.mesh

def loss (removed : Finset (Fin s.allocation.keep.card)) : ℝ :=
  (∏ i ∈ removed, G.primeBound i) * s.base ^ G.exponent

theorem loss_nonneg (removed : Finset (Fin s.allocation.keep.card)) : 0 ≤ G.loss removed :=
  mul_nonneg (Finset.prod_nonneg fun i _ => G.primeBound_nonneg i)
    (Real.rpow_nonneg (zero_lt_one.trans s.base_gt_one).le _)

structure Child where
  removed : Finset (Fin s.allocation.keep.card)
  width_nonneg : 0 ≤ D.parameters.m + D.parameters.q
  width_drop : D.parameters.m + D.parameters.q ≤ G.geometry.parentWidth - G.gap / 2
  capacity : let a := D.restrictedParameters (Finset.univ \ removed)
    a.z = 0 ∨ a.n₁ + a.n₂ + 6 * a.κ * a.z ≤ a.m + a.q
  energy : ∀ ξ, s.energy (σ := σ) ξ ≤
    (D.mass * G.loss removed) * (G.radius ξ) ^ ((s.allocation.keep.card + 2) * 2) *
      pairedEnergy (G.childData (Finset.univ \ removed) ξ)
        (D.restrictedParameters (Finset.univ \ removed)) s.base (D.height ξ)

/-- The exact full-profile factor uses the slot count before deletion.
The normalized prime estimate is applied only after the entire actual
child has been rescaled by its genuine Fourier-profile radius. -/
theorem zero_or_child : (∀ ξ, s.energy (σ := σ) ξ = 0) ∨ Nonempty G.Child := by
  by_cases hzero : ∀ ξ, s.energy (σ := σ) ξ = 0
  · exact Or.inl hzero
  right
  obtain ⟨ξ₀, hnonzero⟩ := not_forall.mp hzero
  have hE : pairedEnergy (D.data ξ₀) D.parameters s.base (D.height ξ₀) ≠ 0 := by
    intro he
    have hb := D.energy_le ξ₀
    rw [he, mul_zero] at hb
    exact hnonzero (le_antisymm hb (s.energy_nonneg (σ := σ) ξ₀))
  let clipCost := (Real.log G.leftAnnulus + Real.log G.rightAnnulus) / Real.log s.base
  have hclipCost : 0 ≤ clipCost := div_nonneg
    (add_nonneg (Real.log_nonneg G.leftAnnulus_one) (Real.log_nonneg G.rightAnnulus_one))
    (Real.log_pos s.base_gt_one).le
  have hclip := paired_clipping_budget (D.data ξ₀) D.parameters s.base (D.height ξ₀)
    G.leftAnnulus G.rightAnnulus s.base_gt_one G.leftAnnulus_one G.rightAnnulus_one
    (G.left_annulus ξ₀) (G.right_annulus ξ₀) hE
  have hclip' : D.clippedParameters.n₁ + D.clippedParameters.n₂ + D.clippedParameters.z ≤
      G.geometry.rawDegree - s.allocatedLength + (G.rawClipError + clipCost) := by
    change (clipPlainParameters D.parameters).n₁ + (clipPlainParameters D.parameters).n₂ +
      D.parameters.z ≤ _
    change (clipPlainParameters D.parameters).n₁ + (clipPlainParameters D.parameters).n₂ -
      (D.parameters.n₁ + D.parameters.n₂) ≤ clipCost at hclip
    linarith [G.raw_length]
  have hbudget' : 0 ≤ 6 * (G.geometry.w + G.ell) + G.supportError +
      (G.rawClipError + clipCost) + G.widthError := by linarith [G.budget_nonneg]
  have hcharge' : 0 ≤ (G.b₂ - G.p₂ + G.geometry.w + G.boundary + G.ell) +
      (G.supportError + (G.rawClipError + clipCost) + G.widthError) / 6 +
        D.clippedParameters.κ * G.mesh := by
    change 0 ≤ (G.b₂ - G.p₂ + G.geometry.w + G.boundary + G.ell) +
      (G.supportError + (G.rawClipError + clipCost) + G.widthError) / 6 +
        D.parameters.κ * G.mesh
    linarith [G.charge_nonneg]
  have hlength (ξ : V) (i : Fin s.allocation.keep.card) :
      ((G.normalizedData ξ).geometry.slots
        (lengthSlot (G.normalizedData ξ) s.allocation.keep.card (D.count ξ) i)).length =
          s.childLength i := D.clipped_lengths ξ i
  obtain ⟨hdrop, _, removed, hcapacity, hbound⟩ :=
    uniform_length_child_capacity_of_allocation G.normalizedData s.allocation.keep.card
      s.childLength D.count hlength D.clippedParameters G.geometry
      s.beforeLength s.allocatedLength G.b₂ G.p₂ G.boundary G.ell G.gap G.δ G.mesh
      G.supportError (G.rawClipError + clipCost) G.widthError G.gap_pos G.kappa_pos
      G.mesh_nonneg (fun i => (s.length_pos _).le) (fun i => G.fits_mesh _) D.slot_sum
      D.principal_in_theta G.enlargement G.unit_length G.actual_width G.boundary_width
      G.radical_length G.boundary_nonneg D.live_length_le D.actual_length_reduction.le
      G.parent_capacity G.common_length G.paid_shift hclip' G.width_error hbudget' hcharge'
  refine ⟨{ removed := removed,
    width_nonneg := D.clipped_width_nonneg_of_source_nonzero ξ₀ hnonzero,
    width_drop := hdrop, capacity := hcapacity, energy := ?_ }⟩
  intro ξ
  have hprime : ∀ u ∈ pairedRows (G.normalizedData ξ) D.clippedParameters s.base,
      ∀ i : Fin s.allocation.keep.card,
      ‖primePolynomial (G.normalizedData ξ)
        (lengthSlot (G.normalizedData ξ) s.allocation.keep.card (D.count ξ) i)
        u s.base (D.height ξ)‖ ^ 2 ≤
        G.primeBound i * s.base ^ (D.clippedParameters.κ * s.childLength i) :=
    G.prime_bound ξ
  have hc := hbound ξ s.base s.base_gt_one.le G.primeBound G.primeBound_nonneg
    (D.height ξ) hprime
  have hnormalized := pairedEnergy_profile_factor (D.clippedData ξ) D.clippedParameters
    (G.radius ξ) (G.radius_pos ξ) s.base (D.height ξ)
  change pairedEnergy (D.clippedData ξ) D.clippedParameters s.base (D.height ξ) =
    (G.radius ξ) ^ (((D.data ξ).geometry.slotCount + 2) * 2) *
      pairedEnergy (G.normalizedData ξ) D.clippedParameters s.base (D.height ξ) at hnormalized
  rw [D.count ξ] at hnormalized
  have hb := D.energy_le_clipped ξ
  rw [hnormalized] at hb
  have hmul := mul_le_mul_of_nonneg_left hc
    (mul_nonneg D.mass_nonneg (pow_nonneg (G.radius_pos ξ).le _))
  exact hb.trans (by
    change D.mass * ((G.radius ξ) ^ ((s.allocation.keep.card + 2) * 2) * _) ≤ _
    simpa only [clipCost, loss, exponent, childData, Calibration.restrictedParameters,
      Calibration.clippedParameters, clipPlainParameters, mul_assoc, mul_left_comm, mul_comm]
        using hmul)

namespace Child

variable {G} (out : G.Child)

def data (ξ : V) : MomentData F ω ψ := G.childData (Finset.univ \ out.removed) ξ
def parameters : RealParameters := D.restrictedParameters (Finset.univ \ out.removed)
def weight : ℝ := D.mass * G.loss out.removed

/-- The actual evaluation height is frozen into the retained profiles,
so the next moment call uses the common twist value zero. -/
def frozenData (ξ : V) : MomentData F ω ψ := frozenMomentProfiles (out.data ξ) (D.height ξ)

theorem frozen_energy (ξ : V) :
    normalizedPairedEnergy (out.frozenData ξ) out.parameters s.base 0 =
      normalizedPairedEnergy (out.data ξ) out.parameters s.base (D.height ξ) :=
  normalizedPairedEnergy_frozenMomentProfiles _ _ _ _

theorem weight_nonneg : 0 ≤ out.weight := mul_nonneg D.mass_nonneg (G.loss_nonneg _)
theorem plain_left_nonneg : 0 ≤ out.parameters.n₁ := le_max_right _ _
theorem plain_right_nonneg : 0 ≤ out.parameters.n₂ := le_max_right _ _
theorem width_eq : out.parameters.m + out.parameters.q = D.parameters.m + D.parameters.q := rfl
theorem kappa_eq : out.parameters.κ = D.parameters.κ := rfl
theorem theta_eq (ξ : V) : (out.data ξ).theta = (D.data ξ).theta := rfl
theorem frozen_theta_eq (ξ : V) : (out.frozenData ξ).theta = (D.data ξ).theta := rfl

theorem total_length (ξ : V) : out.parameters.z = (out.data ξ).geometry.totalLength :=
  (length_restrictSlots_length (G.normalizedData ξ) _ (D.count ξ) s.childLength
    (D.clipped_lengths ξ) _).symm

theorem slot_count (ξ : V) : (out.data ξ).geometry.slotCount ≤ k := by
  change (G.childData (Finset.univ \ out.removed) ξ).geometry.slotCount ≤ k
  rw [childData, length_restrictSlots_count]
  have hc : (Finset.univ \ out.removed).card ≤ s.allocation.keep.card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Finset.univ \ out.removed))
  exact hc.trans s.allocation.keep_card_le

theorem frozen_total_length (ξ : V) :
    out.parameters.z = (out.frozenData ξ).geometry.totalLength := out.total_length ξ

theorem frozen_slot_count (ξ : V) : (out.frozenData ξ).geometry.slotCount ≤ k :=
  out.slot_count ξ

theorem length_nonneg : 0 ≤ out.parameters.z :=
  D.restricted_z_nonneg (Finset.univ \ out.removed)

theorem length_le : out.parameters.z ≤ D.parameters.z :=
  D.restricted_z_le (Finset.univ \ out.removed)

theorem parameters_width_nonneg : 0 ≤ out.parameters.m + out.parameters.q := out.width_nonneg

theorem parameters_width_drop :
    out.parameters.m + out.parameters.q ≤ G.geometry.parentWidth - G.gap / 2 := out.width_drop

theorem frozen_slot_in_theta (ξ : V) (i : Fin (out.frozenData ξ).geometry.slotCount) :
    (out.frozenData ξ).slotCoefficient i ∈ (D.data ξ).theta :=
  D.restricted_slot_in_theta (Finset.univ \ out.removed) ξ i

theorem frozen_mesh (ξ : V) : (out.frozenData ξ).geometry.fitsMesh G.mesh :=
  D.restricted_mesh (Finset.univ \ out.removed) ξ G.mesh G.fits_mesh

theorem zero_length_inherited (hzero : s.beforeLength = 0) :
    out.parameters.z = 0 ∧ ∀ ξ, (out.frozenData ξ).geometry.slotCount = 0 :=
  D.restricted_zero_inherited (Finset.univ \ out.removed) hzero

/-- Admissibility uses bounds for the actual clipped profiles before
normalization and deletion.  Restriction preserves the same finite unit
ball, and freezing changes only the evaluation time. -/
theorem frozen_unit_ball (ξ : V) (orders : Finset (ℕ × ℝ))
    (hideal : ∀ q ∈ orders,
      ∀ W ∈ [(D.clippedData ξ).inverseTest, (D.clippedData ξ).plainTest₁,
        (D.clippedData ξ).plainTest₂], ∀ u,
      testSeminorm (W.profile u (D.height ξ)) q.1 q.2 ≤ G.radius ξ)
    (hprime : ∀ q ∈ orders, ∀ i,
      testSeminorm (((D.clippedData ξ).geometry.slots i).profile (D.height ξ)) q.1 q.2 ≤
        G.radius ξ) :
    MomentProfileUnitBall (out.frozenData ξ) 0 orders := by
  apply MomentProfileUnitBall.freeze_time
  exact MomentProfileUnitBall.restrictSlots (G.normalizedData ξ)
    (lengthSelection (G.normalizedData ξ) s.allocation.keep.card (D.count ξ)
      (Finset.univ \ out.removed)) (D.height ξ) orders
    (normalizedMomentProfiles_unit_ball (D.clippedData ξ) (G.radius ξ) (G.radius_pos ξ)
      (D.height ξ) orders hideal hprime)

/-- The radius exponent is the original live-profile count, not the
number of slots that survived capacity repair. -/
theorem sqrt_energy_le (ξ : V) :
    Real.sqrt (s.energy (σ := σ) ξ) ≤
      Real.sqrt out.weight * (G.radius ξ) ^ (s.allocation.keep.card + 2) *
        Real.sqrt (pairedEnergy (out.data ξ) out.parameters s.base (D.height ξ)) := by
  apply (Real.sqrt_le_sqrt (out.energy ξ)).trans_eq
  rw [Real.sqrt_mul (mul_nonneg out.weight_nonneg (pow_nonneg (G.radius_pos ξ).le _)),
    Real.sqrt_mul out.weight_nonneg, pow_mul,
    Real.sqrt_sq (pow_nonneg (G.radius_pos ξ).le _)]

end Child
end NormalizedCapacityData

end ActualAllocatedSource.Calibration
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ActualSecondCorrelationRows

variable (R : ActualSecondCorrelationRows A σ H ι)
variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]

/-- A literal left allocation of the second transformed coefficient
either vanishes for every Fourier mode or produces one actual capacity
child.  Its additional original Gauss normalization is paid exactly once. -/
theorem left_zero_or_normalized_capacity_child
    (C : A.GeneralArithmeticContext σ η hS)
    (B : ActualColumnAllocation F k) (T : FixedChildCharacters F k)
    (χ : (Ray × Ray) →* Circle)
    (D : SecondCoefficientTermDictionary T (fixedLeftPhase Ray χ)
      B.plain₁ B.plain₂ B.slots)
    (hbase : 1 < D.base) (hlength : ∀ i, 0 < D.length i)
    (IA : AllocationColumn F k → A.Exterior)
    (hIA : ∀ i ∈ childCartesianColumns B.plain₁ B.plain₂ B.slots,
      (IA i).val = allocationColumnIdeal i)
    (u v : ℂ) (t : Fin k → ℂ)
    (x₁ x₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → V)
    (x : H → Fin k → HeightOneSpectrum (𝓞 F) → V)
    (cal : (R.source C B T (fixedLeftPhase Ray χ) D hbase hlength x₁ x₂ x).Calibration
      (σ := σ) ω ψ) (G : cal.NormalizedCapacityData) :
    (∀ ξ : V, jointColumnEnergy R.rows B.columns
      (fun h => R.weight h * R.correlation h)
      (secondAllocatedLeftCoefficient Ray IA R.frequency D.ray χ
        (D.normalizedCoefficient u v t))
      (fun h => rawSourceLocation (x₁ h) (x₂ h) (x h)) ξ = 0) ∨
    ∃ out : G.Child, ∀ ξ : V,
      Real.sqrt (jointColumnEnergy R.rows B.columns
        (fun h => R.weight h * R.correlation h)
        (secondAllocatedLeftCoefficient Ray IA R.frequency D.ray χ
          (D.normalizedCoefficient u v t))
        (fun h => rawSourceLocation (x₁ h) (x₂ h) (x h)) ξ) ≤
        ‖SecondCoefficientTermDictionary.centralNormalizer u v t‖ * Real.sqrt out.weight *
          (G.radius ξ) ^ (B.keep.card + 2) * Real.sqrt (pairedEnergy (out.data ξ) out.parameters D.base (cal.height ξ)) := by
  rcases G.zero_or_child with hz | ⟨out⟩
  · left
    intro ξ
    rw [R.left_energy_eq_source Ray C B T χ D hbase hlength IA hIA u v t x₁ x₂ x ξ,
      hz ξ, mul_zero]
  · refine Or.inr ⟨out, ?_⟩
    intro ξ
    rw [R.left_energy_eq_source Ray C B T χ D hbase hlength IA hIA u v t x₁ x₂ x ξ,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (out.sqrt_energy_le ξ) (norm_nonneg _)).trans_eq
      (by ring)

/-- The right complete coefficient keeps the required star, negative
frequency and negated joint phase locations through its capacity choice. -/
theorem right_zero_or_normalized_capacity_child
    (C : A.GeneralArithmeticContext σ η hS)
    (B : ActualColumnAllocation F k) (T : FixedChildCharacters F k)
    (χ : (Ray × Ray) →* Circle)
    (D : SecondCoefficientTermDictionary T (fixedRightPhase Ray χ)
      B.plain₁ B.plain₂ B.slots)
    (hbase : 1 < D.base) (hlength : ∀ i, 0 < D.length i)
    (IB : AllocationColumn F k → A.Exterior)
    (hIB : ∀ i ∈ childCartesianColumns B.plain₁ B.plain₂ B.slots,
      (IB i).val = allocationColumnIdeal i)
    (u v : ℂ) (t : Fin k → ℂ)
    (x₁ x₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → V)
    (x : H → Fin k → HeightOneSpectrum (𝓞 F) → V)
    (cal : (R.source C B T (fixedRightPhase Ray χ) D hbase hlength x₁ x₂ x).negativeSide.Calibration
      (σ := σ) ω ψ) (G : cal.NormalizedCapacityData) :
    (∀ ξ : V, jointColumnEnergy R.rows B.columns
      (fun h => R.weight h * R.correlation h)
      (secondAllocatedRightCoefficient Ray IB R.frequency D.ray χ
        (D.normalizedCoefficient u v t))
      (fun h => rawSourceLocation (x₁ h) (x₂ h) (x h)) ξ = 0) ∨
    ∃ out : G.Child, ∀ ξ : V,
      Real.sqrt (jointColumnEnergy R.rows B.columns
        (fun h => R.weight h * R.correlation h)
        (secondAllocatedRightCoefficient Ray IB R.frequency D.ray χ
          (D.normalizedCoefficient u v t))
        (fun h => rawSourceLocation (x₁ h) (x₂ h) (x h)) ξ) ≤
        ‖SecondCoefficientTermDictionary.centralNormalizer u v t‖ * Real.sqrt out.weight *
          (G.radius ξ) ^ (B.keep.card + 2) * Real.sqrt (pairedEnergy (out.data ξ) out.parameters D.base (cal.height ξ)) := by
  rcases G.zero_or_child with hz | ⟨out⟩
  · left
    intro ξ
    rw [R.right_energy_eq_source Ray C B T χ D hbase hlength IB hIB u v t x₁ x₂ x ξ,
      hz ξ, mul_zero]
  · refine Or.inr ⟨out, ?_⟩
    intro ξ
    rw [R.right_energy_eq_source Ray C B T χ D hbase hlength IB hIB u v t x₁ x₂ x ξ,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (out.sqrt_energy_le ξ) (norm_nonneg _)).trans_eq
      (by ring)

end ActualSecondCorrelationRows

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.NormalizedCapacityData.zero_or_child
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.NormalizedCapacityData.Child.sqrt_energy_le

#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.left_zero_or_normalized_capacity_child
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.right_zero_or_normalized_capacity_child
