import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocatedChildFamily
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.UniformLengthCapacity

/-!
# Induction invariants of the actual allocated children

A nonempty genuine ideal row forces nonnegative effective width.  A
negative width gives the empty actual row set, so that branch has zero
energy before any induction is applied.

The live slots are computed from the actual allocation.  Their number
cannot increase, their lengths sum to the new z, and the same mesh bound
holds for every Fourier profile in the family.  The last capacity removal
uses the literal MomentData.restrictSlots and preserves kappa and width.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F}
variable {ω ψ : HeckeCharacter F}

theorem actual_momentIdeal_norm_one_le (I : HeckeGeneral.Analysis.NonzeroIdeal F) :
    1 ≤ HeckeGeneral.Analysis.idealNorm F I := by
  change (1 : ℝ) ≤ (Ideal.absNorm I.val : ℝ)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (fun hz => nonZeroDivisors.coe_ne_zero I (Ideal.absNorm_eq_zero_iff.mp hz))

theorem width_nonneg_of_actual_ideal_cutoff
    (I : HeckeGeneral.Analysis.NonzeroIdeal F) (Z width : ℝ) (hZ : 1 < Z)
    (hcutoff : HeckeGeneral.Analysis.idealNorm F I ≤ Z ^ width) : 0 ≤ width := by
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  simpa only [Real.rpow_zero] using (actual_momentIdeal_norm_one_le I).trans hcutoff

theorem ActualChildRow.width_nonneg {Ih : A.Exterior} {h g : A.R} {Q : ℝ}
    (r : ActualChildRow Ih h g Q) (Z width : ℝ) (hZ : 1 < Z)
    (hcutoff : A.exteriorNorm Ih ≤ Q * Z ^ width) : 0 ≤ width :=
  width_nonneg_of_actual_ideal_cutoff r.momentIdeal Z width hZ (r.norm_le _ hcutoff)

theorem paired_width_nonneg_of_row (d : MomentData F ω ψ) (a : RealParameters)
    (Z : ℝ) (hZ : 1 < Z) (u : HeckeGeneral.Analysis.NonzeroIdeal F)
    (hu : u ∈ pairedRows d a Z) : 0 ≤ a.m + a.q := by
  have hrow := (d.rows_spec _ u).mp (Finset.mem_filter.mp hu).1
  exact width_nonneg_of_actual_ideal_cutoff u Z (a.m + a.q) hZ hrow.2

theorem pairedRows_empty_of_width_neg (d : MomentData F ω ψ) (a : RealParameters)
    (Z : ℝ) (hZ : 1 < Z) (hwidth : a.m + a.q < 0) :
    pairedRows d a Z = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨u, hu⟩
  exact (not_le_of_gt hwidth) (paired_width_nonneg_of_row d a Z hZ u hu)

theorem pairedEnergy_zero_of_width_neg (d : MomentData F ω ψ) (a : RealParameters)
    (Z t : ℝ) (hZ : 1 < Z) (hwidth : a.m + a.q < 0) :
    pairedEnergy d a Z t = 0 := by
  rw [pairedEnergy, pairedRows_empty_of_width_neg d a Z hZ hwidth, Finset.sum_empty]

theorem paired_width_nonneg_of_energy_ne_zero (d : MomentData F ω ψ) (a : RealParameters)
    (Z t : ℝ) (hZ : 1 < Z) (hne : pairedEnergy d a Z t ≠ 0) :
    0 ≤ a.m + a.q := by
  by_contra hwidth
  exact hne (pairedEnergy_zero_of_width_neg d a Z t hZ (lt_of_not_ge hwidth))

theorem actual_totalLength_nonneg (g : SlotGeometry F) : 0 ≤ g.totalLength :=
  Finset.sum_nonneg (fun i _ => (g.slots i).length_pos.le)

theorem actual_slotCount_zero_of_totalLength_zero (g : SlotGeometry F)
    (hz : g.totalLength = 0) : g.slotCount = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hk
  let i : Fin g.slotCount := ⟨0, hk⟩
  have hi : (g.slots i).length ≤ g.totalLength :=
    Finset.single_le_sum (fun j _ => (g.slots j).length_pos.le) (Finset.mem_univ i)
  rw [hz] at hi
  exact (not_le_of_gt (g.slots i).length_pos) hi

theorem actual_restriction_slot_count (d : MomentData F ω ψ)
    (keep : Finset (Fin d.geometry.slotCount)) :
    (d.restrictSlots keep).geometry.slotCount ≤ d.geometry.slotCount := by
  change keep.card ≤ d.geometry.slotCount
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_card (Finset.subset_univ keep)

theorem actual_restriction_parameters (d : MomentData F ω ψ) (a : RealParameters)
    (keep : Finset (Fin d.geometry.slotCount)) :
    (remainingParameters d a keep).κ = a.κ ∧
      (remainingParameters d a keep).m + (remainingParameters d a keep).q = a.m + a.q ∧
      (remainingParameters d a keep).z = (d.restrictSlots keep).geometry.totalLength :=
  ⟨rfl, rfl, rfl⟩

theorem actual_restriction_zero_inherited (d : MomentData F ω ψ) (a : RealParameters)
    (keep : Finset (Fin d.geometry.slotCount))
    (hz : a.z = d.geometry.totalLength) (hzero : a.z = 0) :
    (d.restrictSlots keep).geometry.slotCount = 0 ∧
      (remainingParameters d a keep).z = 0 := by
  have hcount := actual_slotCount_zero_of_totalLength_zero d.geometry (hz.symm.trans hzero)
  have hle := actual_restriction_slot_count d keep
  constructor
  · omega
  · apply le_antisymm
    · simpa only [hzero] using remainingParameters_z_le d a keep hz
    · exact remainingParameters_z_nonneg d a keep

theorem actual_restriction_mesh (d : MomentData F ω ψ)
    (keep : Finset (Fin d.geometry.slotCount)) (mesh : ℝ)
    (hmesh : d.geometry.fitsMesh mesh) :
    (d.restrictSlots keep).geometry.fitsMesh mesh :=
  d.geometry.fitsMesh_restrictSlots keep (fun i _ => hmesh i)

theorem lengthSlot_cast (d : MomentData F ω ψ) (n : ℕ)
    (hcount : d.geometry.slotCount = n) (i : Fin d.geometry.slotCount) :
    lengthSlot d n hcount (Fin.cast hcount i) = i := by
  subst n
  rfl

namespace ActualColumnAllocation

variable {k : ℕ}

/-- The parameter array depends on the actual allocation and the fixed
source length array, before the Fourier parameter is chosen. -/
def parameters (B : ActualColumnAllocation F k) (a : RealParameters) (L : Fin k → ℝ) :
    RealParameters := lengthRemainingParameters L a B.keep

theorem keep_card_le (B : ActualColumnAllocation F k) : B.keep.card ≤ k := by
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_card (Finset.subset_univ B.keep)

theorem parameters_kappa (B : ActualColumnAllocation F k) (a : RealParameters)
    (L : Fin k → ℝ) : (B.parameters a L).κ = a.κ := rfl

theorem parameters_width (B : ActualColumnAllocation F k) (a : RealParameters)
    (L : Fin k → ℝ) :
    (B.parameters a L).m + (B.parameters a L).q = a.m + a.q := rfl

theorem parameters_z_nonneg (B : ActualColumnAllocation F k) (a : RealParameters)
    (L : Fin k → ℝ) (hL : ∀ i, 0 ≤ L i) : 0 ≤ (B.parameters a L).z := by
  change 0 ≤ ∑ i ∈ B.keep, L i
  exact Finset.sum_nonneg (fun i _ => hL i)

theorem parameters_z_le (B : ActualColumnAllocation F k) (a : RealParameters)
    (L : Fin k → ℝ) (hL : ∀ i, 0 ≤ L i) (hz : a.z = ∑ i, L i) :
    (B.parameters a L).z ≤ a.z := by
  rw [hz]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B.keep)
    (fun i _ _ => hL i)

theorem zero_inherited (B : ActualColumnAllocation F k) (a : RealParameters)
    (L : Fin k → ℝ) (hL : ∀ i, 0 < L i) (hz : a.z = ∑ i, L i)
    (hzero : a.z = 0) :
    B.keep.card = 0 ∧ (B.parameters a L).z = 0 := by
  have hk : k = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hk
    let i : Fin k := ⟨0, hk⟩
    have hi : L i ≤ ∑ j, L j :=
      Finset.single_le_sum (fun j _ => (hL j).le) (Finset.mem_univ i)
    rw [← hz, hzero] at hi
    exact (not_le_of_gt (hL i)) hi
  constructor
  · have hle := B.keep_card_le
    omega
  · exact le_antisymm
      (by simpa only [hzero] using B.parameters_z_le a L (fun i => (hL i).le) hz)
      (B.parameters_z_nonneg a L (fun i => (hL i).le))

/-- Count and individual slot lengths suffice to identify the actual
child z; equality of complete prime-window profiles is unnecessary. -/
theorem geometry_z (B : ActualColumnAllocation F k) (a : RealParameters) (L : Fin k → ℝ)
    (d : MomentData F ω ψ) (hcount : d.geometry.slotCount = B.keep.card)
    (hlength : ∀ i, (d.geometry.slots (lengthSlot d B.keep.card hcount i)).length =
      L (SlotRestriction.index B.keep i)) :
    (B.parameters a L).z = d.geometry.totalLength := by
  symm
  rw [length_totalLength_eq d B.keep.card hcount
    (fun i => L (SlotRestriction.index B.keep i)) hlength]
  exact selectedSlots_sum B.keep L

theorem geometry_count_le (B : ActualColumnAllocation F k)
    (d : MomentData F ω ψ) (hcount : d.geometry.slotCount = B.keep.card) :
    d.geometry.slotCount ≤ k := by
  rw [hcount]
  exact B.keep_card_le

theorem geometry_mesh (B : ActualColumnAllocation F k) (L : Fin k → ℝ)
    (d : MomentData F ω ψ) (hcount : d.geometry.slotCount = B.keep.card)
    (hlength : ∀ i, (d.geometry.slots (lengthSlot d B.keep.card hcount i)).length =
      L (SlotRestriction.index B.keep i))
    (mesh : ℝ) (hmesh : ∀ i, L i ≤ mesh) :
    d.geometry.fitsMesh mesh := by
  intro i
  have he := hlength (Fin.cast hcount i)
  rw [lengthSlot_cast] at he
  exact he.le.trans (hmesh _)

/-- Every member of a true Fourier family inherits the same numerical
slot data, while all its prime test profiles may vary. -/
theorem family_invariants {V : Type*} (B : ActualColumnAllocation F k)
    (a : RealParameters) (L : Fin k → ℝ) (hL : ∀ i, 0 < L i)
    (hz : a.z = ∑ i, L i) (mesh : ℝ) (hmesh : ∀ i, L i ≤ mesh)
    (D : V → MomentData F ω ψ)
    (hcount : ∀ ξ, (D ξ).geometry.slotCount = B.keep.card)
    (hlength : ∀ ξ i,
      ((D ξ).geometry.slots (lengthSlot (D ξ) B.keep.card (hcount ξ) i)).length =
        L (SlotRestriction.index B.keep i)) :
    (B.parameters a L).κ = a.κ ∧
      (B.parameters a L).m + (B.parameters a L).q = a.m + a.q ∧
      0 ≤ (B.parameters a L).z ∧ (B.parameters a L).z ≤ a.z ∧
      (a.z = 0 → (B.parameters a L).z = 0) ∧
      ∀ ξ, (D ξ).geometry.slotCount ≤ k ∧
        (B.parameters a L).z = (D ξ).geometry.totalLength ∧
        (D ξ).geometry.fitsMesh mesh ∧
        (a.z = 0 → (D ξ).geometry.slotCount = 0) := by
  refine ⟨rfl, rfl, B.parameters_z_nonneg a L (fun i => (hL i).le),
    B.parameters_z_le a L (fun i => (hL i).le) hz,
    fun hzero => (B.zero_inherited a L hL hz hzero).2, ?_⟩
  intro ξ
  refine ⟨B.geometry_count_le (D ξ) (hcount ξ),
    B.geometry_z a L (D ξ) (hcount ξ) (hlength ξ),
    B.geometry_mesh L (D ξ) (hcount ξ) (hlength ξ) mesh hmesh, ?_⟩
  intro hzero
  exact (hcount ξ).trans (B.zero_inherited a L hL hz hzero).1

end ActualColumnAllocation
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.pairedEnergy_zero_of_width_neg
#print axioms HeckeSkeleton.Moments.EngineStep.ActualColumnAllocation.family_invariants
#print axioms HeckeSkeleton.Moments.EngineStep.actual_restriction_zero_inherited

