import HeckeSkeleton.Moments.MOM_INV_STEP.ActualMaskReconstruction
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondMobiusGeometry
import HeckeSkeleton.Moments.MOM_INV_STEP.PrimeChoiceSlots
import HeckeSkeleton.Moments.MOM_INV_STEP.FixedTripleEnergy

/-!
# The literal one-pass inverse source and its reconstruction fibers

This source index is exactly the actual second common ideal, actual
principal-mask subset, original ideal-sector frequency, and independent
full-Moebius overlap. The unit old label and divisor remove the first
fourth-power/cube data. Original marked coefficients are expanded into
their two independent prime choices before the proved finite fiber count.

The reconstruction retains every actual mask and sector: its core
records the actual mask ideal, while its frequency records the original
sector before the two genuine divisor translations. No estimate for
reconstruction fibers or child energies is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialSource

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP
open FixedTripleFibers FixedTripleEnergy CanonicalNormPools ActualDivisorSectors
  SecondSourceColumns SecondMobiusGeometry AssignedMarkSource
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

abbrev Cutoff := Ext → Finset (HeightOneSpectrum OS) → ℝ

def unitDivisor : NonzeroRingElements OS := ⟨1, one_ne_zero⟩

theorem unitDivisor_ideal : (divisorIdeal K S (unitDivisor K S)).val.val = 1 := by
  change sIntegerModulusContraction K Sset (1 : OS) = 1
  simp [sIntegerModulusContraction, Ideal.one_eq_top]

theorem unitDivisor_norm : (sIntegerElementNorm K Sset (unitDivisor K S)).val = 1 := by
  rw [← divisorIdeal_norm, unitDivisor_ideal, map_one, Nat.cast_one]

/-- The complete one-pass production index. Its arithmetic components
are those appearing in `SecondAdaptiveProduction.totalAt`. -/
abbrev Index (X : ℝ) (H : Cutoff K S) :=
  Σ g : squarefreePool K Sset (2 * X),
    Σ delta : (SecondSourceMasks.commonMask K S D g.val).powerset,
      Σ k : FirstDualTruncation.sectorCutoff K S D Γ (H g.val delta.val),
        overlapPool K S X g.val

variable (X : ℝ) (H : Cutoff K S)
local notation "Idx" => Index K S D Γ X H

def common (i : Idx) : Ext := i.1.val

def mask (i : Idx) : Finset (HeightOneSpectrum OS) := i.2.1.val

def divisor (i : Idx) : Ext := divisorIdeal K S (sIntegerMaskGenerator K Sset (mask K S D Γ X H i))

def frequency (i : Idx) : Ext × Sector := i.2.2.1.val

def overlap (i : Idx) : Ext := overlapIdeal K S X i.1.val i.2.2.2

def residual (i : Idx) : Ext := SecondOverlapColumns.residual K S
  (common K S D Γ X H i) (divisor K S D Γ X H i)

theorem divisor_dvd_common (i : Idx) :
    (divisor K S D Γ X H i).val.val ∣ (common K S D Γ X H i).val.val :=
  SecondSourceMasks.actual_divisor_dvd K S D i.1.val
    (squarefreePool_squarefree K Sset i.1.property) i.2.1.val
    (Finset.mem_powerset.mp i.2.1.property)

theorem common_factorization (i : Idx) :
    (divisor K S D Γ X H i).val.val * (residual K S D Γ X H i).val.val =
      (common K S D Γ X H i).val.val := by
  exact congrArg (fun q : Ext => q.val.val)
    (SecondOverlapColumns.divisor_factorization K S i.1.val _
      (squarefreePool_squarefree K Sset i.1.property) (divisor_dvd_common K S D Γ X H i))

def outer (i : Idx) : OuterTriple K := ⟨1, 1, (residual K S D Γ X H i).val.val⟩

def newLabel (i : Idx) : Ideal (𝓞 K) :=
  (divisor K S D Γ X H i).val.val * (overlap K S D Γ X H i).val.val

/-- The first unit translation is the translation of the actual element
1, rather than that of an arbitrarily chosen unit-ideal generator. -/
def sectorTransport (_I J : Ideal (𝓞 K)) : Sector ≃ Sector :=
  if hj : ActualMaskReconstruction.localGenerator K S J ≠ 0 then
    (directDivisorTransport K S Γ D (unitDivisor K S)).trans
      (divisorTransport K S Γ D ⟨ActualMaskReconstruction.localGenerator K S J, hj⟩)
  else Equiv.refl _

theorem sectorTransport_actual (delta : Finset (HeightOneSpectrum OS)) (xi : Sector) :
    sectorTransport K S D Γ 1 (FirstMaskGeometry.maskIdeal K S delta) xi =
      newSector K S Γ D (unitDivisor K S) (sIntegerMaskGenerator K Sset delta) xi := by
  unfold sectorTransport
  rw [ActualMaskReconstruction.localGenerator_actual,
    dif_pos (sIntegerMaskGenerator K Sset delta).property]
  rfl

def newRow (i : Idx) : Ideal (𝓞 K) × Sector :=
  ((divisor K S D Γ X H i).val.val * (frequency K S D Γ X H i).1.val.val,
    sectorTransport K S D Γ 1 (divisor K S D Γ X H i).val.val
      (frequency K S D Γ X H i).2)

theorem newRow_actual (i : Idx) :
    newRow K S D Γ X H i =
      ((newRowIdeal K S (frequency K S D Γ X H i).1 (unitDivisor K S)
        (sIntegerMaskGenerator K Sset (mask K S D Γ X H i))).val.val,
        newSector K S Γ D (unitDivisor K S)
          (sIntegerMaskGenerator K Sset (mask K S D Γ X H i))
            (frequency K S D Γ X H i).2) := by
  apply Prod.ext
  · simp only [newRow, newRowIdeal_val, unitDivisor_ideal, one_mul, divisor]
  · exact sectorTransport_actual K S D Γ _ _

def child (i : Idx) : SecondChild K Sector :=
  (outer K S D Γ X H i, newLabel K S D Γ X H i, newRow K S D Γ X H i)

def live (i : Idx) : Prop :=
  IsCoprime (overlap K S D Γ X H i).val.val (common K S D Γ X H i).val.val

def livePool (P : Finset Idx) : Finset Idx := P.filter (live K S D Γ X H)

theorem newLabel_squarefree (i : Idx) (hi : live K S D Γ X H i) :
    Squarefree (newLabel K S D Γ X H i) := by
  have hg := squarefreePool_squarefree K Sset i.1.property
  have hd := hg.squarefree_of_dvd (divisor_dvd_common K S D Γ X H i)
  have hv := overlapIdeal_squarefree K S X i.1.val i.2.2.2
  have hcop := hi.of_isCoprime_of_dvd_right (divisor_dvd_common K S D Γ X H i)
  exact squarefree_mul_iff.mpr ⟨hcop.symm.isRelPrime, hd, hv⟩

theorem newLabel_nonzero (i : Idx) : newLabel K S D Γ X H i ≠ 0 :=
  mul_ne_zero (nonZeroDivisors.coe_ne_zero (divisor K S D Γ X H i).val)
    (nonZeroDivisors.coe_ne_zero (overlap K S D Γ X H i).val)

theorem overlapZero_eq (i : Idx) :
    ‖SecondColumnEnergy.overlapZero K S (common K S D Γ X H i)
      (FirstInversePoisson.unitIdeal K S) (overlap K S D Γ X H i)‖ =
      if live K S D Γ X H i then 1 else 0 := by
  by_cases hi : live K S D Γ X H i
  · rw [ite_eq_left hi]
    change IsCoprime (overlap K S D Γ X H i).val.val
      (common K S D Γ X H i).val.val at hi
    simp only [SecondColumnEnergy.overlapZero, FirstInversePoisson.unitIdeal_val,
      mul_one, idealCoprimeMask, ite_eq_left hi, norm_one]
  · rw [ite_eq_right hi]
    change ¬ IsCoprime (overlap K S D Γ X H i).val.val
      (common K S D Γ X H i).val.val at hi
    simp only [SecondColumnEnergy.overlapZero, FirstInversePoisson.unitIdeal_val,
      mul_one, idealCoprimeMask, ite_eq_right hi, norm_zero]

section Marks

variable {sigma : Type*} (J : Finset sigma) (lists : sigma → Finset (Ideal (𝓞 K)))
variable (hprime : ∀ j ∈ J, ∀ p ∈ lists j, Prime p)

local notation "PL" => PrimeChoiceSlots.lists J lists hprime

def choices (i : Idx) := pairedChoices PL
  ((common K S D Γ X H i).val.val * (overlap K S D Γ X H i).val.val)

abbrev Expanded (P : Finset Idx) :=
  Σ i : livePool K S D Γ X H P, choices K S D Γ X H J lists hprime i.val

/-- A literal reconstruction tuple with all unused first-pass data one. -/
def tuple (i : Idx) (q : choices K S D Γ X H J lists hprime i) :
    SecondTuple K Sector 0 (J.card + J.card) where
  outer := outer K S D Γ X H i
  core := fun j => if j = 2 then (divisor K S D Γ X H i).val.val else 1
  commonResidual := (overlap K S D Γ X H i).val.val
  cubeResidual := 1
  secondCube := 1
  extractedCommon := (common K S D Γ X H i).val.val
  frequency := ((frequency K S D Γ X H i).1.val.val, (frequency K S D Γ X H i).2)
  oldAssigned := fun j => Fin.elim0 j
  newAssigned := pairedAssignment q.val

theorem tuple_valid (i : Idx) (q : choices K S D Γ X H J lists hprime i) :
    Valid (sectorTransport K S D Γ) (tuple K S D Γ X H J lists hprime i q)
      (outer K S D Γ X H i) (newLabel K S D Γ X H i) (newRow K S D Γ X H i) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · simp [tuple, newLabel]
  · simp [tuple]
  · simp [tuple, outer, Ideal.top_pow, Ideal.top_mul]
  · simp [tuple]
  · simp [tuple]
  · simp [tuple]
  · simpa only [tuple, if_pos rfl, ite_true, outer] using common_factorization K S D Γ X H i
  · simp [tuple, newRow]
  · intro j
    exact Fin.elim0 j
  · intro j
    have hd := (pairedAssignment_source PL _ q.val q.property j).2
    have he : (common K S D Γ X H i).val.val * (overlap K S D Γ X H i).val.val =
        newLabel K S D Γ X H i * (outer K S D Γ X H i).residual := by
      rw [← common_factorization K S D Γ X H i]
      dsimp only [newLabel, outer]
      ring
    simpa only [tuple, he] using hd

theorem tuple_child (i : Idx) (q : choices K S D Γ X H J lists hprime i) :
    secondChild (sectorTransport K S D Γ) (tuple K S D Γ X H J lists hprime i q) =
      child K S D Γ X H i := by
  simp [secondChild, tuple, child, newLabel, newRow]

/-- Recover the actual sigma source from its four arithmetic components. -/
theorem index_ext (i j : Idx)
    (hg : (common K S D Γ X H i).val.val = (common K S D Γ X H j).val.val)
    (hd : (divisor K S D Γ X H i).val.val = (divisor K S D Γ X H j).val.val)
    (hk : ((frequency K S D Γ X H i).1.val.val, (frequency K S D Γ X H i).2) =
      ((frequency K S D Γ X H j).1.val.val, (frequency K S D Γ X H j).2))
    (hv : (overlap K S D Γ X H i).val.val = (overlap K S D Γ X H j).val.val) : i = j := by
  rcases i with ⟨gi, di, ki, vi⟩
  rcases j with ⟨gj, dj, kj, vj⟩
  have hg' : gi = gj := Subtype.ext (Subtype.ext (Subtype.ext hg))
  cases hg'
  have hd' : di = dj := Subtype.ext (ActualMaskReconstruction.maskIdeal_injective K S hd)
  cases hd'
  have hk' : ki = kj := by
    change (ki.val.1.val.val, ki.val.2) = (kj.val.1.val.val, kj.val.2) at hk
    have hkIdeal := congrArg (fun p : Ideal (𝓞 K) × Sector => p.1) hk
    have hkSector := congrArg (fun p : Ideal (𝓞 K) × Sector => p.2) hk
    apply Subtype.ext
    exact Prod.ext (Subtype.ext (Subtype.ext hkIdeal)) hkSector
  cases hk'
  have hv' : vi = vj := Subtype.ext hv
  cases hv'
  rfl

def expandedTuple (P : Finset Idx) (x : Expanded K S D Γ X H J lists hprime P) :=
  tuple K S D Γ X H J lists hprime x.1.val x.2

theorem expandedTuple_injective (P : Finset Idx) :
    Function.Injective (expandedTuple K S D Γ X H J lists hprime P) := by
  intro x y h
  have hi : x.1 = y.1 := by
    apply Subtype.ext
    apply index_ext K S D Γ X H
    · exact congrArg SecondTuple.extractedCommon h
    · simpa only [expandedTuple, tuple, if_pos rfl, ite_true] using
        congrArg (fun q : SecondTuple K Sector 0 (J.card + J.card) => q.core 2) h
    · exact congrArg SecondTuple.frequency h
    · exact congrArg SecondTuple.commonResidual h
  rcases x with ⟨i, q⟩
  rcases y with ⟨j, r⟩
  dsimp only at hi
  cases hi
  have hq : q = r := Subtype.ext
    (pairedAssignment_injective (congrArg SecondTuple.newAssigned h))
  cases hq
  rfl

def source (P : Finset Idx) : Finset (SecondTuple K Sector 0 (J.card + J.card)) :=
  Finset.univ.image (expandedTuple K S D Γ X H J lists hprime P)

def noLists : Fin 0 → Finset (HeightOneSpectrum (𝓞 K)) := fun j => Fin.elim0 j

def doubledLists : Fin (J.card + J.card) → Finset (HeightOneSpectrum (𝓞 K)) :=
  Fin.addCases PL PL

theorem originalSource_eq (P : Finset Idx) :
    originalSource (source K S D Γ X H J lists hprime P)
      (noLists K) (doubledLists K J lists hprime) (fun _ => True) =
        source K S D Γ X H J lists hprime P := by
  classical
  ext x
  simp only [originalSource, Finset.mem_filter]
  constructor
  · exact fun h => h.1
  intro hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
  refine ⟨Finset.mem_image.mpr ⟨q, hq, rfl⟩, fun j => Fin.elim0 j, ?_, trivial⟩
  intro j
  exact (pairedAssignment_source PL _ q.2.val q.2.property j).1

def labels (P : Finset Idx) : Finset (Ideal (𝓞 K)) :=
  (livePool K S D Γ X H P).image (newLabel K S D Γ X H)

def rows (P : Finset Idx) : Finset (Ideal (𝓞 K) × Sector) :=
  (livePool K S D Γ X H P).image (newRow K S D Γ X H)

variable (slotCap : ℕ) (hcap : J.card ≤ slotCap)

include hcap in
/-- The actual one-pass packet inherits the independently proved fiber
count, with no assumed source energy or terminal estimate. -/
def packet (P : Finset Idx) :
    ReconstructionPacket (K := K) (sectorTransport K S D Γ)
      slotCap 0 (J.card + J.card) where
  source := source K S D Γ X H J lists hprime P
  oldLists := noLists K
  newLists := doubledLists K J lists hprime
  keep := fun _ => True
  labels := labels K S D Γ X H P
  rows := rows K S D Γ X H P
  scalar := fun _ => 1
  valid := by
    intro x hx
    rw [originalSource_eq] at hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    rw [show secondChild (sectorTransport K S D Γ)
      (expandedTuple K S D Γ X H J lists hprime P q) = child K S D Γ X H q.1.val from
        tuple_child K S D Γ X H J lists hprime q.1.val q.2]
    exact tuple_valid K S D Γ X H J lists hprime q.1.val q.2
  label_squarefree := by
    intro f hf
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hf
    exact newLabel_squarefree K S D Γ X H i (Finset.mem_filter.mp hi).2
  label_nonzero := by
    intro f hf
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hf
    exact newLabel_nonzero K S D Γ X H i
  outer_nonzero := by
    intro gamma hgamma
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hgamma
    rw [originalSource_eq] at hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨one_ne_zero, one_ne_zero,
      nonZeroDivisors.coe_ne_zero (residual K S D Γ X H q.1.val).val⟩
  child_mem := by
    intro x hx
    rw [originalSource_eq] at hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    simp only [expandedTuple, tuple_child]
    exact ⟨Finset.mem_image.mpr ⟨q.1.val, q.1.property, rfl⟩,
      Finset.mem_image.mpr ⟨q.1.val, q.1.property, rfl⟩⟩
  old_cap := Nat.zero_le _
  new_cap := by simpa only [two_mul] using Nat.add_le_add hcap hcap
  scalar_norm := by intros; simp

theorem packet_triple_member (P : Finset Idx) (gamma : OuterTriple K)
    (hgamma : gamma ∈ (packet K S D Γ X H J lists hprime slotCap hcap P).triples) :
    ∃ i ∈ livePool K S D Γ X H P, outer K S D Γ X H i = gamma := by
  obtain ⟨x, hx, hxgamma⟩ := Finset.mem_image.mp hgamma
  change x ∈ originalSource (source K S D Γ X H J lists hprime P)
    (noLists K) (doubledLists K J lists hprime) (fun _ => True) at hx
  rw [originalSource_eq] at hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨q.1.val, q.1.property, hxgamma⟩

/-- The expanded actual prime choices enter the packet without losing
any mask or original sector multiplicity. -/
theorem expanded_energy_le_packet (P : Finset Idx) (F : SecondChild K Sector → ℂ) :
    (∑ x : Expanded K S D Γ X H J lists hprime P,
      ‖F (child K S D Γ X H x.1.val)‖ ^ 2) ≤
      ∑ gamma ∈ (packet K S D Γ X H J lists hprime slotCap hcap P).triples,
        tripleDivisorWeight slotCap gamma *
          (packet K S D Γ X H J lists hprime slotCap hcap P).energy F gamma := by
  let Q := packet K S D Γ X H J lists hprime slotCap hcap P
  have hp := source_energy_projection (sectorTransport K S D Γ) Q.source Q.oldLists
    Q.newLists Q.keep Q.valid Q.labels Q.rows Q.label_nonzero Q.outer_nonzero Q.child_mem
    slotCap Q.old_cap Q.new_cap (fun _ => 1) (fun _ _ => le_rfl) F
  change _ ≤ ∑ gamma ∈ Q.triples, tripleDivisorWeight slotCap gamma * Q.energy F gamma
  apply le_trans _ hp
  dsimp only [Q, packet]
  rw [originalSource_eq, source,
    Finset.sum_image (fun _ _ _ _ he => expandedTuple_injective K S D Γ X H J lists hprime P he)]
  apply Finset.sum_le_sum
  intro x hx
  rw [show secondChild (sectorTransport K S D Γ)
    (expandedTuple K S D Γ X H J lists hprime P x) = child K S D Γ X H x.1.val from
      tuple_child K S D Γ X H J lists hprime x.1.val x.2, one_mul]

/-- The actual assigned mark square is expanded with its original
individual coefficients. The overlap zero is removed only by its exact
coprimality criterion, before enlarging the squarefree label measure. -/
theorem marked_energy_le_packet (weights : sigma → Ideal (𝓞 K) → ℂ)
    (hweights : ∀ j ∈ J, ∀ p ∈ lists j, ‖weights j p‖ ≤ 1)
    (P : Finset Idx) (F : SecondChild K Sector → ℂ) :
    (∑ i ∈ P,
      ‖SecondColumnEnergy.overlapZero K S (common K S D Γ X H i)
        (FirstInversePoisson.unitIdeal K S) (overlap K S D Γ X H i)‖ *
      ‖divisorMark J lists weights
        ((common K S D Γ X H i).val.val * (overlap K S D Γ X H i).val.val)‖ ^ 2 *
      ‖F (child K S D Γ X H i)‖ ^ 2) ≤
      ∑ gamma ∈ (packet K S D Γ X H J lists hprime slotCap hcap P).triples,
        tripleDivisorWeight slotCap gamma *
          (packet K S D Γ X H J lists hprime slotCap hcap P).energy F gamma := by
  have hrestrict : (∑ i ∈ P,
      ‖SecondColumnEnergy.overlapZero K S (common K S D Γ X H i)
        (FirstInversePoisson.unitIdeal K S) (overlap K S D Γ X H i)‖ *
      ‖divisorMark J lists weights
        ((common K S D Γ X H i).val.val * (overlap K S D Γ X H i).val.val)‖ ^ 2 *
      ‖F (child K S D Γ X H i)‖ ^ 2) =
      ∑ i ∈ livePool K S D Γ X H P,
        ‖divisorMark J lists weights
          ((common K S D Γ X H i).val.val * (overlap K S D Γ X H i).val.val)‖ ^ 2 *
        ‖F (child K S D Γ X H i)‖ ^ 2 := by
    simp only [livePool, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    rw [overlapZero_eq]
    split_ifs <;> simp
  rw [hrestrict]
  apply le_trans _ (expanded_energy_le_packet K S D Γ X H J lists hprime slotCap hcap P F)
  rw [Fintype.sum_sigma, ← Finset.sum_coe_sort (livePool K S D Γ X H P)]
  apply Finset.sum_le_sum
  intro i hi
  have hm : ‖divisorMark J lists weights
      ((common K S D Γ X H i).val.val * (overlap K S D Γ X H i).val.val)‖ ^ 2 ≤
        ((choices K S D Γ X H J lists hprime i).card : ℝ) := by
    apply (PrimeChoiceSlots.actual_mark_square_le J lists hprime weights _).trans
    apply le_trans (Finset.sum_le_sum (fun q hq =>
      pairedWeight_norm_le_one PL (PrimeChoiceSlots.weights J weights) _
        (PrimeChoiceSlots.original_weights J lists hprime weights hweights) q hq))
    simp only [choices, Finset.sum_const, nsmul_eq_mul, mul_one, le_refl]
  simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe] using
    mul_le_mul_of_nonneg_right hm (sq_nonneg ‖F (child K S D Γ X H i)‖)

end Marks

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialSource

end
