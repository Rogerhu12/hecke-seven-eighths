import HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorSource

/-!
# Total original marked mass of the first outer error source

The true first outer choices and overlap are inserted into the counting
completion of FirstErrorSource. Two independent original prime choices
expand the square of each selected original mark. The proved fixed-triple
fiber count is then paired with the divisor-row graph count.

Consequently the mass costs the three actual norm ranges q₀, e and CJ,
up to an arbitrarily small power. No bound for the number of cube pairs,
no global source mass estimate and no energy estimate is assumed.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorMass

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  DedekindZetaZeroFree.LargeSieve
open HeckeSkeleton.Moments.MOMInvStep FixedTripleFibers FixedTripleEnergy
open FirstParentEnergy FirstParentRows PositiveAssignedSource PositiveReconstruction
open FirstErrorSource CanonicalChildren
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

section Packet

variable {σ : Type*} (T : FirstParentEnergy.Data K S (σ := σ))
variable (hmask : T.mask = ∅) (I : Finset (FirstErrorSource.Index K S D T))
variable (side : Bool) (J : Finset σ) (hJ : J ⊆ T.columns.slots)
variable (hprime : ∀ j ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists j, Prime p)
variable (hweights : ∀ j ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists j,
  ‖T.columns.primeWeights j p‖ ≤ 1)
variable (slotCap : ℕ) (hcap : T.columns.slots.card ≤ slotCap)

def lists : Fin J.card → Finset (HeightOneSpectrum (𝓞 K)) :=
  PrimeChoiceSlots.lists J T.columns.primeLists (fun j hj => hprime j (hJ hj))

def packet :
    ReconstructionPacket (K := K) (Sector := Sector)
      (ActualMaskReconstruction.sectorTransport K S D Γ)
      slotCap (J.card + J.card) (0 + 0) :=
  PositiveAssignedSource.reconstructionPacket
    (lists K S T J hJ hprime) (noLists (K := K))
    (FirstErrorSource.source K S D Γ T hmask I) side (fun _ => 1) (fun _ => 1)
    (PrimeChoiceSlots.weights J T.columns.primeWeights) (fun i => Fin.elim0 i)
    (fun _ _ => by simp)
    (PrimeChoiceSlots.original_weights J T.columns.primeLists
      (fun j hj => hprime j (hJ hj)) T.columns.primeWeights
      (fun j hj => hweights j (hJ hj))) (fun i => Fin.elim0 i)
    slotCap ((Finset.card_le_card hJ).trans hcap) (Nat.zero_le _)

theorem packet_source_witness
    (t : SecondTuple K Sector (J.card + J.card) (0 + 0))
    (ht : t ∈ originalSource
      (packet K S D Γ T hmask I side J hJ hprime hweights slotCap hcap).source
      (packet K S D Γ T hmask I side J hJ hprime hweights slotCap hcap).oldLists
      (packet K S D Γ T hmask I side J hJ hprime hweights slotCap hcap).newLists
      (packet K S D Γ T hmask I side J hJ hprime hweights slotCap hcap).keep) :
    ∃ i ∈ I, t.outer = (bare K S D Γ T hmask i).outer ∧
      (secondChild (ActualMaskReconstruction.sectorTransport K S D Γ) t).2.1 =
        (bare K S D Γ T hmask i).newLabel := by
  obtain ⟨B,hB,rfl,hlive⟩ :=
    (PositiveReconstructionPacket.mem_liveTuples _ _ _ t).mp ht
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hB
  obtain ⟨i,hi,hBi⟩ := Finset.mem_image.mp q.1.property
  refine ⟨i,hi,?_,?_⟩
  · change q.1.val.outer = _
    rw [← hBi]
  · change q.1.val.newLabel = _
    rw [← hBi]

theorem packet_label_witness (f : Ideal (𝓞 K))
    (hf : f ∈ (packet K S D Γ T hmask I side J hJ hprime hweights slotCap hcap).labels) :
    ∃ i ∈ I, f = (bare K S D Γ T hmask i).newLabel := by
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hf
  obtain ⟨i,hi,ho,hl⟩ :=
    packet_source_witness K S D Γ T hmask I side J hJ hprime hweights slotCap hcap t ht
  exact ⟨i,hi,hl⟩

/-- Every summand is the actual original selected mark, with no
historical residual-column multiplicity retained in its index. -/
theorem original_mark_le_packet :
    (∑ i ∈ I,
      ‖divisorMark J T.columns.primeLists T.columns.primeWeights
        (PositiveAssignedSource.oldExtracted (bare K S D Γ T hmask i) side)‖ ^ 2) ≤
      ∑ γ ∈ (packet K S D Γ T hmask I side J hJ hprime hweights slotCap hcap).triples,
        tripleDivisorWeight slotCap γ *
          (packet K S D Γ T hmask I side J hJ hprime hweights slotCap hcap).energy
            (DivisorRowMass.test (rowSector K S D Γ)) γ := by
  have hb := PositiveAssignedSource.actual_source_energy_le_packet
    (lists K S T J hJ hprime) (noLists (K := K))
    (FirstErrorSource.source K S D Γ T hmask I) side (fun _ => 1) (fun _ => 1)
    (PrimeChoiceSlots.weights J T.columns.primeWeights) (fun i => Fin.elim0 i)
    (fun _ _ => by simp)
    (PrimeChoiceSlots.original_weights J T.columns.primeLists
      (fun j hj => hprime j (hJ hj)) T.columns.primeWeights
      (fun j hj => hweights j (hJ hj))) (fun i => Fin.elim0 i)
    slotCap ((Finset.card_le_card hJ).trans hcap) (Nat.zero_le _)
    (DivisorRowMass.test (rowSector K S D Γ))
  refine le_trans ?_ hb
  rw [FirstErrorSource.source_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [retainedZero_one K S D Γ T hmask i,
    counting_test_one K S D Γ T hmask i]
  have hnew : divisorMark Finset.univ
      (fun j => ((noLists (K := K)) j).image HeightOneSpectrum.asIdeal)
      (fun j : Fin 0 => Fin.elim0 j)
      (newExtracted (bare K S D Γ T hmask i)) = 1 := by
    simp [divisorMark]
  rw [hnew]
  simp only [lists, PrimeChoiceSlots.divisorMark_selected,
    one_mul, norm_one, one_pow, mul_one, le_refl]

end Packet

/-- The constants are fixed before the original source, its slot type,
its prime lists, all extraction and mask choices, and all three norm
windows. The only source conditions are the displayed actual ideal
norm windows and the original individual mark contractions. -/
theorem exists_original_mass_bound (slotCap : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ {σ : Type*}
      (T : FirstParentEnergy.Data K S (σ := σ)) (hmask : T.mask = ∅)
      (I : Finset (FirstErrorSource.Index K S D T)) (side : Bool)
      (J : Finset σ), J ⊆ T.columns.slots →
      (∀ j ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists j, Prime p) →
      (∀ j ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists j,
        ‖T.columns.primeWeights j p‖ ≤ 1) →
      T.columns.slots.card ≤ slotCap →
      ∀ Xq Xe Xf : ℝ, 1 ≤ Xq → 1 ≤ Xe → 1 ≤ Xf →
      (∀ i ∈ I,
        ((bare K S D Γ T hmask i).cubeQ.absNorm : ℝ) ≤ Xq ∧
        ((bare K S D Γ T hmask i).quotient.val.val.absNorm : ℝ) ≤ Xe ∧
        ((bare K S D Γ T hmask i).firstLabel.val.val.absNorm : ℝ) ≤ Xf) →
      (∑ i ∈ I,
        ‖divisorMark J T.columns.primeLists T.columns.primeWeights
          (PositiveAssignedSource.oldExtracted (bare K S D Γ T hmask i) side)‖ ^ 2) ≤
        A * (Xq * Xe) ^ (1 + ε) * Xq ^ ε * Xf ^ (1 + ε) := by
  obtain ⟨A,hA,hbound⟩ := DivisorRowMass.exists_packet_mass_bound
    (K := K) (Sector := Sector) (ActualMaskReconstruction.sectorTransport K S D Γ)
    slotCap ε hε
  refine ⟨A,hA,?_⟩
  intro σ T hmask I side J hJ hprime hweights hcap Xq Xe Xf hq he hf hnorm
  let P := packet K S D Γ T hmask I side J hJ hprime hweights slotCap hcap
  apply (original_mark_le_packet K S D Γ T hmask I side J hJ hprime hweights
    slotCap hcap).trans
  apply hbound P (rowSector K S D Γ) Xq Xe Xf hq he hf
  · intro t ht
    obtain ⟨i,hi,ho,hl⟩ :=
      packet_source_witness K S D Γ T hmask I side J hJ hprime hweights
        slotCap hcap t ht
    rw [ho, outer_eq K S D Γ T hmask i]
    exact ⟨(hnorm i hi).1,(hnorm i hi).2.1,rfl⟩
  · intro f hf
    obtain ⟨i,hi,rfl⟩ :=
      packet_label_witness K S D Γ T hmask I side J hJ hprime hweights
        slotCap hcap f hf
    rw [label_eq K S D Γ T hmask i]
    exact (hnorm i hi).2.2

/-- Summing all original slot assignments costs only the fixed slot
cap. The original signed mark is squared before its two prime choices
are counted. -/
theorem exists_all_original_mass_bound (slotCap : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ {σ : Type*}
      (T : FirstParentEnergy.Data K S (σ := σ)) (hmask : T.mask = ∅)
      (I : Finset (FirstErrorSource.Index K S D T)) (side : Bool),
      (∀ j ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists j, Prime p) →
      (∀ j ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists j,
        ‖T.columns.primeWeights j p‖ ≤ 1) →
      T.columns.slots.card ≤ slotCap →
      ∀ Xq Xe Xf : ℝ, 1 ≤ Xq → 1 ≤ Xe → 1 ≤ Xf →
      (∀ i ∈ I,
        ((bare K S D Γ T hmask i).cubeQ.absNorm : ℝ) ≤ Xq ∧
        ((bare K S D Γ T hmask i).quotient.val.val.absNorm : ℝ) ≤ Xe ∧
        ((bare K S D Γ T hmask i).firstLabel.val.val.absNorm : ℝ) ≤ Xf) →
      (∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset,
        ‖divisorMark J T.columns.primeLists T.columns.primeWeights
          (PositiveAssignedSource.oldExtracted (bare K S D Γ T hmask i) side)‖ ^ 2) ≤
        A * (Xq * Xe) ^ (1 + ε) * Xq ^ ε * Xf ^ (1 + ε) := by
  obtain ⟨A,hA,hbound⟩ := exists_original_mass_bound K S D Γ slotCap ε hε
  refine ⟨(2 : ℝ) ^ slotCap * A, mul_pos (pow_pos (by norm_num) _) hA, ?_⟩
  intro σ T hmask I side hprime hweights hcap Xq Xe Xf hq he hf hnorm
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ J ∈ T.columns.slots.powerset,
        A * (Xq * Xe) ^ (1 + ε) * Xq ^ ε * Xf ^ (1 + ε) := by
      apply Finset.sum_le_sum
      intro J hJ
      exact hbound T hmask I side J (Finset.mem_powerset.mp hJ)
        hprime hweights hcap Xq Xe Xf hq he hf hnorm
    _ = ((T.columns.slots.powerset.card : ℕ) : ℝ) *
        (A * (Xq * Xe) ^ (1 + ε) * Xq ^ ε * Xf ^ (1 + ε)) := by simp
    _ ≤ (2 : ℝ) ^ slotCap *
        (A * (Xq * Xe) ^ (1 + ε) * Xq ^ ε * Xf ^ (1 + ε)) := by
      apply mul_le_mul_of_nonneg_right
      · rw [Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat]
        exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hcap
      · positivity
    _ = _ := by ring

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorMass

end

