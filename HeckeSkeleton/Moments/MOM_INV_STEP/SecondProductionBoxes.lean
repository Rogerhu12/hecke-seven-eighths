import HeckeSkeleton.Moments.MOM_INV_STEP.SecondProductionIntegral
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualProductionBoxes
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualPacketProvenance

/-!
# Exact fixed-box decomposition of the actual integrated second source

The genuine production index is transported through its proved
arithmetic equivalence to the fixed norm partition. The integral and
every original coefficient are unchanged. The resulting source subsets
are precisely the subsets used by the automatic canonical packets.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondProductionBoxes

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers FixedTripleEnergy CanonicalChildren CanonicalNormPools FirstParentRows
  FirstToSecondData CommonKernel ActualProductionBoxes
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "OS" => Set.integer Sset K
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable {σ : Type*} [DecidableEq σ]
variable (T : FirstParentEnergy.Data K S (σ := σ))
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (hbase : 1 < T.columns.base)
variable (R : OuterIndex K S D T → {r : ℝ // 0 < r})
variable (U : {r : ℝ // 0 < r}) (J₁ : Finset σ) (s : ℝ)
variable (H₂ : ∀ o : OuterIndex K S D T, (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K)))) → Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)) → ℝ)
variable (hmask : T.mask = ∅)
local notation "X" => sourceScale K S T U
local notation "Idx" => ProductionIndex K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂
local notation "Eidx" => indexEquiv K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂
local notation "Hraw" => actualCutoff K S D T U H₂

def normBox (P : Finset Idx) (Z L : ℝ) (j : BoxIndex Z L) : Finset Idx :=
  P.filter (fun i =>
    ActualProductionBoxes.assignment K S D Γ T hmask X Hraw Z L (Eidx i) = j)

@[simp] theorem mem_normBox (P : Finset Idx) (Z L : ℝ) (j : BoxIndex Z L) (i : Idx) :
    i ∈ normBox K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask P Z L j ↔
      i ∈ P ∧ ActualProductionBoxes.assignment K S D Γ T hmask X Hraw Z L (Eidx i) = j := by
  simp only [normBox, Finset.mem_filter]

theorem image_normBox (P : Finset Idx) (Z L : ℝ) (j : BoxIndex Z L) :
    (normBox K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask P Z L j).image Eidx =
      ActualProductionBoxes.box K S D Γ T hmask X Hraw (P.image Eidx) Z L j := by
  ext k
  constructor
  · intro hk
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hi,hj⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i,hi,rfl⟩,hj⟩
  · intro hk
    obtain ⟨hk,hj⟩ := Finset.mem_filter.mp hk
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,hj⟩,rfl⟩

theorem sum_normBoxes {A : Type*} [AddCommMonoid A]
    (P : Finset Idx) (Z L : ℝ) (F : Idx → A) :
    (∑ i ∈ P, F i) =
      ∑ j : BoxIndex Z L,
        ∑ i ∈ normBox K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask P Z L j, F i := by
  simp only [normBox, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

/-- The packet source is exactly the original arithmetic box, not a
new independently chosen set of reconstruction records. -/
theorem sourceOn_normBox (P : Finset Idx) (Z L : ℝ) (j : BoxIndex Z L) :
    FirstProductionChildren.sourceOn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
      (normBox K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask P Z L j) =
    ActualPositiveIndex.source K S D Γ T hmask X Hraw
      (ActualProductionBoxes.box K S D Γ T hmask X Hraw (P.image Eidx) Z L j) := by
  unfold FirstProductionChildren.sourceOn
  rw [image_normBox]

theorem source_triple_norm_box (P : Finset Idx) (Z L ell h : ℝ) (hZ : 1 < Z)
    (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hb : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ L)
    (hfirst : 2 * T.scale.val ≤ Z ^ L) (hsecond : 4 * X ≤ Z ^ L)
    (hcube : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ (ell + h))
    (j : BoxIndex Z L)
    (B : PositiveAssignedSource.BareSource (K := K) (S := S) (D := D) (Γ := Γ)
      (N := FirstParentEnergy.columnPool K S T) («X» := X))
    (hB : B ∈ FirstProductionChildren.sourceOn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
      (normBox K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask P Z L j)) :
    (Ideal.absNorm B.outer.q0 : ℝ) ≤
        Z ^ (ell + length Z j .activeConductor / 2 - length Z j .cubeLabel + 5 * h / 2) ∧
      (Ideal.absNorm B.outer.quotient : ℝ) ≤ Z ^ (length Z j .firstOverlap + h) ∧
      (Ideal.absNorm B.outer.residual : ℝ) ≤
        Z ^ (length Z j .secondCommon - length Z j .secondDivisor + 2 * h) := by
  rw [sourceOn_normBox] at hB
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
  exact ActualProductionBoxes.triple_norm_box K S D Γ T hmask X Hraw
    (P.image Eidx) Z L ell h hZ hh hwidth hb hfirst hsecond hcube j i hi

theorem source_label_norm_bound (P : Finset Idx) (Z L h : ℝ) (hZ : 1 < Z)
    (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hb : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ L)
    (hfirst : 2 * T.scale.val ≤ Z ^ L) (hsecond : 4 * X ≤ Z ^ L)
    (j : BoxIndex Z L)
    (B : PositiveAssignedSource.BareSource (K := K) (S := S) (D := D) (Γ := Γ)
      (N := FirstParentEnergy.columnPool K S T) («X» := X))
    (hB : B ∈ FirstProductionChildren.sourceOn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
      (normBox K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask P Z L j)) :
    (Ideal.absNorm B.newLabel : ℝ) ≤
      Z ^ (length Z j .firstCommon + length Z j .secondDivisor +
        length Z j .secondOverlap + length Z j .cubeLabel + 4 * h) := by
  rw [sourceOn_normBox] at hB
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
  exact ActualProductionBoxes.newLabel_norm_bound K S D Γ T hmask X Hraw
    (P.image Eidx) Z L h hZ hh hwidth hb hfirst hsecond j i hi

/-- The exact norm-box premise of the smaller-child budget follows
from the original source pools and the actual automatic packet. -/
theorem packet_source_norm_box (P : Finset Idx) (Z L ell h : ℝ) (hZ : 1 < Z)
    (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hb : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ L)
    (hfirst : 2 * T.scale.val ≤ Z ^ L) (hsecond : 4 * X ≤ Z ^ L)
    (hcube : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ (ell + h))
    (j : BoxIndex Z L)
    (hprime : ∀ k ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists k, Prime p)
    (hweights : ∀ k ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists k,
      ‖T.columns.primeWeights k p‖ ≤ 1)
    (hJ₁ : J₁ ⊆ T.columns.slots) (J₂ : Finset σ) (hJ₂ : J₂ ⊆ T.columns.slots)
    (side : Bool) (slotCap : ℕ) (hcap : T.columns.slots.card ≤ slotCap) :
    let Q := ActualTwoPassChildren.packet K S T.columns D Γ hprime hweights
      J₁ J₂ hJ₁ hJ₂
      (FirstProductionChildren.sourceOn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
        (normBox K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask P Z L j))
      side slotCap hcap
    ∀ x ∈ originalSource Q.source Q.oldLists Q.newLists Q.keep,
      (Ideal.absNorm x.outer.q0 : ℝ) ≤
          Z ^ (ell + length Z j .activeConductor / 2 - length Z j .cubeLabel + 5 * h / 2) ∧
        (Ideal.absNorm x.outer.quotient : ℝ) ≤ Z ^ (length Z j .firstOverlap + h) ∧
        (Ideal.absNorm x.outer.residual : ℝ) ≤
          Z ^ (length Z j .secondCommon - length Z j .secondDivisor + 2 * h) := by
  intro x hx
  apply ActualPacketProvenance.source_norm_box K S T.columns D Γ hprime hweights
    J₁ J₂ hJ₁ hJ₂ _ side slotCap hcap _ _ _ ?_ x hx
  intro B hB
  exact source_triple_norm_box K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    P Z L ell h hZ hh hwidth hb hfirst hsecond hcube j B hB

theorem packet_labels_norm_bound (P : Finset Idx) (Z L h : ℝ) (hZ : 1 < Z)
    (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hb : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ L)
    (hfirst : 2 * T.scale.val ≤ Z ^ L) (hsecond : 4 * X ≤ Z ^ L)
    (j : BoxIndex Z L)
    (hprime : ∀ k ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists k, Prime p)
    (hweights : ∀ k ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists k,
      ‖T.columns.primeWeights k p‖ ≤ 1)
    (hJ₁ : J₁ ⊆ T.columns.slots) (J₂ : Finset σ) (hJ₂ : J₂ ⊆ T.columns.slots)
    (side : Bool) (slotCap : ℕ) (hcap : T.columns.slots.card ≤ slotCap) :
    let Q := ActualTwoPassChildren.packet K S T.columns D Γ hprime hweights
      J₁ J₂ hJ₁ hJ₂
      (FirstProductionChildren.sourceOn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
        (normBox K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask P Z L j))
      side slotCap hcap
    ∀ f ∈ Q.labels, (Ideal.absNorm f : ℝ) ≤
      Z ^ (length Z j .firstCommon + length Z j .secondDivisor +
        length Z j .secondOverlap + length Z j .cubeLabel + 4 * h) := by
  intro f hf
  apply ActualPacketProvenance.labels_norm_bound K S T.columns D Γ hprime hweights
    J₁ J₂ hJ₁ hJ₂ _ side slotCap hcap _ ?_ f hf
  intro B hB
  exact source_label_norm_bound K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    P Z L h hZ hh hwidth hb hfirst hsecond j B hB

variable (w : ∀ o : OuterIndex K S D T, FirstOuterCenters.Overlap K S D T o → ℝ)
variable (ε : ℝ) (side₁ : Bool)

theorem sourceIntegral_eq_normBoxes (m : ℕ) (side₂ : Bool) (P : Finset Idx)
    (b : SecondMobiusGeometry.Index X) (J₂ : Finset σ) (Z L : ℝ) :
    SecondProductionIntegral.sourceIntegral K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
      w ε side₁ m side₂ P b J₂ =
    ∑ j : BoxIndex Z L,
      SecondProductionIntegral.sourceIntegral K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
        w ε side₁ m side₂
        (normBox K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask P Z L j) b J₂ := by
  simp_rw [SecondProductionIntegral.sourceIntegral_eq_sum]
  exact sum_normBoxes K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask P Z L _

/-- The literal adaptive second total, after its original coefficients,
finite Cauchy factors and both actual spectral measures, is exactly the
sum of fixed-box canonical production integrals. -/
theorem actualTotal_eq_boxed_integrals (m : ℕ) (side₂ : Bool) (Z L : ℝ) :
    SecondProductionIntegral.actualTotal K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
      w ε side₁ m side₂ =
    SecondProductionIntegral.cauchyMass K S T J₁ s *
      ∑ b : SecondMobiusGeometry.Index X, ∑ J₂ ∈ (T.columns.slots \ J₁).powerset,
        ∑ j : BoxIndex Z L,
          SecondProductionIntegral.sourceIntegral K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
            w ε side₁ m side₂
            (normBox K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
              (SecondProductionIntegral.bin K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
                Finset.univ b) Z L j) b J₂ := by
  rw [SecondProductionIntegral.actualTotal_eq_integrals]
  apply congrArg (fun z : ℝ => SecondProductionIntegral.cauchyMass K S T J₁ s * z)
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro J₂ hJ₂
  exact sourceIntegral_eq_normBoxes K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
    hmask w ε side₁ m side₂ _ b J₂ Z L

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondProductionBoxes

end

