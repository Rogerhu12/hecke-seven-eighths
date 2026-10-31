import HeckeSkeleton.Moments.MOM_INV_STEP.ActualTwoPassChildren

/-!
# Literal child packets from the actual two-pass production index

The left side of the production theorem is indexed by the actual first
arithmetic extraction, first overlap, fresh second common ideal, actual
second mask, original unit sector, and independent second overlap. Its
column is precisely the second centered column at those data. The right
side is a packet constructed from that finite source and the unchanged
original prime weights. No prior source-to-packet identity is assumed.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstProductionChildren

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools FirstParentRows
  FirstToSecondData PositiveAssignedSource
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
local notation "Idx" => ProductionIndex K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂

/-- This is the literal second centered column occurring inside the
actual positive second energy. The common ideal is not recomputed after
adjoining the full-Moebius overlap. -/
def actualChildColumn (J₂ : Finset σ) (U₂ t : ℝ) (i : Idx) : ℂ :=
  let Q := data K S D T Θ ψ G hν hG hbase R U J₁ s i.1 i.2.1
  let g := i.2.2.1.1.val
  let d₂ := ActualDivisorSectors.divisorIdeal K S
    (SecondAdaptiveRetained.selectedDivisorAt K S D Γ Q (H₂ i.1) i.2.2.1)
  let v := SecondMobiusGeometry.overlapIdeal K S (sourceScale K S T U) g i.2.2.2
  column K Sset D (SecondCenteredFamily.family K S Q.columns Q.triple G hG J₂ U₂ t)
    (CanonicalSectors.sectorUnit K Sset Γ)
    (SecondCenteredFamily.appendResidual K Q.triple
      (SecondOverlapColumns.residual K S g d₂).val.val)
    (SecondCompleteColumns.finalLabel K S Q.label d₂ v).val.val
    ((SecondAdaptiveRetained.selectedRowAt K S D Γ Q (H₂ i.1) i.2.2.1).val.val,
      SecondAdaptiveRetained.selectedSectorAt K S D Γ Q (H₂ i.1) i.2.2.1)

theorem actualChildColumn_eq (hmask : T.mask = ∅)
    (J₂ : Finset σ) (U₂ t : ℝ) (i : Idx) :
    actualChildColumn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ J₂ U₂ t i =
      childValue K Sset D (ActualTwoPassChildren.family K S T.columns Θ ψ hν J₁ J₂ U₂ t)
        (CanonicalSectors.sectorUnit K Sset Γ)
        ((FirstToSecondData.bare K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂ hmask i).outer,
          (FirstToSecondData.bare K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂ hmask i).newLabel,
          (FirstToSecondData.bare K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂ hmask i).newRow) := by
  change PositiveLiteralChildren.sourceColumn K S D Γ
    (FirstCenteredFamily.family K S T.columns Θ ψ G hν hG J₁ U.val (-(1 / 2 : ℝ)) s)
      G hG J₂ U₂ t
      (FirstToSecondData.bare K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂ hmask i) = _
  exact ActualTwoPassChildren.sourceColumn_eq_original K S T.columns Θ ψ hν D Γ
    G hG J₁ J₂ U.val s U₂ t _

local notation "Bare" => BareSource (K := K) (S := S) (D := D) (Γ := Γ)
  (N := FirstParentEnergy.columnPool K S T) (X := sourceScale K S T U)

def source (hmask : T.mask = ∅) : Finset Bare :=
  ActualPositiveIndex.source K S D Γ T hmask (sourceScale K S T U)
    (actualCutoff K S D T U H₂) Finset.univ

/-- Restrict the original production index to a fixed collection of
arithmetic norm boxes or center assignments, then take its exact image.
The column family is unaffected by this finite restriction. -/
def sourceOn (hmask : T.mask = ∅) (P : Finset Idx) : Finset Bare :=
  ActualPositiveIndex.source K S D Γ T hmask (sourceScale K S T U)
    (actualCutoff K S D T U H₂)
    (P.image (indexEquiv K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂))

theorem sourceOn_sum {A : Type*} [AddCommMonoid A]
    (hmask : T.mask = ∅) (P : Finset Idx) (F : Bare → A) :
    (∑ b ∈ sourceOn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask P, F b) =
      ∑ i ∈ P, F (FirstToSecondData.bare K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂ hmask i) := by
  unfold sourceOn
  rw [ActualPositiveIndex.source_sum]
  rw [Finset.sum_image (fun _ _ _ _ h =>
    (indexEquiv K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂).injective h)]
  rfl

variable (hprime : ∀ j ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists j, Prime p)
variable (hweights : ∀ j ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists j,
  ‖T.columns.primeWeights j p‖ ≤ 1)
variable (hJ₁ : J₁ ⊆ T.columns.slots)

/-- Genuine finite production, with both original marks and the exact
retained zero factor, bounded by its automatically reconstructed literal
canonical children. All row/label dependence remains in those children. -/
theorem production_energy_le_children (hmask : T.mask = ∅)
    (J₂ : Finset σ) (hJ₂ : J₂ ⊆ T.columns.slots) (U₂ t : ℝ) (side : Bool)
    (slotCap : ℕ) (hcap : T.columns.slots.card ≤ slotCap) :
    (∑ i : Idx,
      let b := FirstToSecondData.bare K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂ hmask i
      ‖b.retainedZero (ActualTwoPassChildren.oldPuncture K S T.columns D Γ b)‖ *
        ‖divisorMark J₁ T.columns.primeLists T.columns.primeWeights (oldExtracted b side)‖ ^ 2 *
        ‖divisorMark J₂ T.columns.primeLists T.columns.primeWeights (newExtracted b)‖ ^ 2 *
        ‖actualChildColumn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ J₂ U₂ t i‖ ^ 2) ≤
    let P := ActualTwoPassChildren.packet K S T.columns D Γ hprime hweights
      J₁ J₂ hJ₁ hJ₂ (source K S D Γ T U H₂ hmask) side slotCap hcap
    ∑ γ ∈ P.triples, tripleDivisorWeight slotCap γ *
      P.energy (childValue K Sset D
        (ActualTwoPassChildren.family K S T.columns Θ ψ hν J₁ J₂ U₂ t)
        (CanonicalSectors.sectorUnit K Sset Γ)) γ := by
  have hp := ActualTwoPassChildren.actual_marks_source_le_children K S T.columns Θ ψ hν
    D Γ hprime hweights J₁ J₂ hJ₁ hJ₂ G hG U.val s U₂ t
    (source K S D Γ T U H₂ hmask) side slotCap hcap
  simp_rw [ActualTwoPassChildren.sourceColumn_eq_original K S T.columns Θ ψ hν D Γ] at hp
  unfold source at hp
  rw [FirstToSecondData.production_source_sum K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂ hmask] at hp
  simpa only [actualChildColumn_eq K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask] using hp

/-- Fixed-bin production form. P restricts only the original complete
source index; it does not alter the final column coefficients, scale or
Schwartz test. The complete-source theorem above is its unfiltered case. -/
theorem production_energy_le_children_on (hmask : T.mask = ∅)
    (P : Finset Idx) (J₂ : Finset σ) (hJ₂ : J₂ ⊆ T.columns.slots)
    (U₂ t : ℝ) (side : Bool) (slotCap : ℕ) (hcap : T.columns.slots.card ≤ slotCap) :
    (∑ i ∈ P,
      let b := FirstToSecondData.bare K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂ hmask i
      ‖b.retainedZero (ActualTwoPassChildren.oldPuncture K S T.columns D Γ b)‖ *
        ‖divisorMark J₁ T.columns.primeLists T.columns.primeWeights (oldExtracted b side)‖ ^ 2 *
        ‖divisorMark J₂ T.columns.primeLists T.columns.primeWeights (newExtracted b)‖ ^ 2 *
        ‖actualChildColumn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ J₂ U₂ t i‖ ^ 2) ≤
    let P' := ActualTwoPassChildren.packet K S T.columns D Γ hprime hweights
      J₁ J₂ hJ₁ hJ₂
      (sourceOn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask P) side slotCap hcap
    ∑ γ ∈ P'.triples, tripleDivisorWeight slotCap γ *
      P'.energy (childValue K Sset D
        (ActualTwoPassChildren.family K S T.columns Θ ψ hν J₁ J₂ U₂ t)
        (CanonicalSectors.sectorUnit K Sset Γ)) γ := by
  have hp := ActualTwoPassChildren.actual_marks_source_le_children K S T.columns Θ ψ hν
    D Γ hprime hweights J₁ J₂ hJ₁ hJ₂ G hG U.val s U₂ t
    (sourceOn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask P) side slotCap hcap
  simp_rw [ActualTwoPassChildren.sourceColumn_eq_original K S T.columns Θ ψ hν D Γ] at hp
  rw [sourceOn_sum K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask P] at hp
  simpa only [actualChildColumn_eq K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask] using hp

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstProductionChildren

end
