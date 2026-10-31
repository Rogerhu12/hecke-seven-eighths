import HeckeSkeleton.Moments.MOM_INV_STEP.FirstToSecondData

/-!
# Actual two-pass columns and their original finite mark coefficients

The first background multiplication by G and the second multiplication
by its inverse cancel exactly. The resulting canonical family has the
original background and the original individual prime weights. Only
the two selected slot sets are removed. Its final center and Schwartz
test are fixed before the new row and label, and are independent of the
first Mellin frequency.

The positive packet below is constructed by enumerating the actual
original slots and their two independent prime choices. The finite
source consists of actual arithmetic records with retained zero factors.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualTwoPassChildren

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers FixedTripleEnergy CanonicalChildren CanonicalNormPools
  PositiveReconstruction PositiveAssignedSource
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
variable {σ : Type*} [DecidableEq σ]
variable (C : CanonicalBlock.ColumnData K S σ)
variable (Θ : Subgroup (HeckeCharacter K)) (ψ : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ C.background)

/-- One literal child family for the fixed pair of slot subsets, final
norm center, and final frequency. The original background is restored. -/
def family (J₁ J₂ : Finset σ) (U t : ℝ) : ColumnFamily K Sset σ Θ ψ where
  lambda := C.lambda
  background := fun _ => C.background
  background_admissible := fun _ => hν
  originalPuncture := C.puncture
  originalSlots := C.slots
  primeLists := C.primeLists
  primeWeights := C.primeWeights
  survivors := fun _ => (C.slots \ J₁) \ J₂
  survivors_subset := fun _ => Finset.sdiff_subset.trans Finset.sdiff_subset
  columns := fun _ => squarefreePool K Sset (2 * U)
  columns_squarefree := fun _ _ hn => squarefreePool_squarefree K Sset hn
  cutoff := fun _ => FinalMellinTests.weightedTest 0 t
  base := C.base
  columnLength := fun _ => Real.log U / Real.log C.base

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

theorem background_cycle (G : HeckeCharacter K) (hG : G ∈ Θ)
    (J₁ J₂ : Finset σ) (U₁ s U₂ t : ℝ) (γ : OuterTriple K)
    (f : Ideal (𝓞 K)) (y : Ideal (𝓞 K) × Sector) :
    column K Sset D
      (PositiveLiteralChildren.family K S
        (FirstCenteredFamily.family K S C Θ ψ G hν hG J₁ U₁ (-(1 / 2 : ℝ)) s)
        G hG J₂ U₂ t) (CanonicalSectors.sectorUnit K Sset Γ) γ f y =
      column K Sset D (family K S C Θ ψ hν J₁ J₂ U₂ t)
        (CanonicalSectors.sectorUnit K Sset Γ) γ f y := by
  unfold column
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [PositiveLiteralChildren.family, FirstCenteredFamily.family,
    FirstCompleteFamily.family, family]
  rw [mul_inv_cancel_right]

variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable {N : Finset Ext} {X : ℝ}
local notation "Bare" => BareSource (K := K) (S := S) (D := D) (Γ := Γ) (N := N) (X := X)

/-- The actual second complete column is a column of the restored
original family. Neither its test nor its length uses its new label. -/
theorem sourceColumn_eq_original (G : HeckeCharacter K) (hG : G ∈ Θ)
    (J₁ J₂ : Finset σ) (U₁ s U₂ t : ℝ) (B : Bare) :
    PositiveLiteralChildren.sourceColumn K S D Γ
      (FirstCenteredFamily.family K S C Θ ψ G hν hG J₁ U₁ (-(1 / 2 : ℝ)) s)
      G hG J₂ U₂ t B =
    childValue K Sset D (family K S C Θ ψ hν J₁ J₂ U₂ t)
      (CanonicalSectors.sectorUnit K Sset Γ) (B.outer,B.newLabel,B.newRow) := by
  rw [PositiveLiteralChildren.sourceColumn_eq]
  exact background_cycle K S C Θ ψ hν D Γ G hG J₁ J₂ U₁ s U₂ t
    B.outer B.newLabel B.newRow

def oldPuncture (B : Bare) : Ideal (𝓞 K) :=
  childPuncture C.puncture (PositiveLiteralChildren.priorTriple K B.outer)

variable (hprime : ∀ i ∈ C.slots, ∀ p ∈ C.primeLists i, Prime p)
variable (hweights : ∀ i ∈ C.slots, ∀ p ∈ C.primeLists i, ‖C.primeWeights i p‖ ≤ 1)
variable (J₁ J₂ : Finset σ) (hJ₁ : J₁ ⊆ C.slots) (hJ₂ : J₂ ⊆ C.slots)

def firstLists : Fin J₁.card → Finset (HeightOneSpectrum (𝓞 K)) :=
  PrimeChoiceSlots.lists J₁ C.primeLists (fun i hi => hprime i (hJ₁ hi))

def secondLists : Fin J₂.card → Finset (HeightOneSpectrum (𝓞 K)) :=
  PrimeChoiceSlots.lists J₂ C.primeLists (fun i hi => hprime i (hJ₂ hi))

/-- The packet is built from the actual original squared marks. Its
structural conditions and scalar contraction are proved internally. -/
def packet (B : Finset Bare) (side : Bool) (slotCap : ℕ) (hcap : C.slots.card ≤ slotCap) :
    ReconstructionPacket (K := K) (Sector := Sector)
      (ActualMaskReconstruction.sectorTransport K S D Γ) slotCap
      (J₁.card + J₁.card) (J₂.card + J₂.card) :=
  PositiveAssignedSource.reconstructionPacket
    (firstLists K S C hprime J₁ hJ₁) (secondLists K S C hprime J₂ hJ₂)
    B side (oldPuncture K S C D Γ) (fun _ => 1)
    (PrimeChoiceSlots.weights J₁ C.primeWeights)
    (PrimeChoiceSlots.weights J₂ C.primeWeights)
    (fun _ _ => by simp)
    (PrimeChoiceSlots.original_weights J₁ C.primeLists (fun i hi => hprime i (hJ₁ hi))
      C.primeWeights (fun i hi => hweights i (hJ₁ hi)))
    (PrimeChoiceSlots.original_weights J₂ C.primeLists (fun i hi => hprime i (hJ₂ hi))
      C.primeWeights (fun i hi => hweights i (hJ₂ hi)))
    slotCap ((Finset.card_le_card hJ₁).trans hcap) ((Finset.card_le_card hJ₂).trans hcap)

/-- Both original marks, with every original individual weight, are
carried from the actual second source into the literal child energy.
No source identity, fiber estimate, or energy bound is an input. -/
theorem actual_marks_source_le_children (G : HeckeCharacter K) (hG : G ∈ Θ)
    (U₁ s U₂ t : ℝ) (B : Finset Bare) (side : Bool)
    (slotCap : ℕ) (hcap : C.slots.card ≤ slotCap) :
    (∑ b ∈ B, ‖b.retainedZero (oldPuncture K S C D Γ b)‖ *
      ‖divisorMark J₁ C.primeLists C.primeWeights (oldExtracted b side)‖ ^ 2 *
      ‖divisorMark J₂ C.primeLists C.primeWeights (newExtracted b)‖ ^ 2 *
      ‖PositiveLiteralChildren.sourceColumn K S D Γ
        (FirstCenteredFamily.family K S C Θ ψ G hν hG J₁ U₁ (-(1 / 2 : ℝ)) s)
        G hG J₂ U₂ t b‖ ^ 2) ≤
    ∑ γ ∈ (packet K S C D Γ hprime hweights J₁ J₂ hJ₁ hJ₂ B side slotCap hcap).triples,
      tripleDivisorWeight slotCap γ *
        (packet K S C D Γ hprime hweights J₁ J₂ hJ₁ hJ₂ B side slotCap hcap).energy
          (childValue K Sset D (family K S C Θ ψ hν J₁ J₂ U₂ t)
            (CanonicalSectors.sectorUnit K Sset Γ)) γ := by
  have hb := PositiveAssignedSource.actual_source_energy_le_packet
    (firstLists K S C hprime J₁ hJ₁) (secondLists K S C hprime J₂ hJ₂)
    B side (oldPuncture K S C D Γ) (fun _ => 1)
    (PrimeChoiceSlots.weights J₁ C.primeWeights)
    (PrimeChoiceSlots.weights J₂ C.primeWeights)
    (fun _ _ => by simp)
    (PrimeChoiceSlots.original_weights J₁ C.primeLists (fun i hi => hprime i (hJ₁ hi))
      C.primeWeights (fun i hi => hweights i (hJ₁ hi)))
    (PrimeChoiceSlots.original_weights J₂ C.primeLists (fun i hi => hprime i (hJ₂ hi))
      C.primeWeights (fun i hi => hweights i (hJ₂ hi)))
    slotCap ((Finset.card_le_card hJ₁).trans hcap) ((Finset.card_le_card hJ₂).trans hcap)
    (childValue K Sset D (family K S C Θ ψ hν J₁ J₂ U₂ t)
      (CanonicalSectors.sectorUnit K Sset Γ))
  simp only [firstLists, secondLists, PrimeChoiceSlots.divisorMark_selected, one_mul] at hb
  simp_rw [sourceColumn_eq_original K S C Θ ψ hν D Γ]
  exact hb

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualTwoPassChildren

end
