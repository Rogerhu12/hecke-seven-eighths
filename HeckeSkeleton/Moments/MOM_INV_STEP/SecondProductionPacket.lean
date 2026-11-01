import HeckeSkeleton.Moments.MOM_INV_STEP.SecondProductionIntegral

/-!
# Actual common spectral production enters the literal child packet

Only a numerical bound for the displayed physical scalar is used here.
The original marks, actual zero factors and finite production source
are expanded internally. Every integral is justified from the genuine
finite canonical columns. Thus the right side is the integrated smaller
canonical child energy of an explicitly constructed packet.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondProductionPacket

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers FixedTripleEnergy CanonicalChildren CanonicalNormPools FirstParentRows
  FirstToSecondData CommonKernel SecondProductionIntegral
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
local notation "X" => sourceScale K S T U
local notation "Idx" => ProductionIndex K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂
local notation "Bin" => SecondMobiusGeometry.Index X

def radialWeight (ε : ℝ) (i : Idx) : ℝ :=
  let Q := data K S D T Θ ψ G hν hG hbase R U J₁ s i.1 i.2.1
  (SecondParentProduction.radialScale K S D Γ
    (SecondAdaptiveRetained.dataAt K S D Γ Q (H₂ i.1) i.2.2.1)
    (SecondAdaptiveRetained.oldIndexAt K S D Γ Q (H₂ i.1) i.2.2.1)) ^ ε

theorem radialWeight_nonneg (ε : ℝ) (i : Idx) :
    0 ≤ radialWeight K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ ε i :=
  Real.rpow_nonneg (SecondParentProduction.radialScale_pos K S D Γ _ _).le ε

variable (w : ∀ o : OuterIndex K S D T, FirstOuterCenters.Overlap K S D T o → ℝ)
variable (ε : ℝ) (hmask : T.mask = ∅)

theorem scalar_le (P : Finset Idx) (A : ℝ)
    (hw : ∀ i ∈ P, 0 ≤ w i.1 i.2.1)
    (hphysical : ∀ i ∈ P, w i.1 i.2.1 *
      radialWeight K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ ε i *
      FirstProductionWeight.physicalCost K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask i ≤ A)
    (i : Idx) (hi : i ∈ P) :
    SecondProductionIntegral.scalar K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε i ≤
      let B := FirstToSecondData.bare K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂ hmask i
      A * ‖B.retainedZero (ActualTwoPassChildren.oldPuncture K S T.columns D Γ B)‖ := by
  let B := FirstToSecondData.bare K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂ hmask i
  let c := w i.1 i.2.1 * radialWeight K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ ε i
  have hc : 0 ≤ c := mul_nonneg (hw i hi)
    (radialWeight_nonneg K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ ε i)
  have h := mul_le_mul_of_nonneg_left
    (FirstProductionWeight.actual_weight_le K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask i) hc
  have h' : SecondProductionIntegral.scalar K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε i ≤
      (c * FirstProductionWeight.physicalCost K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask i) *
        ‖B.retainedZero (ActualTwoPassChildren.oldPuncture K S T.columns D Γ B)‖ := by
    convert h using 1 <;> dsimp only [SecondProductionIntegral.scalar, c, radialWeight] <;> ring
  exact h'.trans (mul_le_mul_of_nonneg_right (hphysical i hi) (norm_nonneg _))

variable (hprime : ∀ j ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists j, Prime p)
variable (hweights : ∀ j ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists j,
  ‖T.columns.primeWeights j p‖ ≤ 1)
variable (hJ₁ : J₁ ⊆ T.columns.slots)
variable (J₂ : Finset σ) (hJ₂ : J₂ ⊆ T.columns.slots)
variable (P : Finset (FirstToSecondData.ProductionIndex K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂)) (side₁ : Bool) (slotCap : ℕ) (hcap : T.columns.slots.card ≤ slotCap)

def packet : ReconstructionPacket (K := K) («Sector» := Sector)
    (ActualMaskReconstruction.sectorTransport K S D Γ) slotCap
      (J₁.card + J₁.card) (J₂.card + J₂.card) :=
  ActualTwoPassChildren.packet K S T.columns D Γ hprime hweights J₁ J₂ hJ₁ hJ₂
    (FirstProductionChildren.sourceOn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask P)
    side₁ slotCap hcap

def childFunction (side₂ : Bool) (b : Bin) (p : LogPlane × ℝ) : SecondChild K Sector → ℂ :=
  childValue K Sset D
    (ActualTwoPassChildren.family K S T.columns Θ ψ hν J₁ J₂
      (SecondMobiusGeometry.childScale X b) (p.2 + SecondParentProduction.coordinate side₂ p.1))
    (CanonicalSectors.sectorUnit K Sset Γ)

def packetEnergy (side₂ : Bool) (b : Bin) (p : LogPlane × ℝ) : ℝ :=
  let Q := packet K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask hprime hweights
    hJ₁ J₂ hJ₂ P side₁ slotCap hcap
  ∑ γ ∈ Q.triples, tripleDivisorWeight slotCap γ *
    Q.energy (childFunction K S D Γ T Θ ψ hν U J₁ J₂ side₂ b p) γ

theorem source_pointwise_le (m : ℕ) (side₂ : Bool) (b : Bin)
    (A : ℝ) (hA : 0 ≤ A) (hw : ∀ i ∈ P, 0 ≤ w i.1 i.2.1)
    (hphysical : ∀ i ∈ P, w i.1 i.2.1 *
      radialWeight K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ ε i *
      FirstProductionWeight.physicalCost K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask i ≤ A)
    (p : LogPlane × ℝ) :
    (∑ i ∈ P,
      SecondProductionIntegral.scalar K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε i *
        ‖firstMark K S D T J₁ side₁ i.1 i.2.1‖ ^ 2 *
        ‖secondMark K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ J₂ i‖ ^ 2 *
        ‖FirstProductionChildren.actualChildColumn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
          J₂ (SecondMobiusGeometry.childScale X b)
          (p.2 + SecondParentProduction.coordinate side₂ p.1) i‖ ^ 2) ≤
      A * packetEnergy K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask hprime hweights
        hJ₁ J₂ hJ₂ P side₁ slotCap hcap side₂ b p := by
  have hp := FirstProductionChildren.production_energy_le_children_on K S D Γ T Θ ψ G
    hν hG hbase R U J₁ s H₂ hprime hweights hJ₁ hmask P J₂ hJ₂
    (SecondMobiusGeometry.childScale X b) (p.2 + SecondParentProduction.coordinate side₂ p.1)
    side₁ slotCap hcap
  apply le_trans _ (mul_le_mul_of_nonneg_left hp hA)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hs := scalar_le K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε hmask P A hw hphysical i hi
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs
      (sq_nonneg ‖firstMark K S D T J₁ side₁ i.1 i.2.1‖))
      (sq_nonneg ‖secondMark K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ J₂ i‖))
    (sq_nonneg ‖FirstProductionChildren.actualChildColumn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
      J₂ (SecondMobiusGeometry.childScale X b) (p.2 + SecondParentProduction.coordinate side₂ p.1) i‖)
  have h1 : ‖firstMark K S D T J₁ side₁ i.1 i.2.1‖ =
      ‖divisorMark J₁ T.columns.primeLists T.columns.primeWeights
        (PositiveAssignedSource.oldExtracted
          (FirstToSecondData.bare K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂ hmask i) side₁)‖ := rfl
  have h2 : ‖secondMark K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ J₂ i‖ =
      ‖divisorMark J₂ T.columns.primeLists T.columns.primeWeights
        (PositiveAssignedSource.newExtracted
          (FirstToSecondData.bare K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂ hmask i))‖ := rfl
  refine hh.trans_eq ?_
  rw [h1, h2]
  dsimp only
  ring

include G hG hbase in
/-- Every reconstructed canonical column is jointly integrable under
the same true Fourier/Mellin density, including labels and rows absent
from an individual source fiber. -/
theorem child_joint_integrable (m : ℕ) (side₂ : Bool) (b : Bin)
    (γ : OuterTriple K) (f : Ideal (𝓞 K)) (y : Ideal (𝓞 K) × Sector) :
    Integrable (fun p : LogPlane × ℝ => jointDensity s m p *
      ‖childFunction K S D Γ T Θ ψ hν U J₁ J₂ side₂ b p (γ,f,y)‖ ^ 2)
      ((volume : Measure LogPlane).prod (volume : Measure ℝ)) := by
  let C := FirstCenteredFamily.family K S T.columns Θ ψ G hν hG J₁ U.val (-(1 / 2 : ℝ)) s
  have he (t : ℝ) : column K Sset D
      (SecondCenteredFamily.family K S C (PositiveLiteralChildren.priorTriple K γ)
        G hG J₂ (SecondMobiusGeometry.childScale X b) t)
      (CanonicalSectors.sectorUnit K Sset Γ) γ f y =
      column K Sset D (ActualTwoPassChildren.family K S T.columns Θ ψ hν J₁ J₂
        (SecondMobiusGeometry.childScale X b) t) (CanonicalSectors.sectorUnit K Sset Γ) γ f y :=
    (PositiveLiteralChildren.family_column K S D Γ C G hG J₂
      (SecondMobiusGeometry.childScale X b) t γ f y).symm.trans
      (ActualTwoPassChildren.background_cycle K S T.columns Θ ψ hν D Γ G hG
        J₁ J₂ U.val s (SecondMobiusGeometry.childScale X b) t γ f y)
  have hi := SecondMellinEnergy.joint_column_integrable K S D Γ C
    (PositiveLiteralChildren.priorTriple K γ) G hG J₂ (SecondMobiusGeometry.childScale X b)
    γ f y (mellinTest s) (mellinTest_support s) hbase
    (SecondMobiusGeometry.childScale_pos X
      (by rw [sourceScale_eq K S T hbase U]; exact U.property) b)
    (FirstCommonEnvelope.frequencyEnvelope m) (FirstCommonEnvelope.frequencyEnvelope_integrable m)
    (FirstCommonEnvelope.frequencyEnvelope_continuous m) (SecondParentProduction.coordinate side₂)
  simpa only [he, childFunction, childValue, jointDensity] using hi

theorem packetEnergy_integrable (m : ℕ) (side₂ : Bool) (b : Bin) :
    Integrable (fun p : LogPlane × ℝ => jointDensity s m p *
      packetEnergy K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask hprime hweights
        hJ₁ J₂ hJ₂ P side₁ slotCap hcap side₂ b p)
      ((volume : Measure LogPlane).prod (volume : Measure ℝ)) := by
  unfold packetEnergy ReconstructionPacket.energy childEnergy
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro γ hγ
  apply integrable_finsetSum
  intro f hf
  apply integrable_finsetSum
  intro y hy
  have hi := (child_joint_integrable K S D Γ T Θ ψ G hν hG hbase U J₁ s
    J₂ m side₂ b γ f y).const_mul
      (tripleDivisorWeight slotCap γ * labelDivisorWeight slotCap f)
  convert hi using 1
  funext p
  ring

/-- The actual second positive source inside one fixed arithmetic box
is bounded by the integrated literal packet. The only displayed bound
assumed is on its numerical physical prefactor, not on any energy. -/
theorem sourceIntegral_le_packetIntegral (m : ℕ) (side₂ : Bool) (b : Bin)
    (A : ℝ) (hA : 0 ≤ A) (hw : ∀ i ∈ P, 0 ≤ w i.1 i.2.1)
    (hphysical : ∀ i ∈ P, w i.1 i.2.1 *
      radialWeight K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ ε i *
      FirstProductionWeight.physicalCost K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask i ≤ A) :
    sourceIntegral K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε side₁ m side₂ P b J₂ ≤
      A * ∫ p : LogPlane × ℝ, jointDensity s m p *
        packetEnergy K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask hprime hweights
          hJ₁ J₂ hJ₂ P side₁ slotCap hcap side₂ b p
          ∂((volume : Measure LogPlane).prod (volume : Measure ℝ)) := by
  have hsrc : Integrable (fun p : LogPlane × ℝ => jointDensity s m p *
      ∑ i ∈ P,
        SecondProductionIntegral.scalar K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε i *
          ‖firstMark K S D T J₁ side₁ i.1 i.2.1‖ ^ 2 *
          ‖secondMark K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ J₂ i‖ ^ 2 *
          ‖FirstProductionChildren.actualChildColumn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
            J₂ (SecondMobiusGeometry.childScale X b)
            (p.2 + SecondParentProduction.coordinate side₂ p.1) i‖ ^ 2)
        ((volume : Measure LogPlane).prod (volume : Measure ℝ)) := by
    simp only [Finset.mul_sum]
    apply integrable_finsetSum
    intro i hi
    have hh := (jointColumn_integrable K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
      m side₂ b J₂ i).const_mul
      (SecondProductionIntegral.scalar K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε i *
        ‖firstMark K S D T J₁ side₁ i.1 i.2.1‖ ^ 2 *
        ‖secondMark K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ J₂ i‖ ^ 2)
    convert hh using 1
    funext p
    dsimp only [jointColumn]
    ring
  have htarget := (packetEnergy_integrable K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
    hmask hprime hweights hJ₁ J₂ hJ₂ P side₁ slotCap hcap m side₂ b).const_mul A
  have hi := integral_mono hsrc htarget (fun p => by
    have hb := mul_le_mul_of_nonneg_left
      (source_pointwise_le K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε hmask
        hprime hweights hJ₁ J₂ hJ₂ P side₁ slotCap hcap m side₂ b A hA hw hphysical p)
      (jointDensity_nonneg s m p)
    simpa only [mul_left_comm (jointDensity s m p) A] using hb)
  simpa only [integral_const_mul, sourceIntegral] using hi

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondProductionPacket

end
