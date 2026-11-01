import HeckeSkeleton.Moments.MOM_INV_STEP.FirstProductionWeight

/-!
# The actual second positive production under one joint spectral measure

The powered first test depends only on the fixed first frequency. Its
Mellin density is therefore shared by every actual extraction, common
ideal, divisor, original unit sector and second overlap. The lemmas here
prove joint integrability from the literal finite canonical columns,
then move the finite production source into that common integral.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondProductionIntegral

open NumberField IsDedekindDomain MeasureTheory UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools FirstParentRows
  FirstToSecondData CommonKernel
open scoped Classical BigOperators nonZeroDivisors

def mellinTest (s : ℝ) : SchwartzMap ℝ ℂ :=
  FinalMellinTests.powerTest (WideMellinTests.weightedTest (-(1 / 2 : ℝ)) s) (-(1 / 2 : ℝ))

theorem mellinTest_support (s : ℝ) :
    tsupport (mellinTest s) ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8) :=
  (FinalMellinTests.powerTest_support _ _).trans (WideMellinTests.weightedTest_support _ _)

def jointDensity (s : ℝ) (m : ℕ) (p : LogPlane × ℝ) : ℝ :=
  FirstCommonEnvelope.frequencyEnvelope m p.1 *
    ‖SecondMellinEnergy.mellinDensity (mellinTest s) (mellinTest_support s) p.2‖

theorem jointDensity_nonneg (s : ℝ) (m : ℕ) (p : LogPlane × ℝ) :
    0 ≤ jointDensity s m p :=
  mul_nonneg (FirstCommonEnvelope.frequencyEnvelope_nonneg m p.1) (norm_nonneg _)

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

def selectedCenter (i : Idx) : Bin :=
  SecondMobiusGeometry.centerIndex K S X i.2.2.1.1.val i.2.2.2

def bin (P : Finset Idx) (b : Bin) : Finset Idx :=
  P.filter (fun i => selectedCenter K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ i = b)

theorem sum_bins {A : Type*} [AddCommMonoid A] (P : Finset Idx) (F : Bin → Idx → A) :
    (∑ i ∈ P, F (selectedCenter K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ i) i) =
      ∑ b : Bin, ∑ i ∈ bin K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ P b, F b i := by
  simp only [bin, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

def firstMark (side : Bool) (o : OuterIndex K S D T)
    (e : FirstOuterCenters.Overlap K S D T o) : ℂ :=
  FirstOverlapColumns.assignedMark K S T.columns
    (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val side
    (quotient K S D T o e) J₁

def secondMark (J₂ : Finset σ) (i : Idx) : ℂ :=
  divisorMark J₂ T.columns.primeLists T.columns.primeWeights
    (i.2.2.1.1.val.val.val * i.2.2.2.val)

def cauchyMass : ℝ :=
  (((T.columns.slots \ J₁).powerset.card : ℝ) *
    SecondMellinEnergy.mellinMass (mellinTest s) (mellinTest_support s))

def jointColumn (m : ℕ) (side : Bool) (b : Bin) (J₂ : Finset σ) (i : Idx)
    (p : LogPlane × ℝ) : ℝ :=
  jointDensity s m p *
    ‖FirstProductionChildren.actualChildColumn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
      J₂ (SecondMobiusGeometry.childScale X b) (p.2 + SecondParentProduction.coordinate side p.1) i‖ ^ 2

theorem jointColumn_integrable (m : ℕ) (side : Bool) (b : Bin) (J₂ : Finset σ) (i : Idx) :
    Integrable (jointColumn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ m side b J₂ i)
      ((volume : Measure LogPlane).prod (volume : Measure ℝ)) := by
  let Q := data K S D T Θ ψ G hν hG hbase R U J₁ s i.1 i.2.1
  let g := i.2.2.1.1.val
  let d₂ := ActualDivisorSectors.divisorIdeal K S
    (SecondAdaptiveRetained.selectedDivisorAt K S D Γ Q (H₂ i.1) i.2.2.1)
  let v := SecondMobiusGeometry.overlapIdeal K S X g i.2.2.2
  exact SecondMellinEnergy.joint_column_integrable K S D Γ Q.columns Q.triple G hG J₂
    (SecondMobiusGeometry.childScale X b)
    (SecondCenteredFamily.appendResidual K Q.triple (SecondOverlapColumns.residual K S g d₂).val.val)
    (SecondCompleteColumns.finalLabel K S Q.label d₂ v).val.val
    ((SecondAdaptiveRetained.selectedRowAt K S D Γ Q (H₂ i.1) i.2.2.1).val.val,
      SecondAdaptiveRetained.selectedSectorAt K S D Γ Q (H₂ i.1) i.2.2.1)
    (mellinTest s) (mellinTest_support s) hbase
    (SecondMobiusGeometry.childScale_pos X (SecondParentProduction.scale_pos K S Q) b)
    (FirstCommonEnvelope.frequencyEnvelope m) (FirstCommonEnvelope.frequencyEnvelope_integrable m)
    (FirstCommonEnvelope.frequencyEnvelope_continuous m) (SecondParentProduction.coordinate side)

def jointEnergy (m : ℕ) (side : Bool) (b : Bin) (J₂ : Finset σ) (i : Idx) : ℝ :=
  ∫ p : LogPlane × ℝ,
    jointColumn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ m side b J₂ i
      p ∂((volume : Measure LogPlane).prod (volume : Measure ℝ))

def columnEnergyAt (b : Bin) (J₂ : Finset σ) (i : Idx) (τ : ℝ) : ℝ :=
  ∫ t : ℝ, ‖SecondMellinEnergy.mellinDensity (mellinTest s) (mellinTest_support s) t‖ *
    ‖FirstProductionChildren.actualChildColumn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
      J₂ (SecondMobiusGeometry.childScale X b) (t + τ) i‖ ^ 2

theorem outer_column_integrable (m : ℕ) (side : Bool) (b : Bin) (J₂ : Finset σ) (i : Idx) :
    Integrable (fun ξ : LogPlane => FirstCommonEnvelope.frequencyEnvelope m ξ *
      columnEnergyAt K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ b J₂ i
        (SecondParentProduction.coordinate side ξ)) := by
  have hi := (jointColumn_integrable K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
    m side b J₂ i).integral_prod_left
  simpa only [jointColumn, jointDensity, mul_assoc, integral_const_mul, columnEnergyAt] using hi

theorem outer_column_eq_joint (m : ℕ) (side : Bool) (b : Bin) (J₂ : Finset σ) (i : Idx) :
    (∫ ξ : LogPlane, FirstCommonEnvelope.frequencyEnvelope m ξ *
      columnEnergyAt K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ b J₂ i
        (SecondParentProduction.coordinate side ξ)) =
      jointEnergy K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ m side b J₂ i := by
  unfold jointEnergy
  rw [integral_prod _ (jointColumn_integrable K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
    m side b J₂ i)]
  simp only [jointColumn, jointDensity, mul_assoc, integral_const_mul, columnEnergyAt]

def branchAt (b : Bin) (i : Idx) (τ : ℝ) : ℝ :=
  let Q := data K S D T Θ ψ G hν hG hbase R U J₁ s i.1 i.2.1
  SecondPositiveChildren.branchEnergy K S D Γ Q.columns Q.triple G hG i.2.2.1.1.val Q.label
    (ActualDivisorSectors.divisorIdeal K S
      (SecondAdaptiveRetained.selectedDivisorAt K S D Γ Q (H₂ i.1) i.2.2.1))
    (SecondAdaptiveRetained.selectedRowAt K S D Γ Q (H₂ i.1) i.2.2.1)
    (SecondAdaptiveRetained.selectedSectorAt K S D Γ Q (H₂ i.1) i.2.2.1)
    (mellinTest s) (mellinTest_support s) X b i.2.2.2 τ

theorem branchAt_eq (b : Bin) (i : Idx) (τ : ℝ) :
    branchAt K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ b i τ =
      (FirstProductionWeight.overlapZeroNorm K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ i *
        cauchyMass K S T J₁ s) *
      ∑ J₂ ∈ (T.columns.slots \ J₁).powerset,
        ‖secondMark K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ J₂ i‖ ^ 2 *
          columnEnergyAt K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ b J₂ i τ := by
  cases Subsingleton.elim ‹DecidableEq σ› (Classical.typeDecidableEq σ)
  rfl

def nodeIntegral (m : ℕ) (side : Bool) (b : Bin) (i : Idx) : ℝ :=
  ∫ ξ : LogPlane, FirstCommonEnvelope.frequencyEnvelope m ξ *
    branchAt K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ b i (SecondParentProduction.coordinate side ξ)

theorem nodeIntegral_eq (m : ℕ) (side : Bool) (b : Bin) (i : Idx) :
    nodeIntegral K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ m side b i =
      (FirstProductionWeight.overlapZeroNorm K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ i *
        cauchyMass K S T J₁ s) *
      ∑ J₂ ∈ (T.columns.slots \ J₁).powerset,
        ‖secondMark K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ J₂ i‖ ^ 2 *
          jointEnergy K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ m side b J₂ i := by
  let c := FirstProductionWeight.overlapZeroNorm K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ i *
    cauchyMass K S T J₁ s
  have he : nodeIntegral K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ m side b i =
      ∫ ξ : LogPlane, ∑ J₂ ∈ (T.columns.slots \ J₁).powerset,
        (c * ‖secondMark K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ J₂ i‖ ^ 2) *
        (FirstCommonEnvelope.frequencyEnvelope m ξ *
          columnEnergyAt K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ b J₂ i
            (SecondParentProduction.coordinate side ξ)) := by
    apply integral_congr_ae
    filter_upwards [] with ξ
    rw [branchAt_eq]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J₂ hJ₂
    dsimp only [c]
    ring
  rw [he, integral_finsetSum _ (fun J₂ _ =>
    (outer_column_integrable K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ m side b J₂ i).const_mul _)]
  simp only [integral_const_mul, outer_column_eq_joint, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J₂ hJ₂
  dsimp only [c]
  ring

variable (w : ∀ o : OuterIndex K S D T, FirstOuterCenters.Overlap K S D T o → ℝ)
variable (ε : ℝ) (side₁ : Bool)

/-- The exact scalar in the expanded positive source. Its common and
overlap zero factors are not enlarged away. -/
def scalar (i : Idx) : ℝ :=
  let Q := data K S D T Θ ψ G hν hG hbase R U J₁ s i.1 i.2.1
  w i.1 i.2.1 *
    (SecondParentProduction.radialScale K S D Γ
      (SecondAdaptiveRetained.dataAt K S D Γ Q (H₂ i.1) i.2.2.1)
      (SecondAdaptiveRetained.oldIndexAt K S D Γ Q (H₂ i.1) i.2.2.1)) ^ ε *
    SecondAdaptiveProduction.weightAt K S D Γ Q (H₂ i.1) i.2.2.1 *
    ‖(moebius i.2.2.2.val : ℂ)‖ *
    FirstProductionWeight.overlapZeroNorm K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ i

def sourceIntegral (m : ℕ) (side₂ : Bool) (P : Finset Idx) (b : Bin) (J₂ : Finset σ) : ℝ :=
  ∫ p : LogPlane × ℝ, jointDensity s m p *
    ∑ i ∈ P,
      scalar K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε i *
      ‖firstMark K S D T J₁ side₁ i.1 i.2.1‖ ^ 2 *
      ‖secondMark K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ J₂ i‖ ^ 2 *
      ‖FirstProductionChildren.actualChildColumn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
        J₂ (SecondMobiusGeometry.childScale X b)
        (p.2 + SecondParentProduction.coordinate side₂ p.1) i‖ ^ 2
      ∂((volume : Measure LogPlane).prod (volume : Measure ℝ))

/-- The finite arithmetic source is moved inside the actual common
joint spectral integral, with integrability proved from its columns. -/
theorem sourceIntegral_eq_sum (m : ℕ) (side₂ : Bool) (P : Finset Idx) (b : Bin) (J₂ : Finset σ) :
    sourceIntegral K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε side₁ m side₂ P b J₂ =
      ∑ i ∈ P,
        (scalar K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε i *
          ‖firstMark K S D T J₁ side₁ i.1 i.2.1‖ ^ 2 *
          ‖secondMark K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ J₂ i‖ ^ 2) *
        jointEnergy K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ m side₂ b J₂ i := by
  let c : Idx → ℝ := fun i => scalar K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε i *
    ‖firstMark K S D T J₁ side₁ i.1 i.2.1‖ ^ 2 *
    ‖secondMark K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ J₂ i‖ ^ 2
  have he : sourceIntegral K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε side₁ m side₂ P b J₂ =
      ∫ p : LogPlane × ℝ, ∑ i ∈ P,
        c i * jointColumn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ m side₂ b J₂ i p
          ∂((volume : Measure LogPlane).prod (volume : Measure ℝ)) := by
    apply integral_congr_ae
    filter_upwards [] with p
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [c, jointColumn]
    ring
  rw [he, integral_finsetSum _ (fun i _ =>
    (jointColumn_integrable K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ m side₂ b J₂ i).const_mul (c i))]
  simp only [integral_const_mul, jointEnergy, c]

def preScalar (i : Idx) : ℝ :=
  let Q := data K S D T Θ ψ G hν hG hbase R U J₁ s i.1 i.2.1
  w i.1 i.2.1 *
    (SecondParentProduction.radialScale K S D Γ
      (SecondAdaptiveRetained.dataAt K S D Γ Q (H₂ i.1) i.2.2.1)
      (SecondAdaptiveRetained.oldIndexAt K S D Γ Q (H₂ i.1) i.2.2.1)) ^ ε *
    SecondAdaptiveProduction.weightAt K S D Γ Q (H₂ i.1) i.2.2.1 *
    ‖(moebius i.2.2.2.val : ℂ)‖

def selectedTotalOn (m : ℕ) (side₂ : Bool) (P : Finset Idx) : ℝ :=
  ∑ i ∈ P, preScalar K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε i *
    ‖firstMark K S D T J₁ side₁ i.1 i.2.1‖ ^ 2 *
    nodeIntegral K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ m side₂
      (selectedCenter K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ i) i

/-- The original totalAt, with an arbitrary frozen first arithmetic
weight and the actual old assigned mark. No second source is supplied
in place of this quantity. -/
def actualTotal (m : ℕ) (side₂ : Bool) : ℝ :=
  ∑ o : OuterIndex K S D T, ∑ e : FirstOuterCenters.Overlap K S D T o,
    w o e * ‖firstMark K S D T J₁ side₁ o e‖ ^ 2 *
      SecondAdaptiveProduction.totalAt K S D Γ
        (data K S D T Θ ψ G hν hG hbase R U J₁ s o e) (H₂ o) G hG ε m side₂

theorem actualTotal_eq_selected (m : ℕ) (side₂ : Bool) :
    actualTotal K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε side₁ m side₂ =
      selectedTotalOn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε side₁ m side₂
        Finset.univ := by
  unfold actualTotal selectedTotalOn
  conv_rhs => rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro o ho
  conv_rhs => rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro e he
  unfold SecondAdaptiveProduction.totalAt
  rw [Finset.mul_sum]
  conv_rhs => rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro q hq
  unfold SecondAdaptiveProduction.centeredEnergyAt SecondParentProduction.centeredEnergy
  rw [SecondPositiveChildren.centeredEnergy_eq]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  dsimp only [preScalar, nodeIntegral, branchAt, selectedCenter,
    SecondAdaptiveRetained.dataAt, SecondAdaptiveRetained.oldIndexAt,
    SecondParentProduction.test, FirstToSecondData.data,
    FirstCenteredFamily.family, FirstCompleteFamily.family, mellinTest,
    SecondParentProduction.selectedDivisor, SecondParentProduction.selectedRow,
    SecondParentProduction.selectedSector, SecondAdaptiveRetained.selectedDivisorAt,
    SecondAdaptiveRetained.selectedRowAt, SecondAdaptiveRetained.selectedSectorAt,
    SecondParentProduction.scale, FirstToSecondData.sourceScale]
  ring

/-- Every actual finite subsource is first partitioned by its common/
overlap center and then placed inside the fixed joint spectral measure.
The same formula applies to all later norm-box restrictions P. -/
theorem selectedTotalOn_eq_integrals (m : ℕ) (side₂ : Bool) (P : Finset Idx) :
    selectedTotalOn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε side₁ m side₂ P =
      cauchyMass K S T J₁ s *
        ∑ b : Bin, ∑ J₂ ∈ (T.columns.slots \ J₁).powerset,
          sourceIntegral K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε side₁ m side₂
            (bin K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ P b) b J₂ := by
  unfold selectedTotalOn
  rw [sum_bins K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ P
    (fun b i => preScalar K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε i *
      ‖firstMark K S D T J₁ side₁ i.1 i.2.1‖ ^ 2 *
      nodeIntegral K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ m side₂ b i)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  simp_rw [nodeIntegral_eq, sourceIntegral_eq_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₂ hJ₂
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [preScalar, scalar]
  ring

/-- Exact production assembly: actual totalAt enters the common
integral of actual finite source columns, preserving every original
prime weight, both mask divisors, all unit sectors and the overlap zero. -/
theorem actualTotal_eq_integrals (m : ℕ) (side₂ : Bool) :
    actualTotal K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε side₁ m side₂ =
      cauchyMass K S T J₁ s *
        ∑ b : Bin, ∑ J₂ ∈ (T.columns.slots \ J₁).powerset,
          sourceIntegral K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε side₁ m side₂
            (bin K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ Finset.univ b) b J₂ := by
  rw [actualTotal_eq_selected, selectedTotalOn_eq_integrals]

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondProductionIntegral

end
