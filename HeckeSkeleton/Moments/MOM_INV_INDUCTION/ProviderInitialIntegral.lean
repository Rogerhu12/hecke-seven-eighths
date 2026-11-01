import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialPointwise
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondMellinEnergy

/-!
# The actual initial production under its common spectral measure

The original norm profile determines one powered Mellin density before
any arithmetic source is chosen. Every actual common ideal, divisor,
original unit sector and independent overlap enters the finite source
under that same measure. Integrability is proved from the literal finite
canonical columns. The source normalization X⁻¹ is retained throughout.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialIntegral

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP
open FixedTripleFibers CanonicalChildren CanonicalNormPools ActualDivisorSectors CommonKernel
open SecondSourceColumns (newRowIdeal newSector)
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable {σ : Type*} [DecidableEq σ]
variable (C : CanonicalBlock.ColumnData K S σ)
variable (Θ : Subgroup (HeckeCharacter K)) (ψ : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ C.background)
variable (W : SchwartzMap ℝ ℂ) (G : HeckeCharacter K) (hG : G ∈ Θ)
variable (hbase : 1 < C.base) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
variable (m : ℝ) (H : ProviderInitialSource.Cutoff K S)
local notation "X" => C.base ^ C.length
local notation "T" => ProviderInitialProduction.parent K S C Θ ψ hν W hbase hW m
local notation "Idx" => ProviderInitialSource.Index K S D Γ X H
local notation "Bin" => SecondMobiusGeometry.Index X
local notation "Cinitial" => ProviderInitialInverse.family K S C Θ ψ hν W
local notation "gamma0" => ProviderInitialInverse.unitTriple K

def mellinTest : SchwartzMap ℝ ℂ := FinalMellinTests.powerTest W (-(1 / 2 : ℝ))

include hW in
theorem mellinTest_support : tsupport (mellinTest W) ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8) := by
  intro x hx
  have hh := hW (FinalMellinTests.powerTest_support W (-(1 / 2 : ℝ)) hx)
  exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

def density (k : ℕ) (p : LogPlane × ℝ) : ℝ :=
  FirstCommonEnvelope.frequencyEnvelope k p.1 *
    ‖SecondMellinEnergy.mellinDensity (mellinTest W) (mellinTest_support W hW) p.2‖

theorem density_nonneg (k : ℕ) (p : LogPlane × ℝ) : 0 ≤ density W hW k p :=
  mul_nonneg (FirstCommonEnvelope.frequencyEnvelope_nonneg k p.1) (norm_nonneg _)

def cauchyMass : ℝ := (C.slots.powerset.card : ℝ) *
  SecondMellinEnergy.mellinMass (mellinTest W) (mellinTest_support W hW)

def actualColumn (J : Finset σ) (b : Bin) (i : Idx) (t : ℝ) : ℂ :=
  childValue K Sset D (ProviderInitialNodes.wideFamily K S C Θ ψ hν W G hG J b t)
    (CanonicalSectors.sectorUnit K Sset Γ) (ProviderInitialSource.child K S D Γ X H i)

theorem column_as_actual_child (J : Finset σ) (b : Bin) (i : Idx) (t : ℝ) :
    column K Sset D
      (SecondCenteredFamily.family K S Cinitial gamma0 G hG J (SecondMobiusGeometry.childScale X b) t)
      (CanonicalSectors.sectorUnit K Sset Γ)
      (SecondCenteredFamily.appendResidual K gamma0
        (ProviderInitialSource.residual K S D Γ X H i).val.val)
      (SecondCompleteColumns.finalLabel K S (FirstInversePoisson.unitIdeal K S)
        (ProviderInitialSource.divisor K S D Γ X H i)
        (ProviderInitialSource.overlap K S D Γ X H i)).val.val
      ((newRowIdeal K S (ProviderInitialSource.frequency K S D Γ X H i).1
        (ProviderInitialSource.unitDivisor K S)
        (sIntegerMaskGenerator K Sset (ProviderInitialSource.mask K S D Γ X H i))).val.val,
        newSector K S Γ D (ProviderInitialSource.unitDivisor K S)
          (sIntegerMaskGenerator K Sset (ProviderInitialSource.mask K S D Γ X H i))
          (ProviderInitialSource.frequency K S D Γ X H i).2) =
        actualColumn K S D Γ C Θ ψ hν W G hG H J b i t := by
  have hgamma : SecondCenteredFamily.appendResidual K gamma0
      (ProviderInitialSource.residual K S D Γ X H i).val.val =
      ProviderInitialSource.outer K S D Γ X H i := by
    simp only [SecondCenteredFamily.appendResidual, ProviderInitialInverse.unitTriple,
      ProviderInitialSource.outer, one_mul]
  have hlabel : (SecondCompleteColumns.finalLabel K S (FirstInversePoisson.unitIdeal K S)
      (ProviderInitialSource.divisor K S D Γ X H i)
      (ProviderInitialSource.overlap K S D Γ X H i)).val.val =
      ProviderInitialSource.newLabel K S D Γ X H i := by
    change (1 : Ideal (𝓞 K)) *
      (ProviderInitialSource.divisor K S D Γ X H i).val.val *
      (ProviderInitialSource.overlap K S D Γ X H i).val.val = _
    simp only [one_mul, ProviderInitialSource.newLabel]
  rw [hgamma, hlabel]
  unfold actualColumn childValue ProviderInitialSource.child
  rw [ProviderInitialSource.newRow_actual]
  rfl

def jointColumn (k : ℕ) (side : Bool) (J : Finset σ) (b : Bin) (i : Idx)
    (p : LogPlane × ℝ) : ℝ :=
  density W hW k p * ‖actualColumn K S D Γ C Θ ψ hν W G hG H J b i
    (p.2 + SecondParentProduction.coordinate side p.1)‖ ^ 2

include hbase in
theorem jointColumn_integrable (k : ℕ) (side : Bool) (J : Finset σ) (b : Bin) (i : Idx) :
    Integrable (jointColumn K S D Γ C Θ ψ hν W G hG hW H k side J b i)
      ((volume : Measure LogPlane).prod (volume : Measure ℝ)) := by
  exact SecondMellinEnergy.joint_column_integrable K S D Γ Cinitial gamma0 G hG J
    (SecondMobiusGeometry.childScale X b) (ProviderInitialSource.outer K S D Γ X H i)
    (ProviderInitialSource.newLabel K S D Γ X H i) (ProviderInitialSource.newRow K S D Γ X H i)
    (mellinTest W) (mellinTest_support W hW) hbase
    (SecondMobiusGeometry.childScale_pos X (Real.rpow_pos_of_pos (zero_lt_one.trans hbase) _) b)
    (FirstCommonEnvelope.frequencyEnvelope k) (FirstCommonEnvelope.frequencyEnvelope_integrable k)
    (FirstCommonEnvelope.frequencyEnvelope_continuous k) (SecondParentProduction.coordinate side)

def jointEnergy (k : ℕ) (side : Bool) (J : Finset σ) (b : Bin) (i : Idx) : ℝ :=
  ∫ p : LogPlane × ℝ, jointColumn K S D Γ C Θ ψ hν W G hG hW H k side J b i p
    ∂((volume : Measure LogPlane).prod (volume : Measure ℝ))

def columnEnergyAt (J : Finset σ) (b : Bin) (i : Idx) (tau : ℝ) : ℝ :=
  ∫ t : ℝ, ‖SecondMellinEnergy.mellinDensity (mellinTest W) (mellinTest_support W hW) t‖ *
    ‖actualColumn K S D Γ C Θ ψ hν W G hG H J b i (t + tau)‖ ^ 2

include hbase in
theorem outer_column_integrable (k : ℕ) (side : Bool) (J : Finset σ) (b : Bin) (i : Idx) :
    Integrable (fun xi : LogPlane => FirstCommonEnvelope.frequencyEnvelope k xi *
      columnEnergyAt K S D Γ C Θ ψ hν W G hG hW H J b i (SecondParentProduction.coordinate side xi)) := by
  have hi := (jointColumn_integrable K S D Γ C Θ ψ hν W G hG hbase hW H k side J b i).integral_prod_left
  simpa only [jointColumn, density, mul_assoc, integral_const_mul, columnEnergyAt] using hi

include hbase in
theorem outer_column_eq_joint (k : ℕ) (side : Bool) (J : Finset σ) (b : Bin) (i : Idx) :
    (∫ xi : LogPlane, FirstCommonEnvelope.frequencyEnvelope k xi *
      columnEnergyAt K S D Γ C Θ ψ hν W G hG hW H J b i (SecondParentProduction.coordinate side xi)) =
      jointEnergy K S D Γ C Θ ψ hν W G hG hW H k side J b i := by
  unfold jointEnergy
  rw [integral_prod _ (jointColumn_integrable K S D Γ C Θ ψ hν W G hG hbase hW H k side J b i)]
  simp only [jointColumn, density, mul_assoc, integral_const_mul, columnEnergyAt]

def overlapZeroNorm (i : Idx) : ℝ :=
  ‖SecondColumnEnergy.overlapZero K S (ProviderInitialSource.common K S D Γ X H i)
    (FirstInversePoisson.unitIdeal K S) (ProviderInitialSource.overlap K S D Γ X H i)‖

def assignedMark (J : Finset σ) (i : Idx) : ℂ :=
  divisorMark J C.primeLists C.primeWeights
    ((ProviderInitialSource.common K S D Γ X H i).val.val *
      (ProviderInitialSource.overlap K S D Γ X H i).val.val)

def branchAt (b : Bin) (i : Idx) (tau : ℝ) : ℝ :=
  SecondPositiveChildren.branchEnergy K S D Γ Cinitial gamma0 G hG
    (ProviderInitialSource.common K S D Γ X H i) (FirstInversePoisson.unitIdeal K S)
    (ProviderInitialSource.divisor K S D Γ X H i)
    (newRowIdeal K S (ProviderInitialSource.frequency K S D Γ X H i).1
      (ProviderInitialSource.unitDivisor K S)
      (sIntegerMaskGenerator K Sset (ProviderInitialSource.mask K S D Γ X H i)))
    (newSector K S Γ D (ProviderInitialSource.unitDivisor K S)
      (sIntegerMaskGenerator K Sset (ProviderInitialSource.mask K S D Γ X H i))
      (ProviderInitialSource.frequency K S D Γ X H i).2)
    (mellinTest W) (mellinTest_support W hW) X b i.2.2.2 tau

theorem branchAt_eq (b : Bin) (i : Idx) (tau : ℝ) :
    branchAt K S D Γ C Θ ψ hν W G hG hW H b i tau =
      (overlapZeroNorm K S D Γ C H i * cauchyMass K S C W hW) *
        ∑ J ∈ C.slots.powerset, ‖assignedMark K S D Γ C H J i‖ ^ 2 *
          columnEnergyAt K S D Γ C Θ ψ hν W G hG hW H J b i tau := by
  unfold branchAt
  dsimp only [ProviderInitialSource.common]
  unfold SecondPositiveChildren.branchEnergy
  unfold columnEnergyAt SecondMellinEnergy.columnEnergy
  have hcolumn (J : Finset σ) (t : ℝ) :=
    column_as_actual_child K S D Γ C Θ ψ hν W G hG H J b i t
  dsimp only [ProviderInitialSource.residual, ProviderInitialSource.common,
    ProviderInitialSource.overlap] at hcolumn
  simp_rw [hcolumn]
  rfl

def nodeIntegral (k : ℕ) (side : Bool) (b : Bin) (i : Idx) : ℝ :=
  ∫ xi : LogPlane, FirstCommonEnvelope.frequencyEnvelope k xi *
    branchAt K S D Γ C Θ ψ hν W G hG hW H b i (SecondParentProduction.coordinate side xi)

include hbase in
theorem nodeIntegral_eq (k : ℕ) (side : Bool) (b : Bin) (i : Idx) :
    nodeIntegral K S D Γ C Θ ψ hν W G hG hW H k side b i =
      (overlapZeroNorm K S D Γ C H i * cauchyMass K S C W hW) *
        ∑ J ∈ C.slots.powerset, ‖assignedMark K S D Γ C H J i‖ ^ 2 *
          jointEnergy K S D Γ C Θ ψ hν W G hG hW H k side J b i := by
  let c := overlapZeroNorm K S D Γ C H i * cauchyMass K S C W hW
  have he : nodeIntegral K S D Γ C Θ ψ hν W G hG hW H k side b i =
      ∫ xi : LogPlane, ∑ J ∈ C.slots.powerset,
        (c * ‖assignedMark K S D Γ C H J i‖ ^ 2) *
        (FirstCommonEnvelope.frequencyEnvelope k xi *
          columnEnergyAt K S D Γ C Θ ψ hν W G hG hW H J b i (SecondParentProduction.coordinate side xi)) := by
    apply integral_congr_ae
    filter_upwards [] with xi
    rw [branchAt_eq]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only [c]
    ring
  rw [he, integral_finsetSum _ (fun J _ =>
    (outer_column_integrable K S D Γ C Θ ψ hν W G hG hbase hW H k side J b i).const_mul _)]
  simp only [integral_const_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [outer_column_eq_joint K S D Γ C Θ ψ hν W G hG hbase hW H k side J b i]
  dsimp only [c]
  ring

def sourceIntegral (e : ℝ) (k : ℕ) (side : Bool) (P : Finset Idx) (b : Bin) (J : Finset σ) : ℝ :=
  ∫ p : LogPlane × ℝ, density W hW k p *
    ProviderInitialPointwise.sourceSum K S D Γ C Θ ψ hν W G hG hbase hW m H P b J e
      (p.2 + SecondParentProduction.coordinate side p.1)
    ∂((volume : Measure LogPlane).prod (volume : Measure ℝ))

theorem sourceIntegral_eq_sum (e : ℝ) (k : ℕ) (side : Bool) (P : Finset Idx) (b : Bin) (J : Finset σ) :
    sourceIntegral K S D Γ C Θ ψ hν W G hG hbase hW m H e k side P b J =
      X⁻¹ * ∑ i ∈ P,
        ProviderInitialProduction.positiveScalar K S D Γ C Θ ψ hν W hbase hW m H e i *
          overlapZeroNorm K S D Γ C H i * ‖assignedMark K S D Γ C H J i‖ ^ 2 *
          jointEnergy K S D Γ C Θ ψ hν W G hG hW H k side J b i := by
  let c := fun i : Idx => X⁻¹ *
    ProviderInitialProduction.positiveScalar K S D Γ C Θ ψ hν W hbase hW m H e i *
      overlapZeroNorm K S D Γ C H i * ‖assignedMark K S D Γ C H J i‖ ^ 2
  have he : sourceIntegral K S D Γ C Θ ψ hν W G hG hbase hW m H e k side P b J =
      ∫ p : LogPlane × ℝ, ∑ i ∈ P,
        c i * jointColumn K S D Γ C Θ ψ hν W G hG hW H k side J b i p
        ∂((volume : Measure LogPlane).prod (volume : Measure ℝ)) := by
    apply integral_congr_ae
    filter_upwards [] with p
    unfold ProviderInitialPointwise.sourceSum
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [c, jointColumn, overlapZeroNorm, assignedMark, actualColumn]
    ring
  rw [he, integral_finsetSum _ (fun i _ =>
    (jointColumn_integrable K S D Γ C Θ ψ hν W G hG hbase hW H k side J b i).const_mul (c i))]
  simp only [integral_const_mul, jointEnergy, c, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def selectedTotalOn (e : ℝ) (k : ℕ) (side : Bool) (P : Finset Idx) : ℝ :=
  ∑ i ∈ P, ProviderInitialProduction.positiveScalar K S D Γ C Θ ψ hν W hbase hW m H e i *
    nodeIntegral K S D Γ C Θ ψ hν W G hG hW H k side
      (ProviderInitialBoxes.binIndex K S D Γ X H i) i

/-- This equality starts with the provider's actual `totalAt` and
reindexes its three original indices together with the independent
Moebius overlap. No surrogate positive source is supplied. -/
theorem actualTotal_eq_selected (e : ℝ) (k : ℕ) (side : Bool) :
    SecondAdaptiveProduction.totalAt K S D Γ T H G hG e k side =
      selectedTotalOn K S D Γ C Θ ψ hν W G hG hbase hW m H e k side Finset.univ := by
  unfold SecondAdaptiveProduction.totalAt selectedTotalOn
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.sum_congr rfl
  intro delta hdelta
  apply Finset.sum_congr rfl
  intro row hrow
  unfold SecondAdaptiveProduction.centeredEnergyAt SecondParentProduction.centeredEnergy
  rw [SecondPositiveChildren.centeredEnergy_eq]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  dsimp only [ProviderInitialProduction.positiveScalar, ProviderInitialProduction.parentIndex,
    nodeIntegral, branchAt, ProviderInitialBoxes.binIndex,
    ProviderInitialSource.common, ProviderInitialSource.mask, ProviderInitialSource.divisor,
    ProviderInitialSource.frequency, ProviderInitialSource.overlap,
    SecondAdaptiveRetained.dataAt, SecondAdaptiveRetained.oldIndexAt,
    ProviderInitialProduction.parent, ProviderInitialInverse.parentData,
    ProviderInitialInverse.family, SecondParentProduction.test, SecondParentProduction.scale,
    SecondParentProduction.selectedDivisor, SecondParentProduction.selectedRow,
    SecondParentProduction.selectedSector, ProviderInitialSource.unitDivisor, mellinTest]
  ring

/-- The exact normalized initial total is expressed using one joint
spectral measure. All original slot subsets, common norms, mask
divisors, sectors and overlap ideals remain in the finite source. -/
theorem selectedTotalOn_eq_integrals (e : ℝ) (k : ℕ) (side : Bool) (P : Finset Idx) :
    X⁻¹ * selectedTotalOn K S D Γ C Θ ψ hν W G hG hbase hW m H e k side P =
      cauchyMass K S C W hW * ∑ b : Bin, ∑ J ∈ C.slots.powerset,
        sourceIntegral K S D Γ C Θ ψ hν W G hG hbase hW m H e k side
          (ProviderInitialBoxes.bin K S D Γ X H P b) b J := by
  unfold selectedTotalOn
  rw [ProviderInitialBoxes.sum_bins_dependent K S D Γ X H P
    (fun b i => ProviderInitialProduction.positiveScalar K S D Γ C Θ ψ hν W hbase hW m H e i *
      nodeIntegral K S D Γ C Θ ψ hν W G hG hW H k side b i)]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  simp_rw [nodeIntegral_eq K S D Γ C Θ ψ hν W G hG hbase hW H k side,
    sourceIntegral_eq_sum K S D Γ C Θ ψ hν W G hG hbase hW m H e k side]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem actualTotal_eq_integrals (e : ℝ) (k : ℕ) (side : Bool) :
    X⁻¹ * SecondAdaptiveProduction.totalAt K S D Γ T H G hG e k side =
      cauchyMass K S C W hW * ∑ b : Bin, ∑ J ∈ C.slots.powerset,
        sourceIntegral K S D Γ C Θ ψ hν W G hG hbase hW m H e k side
          (ProviderInitialBoxes.bin K S D Γ X H Finset.univ b) b J := by
  rw [actualTotal_eq_selected, selectedTotalOn_eq_integrals]

theorem sourceIntegral_sum_boxes (e : ℝ) (k : ℕ) (side : Bool)
    (P : Finset Idx) (b : Bin) (J : Finset σ) (A : ℝ) :
    sourceIntegral K S D Γ C Θ ψ hν W G hG hbase hW m H e k side P b J =
      ∑ j : ProviderInitialBoxes.BoxIndex C.base A,
        sourceIntegral K S D Γ C Θ ψ hν W G hG hbase hW m H e k side
          (ProviderInitialBoxes.box K S D Γ X H P C.base A j) b J := by
  rw [sourceIntegral_eq_sum]
  rw [ProviderInitialBoxes.sum_boxes K S D Γ X H P C.base A
    (fun i => ProviderInitialProduction.positiveScalar K S D Γ C Θ ψ hν W hbase hW m H e i *
      overlapZeroNorm K S D Γ C H i * ‖assignedMark K S D Γ C H J i‖ ^ 2 *
      jointEnergy K S D Γ C Θ ψ hν W G hG hW H k side J b i)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact (sourceIntegral_eq_sum K S D Γ C Θ ψ hν W G hG hbase hW m H e k side _ b J).symm

theorem actualTotal_eq_boxed_integrals (e : ℝ) (k : ℕ) (side : Bool) (A : ℝ) :
    X⁻¹ * SecondAdaptiveProduction.totalAt K S D Γ T H G hG e k side =
      cauchyMass K S C W hW * ∑ b : Bin, ∑ J ∈ C.slots.powerset,
        ∑ j : ProviderInitialBoxes.BoxIndex C.base A,
          sourceIntegral K S D Γ C Θ ψ hν W G hG hbase hW m H e k side
            (ProviderInitialBoxes.boxed K S D Γ X H Finset.univ b C.base A j) b J := by
  rw [actualTotal_eq_integrals]
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro J hJ
  exact sourceIntegral_sum_boxes K S D Γ C Θ ψ hν W G hG hbase hW m H e k side _ b J A

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialIntegral

end
