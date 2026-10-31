import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondFactorIdentification
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondExceptionalPartition
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteNormalizedChildren
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityChildIntegrability

/-!
# Literal second allocations assemble the normalized child family

Every label is the original divisor, finite character and two occurrence
allocations.  The two sources are constructed from those allocations and
the actual correlation rows.  One original exceptional predicate is
applied before row Cauchy; the exact restriction identities identify its
two source energies.  Original arithmetic weights and the original
Fourier density form the measure used for all produced children.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum WholeAllocation

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {V H ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [Fintype ι] [DecidableEq ι]
variable {k l : ℕ} {ω ψ : HeckeCharacter F}
variable {S₁ S₂ T₁ T₂ : Finset (Ideal (𝓞 F))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 F))}
variable {T : Fin l → Finset (HeightOneSpectrum (𝓞 F))}
variable {IB : AllocationColumn F l → A.Exterior}

local notation "Labels" => ↥(liveSecondAllocationLabels Ray S₁ S₂ S T₁ T₂ T IB)

variable (R : ActualSecondCorrelationRows A σ H ι)
variable (C : A.GeneralArithmeticContext σ η hS)
variable (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ I ∈ S₂, I ≠ 0)
variable (hT₁ : ∀ I ∈ T₁, I ≠ 0) (hT₂ : ∀ I ∈ T₂, I ≠ 0)
variable (LC : Labels → FixedChildCharacters F k) (RC : Labels → FixedChildCharacters F l)
variable (DL : ∀ z : Labels,
  SecondCoefficientTermDictionary (LC z) (fixedLeftPhase Ray z.val.2.1) S₁ S₂ S)
variable (DR : ∀ z : Labels,
  SecondCoefficientTermDictionary (RC z) (fixedRightPhase Ray z.val.2.1) T₁ T₂ T)
variable (hbaseL : ∀ z, 1 < (DL z).base) (hbaseR : ∀ z, 1 < (DR z).base)
variable (hlengthL : ∀ z i, 0 < (DL z).length i) (hlengthR : ∀ z i, 0 < (DR z).length i)
variable (x₁ x₂ y₁ y₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → V)
variable (x : H → Fin k → HeightOneSpectrum (𝓞 F) → V)
variable (y : H → Fin l → HeightOneSpectrum (𝓞 F) → V)

def secondOriginalLeftSource (z : Labels) : ActualAllocatedSource A V R.live k :=
  R.source C (secondLabelLeftAllocation hS₁ hS₂ z) (LC z) (fixedLeftPhase Ray z.val.2.1)
    (DL z) (hbaseL z) (hlengthL z) x₁ x₂ x

def secondOriginalRightSource (z : Labels) : ActualAllocatedSource A V R.live l :=
  (R.source C (secondLabelRightAllocation hT₁ hT₂ z) (RC z) (fixedRightPhase Ray z.val.2.1)
    (DR z) (hbaseR z) (hlengthR z) y₁ y₂ y).negativeSide

local notation "LSource" => secondOriginalLeftSource R C hS₁ hS₂ LC DL hbaseL hlengthL x₁ x₂ x
local notation "RSource" => secondOriginalRightSource R C hT₁ hT₂ RC DR hbaseR hlengthR y₁ y₂ y

variable {theta : Finset (HeckeCharacter F)} (Q : PairedFiniteCharacters theta H)

/-- Full-row factor/profile calibrations and finite inducing-character
ratios produce the two calibrations on one original nonexceptional set.
This is the raw-input entry to the capacity family below. -/
def secondNonexceptionalCalibrations
    (CL : ∀ z : Labels, ActualAllocatedSource.FullCalibration (LSource z) (σ := σ) ω ψ)
    (CR : ∀ z : Labels, ActualAllocatedSource.FullCalibration (RSource z) (σ := σ) ω ψ)
    (left_theta : ∀ z ξ, ((CL z).data ξ).theta = theta)
    (right_theta : ∀ z ξ, ((CR z).data ξ).theta = theta)
    (left_ratio : ∀ z ξ h,
      ((CL z).data ξ).rowCharacter ((LSource z).row h).momentIdeal / Q.left h.val ∈ Q.subgroup)
    (right_ratio : ∀ z ξ h,
      ((CR z).data ξ).rowCharacter ((RSource z).row h).momentIdeal / Q.right h.val ∈ Q.subgroup)
    (z : Labels) :
    ((LSource z).restrictRows (fun h => ¬ Q.exceptional h.val)).Calibration (σ := σ) ω ψ ×
      ((RSource z).restrictRows (fun h => ¬ Q.exceptional h.val)).Calibration (σ := σ) ω ψ :=
  (Q.comap (fun h : R.live => h.val)).nonexceptionalCalibrationsOfFiniteTwists
    (CL z) (CR z) (left_theta z) (right_theta z) (left_ratio z) (right_ratio z)

variable (CL : ∀ z : Labels,
  ((LSource z).restrictRows (fun h => ¬ Q.exceptional h.val)).Calibration (σ := σ) ω ψ)
variable (CR : ∀ z : Labels,
  ((RSource z).restrictRows (fun h => ¬ Q.exceptional h.val)).Calibration (σ := σ) ω ψ)
variable (GL : ∀ z : Labels, (CL z).NormalizedCapacityData)
variable (GR : ∀ z : Labels, (CR z).NormalizedCapacityData)
variable (PL : SecondColumnFactors F Ray k) (PR : SecondColumnFactors F Ray l)
variable {Z : ℝ} (left_base : ∀ z, (DL z).base = Z) (right_base : ∀ z, (DR z).base = Z)

/-- The finite family contains the actual computed sources for every
nonempty original allocation.  Its later active filter removes only
source pairs proved identically zero, before all continuous parameters. -/
def secondNormalizedPairFamily : ActualNormalizedPairFamily A σ V Labels ω ψ Z where
  LeftRow _ := R.live
  RightRow _ := R.live
  leftSlots _ := k
  rightSlots _ := l
  leftSource z := (LSource z).restrictRows (fun h => ¬ Q.exceptional h.val)
  rightSource z := (RSource z).restrictRows (fun h => ¬ Q.exceptional h.val)
  leftCalibration := CL
  rightCalibration := CR
  leftCapacity := GL
  rightCapacity := GR
  left_base := left_base
  right_base := right_base
  leftNormalizer _ := PL.normalizer
  rightNormalizer _ := PR.normalizer

local notation "Fam" => secondNormalizedPairFamily R C hS₁ hS₂ hT₁ hT₂ LC RC DL DR
  hbaseL hbaseR hlengthL hlengthR x₁ x₂ y₁ y₂ x y Q CL CR GL GR PL PR left_base right_base

variable (hidentL : ∀ z : Labels, (DL z).FactorIdentification PL)
variable (hidentR : ∀ z : Labels, (DR z).FactorIdentification PR)
variable (IA : AllocationColumn F k → A.Exterior)
variable (hIA : ∀ i ∈ childCartesianColumns S₁ S₂ S, (IA i).val = allocationColumnIdeal i)
variable (hIB : ∀ i ∈ childCartesianColumns T₁ T₂ T, (IB i).val = allocationColumnIdeal i)

/-- The source pair in the produced family is exactly the original
second allocation pair, on the same original nonexceptional rows. -/
theorem secondNormalizedPairFamily_sourcePair (parentWidth : ℝ) (z : Labels) (ξ : V) :
    Fam.sourcePair parentWidth z ξ =
      z.val.pairEnergy (S₁ := S₁) (S₂ := S₂) (S := S)
        (R.restrictRows (fun h => ¬ Q.exceptional h)) IA
        PL.ray PR.ray PL.coefficient PR.coefficient
        (fun h => rawSourceLocation (x₁ h) (x₂ h) (x h))
        (fun h => rawSourceLocation (y₁ h) (y₂ h) (y h)) ξ / Z ^ parentWidth := by
  rw [z.val.pairEnergy_identified _ IA PL PR (LC z) (RC z) (DL z) (DR z)
    (hidentL z) (hidentR z)]
  rw [secondAllocationLabel_pair_eq_actual_sources
    (R.restrictRows (fun h => ¬ Q.exceptional h)) C hS₁ hS₂ hT₁ hT₂ z
    (LC z) (RC z) (DL z) (DR z) (hbaseL z) (hlengthL z) (hbaseR z) (hlengthR z)
    IA hIA hIB PL.leftNormalizer PL.rightNormalizer PR.leftNormalizer PR.rightNormalizer
    PL.slotNormalizer PR.slotNormalizer x₁ x₂ y₁ y₂ x y ξ]
  rw [R.source_restrictRows_energy, R.negative_source_restrictRows_energy]
  rfl

/-- The original finite arithmetic coefficient is part of the same
positive measure as the original Fourier density. -/
def secondOriginalLabelMeasure (Fker : 𝓢(V, ℂ)) (phaseTable : Ray × Ray → Circle)
    (z : Labels) : Measure V :=
  ENNReal.ofReal (z.val.weight phaseTable) • actualFourierMeasure Fker

theorem secondOriginalLabelMeasure_integral (Fker : 𝓢(V, ℂ))
    (phaseTable : Ray × Ray → Circle) (z : Labels) (f : V → ℝ) :
    (∫ ξ, f ξ ∂secondOriginalLabelMeasure Fker phaseTable z) =
      z.val.weight phaseTable * ∫ ξ, f ξ ∂actualFourierMeasure Fker := by
  rw [secondOriginalLabelMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (z.val.weight_nonneg phaseTable), smul_eq_mul]

/-- No source-energy integrability premise is needed: the original
finite allocated columns prove it for the actual arithmetic measure. -/
theorem secondNormalizedPairFamily_sourcePair_integrable
    (Fker : 𝓢(V, ℂ)) (phaseTable : Ray × Ray → Circle) (parentWidth : ℝ) (z : Labels) :
    Integrable (Fam.sourcePair parentWidth z) (secondOriginalLabelMeasure Fker phaseTable z) := by
  change Integrable (fun ξ => Fam.sourcePair parentWidth z ξ) _
  simp_rw [secondNormalizedPairFamily_sourcePair (hidentL := hidentL) (hidentR := hidentR)
    (hIA := hIA) (hIB := hIB)]
  exact ((z.val.pairEnergy_integrable Fker (R.restrictRows (fun h => ¬ Q.exceptional h))
    IA PL.ray PR.ray PL.coefficient PR.coefficient
    (fun h => rawSourceLocation (x₁ h) (x₂ h) (x h))
    (fun h => rawSourceLocation (y₁ h) (y₂ h) (y h))).div_const (Z ^ parentWidth)).smul_measure
      ENNReal.ofReal_ne_top

def secondNonexceptionalAllocatedCost (Fker : 𝓢(V, ℂ)) (phaseTable : Ray × Ray → Circle) : ℝ :=
  let R' := R.restrictRows (fun h => ¬ Q.exceptional h)
  secondAllocatedKernelCost Ray Fker R'.rows R'.frequency S₁ S₂ S T₁ T₂ T
    (primePowerProduct R'.primes R'.leftMultiplicity)
    (primePowerProduct R'.primes R'.rightMultiplicity)
    IA IB R'.leftGenerator R'.rightGenerator R'.leftGenerates R'.rightGenerates
    PL.ray PR.ray phaseTable R'.weight PL.coefficient PR.coefficient
    (fun h => rawSourceLocation (x₁ h) (x₂ h) (x h))
    (fun h => rawSourceLocation (y₁ h) (y₂ h) (y h))

local notation "Cost" => secondNonexceptionalAllocatedCost R x₁ x₂ y₁ y₂ x y Q PL PR IA

def secondNonexceptionalResidualCost (Fker : 𝓢(V, ℂ)) (phaseTable : Ray × Ray → Circle) : ℝ :=
  let R' := R.restrictRows (fun h => ¬ Q.exceptional h)
  secondResidualKernelCost Ray Fker R'.rows R'.frequency
    (childCartesianColumns S₁ S₂ S) (childCartesianColumns T₁ T₂ T)
    (primePowerProduct R'.primes R'.leftMultiplicity)
    (primePowerProduct R'.primes R'.rightMultiplicity)
    IA IB R'.leftGenerator R'.rightGenerator R'.leftGenerates R'.rightGenerates
    PL.ray PR.ray phaseTable R'.weight PL.coefficient PR.coefficient
    (fun h => rawSourceLocation (x₁ h) (x₂ h) (x h))
    (fun h => rawSourceLocation (y₁ h) (y₂ h) (y h))

local notation "ResidualCost" => secondNonexceptionalResidualCost R x₁ x₂ y₁ y₂ x y Q PL PR IA

theorem secondNonexceptionalResidualCost_le_allocated
    (Fker : 𝓢(V, ℂ)) (phaseTable : Ray × Ray → Circle) :
    ResidualCost Fker phaseTable ≤ Cost Fker phaseTable := by
  unfold secondNonexceptionalResidualCost secondNonexceptionalAllocatedCost
  exact actual_second_kernel_allocation_bound Ray Fker
    (R.restrictRows (fun h => ¬ Q.exceptional h)).rows R.frequency
    S₁ S₂ S T₁ T₂ T
    (primePowerProduct R.primes R.leftMultiplicity) (primePowerProduct R.primes R.rightMultiplicity)
    IA IB hIA hIB R.leftGenerator R.rightGenerator R.leftGenerates R.rightGenerates
    PL.ray PR.ray phaseTable R.weight PL.coefficient PR.coefficient
    (fun h => rawSourceLocation (x₁ h) (x₂ h) (x h))
    (fun h => rawSourceLocation (y₁ h) (y₂ h) (y h))

/-- Exact identification of the original cost with the computed finite
source family, with every original arithmetic factor appearing once. -/
theorem secondNonexceptionalAllocatedCost_eq_sources
    (Fker : 𝓢(V, ℂ)) (phaseTable : Ray × Ray → Circle) (parentWidth : ℝ) :
    Cost Fker phaseTable / Z ^ parentWidth =
      ∑ z : Labels, ∫ ξ, Fam.sourcePair parentWidth z ξ
        ∂secondOriginalLabelMeasure Fker phaseTable z := by
  unfold secondNonexceptionalAllocatedCost
  rw [secondAllocatedKernelCost_eq_live_labels, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  rw [secondOriginalLabelMeasure_integral]
  simp_rw [secondNormalizedPairFamily_sourcePair (hidentL := hidentL) (hidentR := hidentR)
    (hIA := hIA) (hIB := hIB)]
  rw [integral_div_const, actualFourierMeasure_integral_eq]
  ring

/-- The genuine original second cost reaches the actual normalized
children.  The integrability premises are analytic facts about the raw
finite atoms and their explicit profile envelope, never an energy,
parent-recursion or total-mass estimate. -/
theorem secondNonexceptionalAllocatedCost_le_children
    (Fker : 𝓢(V, ℂ)) (phaseTable : Ray × Ray → Circle) (parentWidth : ℝ) (hZ : 0 < Z)
    (hprofile : ∀ z : Fam.active Finset.univ, Measurable (Fam.envelope Finset.univ z))
    (hchild : ∀ z : Fam.active Finset.univ, Integrable
      (fun ξ => Fam.envelope Finset.univ z ξ * Fam.childPair Finset.univ z ξ)
      (secondOriginalLabelMeasure Fker phaseTable z.val)) :
    Cost Fker phaseTable / Z ^ parentWidth ≤
      ∑ z : Fam.active Finset.univ, ∫ ξ, Fam.childPair Finset.univ z ξ
        ∂Fam.kernel Finset.univ (secondOriginalLabelMeasure Fker phaseTable) parentWidth z := by
  rw [secondNonexceptionalAllocatedCost_eq_sources (hidentL := hidentL) (hidentR := hidentR)
    (hIA := hIA) (hIB := hIB)]
  exact Fam.finite_integral Finset.univ (secondOriginalLabelMeasure Fker phaseTable)
    parentWidth hZ hprofile (fun z _ => by
      apply secondNormalizedPairFamily_sourcePair_integrable
        (hidentL := hidentL) (hidentR := hidentR) (hIA := hIA) (hIB := hIB)) hchild

/-- Complete nonexceptional second-kernel reduction.  The original
divisor and occurrence allocations, actual arithmetic coefficients,
capacity repairs, Fourier envelope and both child moments are connected
by the preceding proved identities and inequalities. -/
theorem secondNonexceptionalResidualCost_le_children
    (Fker : 𝓢(V, ℂ)) (phaseTable : Ray × Ray → Circle) (parentWidth : ℝ) (hZ : 0 < Z)
    (hprofile : ∀ z : Fam.active Finset.univ, Measurable (Fam.envelope Finset.univ z))
    (hchild : ∀ z : Fam.active Finset.univ, Integrable
      (fun ξ => Fam.envelope Finset.univ z ξ * Fam.childPair Finset.univ z ξ)
      (secondOriginalLabelMeasure Fker phaseTable z.val)) :
    ResidualCost Fker phaseTable / Z ^ parentWidth ≤
      ∑ z : Fam.active Finset.univ, ∫ ξ, Fam.childPair Finset.univ z ξ
        ∂Fam.kernel Finset.univ (secondOriginalLabelMeasure Fker phaseTable) parentWidth z := by
  have halloc : ResidualCost Fker phaseTable ≤ Cost Fker phaseTable := by
    apply secondNonexceptionalResidualCost_le_allocated (hIA := hIA) (hIB := hIB)
  apply (div_le_div_of_nonneg_right halloc (Real.rpow_pos_of_pos hZ parentWidth).le).trans
  apply secondNonexceptionalAllocatedCost_le_children
    (hidentL := hidentL) (hidentR := hidentR) (hIA := hIA) (hIB := hIB)
    (hZ := hZ) (hprofile := hprofile) (hchild := hchild)

/-- A raw-atom version of the complete second reduction.  Every
integrability statement is proved internally; the final actual children
are frozen at time zero for the next induction call. -/
theorem secondNonexceptionalResidualCost_le_children_from_atoms
    (Fker : 𝓢(V, ℂ)) (phaseTable : Ray × Ray → Circle) (parentWidth : ℝ) (hZ : 0 < Z)
    (hleftMeas : ∀ z : Fam.active Finset.univ, Measurable (GL z.val).radius)
    (hrightMeas : ∀ z : Fam.active Finset.univ, Measurable (GR z.val).radius)
    (hleftOne : ∀ z : Fam.active Finset.univ, ∀ ξ, 1 ≤ (GL z.val).radius ξ)
    (hrightOne : ∀ z : Fam.active Finset.univ, ∀ ξ, 1 ≤ (GR z.val).radius ξ)
    (profileConstant : Fam.active Finset.univ → ℝ)
    (hprofileConstant : ∀ z, 0 ≤ profileConstant z)
    (profileOrder : Fam.active Finset.univ → ℕ)
    (profile_bound : ∀ z : Fam.active Finset.univ, ∀ ξ,
      Fam.envelope Finset.univ z ξ ≤ profileConstant z * (1 + ‖ξ‖) ^ profileOrder z)
    (calL : ∀ z : Fam.active Finset.univ,
      ActualFiniteFamilyControl (Fam.leftChild Finset.univ z).rawData
        (Fam.leftChild Finset.univ z).retainedCount (Fam.leftChild Finset.univ z).raw_count
        (Fam.leftChild Finset.univ z).parameters Z (CL z.val).height)
    (calR : ∀ z : Fam.active Finset.univ,
      ActualFiniteFamilyControl (Fam.rightChild Finset.univ z).rawData
        (Fam.rightChild Finset.univ z).retainedCount (Fam.rightChild Finset.univ z).raw_count
        (Fam.rightChild Finset.univ z).parameters Z (CR z.val).height) :
    ResidualCost Fker phaseTable / Z ^ parentWidth ≤
      ∑ z : Fam.active Finset.univ, ∫ ξ,
        Real.sqrt (normalizedPairedEnergy (Fam.leftData Finset.univ z ξ)
          (Fam.leftParameters Finset.univ z) Z 0) *
        Real.sqrt (normalizedPairedEnergy (Fam.rightData Finset.univ z ξ)
          (Fam.rightParameters Finset.univ z) Z 0)
          ∂Fam.kernel Finset.univ (secondOriginalLabelMeasure Fker phaseTable) parentWidth z := by
  have hprofile (z : Fam.active Finset.univ) : Measurable (Fam.envelope Finset.univ z) :=
    ((hleftMeas z).pow _).mul ((hrightMeas z).pow _)
  have hchild (z : Fam.active Finset.univ) : Integrable
      (fun ξ => Fam.envelope Finset.univ z ξ * Fam.childPair Finset.univ z ξ)
      (secondOriginalLabelMeasure Fker phaseTable z.val) :=
    normalized_capacity_pair_actual_label_integrable
      (Fam.leftChild Finset.univ z) (Fam.rightChild Finset.univ z) Z hZ
      (calL z) (calR z) Fker (z.val.val.weight phaseTable)
      (hleftMeas z) (hrightMeas z) (hleftOne z) (hrightOne z)
      (profileConstant z) (hprofileConstant z) (profileOrder z) (profile_bound z)
  have hb : ResidualCost Fker phaseTable / Z ^ parentWidth ≤
      ∑ z : Fam.active Finset.univ, ∫ ξ, Fam.childPair Finset.univ z ξ
        ∂Fam.kernel Finset.univ (secondOriginalLabelMeasure Fker phaseTable) parentWidth z := by
    apply secondNonexceptionalResidualCost_le_children
      (hidentL := hidentL) (hidentR := hidentR) (hIA := hIA) (hIB := hIB)
      (hZ := hZ) (hprofile := hprofile) (hchild := hchild)
  simpa only [Fam.childPair_eq_frozen] using hb

/-- The exact total mass is computed on the very same retained
allocation carrier and original Fourier measure used in the inequality.
The divisor/allocation estimates must bound this explicit expression. -/
theorem secondNormalizedPairFamily_total_mass
    (Fker : 𝓢(V, ℂ)) (phaseTable : Ray × Ray → Circle) (parentWidth : ℝ) (hZ : 0 < Z)
    (hprofile : ∀ z : Fam.active Finset.univ,
      AEStronglyMeasurable (Fam.envelope Finset.univ z)
        (secondOriginalLabelMeasure Fker phaseTable z.val)) :
    (∑ z : Fam.active Finset.univ,
      (Fam.kernel Finset.univ (secondOriginalLabelMeasure Fker phaseTable) parentWidth z).real Set.univ) =
      ∑ z : Fam.active Finset.univ,
        z.val.val.weight phaseTable * Fam.weight Finset.univ parentWidth z *
          ∫ ξ, Fam.envelope Finset.univ z ξ ∂actualFourierMeasure Fker := by
  rw [Fam.total_mass Finset.univ (secondOriginalLabelMeasure Fker phaseTable)
    parentWidth hZ hprofile]
  apply Finset.sum_congr rfl
  intro z _
  rw [secondOriginalLabelMeasure_integral]
  ring

/-- Fourier decay gives finite kernels and reduces their actual total
mass to one explicit finite arithmetic sum.  This is the expression to
which the genuine divisor and allocation mass bounds apply. -/
theorem secondNormalizedPairFamily_finite_mass_from_profiles
    (Fker : 𝓢(V, ℂ)) (phaseTable : Ray × Ray → Circle) (parentWidth : ℝ) (hZ : 0 < Z)
    (hleftMeas : ∀ z : Fam.active Finset.univ, Measurable (GL z.val).radius)
    (hrightMeas : ∀ z : Fam.active Finset.univ, Measurable (GR z.val).radius)
    (profileConstant : Fam.active Finset.univ → ℝ) (J : ℕ)
    (profile_bound : ∀ z : Fam.active Finset.univ, ∀ ξ,
      Fam.envelope Finset.univ z ξ ≤ profileConstant z * (1 + ‖ξ‖) ^ J) :
    (∀ z : Fam.active Finset.univ,
      IsFiniteMeasure (Fam.kernel Finset.univ
        (secondOriginalLabelMeasure Fker phaseTable) parentWidth z)) ∧
    (∑ z : Fam.active Finset.univ,
      (Fam.kernel Finset.univ (secondOriginalLabelMeasure Fker phaseTable) parentWidth z).real Set.univ) ≤
      (∫ ξ : V, (1 + ‖ξ‖) ^ J ∂actualFourierMeasure Fker) *
        ∑ z : Fam.active Finset.univ,
          z.val.val.weight phaseTable * Fam.weight Finset.univ parentWidth z * profileConstant z := by
  have hm (z : Fam.active Finset.univ) : Measurable (Fam.envelope Finset.univ z) :=
    ((hleftMeas z).pow _).mul ((hrightMeas z).pow _)
  have hn (z : Fam.active Finset.univ) (ξ : V) : 0 ≤ Fam.envelope Finset.univ z ξ :=
    normalizedCapacityPairEnvelope_nonneg ξ
  have hi (z : Fam.active Finset.univ) :
      Integrable (Fam.envelope Finset.univ z) (actualFourierMeasure Fker) := by
    apply ((actualFourierMeasure_polynomial_integrable Fker J).const_mul
      (profileConstant z)).mono' (hm z).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hn z ξ)]
      exact profile_bound z ξ
  have hilabel (z : Fam.active Finset.univ) :
      Integrable (Fam.envelope Finset.univ z)
        (secondOriginalLabelMeasure Fker phaseTable z.val) :=
    (hi z).smul_measure ENNReal.ofReal_ne_top
  refine ⟨fun z => Fam.kernel_finite Finset.univ (secondOriginalLabelMeasure Fker phaseTable)
    parentWidth z (hilabel z), ?_⟩
  rw [secondNormalizedPairFamily_total_mass (hZ := hZ)
    (hprofile := fun z => (hilabel z).aestronglyMeasurable)]
  calc
    _ ≤ ∑ z : Fam.active Finset.univ,
        z.val.val.weight phaseTable * Fam.weight Finset.univ parentWidth z *
          (profileConstant z * ∫ ξ : V, (1 + ‖ξ‖) ^ J ∂actualFourierMeasure Fker) := by
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (z.val.val.weight_nonneg phaseTable)
          (Fam.weight_nonneg Finset.univ parentWidth z hZ))
      calc
        _ ≤ ∫ ξ : V, profileConstant z * (1 + ‖ξ‖) ^ J ∂actualFourierMeasure Fker :=
          integral_mono (hi z) ((actualFourierMeasure_polynomial_integrable Fker J).const_mul _)
            (profile_bound z)
        _ = _ := integral_const_mul _ _
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.secondNonexceptionalCalibrations
#print axioms HeckeSkeleton.Moments.EngineStep.secondNormalizedPairFamily_sourcePair
#print axioms HeckeSkeleton.Moments.EngineStep.secondNonexceptionalAllocatedCost_le_children
#print axioms HeckeSkeleton.Moments.EngineStep.secondNonexceptionalResidualCost_le_children
#print axioms HeckeSkeleton.Moments.EngineStep.secondNonexceptionalResidualCost_le_children_from_atoms
#print axioms HeckeSkeleton.Moments.EngineStep.secondNormalizedPairFamily_total_mass
#print axioms HeckeSkeleton.Moments.EngineStep.secondNormalizedPairFamily_finite_mass_from_profiles
