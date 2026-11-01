import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CompleteRowRecipe
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CommonRadical
import HeckeAxiom.ArithmeticAdapter
import HeckeGeneral.Characters.FiniteRayCoefficientExpansion

/-!
# Complete rows with their original fixed moving factors

The internal class at manuscript lines 1611--1626 contains a fixed
finite product of actual sextic factors in addition to the complete
varying row.  In particular, extraction of a common frequency factor
does not make its character a member of the fixed theta family.

Every moving factor below is an actual nonzero S-integer and an integer
exponent.  Its complete ideal, unit sector and finite Hecke character
are computed with the original probe's proved orbit equivalence.  The
displayed support is the radical of the product of the original factor
ideals, before exponent cancellation, including exponent zero.  The
fixed remaining deletion ideal is separate from this displayed support.

This recipe contains no polynomial bound, transformed dictionary or
admissibility oracle.  Its mask and character fields identify literal
original data on all allowed complete rows.  Scale budgets are separate
predicates, so the same arithmetic recipe survives every profile change.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- Only original elements and exponents are inputs.  No moving Hecke
character, selected sector, or phase calibration is a field. -/
structure OriginalMovingFactors (A : SArithmeticData K)
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P) where
  count : ℕ
  element : Fin count → NonzeroRingElements A.R
  power : Fin count → ℤ

namespace OriginalMovingFactors

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable (D : OriginalMovingFactors A P R)

def orbit (i : Fin D.count) :
    ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) :=
  Quotient.mk _ (D.element i)

def decomposition (i : Fin D.count) :
    ExteriorIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ×
      SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) :=
  (exteriorIdealSectorsEquivActualOrbits K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P).symm (D.orbit i)

theorem decomposition_orbit (i : Fin D.count) :
    decomposedIdealSectorOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P
      (D.decomposition i) = D.orbit i :=
  (exteriorIdealSectorsEquivActualOrbits K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P).apply_symm_apply (D.orbit i)

def factorIdeal (i : Fin D.count) : A.Exterior :=
  (HeckeAxiom.exteriorEquiv A).symm (D.decomposition i).1

def factorCharacter (i : Fin D.count) : HeckeCharacter K :=
  R.character (decomposedFrequencyRow K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (D.decomposition i).1 (D.decomposition i).2)

theorem factorCharacter_finite (i : Fin D.count) : FiniteOrder (D.factorCharacter i) :=
  R.finite_order _

/-- The original probe gives the exact zero-extended single-ideal
dictionary of each computed moving character.  Full ideal zeros remain. -/
theorem factor_evaluation (i : Fin D.count) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    actualOrbitSexticEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding I (D.orbit i) =
      heckeIdealCoefficient K (D.factorCharacter i) I *
        decomposedIdealRowMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          (D.decomposition i).1 I := by
  rw [← D.decomposition_orbit i]
  exact actualOrbitSexticEvaluation_decomposed_character K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R (D.decomposition i) I

def character : HeckeCharacter K := ∏ i, D.factorCharacter i ^ D.power i

theorem character_finite : FiniteOrder D.character := by
  apply finiteOrder_finset_prod K Finset.univ
  intro i _
  exact (D.factorCharacter_finite i).zpow

/-- Every original factor occurs, independently of its exponent. -/
def fullIdeal : A.Exterior :=
  GaussProductCancellation.productExterior A D.factorIdeal Finset.univ

/-- Radical of the entire original factor list.  Repeated occurrences
are charged once, while cancellations never delete displayed support. -/
def support : A.Exterior := by
  let I := D.fullIdeal
  refine ⟨CommonSupportMass.commonRadical I.val I.val,
    CommonSupportMass.commonRadical_ne_zero I.val I.val, ?_⟩
  apply top_le_iff.mp
  exact I.property.2.ge.trans (sup_le_sup_right
    (Ideal.dvd_iff_le.mp
      (CommonSupportMass.commonRadical_dvd I.val I.val I.property.1 I.property.1).1) _)

theorem support_squarefree : Squarefree D.support.val :=
  CommonSupportMass.commonRadical_squarefree D.fullIdeal.val D.fullIdeal.val

theorem support_primes :
    HeckePort.IdealMobiusDivisorSum.primeSupport D.support.val =
      HeckePort.IdealMobiusDivisorSum.primeSupport D.fullIdeal.val := by
  rw [support, CommonSupportMass.commonRadical_support, Finset.inter_self]

/-- The complete additional deletion support, including the fixed
remaining ideal.  This is the support used by the full row budget. -/
def fullMaskSupport (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) : HeckeGeneral.Analysis.NonzeroIdeal K :=
  ⟨CommonSupportMass.commonRadical (D.support.val * remaining.val)
    (D.support.val * remaining.val),
    mem_nonZeroDivisors_of_ne_zero (CommonSupportMass.commonRadical_ne_zero _ _)⟩

theorem fullMaskSupport_squarefree (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    Squarefree (D.fullMaskSupport remaining).val :=
  CommonSupportMass.commonRadical_squarefree _ _

theorem support_dvd_fullMaskSupport (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    D.support.val ∣ (D.fullMaskSupport remaining).val := by
  have hprod : D.support.val * remaining.val ≠ 0 :=
    mul_ne_zero D.support.property.1 (nonZeroDivisors.ne_zero remaining.property)
  exact CommonSupportMass.old_mask_dvd_commonRadical D.support.val
    (D.support.val * remaining.val) (D.support.val * remaining.val)
    D.support_squarefree hprod hprod (dvd_mul_right _ _) (dvd_mul_right _ _)

theorem support_norm_le_fullMaskSupport (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    A.exteriorNorm D.support ≤ idealNorm K (D.fullMaskSupport remaining) :=
  HeckePort.Moments.norm_le_of_dvd
    (nonZeroDivisors.ne_zero (D.fullMaskSupport remaining).property)
    (D.support_dvd_fullMaskSupport remaining)

def empty : OriginalMovingFactors A P R where
  count := 0
  element := Fin.elim0
  power := Fin.elim0

@[simp] theorem empty_character :
    (empty (A := A) (P := P) (R := R)).character = 1 := by
  unfold character
  exact Fin.prod_univ_zero _

@[simp] theorem empty_support :
    (empty (A := A) (P := P) (R := R)).support = unitExterior A := by
  have hfull : (empty (A := A) (P := P) (R := R)).fullIdeal.val =
      (1 : Ideal (𝓞 K)) := by
    change (∏ i : Fin 0,
      ((empty (A := A) (P := P) (R := R)).factorIdeal i).val) = 1
    exact Fin.prod_univ_zero _
  apply Subtype.ext
  change CommonSupportMass.commonRadical
    (empty (A := A) (P := P) (R := R)).fullIdeal.val
    (empty (A := A) (P := P) (R := R)).fullIdeal.val = (⊤ : Ideal (𝓞 K))
  rw [hfull, ← Ideal.one_eq_top]
  simp only [CommonSupportMass.commonRadical, HeckePort.IdealMobiusDivisorSum.primeSupport,
    UniqueFactorizationMonoid.normalizedFactors_one, Multiset.toFinset_zero,
    Finset.inter_self, Finset.prod_empty]

end OriginalMovingFactors

/-- Fixed moving arithmetic, the original finite correction, and the
literal complete common mask.  All fields precede the Fourier parameter. -/
structure CompleteMovingRowRecipe (A : SArithmeticData K)
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
    {X : Type*} (data : X → MomentData K ω ψ) where
  moving : OriginalMovingFactors A P R
  correction : HeckeCharacter K
  correction_mem : ∀ ξ, correction = 1 ∨ correction ∈ (data ξ).theta
  sector : HeckeGeneral.Analysis.NonzeroIdeal K → SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
  exterior : ∀ ξ u, (data ξ).allowedRow u →
    completeIdealIsExterior K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u
  character : ∀ ξ u, (data ξ).allowedRow u →
    (data ξ).rowCharacter u = correction * moving.character *
      completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R (sector u) u
  remaining : HeckeGeneral.Analysis.NonzeroIdeal K
  mask : ∀ ξ u I, (data ξ).commonMask u I =
    ((completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I &&
      decide (IsCoprime I moving.support.val)) && decide (IsCoprime I remaining.val))

namespace CompleteMovingRowRecipe

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {X : Type*} {data other : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)

/-- The arbitrary fixed remaining mask is not reclassified as moving
support.  Only the actual displayed factor support is charged to q. -/
def SupportBudget (Z q : ℝ) : Prop := A.exteriorNorm Q.moving.support ≤ Z ^ q

/-- A bound on the actual row times the same displayed support, for
every admitted row, including rows newly exposed by slot removal. -/
def JointBudget (Z width : ℝ) : Prop :=
  ∀ ξ u, (data ξ).allowedRow u →
    idealNorm K u * A.exteriorNorm Q.moving.support ≤ Z ^ width

/-- The complete mask budget is stronger than the moving-factor-only
budget.  It retains the fixed remaining deletion and is the condition
needed for the original reflection and engine admissibility. -/
def FullJointBudget (Z width : ℝ) : Prop :=
  ∀ ξ u, (data ξ).allowedRow u →
    idealNorm K u * idealNorm K (Q.moving.fullMaskSupport Q.remaining) ≤ Z ^ width

theorem jointBudget_of_full (Z width : ℝ) (h : Q.FullJointBudget Z width) :
    Q.JointBudget Z width := by
  intro ξ u hu
  exact (mul_le_mul_of_nonneg_left (Q.moving.support_norm_le_fullMaskSupport Q.remaining)
    (idealNorm_pos K u).le).trans (h ξ u hu)

theorem correction_finite (ξ : X) : FiniteOrder Q.correction := by
  rcases Q.correction_mem ξ with h | h
  · rw [h]
    exact IsOfFinOrder.one
  · exact (data ξ).theta_finite _ h

/-- Transport uses only literal identities and inclusion of allowed
rows.  The same elements, exponents, sectors and fixed mask survive. -/
def ofAllowedSubset
    (allowed : ∀ ξ u, (other ξ).allowedRow u → (data ξ).allowedRow u)
    (character : ∀ ξ, (other ξ).rowCharacter = (data ξ).rowCharacter)
    (mask : ∀ ξ, (other ξ).commonMask = (data ξ).commonMask)
    (theta : ∀ ξ, (other ξ).theta = (data ξ).theta) :
    CompleteMovingRowRecipe A P R other where
  moving := Q.moving
  correction := Q.correction
  correction_mem ξ := by rw [theta ξ]; exact Q.correction_mem ξ
  sector := Q.sector
  exterior ξ u hu := Q.exterior ξ u (allowed ξ u hu)
  character ξ u hu := by rw [character ξ]; exact Q.character ξ u (allowed ξ u hu)
  remaining := Q.remaining
  mask ξ u I := by rw [mask ξ]; exact Q.mask ξ u I

def clipped (a : RealParameters) (Z : ℝ) (hZ : 0 < Z) :
    CompleteMovingRowRecipe A P R (fun ξ => clipPlainData (data ξ) a Z hZ) :=
  Q.ofAllowedSubset (fun _ _ hu => hu) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

def normalized (B : X → ℝ) (hB : ∀ ξ, 0 < B ξ) :
    CompleteMovingRowRecipe A P R
      (fun ξ => normalizedMomentProfiles (data ξ) (B ξ) (hB ξ)) :=
  Q.ofAllowedSubset (fun _ _ hu => hu) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

def frozen (t : X → ℝ) :
    CompleteMovingRowRecipe A P R (fun ξ => frozenMomentProfiles (data ξ) (t ξ)) :=
  Q.ofAllowedSubset (fun _ _ hu => hu) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

def restricted (keep : ∀ ξ, Finset (Fin (data ξ).geometry.slotCount)) :
    CompleteMovingRowRecipe A P R (fun ξ => (data ξ).restrictSlots (keep ξ)) :=
  Q.ofAllowedSubset (fun _ _ hu => hu) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

def jointRows (support : HeckeGeneral.Analysis.NonzeroIdeal K → A.Exterior) (budget : ℝ) :
    CompleteMovingRowRecipe A P R (fun ξ => jointRowBudgetData (data ξ) support budget) :=
  Q.ofAllowedSubset (fun _ _ hu => hu.1) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem paired_character (ξ : X) (a : RealParameters) (Z : ℝ)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (hu : u ∈ pairedRows (data ξ) a Z) :
    (data ξ).rowCharacter u = Q.correction * Q.moving.character *
      completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R (Q.sector u) u :=
  Q.character ξ u ((((data ξ).rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1)

theorem paired_jointBudget (Z width : ℝ) (hbudget : Q.JointBudget Z width)
    (ξ : X) (a : RealParameters) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hu : u ∈ pairedRows (data ξ) a Z) :
    idealNorm K u * A.exteriorNorm Q.moving.support ≤ Z ^ width :=
  hbudget ξ u ((((data ξ).rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1)

theorem paired_fullJointBudget (Z width : ℝ) (hbudget : Q.FullJointBudget Z width)
    (ξ : X) (a : RealParameters) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hu : u ∈ pairedRows (data ξ) a Z) :
    idealNorm K u * idealNorm K (Q.moving.fullMaskSupport Q.remaining) ≤ Z ^ width :=
  hbudget ξ u ((((data ξ).rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1)

theorem ofAllowedSubset_fullJointBudget
    (allowed : ∀ ξ u, (other ξ).allowedRow u → (data ξ).allowedRow u)
    (character : ∀ ξ, (other ξ).rowCharacter = (data ξ).rowCharacter)
    (mask : ∀ ξ, (other ξ).commonMask = (data ξ).commonMask)
    (theta : ∀ ξ, (other ξ).theta = (data ξ).theta)
    (Z width : ℝ) (hbudget : Q.FullJointBudget Z width) :
    (Q.ofAllowedSubset allowed character mask theta).FullJointBudget Z width := by
  intro ξ u hu
  exact hbudget ξ u (allowed ξ u hu)

end CompleteMovingRowRecipe

namespace CompleteRowRecipe

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {X : Type*} {data : X → MomentData K ω ψ}

/-- The legacy character recipe is the empty-moving special case once
its separate original fixed-mask identity has been supplied. -/
def toMoving (Q : CompleteRowRecipe A P R data) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hmask : ∀ ξ u I, (data ξ).commonMask u I =
      (completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I &&
        decide (IsCoprime I remaining.val))) : CompleteMovingRowRecipe A P R data where
  moving := OriginalMovingFactors.empty
  correction := 1
  correction_mem _ := Or.inl rfl
  sector := Q.sector
  exterior := Q.exterior
  character ξ u hu := by
    simpa only [OriginalMovingFactors.empty_character, one_mul] using Q.character ξ u hu
  remaining := remaining
  mask ξ u I := by
    rw [hmask ξ u I, OriginalMovingFactors.empty_support]
    change (_ && _) = ((_ && decide (IsCoprime I (⊤ : Ideal (𝓞 K)))) && _)
    simp only [← Ideal.one_eq_top, isCoprime_one_right, decide_true, Bool.and_true]

end CompleteRowRecipe

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalMovingFactors.factor_evaluation
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalMovingFactors.character_finite
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.paired_jointBudget
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteRowRecipe.toMoving
