import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CompleteMovingRowRecipe
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MovingRowConductor

/-!
# Conductors of the canonical original moving factors

This file consumes the exact `CompleteMovingRowRecipe` published by the
single-step producer. Its factors are the original S-integers, not
arbitrary moving characters. Each character is identified with the
complete ideal and sector computed by that recipe. The radical of each
factor divides the displayed support even when its exponent is zero.

`SupportBudget` bounds the moving character by the original q budget.
The full row bounds instead consume `FullJointBudget`, which pays for
the radical of the displayed support and the fixed remaining mask
together with the original row u. No exponent or factor-count norm loss
is introduced, and no analytic or polynomial estimate is a premise.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.MovingRecipe

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic.ConductorNormDraft
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckePort.IdealMobiusDivisorSum
open EngineStep
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]
variable {omegaCharacter psiCharacter : HeckeCharacter K}
variable {A : DedekindZetaZeroFree.SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

theorem factorCharacter_eq_complete (D : OriginalMovingFactors A P R)
    (i : Fin D.count) :
    D.factorCharacter i =
      completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R
        (D.decomposition i).2 (D.decomposition i).1.val := by
  rw [completeIdealRowCharacter_exterior]
  rfl

/-- The genuine ideal radical is compared with the actual support
product through its prime-ideal description. No identification of the
two notions of radical is assumed. -/
theorem factor_radical_dvd_support (D : OriginalMovingFactors A P R)
    (i : Fin D.count) :
    (nonzeroIdealRadical K (D.decomposition i).1.val).val ∣ D.support.val := by
  apply Ideal.dvd_iff_le.mpr
  change D.support.val ≤ ((D.decomposition i).1.val.val).radical
  rw [Ideal.radical_eq_sInf]
  apply le_sInf
  intro J hJ
  have hfactor : (D.factorIdeal i).val ∣ D.fullIdeal.val := by
    change (D.factorIdeal i).val ∣ ∏ j, (D.factorIdeal j).val
    exact Finset.dvd_prod_of_mem (fun j => (D.factorIdeal j).val) (Finset.mem_univ i)
  have hfactor_le : (D.factorIdeal i).val ≤ J := hJ.1
  have hfull_le : D.fullIdeal.val ≤ J :=
    (Ideal.dvd_iff_le.mp hfactor).trans hfactor_le
  have hmem : J ∈ primeSupport D.fullIdeal.val :=
    Multiset.mem_toFinset.mpr
      ((Ideal.mem_normalizedFactors_iff D.fullIdeal.property.1).mpr ⟨hJ.2, hfull_le⟩)
  change (∏ Q ∈ primeSupport D.fullIdeal.val ∩ primeSupport D.fullIdeal.val, Q) ≤ J
  rw [Finset.inter_self]
  exact Ideal.dvd_iff_le.mp (Finset.dvd_prod_of_mem (fun Q : Ideal (𝓞 K) => Q) hmem)

theorem factor_radical_dvd_fullMaskSupport (D : OriginalMovingFactors A P R)
    (remaining : NonzeroIdeal K) (i : Fin D.count) :
    (nonzeroIdealRadical K (D.decomposition i).1.val).val ∣
      (D.fullMaskSupport remaining).val :=
  (factor_radical_dvd_support D i).trans (D.support_dvd_fullMaskSupport remaining)

theorem character_eq_complete_product (D : OriginalMovingFactors A P R) :
    D.character = ∏ i,
      completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R
        (D.decomposition i).2 (D.decomposition i).1.val ^ D.power i := by
  unfold OriginalMovingFactors.character
  apply Finset.prod_congr rfl
  intro i _
  rw [factorCharacter_eq_complete]

variable {X : Type*} {data : X → MomentData K omegaCharacter psiCharacter}

/-- The original q budget bounds the moving conductor without charging
integer multiplicities or the number of original factors. -/
theorem moving_conductor_norm_le
    (Q : CompleteMovingRowRecipe A P R data) (U q : ℝ)
    (hbudget : Q.SupportBudget U q) :
    (Ideal.absNorm (finiteConductor K Q.moving.character).val : ℝ) ≤
      (Ideal.absNorm (sexticSConductorBudgetIdeal K
        (A.Sf : Set (HeightOneSpectrum (𝓞 K)))).val : ℝ) * U ^ q := by
  let displayed : NonzeroIdeal K :=
    ⟨Q.moving.support.val, mem_nonZeroDivisors_of_ne_zero Q.moving.support.property.1⟩
  have hdiv := completeMovingCharacter_conductor_dvd
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R Finset.univ
    (fun i => (Q.moving.decomposition i).1)
    (fun i => (Q.moving.decomposition i).2) Q.moving.power displayed
    (fun i _ => factor_radical_dvd_support Q.moving i)
  rw [← character_eq_complete_product Q.moving] at hdiv
  have hn := Nat.le_of_dvd
    (Ideal.absNorm_pos_of_nonZeroDivisors
      (sexticSConductorBudgetIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) * displayed))
    (map_dvd Ideal.absNorm hdiv)
  simp only [Submonoid.coe_mul, map_mul, displayed] at hn
  have hreal : (Ideal.absNorm (finiteConductor K Q.moving.character).val : ℝ) ≤
      (Ideal.absNorm (sexticSConductorBudgetIdeal K
        (A.Sf : Set (HeightOneSpectrum (𝓞 K)))).val : ℝ) *
          A.exteriorNorm Q.moving.support := by
    change (Ideal.absNorm (finiteConductor K Q.moving.character).val : ℝ) ≤
      (Ideal.absNorm (sexticSConductorBudgetIdeal K
        (A.Sf : Set (HeightOneSpectrum (𝓞 K)))).val : ℝ) *
          (Ideal.absNorm Q.moving.support.val : ℝ)
    exact_mod_cast hn
  exact hreal.trans (mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg _))

/-- A fixed background is separated from the fixed finite correction.
The displayed moving factors and residual row still use one S budget. -/
theorem row_conductor_dvd
    (Q : CompleteMovingRowRecipe A P R data) (xi : X)
    (beta : HeckeCharacter K) (u : NonzeroIdeal K)
    (hu : (data xi).allowedRow u) :
    (finiteConductor K (beta * (data xi).rowCharacter u)).val ∣
      (finiteConductor K (beta * Q.correction) *
        sexticSConductorBudgetIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) *
          Q.moving.fullMaskSupport Q.remaining * u).val := by
  let v : ExteriorIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) :=
    ⟨u, Q.exterior xi u hu⟩
  have hchar : beta * (data xi).rowCharacter u =
      (beta * Q.correction) * ((∏ i,
        completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R
          (Q.moving.decomposition i).2 (Q.moving.decomposition i).1.val ^ Q.moving.power i) *
            completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
              P R (Q.sector u) v.val) := by
    rw [Q.character xi u hu, character_eq_complete_product]
    simp only [mul_assoc, v]
  rw [hchar]
  exact completeMovingRowCharacter_conductor_dvd
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R (beta * Q.correction)
    Finset.univ (fun i => (Q.moving.decomposition i).1)
    (fun i => (Q.moving.decomposition i).2) Q.moving.power
    (Q.moving.fullMaskSupport Q.remaining)
    (fun i _ => factor_radical_dvd_fullMaskSupport Q.moving Q.remaining i)
    (Q.sector u) v

set_option maxHeartbeats 800000 in
/-- The actual FE scale is linear in the one full mask support and
the original row. The fixed correction occurs only in the fixed
background constant, and never enlarges the moving norm exponent. -/
theorem row_scale_le
    (Q : CompleteMovingRowRecipe A P R data) (xi : X)
    (beta : HeckeCharacter K) (u : NonzeroIdeal K)
    (hu : (data xi).allowedRow u) :
    heckeConductorScale K (beta * (data xi).rowCharacter u) ≤
      reflectionConductorConstant (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (beta * Q.correction) * idealNorm K u *
          idealNorm K (Q.moving.fullMaskSupport Q.remaining) := by
  have hn := Nat.le_of_dvd
    (Ideal.absNorm_pos_of_nonZeroDivisors
      (finiteConductor K (beta * Q.correction) *
        sexticSConductorBudgetIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) *
          Q.moving.fullMaskSupport Q.remaining * u))
    (map_dvd Ideal.absNorm (row_conductor_dvd Q xi beta u hu))
  simp only [Submonoid.coe_mul, map_mul] at hn
  have hreal : (Ideal.absNorm (finiteConductor K (beta * (data xi).rowCharacter u)).val : ℝ) ≤
      (Ideal.absNorm (finiteConductor K (beta * Q.correction)).val : ℝ) *
        (Ideal.absNorm (sexticSConductorBudgetIdeal K
          (A.Sf : Set (HeightOneSpectrum (𝓞 K)))).val : ℝ) *
            idealNorm K (Q.moving.fullMaskSupport Q.remaining) * idealNorm K u := by
    dsimp only [idealNorm]
    exact_mod_cast hn
  have hfixed : 1 ≤ (Ideal.absNorm
      (fixedRowDeletionIdeal (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero
      (fun hz => fixedRowDeletionIdeal_ne_bot (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hmass : 0 ≤ ((NumberField.discr K).natAbs : ℝ) *
      (Ideal.absNorm (finiteConductor K (beta * Q.correction)).val : ℝ) *
        (Ideal.absNorm (sexticSConductorBudgetIdeal K
          (A.Sf : Set (HeightOneSpectrum (𝓞 K)))).val : ℝ) *
            idealNorm K u * idealNorm K (Q.moving.fullMaskSupport Q.remaining) := by
    have huN := (idealNorm_pos K u).le
    have hDN := (idealNorm_pos K (Q.moving.fullMaskSupport Q.remaining)).le
    positivity
  have hmul := mul_le_mul_of_nonneg_left hreal
    (Nat.cast_nonneg (NumberField.discr K).natAbs : (0 : ℝ) ≤ _)
  calc
    _ ≤ ((NumberField.discr K).natAbs : ℝ) *
        (Ideal.absNorm (finiteConductor K (beta * Q.correction)).val : ℝ) *
          (Ideal.absNorm (sexticSConductorBudgetIdeal K
            (A.Sf : Set (HeightOneSpectrum (𝓞 K)))).val : ℝ) *
              idealNorm K u * idealNorm K (Q.moving.fullMaskSupport Q.remaining) := by
      simpa only [heckeConductorScale, mul_assoc, mul_left_comm, mul_comm] using hmul
    _ ≤ _ := by
      have h := le_mul_of_one_le_right hmass hfixed
      simpa only [reflectionConductorConstant, reflectionConductorBudget,
        map_mul, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using h

theorem row_scale_le_fullJointBudget
    (Q : CompleteMovingRowRecipe A P R data) (U width : ℝ)
    (hbudget : Q.FullJointBudget U width)
    (xi : X) (beta : HeckeCharacter K) (u : NonzeroIdeal K)
    (hu : (data xi).allowedRow u) :
    heckeConductorScale K (beta * (data xi).rowCharacter u) ≤
      reflectionConductorConstant (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (beta * Q.correction) * U ^ width := by
  calc
    _ ≤ reflectionConductorConstant (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (beta * Q.correction) * idealNorm K u *
          idealNorm K (Q.moving.fullMaskSupport Q.remaining) := row_scale_le Q xi beta u hu
    _ = reflectionConductorConstant (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (beta * Q.correction) *
          (idealNorm K u * idealNorm K (Q.moving.fullMaskSupport Q.remaining)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hbudget xi u hu)
      (reflectionConductorConstant_pos (A.Sf : Set (HeightOneSpectrum (𝓞 K))) _).le

end HeckeSkeleton.Moments.EngineInduction.MovingRecipe
