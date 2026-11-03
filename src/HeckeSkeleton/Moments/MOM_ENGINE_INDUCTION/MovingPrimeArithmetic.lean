import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MovingRecipeConductor
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MovingRecipeArithmetic
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.PrimeAnnulusArithmetic

/-!
# Prime conductor and deletion budgets for the actual moving recipe

The finite family below contains the slot character times the canonical
fixed correction. It is chosen before the moving S-integers, their
integer powers, the remaining ideal and every row or scale. Including
the identity correction handles the canonical recipe literally, without
assuming that an arbitrary finite theta set contains one or is closed
under multiplication. For the actual canonical theta set this is its
finite product family.

The moving characters themselves are never inserted in that fixed
family. Their conductor and the actual deleted-prime count are paid by
the same full joint support budget. No prime-polynomial bound is input.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.MovingRecipe

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeSkeleton.PrimeCancellationHecke HeckeSkeleton.PrimeCancellationMoment
open EngineStep
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]
variable {omegaCharacter psiCharacter : HeckeCharacter K}

def primeBackgrounds (theta : Finset (HeckeCharacter K)) : Finset (HeckeCharacter K) :=
  ((insert 1 theta) ×ˢ theta).image (fun pair => pair.2 * pair.1)

theorem slot_correction_mem_primeBackgrounds
    {A : DedekindZetaZeroFree.SArithmeticData K}
    {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
    {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
    {X : Type*} {data : X → MomentData K omegaCharacter psiCharacter}
    (Q : CompleteMovingRowRecipe A P R data) (xi : X)
    (theta : Finset (HeckeCharacter K)) (htheta : (data xi).theta = theta)
    (hslots : ∀ j, (data xi).slotCoefficient j ∈ theta)
    (j : Fin (data xi).geometry.slotCount) :
    (data xi).slotCoefficient j * Q.correction ∈ primeBackgrounds theta := by
  have hc : Q.correction ∈ insert 1 theta := by
    rcases Q.correction_mem xi with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr (htheta ▸ h))
  exact Finset.mem_image.mpr
    ⟨(Q.correction, (data xi).slotCoefficient j),
      Finset.mem_product.mpr ⟨hc, hslots j⟩, rfl⟩

variable {A : DedekindZetaZeroFree.SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {X : Type*} {data : X → MomentData K omegaCharacter psiCharacter}

theorem slot_conductor_le
    (Q : CompleteMovingRowRecipe A P R data) (xi : X)
    (a : RealParameters) (U width : ℝ) (hbudget : Q.FullJointBudget U width)
    (theta : Finset (HeckeCharacter K)) (htheta : (data xi).theta = theta)
    (hslots : ∀ j, (data xi).slotCoefficient j ∈ theta)
    (hU : 1 ≤ U) (hwidth : width ≤ 2)
    (u : NonzeroIdeal K) (hu : u ∈ pairedRows (data xi) a U)
    (j : Fin (data xi).geometry.slotCount) :
    heckeConductorScale K ((data xi).rowCharacter u * (data xi).slotCoefficient j) ≤
      primeThetaConductorConstant (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (primeBackgrounds theta) * U ^ (2 : ℝ) := by
  have hallowed : (data xi).allowedRow u :=
    (((data xi).rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1
  have hscale := row_scale_le_fullJointBudget Q U width hbudget xi
    ((data xi).slotCoefficient j) u hallowed
  have hconstant := reflectionConductorConstant_le_primeTheta
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (primeBackgrounds theta)
    ((data xi).slotCoefficient j * Q.correction)
    (slot_correction_mem_primeBackgrounds Q xi theta htheta hslots j)
  calc
    _ = heckeConductorScale K ((data xi).slotCoefficient j * (data xi).rowCharacter u) :=
      congrArg (heckeConductorScale K) (mul_comm _ _)
    _ ≤ reflectionConductorConstant (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        ((data xi).slotCoefficient j * Q.correction) * U ^ width := hscale
    _ ≤ _ := mul_le_mul hconstant
      (Real.rpow_le_rpow_of_exponent_le hU hwidth)
      (Real.rpow_nonneg (zero_le_one.trans hU) _)
      (zero_le_one.trans (primeThetaConductorConstant_one_le
        (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (primeBackgrounds theta)))

theorem slot_log_conductor_le
    (Q : CompleteMovingRowRecipe A P R data) (xi : X)
    (a : RealParameters) (U width : ℝ) (hbudget : Q.FullJointBudget U width)
    (theta : Finset (HeckeCharacter K)) (htheta : (data xi).theta = theta)
    (hslots : ∀ j, (data xi).slotCoefficient j ∈ theta)
    (hU : 1 ≤ U) (hwidth : width ≤ 2)
    (u : NonzeroIdeal K) (hu : u ∈ pairedRows (data xi) a U)
    (j : Fin (data xi).geometry.slotCount) :
    Real.log (heckeConductorScale K
      ((data xi).rowCharacter u * (data xi).slotCoefficient j)) ≤
      (3 + Real.log (primeThetaConductorConstant
        (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (primeBackgrounds theta))) *
          (1 + Real.log U) := by
  have hQ : 0 < heckeConductorScale K
      ((data xi).rowCharacter u * (data xi).slotCoefficient j) := by
    unfold heckeConductorScale
    apply mul_pos
    · exact Nat.cast_pos.mpr (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K))
    · exact Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors _)
  have h := logQ_le_of_norm_polynomial _
    (primeThetaConductorConstant (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (primeBackgrounds theta)) U U 2 hQ
    (primeThetaConductorConstant_one_le (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (primeBackgrounds theta))
    (zero_lt_one.trans_le hU) (le_refl U) hU (by norm_num)
    (slot_conductor_le Q xi a U width hbudget theta htheta hslots hU hwidth u hu j)
  convert h using 1 <;> ring

/-- The literal nested moving mask is rewritten to its exact full
support before counting. In particular the fixed remaining ideal is
not assumed to divide its radical, and it is not charged twice. -/
theorem deleted_prime_count
    (Q : CompleteMovingRowRecipe A P R data) (xi : X)
    (a : RealParameters) (U width : ℝ) (hbudget : Q.FullJointBudget U width)
    (hU : 1 ≤ U) (hwidth : width ≤ 2)
    (u : NonzeroIdeal K) (hu : u ∈ pairedRows (data xi) a U)
    (pool : Finset (HeightOneSpectrum (𝓞 K))) :
    ((pool.filter (fun p => (data xi).commonMask u p.asIdeal = false)).card : ℝ) ≤
      ((3 + Real.log (Ideal.absNorm
        (fixedRowDeletionIdeal (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) : ℝ)) /
          Real.log 2) * (1 + Real.log U) := by
  let extra := Q.moving.fullMaskSupport Q.remaining
  let D := fixedRowDeletionIdeal (A.Sf : Set (HeightOneSpectrum (𝓞 K))) * u.val * extra.val
  have hDzero : D ≠ ⊥ := mul_ne_zero
    (mul_ne_zero (fixedRowDeletionIdeal_ne_bot (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (nonZeroDivisors.coe_ne_zero u)) (nonZeroDivisors.coe_ne_zero extra)
  have hDpos : 0 < Ideal.absNorm D :=
    Nat.pos_of_ne_zero (fun hz => hDzero (Ideal.absNorm_eq_zero_iff.mp hz))
  have hcount := PrimeCancellation.MaskCount.card_prime_divisors_le_log
    Ideal.absNorm (pool.filter (fun p => (data xi).commonMask u p.asIdeal = false))
    D 2 hDpos (by norm_num)
    (fun p _ => primeNorm_ge_two K p)
    (fun p hp => remainingMask_deleted_prime_dvd
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (data xi) u extra
      (completeMovingRowRecipe_mask Q xi u) p (Finset.mem_filter.mp hp).2)
  have hfixed : 1 ≤ (Ideal.absNorm
      (fixedRowDeletionIdeal (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero
      (fun hz => fixedRowDeletionIdeal_ne_bot (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hnorm : (Ideal.absNorm D : ℝ) ≤
      (Ideal.absNorm (fixedRowDeletionIdeal (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) : ℝ) *
        U ^ (2 : ℝ) := by
    calc
      _ = (Ideal.absNorm (fixedRowDeletionIdeal
          (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) : ℝ) *
            (idealNorm K u * idealNorm K extra) := by
        simp only [D, map_mul, Nat.cast_mul, idealNorm]
        ring
      _ ≤ (Ideal.absNorm (fixedRowDeletionIdeal
          (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) : ℝ) * U ^ width :=
        mul_le_mul_of_nonneg_left (Q.paired_fullJointBudget U width hbudget xi a u hu)
          (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hU hwidth) (Nat.cast_nonneg _)
  have hlog := logQ_le_of_norm_polynomial (Ideal.absNorm D : ℝ)
    (Ideal.absNorm (fixedRowDeletionIdeal (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) : ℝ)
    U U 2 (Nat.cast_pos.mpr hDpos) hfixed (zero_lt_one.trans_le hU)
    (le_refl U) hU (by norm_num) hnorm
  refine hcount.trans ((div_le_div_of_nonneg_right hlog
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le).trans_eq ?_)
  ring

end HeckeSkeleton.Moments.EngineInduction.MovingRecipe
