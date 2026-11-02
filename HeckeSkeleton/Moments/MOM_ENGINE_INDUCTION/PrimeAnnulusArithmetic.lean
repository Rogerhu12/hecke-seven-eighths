import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RestorationRows
import HeckeSkeleton.PrimeCancellationHecke
import HeckeSkeleton.PrimeCancellationPolynomials
import PrimeCancellationMaskCount

/-!
# Genuine arithmetic budgets for every retained prime slot

The fixed finite set of slot characters determines one conductor
constant.  Every moving row is identified with its actual complete
sextic character, and the full joint row/remaining-ideal norm budget is
retained.  The original Boolean mask therefore deletes only primes
dividing the fixed S/6 ideal times the complete row and remaining ideal.

The estimates concern the literal conductor and literal deleted-prime
set.  No prime-polynomial or moment estimate is an input.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open HeckeSkeleton.ExplicitHeckeFunctionalEquation HeckeSkeleton.HeckeConductorNorm
open HeckeSkeleton.PrimeCancellationHecke HeckeSkeleton.PrimeCancellationMoment
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]
variable {omegaCharacter psiCharacter : HeckeCharacter K}

/-- The constant is chosen from the fixed finite exceptional family,
before the model, complete row, remaining mask or slot index. -/
def primeThetaConductorConstant
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (theta : Finset (HeckeCharacter K)) : ℝ :=
  1 + ∑ chi ∈ theta, reflectionConductorConstant S chi

theorem primeThetaConductorConstant_one_le
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (theta : Finset (HeckeCharacter K)) :
    1 ≤ primeThetaConductorConstant S theta := by
  have hsum : 0 ≤ ∑ chi ∈ theta, reflectionConductorConstant S chi :=
    Finset.sum_nonneg fun chi _ => (reflectionConductorConstant_pos S chi).le
  unfold primeThetaConductorConstant
  linarith

theorem reflectionConductorConstant_le_primeTheta
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (theta : Finset (HeckeCharacter K)) (chi : HeckeCharacter K)
    (hchi : chi ∈ theta) :
    reflectionConductorConstant S chi ≤ primeThetaConductorConstant S theta := by
  have hsum := Finset.single_le_sum
    (fun eta (_ : eta ∈ theta) => (reflectionConductorConstant_pos S eta).le) hchi
  unfold primeThetaConductorConstant
  linarith

/-- The positive-slot exclusion is applied to the actual product
character.  The existence of the slot itself proves positive total
length, so there is no missing positive-slot hypothesis. -/
theorem paired_slot_finite_nonNorm_of_theta
    (d : MomentData K omegaCharacter psiCharacter) (a : RealParameters)
    (U : ℝ) (theta : Finset (HeckeCharacter K))
    (htheta : d.theta = theta)
    (hinverse : ∀ chi ∈ theta, chi⁻¹ ∈ theta)
    (hslots : ∀ j, d.slotCoefficient j ∈ theta)
    (hlen : a.z = d.geometry.totalLength)
    (u : NonzeroIdeal K) (hu : u ∈ pairedRows d a U)
    (j : Fin d.geometry.slotCount) :
    FiniteOrder (d.rowCharacter u * d.slotCoefficient j) ∧
      d.rowCharacter u * d.slotCoefficient j ≠ 1 ∧
      ∀ t : ℝ, d.rowCharacter u * d.slotCoefficient j ≠ heckeNormTwist K t := by
  have hslot : d.slotCoefficient j ∈ d.theta := by
    rw [htheta]
    exact hslots j
  have hfinite := (d.rowCharacter_finite u).mul (d.theta_finite _ hslot)
  have hne := paired_slot_character_ne_one d a U hlen.symm
    (fun k => by rw [htheta]; exact hinverse _ (hslots k)) u hu j
  exact ⟨hfinite, hne, nonNorm_of_finiteOrder_ne_one K _ hfinite hne⟩

/-- Literal deletion at a prime forces divisibility by the full fixed
and moving modulus.  The remaining ideal is charged in full. -/
theorem remainingMask_deleted_prime_dvd
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (d : MomentData K omegaCharacter psiCharacter)
    (u extra : NonzeroIdeal K)
    (hmask : ∀ I, d.commonMask u I =
      (completeIdealCommonMask K S u I && decide (IsCoprime I extra.val)))
    (p : HeightOneSpectrum (𝓞 K))
    (hdeleted : d.commonMask u p.asIdeal = false) :
    p.asIdeal ∣ fixedRowDeletionIdeal S * u.val * extra.val := by
  have hbool := remainingCommonMask_eq_deletion S u extra (primeNonzeroIdeal K p)
  change (completeIdealCommonMask K S u p.asIdeal &&
    decide (IsCoprime p.asIdeal extra.val)) =
      decide (outside (remainingRowDeletionPrimes S u extra) p.asIdeal) at hbool
  have hnot : ¬outside (remainingRowDeletionPrimes S u extra) p.asIdeal := by
    intro hout
    have htrue : d.commonMask u p.asIdeal = true := by
      rw [hmask, hbool]
      simp only [hout, decide_true]
    have hbad : (false : Bool) = true := hdeleted.symm.trans htrue
    cases hbad
  unfold outside at hnot
  push_neg at hnot
  obtain ⟨Q, hQ, hQp⟩ := hnot
  let q : HeightOneSpectrum (𝓞 K) :=
    HeightOneSpectrum.ofPrime (remainingRowDeletionPrimes_prime S u extra Q hQ)
  have heq : q = p :=
    HeckeSkeleton.PrimeCancellationIdealMask.prime_eq_of_asIdeal_dvd hQp
  have hQeq : Q = p.asIdeal := congrArg HeightOneSpectrum.asIdeal heq
  have hdiv : Q ∣ fixedRowDeletionIdeal S * u.val * extra.val :=
    (Finset.dvd_prod_of_mem (fun I : Ideal (𝓞 K) => I) hQ).trans
      (remainingRowDeletionProduct_dvd S u extra)
  simpa only [hQeq] using hdiv

private theorem completeRow_conductor_le_joint
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (probe : ProbeData K S) (rows : RowCharacterInput K S probe)
    (beta : HeckeCharacter K) (sector : SixthUnitClasses K S)
    (u : ExteriorIdeal K S) (extra : NonzeroIdeal K) :
    heckeConductorScale K (beta * completeIdealRowCharacter K S probe rows sector u.val) ≤
      reflectionConductorConstant S beta * idealNorm K u.val * idealNorm K extra := by
  let chi := beta * completeIdealRowCharacter K S probe rows sector u.val
  let E := remainingRowDeletionPrimes S u.val extra \
    primeSupport (finiteConductor K chi).val
  have hEprime : ∀ Q ∈ E, Prime Q := fun Q hQ =>
    remainingRowDeletionPrimes_prime S u.val extra Q (Finset.mem_sdiff.mp hQ).1
  have hprod : 1 ≤ (Ideal.absNorm (∏ Q ∈ E, Q) : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero
      (fun hz => subset_product_nonzero E hEprime (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hQ : 0 ≤ heckeConductorScale K chi := by
    unfold heckeConductorScale
    positivity
  calc
    _ ≤ heckeConductorScale K chi * (Ideal.absNorm (∏ Q ∈ E, Q) : ℝ) :=
      le_mul_of_one_le_right hQ hprod
    _ ≤ _ := actualReflectionScale_remainingProduct_le S probe rows beta sector u extra

/-- The actual slot conductor is uniformly polynomial in the common
base.  It uses the existing complete-row conductor divisibility theorem
through `actualReflectionScale_remainingProduct_le`. -/
theorem ReflectionRowCalibration.slot_conductor_le
    {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
    {probe : ProbeData K S} {rows : RowCharacterInput K S probe}
    {node : Node K omegaCharacter psiCharacter}
    {extra : NonzeroIdeal K → NonzeroIdeal K} {U : ℝ}
    (cal : ReflectionRowCalibration S probe rows node extra U)
    (theta : Finset (HeckeCharacter K)) (hslots : ∀ j, node.data.slotCoefficient j ∈ theta)
    (hU : 1 ≤ U) (hwidth : node.width ≤ 2)
    (u : NonzeroIdeal K) (hu : u ∈ pairedRows node.data node.parameters U)
    (j : Fin node.data.geometry.slotCount) :
    heckeConductorScale K (node.data.rowCharacter u * node.data.slotCoefficient j) ≤
      primeThetaConductorConstant S theta * U ^ (2 : ℝ) := by
  obtain ⟨v, hv, sector, hrow⟩ := cal.identify u hu
  have hscale := completeRow_conductor_le_joint S probe rows
    (node.data.slotCoefficient j) sector v (extra u)
  have hchar : node.data.rowCharacter u * node.data.slotCoefficient j =
      node.data.slotCoefficient j * completeIdealRowCharacter K S probe rows sector v.val := by
    rw [hv, ← hrow, mul_comm]
  rw [← hchar, hv] at hscale
  calc
    _ ≤ reflectionConductorConstant S (node.data.slotCoefficient j) *
        idealNorm K u * idealNorm K (extra u) := hscale
    _ = reflectionConductorConstant S (node.data.slotCoefficient j) *
        (idealNorm K u * idealNorm K (extra u)) := by ring
    _ ≤ reflectionConductorConstant S (node.data.slotCoefficient j) * U ^ node.width :=
      mul_le_mul_of_nonneg_left (cal.product_budget u hu)
        (reflectionConductorConstant_pos S _).le
    _ ≤ primeThetaConductorConstant S theta * U ^ (2 : ℝ) :=
      mul_le_mul (reflectionConductorConstant_le_primeTheta S theta _ (hslots j))
        (Real.rpow_le_rpow_of_exponent_le hU hwidth)
        (Real.rpow_nonneg (zero_le_one.trans hU) _)
        (zero_le_one.trans (primeThetaConductorConstant_one_le S theta))

theorem ReflectionRowCalibration.slot_log_conductor_le
    {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
    {probe : ProbeData K S} {rows : RowCharacterInput K S probe}
    {node : Node K omegaCharacter psiCharacter}
    {extra : NonzeroIdeal K → NonzeroIdeal K} {U : ℝ}
    (cal : ReflectionRowCalibration S probe rows node extra U)
    (theta : Finset (HeckeCharacter K)) (hslots : ∀ j, node.data.slotCoefficient j ∈ theta)
    (hU : 1 ≤ U) (hwidth : node.width ≤ 2)
    (u : NonzeroIdeal K) (hu : u ∈ pairedRows node.data node.parameters U)
    (j : Fin node.data.geometry.slotCount) :
    Real.log (heckeConductorScale K (node.data.rowCharacter u * node.data.slotCoefficient j)) ≤
      (3 + Real.log (primeThetaConductorConstant S theta)) * (1 + Real.log U) := by
  have hQ : 0 < heckeConductorScale K
      (node.data.rowCharacter u * node.data.slotCoefficient j) := by
    unfold heckeConductorScale
    apply mul_pos
    · exact Nat.cast_pos.mpr (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K))
    · exact Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors _)
  have h := logQ_le_of_norm_polynomial _ (primeThetaConductorConstant S theta)
    U U 2 hQ (primeThetaConductorConstant_one_le S theta)
    (zero_lt_one.trans_le hU) (le_refl U) hU (by norm_num)
    (cal.slot_conductor_le theta hslots hU hwidth u hu j)
  convert h using 1 <;> ring

/-- One logarithmic cost for the actual original mask and all remaining
exclusions.  Its coefficient does not depend on the model, row or pool. -/
theorem ReflectionRowCalibration.deleted_prime_count
    {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
    {probe : ProbeData K S} {rows : RowCharacterInput K S probe}
    {node : Node K omegaCharacter psiCharacter}
    {extra : NonzeroIdeal K → NonzeroIdeal K} {U : ℝ}
    (cal : ReflectionRowCalibration S probe rows node extra U)
    (hmask : ∀ u I, node.data.commonMask u I =
      (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val)))
    (hU : 1 ≤ U) (hwidth : node.width ≤ 2)
    (u : NonzeroIdeal K) (hu : u ∈ pairedRows node.data node.parameters U)
    (pool : Finset (HeightOneSpectrum (𝓞 K))) :
    ((pool.filter (fun p => node.data.commonMask u p.asIdeal = false)).card : ℝ) ≤
      ((3 + Real.log (Ideal.absNorm (fixedRowDeletionIdeal S) : ℝ)) / Real.log 2) *
        (1 + Real.log U) := by
  let D := fixedRowDeletionIdeal S * u.val * (extra u).val
  have hDzero : D ≠ ⊥ := mul_ne_zero
    (mul_ne_zero (fixedRowDeletionIdeal_ne_bot S) (nonZeroDivisors.coe_ne_zero u))
    (nonZeroDivisors.coe_ne_zero (extra u))
  have hDpos : 0 < Ideal.absNorm D :=
    Nat.pos_of_ne_zero (fun hz => hDzero (Ideal.absNorm_eq_zero_iff.mp hz))
  have hcount := PrimeCancellation.MaskCount.card_prime_divisors_le_log
    Ideal.absNorm (pool.filter (fun p => node.data.commonMask u p.asIdeal = false))
    D 2 hDpos (by norm_num)
    (fun p _ => primeNorm_ge_two K p)
    (fun p hp => remainingMask_deleted_prime_dvd S node.data u (extra u)
      (hmask u) p (Finset.mem_filter.mp hp).2)
  have hfixed : 1 ≤ (Ideal.absNorm (fixedRowDeletionIdeal S) : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero
      (fun hz => fixedRowDeletionIdeal_ne_bot S (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hnorm : (Ideal.absNorm D : ℝ) ≤
      (Ideal.absNorm (fixedRowDeletionIdeal S) : ℝ) * U ^ (2 : ℝ) := by
    calc
      _ = (Ideal.absNorm (fixedRowDeletionIdeal S) : ℝ) *
          (idealNorm K u * idealNorm K (extra u)) := by
        simp only [D, map_mul, Nat.cast_mul, idealNorm]
        ring
      _ ≤ (Ideal.absNorm (fixedRowDeletionIdeal S) : ℝ) * U ^ node.width :=
        mul_le_mul_of_nonneg_left (cal.product_budget u hu) (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hU hwidth) (Nat.cast_nonneg _)
  have hlog := logQ_le_of_norm_polynomial (Ideal.absNorm D : ℝ)
    (Ideal.absNorm (fixedRowDeletionIdeal S) : ℝ) U U 2
    (Nat.cast_pos.mpr hDpos) hfixed (zero_lt_one.trans_le hU)
    (le_refl U) hU (by norm_num) hnorm
  refine hcount.trans ((div_le_div_of_nonneg_right hlog
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le).trans_eq ?_)
  ring

end HeckeSkeleton.Moments.EngineInduction
