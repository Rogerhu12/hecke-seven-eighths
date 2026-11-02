import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3aValuationMaskSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SixthRootSupportBudget

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The complete exceptional mask is paid by the original frequency ideal

The active radical and the full sixth-root ideal together divide the
original common gcd. This is a prime-exponent calculation for every
positive common multiplicity. Consequently the full exceptional mask
divides the fixed bad-prime ideal times the old mask times the original
frequency ideal. No reduced or substituted residual mask is used.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

namespace T3b

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem activeSupport_mul_sixthRoot_dvd_gcd
    (C : A.GeneralArithmeticContext σ η hS) (primes : ι → ExteriorPrime A)
    (hp : Function.Injective primes) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (pattern : ι → Bool) :
    (secondOriginalMovingFactors P R C primes m n pattern).support.val *
        (secondSixthRootIdeal primes m n).val ∣
      gcd (primePowerProduct primes m).val (primePowerProduct primes n).val := by
  rw [secondOriginalMovingFactors,
    OriginalMovingFactors.singleton_support
      (secondActiveFrequencyIdeal primes m n pattern)
      (secondActiveFrequencyGenerator C primes m n pattern)
      (secondActiveFrequencyGenerator_generates C primes m n pattern) 1,
    secondActiveFrequencyIdeal, commonRadical_primePowerProduct_indicator primes hp,
    secondSixthRootIdeal, ← primePowerProduct_add]
  refine dvd_trans ?_ (primePowerProduct_min_dvd_gcd primes m n)
  apply Finset.prod_dvd_prod_of_dvd
  intro i _
  apply pow_dvd_pow
  have hi := secondSixthRootBudget_exponent (m i) (n i) (hm i) (hn i)
  change (if secondActiveExponent m n pattern i ≠ 0 then 1 else 0) +
    min (m i) (n i) / 6 ≤ min (m i) (n i)
  split_ifs <;> omega

theorem completePhaseMask_dvd_original {H : Type*}
    (C : A.GeneralArithmeticContext σ η hS)
    (Q : ActualSecondCorrelationRows A σ H ι)
    (hm : ∀ i, 0 < Q.leftMultiplicity i) (hn : ∀ i, 0 < Q.rightMultiplicity i)
    (h : Q.live) (oldMask : HeckeGeneral.Analysis.NonzeroIdeal K) :
    completePhaseMask (Q.extractedRow C h).momentIdeal
        (secondOriginalMovingFactors P R C Q.primes Q.leftMultiplicity Q.rightMultiplicity
          (actualNonunitPattern C Q.primes Q.leftMultiplicity Q.rightMultiplicity
            (Q.frequency h.val))).support.val
        (secondSixthRootIdeal Q.primes Q.leftMultiplicity Q.rightMultiplicity) oldMask ∣
      A.cS * oldMask.val * (Q.originalIdeal h.val).val := by
  let D := secondOriginalMovingFactors P R C Q.primes Q.leftMultiplicity Q.rightMultiplicity
    (actualNonunitPattern C Q.primes Q.leftMultiplicity Q.rightMultiplicity (Q.frequency h.val))
  let root := secondSixthRootIdeal Q.primes Q.leftMultiplicity Q.rightMultiplicity
  have hs : D.support.val * root.val ∣
      gcd (primePowerProduct Q.primes Q.leftMultiplicity).val
        (primePowerProduct Q.primes Q.rightMultiplicity).val :=
    activeSupport_mul_sixthRoot_dvd_gcd P R C Q.primes Q.primes_injective
      Q.leftMultiplicity Q.rightMultiplicity hm hn _
  have hfreq : (Q.extractedRow C h).ideal.val * D.support.val * root.val ∣
      (Q.originalIdeal h.val).val := by
    rw [Q.extractedRow_ideal_factor C h]
    have hd := mul_dvd_mul
      (dvd_mul_of_dvd_left hs
        (nonunitFrequencyRadical C Q.primes Q.leftMultiplicity Q.rightMultiplicity
          (Q.frequency h.val)).val)
      (dvd_rfl : (Q.extractedRow C h).ideal.val ∣ (Q.extractedRow C h).ideal.val)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hd
  have hd := mul_dvd_mul (dvd_rfl : A.cS * oldMask.val ∣ A.cS * oldMask.val) hfreq
  simpa only [completePhaseMask, ActualChildRow.momentIdeal, exteriorMomentIdeal,
    mul_assoc, mul_comm, mul_left_comm] using hd

end T3b

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p) (phases : OriginalPhaseData packet)
variable (h : packet.R.live)

theorem t3bCompleteMask_dvd_original :
    packet.t3bCompleteMask phases h ∣ (Arithmetic.data c).cS *
      (phases.mask false).val * (packet.R.originalIdeal h.val).val :=
  T3b.completePhaseMask_dvd_original (probeData K c) (momentRowCharacters K c)
    (Arithmetic.context c) packet.R packet.block.left_positive packet.block.right_positive
    h (phases.mask false)

theorem t3bCompleteMask_norm_le :
    (Ideal.absNorm (packet.t3bCompleteMask phases h) : ℝ) ≤
      (Ideal.absNorm (Arithmetic.data c).cS : ℝ) *
        (Ideal.absNorm (phases.mask false).val : ℝ) *
        (Ideal.absNorm (packet.R.originalIdeal h.val).val : ℝ) := by
  have htarget : (Arithmetic.data c).cS * (phases.mask false).val *
      (packet.R.originalIdeal h.val).val ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Arithmetic.data c).cS_ne_zero
      (nonZeroDivisors.coe_ne_zero (phases.mask false)))
      (packet.R.originalIdeal h.val).property.1
  have hnorm := HeckePort.Moments.norm_le_of_dvd htarget
    (packet.t3bCompleteMask_dvd_original phases h)
  simpa only [map_mul, Nat.cast_mul] using hnorm

/-- The S5 window is for the already selected extracted row. -/
theorem t3b_extractedRow_norm_le (hpacket : packet.Realizes) (side : Bool) :
    idealNorm K (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal ≤
      call.base ^ ((packet.nominal side).skeleton.nominalRow + 12 * p.loss) := by
  rcases hpacket with ⟨trace, geometry, raw, j, _, hgeometry, _, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).rowWindow side h

/-- Restoring the actual gcd and nonunit radical pays the original
frequency ideal; no estimate for a replacement row is used. -/
theorem t3b_originalRow_norm_le (hpacket : packet.Realizes) (side : Bool) :
    (Ideal.absNorm (packet.R.originalIdeal h.val).val : ℝ) ≤
      (Ideal.absNorm (gcd (primePowerProduct packet.R.primes packet.R.leftMultiplicity).val
        (primePowerProduct packet.R.primes packet.R.rightMultiplicity).val) : ℝ) *
      (Ideal.absNorm (nonunitFrequencyRadical (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val)).val : ℝ) *
      call.base ^ ((packet.nominal side).skeleton.nominalRow + 12 * p.loss) := by
  rw [packet.R.extractedRow_ideal_factor (Arithmetic.context c) h]
  simp only [map_mul, Nat.cast_mul]
  exact mul_le_mul_of_nonneg_left (packet.t3b_extractedRow_norm_le h hpacket side)
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem t3bCompleteMask_norm_le_geometry (hpacket : packet.Realizes) (side : Bool) :
    (Ideal.absNorm (packet.t3bCompleteMask phases h) : ℝ) ≤
      (Ideal.absNorm (Arithmetic.data c).cS : ℝ) *
      (Ideal.absNorm (phases.mask false).val : ℝ) *
      ((Ideal.absNorm (gcd (primePowerProduct packet.R.primes packet.R.leftMultiplicity).val
        (primePowerProduct packet.R.primes packet.R.rightMultiplicity).val) : ℝ) *
      (Ideal.absNorm (nonunitFrequencyRadical (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val)).val : ℝ) *
      call.base ^ ((packet.nominal side).skeleton.nominalRow + 12 * p.loss)) :=
  (packet.t3bCompleteMask_norm_le phases h).trans
    (mul_le_mul_of_nonneg_left (packet.t3b_originalRow_norm_le h hpacket side)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))

/-- Any established original mask and original row windows combine
without an additional moving-ideal norm loss. -/
theorem t3bCompleteMask_norm_le_of_original_windows
    (oldExponent rowExponent : ℝ)
    (hold : (Ideal.absNorm (phases.mask false).val : ℝ) ≤ call.base ^ oldExponent)
    (hrow : (Ideal.absNorm (packet.R.originalIdeal h.val).val : ℝ) ≤
      call.base ^ rowExponent) :
    (Ideal.absNorm (packet.t3bCompleteMask phases h) : ℝ) ≤
      (Ideal.absNorm (Arithmetic.data c).cS : ℝ) * call.base ^ (oldExponent + rowExponent) := by
  calc
    _ ≤ (Ideal.absNorm (Arithmetic.data c).cS : ℝ) *
        (Ideal.absNorm (phases.mask false).val : ℝ) *
        (Ideal.absNorm (packet.R.originalIdeal h.val).val : ℝ) :=
      packet.t3bCompleteMask_norm_le phases h
    _ ≤ (Ideal.absNorm (Arithmetic.data c).cS : ℝ) *
        call.base ^ oldExponent * call.base ^ rowExponent :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left hold (Nat.cast_nonneg _)) hrow
        (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg call.base_pos.le _))
    _ = _ := by rw [mul_assoc, ← Real.rpow_add call.base_pos]

end RawLeafPacket

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3bCompleteMask_dvd_original
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3bCompleteMask_norm_le
