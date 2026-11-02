import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OriginalPhaseData
import Mathlib.RingTheory.Coprime.Lemmas
import RowCharacterInputUniqueness

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original pool phase on the restored passive carrier

The only phase replacement is the proved element identity at the actual
amplifier valuation.  Its passive prime mask remains explicit until its
divisibility into the original deletion product has been established.
The old moving factors, the first element and the empty-divisor unit
are unchanged.  No equality of independently chosen Hecke characters
is used, and the background character may ramify.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePhaseBridge

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open CanonicalOriginalPhaseCalibration (originalCoprimeMask)

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p} (P : OriginalPhaseData packet)

private def gate (M I : Ideal (𝓞 K)) : ℂ := if IsCoprime I M then 1 else 0

private theorem gate_mul (M N I : Ideal (𝓞 K)) :
    gate (M * N) I = gate M I * gate N I := by
  rw [gate, IsCoprime.mul_right_iff]
  by_cases hM : IsCoprime I M <;> by_cases hN : IsCoprime I N <;>
    simp [gate, hM, hN]

private theorem gate_absorb {M N : Ideal (𝓞 K)} (hMN : M ∣ N)
    (I : Ideal (𝓞 K)) : gate M I * gate N I = gate N I := by
  by_cases hN : IsCoprime I N
  · simp [gate, hN, hN.of_isCoprime_of_dvd_right hMN]
  · simp [gate, hN]

/-- The generated ideal of the literal pool element on either side of
the active reduction.  Direct and main branches use the actual unit. -/
def poolIdeal (paid : Bool) : (Arithmetic.data c).Exterior :=
  match P.pool with
  | none => unitExterior (Arithmetic.data c)
  | some (e, q) => if paid then CanonicalLiteralPassivePhases.activeIdeal q e
      else powerIdeal q (2 * e.multiplicity)

def poolElement (paid : Bool) : (Arithmetic.data c).R :=
  match P.pool with
  | none => 1
  | some (e, q) => if paid then
      CanonicalLiteralPassivePhases.activeElement (Arithmetic.context c) q e
      else generator (Arithmetic.context c) q ^ (2 * e.multiplicity)

theorem pool_generates (paid : Bool) :
    (Arithmetic.data c).Generates (poolIdeal P paid) (poolElement P paid) := by
  cases hp : P.pool with
  | none =>
      simp only [poolIdeal, poolElement, hp]
      exact ⟨one_ne_zero, by
        simp [unitExterior, SArithmeticData.extendIdeal, Ideal.map_top]⟩
  | some qe =>
      rcases qe with ⟨e, q⟩
      simp only [poolIdeal, poolElement, hp]
      cases paid
      · exact generator_power_generates (Arithmetic.context c) q (2 * e.multiplicity)
      · exact CanonicalLiteralPassivePhases.activeElement_generates
          (Arithmetic.context c) q e

private theorem poolMoving_eq (paid : Bool) :
    P.poolMoving paid = OriginalMovingFactors.singleton
      (P := probeData K c) (R := momentRowCharacters K c)
      ⟨poolElement P paid, (pool_generates P paid).1⟩ 1 := by
  cases hp : P.pool with
  | none => simp only [OriginalPhaseData.poolMoving, poolElement, hp]
  | some qe =>
      rcases qe with ⟨e, q⟩
      cases paid <;> simp only [OriginalPhaseData.poolMoving, poolElement, hp,
        Bool.false_eq_true, if_false, if_true, CanonicalLiteralPassivePhases.activeMoving]

/-- This is one except at valuation six, where it is precisely the
actual pool prime.  It is never charged as new moving support. -/
def poolPassiveIdeal : (Arithmetic.data c).Exterior :=
  match P.pool with
  | none => unitExterior (Arithmetic.data c)
  | some (e, q) => CanonicalLiteralPassivePhases.passiveIdeal q e

theorem pool_residue (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
        J.val (poolElement P false) =
      actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
          J.val (poolElement P true) * gate (poolPassiveIdeal P).val J.val := by
  cases hp : P.pool with
  | none =>
      simp only [poolElement, poolPassiveIdeal, hp, unitExterior, gate,
        ← Ideal.one_eq_top, isCoprime_one_right, ite_true, mul_one]
  | some qe =>
      rcases qe with ⟨e, q⟩
      simp only [poolElement, poolPassiveIdeal, hp, Bool.false_eq_true,
        ite_false, ite_true, gate]
      exact CanonicalLiteralPassivePhases.residue_eq_reduced_element
        (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
        (probeData K c) (momentRowCharacters K c) rfl rfl
        (Arithmetic.context c) q e J

private theorem pool_residue_eq_coefficient (paid : Bool)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hfixed : IsCoprime J.val (Arithmetic.data c).cS)
    (hpool : IsCoprime J.val (poolIdeal P paid).val) :
    actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
        J.val (poolElement P paid) =
      heckeIdealCoefficient K (P.poolMoving paid).character J := by
  let D : OriginalMovingFactors (Arithmetic.data c)
      (probeData K c) (momentRowCharacters K c) :=
    OriginalMovingFactors.singleton
      ⟨poolElement P paid, (pool_generates P paid).1⟩ 1
  have hd : P.poolMoving paid = D := poolMoving_eq P paid
  have he := CanonicalOriginalPhaseCalibration.residue_eq_probe_evaluation
    (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
    (probeData K c) rfl rfl J (poolElement P paid)
  have hs := CanonicalLiteralFirstPhase.singleton_evaluation
    (A := Arithmetic.data c) (probeData K c) (momentRowCharacters K c)
    (poolIdeal P paid) (poolElement P paid) (pool_generates P paid) J
  have hmask :
      (if sexticIdealOutsideS K
          ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))) J ∧
          IsCoprime J.val (poolIdeal P paid).val then (1 : ℂ) else 0) = 1 :=
    if_pos ⟨(CanonicalOriginalPhaseCalibration.outside_iff_coprime
      (A := Arithmetic.data c) J).mpr hfixed, hpool⟩
  have hmask' :=
    (congrArg (fun z : ℂ => heckeIdealCoefficient K D.character J * z) hmask).trans
      (mul_one _)
  have hcharacter := congrArg
    (fun E : OriginalMovingFactors (Arithmetic.data c)
        (probeData K c) (momentRowCharacters K c) =>
      heckeIdealCoefficient K E.character J) hd
  exact he.trans (hs.trans (hmask'.trans hcharacter.symm))

/-- Global equality is proved, not postulated: the actual residue
identity determines the two finite-order characters at all primes
outside one explicitly finite set.  Merged GL(1) uniqueness then also
determines their values at the excluded primes. -/
theorem poolMoving_character : (P.poolMoving false).character = (P.poolMoving true).character := by
  let M : Ideal (𝓞 K) :=
    (poolIdeal P false).val * (poolIdeal P true).val * (poolPassiveIdeal P).val
  have hM : M ≠ 0 := mul_ne_zero
    (mul_ne_zero (poolIdeal P false).property.1 (poolIdeal P true).property.1)
    (poolPassiveIdeal P).property.1
  have hfinite :=
    AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeDivisors_finite K M hM
  let bad : Finset (HeightOneSpectrum (𝓞 K)) := (Arithmetic.data c).Sf ∪ hfinite.toFinset
  refine HeckeGeneral.Characters.RowUniquenessDraft.finiteOrder_heckeCharacter_eq_of_primeCoefficient_eq_away
    K (P.poolMoving false).character (P.poolMoving true).character
    (P.poolMoving false).character_finite (P.poolMoving true).character_finite bad ?_
  intro q hq
  have hqS : q ∉ ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))) := by
    intro h
    exact hq (Finset.mem_union_left _ h)
  have hqM : ¬q.asIdeal ∣ M := by
    intro h
    exact hq (Finset.mem_union_right _ (hfinite.mem_toFinset.mpr h))
  have hcop := isCoprime_primeIdeal_of_not_dvd K q M hqM
  have hparts :
      (IsCoprime q.asIdeal (poolIdeal P false).val ∧
        IsCoprime q.asIdeal (poolIdeal P true).val) ∧
          IsCoprime q.asIdeal (poolPassiveIdeal P).val := by
    simpa only [M, IsCoprime.mul_right_iff] using hcop
  have hfixed : IsCoprime (CanonicalOriginalPhaseCalibration.primeIdeal q).val
      (Arithmetic.data c).cS :=
    (CanonicalOriginalPhaseCalibration.outside_iff_coprime
      (A := Arithmetic.data c) _).mp
      (CanonicalOriginalPhaseCalibration.outside_prime
        (A := Arithmetic.data c) (probeData K c) q hqS)
  have hleft := pool_residue_eq_coefficient P false
    (CanonicalOriginalPhaseCalibration.primeIdeal q) hfixed hparts.1.1
  have hright := pool_residue_eq_coefficient P true
    (CanonicalOriginalPhaseCalibration.primeIdeal q) hfixed hparts.1.2
  have hgate : gate (poolPassiveIdeal P).val
      (CanonicalOriginalPhaseCalibration.primeIdeal q).val = 1 :=
    if_pos hparts.2
  have he := hleft.symm.trans
    ((pool_residue P (CanonicalOriginalPhaseCalibration.primeIdeal q)).trans
      ((congrArg₂ (fun x y : ℂ => x * y) hright hgate).trans (mul_one _)))
  exact (CanonicalOriginalPhaseCalibration.coefficient_prime
      (P.poolMoving false).character q).symm.trans
    (he.trans (CanonicalOriginalPhaseCalibration.coefficient_prime
      (P.poolMoving true).character q))

private theorem pool_coprime (I : Ideal (𝓞 K)) :
    IsCoprime I (poolIdeal P false).val ↔
      IsCoprime I (poolIdeal P true).val ∧ IsCoprime I (poolPassiveIdeal P).val := by
  cases hp : P.pool with
  | none => simp [poolIdeal, poolPassiveIdeal, hp, unitExterior]
  | some qe =>
      rcases qe with ⟨e, q⟩
      simp only [poolIdeal, poolPassiveIdeal, hp, Bool.false_eq_true, if_false, if_true,
        CanonicalLiteralPassivePhases.activeIdeal, CanonicalLiteralPassivePhases.activeExponent,
        CanonicalLiteralPassivePhases.passiveIdeal]
      cases e with
      | one =>
          change IsCoprime I (q.val.asIdeal ^ 2) ↔
            IsCoprime I (q.val.asIdeal ^ 2) ∧ IsCoprime I (1 : Ideal (𝓞 K))
          simp only [isCoprime_one_right, and_true]
      | six =>
          change IsCoprime I (q.val.asIdeal ^ 12) ↔
            IsCoprime I (1 : Ideal (𝓞 K)) ∧ IsCoprime I (q.val.asIdeal ^ 1)
          simp only [isCoprime_one_right, true_and, pow_one]
          exact IsCoprime.pow_right_iff (by decide : 0 < (12 : ℕ))
      | seven =>
          change IsCoprime I (q.val.asIdeal ^ 14) ↔
            IsCoprime I (q.val.asIdeal ^ 2) ∧ IsCoprime I (1 : Ideal (𝓞 K))
          simp only [isCoprime_one_right, and_true]
          rw [IsCoprime.pow_right_iff (by decide : 0 < (14 : ℕ)),
            IsCoprime.pow_right_iff (by decide : 0 < (2 : ℕ))]

private theorem pool_gate_split (I : Ideal (𝓞 K)) :
    gate (poolIdeal P false).val I =
      gate (poolIdeal P true).val I * gate (poolPassiveIdeal P).val I := by
  unfold gate
  rw [pool_coprime P I]
  by_cases ha : IsCoprime I (poolIdeal P true).val <;>
    by_cases hp : IsCoprime I (poolPassiveIdeal P).val <;> simp [ha, hp]

private def commonMoving : OriginalMovingFactors (Arithmetic.data c)
    (probeData K c) (momentRowCharacters K c) :=
  (call.localizedSource.source.recipe.moving.append P.firstMoving).append
    (CanonicalLiteralFixedPhases.emptyDivisorMoving
      (probeData K c) (momentRowCharacters K c))

private theorem moving_character (paid : Bool) :
    (P.moving paid).character = (commonMoving P).character * (P.poolMoving paid).character := by
  let D : OriginalMovingFactors (Arithmetic.data c)
      (probeData K c) (momentRowCharacters K c) :=
    call.localizedSource.source.recipe.moving.append P.firstMoving
  let E : OriginalMovingFactors (Arithmetic.data c)
      (probeData K c) (momentRowCharacters K c) :=
    CanonicalLiteralFixedPhases.emptyDivisorMoving
      (probeData K c) (momentRowCharacters K c)
  let Q := P.poolMoving paid
  change ((D.append Q).append E).character = (D.append E).character * Q.character
  calc
    _ = (D.append Q).character * E.character :=
      OriginalMovingFactors.append_character
        (A := Arithmetic.data c) (P := probeData K c) (R := momentRowCharacters K c)
        (D.append Q) E
    _ = (D.character * Q.character) * E.character :=
      congrArg (fun χ : HeckeCharacter K => χ * E.character)
        (OriginalMovingFactors.append_character
          (A := Arithmetic.data c) (P := probeData K c) (R := momentRowCharacters K c)
          D Q)
    _ = (D.character * E.character) * Q.character := mul_right_comm _ _ _
    _ = _ :=
      congrArg (fun χ : HeckeCharacter K => χ * Q.character)
        (OriginalMovingFactors.append_character
          (A := Arithmetic.data c) (P := probeData K c) (R := momentRowCharacters K c)
          D E).symm

/-- The same complete moving character is used by the original
exceptional predicate and by the paid child's row recipe. -/
theorem moving_character_paid : (P.moving false).character = (P.moving true).character := by
  rw [moving_character P false, moving_character P true, poolMoving_character P]

private theorem moving_coprime (paid : Bool) (I : Ideal (𝓞 K)) :
    IsCoprime I (P.moving paid).support.val ↔
      IsCoprime I (commonMoving P).support.val ∧
        IsCoprime I (poolIdeal P paid).val := by
  have hfull : (P.poolMoving paid).fullIdeal = poolIdeal P paid :=
    (congrArg
      (fun D : OriginalMovingFactors (Arithmetic.data c)
        (probeData K c) (momentRowCharacters K c) => D.fullIdeal)
      (poolMoving_eq P paid)).trans
        (OriginalMovingFactors.singleton_fullIdeal
          (A := Arithmetic.data c) (P := probeData K c) (R := momentRowCharacters K c)
          (poolIdeal P paid) (poolElement P paid) (pool_generates P paid) 1)
  have hp : IsCoprime I (P.poolMoving paid).support.val ↔
      IsCoprime I (poolIdeal P paid).val :=
    (OriginalMovingFactors.coprime_support_iff_fullIdeal
      (A := Arithmetic.data c) (P := probeData K c) (R := momentRowCharacters K c)
      (P.poolMoving paid) I).trans
        (Iff.of_eq (congrArg
          (fun J : (Arithmetic.data c).Exterior => IsCoprime I J.val) hfull))
  let D : OriginalMovingFactors (Arithmetic.data c)
      (probeData K c) (momentRowCharacters K c) :=
    call.localizedSource.source.recipe.moving.append P.firstMoving
  let E : OriginalMovingFactors (Arithmetic.data c)
      (probeData K c) (momentRowCharacters K c) :=
    CanonicalLiteralFixedPhases.emptyDivisorMoving
      (probeData K c) (momentRowCharacters K c)
  let Q := P.poolMoving paid
  have hleft : IsCoprime I (P.moving paid).support.val ↔
      (IsCoprime I D.support.val ∧ IsCoprime I Q.support.val) ∧
        IsCoprime I E.support.val :=
    (OriginalMovingFactors.coprime_append_support
      (A := Arithmetic.data c) (P := probeData K c) (R := momentRowCharacters K c)
      (D.append Q) E I).trans
        (and_congr
          (OriginalMovingFactors.coprime_append_support
            (A := Arithmetic.data c) (P := probeData K c) (R := momentRowCharacters K c)
            D Q I) Iff.rfl)
  have hright : IsCoprime I (commonMoving P).support.val ↔
      IsCoprime I D.support.val ∧ IsCoprime I E.support.val :=
    OriginalMovingFactors.coprime_append_support
      (A := Arithmetic.data c) (P := probeData K c) (R := momentRowCharacters K c)
      D E I
  constructor
  · intro h
    rcases hleft.mp h with ⟨⟨hD, hQ⟩, hE⟩
    exact ⟨hright.mpr ⟨hD, hE⟩, hp.mp hQ⟩
  · rintro ⟨hDE, hQ⟩
    rcases hright.mp hDE with ⟨hD, hE⟩
    exact hleft.mpr ⟨⟨hD, hp.mpr hQ⟩, hE⟩

private def commonGate (I : Ideal (𝓞 K)) : ℂ :=
  gate (commonMoving P).support.val I *
    gate (remainingMaskIdeal (Arithmetic.data c)
      call.localizedSource.source.recipe.remaining).val I

private def deletionGate (paid : Bool) (I : Ideal (𝓞 K)) : ℂ :=
  if paid then 1 else gate P.deletionIdeal.val I

private theorem mask_eq (paid : Bool) (I : Ideal (𝓞 K)) :
    originalCoprimeMask (P.mask paid) I =
      commonGate P I * gate (poolIdeal P paid).val I * deletionGate P paid I := by
  have hfull : IsCoprime I
      ((P.moving paid).effectiveFullSupport call.localizedSource.source.recipe.remaining).val ↔
      (IsCoprime I (commonMoving P).support.val ∧ IsCoprime I (poolIdeal P paid).val) ∧
        IsCoprime I (remainingMaskIdeal (Arithmetic.data c)
          call.localizedSource.source.recipe.remaining).val :=
    (OriginalMovingFactors.fullMaskSupport_coprime_iff
      (A := Arithmetic.data c) (P := probeData K c) (R := momentRowCharacters K c)
      (P.moving paid)
      (remainingMaskIdeal (Arithmetic.data c) call.localizedSource.source.recipe.remaining) I).trans
        (and_congr (moving_coprime P paid I) Iff.rfl)
  have hgate :
      gate ((P.moving paid).effectiveFullSupport
        call.localizedSource.source.recipe.remaining).val I =
      commonGate P I * gate (poolIdeal P paid).val I := by
    by_cases hc : IsCoprime I (commonMoving P).support.val <;>
      by_cases hp : IsCoprime I (poolIdeal P paid).val <;>
      by_cases hr : IsCoprime I (remainingMaskIdeal (Arithmetic.data c)
        call.localizedSource.source.recipe.remaining).val <;>
      simp only [gate, commonGate, hfull, hc, hp, hr, and_self, true_and, false_and,
        and_true, and_false, ite_true, ite_false, one_mul, mul_one, zero_mul, mul_zero]
  have hdelete :
      gate (if paid then (1 : HeckeGeneral.Analysis.NonzeroIdeal K) else P.deletionIdeal).val I =
        deletionGate P paid I := by
    cases paid
    · rfl
    · change (if IsCoprime I (1 : Ideal (𝓞 K)) then (1 : ℂ) else 0) = 1
      exact if_pos isCoprime_one_right
  change gate
    (((P.moving paid).effectiveFullSupport call.localizedSource.source.recipe.remaining).val *
      (if paid then (1 : HeckeGeneral.Analysis.NonzeroIdeal K) else P.deletionIdeal).val) I = _
  exact (gate_mul
    ((P.moving paid).effectiveFullSupport call.localizedSource.source.recipe.remaining).val
    (if paid then (1 : HeckeGeneral.Analysis.NonzeroIdeal K) else P.deletionIdeal).val I).trans
      (congrArg₂ (fun x y : ℂ => x * y) hgate hdelete)

/-- The full original deletion absorbs the pool's only passive mask.
Unlike the element calibration, this is an ideal identity at every
candidate ideal, including primes in the fixed exceptional set. -/
theorem mask_fullDeletion (hpassive : (poolPassiveIdeal P).val ∣ P.deletionIdeal.val)
    (I : Ideal (𝓞 K)) :
    originalCoprimeMask (P.mask false) I =
      originalCoprimeMask (P.mask true) I * originalCoprimeMask P.deletionIdeal I := by
  rw [mask_eq P false I, mask_eq P true I]
  change commonGate P I * gate (poolIdeal P false).val I * gate P.deletionIdeal.val I =
    (commonGate P I * gate (poolIdeal P true).val I * 1) * gate P.deletionIdeal.val I
  rw [pool_gate_split P I, mul_one]
  calc
    _ = (commonGate P I * gate (poolIdeal P true).val I) *
        (gate (poolPassiveIdeal P).val I * gate P.deletionIdeal.val I) := by ring
    _ = _ := by rw [gate_absorb hpassive I]

theorem coefficient_fullDeletion_global (χ : HeckeCharacter K)
    (hpassive : (poolPassiveIdeal P).val ∣ P.deletionIdeal.val)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    heckeIdealCoefficient K (χ * (P.moving false).character) J *
        originalCoprimeMask (P.mask false) J.val =
      (heckeIdealCoefficient K (χ * (P.moving true).character) J *
        originalCoprimeMask (P.mask true) J.val) * originalCoprimeMask P.deletionIdeal J.val := by
  rw [moving_character_paid P, mask_fullDeletion P hpassive J.val, mul_assoc]

private def coefficient (paid : Bool) (χ : HeckeCharacter K)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) : ℂ :=
  heckeIdealCoefficient K (χ * (P.moving paid).character) J *
    originalCoprimeMask (P.mask paid) J.val

private theorem coefficient_eq_residue (paid : Bool) (χ : HeckeCharacter K)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) (hJ : IsCoprime J.val (Arithmetic.data c).cS) :
    coefficient P paid χ J =
      heckeIdealCoefficient K (χ * (commonMoving P).character) J *
        actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
          J.val (poolElement P paid) * commonGate P J.val * deletionGate P paid J.val := by
  have hout := (CanonicalOriginalPhaseCalibration.outside_iff_coprime J).mpr hJ
  have he := CanonicalLiteralFirstPhase.multiply_singleton_residue
    (probeData K c) (momentRowCharacters K c) rfl rfl
    (poolIdeal P paid) (poolElement P paid) (pool_generates P paid)
    (χ * (commonMoving P).character) J
  rw [← poolMoving_eq P paid] at he
  simp only [hout, true_and] at he
  unfold coefficient
  rw [moving_character P paid, ← mul_assoc, mask_eq P paid J.val]
  calc
    _ = (heckeIdealCoefficient K ((χ * (commonMoving P).character) *
          (P.poolMoving paid).character) J * gate (poolIdeal P paid).val J.val) *
          commonGate P J.val * deletionGate P paid J.val := by ring
    _ = _ := by
      have heGate :
          heckeIdealCoefficient K (χ * (commonMoving P).character) J *
              actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
                J.val (poolElement P paid) =
            heckeIdealCoefficient K ((χ * (commonMoving P).character) *
              (P.poolMoving paid).character) J * gate (poolIdeal P paid).val J.val := he
      exact congrArg
        (fun z : ℂ => z * commonGate P J.val * deletionGate P paid J.val)
        heGate.symm

/-- A single ideal's exact original coefficient, including the extra
valuation-six mask.  The entire background remains arbitrary. -/
theorem coefficient_reduced (χ : HeckeCharacter K)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) (hJ : IsCoprime J.val (Arithmetic.data c).cS) :
    heckeIdealCoefficient K (χ * (P.moving false).character) J *
        originalCoprimeMask (P.mask false) J.val =
      (heckeIdealCoefficient K (χ * (P.moving true).character) J *
        originalCoprimeMask (P.mask true) J.val) *
          gate (poolPassiveIdeal P).val J.val * originalCoprimeMask P.deletionIdeal J.val := by
  change coefficient P false χ J = coefficient P true χ J *
    gate (poolPassiveIdeal P).val J.val * gate P.deletionIdeal.val J.val
  rw [coefficient_eq_residue P false χ J hJ,
    coefficient_eq_residue P true χ J hJ, pool_residue P J]
  simp only [deletionGate, Bool.false_eq_true, if_false, if_true]
  ring

theorem coefficient_fullDeletion (χ : HeckeCharacter K)
    (hpassive : (poolPassiveIdeal P).val ∣ P.deletionIdeal.val)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) (hJ : IsCoprime J.val (Arithmetic.data c).cS) :
    heckeIdealCoefficient K (χ * (P.moving false).character) J *
        originalCoprimeMask (P.mask false) J.val =
      (heckeIdealCoefficient K (χ * (P.moving true).character) J *
        originalCoprimeMask (P.mask true) J.val) * originalCoprimeMask P.deletionIdeal J.val := by
  rw [coefficient_reduced P χ J hJ, mul_assoc]
  exact congrArg (fun z : ℂ =>
    (heckeIdealCoefficient K (χ * (P.moving true).character) J *
      originalCoprimeMask (P.mask true) J.val) * z) (gate_absorb hpassive J.val)

variable {k : ℕ} (index : Fin k → Fin call.localizedData.geometry.slotCount)

theorem plain_coefficient_global (hpassive : (poolPassiveIdeal P).val ∣ P.deletionIdeal.val)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    sourcePlainCoefficient (P.characters false index).plain
        (P.characters false index).plainTwist (P.characters false index).mask J =
      sourcePlainCoefficient (P.characters true index).plain
        (P.characters true index).plainTwist (P.characters true index).mask J *
          originalCoprimeMask P.deletionIdeal J.val := by
  simpa only [OriginalPhaseData.characters, CanonicalOriginalPhaseCalibration.sourceCharacters,
    sourcePlainCoefficient, CanonicalOriginalPhaseCalibration.coefficient_one, mul_one,
    mul_assoc] using
      coefficient_fullDeletion_global P
        (call.localizedData.plainBackground * call.localizedSource.source.recipe.correction)
        hpassive J

theorem prime_coefficient_global (hpassive : (poolPassiveIdeal P).val ∣ P.deletionIdeal.val)
    (i : Fin k) (q : HeightOneSpectrum (𝓞 K)) :
    sourcePrimeCoefficient ((P.characters false index).slot i)
        ((P.characters false index).slotTwist i) (P.characters false index).mask q =
      sourcePrimeCoefficient ((P.characters true index).slot i)
        ((P.characters true index).slotTwist i) (P.characters true index).mask q *
          originalCoprimeMask P.deletionIdeal q.asIdeal := by
  have hqval : (CanonicalOriginalPhaseCalibration.primeIdeal q).val = q.asIdeal := rfl
  simpa only [OriginalPhaseData.characters, CanonicalOriginalPhaseCalibration.sourceCharacters,
    sourcePrimeCoefficient, CanonicalOriginalPhaseCalibration.coefficient_prime,
    hqval, primeCoefficient_one, mul_one, mul_assoc] using
      coefficient_fullDeletion_global P
        (call.localizedData.slotCoefficient (index i) * call.localizedSource.source.recipe.correction)
        hpassive (CanonicalOriginalPhaseCalibration.primeIdeal q)

theorem plain_coefficient (hpassive : (poolPassiveIdeal P).val ∣ P.deletionIdeal.val)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) (hJ : IsCoprime J.val (Arithmetic.data c).cS) :
    sourcePlainCoefficient (P.characters false index).plain
        (P.characters false index).plainTwist (P.characters false index).mask J =
      sourcePlainCoefficient (P.characters true index).plain
        (P.characters true index).plainTwist (P.characters true index).mask J *
          originalCoprimeMask P.deletionIdeal J.val := by
  simpa only [OriginalPhaseData.characters, CanonicalOriginalPhaseCalibration.sourceCharacters,
    sourcePlainCoefficient, CanonicalOriginalPhaseCalibration.coefficient_one, mul_one,
    mul_assoc] using
      coefficient_fullDeletion P
        (call.localizedData.plainBackground * call.localizedSource.source.recipe.correction)
        hpassive J hJ

theorem prime_coefficient (hpassive : (poolPassiveIdeal P).val ∣ P.deletionIdeal.val)
    (i : Fin k) (q : HeightOneSpectrum (𝓞 K)) (hq : IsCoprime q.asIdeal (Arithmetic.data c).cS) :
    sourcePrimeCoefficient ((P.characters false index).slot i)
        ((P.characters false index).slotTwist i) (P.characters false index).mask q =
      sourcePrimeCoefficient ((P.characters true index).slot i)
        ((P.characters true index).slotTwist i) (P.characters true index).mask q *
          originalCoprimeMask P.deletionIdeal q.asIdeal := by
  have hqval : (CanonicalOriginalPhaseCalibration.primeIdeal q).val = q.asIdeal := rfl
  simpa only [OriginalPhaseData.characters, CanonicalOriginalPhaseCalibration.sourceCharacters,
    sourcePrimeCoefficient, CanonicalOriginalPhaseCalibration.coefficient_prime,
    hqval, primeCoefficient_one, mul_one, mul_assoc] using
      coefficient_fullDeletion P
        (call.localizedData.slotCoefficient (index i) * call.localizedSource.source.recipe.correction)
        hpassive (CanonicalOriginalPhaseCalibration.primeIdeal q) hq

/-- The complete source term retains its fixed bad-prime zeros, even
when the candidate ideal is outside the restored carrier. -/
theorem plain_term (hpassive : (poolPassiveIdeal P).val ∣ P.deletionIdeal.val)
    (g h : (Arithmetic.data c).R) (w : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (N : ℝ) (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    sourcePlainTerm (σ := Arithmetic.embedding c) (P.characters false index).plain
        (P.characters false index).plainTwist (P.characters false index).mask g h w N J =
      sourcePlainTerm (σ := Arithmetic.embedding c) (P.characters true index).plain
        (P.characters true index).plainTwist (P.characters true index).mask g h w N J *
          originalCoprimeMask P.deletionIdeal J.val := by
  by_cases hJ : IsCoprime J.val (Arithmetic.data c).cS
  · simp only [sourcePlainTerm, plain_coefficient P index hpassive J hJ]
    ring
  · have hz : actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
        J.val (g * h) = 0 := dif_neg (fun hx => hJ hx.2)
    simp only [sourcePlainTerm, hz, mul_zero, zero_mul]

theorem prime_term (hpassive : (poolPassiveIdeal P).val ∣ P.deletionIdeal.val)
    (g h : (Arithmetic.data c).R) (w : HeightOneSpectrum (𝓞 K) → ℂ)
    (N : ℝ) (i : Fin k) (q : HeightOneSpectrum (𝓞 K)) :
    sourcePrimeTerm (σ := Arithmetic.embedding c) ((P.characters false index).slot i)
        ((P.characters false index).slotTwist i) (P.characters false index).mask g h w N q =
      sourcePrimeTerm (σ := Arithmetic.embedding c) ((P.characters true index).slot i)
        ((P.characters true index).slotTwist i) (P.characters true index).mask g h w N q *
          originalCoprimeMask P.deletionIdeal q.asIdeal := by
  by_cases hq : IsCoprime q.asIdeal (Arithmetic.data c).cS
  · simp only [sourcePrimeTerm, prime_coefficient P index hpassive i q hq]
    ring
  · have hz : actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
        q.asIdeal (g * h) = 0 := dif_neg (fun hx => hq hx.2)
    simp only [sourcePrimeTerm, hz, mul_zero, zero_mul]

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePhaseBridge

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePhaseBridge.pool_residue
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePhaseBridge.poolMoving_character
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePhaseBridge.moving_character_paid
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePhaseBridge.mask_fullDeletion
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePhaseBridge.plain_coefficient_global
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePhaseBridge.prime_coefficient_global
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePhaseBridge.coefficient_reduced
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePhaseBridge.coefficient_fullDeletion
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePhaseBridge.plain_term
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePhaseBridge.prime_term
