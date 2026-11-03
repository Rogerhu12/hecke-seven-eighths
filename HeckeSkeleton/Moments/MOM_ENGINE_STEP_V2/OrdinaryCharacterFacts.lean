import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryAtomModel
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OriginalPhaseData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The three fixed original residue factors at each occurrence

Appending a genuine generated singleton changes the original Euler
coefficient by its residue, including all nonunit zeros. The background
character need not be unramified. The same proof applies separately to
both plain ideals and every retained prime occurrence.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryCharacters

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {k : ℕ}

/-- This operation appends the actual singleton and its complete
coprimality mask. The finite ray twists remain the original ones. -/
def twist (T : FixedChildCharacters K k) (I : A.Exterior)
    (a : A.R) (ha : A.Generates I a) : FixedChildCharacters K k :=
  { T with
    plain := T.plain * (OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1).character
    slot := fun j => T.slot j *
      (OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1).character
    mask := T.mask * CanonicalOriginalPhaseCalibration.originalCoprimeMask
      (exteriorMomentIdeal I) }

theorem twist_plain (T : FixedChildCharacters K k)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) (hJ : IsCoprime J.val A.cS) :
    sourcePlainCoefficient (twist P R T I a ha).plain
        (twist P R T I a ha).plainTwist (twist P R T I a ha).mask J =
      sourcePlainCoefficient T.plain T.plainTwist T.mask J *
        actualIdealResidue (A := A) (σ := σ) J.val a := by
  have hout := (CanonicalOriginalPhaseCalibration.outside_iff_coprime J).mpr hJ
  have he := CanonicalLiteralFirstPhase.multiply_singleton_residue
    P R hroot hemb I a ha T.plain J
  simp only [hout, true_and] at he
  change heckeIdealCoefficient K _ J * heckeIdealCoefficient K T.plainTwist J *
      (T.mask J.val * (if IsCoprime J.val I.val then 1 else 0)) =
    (heckeIdealCoefficient K T.plain J * heckeIdealCoefficient K T.plainTwist J *
      T.mask J.val) * actualIdealResidue (A := A) (σ := σ) J.val a
  calc
    _ = (heckeIdealCoefficient K _ J * (if IsCoprime J.val I.val then 1 else 0)) *
        heckeIdealCoefficient K T.plainTwist J * T.mask J.val := by ring
    _ = (heckeIdealCoefficient K T.plain J *
          actualIdealResidue (A := A) (σ := σ) J.val a) *
        heckeIdealCoefficient K T.plainTwist J * T.mask J.val := by
      exact congrArg (fun z : ℂ => z * heckeIdealCoefficient K T.plainTwist J *
        T.mask J.val) he.symm
    _ = _ := by ring

theorem twist_prime (T : FixedChildCharacters K k)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (j : Fin k) (q : HeightOneSpectrum (𝓞 K)) (hq : IsCoprime q.asIdeal A.cS) :
    sourcePrimeCoefficient ((twist P R T I a ha).slot j)
        ((twist P R T I a ha).slotTwist j) (twist P R T I a ha).mask q =
      sourcePrimeCoefficient (T.slot j) (T.slotTwist j) T.mask q *
        actualIdealResidue (A := A) (σ := σ) q.asIdeal a := by
  have hout := (CanonicalOriginalPhaseCalibration.outside_iff_coprime
    (CanonicalOriginalPhaseCalibration.primeIdeal q)).mpr hq
  have he := CanonicalLiteralFirstPhase.multiply_singleton_residue
    P R hroot hemb I a ha (T.slot j) (CanonicalOriginalPhaseCalibration.primeIdeal q)
  simp only [CanonicalOriginalPhaseCalibration.coefficient_prime, hout, true_and] at he
  change primeCoefficient K _ q * primeCoefficient K (T.slotTwist j) q *
      (T.mask q.asIdeal * (if IsCoprime q.asIdeal I.val then 1 else 0)) =
    (primeCoefficient K (T.slot j) q * primeCoefficient K (T.slotTwist j) q *
      T.mask q.asIdeal) * actualIdealResidue (A := A) (σ := σ) q.asIdeal a
  calc
    _ = (primeCoefficient K _ q * (if IsCoprime q.asIdeal I.val then 1 else 0)) *
        primeCoefficient K (T.slotTwist j) q * T.mask q.asIdeal := by ring
    _ = (primeCoefficient K (T.slot j) q *
          actualIdealResidue (A := A) (σ := σ) q.asIdeal a) *
        primeCoefficient K (T.slotTwist j) q * T.mask q.asIdeal := by
      exact congrArg (fun z : ℂ => z * primeCoefficient K (T.slotTwist j) q *
        T.mask q.asIdeal) he.symm
    _ = _ := by ring

/-- This is a product identity at one actual column. Exteriority of
the complete column proves the required condition for every factor. -/
theorem twist_bare (T : FixedChildCharacters K k)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) (J : A.Exterior)
    (hJ : J.val = allocationColumnIdeal i) :
    rawBareSourceCoefficient (twist P R T I a ha) N₁ N₂ Z length w₁ w₂ w i =
      rawBareSourceCoefficient T N₁ N₂ Z length w₁ w₂ w i *
        actualIdealResidue (A := A) (σ := σ) J.val a := by
  have hn : allocationColumnIdeal i ≠ 0 := hJ ▸ J.property.1
  have h₁ : i.1.1 ≠ 0 := by
    intro hz
    apply hn
    simp only [allocationColumnIdeal, hz, zero_mul]
  have h₂ : i.1.2 ≠ 0 := by
    intro hz
    apply hn
    simp only [allocationColumnIdeal, hz, mul_zero, zero_mul]
  have hc : IsCoprime (allocationColumnIdeal i) A.cS :=
    hJ ▸ Ideal.isCoprime_iff_sup_eq.mpr J.property.2
  have hparts : (IsCoprime i.1.1 A.cS ∧ IsCoprime i.1.2 A.cS) ∧
      ∀ j, IsCoprime (i.2 j).asIdeal A.cS := by
    simpa only [allocationColumnIdeal, IsCoprime.mul_left_iff,
      IsCoprime.prod_left_iff, Finset.mem_univ, forall_const] using hc
  have hp₁ := twist_plain P R T hroot hemb I a ha (sourceMomentIdeal i.1.1)
    (by simpa only [sourceMomentIdeal_val_of_ne_zero _ h₁] using hparts.1.1)
  have hp₂ := twist_plain P R T hroot hemb I a ha (sourceMomentIdeal i.1.2)
    (by simpa only [sourceMomentIdeal_val_of_ne_zero _ h₂] using hparts.1.2)
  have hs (j : Fin k) := twist_prime P R T hroot hemb I a ha j (i.2 j) (hparts.2 j)
  simp only [rawBareSourceCoefficient, FixedChildCharacters.bareCoefficient,
    childCartesianCoefficient, hp₁, hp₂]
  simp_rw [hs]
  simp only [sourceMomentIdeal_val_of_ne_zero _ h₁,
    sourceMomentIdeal_val_of_ne_zero _ h₂, hJ, allocationColumnIdeal,
    actualIdealResidue_ideal_mul, actualIdealResidue_prod, Finset.prod_mul_distrib]
  ring

@[simp] theorem twist_restrictSlots (T : FixedChildCharacters K k)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a) (keep : Finset (Fin k)) :
    (twist P R T I a ha).restrictSlots keep =
      twist P R (T.restrictSlots keep) I a ha := rfl

/-- Multiplying two deletion ideals gives the pointwise product of
their original complete masks, with every zero retained. -/
theorem coprimeMask_mul (M N : HeckeGeneral.Analysis.NonzeroIdeal K) :
    CanonicalOriginalPhaseCalibration.originalCoprimeMask (M * N) =
      CanonicalOriginalPhaseCalibration.originalCoprimeMask M *
        CanonicalOriginalPhaseCalibration.originalCoprimeMask N := by
  ext I
  change (if IsCoprime I (M.val * N.val) then (1 : ℂ) else 0) =
    (if IsCoprime I M.val then 1 else 0) * (if IsCoprime I N.val then 1 else 0)
  rw [IsCoprime.mul_right_iff]
  by_cases hM : IsCoprime I M.val <;> by_cases hN : IsCoprime I N.val <;> simp [hM, hN]

/-- The complete moving mask after appending a generated singleton
has exactly the same zeros as the old mask times that generated ideal. -/
theorem effectiveMask_append_singleton
    (moving : OriginalMovingFactors A P R) (remaining deletion : HeckeGeneral.Analysis.NonzeroIdeal K)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a) :
    CanonicalOriginalPhaseCalibration.originalCoprimeMask
      (exteriorMomentIdeal
        ((moving.append (OriginalMovingFactors.singleton ⟨a, ha.1⟩ 1)).effectiveFullSupport remaining) *
          deletion) =
      CanonicalOriginalPhaseCalibration.originalCoprimeMask
        (exteriorMomentIdeal (moving.effectiveFullSupport remaining) * deletion) *
          CanonicalOriginalPhaseCalibration.originalCoprimeMask (exteriorMomentIdeal I) := by
  ext J
  let E := OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1
  have hs : IsCoprime J ((moving.append E).effectiveFullSupport remaining).val ↔
      IsCoprime J (moving.effectiveFullSupport remaining).val ∧ IsCoprime J I.val := by
    change IsCoprime J ((moving.append E).fullMaskSupport
      (remainingMaskIdeal A remaining)).val ↔ _
    rw [moving.coprime_append_fullMaskSupport E]
    rw [E.coprime_support_iff_fullIdeal J]
    rw [show E.fullIdeal = I from OriginalMovingFactors.singleton_fullIdeal I a ha 1]
    rfl
  change (if IsCoprime J (((moving.append E).effectiveFullSupport remaining).val * deletion.val)
      then (1 : ℂ) else 0) =
    (if IsCoprime J ((moving.effectiveFullSupport remaining).val * deletion.val) then 1 else 0) *
      (if IsCoprime J I.val then 1 else 0)
  simp only [IsCoprime.mul_right_iff, hs]
  by_cases hm : IsCoprime J (moving.effectiveFullSupport remaining).val <;>
    by_cases hd : IsCoprime J deletion.val <;>
      by_cases hi : IsCoprime J I.val <;> simp [hm, hd, hi]

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryCharacters

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryCharacters.twist_bare
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryCharacters.effectiveMask_append_singleton
