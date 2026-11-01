import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassivePhases
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPhaseCalibration

/-!
# Paid moving characters with the passive deletion outside the source

The first and unit factors are unchanged.  An amplifier factor is
replaced by its proved reduced active element, and the original extra
deletion together with the valuation-six prime mask is kept as a separate
finite mask.  The paid source uses only the original remaining ideal.

All identities are proved on individual ideal or prime coefficients.
On the original fixed-S gate they follow from the genuine generated
residue identities; off that gate the full source term vanishes by its
actual residue.  No equality of the two complete Hecke-character records
is assumed.  These identities precede the finite passive-mask expansion
and the selection of any new normalized child.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidCharacters

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open CanonicalLiteralPhaseCalibration
open CanonicalOriginalPhaseCalibration (originalCoprimeMask)

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {k : ℕ}

/-- Only the literal pool factor is replaced. The first and unit
elements, including their actual chosen generators, remain identical. -/
def reducedPhases (F : FixedPhases A) (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (e : AmplifierValuation) : FixedPhases A :=
  { F with
    poolIdeal := CanonicalLiteralPassivePhases.activeIdeal p e
    poolElement := CanonicalLiteralPassivePhases.activeElement C p e
    pool_generates := CanonicalLiteralPassivePhases.activeElement_generates C p e }

/-- This is expanded by finite Mobius inversion, not added to the paid
source's moving support or remaining ideal. Overlap is permitted. -/
def passiveMask (extra : HeckeGeneral.Analysis.NonzeroIdeal K)
    (p : ExteriorPrime A) (e : AmplifierValuation) :
    HeckeGeneral.Analysis.NonzeroIdeal K :=
  extra * exteriorMomentIdeal (CanonicalLiteralPassivePhases.passiveIdeal p e)

@[simp] theorem reducedPhases_poolMoving (F : FixedPhases A)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation) :
    (reducedPhases F C p e).poolMoving P R =
      CanonicalLiteralPassivePhases.activeMoving P R C p e := rfl

@[simp] theorem coprimeMask_one (I : Ideal (𝓞 K)) :
    originalCoprimeMask (1 : HeckeGeneral.Analysis.NonzeroIdeal K) I = 1 := by
  change (if IsCoprime I (1 : Ideal (𝓞 K)) then (1 : ℂ) else 0) = 1
  simp

theorem coprimeMask_mul (M N : HeckeGeneral.Analysis.NonzeroIdeal K)
    (I : Ideal (𝓞 K)) :
    originalCoprimeMask (M * N) I =
      originalCoprimeMask M I * originalCoprimeMask N I := by
  change (if IsCoprime I (M.val * N.val) then (1 : ℂ) else 0) =
    (if IsCoprime I M.val then 1 else 0) * (if IsCoprime I N.val then 1 else 0)
  rw [IsCoprime.mul_right_iff]
  by_cases hM : IsCoprime I M.val <;> by_cases hN : IsCoprime I N.val <;> simp [hM, hN]

/-- The exact three original residues in a single plain coefficient. -/
theorem applyCharacters_plain (F : FixedPhases A) (T : FixedChildCharacters K k)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (extra : HeckeGeneral.Analysis.NonzeroIdeal K)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) (hJ : IsCoprime J.val A.cS) :
    sourcePlainCoefficient (F.applyCharacters P R T extra).plain
        (F.applyCharacters P R T extra).plainTwist (F.applyCharacters P R T extra).mask J =
      sourcePlainCoefficient T.plain T.plainTwist T.mask J *
        actualIdealResidue (A := A) (σ := σ) J.val F.firstElement *
        actualIdealResidue (A := A) (σ := σ) J.val F.poolElement *
        actualIdealResidue (A := A) (σ := σ) J.val F.unitElement *
        originalCoprimeMask extra J.val := by
  rw [FixedPhases.applyCharacters, FixedChildCharacters.deleteMask_plain]
  rw [FixedChildCharacters.movingSingleton_plain P R _ hroot hemb
      F.unitIdeal F.unitElement F.unit_generates J hJ,
    FixedChildCharacters.movingSingleton_plain P R _ hroot hemb
      F.poolIdeal F.poolElement F.pool_generates J hJ,
    FixedChildCharacters.movingSingleton_plain P R _ hroot hemb
      F.firstIdeal F.firstElement F.first_generates J hJ]

theorem applyCharacters_prime (F : FixedPhases A) (T : FixedChildCharacters K k)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (extra : HeckeGeneral.Analysis.NonzeroIdeal K)
    (i : Fin k) (q : HeightOneSpectrum (𝓞 K)) (hq : IsCoprime q.asIdeal A.cS) :
    sourcePrimeCoefficient ((F.applyCharacters P R T extra).slot i)
        ((F.applyCharacters P R T extra).slotTwist i) (F.applyCharacters P R T extra).mask q =
      sourcePrimeCoefficient (T.slot i) (T.slotTwist i) T.mask q *
        actualIdealResidue (A := A) (σ := σ) q.asIdeal F.firstElement *
        actualIdealResidue (A := A) (σ := σ) q.asIdeal F.poolElement *
        actualIdealResidue (A := A) (σ := σ) q.asIdeal F.unitElement *
        originalCoprimeMask extra q.asIdeal := by
  rw [FixedPhases.applyCharacters, FixedChildCharacters.deleteMask_prime]
  rw [FixedChildCharacters.movingSingleton_prime P R _ hroot hemb
      F.unitIdeal F.unitElement F.unit_generates i q hq,
    FixedChildCharacters.movingSingleton_prime P R _ hroot hemb
      F.poolIdeal F.poolElement F.pool_generates i q hq,
    FixedChildCharacters.movingSingleton_prime P R _ hroot hemb
      F.firstIdeal F.firstElement F.first_generates i q hq]

theorem applyCharacters_plain_delete (F : FixedPhases A) (T : FixedChildCharacters K k)
    (extra J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    sourcePlainCoefficient (F.applyCharacters P R T extra).plain
        (F.applyCharacters P R T extra).plainTwist (F.applyCharacters P R T extra).mask J =
      sourcePlainCoefficient (F.applyCharacters P R T 1).plain
        (F.applyCharacters P R T 1).plainTwist (F.applyCharacters P R T 1).mask J *
        originalCoprimeMask extra J.val := by
  simp only [FixedPhases.applyCharacters, FixedChildCharacters.deleteMask_plain,
    coprimeMask_one, mul_one]

theorem applyCharacters_prime_delete (F : FixedPhases A) (T : FixedChildCharacters K k)
    (extra : HeckeGeneral.Analysis.NonzeroIdeal K) (i : Fin k)
    (q : HeightOneSpectrum (𝓞 K)) :
    sourcePrimeCoefficient ((F.applyCharacters P R T extra).slot i)
        ((F.applyCharacters P R T extra).slotTwist i) (F.applyCharacters P R T extra).mask q =
      sourcePrimeCoefficient ((F.applyCharacters P R T 1).slot i)
        ((F.applyCharacters P R T 1).slotTwist i) (F.applyCharacters P R T 1).mask q *
        originalCoprimeMask extra q.asIdeal := by
  simp only [FixedPhases.applyCharacters, FixedChildCharacters.deleteMask_prime,
    coprimeMask_one, mul_one]

/-- The amplifier reduction is proved against the actual original
generated element, without identifying whole character records. -/
theorem applyCharacters_plain_reduced (F : FixedPhases A) (T : FixedChildCharacters K k)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (extra J : HeckeGeneral.Analysis.NonzeroIdeal K) (hJ : IsCoprime J.val A.cS) :
    sourcePlainCoefficient (F.applyCharacters P R T extra).plain
        (F.applyCharacters P R T extra).plainTwist (F.applyCharacters P R T extra).mask J =
      sourcePlainCoefficient ((reducedPhases F C p e).applyCharacters P R T 1).plain
        ((reducedPhases F C p e).applyCharacters P R T 1).plainTwist
        ((reducedPhases F C p e).applyCharacters P R T 1).mask J *
        originalCoprimeMask (passiveMask extra p e) J.val := by
  rw [applyCharacters_plain P R F T hroot hemb extra J hJ,
    applyCharacters_plain P R (reducedPhases F C p e) T hroot hemb 1 J hJ]
  simp only [reducedPhases, coprimeMask_one, mul_one]
  rw [hpool, CanonicalLiteralPassivePhases.residue_eq_reduced_element P R hroot hemb C p e J,
    passiveMask, coprimeMask_mul]
  change _ = _ * (originalCoprimeMask extra J.val *
    (if IsCoprime J.val (CanonicalLiteralPassivePhases.passiveIdeal p e).val then 1 else 0))
  ring

theorem applyCharacters_prime_reduced (F : FixedPhases A) (T : FixedChildCharacters K k)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (extra : HeckeGeneral.Analysis.NonzeroIdeal K)
    (i : Fin k) (q : HeightOneSpectrum (𝓞 K)) (hq : IsCoprime q.asIdeal A.cS) :
    sourcePrimeCoefficient ((F.applyCharacters P R T extra).slot i)
        ((F.applyCharacters P R T extra).slotTwist i) (F.applyCharacters P R T extra).mask q =
      sourcePrimeCoefficient (((reducedPhases F C p e).applyCharacters P R T 1).slot i)
        (((reducedPhases F C p e).applyCharacters P R T 1).slotTwist i)
        ((reducedPhases F C p e).applyCharacters P R T 1).mask q *
        originalCoprimeMask (passiveMask extra p e) q.asIdeal := by
  rw [applyCharacters_prime P R F T hroot hemb extra i q hq,
    applyCharacters_prime P R (reducedPhases F C p e) T hroot hemb 1 i q hq]
  simp only [reducedPhases, coprimeMask_one, mul_one]
  rw [hpool, CanonicalLiteralPassivePhases.residue_eq_reduced_element P R hroot hemb C p e
    (CanonicalOriginalPhaseCalibration.primeIdeal q), passiveMask, coprimeMask_mul]
  change _ = _ * (originalCoprimeMask extra q.asIdeal *
    (if IsCoprime q.asIdeal (CanonicalLiteralPassivePhases.passiveIdeal p e).val then 1 else 0))
  ring

private theorem plain_term_of_gate (T U : FixedChildCharacters K k)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (he : ∀ J : HeckeGeneral.Analysis.NonzeroIdeal K, IsCoprime J.val A.cS →
      sourcePlainCoefficient T.plain T.plainTwist T.mask J =
        sourcePlainCoefficient U.plain U.plainTwist U.mask J * originalCoprimeMask M J.val)
    (g h : A.R) (w : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ) (N : ℝ)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    sourcePlainTerm (σ := σ) T.plain T.plainTwist T.mask g h w N J =
      sourcePlainTerm (σ := σ) U.plain U.plainTwist U.mask g h w N J *
        originalCoprimeMask M J.val := by
  by_cases hJ : IsCoprime J.val A.cS
  · simp only [sourcePlainTerm, he J hJ]
    ring
  · have hz : actualIdealResidue (A := A) (σ := σ) J.val (g * h) = 0 :=
      dif_neg (fun h => hJ h.2)
    simp only [sourcePlainTerm, hz, mul_zero, zero_mul]

private theorem prime_term_of_gate (T U : FixedChildCharacters K k)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (he : ∀ (i : Fin k) (q : HeightOneSpectrum (𝓞 K)), IsCoprime q.asIdeal A.cS →
      sourcePrimeCoefficient (T.slot i) (T.slotTwist i) T.mask q =
        sourcePrimeCoefficient (U.slot i) (U.slotTwist i) U.mask q *
          originalCoprimeMask M q.asIdeal)
    (g h : A.R) (w : HeightOneSpectrum (𝓞 K) → ℂ) (N : ℝ)
    (i : Fin k) (q : HeightOneSpectrum (𝓞 K)) :
    sourcePrimeTerm (σ := σ) (T.slot i) (T.slotTwist i) T.mask g h w N q =
      sourcePrimeTerm (σ := σ) (U.slot i) (U.slotTwist i) U.mask g h w N q *
        originalCoprimeMask M q.asIdeal := by
  by_cases hq : IsCoprime q.asIdeal A.cS
  · simp only [sourcePrimeTerm, he i q hq]
    ring
  · have hz : actualIdealResidue (A := A) (σ := σ) q.asIdeal (g * h) = 0 :=
      dif_neg (fun h => hq h.2)
    simp only [sourcePrimeTerm, hz, mul_zero, zero_mul]

section Source

variable {ω ψ : HeckeCharacter K}

/-- The canonical arithmetic source that the new child will calibrate.
Only the original remaining ideal enters its full-support mask. -/
def paidSourceCharacters (F : FixedPhases A) (parent : MomentData K ω ψ)
    (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (index : Fin k → Fin parent.geometry.slotCount) : FixedChildCharacters K k :=
  CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R oldMoving)
    correction remaining index

@[simp] theorem paidSourceCharacters_restrictSlots (F : FixedPhases A)
    (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
    (correction : HeckeCharacter K) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (index : Fin k → Fin parent.geometry.slotCount) (keep : Finset (Fin k)) :
    (paidSourceCharacters P R F parent oldMoving correction remaining index).restrictSlots keep =
      paidSourceCharacters P R F parent oldMoving correction remaining
        (fun i => index (SlotRestriction.index keep i)) := rfl

variable (F : FixedPhases A) (parent : MomentData K ω ψ)
variable (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (index : Fin k → Fin parent.geometry.slotCount)

private theorem sourceCharacters_one_plain (J : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hJ : IsCoprime J.val A.cS) :
    sourcePlainCoefficient
        (sourceCharacters P R F parent oldMoving correction remaining 1 index).plain
        (sourceCharacters P R F parent oldMoving correction remaining 1 index).plainTwist
        (sourceCharacters P R F parent oldMoving correction remaining 1 index).mask J =
      sourcePlainCoefficient
        (paidSourceCharacters P R F parent oldMoving correction remaining index).plain
        (paidSourceCharacters P R F parent oldMoving correction remaining index).plainTwist
        (paidSourceCharacters P R F parent oldMoving correction remaining index).mask J := by
  simpa only [paidSourceCharacters, mul_one] using
    CanonicalLiteralPhaseCalibration.sourceCharacters_plain_coefficient
      P R F parent oldMoving correction remaining 1 index J hJ

private theorem sourceCharacters_one_prime (i : Fin k) (q : HeightOneSpectrum (𝓞 K))
    (hq : IsCoprime q.asIdeal A.cS) :
    sourcePrimeCoefficient
        ((sourceCharacters P R F parent oldMoving correction remaining 1 index).slot i)
        ((sourceCharacters P R F parent oldMoving correction remaining 1 index).slotTwist i)
        (sourceCharacters P R F parent oldMoving correction remaining 1 index).mask q =
      sourcePrimeCoefficient
        ((paidSourceCharacters P R F parent oldMoving correction remaining index).slot i)
        ((paidSourceCharacters P R F parent oldMoving correction remaining index).slotTwist i)
        (paidSourceCharacters P R F parent oldMoving correction remaining index).mask q := by
  simpa only [paidSourceCharacters, mul_one] using
    CanonicalLiteralPhaseCalibration.sourceCharacters_prime_coefficient
      P R F parent oldMoving correction remaining 1 index i q hq

/-- Direct/main sources require only removal of the separate finite
deletion from the paid source. No phase replacement is involved. -/
theorem source_plain_delete (J : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hJ : IsCoprime J.val A.cS) :
    sourcePlainCoefficient
        (sourceCharacters P R F parent oldMoving correction remaining extra index).plain
        (sourceCharacters P R F parent oldMoving correction remaining extra index).plainTwist
        (sourceCharacters P R F parent oldMoving correction remaining extra index).mask J =
      sourcePlainCoefficient
        (paidSourceCharacters P R F parent oldMoving correction remaining index).plain
        (paidSourceCharacters P R F parent oldMoving correction remaining index).plainTwist
        (paidSourceCharacters P R F parent oldMoving correction remaining index).mask J *
        originalCoprimeMask extra J.val := by
  rw [← sourceCharacters_one_plain P R F parent oldMoving correction remaining index J hJ]
  exact applyCharacters_plain_delete P R F _ extra J

theorem source_prime_delete (i : Fin k) (q : HeightOneSpectrum (𝓞 K))
    (hq : IsCoprime q.asIdeal A.cS) :
    sourcePrimeCoefficient
        ((sourceCharacters P R F parent oldMoving correction remaining extra index).slot i)
        ((sourceCharacters P R F parent oldMoving correction remaining extra index).slotTwist i)
        (sourceCharacters P R F parent oldMoving correction remaining extra index).mask q =
      sourcePrimeCoefficient
        ((paidSourceCharacters P R F parent oldMoving correction remaining index).slot i)
        ((paidSourceCharacters P R F parent oldMoving correction remaining index).slotTwist i)
        (paidSourceCharacters P R F parent oldMoving correction remaining index).mask q *
        originalCoprimeMask extra q.asIdeal := by
  rw [← sourceCharacters_one_prime P R F parent oldMoving correction remaining index i q hq]
  exact applyCharacters_prime_delete P R F _ extra i q

theorem source_plain_reduced
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) (hJ : IsCoprime J.val A.cS) :
    sourcePlainCoefficient
        (sourceCharacters P R F parent oldMoving correction remaining extra index).plain
        (sourceCharacters P R F parent oldMoving correction remaining extra index).plainTwist
        (sourceCharacters P R F parent oldMoving correction remaining extra index).mask J =
      sourcePlainCoefficient
        (paidSourceCharacters P R (reducedPhases F C p e) parent oldMoving correction remaining index).plain
        (paidSourceCharacters P R (reducedPhases F C p e) parent oldMoving correction remaining index).plainTwist
        (paidSourceCharacters P R (reducedPhases F C p e) parent oldMoving correction remaining index).mask J *
        originalCoprimeMask (passiveMask extra p e) J.val := by
  rw [← sourceCharacters_one_plain P R (reducedPhases F C p e) parent oldMoving correction
    remaining index J hJ]
  exact applyCharacters_plain_reduced P R F _ hroot hemb C p e hpool extra J hJ

theorem source_prime_reduced
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (i : Fin k) (q : HeightOneSpectrum (𝓞 K)) (hq : IsCoprime q.asIdeal A.cS) :
    sourcePrimeCoefficient
        ((sourceCharacters P R F parent oldMoving correction remaining extra index).slot i)
        ((sourceCharacters P R F parent oldMoving correction remaining extra index).slotTwist i)
        (sourceCharacters P R F parent oldMoving correction remaining extra index).mask q =
      sourcePrimeCoefficient
        ((paidSourceCharacters P R (reducedPhases F C p e) parent oldMoving correction remaining index).slot i)
        ((paidSourceCharacters P R (reducedPhases F C p e) parent oldMoving correction remaining index).slotTwist i)
        (paidSourceCharacters P R (reducedPhases F C p e) parent oldMoving correction remaining index).mask q *
        originalCoprimeMask (passiveMask extra p e) q.asIdeal := by
  rw [← sourceCharacters_one_prime P R (reducedPhases F C p e) parent oldMoving correction
    remaining index i q hq]
  exact applyCharacters_prime_reduced P R F _ hroot hemb C p e hpool extra i q hq

/-- The direct/main single-ideal identity holds on the full smooth
support, without an exterior-ideal condition on its argument. -/
theorem source_plain_term_delete (g h : A.R)
    (w : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ) (N : ℝ)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    let old := sourceCharacters P R F parent oldMoving correction remaining extra index
    let paid := paidSourceCharacters P R F parent oldMoving correction remaining index
    sourcePlainTerm (σ := σ) old.plain old.plainTwist old.mask g h w N J =
      sourcePlainTerm (σ := σ) paid.plain paid.plainTwist paid.mask g h w N J *
        originalCoprimeMask extra J.val := by
  dsimp only
  exact plain_term_of_gate _ _ extra
    (source_plain_delete P R F parent oldMoving correction remaining extra index) g h w N J

theorem source_prime_term_delete (g h : A.R)
    (w : HeightOneSpectrum (𝓞 K) → ℂ) (N : ℝ) (i : Fin k) (q : HeightOneSpectrum (𝓞 K)) :
    let old := sourceCharacters P R F parent oldMoving correction remaining extra index
    let paid := paidSourceCharacters P R F parent oldMoving correction remaining index
    sourcePrimeTerm (σ := σ) (old.slot i) (old.slotTwist i) old.mask g h w N q =
      sourcePrimeTerm (σ := σ) (paid.slot i) (paid.slotTwist i) paid.mask g h w N q *
        originalCoprimeMask extra q.asIdeal := by
  dsimp only
  exact prime_term_of_gate _ _ extra
    (source_prime_delete P R F parent oldMoving correction remaining extra index) g h w N i q

/-- The reduced amplifier source and its entire passive deletion are
identified on every nonzero ideal before a new child is constructed. -/
theorem source_plain_term_reduced
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (g h : A.R) (w : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ) (N : ℝ)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    let old := sourceCharacters P R F parent oldMoving correction remaining extra index
    let paid := paidSourceCharacters P R (reducedPhases F C p e) parent oldMoving correction
      remaining index
    sourcePlainTerm (σ := σ) old.plain old.plainTwist old.mask g h w N J =
      sourcePlainTerm (σ := σ) paid.plain paid.plainTwist paid.mask g h w N J *
        originalCoprimeMask (passiveMask extra p e) J.val := by
  dsimp only
  exact plain_term_of_gate _ _ (passiveMask extra p e)
    (source_plain_reduced P R F parent oldMoving correction remaining extra index
      hroot hemb C p e hpool) g h w N J

theorem source_prime_term_reduced
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (g h : A.R) (w : HeightOneSpectrum (𝓞 K) → ℂ) (N : ℝ)
    (i : Fin k) (q : HeightOneSpectrum (𝓞 K)) :
    let old := sourceCharacters P R F parent oldMoving correction remaining extra index
    let paid := paidSourceCharacters P R (reducedPhases F C p e) parent oldMoving correction
      remaining index
    sourcePrimeTerm (σ := σ) (old.slot i) (old.slotTwist i) old.mask g h w N q =
      sourcePrimeTerm (σ := σ) (paid.slot i) (paid.slotTwist i) paid.mask g h w N q *
        originalCoprimeMask (passiveMask extra p e) q.asIdeal := by
  dsimp only
  exact prime_term_of_gate _ _ (passiveMask extra p e)
    (source_prime_reduced P R F parent oldMoving correction remaining extra index
      hroot hemb C p e hpool) g h w N i q

private def calibrationOfGate
    {T U : FixedChildCharacters K k} (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hray : U.fixedRay = T.fixedRay)
    (hplain : ∀ J : HeckeGeneral.Analysis.NonzeroIdeal K, IsCoprime J.val A.cS →
      sourcePlainCoefficient T.plain T.plainTwist T.mask J =
        sourcePlainCoefficient U.plain U.plainTwist U.mask J * originalCoprimeMask M J.val)
    (hprime : ∀ (i : Fin k) (q : HeightOneSpectrum (𝓞 K)), IsCoprime q.asIdeal A.cS →
      sourcePrimeCoefficient (T.slot i) (T.slotTwist i) T.mask q =
        sourcePrimeCoefficient (U.slot i) (U.slotTwist i) U.mask q *
          originalCoprimeMask M q.asIdeal)
    {d : MomentData K ω ψ} {count : d.geometry.slotCount = k}
    {u : HeckeGeneral.Analysis.NonzeroIdeal K} {g h : A.R}
    (original : T.Calibration (σ := σ) d count u g h) :
    (U.deleteMask M).Calibration (σ := σ) d count u g h where
  fixedRay_mem_theta θ hθ := by
    change θ ∈ U.fixedRay at hθ
    exact original.fixedRay_mem_theta θ (hray ▸ hθ)
  plain J := by
    rw [original.plain J]
    by_cases hJ : IsCoprime J.val A.cS
    · rw [hplain J hJ, U.deleteMask_plain M J]
    · have hz : actualIdealResidue (A := A) (σ := σ) J.val g = 0 :=
        dif_neg (fun h => hJ h.2)
      simp only [hz, mul_zero, zero_mul]
  slot i q := by
    rw [original.slot i q]
    by_cases hq : IsCoprime q.asIdeal A.cS
    · rw [hprime (Fin.cast count i) q hq, U.deleteMask_prime M (Fin.cast count i) q]
    · have hz : actualIdealResidue (A := A) (σ := σ) q.asIdeal g = 0 :=
        dif_neg (fun h => hq h.2)
      simp only [hz, mul_zero, zero_mul]

/-- The old actual atom dictionary constructs the masked paid
dictionary on exactly the same data and extracted row. -/
def calibration_delete (d : MomentData K ω ψ) (count : d.geometry.slotCount = k)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (g h : A.R)
    (original : (sourceCharacters P R F parent oldMoving correction remaining extra index).Calibration
      (σ := σ) d count u g h) :
    ((paidSourceCharacters P R F parent oldMoving correction remaining index).deleteMask extra).Calibration
      (σ := σ) d count u g h :=
  calibrationOfGate extra rfl
    (source_plain_delete P R F parent oldMoving correction remaining extra index)
    (source_prime_delete P R F parent oldMoving correction remaining extra index) original

/-- Pool reduction supplies the same masked calibration without a
whole-character or whole-polynomial premise. -/
def calibration_reduced
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (d : MomentData K ω ψ) (count : d.geometry.slotCount = k)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (g h : A.R)
    (original : (sourceCharacters P R F parent oldMoving correction remaining extra index).Calibration
      (σ := σ) d count u g h) :
    ((paidSourceCharacters P R (reducedPhases F C p e) parent oldMoving correction remaining index).deleteMask
      (passiveMask extra p e)).Calibration (σ := σ) d count u g h :=
  calibrationOfGate (passiveMask extra p e) rfl
    (source_plain_reduced P R F parent oldMoving correction remaining extra index hroot hemb C p e hpool)
    (source_prime_reduced P R F parent oldMoving correction remaining extra index hroot hemb C p e hpool)
    original

end Source
end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidCharacters

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidCharacters.applyCharacters_plain_reduced
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidCharacters.applyCharacters_prime_reduced
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidCharacters.source_plain_delete
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidCharacters.source_prime_delete
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidCharacters.source_plain_reduced
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidCharacters.source_prime_reduced
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidCharacters.source_plain_term_delete
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidCharacters.source_prime_term_delete
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidCharacters.source_plain_term_reduced
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidCharacters.source_prime_term_reduced
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidCharacters.calibration_delete
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidCharacters.calibration_reduced
