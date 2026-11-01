import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentArithmeticAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CompleteRowRecipe
import HeckeSkeleton.Moments.MOM_BASE.PairedPhases
import HeckeGeneral.Analysis.ActualMomentPolynomialBridges
import ArithmeticFrequencyRowConductor
import RowCharacterCanonicalUniqueness

/-!
# Actual orbital atoms from complete rows and a fixed remaining ideal

The canonical interfaces are those of immutable MOM_ENGINE_STEP commit
`fd6acc7066706d250730aed6a100e05d60f1b8f6`. The original probe, supplied
row-character input, complete ideal and rowwise unit sector are retained.
Every phase is the actual zero-extended orbital sextic evaluation on the
original quotient by sixth powers of global S-units.

The fixed remaining-ideal mask belongs to the row-independent arithmetic
factor. The full S/6 and complete-row zeros belong to the actual orbital
phase. On their live support the genuine row character is unramified, so
coefficient factorization is proved even for a ramified fixed background
or slot character. No phase, Gram identity or moment bound is assumed.

The remaining ideal is fixed within each row sum, as in the internal
class at manuscript lines 1611–1635. An arbitrary extra ideal depending
on the row is not silently treated as fixed. To use this construction,
its mask must equal the displayed fixed mask after intersection with the
original row mask. Otherwise a further genuine periodic-column
calibration is required; no free replacement of u by u * R(u)^6 occurs.

A fixed moving character can be kept in the arithmetic coefficients,
while the original complete row and its orbital phase stay unchanged.
The new constructor requires its exact character identity; it does not
claim that the moving character belongs to the fixed exceptional set.
The character must be fixed before the row. A correction that varies
with the row needs a genuine finite partition before this constructor
can be applied to each resulting row sum.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

/-- The actual complete-ideal orbit in the original unit sector. Only
the unused, non-exterior inputs receive the fixed unit-element orbit. -/
def completeIdealSectorRowMap
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (P : ProbeData K S)
    (sector : NonzeroIdeal K → SixthUnitClasses K S) (u : NonzeroIdeal K) :
    ActualSIntegerOrbit K S :=
  if hu : completeIdealIsExterior K S u then
    decomposedIdealSectorOrbit K S P (⟨u, hu⟩, sector u)
  else Quotient.mk _ (⟨1, one_ne_zero⟩ : NonzeroRingElements (S.integer K))

theorem completeIdealSectorRowMap_exterior
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (P : ProbeData K S)
    (sector : NonzeroIdeal K → SixthUnitClasses K S) (u : ExteriorIdeal K S) :
    completeIdealSectorRowMap S P sector u.val =
      decomposedIdealSectorOrbit K S P (u, sector u.val) := by
  unfold completeIdealSectorRowMap
  split
  · rfl
  · rename_i hu
    exact False.elim (hu u.property)

private theorem completeArithmeticRow_unramified
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (P : ProbeData K S)
    (R : RowCharacterInput K S P) (sector : SixthUnitClasses K S) (u : ExteriorIdeal K S)
    (p : HeightOneSpectrum (𝓞 K)) (hpS : p ∉ S)
    (hpu : ¬p.asIdeal ∣ u.val.val) :
    UnramifiedAt K
      (completeIdealRowCharacter K S P R sector u.val) p := by
  rw [completeIdealRowCharacter_exterior,
    rowCharacterInput_character_eq_arithmetic K S P R]
  apply arithmeticRowCharacter_unramified_of_exponent_zero K S P _ p hpS
  change primeExponents (sixthPowerFreePart u.val) p = 0
  rw [primeExponents_apply]
  apply Multiset.count_eq_zero.mpr
  intro hp
  exact hpu ((dvd_of_mem_normalizedFactors hp).trans (sixthPowerFreePart_dvd u.val))

private theorem completeArithmeticAtom_factorization
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (P : ProbeData K S)
    (R : RowCharacterInput K S P) (sector : SixthUnitClasses K S) (u : ExteriorIdeal K S)
    (background : HeckeCharacter K) (I : NonzeroIdeal K) :
    heckeIdealCoefficient K
        (background * completeIdealRowCharacter K S P R sector u.val) I *
        decomposedIdealRowMask K S u I =
      heckeIdealCoefficient K background I *
        actualOrbitSexticEvaluation K S P.arithmetic.root6 P.arithmetic.primitive6
          P.arithmetic.embedding I (decomposedIdealSectorOrbit K S P (u, sector)) := by
  rw [actualOrbitSexticEvaluation_decomposed_character K S P R,
    ← completeIdealRowCharacter_exterior K S P R]
  by_cases hmask : sexticIdealOutsideS K S I ∧ IsCoprime I.val u.val.val
  · simp only [decomposedIdealRowMask, if_pos hmask, mul_one]
    apply MOM_BASE.Paired.idealCoefficient_character_mul
    intro p hpI
    apply completeArithmeticRow_unramified S P R sector u p (hmask.1 p hpI).1
    intro hpu
    have htop : (⊤ : Ideal (𝓞 K)) ≤ p.asIdeal := by
      rw [← hmask.2.sup_eq]
      exact sup_le (Ideal.dvd_iff_le.mp hpI) (Ideal.dvd_iff_le.mp hpu)
    exact p.isPrime.ne_top (top_le_iff.mp htop)
  · simp only [decomposedIdealRowMask, if_neg hmask, mul_zero]

private theorem completeMask_eq_orbitMask
    {omegaCharacter psiCharacter : HeckeCharacter K}
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (d : MomentData K omegaCharacter psiCharacter) (remaining : NonzeroIdeal K)
    (hmask : ∀ u I, d.commonMask u I =
      (completeIdealCommonMask K S u I && decide (IsCoprime I remaining.val)))
    (u : ExteriorIdeal K S) (I : NonzeroIdeal K) :
    maskValue d u.val I.val = decomposedIdealRowMask K S u I *
      (if IsCoprime I.val remaining.val then (1 : ℂ) else 0) := by
  change (if d.commonMask u.val I.val then (1 : ℂ) else 0) = _
  rw [hmask]
  change (if decide (sexticIdealOutsideS K S I ∧ IsCoprime I.val u.val.val) &&
      decide (IsCoprime I.val remaining.val) then (1 : ℂ) else 0) =
    (if sexticIdealOutsideS K S I ∧ IsCoprime I.val u.val.val then (1 : ℂ) else 0) *
      (if IsCoprime I.val remaining.val then (1 : ℂ) else 0)
  by_cases hrow : sexticIdealOutsideS K S I ∧ IsCoprime I.val u.val.val <;>
    by_cases hremaining : IsCoprime I.val remaining.val <;> simp [hrow, hremaining]

private theorem completeArithmeticAtom_identity
    {omegaCharacter psiCharacter : HeckeCharacter K}
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (P : ProbeData K S)
    (R : RowCharacterInput K S P) (sector : NonzeroIdeal K → SixthUnitClasses K S)
    (d : MomentData K omegaCharacter psiCharacter) (remaining : NonzeroIdeal K)
    (hallowed : ∀ u, d.allowedRow u → completeIdealIsExterior K S u)
    (hrow : ∀ u, d.allowedRow u → d.rowCharacter u =
      completeIdealRowCharacter K S P R (sector u) u)
    (hmask : ∀ u I, d.commonMask u I =
      (completeIdealCommonMask K S u I && decide (IsCoprime I remaining.val)))
    (background : HeckeCharacter K) (u : NonzeroIdeal K) (hu : d.allowedRow u)
    (I : NonzeroIdeal K) :
    heckeIdealCoefficient K (background * d.rowCharacter u) I * maskValue d u I.val =
      (heckeIdealCoefficient K background I *
        (if IsCoprime I.val remaining.val then (1 : ℂ) else 0)) *
        actualOrbitSexticEvaluation K S P.arithmetic.root6 P.arithmetic.primitive6
          P.arithmetic.embedding I (completeIdealSectorRowMap S P sector u) := by
  let v : ExteriorIdeal K S := ⟨u, hallowed u hu⟩
  rw [hrow u hu]
  change _ * maskValue d v.val I.val =
    _ * actualOrbitSexticEvaluation K S P.arithmetic.root6 P.arithmetic.primitive6
      P.arithmetic.embedding I (completeIdealSectorRowMap S P sector v.val)
  rw [completeMask_eq_orbitMask S d remaining hmask v I, completeIdealSectorRowMap_exterior]
  have hfactor := completeArithmeticAtom_factorization S P R (sector u) v background I
  calc
    _ = (heckeIdealCoefficient K
        (background * completeIdealRowCharacter K S P R (sector u) u) I *
        decomposedIdealRowMask K S v I) *
          (if IsCoprime I.val remaining.val then (1 : ℂ) else 0) := by ring
    _ = _ := by rw [hfactor]; ring

/-- The actual phase dictionary on all allowed complete rows. The fixed
remaining mask is part of the row-independent arithmetic coefficient. -/
def completeIdealArithmeticAtoms
    {omegaCharacter psiCharacter : HeckeCharacter K}
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (P : ProbeData K S)
    (R : RowCharacterInput K S P) (sector : NonzeroIdeal K → SixthUnitClasses K S)
    (d : MomentData K omegaCharacter psiCharacter) (remaining : NonzeroIdeal K)
    (hallowed : ∀ u, d.allowedRow u → completeIdealIsExterior K S u)
    (hrow : ∀ u, d.allowedRow u → d.rowCharacter u =
      completeIdealRowCharacter K S P R (sector u) u)
    (hmask : ∀ u I, d.commonMask u I =
      (completeIdealCommonMask K S u I && decide (IsCoprime I remaining.val))) :
    EngineStep.ParentArithmeticAtoms (ActualSIntegerOrbit K S) d where
  rowMap := completeIdealSectorRowMap S P sector
  leftArithmetic I := heckeIdealCoefficient K d.plainBackground I *
    (if IsCoprime I.val remaining.val then 1 else 0)
  rightArithmetic I := heckeIdealCoefficient K d.plainBackground I *
    (if IsCoprime I.val remaining.val then 1 else 0)
  primeArithmetic i p := primeCoefficient K (d.slotCoefficient i) p *
    (if IsCoprime p.asIdeal remaining.val then 1 else 0)
  leftPhase q I := actualOrbitSexticEvaluation K S P.arithmetic.root6
    P.arithmetic.primitive6 P.arithmetic.embedding I q
  rightPhase q I := actualOrbitSexticEvaluation K S P.arithmetic.root6
    P.arithmetic.primitive6 P.arithmetic.embedding I q
  primePhase q _ p := actualOrbitSexticEvaluation K S P.arithmetic.root6
    P.arithmetic.primitive6 P.arithmetic.embedding (momentPrimeIdeal K p) q
  left u hu I := completeArithmeticAtom_identity S P R sector d remaining hallowed hrow hmask
    d.plainBackground u hu I
  right u hu I := completeArithmeticAtom_identity S P R sector d remaining hallowed hrow hmask
    d.plainBackground u hu I
  prime u hu i p := by
    have h := completeArithmeticAtom_identity S P R sector d remaining hallowed hrow hmask
      (d.slotCoefficient i) u hu (momentPrimeIdeal K p)
    simp only [heckeIdealCoefficient, nonzeroIdealCoefficient, momentPrimeIdeal,
      idealCoefficient_prime] at h
    rw [mul_comm (d.rowCharacter u) (d.slotCoefficient i)]
    exact h

/-- Consume the canonical full-row recipe directly. The original sector
and genuine phase array are independent of the Fourier parameter. The
remaining ideal may vary between models, but is fixed within each row sum. -/
def completeRowRecipe_arithmeticAtoms
    {omegaCharacter psiCharacter : HeckeCharacter K}
    {A : DedekindZetaZeroFree.SArithmeticData K}
    {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
    {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
    {X : Type*} {data : X → MomentData K omegaCharacter psiCharacter}
    (recipe : EngineStep.CompleteRowRecipe A P R data) (remaining : X → NonzeroIdeal K)
    (hmask : ∀ ξ u I, (data ξ).commonMask u I =
      (completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I &&
        decide (IsCoprime I (remaining ξ).val))) (ξ : X) :
    EngineStep.ParentArithmeticAtoms
      (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) (data ξ) :=
  completeIdealArithmeticAtoms (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R recipe.sector
    (data ξ) (remaining ξ) (recipe.exterior ξ) (recipe.character ξ) (hmask ξ)

/-- Extract a fixed moving character into the actual arithmetic atom.
Its possible ramification is retained: only the original complete row
character is factored using its proved unramified live support. No
multiplicativity assertion for two ramified ideal coefficients is used. -/
theorem completeArithmeticAtom_fixedTwist_identity
    {omegaCharacter psiCharacter : HeckeCharacter K}
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (P : ProbeData K S)
    (R : RowCharacterInput K S P) (sector : NonzeroIdeal K → SixthUnitClasses K S)
    (d : MomentData K omegaCharacter psiCharacter) (remaining : NonzeroIdeal K)
    (Γ : HeckeCharacter K)
    (hallowed : ∀ u, d.allowedRow u → completeIdealIsExterior K S u)
    (hrow : ∀ u, d.allowedRow u → d.rowCharacter u =
      Γ * completeIdealRowCharacter K S P R (sector u) u)
    (hmask : ∀ u I, d.commonMask u I =
      (completeIdealCommonMask K S u I && decide (IsCoprime I remaining.val)))
    (background : HeckeCharacter K) (u : NonzeroIdeal K) (hu : d.allowedRow u)
    (I : NonzeroIdeal K) :
    heckeIdealCoefficient K (background * d.rowCharacter u) I * maskValue d u I.val =
      (heckeIdealCoefficient K (background * Γ) I *
        (if IsCoprime I.val remaining.val then (1 : ℂ) else 0)) *
        actualOrbitSexticEvaluation K S P.arithmetic.root6 P.arithmetic.primitive6
          P.arithmetic.embedding I (completeIdealSectorRowMap S P sector u) := by
  let v : ExteriorIdeal K S := ⟨u, hallowed u hu⟩
  rw [hrow u hu, ← mul_assoc background Γ
    (completeIdealRowCharacter K S P R (sector u) u)]
  change _ * maskValue d v.val I.val =
    _ * actualOrbitSexticEvaluation K S P.arithmetic.root6 P.arithmetic.primitive6
      P.arithmetic.embedding I (completeIdealSectorRowMap S P sector v.val)
  rw [completeMask_eq_orbitMask S d remaining hmask v I, completeIdealSectorRowMap_exterior]
  have hfactor := completeArithmeticAtom_factorization S P R (sector u) v (background * Γ) I
  calc
    _ = (heckeIdealCoefficient K
        ((background * Γ) * completeIdealRowCharacter K S P R (sector u) u) I *
        decomposedIdealRowMask K S v I) *
          (if IsCoprime I.val remaining.val then (1 : ℂ) else 0) := by ring
    _ = _ := by rw [hfactor]; ring

/-- The genuine fixed moving factor changes only the computed arithmetic
coefficients. In particular the row map is still the complete original
u, not the ideal product obtained by multiplying its moving factors.
The fixed remaining mask is retained in both plain atoms and every slot. -/
def completeIdealFixedTwistArithmeticAtoms
    {omegaCharacter psiCharacter : HeckeCharacter K}
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (P : ProbeData K S)
    (R : RowCharacterInput K S P) (sector : NonzeroIdeal K → SixthUnitClasses K S)
    (d : MomentData K omegaCharacter psiCharacter) (remaining : NonzeroIdeal K)
    (Γ : HeckeCharacter K)
    (hallowed : ∀ u, d.allowedRow u → completeIdealIsExterior K S u)
    (hrow : ∀ u, d.allowedRow u → d.rowCharacter u =
      Γ * completeIdealRowCharacter K S P R (sector u) u)
    (hmask : ∀ u I, d.commonMask u I =
      (completeIdealCommonMask K S u I && decide (IsCoprime I remaining.val))) :
    EngineStep.ParentArithmeticAtoms (ActualSIntegerOrbit K S) d where
  rowMap := completeIdealSectorRowMap S P sector
  leftArithmetic I := heckeIdealCoefficient K (d.plainBackground * Γ) I *
    (if IsCoprime I.val remaining.val then 1 else 0)
  rightArithmetic I := heckeIdealCoefficient K (d.plainBackground * Γ) I *
    (if IsCoprime I.val remaining.val then 1 else 0)
  primeArithmetic i p := primeCoefficient K (d.slotCoefficient i * Γ) p *
    (if IsCoprime p.asIdeal remaining.val then 1 else 0)
  leftPhase q I := actualOrbitSexticEvaluation K S P.arithmetic.root6
    P.arithmetic.primitive6 P.arithmetic.embedding I q
  rightPhase q I := actualOrbitSexticEvaluation K S P.arithmetic.root6
    P.arithmetic.primitive6 P.arithmetic.embedding I q
  primePhase q _ p := actualOrbitSexticEvaluation K S P.arithmetic.root6
    P.arithmetic.primitive6 P.arithmetic.embedding (momentPrimeIdeal K p) q
  left u hu I := completeArithmeticAtom_fixedTwist_identity S P R sector d remaining Γ
    hallowed hrow hmask d.plainBackground u hu I
  right u hu I := completeArithmeticAtom_fixedTwist_identity S P R sector d remaining Γ
    hallowed hrow hmask d.plainBackground u hu I
  prime u hu i p := by
    have h := completeArithmeticAtom_fixedTwist_identity S P R sector d remaining Γ
      hallowed hrow hmask (d.slotCoefficient i) u hu (momentPrimeIdeal K p)
    simp only [heckeIdealCoefficient, nonzeroIdealCoefficient, momentPrimeIdeal,
      idealCoefficient_prime] at h
    rw [mul_comm (d.rowCharacter u) (d.slotCoefficient i)]
    exact h

end HeckeSkeleton.Moments.EngineInduction
