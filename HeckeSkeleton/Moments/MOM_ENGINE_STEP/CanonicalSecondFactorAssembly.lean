import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSecondRectangularFactors
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLogProfiles

/-!
# Assembling the second factors from the original arithmetic tables

The fixed background, original correction, displayed moving list and
remaining deletion ideal are kept separate. Appending a genuine moving
factor changes the computed coefficient and its complete mask together.
The two Fourier norm weights are distributed over the same original
ideal and prime occurrences before common extraction or centering.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open LocalFiniteSums
open MeasureTheory

namespace CanonicalSecondFactorAssembly

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

/-- The literal arithmetic deletion in every original column. The
norm budget still uses the radical of this full product. -/
def movingMask (D : OriginalMovingFactors A P R) (remaining : NonzeroIdeal K) :
    NonzeroIdeal K :=
  ⟨D.support.val * remaining.val,
    mem_nonZeroDivisors_of_ne_zero
      (mul_ne_zero D.support.property.1 (nonZeroDivisors.coe_ne_zero remaining))⟩

theorem movingMask_append_coprime
    (D E : OriginalMovingFactors A P R) (remaining : NonzeroIdeal K)
    (I : Ideal (𝓞 K)) :
    IsCoprime I (movingMask (D.append E) remaining).val ↔
      IsCoprime I (movingMask D remaining).val ∧ IsCoprime I E.support.val := by
  simp only [movingMask, IsCoprime.mul_right_iff, D.coprime_append_support E I]
  tauto

variable {ω ψ : HeckeCharacter K} {k : ℕ}

/-- All characters are computed from the same original lists. There is
no extra Hecke-character choice or enlarged theta family here. -/
def movingSourceCharacters (parent : MomentData K ω ψ) (correction : HeckeCharacter K)
    (D : OriginalMovingFactors A P R) (remaining : NonzeroIdeal K)
    (index : Fin k → Fin parent.geometry.slotCount) : FixedChildCharacters K k :=
  CanonicalOriginalPhaseCalibration.sourceCharacters parent
    (correction * D.character) (movingMask D remaining) index

theorem original_movingSourceCharacters {X : Type*} {data : X → MomentData K ω ψ}
    (Q : CompleteMovingRowRecipe A P R data) (ξ : X) :
    movingSourceCharacters (data ξ) Q.correction Q.moving Q.remaining id =
      CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
        (Q.correction * Q.moving.character) Q.arithmeticMask id := rfl

/-- A mask already present in an original phase is retained exactly
when its computed character is appended. Only the actual moving factor
is split from the fixed background coefficient. -/
theorem moving_coefficient_append
    (D E : OriginalMovingFactors A P R)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (background correction : HeckeCharacter K) (remaining : NonzeroIdeal K)
    (I : NonzeroIdeal K)
    (hI : HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) I)
    (hphase : E.residueValue (σ := σ) I.val *
      (if IsCoprime I.val E.support.val then (1 : ℂ) else 0) =
        E.residueValue (σ := σ) I.val) :
    heckeIdealCoefficient K (background * (correction * (D.append E).character)) I *
        (if IsCoprime I.val (movingMask (D.append E) remaining).val then (1 : ℂ) else 0) =
      (heckeIdealCoefficient K (background * (correction * D.character)) I *
        (if IsCoprime I.val (movingMask D remaining).val then (1 : ℂ) else 0)) *
          E.residueValue (σ := σ) I.val := by
  rw [D.append_character E,
    show background * (correction * (D.character * E.character)) =
      (background * (correction * D.character)) * E.character by ac_rfl,
    movingMask_append_coprime]
  by_cases hm : IsCoprime I.val (movingMask D remaining).val
  · simp only [hm, true_and, if_true, mul_one]
    rw [E.background_coefficient_masked hroot hemb
      (background * (correction * D.character)) I hI, mul_assoc, hphase]
  · simp only [hm, false_and, if_false, mul_zero, zero_mul]

theorem moving_plain_append
    (parent : MomentData K ω ψ) (correction : HeckeCharacter K)
    (D E : OriginalMovingFactors A P R) (remaining : NonzeroIdeal K)
    (index : Fin k → Fin parent.geometry.slotCount)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (I : NonzeroIdeal K)
    (hI : HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) I)
    (hphase : E.residueValue (σ := σ) I.val *
      (if IsCoprime I.val E.support.val then (1 : ℂ) else 0) =
        E.residueValue (σ := σ) I.val) :
    sourcePlainCoefficient
        (movingSourceCharacters parent correction (D.append E) remaining index).plain
        (movingSourceCharacters parent correction (D.append E) remaining index).plainTwist
        (movingSourceCharacters parent correction (D.append E) remaining index).mask I =
      sourcePlainCoefficient
        (movingSourceCharacters parent correction D remaining index).plain
        (movingSourceCharacters parent correction D remaining index).plainTwist
        (movingSourceCharacters parent correction D remaining index).mask I *
          E.residueValue (σ := σ) I.val := by
  simpa only [movingSourceCharacters,
    CanonicalOriginalPhaseCalibration.sourceCharacters, sourcePlainCoefficient,
    CanonicalOriginalPhaseCalibration.coefficient_one, mul_one,
    CanonicalOriginalPhaseCalibration.originalCoprimeMask,
    MonoidHom.coe_mk, OneHom.coe_mk] using
    moving_coefficient_append D E hroot hemb parent.plainBackground correction remaining I hI hphase

theorem moving_prime_append
    (parent : MomentData K ω ψ) (correction : HeckeCharacter K)
    (D E : OriginalMovingFactors A P R) (remaining : NonzeroIdeal K)
    (index : Fin k → Fin parent.geometry.slotCount)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (i : Fin k) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hphase : E.residueValue (σ := σ) p.asIdeal *
      (if IsCoprime p.asIdeal E.support.val then (1 : ℂ) else 0) =
        E.residueValue (σ := σ) p.asIdeal) :
    sourcePrimeCoefficient
        ((movingSourceCharacters parent correction (D.append E) remaining index).slot i)
        ((movingSourceCharacters parent correction (D.append E) remaining index).slotTwist i)
        (movingSourceCharacters parent correction (D.append E) remaining index).mask p =
      sourcePrimeCoefficient
        ((movingSourceCharacters parent correction D remaining index).slot i)
        ((movingSourceCharacters parent correction D remaining index).slotTwist i)
        (movingSourceCharacters parent correction D remaining index).mask p *
          E.residueValue (σ := σ) p.asIdeal := by
  simpa only [movingSourceCharacters,
    CanonicalOriginalPhaseCalibration.sourceCharacters, sourcePrimeCoefficient,
    primeCoefficient_one, mul_one, CanonicalOriginalPhaseCalibration.coefficient_prime,
    CanonicalOriginalPhaseCalibration.primeIdeal,
    CanonicalOriginalPhaseCalibration.originalCoprimeMask,
    MonoidHom.coe_mk, OneHom.coe_mk] using
    moving_coefficient_append D E hroot hemb (parent.slotCoefficient (index i))
      correction remaining (CanonicalOriginalPhaseCalibration.primeIdeal p)
      (CanonicalOriginalPhaseCalibration.outside_prime P p hp) hphase

/-- An actual logarithmic Fourier phase is multiplicative on ideals.
Its zero-ideal extension is fixed here only to make the ambient monoid
map total; original Cartesian occurrences are nonzero. -/
def logPhaseHom (ξ slope : ℝ) : Ideal (𝓞 K) →* ℂ where
  toFun I := if I = 0 then 0 else jointPhase ξ (slope * Real.log (Ideal.absNorm I : ℝ))
  map_one' := by simp [jointPhase]
  map_mul' I J := by
    by_cases hI : I = 0
    · simp only [hI, zero_mul, if_pos rfl]
    by_cases hJ : J = 0
    · simp only [hJ, mul_zero, if_pos rfl]
    have hnI : (Ideal.absNorm I : ℝ) ≠ 0 := by
      exact_mod_cast Ideal.absNorm_ne_zero_of_nonZeroDivisors
        (⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ : (Ideal (𝓞 K))⁰)
    have hnJ : (Ideal.absNorm J : ℝ) ≠ 0 := by
      exact_mod_cast Ideal.absNorm_ne_zero_of_nonZeroDivisors
        (⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩ : (Ideal (𝓞 K))⁰)
    simp only [if_neg hI, if_neg hJ, if_neg (mul_ne_zero hI hJ),
      map_mul, Nat.cast_mul, Real.log_mul hnI hnJ, mul_add, jointPhase_add]

/-- The norm tilt and the original first Fourier phase form one
computed multiplicative weight on every occurrence. -/
def normLogWeight (exponent ξ slope : ℝ) : Ideal (𝓞 K) →* ℂ :=
  CanonicalSecondRectangularFactors.normPower exponent * logPhaseHom ξ slope

theorem normLogWeight_exterior (exponent ξ slope : ℝ) (I : A.Exterior) :
    normLogWeight exponent ξ slope I.val =
      ((A.exteriorNorm I ^ exponent : ℝ) : ℂ) *
        jointPhase ξ (slope * Real.log (A.exteriorNorm I)) := by
  simp only [normLogWeight, MonoidHom.mul_apply,
    CanonicalSecondRectangularFactors.normPower, logPhaseHom,
    MonoidHom.coe_mk, OneHom.coe_mk, if_neg I.property.1] <;> rfl

variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- The genuine reciprocal coefficient of a pool valuation source.
The prime remains displayed even when its integer exponent is a
multiple of six. -/
def poolMovingFactors (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) : OriginalMovingFactors A P R :=
  OriginalMovingFactors.singleton
    ⟨generator C p, (generator_generates C p).1⟩ (2 * (n : ℤ))

theorem poolMovingFactors_residue (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (I : Ideal (𝓞 K)) :
    (poolMovingFactors (P := P) (R := R) C p n).residueValue (σ := σ) I =
      actualIdealResidue (A := A) (σ := σ) I (generator C p) ^ (2 * n) := by
  simp only [poolMovingFactors, OriginalMovingFactors.singleton,
    OriginalMovingFactors.residueValue, Fin.prod_univ_one,
    show (2 * (n : ℤ)) = ((2 * n : ℕ) : ℤ) by simp only [Nat.cast_mul, Nat.cast_ofNat],
    zpow_natCast]

theorem poolMovingFactors_fullIdeal (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :
    (poolMovingFactors (P := P) (R := R) C p n).fullIdeal = primeIdeal p :=
  OriginalMovingFactors.singleton_fullIdeal (primeIdeal p) (generator C p)
    (generator_generates C p) (2 * (n : ℤ))

/-- Original reciprocity determines the full complex pool phase.
Its norm-one estimate is not used to replace the phase by one. -/
theorem pool_columnPhase (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) {I : A.Exterior}
    (d : AmplifierResidualPresentation C p n I) :
    d.columnPhase =
      (poolMovingFactors (P := P) (R := R) C p n).residueValue (σ := σ) d.residual.val := by
  have he := congrArg σ
    (C.reciprocity.1 (powerIdeal p n) d.residual
      (generator C p ^ n) d.generator
      (Units.mk0 ((generator C p ^ n : A.R) : K)
        (by exact_mod_cast (generator_power_generates C p n).1))
      (Units.mk0 (d.generator : K) (by exact_mod_cast d.generates.1))
      (generator_power_generates C p n) d.generates rfl rfl
      (actual_prime_power_allowed C p n) d.allowed d.power_coprime.sup_eq)
  rw [AmplifierResidualPresentation.columnPhase,
    generatedIdealCharacter_mk, generatedIdealCharacter_mk, he,
    poolMovingFactors_residue]
  simp only [← actualIdealResidue_exterior]
  change (CanonicalSecondRectangularFactors.frequencyHom (σ := σ) d.residual)
      (generator C p ^ n) *
    (CanonicalSecondRectangularFactors.frequencyHom (σ := σ) d.residual)
      (generator C p ^ n) =
    (CanonicalSecondRectangularFactors.frequencyHom (σ := σ) d.residual)
      (generator C p) ^ (2 * n)
  rw [map_pow, two_mul, pow_add]

theorem poolMovingFactors_coprime (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) {I : A.Exterior}
    (d : AmplifierResidualPresentation C p n I) :
    IsCoprime d.residual.val
      (poolMovingFactors (P := P) (R := R) C p n).support.val := by
  rw [(poolMovingFactors (P := P) (R := R) C p n).
      coprime_support_iff_fullIdeal d.residual.val,
    poolMovingFactors_fullIdeal]
  exact d.coprime.symm

section Occurrences

variable (S₁ S₂ : Finset (Ideal (𝓞 K)))
variable (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))

private theorem divisor_conditions (J active : A.Exterior)
    (hactive : IsCoprime J.val active.val) (I : Ideal (𝓞 K)) (hI : I ∣ J.val) :
    I ≠ 0 ∧ IsCoprime I A.cS ∧ IsCoprime I active.val := by
  refine ⟨?_, ?_, hactive.of_isCoprime_of_dvd_left hI⟩
  · intro hzero
    rw [hzero, zero_dvd_iff] at hI
    exact J.property.1 hI
  · exact (Ideal.isCoprime_iff_sup_eq.mpr J.property.2).
      of_isCoprime_of_dvd_left hI

/-- Every original occurrence inherits its exceptional-place and
active-support coprimality from the actual Cartesian exterior ideal.
One original support witness supplies the other coordinates. -/
theorem occurrence_conditions
    (J : AllocationColumn K k → A.Exterior)
    (hJ : ∀ i ∈ childCartesianColumns S₁ S₂ S, (J i).val = allocationColumnIdeal i)
    (witness : AllocationColumn K k)
    (hwitness : witness ∈ childCartesianColumns S₁ S₂ S)
    (active : A.Exterior)
    (hactive : ∀ i ∈ childCartesianColumns S₁ S₂ S, IsCoprime (J i).val active.val) :
    (∀ I ∈ S₁, I ≠ 0 ∧ IsCoprime I A.cS ∧ IsCoprime I active.val) ∧
      (∀ I ∈ S₂, I ≠ 0 ∧ IsCoprime I A.cS ∧ IsCoprime I active.val) ∧
      (∀ j, ∀ p ∈ S j, IsCoprime p.asIdeal A.cS ∧ IsCoprime p.asIdeal active.val) := by
  have hw : (witness.1.1 ∈ S₁ ∧ witness.1.2 ∈ S₂) ∧
      ∀ j, witness.2 j ∈ S j := by
    simpa only [childCartesianColumns, Finset.product_eq_sprod, Finset.mem_product,
      Fintype.mem_piFinset] using hwitness
  have hg (i : AllocationColumn K k) (hi : i ∈ childCartesianColumns S₁ S₂ S)
      (I : Ideal (𝓞 K)) (hI : I ∣ allocationColumnIdeal i) :
      I ≠ 0 ∧ IsCoprime I A.cS ∧ IsCoprime I active.val :=
    divisor_conditions (J i) active (hactive i hi) I (by rwa [hJ i hi])
  refine ⟨?_, ?_, ?_⟩
  · intro I hI
    let i : AllocationColumn K k := ((I, witness.1.2), witness.2)
    have hi : i ∈ childCartesianColumns S₁ S₂ S := by
      simpa only [i, childCartesianColumns, Finset.product_eq_sprod,
        Finset.mem_product, Fintype.mem_piFinset] using ⟨⟨hI, hw.1.2⟩, hw.2⟩
    exact hg i hi I (dvd_mul_of_dvd_left (dvd_mul_right I witness.1.2) _)
  · intro I hI
    let i : AllocationColumn K k := ((witness.1.1, I), witness.2)
    have hi : i ∈ childCartesianColumns S₁ S₂ S := by
      simpa only [i, childCartesianColumns, Finset.product_eq_sprod,
        Finset.mem_product, Fintype.mem_piFinset] using ⟨⟨hw.1.1, hI⟩, hw.2⟩
    exact hg i hi I (dvd_mul_of_dvd_left (dvd_mul_left I witness.1.1) _)
  · intro j p hp
    let i : AllocationColumn K k := (witness.1, Function.update witness.2 j p)
    have hi : i ∈ childCartesianColumns S₁ S₂ S := by
      simp only [i, childCartesianColumns, Finset.product_eq_sprod,
        Finset.mem_product, Fintype.mem_piFinset]
      refine ⟨hw.1, ?_⟩
      intro l
      by_cases hl : l = j
      · simpa only [hl, Function.update_same] using hp
      · simpa only [Function.update_noteq hl] using hw.2 l
    have hd : p.asIdeal ∣ ∏ l, (i.2 l).asIdeal := by
      have h := Finset.dvd_prod_of_mem (fun l => (i.2 l).asIdeal) (Finset.mem_univ j)
      simpa only [i, Function.update_same] using h
    exact (hg i hi p.asIdeal (dvd_mul_of_dvd_right hd _)).2

end Occurrences

/-- The total monoid weight is evaluated at the actual nonzero plain
ideals, with every prime occurrence still present. -/
theorem nonzero_rectangle_weight
    (left right : NonzeroIdeal K → ℂ)
    (slot : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (M : Ideal (𝓞 K) →* ℂ) (i : AllocationColumn K k)
    (hleft : i.1.1 ≠ 0) (hright : i.1.2 ≠ 0) :
    childCartesianCoefficient
        (fun I => left (sourceMomentIdeal I) * M (sourceMomentIdeal I).val)
        (fun I => right (sourceMomentIdeal I) * M (sourceMomentIdeal I).val)
        (fun j p => slot j p * M p.asIdeal) i =
      childCartesianCoefficient (fun I => left (sourceMomentIdeal I))
        (fun I => right (sourceMomentIdeal I)) slot i * M (allocationColumnIdeal i) := by
  simpa only [childCartesianCoefficient,
    sourceMomentIdeal_val_of_ne_zero i.1.1 hleft,
    sourceMomentIdeal_val_of_ne_zero i.1.2 hright] using
    (CanonicalSecondRectangularFactors.rectangle_mul_ideal_weight M
      (fun I => left (sourceMomentIdeal I)) (fun I => right (sourceMomentIdeal I)) slot i).symm

section Tables

variable (parent : MomentData K ω ψ) (correction : HeckeCharacter K)
variable (D E : OriginalMovingFactors A P R) (remaining : NonzeroIdeal K)
variable (index : Fin k → Fin parent.geometry.slotCount)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (side : SecondColumnSide) (χ : (PUnit × PUnit) →* Circle)
variable (S₁ S₂ : Finset (Ideal (𝓞 K)))
variable (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
variable (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
variable (w₁ w₂ : NonzeroIdeal K → ℂ)
variable (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
variable (M : Ideal (𝓞 K) →* ℂ)

private def oldPlain (N : ℝ) (weight : NonzeroIdeal K → ℂ) (I : NonzeroIdeal K) : ℂ :=
  (Real.sqrt N : ℂ)⁻¹ *
    (sourcePlainCoefficient
      (movingSourceCharacters parent correction D remaining index).plain
      (movingSourceCharacters parent correction D remaining index).plainTwist
      (movingSourceCharacters parent correction D remaining index).mask I * weight I)

private def oldPrime (i : Fin k) (p : HeightOneSpectrum (𝓞 K)) : ℂ :=
  (Real.sqrt (Z ^ length i) : ℂ)⁻¹ *
    (sourcePrimeCoefficient
      ((movingSourceCharacters parent correction D remaining index).slot i)
      ((movingSourceCharacters parent correction D remaining index).slotTwist i)
      (movingSourceCharacters parent correction D remaining index).mask p * w i p)

/-- A constructive single-occurrence update. The atom on the left is
the literal old atom times the original residue and norm/Fourier
weight. Its character and mask identity are proved above. -/
def appendedWeightedDictionary
    (hout₁ : ∀ I ∈ S₁,
      HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
        (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (sourceMomentIdeal I))
    (hout₂ : ∀ I ∈ S₂,
      HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
        (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (sourceMomentIdeal I))
    (hout : ∀ j, ∀ p ∈ S j, p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hmask₁ : ∀ I ∈ S₁, E.residueValue (σ := σ) (sourceMomentIdeal I).val *
      (if IsCoprime (sourceMomentIdeal I).val E.support.val then (1 : ℂ) else 0) =
        E.residueValue (σ := σ) (sourceMomentIdeal I).val)
    (hmask₂ : ∀ I ∈ S₂, E.residueValue (σ := σ) (sourceMomentIdeal I).val *
      (if IsCoprime (sourceMomentIdeal I).val E.support.val then (1 : ℂ) else 0) =
        E.residueValue (σ := σ) (sourceMomentIdeal I).val)
    (hmask : ∀ j, ∀ p ∈ S j, E.residueValue (σ := σ) p.asIdeal *
      (if IsCoprime p.asIdeal E.support.val then (1 : ℂ) else 0) =
        E.residueValue (σ := σ) p.asIdeal) :
    SecondCoefficientTermDictionary
      (movingSourceCharacters parent correction (D.append E) remaining index)
      (side.phase PUnit χ) S₁ S₂ S where
  leftAtom I := oldPlain parent correction D remaining index N₁ w₁ (sourceMomentIdeal I) *
    E.residueValue (σ := σ) (sourceMomentIdeal I).val * M (sourceMomentIdeal I).val
  rightAtom I := oldPlain parent correction D remaining index N₂ w₂ (sourceMomentIdeal I) *
    E.residueValue (σ := σ) (sourceMomentIdeal I).val * M (sourceMomentIdeal I).val
  slotAtom j p := oldPrime parent correction D remaining index Z length w j p *
    E.residueValue (σ := σ) p.asIdeal * M p.asIdeal
  leftRay _ := PUnit.unit
  rightRay _ := PUnit.unit
  slotRay _ _ := PUnit.unit
  scale₁ := N₁
  scale₂ := N₂
  base := Z
  length := length
  leftWeight I := w₁ I * M I.val
  rightWeight I := w₂ I * M I.val
  slotWeight j p := w j p * M p.asIdeal
  plain₁ I hI := by
    rw [CanonicalSecondRectangularFactors.punit_phase, mul_one,
      moving_plain_append parent correction D E remaining index hroot hemb
        (sourceMomentIdeal I) (hout₁ I hI) (hmask₁ I hI)]
    unfold oldPlain
    ring
  plain₂ I hI := by
    rw [CanonicalSecondRectangularFactors.punit_phase, mul_one,
      moving_plain_append parent correction D E remaining index hroot hemb
        (sourceMomentIdeal I) (hout₂ I hI) (hmask₂ I hI)]
    unfold oldPlain
    ring
  prime j p hp := by
    rw [CanonicalSecondRectangularFactors.punit_phase, mul_one,
      moving_prime_append parent correction D E remaining index hroot hemb
        j p (hout j p hp) (hmask j p hp)]
    unfold oldPrime
    ring

end Tables

section FirstTable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (parent : MomentData K ω ψ) (correction : HeckeCharacter K)
variable (D : OriginalMovingFactors A P R) (remaining : NonzeroIdeal K)
variable (index : Fin k → Fin parent.geometry.slotCount)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (side : SecondColumnSide) (χ : (PUnit × PUnit) →* Circle)
variable (S₁ S₂ : Finset (Ideal (𝓞 K)))
variable (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
variable (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
variable (w₁ w₂ : NonzeroIdeal K → ℂ)
variable (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
variable (M : Ideal (𝓞 K) →* ℂ)
variable (C : A.GeneralArithmeticContext σ η hS)
variable (primes : ι → ExteriorPrime A) (m n : ι → ℕ) (right : Bool)
variable (δ : NonzeroRingElements A.R)

/-- The original first divisor update has no phase or atom dictionary
premise. Exceptional-place support and active coprimality descend to
each occurrence from the actual complete residual ideal; the physical
mask zero is proved from the same original generator. -/
def firstWeightedDictionary
    (J : AllocationColumn K k → A.Exterior)
    (hJ : ∀ i ∈ childCartesianColumns S₁ S₂ S, (J i).val = allocationColumnIdeal i)
    (witness : AllocationColumn K k)
    (hwitness : witness ∈ childCartesianColumns S₁ S₂ S)
    (hactive : ∀ i ∈ childCartesianColumns S₁ S₂ S,
      IsCoprime (J i).val (firstActiveIdeal primes m n).val) :
    SecondCoefficientTermDictionary
      (movingSourceCharacters parent correction
        (D.append (CanonicalSecondRectangularFactors.firstMovingFactors
          P R C primes m n right δ)) remaining index)
      (side.phase PUnit χ) S₁ S₂ S := by
  let E := CanonicalSecondRectangularFactors.firstMovingFactors P R C primes m n right δ
  have hc := occurrence_conditions S₁ S₂ S J hJ witness hwitness
    (firstActiveIdeal primes m n) hactive
  have hout₁ (I : Ideal (𝓞 K)) (hI : I ∈ S₁) :
      HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
        (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (sourceMomentIdeal I) := by
    apply (CanonicalOriginalPhaseCalibration.outside_iff_coprime _).mpr
    simpa only [sourceMomentIdeal_val_of_ne_zero I (hc.1 I hI).1] using (hc.1 I hI).2.1
  have hout₂ (I : Ideal (𝓞 K)) (hI : I ∈ S₂) :
      HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
        (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (sourceMomentIdeal I) := by
    apply (CanonicalOriginalPhaseCalibration.outside_iff_coprime _).mpr
    simpa only [sourceMomentIdeal_val_of_ne_zero I (hc.2.1 I hI).1] using (hc.2.1 I hI).2.1
  have hout (j : Fin k) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ S j) :
      p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))) := by
    have he := (CanonicalOriginalPhaseCalibration.outside_iff_coprime
      (CanonicalOriginalPhaseCalibration.primeIdeal p)).mpr (hc.2.2 j p hp).1
    exact (he p (dvd_refl p.asIdeal)).1
  have hmask (I : NonzeroIdeal K)
      (hcop : IsCoprime I.val (firstActiveIdeal primes m n).val) :
      E.residueValue (σ := σ) I.val *
        (if IsCoprime I.val E.support.val then (1 : ℂ) else 0) =
          E.residueValue (σ := σ) I.val :=
    CanonicalSecondRectangularFactors.firstMovingFactors_residue_mask P R hroot hemb
      C primes m n right δ (originalFrequencyIdeal δ.val)
      (originalFrequencyIdeal_generates δ.val δ.property) I hcop
  exact appendedWeightedDictionary parent correction D E remaining index hroot hemb
    side χ S₁ S₂ S N₁ N₂ Z length w₁ w₂ w M hout₁ hout₂ hout
    (fun I hI => hmask (sourceMomentIdeal I) (by
      simpa only [sourceMomentIdeal_val_of_ne_zero I (hc.1 I hI).1] using (hc.1 I hI).2.2))
    (fun I hI => hmask (sourceMomentIdeal I) (by
      simpa only [sourceMomentIdeal_val_of_ne_zero I (hc.2.1 I hI).1] using (hc.2.1 I hI).2.2))
    (fun j p hp => hmask (CanonicalOriginalPhaseCalibration.primeIdeal p) (hc.2.2 j p hp).2)

/-- The computed first dictionary is exactly the old residual
rectangle times its actual complete first divisor, norm and Fourier
weight. This is a conclusion of the single-occurrence construction. -/
theorem firstWeightedDictionary_coefficient
    (J : AllocationColumn K k → A.Exterior)
    (hJ : ∀ i ∈ childCartesianColumns S₁ S₂ S, (J i).val = allocationColumnIdeal i)
    (witness : AllocationColumn K k)
    (hwitness : witness ∈ childCartesianColumns S₁ S₂ S)
    (hactive : ∀ i ∈ childCartesianColumns S₁ S₂ S,
      IsCoprime (J i).val (firstActiveIdeal primes m n).val)
    (i : AllocationColumn K k) (hi : i ∈ childCartesianColumns S₁ S₂ S) :
    (firstWeightedDictionary parent correction D remaining index hroot hemb side χ
      S₁ S₂ S N₁ N₂ Z length w₁ w₂ w M C primes m n right δ
      J hJ witness hwitness hactive).coefficient i =
      rawBareSourceCoefficient (movingSourceCharacters parent correction D remaining index)
        N₁ N₂ Z length w₁ w₂ w i *
          ((CanonicalSecondRectangularFactors.firstMovingFactors P R C primes m n right δ).
            residueHom (σ := σ) * M) (allocationColumnIdeal i) := by
  have hleft : i.1.1 ≠ 0 := by
    intro hz
    apply (J i).property.1
    rw [hJ i hi, allocationColumnIdeal, hz, zero_mul, zero_mul]
  have hright : i.1.2 ≠ 0 := by
    intro hz
    apply (J i).property.1
    rw [hJ i hi, allocationColumnIdeal, hz, mul_zero, zero_mul]
  have he := nonzero_rectangle_weight
    (oldPlain parent correction D remaining index N₁ w₁)
    (oldPlain parent correction D remaining index N₂ w₂)
    (oldPrime parent correction D remaining index Z length w)
    ((CanonicalSecondRectangularFactors.firstMovingFactors P R C primes m n right δ).
      residueHom (σ := σ) * M) i hleft hright
  simpa only [firstWeightedDictionary, appendedWeightedDictionary,
    SecondCoefficientTermDictionary.coefficient, rawBareSourceCoefficient,
    FixedChildCharacters.bareCoefficient, childCartesianCoefficient,
    oldPlain, oldPrime, MonoidHom.mul_apply, OriginalMovingFactors.residueHom,
    MonoidHom.coe_mk, OneHom.coe_mk, mul_assoc] using he

end FirstTable

section SecondUnitTable

variable [IsPrincipalIdealRing A.R]
variable (parent : MomentData K ω ψ) (correction : HeckeCharacter K)
variable (D : OriginalMovingFactors A P R) (remaining : NonzeroIdeal K)
variable (index : Fin k → Fin parent.geometry.slotCount)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (side : SecondColumnSide) (χ : (PUnit × PUnit) →* Circle)
variable (S₁ S₂ : Finset (Ideal (𝓞 K)))
variable (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
variable (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
variable (w₁ w₂ : NonzeroIdeal K → ℂ)
variable (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
variable (M : Ideal (𝓞 K) →* ℂ)

/-- The actual second empty-mask generator contributes its inverse
unit character. Its support is proved to be one, while its phase is
still evaluated on every original occurrence. -/
def emptyMaskWeightedDictionary
    (J : AllocationColumn K k → A.Exterior)
    (hJ : ∀ i ∈ childCartesianColumns S₁ S₂ S, (J i).val = allocationColumnIdeal i)
    (witness : AllocationColumn K k)
    (hwitness : witness ∈ childCartesianColumns S₁ S₂ S) :
    SecondCoefficientTermDictionary
      (movingSourceCharacters parent correction
        (D.append (CanonicalSecondRectangularFactors.secondMaskMovingFactors P R
          (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅)))
        remaining index)
      (side.phase PUnit χ) S₁ S₂ S := by
  let E := CanonicalSecondRectangularFactors.secondMaskMovingFactors P R
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅)
  have hunit (i : AllocationColumn K k) (_hi : i ∈ childCartesianColumns S₁ S₂ S) :
      IsCoprime (J i).val (unitExterior A).val := by
    change IsCoprime (J i).val 1
    exact isCoprime_one_right
  have hc := occurrence_conditions S₁ S₂ S J hJ witness hwitness (unitExterior A) hunit
  have hout₁ (I : Ideal (𝓞 K)) (hI : I ∈ S₁) :
      HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
        (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (sourceMomentIdeal I) := by
    apply (CanonicalOriginalPhaseCalibration.outside_iff_coprime _).mpr
    simpa only [sourceMomentIdeal_val_of_ne_zero I (hc.1 I hI).1] using (hc.1 I hI).2.1
  have hout₂ (I : Ideal (𝓞 K)) (hI : I ∈ S₂) :
      HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
        (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (sourceMomentIdeal I) := by
    apply (CanonicalOriginalPhaseCalibration.outside_iff_coprime _).mpr
    simpa only [sourceMomentIdeal_val_of_ne_zero I (hc.2.1 I hI).1] using (hc.2.1 I hI).2.1
  have hout (j : Fin k) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ S j) :
      p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))) := by
    have he := (CanonicalOriginalPhaseCalibration.outside_iff_coprime
      (CanonicalOriginalPhaseCalibration.primeIdeal p)).mpr (hc.2.2 j p hp).1
    exact (he p (dvd_refl p.asIdeal)).1
  have hmask (I : Ideal (𝓞 K)) :
      E.residueValue (σ := σ) I *
        (if IsCoprime I E.support.val then (1 : ℂ) else 0) =
          E.residueValue (σ := σ) I := by
    have hs : E.support = unitExterior A :=
      CanonicalSecondRectangularFactors.second_empty_mask_support P R
    rw [hs]
    change _ * (if IsCoprime I 1 then (1 : ℂ) else 0) = _
    rw [if_pos isCoprime_one_right, mul_one]
  exact appendedWeightedDictionary parent correction D E remaining index hroot hemb
    side χ S₁ S₂ S N₁ N₂ Z length w₁ w₂ w M hout₁ hout₂ hout
    (fun I _ => hmask (sourceMomentIdeal I).val)
    (fun I _ => hmask (sourceMomentIdeal I).val) (fun _ p _ => hmask p.asIdeal)

theorem emptyMaskWeightedDictionary_coefficient
    (J : AllocationColumn K k → A.Exterior)
    (hJ : ∀ i ∈ childCartesianColumns S₁ S₂ S, (J i).val = allocationColumnIdeal i)
    (witness : AllocationColumn K k)
    (hwitness : witness ∈ childCartesianColumns S₁ S₂ S)
    (i : AllocationColumn K k) (hi : i ∈ childCartesianColumns S₁ S₂ S) :
    (emptyMaskWeightedDictionary parent correction D remaining index hroot hemb side χ
      S₁ S₂ S N₁ N₂ Z length w₁ w₂ w M J hJ witness hwitness).coefficient i =
      rawBareSourceCoefficient (movingSourceCharacters parent correction D remaining index)
        N₁ N₂ Z length w₁ w₂ w i *
          ((CanonicalSecondRectangularFactors.secondMaskMovingFactors P R
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅)).
              residueHom (σ := σ) * M) (allocationColumnIdeal i) := by
  have hleft : i.1.1 ≠ 0 := by
    intro hz
    apply (J i).property.1
    rw [hJ i hi, allocationColumnIdeal, hz, zero_mul, zero_mul]
  have hright : i.1.2 ≠ 0 := by
    intro hz
    apply (J i).property.1
    rw [hJ i hi, allocationColumnIdeal, hz, mul_zero, zero_mul]
  have he := nonzero_rectangle_weight
    (oldPlain parent correction D remaining index N₁ w₁)
    (oldPlain parent correction D remaining index N₂ w₂)
    (oldPrime parent correction D remaining index Z length w)
    ((CanonicalSecondRectangularFactors.secondMaskMovingFactors P R
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅)).
        residueHom (σ := σ) * M) i hleft hright
  simpa only [emptyMaskWeightedDictionary, appendedWeightedDictionary,
    SecondCoefficientTermDictionary.coefficient, rawBareSourceCoefficient,
    FixedChildCharacters.bareCoefficient, childCartesianCoefficient,
    oldPlain, oldPrime, MonoidHom.mul_apply, OriginalMovingFactors.residueHom,
    MonoidHom.coe_mk, OneHom.coe_mk, mul_assoc] using he

end SecondUnitTable

section CanonicalCharts

variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]
variable (C : A.GeneralArithmeticContext σ η hS)
variable {α β : Type*} (left : Finset α) (right : Finset β)
variable (fullI : α → A.Exterior) (fullJ : β → A.Exterior)
variable (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
variable (hDE : DE ∈ commonSupportPool left right
  (fun i => (fullI i).val) (fun j => (fullJ j).val))
variable (φ : 𝓢(mixedEmbedding.euclidean.mixedSpace K, ℂ))
variable (c : α → ℂ) (e : β → ℂ)
variable (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
variable (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
variable (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
variable (radius : {r : ℝ // 0 < r}) (mask : Finset (HeightOneSpectrum A.R))
variable (tilt : ℝ) (htilt : 0 < tilt) (htiltHalf : tilt ≤ 1 / 2)

local notation "firstBlock" => canonicalFirstCommonBlock C left right fullI fullJ DE hDE
local notation "firstChart" => FirstBlockProfileChart.canonicalLogWithCoefficients
  hΓ μv ν firstBlock C left right φ c e finiteTest hlc hcs radius mask tilt htilt htiltHalf
local notation "maskGenerator" =>
  sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) mask

/-- The literal first left Gauss coefficient, including its original
Fourier twist, has the computed fixed moving character and the full
inverse-norm tilt. -/
theorem canonical_first_left_twisted (ξ : ℝ) (i : α) :
    FirstGaussPoolData.twistedCoefficient
        (fun i => firstChart.leftCoefficient i *
          firstLeftDivisorFactor
            (generatedOriginalColumn (σ := σ) hΓ (firstBlock.leftResidual i)
              (firstBlock.leftGenerator i) (firstBlock.left_generates i))
            (actualActiveColumn hΓ C firstBlock.primes firstBlock.primes_injective
              firstBlock.leftMultiplicity firstBlock.rightMultiplicity) maskGenerator.val)
        firstChart.leftPoint ξ i =
      c i *
        ((CanonicalSecondRectangularFactors.firstMovingFactors P R C firstBlock.primes
          firstBlock.leftMultiplicity firstBlock.rightMultiplicity false maskGenerator).
            residueHom (σ := σ) * normLogWeight (tilt - 1) ξ (-1))
          (firstBlock.leftResidual i).val := by
  rw [FirstGaussPoolData.twistedCoefficient,
    FirstBlockProfileChart.canonicalLogWithCoefficients_leftCoefficient_eq,
    CanonicalSecondRectangularFactors.canonical_first_left_factor_moving P R hΓ C
      left right fullI fullJ DE hDE maskGenerator i,
    MonoidHom.mul_apply, normLogWeight_exterior]
  change (((c i * ((A.exteriorNorm (firstBlock.leftResidual i) ^ tilt : ℝ) : ℂ)) /
      (A.exteriorNorm (firstBlock.leftResidual i) : ℂ)) * _) *
        jointPhase ξ (-Real.log (A.exteriorNorm (firstBlock.leftResidual i))) = _
  rw [Real.rpow_sub_one (A.exteriorNorm_pos (firstBlock.leftResidual i)).ne',
    Complex.ofReal_div, neg_one_mul]
  ring

/-- The right first source uses the literal opposite Fourier location.
Its reciprocal character exponents are `1-netExponent`; the eventual
whole conjugation is not folded into an unrelated background. -/
theorem canonical_first_right_twisted (ξ : ℝ) (j : β) :
    FirstGaussPoolData.twistedCoefficient
        (fun j => firstChart.rightCoefficient j *
          firstRightDivisorFactor
            (generatedOriginalColumn (σ := σ) hΓ (firstBlock.rightResidual j)
              (firstBlock.rightGenerator j) (firstBlock.right_generates j))
            (actualActiveColumn hΓ C firstBlock.primes firstBlock.primes_injective
              firstBlock.leftMultiplicity firstBlock.rightMultiplicity) maskGenerator.val)
        (fun j => -firstChart.rightPoint j) ξ j =
      e j *
        ((CanonicalSecondRectangularFactors.firstMovingFactors P R C firstBlock.primes
          firstBlock.leftMultiplicity firstBlock.rightMultiplicity true maskGenerator).
            residueHom (σ := σ) * normLogWeight (tilt - 1) ξ 1)
          (firstBlock.rightResidual j).val := by
  rw [FirstGaussPoolData.twistedCoefficient,
    FirstBlockProfileChart.canonicalLogWithCoefficients_rightCoefficient_eq,
    CanonicalSecondRectangularFactors.canonical_first_right_factor_moving P R hΓ C
      left right fullI fullJ DE hDE maskGenerator j,
    MonoidHom.mul_apply, normLogWeight_exterior]
  change (((e j * ((A.exteriorNorm (firstBlock.rightResidual j) ^ tilt : ℝ) : ℂ)) /
      (A.exteriorNorm (firstBlock.rightResidual j) : ℂ)) * _) *
        jointPhase ξ (- -Real.log (A.exteriorNorm (firstBlock.rightResidual j))) = _
  rw [Real.rpow_sub_one (A.exteriorNorm_pos (firstBlock.rightResidual j)).ne',
    Complex.ofReal_div, neg_neg, one_mul]
  ring

variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → localDifferentExponent K v = 0)
variable (b : FirstCommonCharacterBlock fullI fullJ DE)
variable (rowLabelCount : ℕ)
variable (rowLabel : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
  Fin (rowLabelCount + 1))
variable (hleft : ∀ i ∈ b.leftColumns left,
  IsCoprime (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i) maskGenerator.val)
variable (hright : ∀ j ∈ b.rightColumns right,
  IsCoprime (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j) maskGenerator.val)

local notation "secondChart" => SecondBlockProfileChart.canonicalLogWithCoefficients
  hΓ μv hDiff ν b C left right φ c e finiteTest hlc hcs radius mask rowLabelCount rowLabel
    hleft hright tilt htilt htiltHalf

/-- This projection binds the computed multiplicative weight to the
actual chart field used by second allocation. -/
theorem canonical_second_left_coefficient (i : α) :
    secondChart.sourceLeftCoefficient i = c i *
      CanonicalSecondRectangularFactors.secondWeight (σ := σ) tilt maskGenerator.val
        (b.secondLeftIdeal i).val := by
  change (c i * ((A.exteriorNorm (b.secondLeftIdeal i) ^ tilt : ℝ) : ℂ)) *
      (generatedOriginalColumn (σ := σ) hΓ (b.secondLeftIdeal i)
        (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
        (b.secondLeft_generates C i)).divisorPhase maskGenerator.val = _
  exact CanonicalSecondRectangularFactors.original_second_coefficient hΓ (c i)
    (b.secondLeftIdeal i) _ (b.secondLeft_generates C i) tilt maskGenerator.val

theorem canonical_second_right_coefficient (j : β) :
    secondChart.sourceRightCoefficient j = e j *
      CanonicalSecondRectangularFactors.secondWeight (σ := σ) tilt maskGenerator.val
        (b.secondRightIdeal j).val := by
  change (e j * ((A.exteriorNorm (b.secondRightIdeal j) ^ tilt : ℝ) : ℂ)) *
      (generatedOriginalColumn (σ := σ) hΓ (b.secondRightIdeal j)
        (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j)
        (b.secondRight_generates C j)).divisorPhase maskGenerator.val = _
  exact CanonicalSecondRectangularFactors.original_second_coefficient hΓ (e j)
    (b.secondRightIdeal j) _ (b.secondRight_generates C j) tilt maskGenerator.val

end CanonicalCharts

end CanonicalSecondFactorAssembly
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondFactorAssembly.moving_coefficient_append
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondFactorAssembly.normLogWeight_exterior
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondFactorAssembly.pool_columnPhase
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondFactorAssembly.occurrence_conditions
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondFactorAssembly.firstWeightedDictionary
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondFactorAssembly.firstWeightedDictionary_coefficient
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondFactorAssembly.emptyMaskWeightedDictionary
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondFactorAssembly.canonical_first_left_twisted
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondFactorAssembly.canonical_first_right_twisted
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondFactorAssembly.canonical_second_left_coefficient
