import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalPhaseCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstGaussData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalUnmaskedSecondStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCommonAtomBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalLogNormLocations
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstActiveDictionary
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalMovingFactorAppend
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.MovingOriginalArithmeticAtoms

set_option linter.unusedSectionVars false

/-!
# Original arithmetic factors in the second rectangles

The first divisor factors are evaluated using the same original allowed
generators and the original reciprocity law.  The active character is
not declared trivial: its prime exponents become the displayed fixed
moving factors of the child.  Both signs are retained, as is the actual
chosen generator of the second empty avoidance mask.

All identities in this file are identities of individual original
columns or their original ideal and prime occurrences.  They precede
the Cartesian product, centering, and every energy estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Active
open HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

namespace CanonicalSecondRectangularFactors

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- The full original residue is multiplicative in the frequency on an
exterior ideal.  In particular the empty product has its genuine value. -/
def frequencyHom (I : A.Exterior) : A.R →* ℂ where
  toFun x := actualIdealResidue (A := A) (σ := σ) I.val x
  map_one' := actualIdealResidue_frequency_one I
  map_mul' x y := actualIdealResidue_frequency_mul I.val x y

/-- Multiplicativity in the whole ideal includes the original exterior
zeros, and will be used to distribute one actual phase to every occurrence. -/
def idealPhase (x : A.R) : Ideal (𝓞 K) →* ℂ where
  toFun I := actualIdealResidue (A := A) (σ := σ) I x
  map_one' := actualIdealResidue_one x
  map_mul' I J := actualIdealResidue_ideal_mul I J x

theorem prime_reciprocity
    (C : A.GeneralArithmeticContext σ η hS)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (u : Kˣ) (hu : (u : K) = (a : K)) (hallowed : A.IsAllowed C.correction.B u)
    (p : ExteriorPrime A) (hcop : IsCoprime I.val (primeIdeal p).val) :
    σ (A.sexticResidue (primeIdeal p) a) =
      actualIdealResidue (A := A) (σ := σ) I.val (generator C p) := by
  sorry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem active_prime_dvd (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (i : activeSupport Finset.univ m n) :
    (primeIdeal (p i.val)).val ∣ (firstActiveIdeal p m n).val := by
  sorry

/-- The true active character on the original residual generator is
the product of the reciprocal original prime-generator values. -/
theorem active_character_reciprocity
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (u : Kˣ) (hu : (u : K) = (a : K)) (hallowed : A.IsAllowed C.correction.B u)
    (hcop : IsCoprime I.val (firstActiveIdeal p m n).val) :
    actualFirstActiveCharacter C p hp m n (Ideal.Quotient.mk _ a) =
      ∏ i : activeSupport Finset.univ m n,
        actualIdealResidue (A := A) (σ := σ) I.val (generator C (p i.val)) ^
          netExponent (m i.val) (n i.val) := by
  sorry

theorem active_generator_residue
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (I : A.Exterior) :
    actualIdealResidue (A := A) (σ := σ) I.val (firstActiveGenerator C p m n) =
      ∏ i : activeSupport Finset.univ m n,
        actualIdealResidue (A := A) (σ := σ) I.val (generator C (p i.val)) := by
  sorry

variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)

include hΓ in
theorem residue_star (I : A.Exterior) (a : A.R) (ha : A.Generates I a) (x : A.R) :
    star (actualIdealResidue (A := A) (σ := σ) I.val x) =
      (actualIdealResidue (A := A) (σ := σ) I.val x)⁻¹ := by
  sorry

include hΓ in
theorem residue_prime_ne_zero
    (C : A.GeneralArithmeticContext σ η hS)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (p : ExteriorPrime A) (hcop : IsCoprime I.val (primeIdeal p).val) :
    actualIdealResidue (A := A) (σ := σ) I.val (generator C p) ≠ 0 := by
  sorry

/-- The left first-transform factor contributes the actual exponent
`1 + netExponent` at every displayed active prime. -/
theorem first_left_factor
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (u : Kˣ) (hu : (u : K) = (a : K)) (hallowed : A.IsAllowed C.correction.B u)
    (hcop : IsCoprime I.val (firstActiveIdeal p m n).val) (δ : A.R) :
    firstLeftDivisorFactor (generatedOriginalColumn (σ := σ) hΓ I a ha)
        (actualActiveColumn hΓ C p hp m n) δ =
      actualIdealResidue (A := A) (σ := σ) I.val δ *
        ∏ i : activeSupport Finset.univ m n,
          actualIdealResidue (A := A) (σ := σ) I.val (generator C (p i.val)) ^
            (1 + (netExponent (m i.val) (n i.val) : ℤ)) := by
  sorry

/-- The right first-transform factor keeps the inverse active phase.
Even a zero displayed exponent does not delete that prime's full mask. -/
theorem first_right_factor
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (u : Kˣ) (hu : (u : K) = (a : K)) (hallowed : A.IsAllowed C.correction.B u)
    (hcop : IsCoprime I.val (firstActiveIdeal p m n).val) (δ : A.R) :
    firstRightDivisorFactor (generatedOriginalColumn (σ := σ) hΓ I a ha)
        (actualActiveColumn hΓ C p hp m n) δ =
      actualIdealResidue (A := A) (σ := σ) I.val δ *
        ∏ i : activeSupport Finset.univ m n,
          actualIdealResidue (A := A) (σ := σ) I.val (generator C (p i.val)) ^
            (1 - (netExponent (m i.val) (n i.val) : ℤ)) := by
  sorry

/-- The common-support construction itself proves every residual
column is outside the active support. No column mask is assumed. -/
theorem residual_active_coprimalities
    {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
    {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
    (b : FirstCommonCharacterBlock fullI fullJ DE) :
    (∀ i, IsCoprime (b.leftResidual i).val
      (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val) ∧
    (∀ j, IsCoprime (b.rightResidual j).val
      (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val) := by
  sorry

/-- The actual inverse mask-generator phase, even for an empty mask.
Its value is never replaced by one merely because its generator is a unit. -/
theorem generated_divisor_phase (I : A.Exterior) (a : A.R)
    (ha : A.Generates I a) (δ : A.R) :
    (generatedOriginalColumn (σ := σ) hΓ I a ha).divisorPhase δ =
      (idealPhase (σ := σ) δ I.val)⁻¹ := by
  sorry

/-- The full real ideal-norm power is multiplicative, also on zero
ideals. Only actual nonzero exterior ideals enter the later chart. -/
def normPower (δ : ℝ) : Ideal (𝓞 K) →* ℂ where
  toFun I := (((Ideal.absNorm I : ℝ) ^ δ : ℝ) : ℂ)
  map_one' := by simp
  map_mul' I J := by
    simp only [map_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg (Ideal.absNorm I))
        (Nat.cast_nonneg (Ideal.absNorm J)), Complex.ofReal_mul]

/-- The exact multiplicative weight of the second logarithmic chart.
The fixed original unit phase and the full norm tilt occur once each. -/
def secondWeight (δ : ℝ) (ε : A.R) : Ideal (𝓞 K) →* ℂ where
  toFun I := normPower δ I * (idealPhase (σ := σ) ε I)⁻¹
  map_one' := by simp only [map_one, inv_one, one_mul]
  map_mul' I J := by
    simp only [map_mul, mul_inv_rev]
    ring

theorem original_second_coefficient (c : ℂ) (I : A.Exterior) (a : A.R)
    (ha : A.Generates I a) (δ : ℝ) (ε : A.R) :
    (c * ((A.exteriorNorm I ^ δ : ℝ) : ℂ)) *
        (generatedOriginalColumn (σ := σ) hΓ I a ha).divisorPhase ε =
      c * secondWeight (σ := σ) δ ε I.val := by
  sorry

section Cartesian

variable {k : ℕ}

/-- Every original occurrence receives the same actual multiplicative
ideal factor. Repeated primes and the zero-slot case are covered. -/
theorem rectangle_mul_ideal_weight
    (M : Ideal (𝓞 K) →* ℂ)
    (left right : Ideal (𝓞 K) → ℂ)
    (slot : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) :
    childCartesianCoefficient left right slot i * M (allocationColumnIdeal i) =
      childCartesianCoefficient (fun I => left I * M I) (fun J => right J * M J)
        (fun j p => slot j p * M p.asIdeal) i := by
  sorry

/-- The same multiplicative weight acts on both original rectangles;
the complete subtraction stays inside the later Fourier-column norm. -/
theorem centered_rectangle_mul_ideal_weight
    (M : Ideal (𝓞 K) →* ℂ)
    (left right comparisonLeft comparisonRight : Ideal (𝓞 K) → ℂ)
    (slot : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) :
    (childCartesianCoefficient left right slot i -
      childCartesianCoefficient comparisonLeft comparisonRight slot i) *
        M (allocationColumnIdeal i) =
      childCartesianCoefficient (fun I => left I * M I) (fun J => right J * M J)
        (fun j p => slot j p * M p.asIdeal) i -
      childCartesianCoefficient (fun I => comparisonLeft I * M I)
        (fun J => comparisonRight J * M J) (fun j p => slot j p * M p.asIdeal) i := by
  sorry

/-- The trivial ray parameter has the actual unit value on either side.
This does not assert that an arithmetic mask-generator phase is trivial. -/
theorem punit_phase (side : SecondColumnSide) (χ : (PUnit × PUnit) →* Circle)
    (x : PUnit) : (side.phase PUnit χ x : ℂ) = 1 := by
  sorry

end Cartesian

theorem unramified_zpow {χ : HeckeCharacter K} {p : HeightOneSpectrum (𝓞 K)}
    (hχ : UnramifiedAt K χ p) (n : ℤ) : UnramifiedAt K (χ ^ n) p := by
  sorry

theorem coefficient_pow (χ : HeckeCharacter K) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hχ : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → UnramifiedAt K χ p)
    (n : ℕ) : heckeIdealCoefficient K (χ ^ n) I = heckeIdealCoefficient K χ I ^ n := by
  sorry

theorem coefficient_inv (χ : HeckeCharacter K) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hχ : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → UnramifiedAt K χ p) :
    heckeIdealCoefficient K χ⁻¹ I = (heckeIdealCoefficient K χ I)⁻¹ := by
  sorry

theorem coefficient_zpow (χ : HeckeCharacter K) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hχ : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → UnramifiedAt K χ p)
    (n : ℤ) : heckeIdealCoefficient K (χ ^ n) I = heckeIdealCoefficient K χ I ^ n := by
  sorry

theorem coefficient_prod {J : Type*} (s : Finset J) (χ : J → HeckeCharacter K)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hχ : ∀ j ∈ s, ∀ p : HeightOneSpectrum (𝓞 K),
      p.asIdeal ∣ I.val → UnramifiedAt K (χ j) p) :
    heckeIdealCoefficient K (∏ j ∈ s, χ j) I =
      ∏ j ∈ s, heckeIdealCoefficient K (χ j) I := by
  sorry

end CanonicalSecondRectangularFactors

namespace OriginalMovingFactors

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable (D : OriginalMovingFactors A P R)

/-- The displayed actual elements and integer exponents, before any
character replacement or cancellation of their displayed support. -/
def residueValue (I : Ideal (𝓞 K)) : ℂ :=
  ∏ i, actualIdealResidue (A := A) (σ := σ) I (D.element i).val ^ D.power i

def residueHom : Ideal (𝓞 K) →* ℂ where
  toFun := D.residueValue (σ := σ)
  map_one' := by
    simp only [residueValue, actualIdealResidue_one, one_zpow, Finset.prod_const_one]
  map_mul' I J := by
    simp only [residueValue, actualIdealResidue_ideal_mul, mul_zpow, Finset.prod_mul_distrib]

theorem append_residueValue (E : OriginalMovingFactors A P R) (I : Ideal (𝓞 K)) :
    (D.append E).residueValue (σ := σ) I =
      D.residueValue (σ := σ) I * E.residueValue (σ := σ) I := by
  sorry

theorem factor_generates (i : Fin D.count) :
    A.Generates (D.factorIdeal i) (D.element i).val := by
  sorry

theorem factorIdeal_dvd (i : Fin D.count) : (D.factorIdeal i).val ∣ D.fullIdeal.val := by
  sorry

theorem factor_evaluation_of_coprime (i : Fin D.count) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) I)
    (hcop : IsCoprime I.val (D.factorIdeal i).val) :
    HeckeGeneral.Analysis.SquarefreeAmplification.zeroExtendedSexticIdealEvaluation K
        (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P.arithmetic.root6
        P.arithmetic.primitive6 P.arithmetic.embedding I (D.element i).val =
      heckeIdealCoefficient K (D.factorCharacter i) I := by
  sorry

/-- The original zero extension kills an actual factor sharing a prime
with the column. This statement also applies when its primitive
character alone has a smaller conductor. -/
theorem factor_residue_zero_of_not_coprime
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (i : Fin D.count) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hcop : ¬IsCoprime I.val (D.factorIdeal i).val) :
    actualIdealResidue (A := A) (σ := σ) I.val (D.element i).val = 0 := by
  sorry

/-- Nonvanishing of the original symbol proves unramifiedness of each
computed factor character away from its actual full ideal. -/
theorem factorCharacter_unramified (i : Fin D.count)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hcop : IsCoprime p.asIdeal (D.factorIdeal i).val) :
    UnramifiedAt K (D.factorCharacter i) p := by
  sorry

theorem character_unramified (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hcop : IsCoprime p.asIdeal D.support.val) : UnramifiedAt K D.character p := by
  sorry

/-- The actual moving coefficient is its displayed original residue
product on the complete live mask. All local hypotheses are proved
from the original factor ideals; none is a supplied dictionary. -/
theorem character_coefficient_of_coprime
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) I)
    (hcop : IsCoprime I.val D.support.val) :
    heckeIdealCoefficient K D.character I = D.residueValue (σ := σ) I.val := by
  sorry

/-- The original fixed background may be ramified. Only the computed
moving factors are split, on their already proved full live mask. -/
theorem background_coefficient_of_coprime
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (background : HeckeCharacter K) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) I)
    (hcop : IsCoprime I.val D.support.val) :
    heckeIdealCoefficient K (background * D.character) I =
      heckeIdealCoefficient K background I * D.residueValue (σ := σ) I.val := by
  sorry

/-- Coefficient factorization with the complete displayed moving mask.
The extra zero is explicit until a subsequent original-symbol identity
shows that it was already present. -/
theorem background_coefficient_masked
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (background : HeckeCharacter K) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) I) :
    heckeIdealCoefficient K (background * D.character) I *
        (if IsCoprime I.val D.support.val then (1 : ℂ) else 0) =
      heckeIdealCoefficient K background I * D.residueValue (σ := σ) I.val *
        (if IsCoprime I.val D.support.val then (1 : ℂ) else 0) := by
  sorry

end OriginalMovingFactors

namespace CanonicalSecondRectangularFactors

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original active prime generators are recorded individually.
Both signs use the same displayed list, including exponent zero. -/
def firstActiveMovingFactors (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (right : Bool) :
    OriginalMovingFactors A P R where
  count := Fintype.card (activeSupport Finset.univ m n)
  element i :=
    ⟨generator C (p ((Fintype.equivFin (activeSupport Finset.univ m n)).symm i).val),
      (generator_generates C _).1⟩
  power i :=
    let j := ((Fintype.equivFin (activeSupport Finset.univ m n)).symm i).val
    if right then 1 - (netExponent (m j) (n j) : ℤ)
      else 1 + (netExponent (m j) (n j) : ℤ)

theorem firstActiveMovingFactors_residue
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (right : Bool) (I : Ideal (𝓞 K)) :
    (firstActiveMovingFactors P R C p m n right).residueValue (σ := σ) I =
      ∏ i : activeSupport Finset.univ m n,
        actualIdealResidue (A := A) (σ := σ) I (generator C (p i.val)) ^
          (if right then 1 - (netExponent (m i.val) (n i.val) : ℤ)
           else 1 + (netExponent (m i.val) (n i.val) : ℤ)) := by
  sorry

theorem firstActiveMovingFactors_fullIdeal
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (right : Bool) :
    (firstActiveMovingFactors P R C p m n right).fullIdeal = firstActiveIdeal p m n := by
  sorry

/-- The literal first physical mask generator precedes the original
active list. It is not replaced by an independently selected element. -/
def firstMovingFactors (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (right : Bool)
    (δ : NonzeroRingElements A.R) : OriginalMovingFactors A P R :=
  (OriginalMovingFactors.singleton δ 1).append (firstActiveMovingFactors P R C p m n right)

theorem firstMovingFactors_residue
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (right : Bool)
    (δ : NonzeroRingElements A.R) (I : Ideal (𝓞 K)) :
    (firstMovingFactors P R C p m n right δ).residueValue (σ := σ) I =
      actualIdealResidue (A := A) (σ := σ) I δ.val *
        ∏ i : activeSupport Finset.univ m n,
          actualIdealResidue (A := A) (σ := σ) I (generator C (p i.val)) ^
            (if right then 1 - (netExponent (m i.val) (n i.val) : ℤ)
             else 1 + (netExponent (m i.val) (n i.val) : ℤ)) := by
  sorry

theorem firstMovingFactors_fullIdeal
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (right : Bool)
    (Iδ : A.Exterior) (δ : A.R) (hδ : A.Generates Iδ δ) :
    (firstMovingFactors P R C p m n right ⟨δ, hδ.1⟩).fullIdeal =
      ExteriorIdealEuler.mul Iδ (firstActiveIdeal p m n) := by
  sorry

theorem firstMovingFactors_coprime_support_iff
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (right : Bool)
    (δ : NonzeroRingElements A.R) (Iδ : A.Exterior) (hδ : A.Generates Iδ δ.val)
    (I : Ideal (𝓞 K)) (hactive : IsCoprime I (firstActiveIdeal p m n).val) :
    IsCoprime I (firstMovingFactors P R C p m n right δ).support.val ↔
      IsCoprime I Iδ.val := by
  sorry

/-- The first physical mask zero is already in the actual divisor
factor. The active factors, including any zero exponent, are coprime
to each original residual occurrence. -/
theorem firstMovingFactors_residue_mask
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (right : Bool)
    (δ : NonzeroRingElements A.R) (Iδ : A.Exterior) (hδ : A.Generates Iδ δ.val)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) (hactive : IsCoprime I.val (firstActiveIdeal p m n).val) :
    (firstMovingFactors P R C p m n right δ).residueValue (σ := σ) I.val *
        (if IsCoprime I.val (firstMovingFactors P R C p m n right δ).support.val
          then (1 : ℂ) else 0) =
      (firstMovingFactors P R C p m n right δ).residueValue (σ := σ) I.val := by
  sorry

/-- The original first multiplier is absorbed into the computed fixed
moving character with all physical mask zeros retained. The background
may be ramified; no multiplicativity of two ramified characters is used. -/
theorem firstMovingFactors_masked_coefficient
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (right : Bool)
    (δ : NonzeroRingElements A.R) (Iδ : A.Exterior) (hδ : A.Generates Iδ δ.val)
    (background : HeckeCharacter K) (oldMask : HeckeGeneral.Analysis.NonzeroIdeal K) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) I)
    (hactive : IsCoprime I.val (firstActiveIdeal p m n).val) :
    heckeIdealCoefficient K
        (background * (firstMovingFactors P R C p m n right δ).character) I *
        (if IsCoprime I.val
            (oldMask.val * (firstMovingFactors P R C p m n right δ).support.val)
          then (1 : ℂ) else 0) =
      (heckeIdealCoefficient K background I *
        (if IsCoprime I.val oldMask.val then (1 : ℂ) else 0)) *
          (firstMovingFactors P R C p m n right δ).residueValue (σ := σ) I.val := by
  sorry

variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)

theorem first_left_factor_moving
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (u : Kˣ) (hu : (u : K) = (a : K)) (hallowed : A.IsAllowed C.correction.B u)
    (hcop : IsCoprime I.val (firstActiveIdeal p m n).val)
    (δ : NonzeroRingElements A.R) :
    firstLeftDivisorFactor (generatedOriginalColumn (σ := σ) hΓ I a ha)
        (actualActiveColumn hΓ C p hp m n) δ.val =
      (firstMovingFactors P R C p m n false δ).residueValue (σ := σ) I.val := by
  sorry

theorem first_right_factor_moving
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (u : Kˣ) (hu : (u : K) = (a : K)) (hallowed : A.IsAllowed C.correction.B u)
    (hcop : IsCoprime I.val (firstActiveIdeal p m n).val)
    (δ : NonzeroRingElements A.R) :
    firstRightDivisorFactor (generatedOriginalColumn (σ := σ) hΓ I a ha)
        (actualActiveColumn hΓ C p hp m n) δ.val =
      (firstMovingFactors P R C p m n true δ).residueValue (σ := σ) I.val := by
  sorry

/-- The canonical original block supplies the allowed residual generator
and its actual coprimality with the active support. Neither is a new
input to the moving factorization. -/
theorem canonical_first_left_factor_moving
    (C : A.GeneralArithmeticContext σ η hS)
    {α β : Type*} (left : Finset α) (right : Finset β)
    (fullI : α → A.Exterior) (fullJ : β → A.Exterior)
    (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
    (hDE : DE ∈ commonSupportPool left right
      (fun i => (fullI i).val) (fun j => (fullJ j).val))
    (δ : NonzeroRingElements A.R) (i : α) :
    let b := canonicalFirstCommonBlock C left right fullI fullJ DE hDE
    firstLeftDivisorFactor
        (generatedOriginalColumn (σ := σ) hΓ (b.leftResidual i)
          (b.leftGenerator i) (b.left_generates i))
        (actualActiveColumn hΓ C b.primes b.primes_injective
          b.leftMultiplicity b.rightMultiplicity) δ.val =
      (firstMovingFactors P R C b.primes b.leftMultiplicity b.rightMultiplicity false δ).residueValue (σ := σ) (b.leftResidual i).val := by
  sorry

theorem canonical_first_right_factor_moving
    (C : A.GeneralArithmeticContext σ η hS)
    {α β : Type*} (left : Finset α) (right : Finset β)
    (fullI : α → A.Exterior) (fullJ : β → A.Exterior)
    (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
    (hDE : DE ∈ commonSupportPool left right
      (fun i => (fullI i).val) (fun j => (fullJ j).val))
    (δ : NonzeroRingElements A.R) (j : β) :
    let b := canonicalFirstCommonBlock C left right fullI fullJ DE hDE
    firstRightDivisorFactor
        (generatedOriginalColumn (σ := σ) hΓ (b.rightResidual j)
          (b.rightGenerator j) (b.right_generates j))
        (actualActiveColumn hΓ C b.primes b.primes_injective
          b.leftMultiplicity b.rightMultiplicity) δ.val =
      (firstMovingFactors P R C b.primes b.leftMultiplicity b.rightMultiplicity true δ).residueValue (σ := σ) (b.rightResidual j).val := by
  sorry

/-- The second divisor phase uses the actual inverse chosen unit.
Keeping it as an original factor records the exact fixed arithmetic. -/
def secondMaskMovingFactors (ε : NonzeroRingElements A.R) : OriginalMovingFactors A P R :=
  OriginalMovingFactors.singleton ε (-1)

theorem secondMaskMovingFactors_residue (ε : NonzeroRingElements A.R)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a) :
    (generatedOriginalColumn (σ := σ) hΓ I a ha).divisorPhase ε.val =
      (secondMaskMovingFactors P R ε).residueValue (σ := σ) I.val := by
  sorry

variable [IsPrincipalIdealRing A.R]

theorem empty_mask_generator_generates :
    A.Generates (unitExterior A)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅).val := by
  sorry

/-- The actual empty-mask phase has no displayed ideal cost, although
its finite unit character has not been replaced by the trivial character. -/
theorem second_empty_mask_fullIdeal :
    (secondMaskMovingFactors P R
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅)).fullIdeal =
      unitExterior A := by
  sorry

theorem second_empty_mask_support :
    (secondMaskMovingFactors P R
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅)).support =
      unitExterior A := by
  sorry

end CanonicalSecondRectangularFactors

namespace CompleteMovingRowRecipe

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (ξ : X)

private theorem original_plain_coefficient (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    sourcePlainCoefficient
        (CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
          (Q.correction * Q.moving.character) Q.arithmeticMask id).plain
        (CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
          (Q.correction * Q.moving.character) Q.arithmeticMask id).plainTwist
        (CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
          (Q.correction * Q.moving.character) Q.arithmeticMask id).mask I =
      (Q.arithmeticAtoms ξ).leftArithmetic I := by
  sorry

private theorem original_prime_coefficient
    (i : Fin (data ξ).geometry.slotCount) (p : HeightOneSpectrum (𝓞 K)) :
    sourcePrimeCoefficient
        ((CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
          (Q.correction * Q.moving.character) Q.arithmeticMask id).slot i)
        ((CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
          (Q.correction * Q.moving.character) Q.arithmeticMask id).slotTwist i)
        (CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
          (Q.correction * Q.moving.character) Q.arithmeticMask id).mask p =
      (Q.arithmeticAtoms ξ).primeArithmetic i p := by
  sorry

variable (W : NormProfileRecipe (fun _ : PUnit => data ξ))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ)
variable (side : SecondColumnSide) (χ : (PUnit × PUnit) →* Circle)
variable (S₁ S₂ : Finset (Ideal (𝓞 K)))
variable (S : Fin (data ξ).geometry.slotCount → Finset (HeightOneSpectrum (𝓞 K)))

/-- The exact original per-occurrence table, built from the same
computed parent atoms. No new arithmetic identification is a field. -/
def originalTermDictionary (comparison : Bool) :
    SecondCoefficientTermDictionary
      (CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
        (Q.correction * Q.moving.character) Q.arithmeticMask id)
      (side.phase PUnit χ) S₁ S₂ S where
  leftAtom I := ((Q.arithmeticAtoms ξ).constantAtoms W a Z t).leftValue
    (if comparison then Y₁ else Z ^ a.n₁) (sourceMomentIdeal I)
  rightAtom I := ((Q.arithmeticAtoms ξ).constantAtoms W a Z t).rightValue
    (if comparison then Y₂ else Z ^ a.n₂) (sourceMomentIdeal I)
  slotAtom := ((Q.arithmeticAtoms ξ).constantAtoms W a Z t).primeValue
  leftRay _ := PUnit.unit
  rightRay _ := PUnit.unit
  slotRay _ _ := PUnit.unit
  scale₁ := if comparison then Y₁ else Z ^ a.n₁
  scale₂ := if comparison then Y₂ else Z ^ a.n₂
  base := Z
  length i := ((data ξ).geometry.slots i).length
  leftWeight I := W.left PUnit.unit t
    (idealNorm K I / (if comparison then Y₁ else Z ^ a.n₁))
  rightWeight I := W.right PUnit.unit t
    (idealNorm K I / (if comparison then Y₂ else Z ^ a.n₂))
  slotWeight i p := ((data ξ).geometry.slots i).profile t
    ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ ((data ξ).geometry.slots i).length)
  plain₁ I _ := by
    rw [CanonicalSecondRectangularFactors.punit_phase, mul_one,
      Q.original_plain_coefficient ξ] <;> rfl
  plain₂ I _ := by
    rw [CanonicalSecondRectangularFactors.punit_phase, mul_one,
      Q.original_plain_coefficient ξ] <;> rfl
  prime i p _ := by
    rw [CanonicalSecondRectangularFactors.punit_phase, mul_one,
      Q.original_prime_coefficient ξ] <;> rfl

/-- It is literally the original rectangle before the first transform,
evaluated at the actual Cartesian ideal and prime occurrences. -/
theorem originalTermDictionary_coefficient (comparison : Bool)
    (i : AllocationColumn K (data ξ).geometry.slotCount) :
    (Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S comparison).coefficient i =
      (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).rectangle comparison
        ((sourceMomentIdeal i.1.1, sourceMomentIdeal i.1.2), i.2) := rfl

theorem originalTermDictionary_bare (comparison : Bool)
    (i : AllocationColumn K (data ξ).geometry.slotCount)
    (hi : i ∈ childCartesianColumns S₁ S₂ S) :
    (Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S comparison).coefficient i =
      rawBareSourceCoefficient
        (CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
          (Q.correction * Q.moving.character) Q.arithmeticMask id)
        (if comparison then Y₁ else Z ^ a.n₁) (if comparison then Y₂ else Z ^ a.n₂)
        Z (fun j => ((data ξ).geometry.slots j).length)
        (fun I => W.left PUnit.unit t (idealNorm K I / (if comparison then Y₁ else Z ^ a.n₁)))
        (fun I => W.right PUnit.unit t (idealNorm K I / (if comparison then Y₂ else Z ^ a.n₂)))
        (fun j p => ((data ξ).geometry.slots j).profile t
          ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ ((data ξ).geometry.slots j).length)) i := by
  sorry

/-- Both comparison scales use the same original characters, prime
occurrences and finite-ray labels. Only the two plain tests change. -/
def originalComparison : SecondCoefficientComparison
    (Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S false) where
  leftAtom := (Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S true).leftAtom
  rightAtom := (Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S true).rightAtom
  scale₁ := Y₁
  scale₂ := Y₂
  leftWeight := (Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S true).leftWeight
  rightWeight := (Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S true).rightWeight
  plain₁ := (Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S true).plain₁
  plain₂ := (Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S true).plain₂

@[simp] theorem originalComparison_dictionary :
    (Q.originalComparison ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S).dictionary =
      Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S true := rfl

/-- The original whole centered coefficient is an output of the two
single-atom dictionaries. There is one shared additional normalizer. -/
theorem originalComparison_centeredCoefficient (u v : ℂ)
    (w : Fin (data ξ).geometry.slotCount → ℂ)
    (i : AllocationColumn K (data ξ).geometry.slotCount) :
    (Q.originalComparison ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S).centeredCoefficient u v w i =
      SecondCoefficientTermDictionary.centralNormalizer u v w *
        (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient true
          ((sourceMomentIdeal i.1.1, sourceMomentIdeal i.1.2), i.2) := by
  sorry

variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch S₁ S₂ S support)

/-- The common scalar consists of the original two extracted ideals
and the actual frozen prime occurrences. It is shared by the main and
comparison scales. -/
def originalCommonScalar : ℂ :=
  b.bareCommonScalar
    (CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
      (Q.correction * Q.moving.character) Q.arithmeticMask id)
    Z (fun j => ((data ξ).geometry.slots j).length)
    (fun j p => ((data ξ).geometry.slots j).profile t
      ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ ((data ξ).geometry.slots j).length))

/-- The residual coefficient uses exactly the selected original slot
indices and the original tests evaluated at the reconstructed ideals. -/
def originalResidualCoefficient (comparison : Bool) :
    AllocationColumn K b.keep.card → ℂ :=
  b.bareResidualCoefficient
    (CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
      (Q.correction * Q.moving.character) Q.arithmeticMask id)
    (if comparison then Y₁ else Z ^ a.n₁) (if comparison then Y₂ else Z ^ a.n₂)
    Z (fun j => ((data ξ).geometry.slots j).length)
    (fun I => W.left PUnit.unit t
      (idealNorm K I / (if comparison then Y₁ else Z ^ a.n₁)))
    (fun I => W.right PUnit.unit t
      (idealNorm K I / (if comparison then Y₂ else Z ^ a.n₂)))
    (fun j p => ((data ξ).geometry.slots j).profile t
      ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ ((data ξ).geometry.slots j).length))

/-- Common extraction is an identity of the actual computed parent
coefficient, with no new coefficient factorization premise. -/
theorem originalTermDictionary_extract (comparison : Bool)
    (y : AllocationColumn K b.keep.card) (hy : y ∈ b.residualColumns) :
    (Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S comparison).coefficient (b.reconstruct y) =
      Q.originalCommonScalar ξ Z t S₁ S₂ S b *
        Q.originalResidualCoefficient ξ W a Z t Y₁ Y₂ S₁ S₂ S b comparison y := by
  sorry

/-- The complete original subtraction has one common extracted scalar.
Both residual rectangles retain the same actual prime slots. -/
theorem original_centered_extract
    (y : AllocationColumn K b.keep.card) (hy : y ∈ b.residualColumns) :
    (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient true
        ((sourceMomentIdeal (b.reconstruct y).1.1,
          sourceMomentIdeal (b.reconstruct y).1.2), (b.reconstruct y).2) =
      Q.originalCommonScalar ξ Z t S₁ S₂ S b *
        (Q.originalResidualCoefficient ξ W a Z t Y₁ Y₂ S₁ S₂ S b false y -
          Q.originalResidualCoefficient ξ W a Z t Y₁ Y₂ S₁ S₂ S b true y) := by
  sorry

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondRectangularFactors.first_left_factor
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondRectangularFactors.first_right_factor
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalMovingFactors.character_coefficient_of_coprime
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondRectangularFactors.firstMovingFactors_masked_coefficient
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondRectangularFactors.canonical_first_left_factor_moving
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondRectangularFactors.canonical_first_right_factor_moving
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondRectangularFactors.second_empty_mask_support
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.originalTermDictionary
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.original_centered_extract
