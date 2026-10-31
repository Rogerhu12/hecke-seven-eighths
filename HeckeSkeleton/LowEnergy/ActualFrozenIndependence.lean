import HeckeSkeleton.LowEnergy.ActualFrozenMajorant

/-!
# Coefficient independence and the exact weighted actual reflected term

The dual coefficient is transported to a datum with unit moving ideal and no
marks.  Its reflection index also has no active marks.  Consequently neither
the varying row nor the active marked ideal occurs in the surviving coefficient
data.  This independence is proved, rather than supplied to the hybrid estimate.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.ActualFrozenIndependence

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.IdealRows HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualFrozenCube HeckeSkeleton.LowEnergy.ActualFrozenMajorant
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

def frozenDigit (frozen : ExteriorIdeal K S) (p : ExteriorPrime K S) : Fin 6 :=
  ⟨primeExponents frozen.val p.val % 6, Nat.mod_lt _ (by decide)⟩

theorem moving_not_dvd_frozenPrime (d : MarkedDatum K S) (p : ExteriorPrime K S)
    (hp : p ∈ frozenPrimes K S d) : ¬p.val.asIdeal ∣ d.moving.val.val := by
  intro hm
  rcases Finset.mem_union.mp hp with hf | hr
  · exact p.val.prime.not_unit (d.moving_frozen_coprime.isUnit_of_dvd' hm
      ((mem_exteriorSupport_iff K S d.frozen p).mp hf))
  · exact p.val.prime.not_unit (d.moving_puncture_coprime.isUnit_of_dvd' hm
      ((mem_exteriorSupport_iff K S d.puncture p).mp hr))

/-- At every ordinary frozen prime the digit uses only the frozen ideal. -/
theorem rowDigit_frozen_primes (d : MarkedDatum K S) (p : ExteriorPrime K S)
    (hp : p ∈ frozenPrimes K S d) : rowDigit K S d p = frozenDigit K S d.frozen p := by
  have hm : primeExponents d.moving.val p.val = 0 := by
    by_contra h
    exact moving_not_dvd_frozenPrime K S d p hp
      ((exponent_ne_zero_iff_dvd d.moving.val p.val).mp h)
  apply Fin.ext
  change primeExponents (d.moving.val * d.frozen.val) p.val % 6 =
    primeExponents d.frozen.val p.val % 6
  rw [primeExponents_mul, Finsupp.add_apply, hm, zero_add]

/-- This constructor retains exactly frozen, puncture and unit data. -/
def frozenOnlyDatum (d : MarkedDatum K S) : MarkedDatum K S where
  moving := primeSetIdeal K S ∅
  frozen := d.frozen
  puncture := d.puncture
  moving_squarefree := by rw [emptyPrimeIdeal_val]; exact squarefree_one
  puncture_squarefree := d.puncture_squarefree
  moving_frozen_coprime := by rw [emptyPrimeIdeal_val]; exact isCoprime_one_left
  moving_puncture_coprime := by rw [emptyPrimeIdeal_val]; exact isCoprime_one_left
  rowUnit := d.rowUnit
  marks := ∅
  marks_coprime := by simp

theorem frozenOnlyDatum_eq_of_frozen_data (d e : MarkedDatum K S)
    (hf : d.frozen = e.frozen) (hr : d.puncture = e.puncture) (hu : d.rowUnit = e.rowUnit) :
    frozenOnlyDatum K S d = frozenOnlyDatum K S e := by
  cases d
  cases e
  cases hf
  cases hr
  cases hu
  rfl

variable (d : MarkedDatum K S) (i : ReflectionIndex K S d)

theorem rowDigit_frozenOnly (p : ExteriorPrime K S) (hp : p ∈ i.activeFrozen) :
    rowDigit K S d p = rowDigit K S (frozenOnlyDatum K S d) p := by
  exact (rowDigit_frozen_primes K S d p (i.frozen_subset hp)).trans
    (rowDigit_frozen_primes K S (frozenOnlyDatum K S d) p (i.frozen_subset hp)).symm

/-- The dual index no longer contains any active-mark data. -/
def frozenOnlyIndex : ReflectionIndex K S (frozenOnlyDatum K S d) where
  activeMarks := ∅
  marks_subset := Finset.empty_subset _
  activeFrozen := i.activeFrozen
  frozen_subset := i.frozen_subset
  nonzero_active := by
    intro p hp hn
    apply i.nonzero_active p hp
    have he := (rowDigit_frozen_primes K S d p hp).trans
      (rowDigit_frozen_primes K S (frozenOnlyDatum K S d) p hp).symm
    simpa only [he] using hn
  numeratorFrozen := i.numeratorFrozen
  frozen_support := i.frozen_support
  frozen_digits := i.frozen_digits
  n := i.n
  n_coprime := by
    have hn : IsCoprime i.n.val.val
        ((primeSetIdeal K S i.activeFrozen).val.val *
          (primeSetIdeal K S i.activeMarks).val.val) := i.n_coprime
    have hf := (IsCoprime.mul_right_iff.mp hn).1
    change IsCoprime i.n.val.val
      ((primeSetIdeal K S i.activeFrozen).val.val * (primeSetIdeal K S ∅).val.val)
    rw [emptyPrimeIdeal_val, mul_one]
    exact hf
  c := i.c
  c_squarefree := i.c_squarefree
  c_coprime := i.c_coprime
  unitSector := i.unitSector

/-- All scalar and local factors agree after removing moving-row and mark data. -/
theorem frozenOmega_frozenOnly (θ : HeckeCharacter K) :
    frozenOmega K S D d i θ =
      frozenOmega K S D (frozenOnlyDatum K S d) (frozenOnlyIndex K S d i) θ := by
  unfold frozenOmega
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [rowDigit_frozenOnly K S d i p hp]
  rfl

theorem reflectedColumnFactor_frozenOnly (θ : HeckeCharacter K) :
    reflectedColumnFactor K S D d i θ =
      reflectedColumnFactor K S D (frozenOnlyDatum K S d) (frozenOnlyIndex K S d i) θ := by
  unfold reflectedColumnFactor
  congr 1
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [rowDigit_frozenOnly K S d i p hp]
  rfl

theorem normalizedFrozenOmega_frozenOnly (θ : HeckeCharacter K) :
    normalizedFrozenOmega K S D d i θ =
      normalizedFrozenOmega K S D (frozenOnlyDatum K S d) (frozenOnlyIndex K S d i) θ := by
  unfold normalizedFrozenOmega
  rw [frozenOmega_frozenOnly K S D d i θ]
  rfl

/-- This is the row/mark-independence assertion used when fixing the common
hybrid coefficient.  The right-hand datum has moving=1 and marks=empty. -/
theorem fullCubeCoefficient_frozenOnly (θ : HeckeCharacter K) :
    fullCubeCoefficient K S D d i θ =
      fullCubeCoefficient K S D (frozenOnlyDatum K S d) (frozenOnlyIndex K S d i) θ := by
  unfold fullCubeCoefficient
  rw [normalizedFrozenOmega_frozenOnly K S D d i θ,
    reflectedColumnFactor_frozenOnly K S D d (minimumIndex K S d i) θ]
  rfl

/-- The original support restrictions give the full-cube active-mark mask. -/
theorem numeratorCube_coprime_activeMarked :
    IsCoprime (numeratorCube K S d i).val.val (activeMarkedIdeal K S d i).val.val := by
  apply Ideal.coprime_of_no_prime_ge
  intro P hx hP hprime
  have hP0 : P ≠ ⊥ := by
    intro hz
    exact nonZeroDivisors.coe_ne_zero (numeratorCube K S d i).val
      (le_bot_iff.mp (hz ▸ hx))
  let p : HeightOneSpectrum (𝓞 K) := ⟨P, hprime, hP0⟩
  let ep : ExteriorPrime K S := ⟨p, (numeratorCube K S d i).property p
    (Ideal.dvd_iff_le.mpr hx)⟩
  have hep : ep ∈ i.activeMarks := (prime_dvd_primeSetIdeal_iff K S i.activeMarks ep).mp
    (Ideal.dvd_iff_le.mpr hP)
  exact mark_not_dvd_numeratorCube K S d i ep hep (Ideal.dvd_iff_le.mpr hx)

theorem fullCube_coprime_activeMarked :
    IsCoprime (fullCubeIdeal K S d i).val.val (activeMarkedIdeal K S d i).val.val := by
  have hn : IsCoprime i.n.val.val
      ((activeFrozenIdeal K S d i).val.val * (activeMarkedIdeal K S d i).val.val) :=
    i.n_coprime
  exact (numeratorCube_coprime_activeMarked K S d i).mul_left
    (IsCoprime.mul_right_iff.mp hn).2

def unitPeriodValue (θ : HeckeCharacter K) (u : S.unit K) (I : ExteriorIdeal K S) : ℂ :=
  heckeIdealCoefficient K θ I.val * idealSymbol K S D I (S.unitEquivUnitsInteger K u).val

/-- The mark coefficient's arguments exclude moving rows and all dual columns. -/
def separatedMarkCoefficient (θ : HeckeCharacter K) (u : S.unit K)
    (frozen minimum : ExteriorIdeal K S) (ordinary marks : Finset (ExteriorPrime K S))
    (frequency : S.unit K) : ℂ :=
  unitPeriodValue K S D θ u (primeSetIdeal K S marks) ^ 2 *
  (∏ p ∈ marks, thetaGamma K S D (exteriorPrimeIdeal K S p) 2 *
    (primeEvaluation K S D p (S.unitEquivUnitsInteger K frequency).val *
     primeEvaluation K S D p (D.generator minimum) *
     primeEvaluation K S D p (D.generator (removePrime K S (primeSetIdeal K S marks) p)) ^
       (-2 : ℤ) *
     primeEvaluation K S D p (D.generator (primeSetIdeal K S ordinary)) ^ (-2 : ℤ)) ^ 2) *
  ∏ p ∈ ordinary, primeEvaluation K S D p (D.generator (primeSetIdeal K S marks)) ^
    (-(2 * localWeylExponent (frozenDigit K S frozen p)
      (primeExponents minimum.val p.val) : ℤ))

/-- The row coefficient's arguments exclude active marks and all dual columns. -/
def separatedRowCoefficient (θ : HeckeCharacter K) (u : S.unit K)
    (frozen minimum : ExteriorIdeal K S) (ordinary : Finset (ExteriorPrime K S))
    (frequency : S.unit K) (row : ExteriorIdeal K S) : ℂ :=
  unitPeriodValue K S D θ u row ^ 2 *
  (∏ p ∈ exteriorSupport K S row, localWeylScalar K S D p ⟨1, by decide⟩ 0 *
    (primeEvaluation K S D p (S.unitEquivUnitsInteger K frequency).val *
     primeEvaluation K S D p (D.generator minimum) *
     primeEvaluation K S D p (D.generator (removePrime K S row p)) ^ (-2 : ℤ) *
     primeEvaluation K S D p (D.generator (primeSetIdeal K S ordinary)) ^ (-2 : ℤ))) *
  ∏ p ∈ ordinary, primeEvaluation K S D p (D.generator row) ^
    (-(2 * localWeylExponent (frozenDigit K S frozen p)
      (primeExponents minimum.val p.val) : ℤ))

theorem reflectedMarkFactor_eq_separated (θ : HeckeCharacter K) :
    reflectedMarkFactor K S D d i θ =
      separatedMarkCoefficient K S D θ d.rowUnit d.frozen i.numeratorFrozen
        i.activeFrozen i.activeMarks (frequencyUnit K S d i) := by
  unfold reflectedMarkFactor separatedMarkCoefficient
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [rowDigit_frozen_primes K S d p (i.frozen_subset hp)]
  rfl

theorem reflectedRowFactor_eq_separated (θ : HeckeCharacter K) :
    reflectedRowFactor K S D d i θ =
      separatedRowCoefficient K S D θ d.rowUnit d.frozen i.numeratorFrozen
        i.activeFrozen (frequencyUnit K S d i) d.moving := by
  unfold reflectedRowFactor separatedRowCoefficient
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [rowDigit_frozen_primes K S d p (i.frozen_subset hp)]
  rfl

/-- The actual reflected summand in the weighted full-cube form.  Its sole
dual coefficient has the proved frozen-only representation and norm bound. -/
theorem reflectedTerm_eq_weightedFullCube (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : ℝ → ℂ) (X : ℝ) :
    reflectedTerm K S D d i F θ V X =
      (∏ p ∈ d.marks \ i.activeMarks, (p.val.asIdeal.absNorm : ℂ)⁻¹) *
      (Real.sqrt (exteriorNorm K S (activeMarkedIdeal K S d i)) : ℂ)⁻¹ *
      reflectedMarkFactor K S D d (minimumIndex K S d i) θ *
      reflectedRowFactor K S D d (minimumIndex K S d i) θ *
      fullCubeCoefficient K S D (frozenOnlyDatum K S d) (frozenOnlyIndex K S d i) θ *
      idealSymbol K S D d.moving
        (D.generator i.c * D.generator (fullCubeIdeal K S d i)) ^ 3 *
      idealSymbol K S D (activeMarkedIdeal K S d i) (D.generator i.c) ^ (-2 : ℤ) *
      mellinReflectionKernel K S F θ (QuotientGroup.mk d.rowUnit)
        (frequencyClass K S D d i) V 0
        (X * exteriorNorm K S (numeratorMinimum K S d i) * exteriorNorm K S i.c *
          exteriorNorm K S (fullCubeIdeal K S d i) ^ 3 /
          (exteriorNorm K S d.moving * exteriorNorm K S (activeFrozenIdeal K S d i) *
            exteriorNorm K S (activeMarkedIdeal K S d i)) ^ 2) := by
  rw [reflectedTerm_eq_fullCube K S D d i hD F θ V X,
    ← fullCubeCoefficient_frozenOnly K S D d i θ]
  unfold fullCubeCoefficient
  ring

/-- Every coefficient's allowed variable dependence is visible in this exact
identity: the row factor sees row only, mark factor sees active marks only,
and the dual factor is evaluated in the frozen-only datum with no marks. -/
theorem reflectedTerm_eq_separatedFullCube (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : ℝ → ℂ) (X : ℝ) :
    reflectedTerm K S D d i F θ V X =
      (∏ p ∈ d.marks \ i.activeMarks, (p.val.asIdeal.absNorm : ℂ)⁻¹) *
      (Real.sqrt (exteriorNorm K S (activeMarkedIdeal K S d i)) : ℂ)⁻¹ *
      separatedMarkCoefficient K S D θ d.rowUnit d.frozen (numeratorMinimum K S d i)
        i.activeFrozen i.activeMarks (frequencyUnit K S d i) *
      separatedRowCoefficient K S D θ d.rowUnit d.frozen (numeratorMinimum K S d i)
        i.activeFrozen (frequencyUnit K S d i) d.moving *
      fullCubeCoefficient K S D (frozenOnlyDatum K S d) (frozenOnlyIndex K S d i) θ *
      idealSymbol K S D d.moving
        (D.generator i.c * D.generator (fullCubeIdeal K S d i)) ^ 3 *
      idealSymbol K S D (activeMarkedIdeal K S d i) (D.generator i.c) ^ (-2 : ℤ) *
      mellinReflectionKernel K S F θ (QuotientGroup.mk d.rowUnit)
        (frequencyClass K S D d i) V 0
        (X * exteriorNorm K S (numeratorMinimum K S d i) * exteriorNorm K S i.c *
          exteriorNorm K S (fullCubeIdeal K S d i) ^ 3 /
          (exteriorNorm K S d.moving * exteriorNorm K S (activeFrozenIdeal K S d i) *
            exteriorNorm K S (activeMarkedIdeal K S d i)) ^ 2) := by
  rw [reflectedTerm_eq_weightedFullCube K S D d i hD F θ V X,
    reflectedMarkFactor_eq_separated K S D d (minimumIndex K S d i) θ,
    reflectedRowFactor_eq_separated K S D d (minimumIndex K S d i) θ]
  rfl

end HeckeSkeleton.LowEnergy.ActualFrozenIndependence
