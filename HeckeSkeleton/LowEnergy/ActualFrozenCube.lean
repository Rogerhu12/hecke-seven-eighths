import HeckeSkeleton.LowEnergy.ActualReflection
import HeckeSkeleton.LowEnergy.ActualSymbols
import HeckeSkeleton.LowEnergy.ActualSymbolProducts
import HeckeSkeleton.LowEnergy.FrozenIdealRows
import HeckeSkeleton.LowFrozenCube.LocalCoefficients
import HeckeGeneral.Analysis.ThetaPrimeGaussNorm

/-!
# Literal local coefficients and frozen numerator of the reflected summand

Every coefficient here is the project's actual finite residue sum.  The
positive-progression scaling is exact, not an assumed local-table bound.
The minimum and cube are actual exterior ideals.  Mark and squarefree-column
factors lose their cube dependence exactly; the row keeps its cubic phase.

This is a project adapter, not a replacement definition of `reflectedTerm`.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.ActualFrozenCube

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeSkeleton.LowFrozenCube
open HeckeSkeleton.LowEnergy.IdealRows HeckeSkeleton.LowEnergy.FrozenIdealRows
open HeckeSkeleton.LowEnergy.ActualReflection HeckeSkeleton.LowEnergy.ActualSymbols
open HeckeSkeleton.LowEnergy.ActualSymbolProducts
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- The spherical digit supplies precisely one inverse norm for each cube. -/
theorem sphericalDigit_add_cube (p : ExteriorPrime K S) (e x : ℕ) :
    sphericalDigit K S D p (e + 3 * x) =
      (p.val.asIdeal.absNorm : ℂ)⁻¹ ^ x * sphericalDigit K S D p e := by
  have hm : (e + 3 * x) % 3 = e % 3 := by omega
  have hd : (e + 3 * x) / 3 = e / 3 + x := by omega
  unfold sphericalDigit
  rw [hm, hd, pow_add]
  split_ifs <;> ring

/-- The additive argument is unchanged throughout each positive progression. -/
theorem localWeylScalar_add_cube (p : ExteriorPrime K S) (j : Fin 6)
    (e x : ℕ) (he : 0 < e) :
    localWeylScalar K S D p j (e + 3 * x) =
      (p.val.asIdeal.absNorm : ℂ)⁻¹ ^ x * localWeylScalar K S D p j e := by
  have he0 : e ≠ 0 := by omega
  have hex0 : e + 3 * x ≠ 0 := by omega
  unfold localWeylScalar
  rw [sphericalDigit_add_cube]
  simp only [if_neg he0, if_neg hex0]
  ring

theorem localWeylExponent_frozen (j : Fin 6) (e : ℕ)
    (he : AdmissibleExponent e) :
    localWeylExponent j e = localWeylExponent j (frozenMin e) :=
  localPhaseDigit_frozen j.val e he

/-- Includes e=0 without incorrectly moving it to the positive progression. -/
theorem localWeylScalar_frozen (p : ExteriorPrime K S) (j : Fin 6)
    (e : ℕ) (he : AdmissibleExponent e) :
    localWeylScalar K S D p j e =
      (p.val.asIdeal.absNorm : ℂ)⁻¹ ^ frozenCubeExp e *
        localWeylScalar K S D p j (frozenMin e) := by
  by_cases he0 : e = 0
  · simp [he0]
  · have hm : 0 < frozenMin e := Nat.pos_of_ne_zero
      (fun h => he0 ((frozenMin_eq_zero_iff e).mp h))
    calc
      _ = localWeylScalar K S D p j (frozenMin e + 3 * frozenCubeExp e) := by
        rw [← frozenExponent_decomposition e he]
      _ = _ := localWeylScalar_add_cube K S D p j _ _ hm

def exteriorPower (I : ExteriorIdeal K S) (e : ℕ) : ExteriorIdeal K S :=
  ⟨I.val ^ e, fun p hp => I.property p (p.prime.dvd_of_dvd_pow hp)⟩

variable (d : MarkedDatum K S) (i : ReflectionIndex K S d)

/-- The reflection index's exterior digit condition also covers primes in S. -/
theorem numerator_admissible : Admissible i.numeratorFrozen.val := by
  intro p
  by_cases hpS : p ∉ S
  · have hd := i.frozen_digits (⟨p, hpS⟩ : ExteriorPrime K S)
    unfold AdmissibleExponent
    omega
  · have hz : primeExponents i.numeratorFrozen.val p = 0 := by
      by_contra hne
      exact hpS (i.numeratorFrozen.property p ((exponent_ne_zero_iff_dvd _ p).mp hne))
    simp [AdmissibleExponent, hz]

def numeratorMinimum : ExteriorIdeal K S :=
  ⟨minimumPart i.numeratorFrozen.val, fun p hp => i.numeratorFrozen.property p
    (dvd_trans hp (minimumPart_dvd _ (numerator_admissible K S d i)))⟩

def numeratorCube : ExteriorIdeal K S :=
  ⟨cubePart i.numeratorFrozen.val, fun p hp => i.numeratorFrozen.property p
    (dvd_trans hp (cubePart_dvd _ (numerator_admissible K S d i)))⟩

/-- The cube variable stays inside the sum and includes both original cube parts. -/
def fullCubeIdeal : ExteriorIdeal K S :=
  exteriorMul K S (numeratorCube K S d i) i.n

theorem numerator_minimum_cube :
    exteriorMul K S (numeratorMinimum K S d i)
      (exteriorPower K S (numeratorCube K S d i) 3) = i.numeratorFrozen := by
  apply Subtype.ext
  exact minimum_cube_decomposition _ (numerator_admissible K S d i)

theorem numeratorCube_support :
    exteriorSupport K S (numeratorCube K S d i) ⊆ i.activeFrozen := by
  intro p hp
  apply i.frozen_support
  rw [mem_exteriorSupport_iff] at hp ⊢
  exact dvd_trans hp (cubePart_dvd _ (numerator_admissible K S d i))

theorem numeratorMinimum_support :
    exteriorSupport K S (numeratorMinimum K S d i) =
      exteriorSupport K S i.numeratorFrozen := by
  ext p
  rw [mem_exteriorSupport_iff, mem_exteriorSupport_iff]
  exact minimumPart_support _ p.val

/-- Replace only the numerator by its canonical minimum.  All actual row,
mark, squarefree-column and frequency-unit data are kept literally. -/
def minimumIndex : ReflectionIndex K S d :=
  { i with
    numeratorFrozen := numeratorMinimum K S d i
    frozen_support := by
      rw [numeratorMinimum_support]
      exact i.frozen_support
    frozen_digits := by
      intro p
      change primeExponents (minimumPart i.numeratorFrozen.val) p.val % 3 ≠ 2
      rw [exponent_minimumPart]
      rcases frozenMin_cases (primeExponents i.numeratorFrozen.val p.val) with h | h | h <;>
        simp [h] }

theorem frozenExponent_minimum (p : ExteriorPrime K S) :
    localWeylExponent (rowDigit K S d p) (primeExponents i.numeratorFrozen.val p.val) =
      localWeylExponent (rowDigit K S d p)
        (primeExponents (minimumIndex K S d i).numeratorFrozen.val p.val) := by
  change localWeylExponent (rowDigit K S d p) (primeExponents i.numeratorFrozen.val p.val) =
    localWeylExponent (rowDigit K S d p) (primeExponents (minimumPart i.numeratorFrozen.val) p.val)
  rw [exponent_minimumPart]
  exact localWeylExponent_frozen _ _ (numerator_admissible K S d i p.val)

/-- The local prime evaluation respects actual allowed generators. -/
theorem primeEvaluation_generator_mul (hD : AllowedGeneratorInput K S D)
    (p : ExteriorPrime K S) (A B : ExteriorIdeal K S) :
    primeEvaluation K S D p (D.generator (exteriorMul K S A B)) =
      primeEvaluation K S D p (D.generator A) * primeEvaluation K S D p (D.generator B) := by
  obtain ⟨u, hu⟩ := hD.multiplicative A B
  rw [hu, mul_assoc]
  change sIntegerSexticEvaluation K S p.val p.property D.root6 D.primitive6 D.embedding
    (D.away_six p.val p.property)
      ((S.unitEquivUnitsInteger K u).val ^ 6 * (D.generator A * D.generator B)) = _
  rw [sIntegerSexticEvaluation_mul_sixth_power_unit, sIntegerSexticEvaluation_mul]

theorem primeEvaluation_generator_cube (hD : AllowedGeneratorInput K S D)
    (p : ExteriorPrime K S) (A : ExteriorIdeal K S) :
    primeEvaluation K S D p (D.generator (exteriorPower K S A 3)) =
      primeEvaluation K S D p (D.generator A) ^ 3 := by
  have he : exteriorPower K S A 3 = exteriorMul K S A (exteriorMul K S A A) := by
    apply Subtype.ext
    change A.val ^ 3 = A.val * (A.val * A.val)
    simp only [pow_succ, pow_zero, mul_one, mul_assoc]
  rw [he, primeEvaluation_generator_mul K S D hD,
    primeEvaluation_generator_mul K S D hD]
  ring

theorem primeEvaluation_generator_numerator (hD : AllowedGeneratorInput K S D)
    (p : ExteriorPrime K S) :
    primeEvaluation K S D p (D.generator i.numeratorFrozen) =
      primeEvaluation K S D p (D.generator (numeratorMinimum K S d i)) *
        primeEvaluation K S D p (D.generator (numeratorCube K S d i)) ^ 3 := by
  rw [← numerator_minimum_cube K S d i, primeEvaluation_generator_mul K S D hD,
    primeEvaluation_generator_cube K S D hD]

/-- A prime not dividing an actual ideal sees its generator as a residue unit. -/
theorem primeEvaluation_generator_sixth (p : ExteriorPrime K S) (A : ExteriorIdeal K S)
    (hp : ¬p.val.asIdeal ∣ A.val.val) :
    primeEvaluation K S D p (D.generator A) ^ 6 = 1 := by
  have hr : sIntegerSexticResidueMap K S p.val p.property (D.generator A) ≠ 0 := by
    intro hz
    have hd := (sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction K S p.val
      p.property (D.generator A)).mp hz
    rw [contraction_thetaGenerator K S D A] at hd
    exact hp hd
  unfold primeEvaluation sIntegerSexticEvaluation sexticResidueCharacter
  simpa only [map_pow] using
    HeckeGeneral.Arithmetic.FiniteFieldSexticCharacter.character_sixth_power_of_ne_zero
      _ _ _ _ _ _ _ hr

theorem marks_disjoint_activeFrozen (p : ExteriorPrime K S) (hp : p ∈ i.activeMarks) :
    p ∉ i.activeFrozen := by
  intro hf
  have hmark := d.marks_coprime p (i.marks_subset hp)
  have hf' := i.frozen_subset hf
  rcases Finset.mem_union.mp hf' with hfr | hpu
  · exact hmark.2.1 ((mem_exteriorSupport_iff K S d.frozen p).mp hfr)
  · exact hmark.2.2 ((mem_exteriorSupport_iff K S d.puncture p).mp hpu)

theorem mark_not_dvd_numeratorCube (p : ExteriorPrime K S) (hp : p ∈ i.activeMarks) :
    ¬p.val.asIdeal ∣ (numeratorCube K S d i).val.val := by
  intro h
  exact marks_disjoint_activeFrozen K S d i p hp
    (numeratorCube_support K S d i ((mem_exteriorSupport_iff K S _ p).mpr h))

theorem column_prime_not_dvd_numeratorCube (p : ExteriorPrime K S)
    (hp : p ∈ exteriorSupport K S i.c) :
    ¬p.val.asIdeal ∣ (numeratorCube K S d i).val.val := by
  intro hx
  have hpf : p ∈ i.activeFrozen := numeratorCube_support K S d i
    ((mem_exteriorSupport_iff K S _ p).mpr hx)
  exact p.val.prime.not_unit
    (i.c_coprime.isUnit_of_dvd'
      ((mem_exteriorSupport_iff K S i.c p).mp hp)
      ((prime_dvd_primeSetIdeal_iff K S i.activeFrozen p).mpr hpf))

private theorem square_factor_cube_cancel (u a b c z : ℂ) (hz : z ^ 6 = 1) :
    (u * (a * z ^ 3) * b * c) ^ 2 = (u * a * b * c) ^ 2 := by
  calc
    _ = (u * a * b * c) ^ 2 * z ^ 6 := by ring
    _ = _ := by rw [hz, mul_one]

/-- The literal active-mark coefficient is independent of the remaining cube. -/
theorem reflectedMarkFactor_minimum (hD : AllowedGeneratorInput K S D)
    (θ : HeckeCharacter K) :
    reflectedMarkFactor K S D d i θ =
      reflectedMarkFactor K S D d (minimumIndex K S d i) θ := by
  unfold reflectedMarkFactor
  have hnegative :
      (∏ p ∈ i.activeFrozen, primeEvaluation K S D p
        (D.generator (activeMarkedIdeal K S d i)) ^
          (-(2 * localWeylExponent (rowDigit K S d p)
            (primeExponents i.numeratorFrozen.val p.val) : ℤ))) =
      ∏ p ∈ i.activeFrozen, primeEvaluation K S D p
        (D.generator (activeMarkedIdeal K S d i)) ^
          (-(2 * localWeylExponent (rowDigit K S d p)
            (primeExponents (numeratorMinimum K S d i).val p.val) : ℤ)) := by
    apply Finset.prod_congr rfl
    intro p _
    rw [frozenExponent_minimum K S d i p]
    rfl
  have hmarks :
      (∏ p ∈ i.activeMarks,
        thetaGamma K S D (exteriorPrimeIdeal K S p) 2 *
        (primeEvaluation K S D p (S.unitEquivUnitsInteger K (frequencyUnit K S d i)).val *
         primeEvaluation K S D p (D.generator i.numeratorFrozen) *
         primeEvaluation K S D p (D.generator (removePrime K S (activeMarkedIdeal K S d i) p)) ^
           (-2 : ℤ) *
         primeEvaluation K S D p (D.generator (activeFrozenIdeal K S d i)) ^ (-2 : ℤ)) ^ 2) =
      ∏ p ∈ i.activeMarks,
        thetaGamma K S D (exteriorPrimeIdeal K S p) 2 *
        (primeEvaluation K S D p (S.unitEquivUnitsInteger K (frequencyUnit K S d i)).val *
         primeEvaluation K S D p (D.generator (numeratorMinimum K S d i)) *
         primeEvaluation K S D p (D.generator (removePrime K S (activeMarkedIdeal K S d i) p)) ^
           (-2 : ℤ) *
         primeEvaluation K S D p (D.generator (activeFrozenIdeal K S d i)) ^ (-2 : ℤ)) ^ 2 := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [primeEvaluation_generator_numerator K S D d i hD p]
    congr 1
    have hz := primeEvaluation_generator_sixth K S D p (numeratorCube K S d i)
      (mark_not_dvd_numeratorCube K S d i p hp)
    exact square_factor_cube_cancel _ _ _ _ _ hz
  rw [hnegative, hmarks]
  rfl

/-- The literal squarefree-column coefficient also has no residual-cube dependence. -/
theorem reflectedColumnFactor_minimum (hD : AllowedGeneratorInput K S D)
    (θ : HeckeCharacter K) :
    reflectedColumnFactor K S D d i θ =
      reflectedColumnFactor K S D d (minimumIndex K S d i) θ := by
  unfold reflectedColumnFactor
  have hpositive :
      (∏ p ∈ i.activeFrozen, primeEvaluation K S D p (D.generator i.c) ^
        localWeylExponent (rowDigit K S d p) (primeExponents i.numeratorFrozen.val p.val)) =
      ∏ p ∈ i.activeFrozen, primeEvaluation K S D p (D.generator i.c) ^
        localWeylExponent (rowDigit K S d p)
          (primeExponents (numeratorMinimum K S d i).val p.val) := by
    apply Finset.prod_congr rfl
    intro p _
    rw [frozenExponent_minimum K S d i p]
    rfl
  have hcolumns :
      (∏ p ∈ exteriorSupport K S i.c,
        thetaGamma K S D (exteriorPrimeIdeal K S p) 2 *
        (primeEvaluation K S D p (S.unitEquivUnitsInteger K (frequencyUnit K S d i)).val *
         primeEvaluation K S D p (D.generator i.numeratorFrozen) *
         primeEvaluation K S D p (D.generator (removePrime K S i.c p)) *
         primeEvaluation K S D p (D.generator (activeFrozenIdeal K S d i)) ^ (-2 : ℤ)) ^ 2) =
      ∏ p ∈ exteriorSupport K S i.c,
        thetaGamma K S D (exteriorPrimeIdeal K S p) 2 *
        (primeEvaluation K S D p (S.unitEquivUnitsInteger K (frequencyUnit K S d i)).val *
         primeEvaluation K S D p (D.generator (numeratorMinimum K S d i)) *
         primeEvaluation K S D p (D.generator (removePrime K S i.c p)) *
         primeEvaluation K S D p (D.generator (activeFrozenIdeal K S d i)) ^ (-2 : ℤ)) ^ 2 := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [primeEvaluation_generator_numerator K S D d i hD p]
    congr 1
    have hz := primeEvaluation_generator_sixth K S D p (numeratorCube K S d i)
      (column_prime_not_dvd_numeratorCube K S d i p hp)
    exact square_factor_cube_cancel _ _ _ _ _ hz
  rw [hpositive, hcolumns]
  rfl

/-- The row's cube phase is retained inside the row sum, prime by prime. -/
theorem reflectedRowFactor_minimum_prime_product (hD : AllowedGeneratorInput K S D)
    (θ : HeckeCharacter K) :
    reflectedRowFactor K S D d i θ =
      reflectedRowFactor K S D d (minimumIndex K S d i) θ *
        ∏ p ∈ exteriorSupport K S d.moving,
          primeEvaluation K S D p (D.generator (numeratorCube K S d i)) ^ 3 := by
  unfold reflectedRowFactor
  have hnegative :
      (∏ p ∈ i.activeFrozen, primeEvaluation K S D p (D.generator d.moving) ^
        (-(2 * localWeylExponent (rowDigit K S d p)
          (primeExponents i.numeratorFrozen.val p.val) : ℤ))) =
      ∏ p ∈ i.activeFrozen, primeEvaluation K S D p (D.generator d.moving) ^
        (-(2 * localWeylExponent (rowDigit K S d p)
          (primeExponents (numeratorMinimum K S d i).val p.val) : ℤ)) := by
    apply Finset.prod_congr rfl
    intro p _
    rw [frozenExponent_minimum K S d i p]
    rfl
  rw [hnegative]
  simp_rw [primeEvaluation_generator_numerator K S D d i hD]
  have hprod :
      (∏ p ∈ exteriorSupport K S d.moving,
        localWeylScalar K S D p ⟨1, by decide⟩ 0 *
        (primeEvaluation K S D p (S.unitEquivUnitsInteger K (frequencyUnit K S d i)).val *
         (primeEvaluation K S D p (D.generator (numeratorMinimum K S d i)) *
          primeEvaluation K S D p (D.generator (numeratorCube K S d i)) ^ 3) *
         primeEvaluation K S D p (D.generator (removePrime K S d.moving p)) ^ (-2 : ℤ) *
         primeEvaluation K S D p (D.generator (activeFrozenIdeal K S d i)) ^ (-2 : ℤ))) =
      (∏ p ∈ exteriorSupport K S d.moving,
        localWeylScalar K S D p ⟨1, by decide⟩ 0 *
        (primeEvaluation K S D p (S.unitEquivUnitsInteger K (frequencyUnit K S d i)).val *
         primeEvaluation K S D p (D.generator (numeratorMinimum K S d i)) *
         primeEvaluation K S D p (D.generator (removePrime K S d.moving p)) ^ (-2 : ℤ) *
         primeEvaluation K S D p (D.generator (activeFrozenIdeal K S d i)) ^ (-2 : ℤ))) *
      ∏ p ∈ exteriorSupport K S d.moving,
        primeEvaluation K S D p (D.generator (numeratorCube K S d i)) ^ 3 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    ring
  rw [hprod]
  change _ = (_ * _ * _) * _
  ring

/-- The retained prime product is exactly the actual cubic row symbol. -/
theorem reflectedRowFactor_minimum (hD : AllowedGeneratorInput K S D)
    (θ : HeckeCharacter K) :
    reflectedRowFactor K S D d i θ =
      reflectedRowFactor K S D d (minimumIndex K S d i) θ *
        idealSymbol K S D d.moving (D.generator (numeratorCube K S d i)) ^ 3 := by
  rw [reflectedRowFactor_minimum_prime_product K S D d i hD θ,
    idealSymbol_generator_eq_prime_product K S D hD _ _ d.moving_squarefree,
    Finset.prod_pow]

theorem exteriorNorm_mul (A B : ExteriorIdeal K S) :
    exteriorNorm K S (exteriorMul K S A B) = exteriorNorm K S A * exteriorNorm K S B := by
  simp only [exteriorNorm, exteriorMul, Submonoid.coe_mul, map_mul, Nat.cast_mul]

theorem exteriorNorm_pos (A : ExteriorIdeal K S) : 0 < exteriorNorm K S A := by
  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors A.val

theorem numeratorNorm_minimum_cube :
    exteriorNorm K S i.numeratorFrozen =
      exteriorNorm K S (numeratorMinimum K S d i) *
        exteriorNorm K S (numeratorCube K S d i) ^ 3 :=
  norm_minimum_cube_decomposition _ (numerator_admissible K S d i)

theorem fullCubeNorm :
    exteriorNorm K S (fullCubeIdeal K S d i) =
      exteriorNorm K S (numeratorCube K S d i) * exteriorNorm K S i.n :=
  exteriorNorm_mul K S _ _

/-- Recombining the cube changes no kernel scale. -/
theorem kernel_argument_fullCube (X : ℝ) :
    X * exteriorNorm K S i.numeratorFrozen * exteriorNorm K S i.c *
        exteriorNorm K S i.n ^ 3 /
      (exteriorNorm K S d.moving * exteriorNorm K S (activeFrozenIdeal K S d i) *
        exteriorNorm K S (activeMarkedIdeal K S d i)) ^ 2 =
    X * exteriorNorm K S (numeratorMinimum K S d i) * exteriorNorm K S i.c *
        exteriorNorm K S (fullCubeIdeal K S d i) ^ 3 /
      (exteriorNorm K S d.moving * exteriorNorm K S (activeFrozenIdeal K S d i) *
        exteriorNorm K S (activeMarkedIdeal K S d i)) ^ 2 := by
  rw [numeratorNorm_minimum_cube, fullCubeNorm]
  ring

/-- The row phase gained from x combines with the old completed quadratic
symbol, including all common-prime zeros. -/
theorem quadratic_phase_fullCube (hD : AllowedGeneratorInput K S D) :
    idealSymbol K S D d.moving (D.generator (numeratorCube K S d i)) ^ 3 *
      idealSymbol K S D d.moving (D.generator i.c * D.generator i.n) ^ 3 =
    idealSymbol K S D d.moving
      (D.generator i.c * D.generator (fullCubeIdeal K S d i)) ^ 3 := by
  have hm (a b : S.integer K) : idealSymbol K S D d.moving (a * b) =
      idealSymbol K S D d.moving a * idealSymbol K S D d.moving b :=
    (elementSymbolHom K S D d.moving).map_mul a b
  rw [hm, hm]
  change _ = (idealSymbol K S D d.moving (D.generator i.c) *
    idealSymbol K S D d.moving
      (D.generator (exteriorMul K S (numeratorCube K S d i) i.n))) ^ 3
  rw [actualSymbol_mul_right K S D hD]
  ring

/-- Extract exactly the inverse norm supplied by the frozen local progression. -/
def normalizedFrozenOmega (θ : HeckeCharacter K) : ℂ :=
  (exteriorNorm K S (numeratorCube K S d i) : ℂ) * frozenOmega K S D d i θ

theorem normalizedFrozenOmega_reassemble (θ : HeckeCharacter K) :
    frozenOmega K S D d i θ / (exteriorNorm K S i.n : ℂ) =
      normalizedFrozenOmega K S D d i θ / (exteriorNorm K S (fullCubeIdeal K S d i) : ℂ) := by
  have hx : (exteriorNorm K S (numeratorCube K S d i) : ℂ) ≠ 0 := by
    exact_mod_cast (exteriorNorm_pos K S (numeratorCube K S d i)).ne'
  rw [normalizedFrozenOmega, fullCubeNorm, Complex.ofReal_mul]
  field_simp [hx]

/-- Literal reflectedTerm after the frozen cube is absorbed into the complete
cube variable.  This is an equality, with no row-energy premise and no loss.
Its remaining class argument is the original `frequencyClass`; a separate
finite-class identity can rewrite it without changing this arithmetic row. -/
theorem reflectedTerm_eq_fullCube (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : ℝ → ℂ) (X : ℝ) :
    reflectedTerm K S D d i F θ V X =
      (∏ p ∈ d.marks \ i.activeMarks, (p.val.asIdeal.absNorm : ℂ)⁻¹) *
      (Real.sqrt (exteriorNorm K S (activeMarkedIdeal K S d i)) : ℂ)⁻¹ *
      (normalizedFrozenOmega K S D d i θ /
        (exteriorNorm K S (fullCubeIdeal K S d i) : ℂ)) *
      reflectedMarkFactor K S D d (minimumIndex K S d i) θ *
      reflectedRowFactor K S D d (minimumIndex K S d i) θ *
      reflectedColumnFactor K S D d (minimumIndex K S d i) θ /
        (Real.sqrt (exteriorNorm K S i.c) : ℂ) *
      idealSymbol K S D d.moving
        (D.generator i.c * D.generator (fullCubeIdeal K S d i)) ^ 3 *
      idealSymbol K S D (activeMarkedIdeal K S d i) (D.generator i.c) ^ (-2 : ℤ) *
      mellinReflectionKernel K S F θ (QuotientGroup.mk d.rowUnit)
        (frequencyClass K S D d i) V 0
        (X * exteriorNorm K S (numeratorMinimum K S d i) * exteriorNorm K S i.c *
          exteriorNorm K S (fullCubeIdeal K S d i) ^ 3 /
          (exteriorNorm K S d.moving * exteriorNorm K S (activeFrozenIdeal K S d i) *
            exteriorNorm K S (activeMarkedIdeal K S d i)) ^ 2) := by
  unfold reflectedTerm
  rw [reflectedMarkFactor_minimum K S D d i hD θ,
    reflectedRowFactor_minimum K S D d i hD θ,
    reflectedColumnFactor_minimum K S D d i hD θ,
    kernel_argument_fullCube K S d i X,
    ← quadratic_phase_fullCube K S D d i hD,
    ← normalizedFrozenOmega_reassemble K S D d i θ]
  ring

/-- The literal constraints prove the full cube has a unique supported split. -/
theorem fullCubeSplit_actual :
    fullCubeSplit (i.activeFrozen.image Subtype.val) (fullCubeIdeal K S d i).val =
      ((numeratorCube K S d i).val, i.n.val) := by
  apply fullCubeSplit_mul
  · intro p hp
    by_contra hne
    have hdiv := (exponent_ne_zero_iff_dvd (numeratorCube K S d i).val p).mp hne
    let ep : ExteriorPrime K S := ⟨p, (numeratorCube K S d i).property p hdiv⟩
    have he : ep ∈ i.activeFrozen := numeratorCube_support K S d i
      ((mem_exteriorSupport_iff K S _ ep).mpr hdiv)
    exact hp (Finset.mem_image.mpr ⟨ep, he, rfl⟩)
  · intro p hp
    obtain ⟨ep, hep, rfl⟩ := Finset.mem_image.mp hp
    by_contra hne
    have hn := (exponent_ne_zero_iff_dvd i.n.val ep.val).mp hne
    have hf := (prime_dvd_primeSetIdeal_iff K S i.activeFrozen ep).mpr hep
    have hprod : ep.val.asIdeal ∣
        (exteriorMul K S (primeSetIdeal K S i.activeFrozen)
          (primeSetIdeal K S i.activeMarks)).val.val := dvd_mul_of_dvd_left hf _
    exact ep.val.prime.not_unit (i.n_coprime.isUnit_of_dvd' hn hprod)

end HeckeSkeleton.LowEnergy.ActualFrozenCube
