import HeckeSkeleton.LowFrozenCube.ExteriorLocalTable
import HeckeSkeleton.LowFrozenCube.ExteriorPhases

/-!
# The literal marked reflected coefficient is an actual frozen raw term

Squarefree prime products are reconstructed from the actual coordinates.
They separate the numerator-dependent character in each of the row, mark
and column coefficients.  The final identity retains the original Mellin
kernel and the inactive-mark scalar, and uses the original local Weyl
tables inside `rawSourceTerm`.  No reflection or kernel estimate is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowFrozenCube.Exterior

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeSkeleton.LowHybrid
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S) (hD : AllowedGeneratorInput K S D)

theorem valuation_primeSetIdeal (T : Finset (ExteriorPrime K S))
    (p : ExteriorPrime K S) :
    PrimeCoordinates.valuation (ExteriorArithmetic.coords K S) (primeSetIdeal K S T) p =
      if p ∈ T then 1 else 0 := by
  change primeExponents (squarefreeIdeal K (T.image Subtype.val)) p.val = _
  rw [primeExponents_squarefreeIdeal]
  have hm : p.val ∈ T.image Subtype.val ↔ p ∈ T := by
    constructor
    · intro hp
      obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hp
      have he' : q = p := Subtype.ext he
      simpa only [he'] using hq
    · intro hp
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  simp only [hm]

@[simp] theorem exteriorSupport_primeSetIdeal (T : Finset (ExteriorPrime K S)) :
    exteriorSupport K S (primeSetIdeal K S T) = T := by
  ext p
  rw [mem_exteriorSupport_iff]
  change PrimeCoordinates.valuation (ExteriorArithmetic.coords K S)
    (primeSetIdeal K S T) p ≠ 0 ↔ _
  rw [valuation_primeSetIdeal]
  by_cases hp : p ∈ T <;> simp [hp]

theorem primeSetIdeal_squarefree (T : Finset (ExteriorPrime K S)) :
    Squarefree (primeSetIdeal K S T).val.val := by
  apply (ExteriorArithmetic.coords_squarefree_iff K S _).mp
  intro p
  change PrimeCoordinates.valuation (ExteriorArithmetic.coords K S)
    (primeSetIdeal K S T) p ≤ 1
  rw [valuation_primeSetIdeal]
  split_ifs <;> norm_num

/-- The true squarefree ideal is its product of exterior prime ideals. -/
theorem squarefree_prime_factorization (I : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) :
    I = ∏ p ∈ exteriorSupport K S I, exteriorPrimeIdeal K S p := by
  have hsf := (ExteriorArithmetic.coords_squarefree_iff K S I).mpr hI
  calc
    I = ∏ p ∈ exteriorSupport K S I,
        PrimeCoordinates.primeElement (ExteriorArithmetic.coords K S) p ^
          PrimeCoordinates.valuation (ExteriorArithmetic.coords K S) I p :=
      PrimeCoordinates.factorization (ExteriorArithmetic.coords K S) _ I
        ((supported_iff K S _ I).mpr (Finset.Subset.refl _))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      have hne := (mem_exteriorSupport_iff K S I p).mp hp
      have hle := hsf p
      change primeExponents I.val p.val ≤ 1 at hle
      have he : PrimeCoordinates.valuation (ExteriorArithmetic.coords K S) I p = 1 := by
        change primeExponents I.val p.val = 1
        omega
      rw [he, pow_one, ExteriorArithmetic.prime_coords]

include hD in
/-- No product law for selected generators is postulated: reciprocity,
the allowed sixth-unit error, and actual factorization prove this identity. -/
theorem idealSymbol_generator_eq_prime_product (I A : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) :
    idealSymbol K S D I (D.generator A) =
      ∏ p ∈ exteriorSupport K S I, primeEvaluation K S D p (D.generator A) := by
  change ExteriorSymbol.symbolHom K S D hD I A = _
  calc
    ExteriorSymbol.symbolHom K S D hD I A = ExteriorSymbol.symbolHom K S D hD A I :=
      ExteriorSymbol.symbolHom_reciprocity K S D hD I A
    _ = ExteriorSymbol.symbolHom K S D hD A
        (∏ p ∈ exteriorSupport K S I, exteriorPrimeIdeal K S p) :=
      congrArg (ExteriorSymbol.symbolHom K S D hD A)
        (squarefree_prime_factorization K S I hI)
    _ = _ := by
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro p _
      exact ExteriorSymbol.symbol_prime_right K S D hD A p

variable (d : MarkedDatum K S) (i : ReflectionIndex K S d)

/-- The active marks avoid the moving squarefree row by the actual marked
datum condition, so the first collision mask is one. -/
theorem activeMarked_coprime_moving :
    IsCoprime (activeMarkedIdeal K S d i).val.val d.moving.val.val := by
  apply (ExteriorArithmetic.coords_coprime_iff K S _ _).mp
  intro p
  by_cases hp : p ∈ i.activeMarks
  · right
    change primeExponents d.moving.val p.val = 0
    apply Nat.eq_zero_of_not_pos
    intro hpos
    exact (d.marks_coprime p (i.marks_subset hp)).1
      ((ExteriorArithmetic.primeExponents_pos_iff K d.moving.val p.val).mp hpos)
  · left
    change PrimeCoordinates.valuation (ExteriorArithmetic.coords K S)
      (primeSetIdeal K S i.activeMarks) p = 0
    rw [valuation_primeSetIdeal, if_neg hp]

/-- The second collision mask is one by the complete original `n_coprime`
condition, which includes both the ordinary and active marked prime sets. -/
theorem activeMarked_coprime_cube :
    IsCoprime (activeMarkedIdeal K S d i).val.val i.n.val.val :=
  i.n_coprime.of_mul_right_right.symm

def reflectionRowBase (θ : HeckeCharacter K) (a : ExteriorIdeal K S) : ℂ :=
  periodValue K S D d θ a ^ 2 *
    ∏ p ∈ exteriorSupport K S a,
      localWeylScalar K S D p ⟨1, by decide⟩ 0 *
        (primeEvaluation K S D p (S.unitEquivUnitsInteger K (frequencyUnit K S d i)).val *
          primeEvaluation K S D p (D.generator (removePrime K S a p)) ^ (-2 : ℤ) *
          primeEvaluation K S D p (D.generator (activeFrozenIdeal K S d i)) ^ (-2 : ℤ))

def reflectionMarkBase (θ : HeckeCharacter K) (a : ExteriorIdeal K S) : ℂ :=
  periodValue K S D d θ a ^ 2 *
    ∏ p ∈ exteriorSupport K S a,
      thetaGamma K S D (exteriorPrimeIdeal K S p) 2 *
        (primeEvaluation K S D p (S.unitEquivUnitsInteger K (frequencyUnit K S d i)).val *
          primeEvaluation K S D p (D.generator (removePrime K S a p)) ^ (-2 : ℤ) *
          primeEvaluation K S D p (D.generator (activeFrozenIdeal K S d i)) ^ (-2 : ℤ)) ^ 2

def reflectionColumnBase (θ : HeckeCharacter K) (a : ExteriorIdeal K S) : ℂ :=
  (periodValue K S D d θ a)⁻¹ *
    ∏ p ∈ exteriorSupport K S a,
      thetaGamma K S D (exteriorPrimeIdeal K S p) 2 *
        (primeEvaluation K S D p (S.unitEquivUnitsInteger K (frequencyUnit K S d i)).val *
          primeEvaluation K S D p (D.generator (removePrime K S a p)) *
          primeEvaluation K S D p (D.generator (activeFrozenIdeal K S d i)) ^ (-2 : ℤ)) ^ 2

/-- The phase left after removing the actual ordinary Weyl table.  Its
formula keeps the original period values, unit sector and inactive primes. -/
def reflectionPhase (θ : HeckeCharacter K) (_c a n : ExteriorIdeal K S) : ℂ :=
  (∏ p ∈ frozenPrimes K S d \ i.activeFrozen,
    (1 - (p.val.asIdeal.absNorm : ℂ)⁻¹)) *
  (periodValue K S D d θ a)⁻¹ *
  (periodValue K S D d θ n) ^ (-3 : ℤ) *
  (periodValue K S D d θ (activeFrozenIdeal K S d i)) ^ 2 *
  ∏ p ∈ i.activeFrozen,
    (primeEvaluation K S D p (S.unitEquivUnitsInteger K (frequencyUnit K S d i)).val *
      primeEvaluation K S D p (D.generator (removePrime K S a p)) *
      primeEvaluation K S D p (D.generator n) ^ 3 *
      primeEvaluation K S D p
        (D.generator (removePrime K S (activeFrozenIdeal K S d i) p)) ^ (-2 : ℤ)) ^
          localWeylExponent (rowDigit K S d p) (primeExponents a.val p.val)

/-- A finite source block with every coefficient taken from the literal
reflection formulas.  Its finite cutoffs and row factors remain explicit
so the downstream annular decomposition can choose them. -/
def reflectionSourceBlock (θ : HeckeCharacter K) (pow sup : ExteriorIdeal K S)
    (rows marks columns : Finset (ExteriorIdeal K S))
    (inputs : Finset (ExteriorIdeal K S × ExteriorIdeal K S)) :
    FrozenReduction.SourceBlock (ExteriorPrime K S) (ExteriorIdeal K S) where
  first := first K S D
  prefactor := prefactor K S D
  atZero := atZero K S D
  phase := reflectionPhase K S D d i θ
  a₀ := reflectionMarkBase K S D d i θ
  ρ₀ := reflectionRowBase K S D d i θ
  lam := reflectionColumnBase K S D d i θ
  pow := pow
  sup := sup
  rows := rows
  marks := marks
  columns := columns
  inputs := inputs

@[simp] theorem withActualLocalTables_reflectionSourceBlock (θ : HeckeCharacter K)
    (pow sup : ExteriorIdeal K S) (rows marks columns : Finset (ExteriorIdeal K S))
    (inputs : Finset (ExteriorIdeal K S × ExteriorIdeal K S)) :
    withActualLocalTables K S D
        (reflectionSourceBlock K S D d i θ pow sup rows marks columns inputs) =
      reflectionSourceBlock K S D d i θ pow sup rows marks columns inputs := rfl

theorem reflectionSourceBlock_localBounds (θ : HeckeCharacter K)
    (pow sup : ExteriorIdeal K S) (rows marks columns : Finset (ExteriorIdeal K S))
    (inputs : Finset (ExteriorIdeal K S × ExteriorIdeal K S)) :
    FrozenReduction.PrimitiveLocalBounds
      ((ofReflectionIndex K S d i).toFrozen K S D hD) (ExteriorArithmetic.normHom K S)
      (reflectionSourceBlock K S D d i θ pow sup rows marks columns inputs) := by
  simpa only [withActualLocalTables_reflectionSourceBlock] using
    primitiveLocalBounds K S D hD (ofReflectionIndex K S d i)
      (reflectionSourceBlock K S D d i θ pow sup rows marks columns inputs)

private theorem prime_product_factor_one {ι : Type*} (s : Finset ι)
    (w u a r t : ι → ℂ) :
    (∏ p ∈ s, w p * (u p * a p * r p * t p)) =
      (∏ p ∈ s, w p * (u p * r p * t p)) * ∏ p ∈ s, a p := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  ring

private theorem prime_product_factor_two {ι : Type*} (s : Finset ι)
    (w u a r t : ι → ℂ) :
    (∏ p ∈ s, w p * (u p * a p * r p * t p) ^ 2) =
      (∏ p ∈ s, w p * (u p * r p * t p) ^ 2) * (∏ p ∈ s, a p) ^ 2 := by
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  ring

private theorem reflectionNegativeInteraction_eq (I : ExteriorIdeal K S) :
    negativeOrdinaryInteraction i.activeFrozen
      ((ofReflectionIndex K S d i).toFrozen K S D hD).ordinarySymbol
      (fun p => (rowDigit K S d p).val)
      (PrimeCoordinates.valuation (ExteriorArithmetic.coords K S) i.numeratorFrozen) I =
      ∏ p ∈ i.activeFrozen, primeEvaluation K S D p (D.generator I) ^
        (-(2 * localWeylExponent (rowDigit K S d p)
          (primeExponents i.numeratorFrozen.val p.val) : ℤ)) :=
  Data.negativeOrdinaryInteraction_eq K S D hD (ofReflectionIndex K S d i)
    i.numeratorFrozen I

private theorem reflectionPositiveInteraction_eq (I : ExteriorIdeal K S) :
    positiveOrdinaryInteraction i.activeFrozen
      ((ofReflectionIndex K S d i).toFrozen K S D hD).ordinarySymbol
      (fun p => (rowDigit K S d p).val)
      (PrimeCoordinates.valuation (ExteriorArithmetic.coords K S) i.numeratorFrozen) I =
      ∏ p ∈ i.activeFrozen, primeEvaluation K S D p (D.generator I) ^
        localWeylExponent (rowDigit K S d p)
          (primeExponents i.numeratorFrozen.val p.val) :=
  Data.positiveOrdinaryInteraction_eq K S D hD (ofReflectionIndex K S d i)
    i.numeratorFrozen I

theorem reflectedRowFactor_eq (θ : HeckeCharacter K) :
    reflectedRowFactor K S D d i θ =
      rowCoefficient ((ofReflectionIndex K S d i).toFrozen K S D hD).symbol
        i.activeFrozen ((ofReflectionIndex K S d i).toFrozen K S D hD).ordinarySymbol
        (fun p => (rowDigit K S d p).val)
        (PrimeCoordinates.valuation (ExteriorArithmetic.coords K S) i.numeratorFrozen)
        (reflectionRowBase K S D d i θ) i.numeratorFrozen d.moving := by
  rw [rowCoefficient, reflectionNegativeInteraction_eq K S D hD d i]
  change _ = reflectionRowBase K S D d i θ d.moving *
    idealSymbol K S D d.moving (D.generator i.numeratorFrozen) * _
  rw [idealSymbol_generator_eq_prime_product K S D hD _ _ d.moving_squarefree]
  unfold reflectedRowFactor reflectionRowBase
  rw [prime_product_factor_one]
  ring

theorem reflectedMarkFactor_eq (θ : HeckeCharacter K) :
    reflectedMarkFactor K S D d i θ =
      markCoefficient ((ofReflectionIndex K S d i).toFrozen K S D hD).symbol
        i.activeFrozen ((ofReflectionIndex K S d i).toFrozen K S D hD).ordinarySymbol
        (fun p => (rowDigit K S d p).val)
        (PrimeCoordinates.valuation (ExteriorArithmetic.coords K S) i.numeratorFrozen)
        (reflectionMarkBase K S D d i θ) i.numeratorFrozen (activeMarkedIdeal K S d i) := by
  rw [markCoefficient, reflectionNegativeInteraction_eq K S D hD d i]
  change _ = reflectionMarkBase K S D d i θ (activeMarkedIdeal K S d i) *
    idealSymbol K S D (activeMarkedIdeal K S d i) (D.generator i.numeratorFrozen) ^ 2 * _
  rw [idealSymbol_generator_eq_prime_product K S D hD
    (activeMarkedIdeal K S d i) i.numeratorFrozen
    (primeSetIdeal_squarefree K S i.activeMarks)]
  unfold reflectedMarkFactor reflectionMarkBase
  simp only [activeMarkedIdeal, exteriorSupport_primeSetIdeal]
  rw [prime_product_factor_two]
  ring

theorem reflectedColumnFactor_eq (θ : HeckeCharacter K) :
    reflectedColumnFactor K S D d i θ =
      columnCoefficient ((ofReflectionIndex K S d i).toFrozen K S D hD).symbol
        i.activeFrozen ((ofReflectionIndex K S d i).toFrozen K S D hD).ordinarySymbol
        (fun p => (rowDigit K S d p).val)
        (PrimeCoordinates.valuation (ExteriorArithmetic.coords K S) i.numeratorFrozen)
        (reflectionColumnBase K S D d i θ) i.numeratorFrozen i.c := by
  rw [columnCoefficient, reflectionPositiveInteraction_eq K S D hD d i]
  change _ = reflectionColumnBase K S D d i θ i.c *
    idealSymbol K S D i.c (D.generator i.numeratorFrozen) ^ 2 * _
  rw [idealSymbol_generator_eq_prime_product K S D hD _ _ i.c_squarefree]
  unfold reflectedColumnFactor reflectionColumnBase
  rw [prime_product_factor_two]
  ring

theorem frozenOmega_eq_rawTable (θ : HeckeCharacter K) :
    frozenOmega K S D d i θ =
      reflectionPhase K S D d i θ i.c i.numeratorFrozen i.n *
        ((ofReflectionIndex K S d i).toFrozen K S D hD).rawTable
          (ExteriorArithmetic.normHom K S) (first K S D) (prefactor K S D)
          (atZero K S D) i.numeratorFrozen := by
  rw [rawTable_eq]
  simp only [ofReflectionIndex]
  unfold frozenOmega reflectionPhase
  rw [Finset.prod_mul_distrib]
  ring

theorem reflectedColumnFactor_div_eq (θ : HeckeCharacter K) :
    reflectedColumnFactor K S D d i θ /
        (Real.sqrt (exteriorNorm K S i.c) : ℂ) =
      columnCoefficient ((ofReflectionIndex K S d i).toFrozen K S D hD).symbol
        i.activeFrozen ((ofReflectionIndex K S d i).toFrozen K S D hD).ordinarySymbol
        (fun p => (rowDigit K S d p).val)
        (PrimeCoordinates.valuation (ExteriorArithmetic.coords K S) i.numeratorFrozen)
        (FrozenReduction.annularColumn (ExteriorArithmetic.normHom K S)
          (reflectionColumnBase K S D d i θ)) i.numeratorFrozen i.c := by
  rw [reflectedColumnFactor_eq K S D hD]
  simp only [columnCoefficient, FrozenReduction.annularColumn,
    ExteriorArithmetic.normHom_apply, div_eq_mul_inv]
  ring

/-- Exact original coefficient correspondence, including both square-root
weights.  The Mellin kernel is kept literally as in `reflectedTerm`; its
analytic bound belongs to the subsequent reflected-energy assembly. -/
theorem reflectedTerm_eq_rawSourceTerm (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (V : ℝ → ℂ) (X : ℝ) :
    reflectedTerm K S D d i F θ V X =
      (∏ p ∈ d.marks \ i.activeMarks, (p.val.asIdeal.absNorm : ℂ)⁻¹) *
        ((ofReflectionIndex K S d i).toFrozen K S D hD).rawSourceTerm
          (ExteriorArithmetic.normHom K S) (first K S D) (prefactor K S D)
          (atZero K S D) (reflectionPhase K S D d i θ)
          (reflectionMarkBase K S D d i θ) (reflectionRowBase K S D d i θ)
          (FrozenReduction.annularColumn (ExteriorArithmetic.normHom K S)
            (reflectionColumnBase K S D d i θ))
          d.moving (activeMarkedIdeal K S d i) i.c i.numeratorFrozen i.n *
      mellinReflectionKernel K S F θ (QuotientGroup.mk d.rowUnit)
        (frequencyClass K S D d i) V 0
        (X * exteriorNorm K S i.numeratorFrozen * exteriorNorm K S i.c *
          exteriorNorm K S i.n ^ 3 /
          (exteriorNorm K S d.moving * exteriorNorm K S (activeFrozenIdeal K S d i) *
            exteriorNorm K S (activeMarkedIdeal K S d i)) ^ 2) := by
  have hordinary : ((ofReflectionIndex K S d i).toFrozen K S D hD).ordinary =
      i.activeFrozen := rfl
  have hdigit : ((ofReflectionIndex K S d i).toFrozen K S D hD).digit =
      (fun p => (rowDigit K S d p).val) := rfl
  rw [FrozenReduction.Data.rawSourceTerm,
    Data.mixedPhase_eq_actual_of_coprime K S D hD (ofReflectionIndex K S d i)
      d.moving (activeMarkedIdeal K S d i) i.c i.n
      (activeMarked_coprime_moving K S d i) (activeMarked_coprime_cube K S d i)]
  simp only [hordinary, hdigit, Data.toFrozen_coords]
  rw [← reflectedRowFactor_eq K S D hD d i θ,
    ← reflectedMarkFactor_eq K S D hD d i θ,
    ← reflectedColumnFactor_div_eq K S D hD d i θ,
    ← frozenOmega_eq_rawTable K S D hD d i θ]
  unfold reflectedTerm
  simp only [ExteriorArithmetic.normHom_apply, div_eq_mul_inv]
  ring

#print axioms idealSymbol_generator_eq_prime_product
#print axioms reflectedRowFactor_eq
#print axioms reflectedMarkFactor_eq
#print axioms reflectedColumnFactor_eq
#print axioms reflectedTerm_eq_rawSourceTerm

end HeckeSkeleton.LowFrozenCube.Exterior
