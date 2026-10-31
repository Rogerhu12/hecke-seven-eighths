import ThetaGlobal.ReflectedLocalBounds

/-!
# The literal marked reflected scalar coefficient, independent of project vendors

This model retains every multiplication, inverse, zero extension, prime product,
valuation dependence, and normalization of the project's reflectedTerm.
Only the underlying ideal, residue and unit types are abstracted. Its hypotheses
are individual local facts: norm >= 1, zero-or-unit characters, and normalized
prime Gauss norm 1. The Weyl bound is proved from its finite sum, not supplied.

The actual project instantiation is given in ReflectedCoefficientProject.lean.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.ReflectedCoefficientModel

open ThetaGlobal.ReflectedAbsolute ThetaGlobal.ReflectedLocalBounds
open scoped Classical BigOperators

/-- Scalar data obtained from actual generators, residue characters and prime
Gauss sums. No reflected coefficient bound or summability is a field. -/
structure ScalarData (P I A U : Type) where
  normI : I → ℝ
  normI_ge_one : ∀ a, 1 ≤ normI a
  primeNorm : P → ℝ
  primeNorm_ge_one : ∀ p, 1 ≤ primeNorm p
  generator : I → A
  frequencyUnit : U → A
  removePrime : I → P → I
  exponent : I → P → ℕ
  support : I → Finset P
  primeSetIdeal : Finset P → I
  primeCharacter : P → A → ℂ
  primeCharacter_zeroOrUnit : ∀ p a, ZeroOrUnitNorm (primeCharacter p a)
  idealCharacter : I → A → ℂ
  idealCharacter_zeroOrUnit : ∀ a x, ZeroOrUnitNorm (idealCharacter a x)
  period : I → ℂ
  period_zeroOrUnit : ∀ a, ZeroOrUnitNorm (period a)
  gamma : P → ℂ
  gamma_norm : ∀ p, ‖gamma p‖ = 1
  residueUnits : P → Type
  residueFintype : ∀ p, Fintype (residueUnits p)
  residueCharacter : (p : P) → residueUnits p → ℂ
  residueCharacter_zeroOrUnit : ∀ p x, ZeroOrUnitNorm (residueCharacter p x)
  digit : (p : P) → Fin 6 → residueUnits p → ℂ
  inversePhase : (p : P) → residueUnits p → ℂ

variable {P I A U : Type} [CommMonoid A] (D : ScalarData P I A U)

/-- This is the literal nonzero-digit finite sum at the local unit 1. -/
def localWeyl (p : P) (j : Fin 6) (e : ℕ) : ℂ := by
  letI := D.residueFintype p
  exact finiteWeylCoefficient (D.primeNorm p) (D.gamma p)
    (D.digit p j) (D.residueCharacter p) (D.inversePhase p) e

def localWeylBound (p : P) (j : Fin 6) : ℝ := by
  letI := D.residueFintype p
  exact finiteWeylBound (D.digit p j) (D.inversePhase p)

theorem localWeylBound_nonneg (p : P) (j : Fin 6) :
    0 ≤ localWeylBound D p j := by
  letI := D.residueFintype p
  exact finiteWeylBound_nonneg _ _

theorem norm_localWeyl_le (p : P) (j : Fin 6) (e : ℕ) :
    ‖localWeyl D p j e‖ ≤ localWeylBound D p j := by
  letI := D.residueFintype p
  exact norm_finiteWeylCoefficient_le (D.primeNorm_ge_one p) (D.gamma_norm p)
    (D.digit p j) (D.residueCharacter p) (D.inversePhase p)
    (D.residueCharacter_zeroOrUnit p) e

/-- Exactly the project's exponent; in particular e=0 is a distinct case. -/
def localExponent (j : Fin 6) (e : ℕ) : ℕ :=
  if e = 0 then (8 - j.val) % 6 else (4 + 2 * e) % 6

structure Frame (P I : Type) where
  moving : I
  frozenPrimes : Finset P
  marks : Finset P
  rowDigit : P → Fin 6

/-- This unrestricted ambient index contains the actual index injectively.
Deleting restrictions is legitimate for a positive convergence majorant. -/
structure Index (P I U : Type) where
  activeMarks : Finset P
  activeFrozen : Finset P
  numeratorFrozen : I
  n : I
  c : I
  unitSector : U

variable (d : Frame P I) (i : Index P I U)

def activeFrozenIdeal : I := D.primeSetIdeal i.activeFrozen
def activeMarkedIdeal : I := D.primeSetIdeal i.activeMarks

def frozenOmega : ℂ :=
  (Finset.prod (d.frozenPrimes \ i.activeFrozen)
    (fun p => 1 - (D.primeNorm p : ℂ)⁻¹)) *
  (D.period i.numeratorFrozen)⁻¹ * D.period i.n ^ (-3 : ℤ) *
  D.period (activeFrozenIdeal D i) ^ 2 *
  ∏ p ∈ i.activeFrozen,
    let e := D.exponent i.numeratorFrozen p
    localWeyl D p (d.rowDigit p) e *
      (D.primeCharacter p (D.frequencyUnit i.unitSector) *
       D.primeCharacter p (D.generator (D.removePrime i.numeratorFrozen p)) *
       D.primeCharacter p (D.generator i.n) ^ 3 *
       D.primeCharacter p (D.generator (D.removePrime (activeFrozenIdeal D i) p)) ^
         (-2 : ℤ)) ^ localExponent (d.rowDigit p) e

def reflectedRowFactor : ℂ :=
  D.period d.moving ^ 2 *
  (∏ p ∈ D.support d.moving,
    localWeyl D p ⟨1, by decide⟩ 0 *
    (D.primeCharacter p (D.frequencyUnit i.unitSector) *
     D.primeCharacter p (D.generator i.numeratorFrozen) *
     D.primeCharacter p (D.generator (D.removePrime d.moving p)) ^ (-2 : ℤ) *
     D.primeCharacter p (D.generator (activeFrozenIdeal D i)) ^ (-2 : ℤ))) *
  ∏ p ∈ i.activeFrozen, D.primeCharacter p (D.generator d.moving) ^
    (-(2 * localExponent (d.rowDigit p) (D.exponent i.numeratorFrozen p) : ℤ))

def reflectedMarkFactor : ℂ :=
  D.period (activeMarkedIdeal D i) ^ 2 *
  (∏ p ∈ i.activeMarks,
    D.gamma p *
    (D.primeCharacter p (D.frequencyUnit i.unitSector) *
     D.primeCharacter p (D.generator i.numeratorFrozen) *
     D.primeCharacter p (D.generator (D.removePrime (activeMarkedIdeal D i) p)) ^ (-2 : ℤ) *
     D.primeCharacter p (D.generator (activeFrozenIdeal D i)) ^ (-2 : ℤ)) ^ 2) *
  ∏ p ∈ i.activeFrozen,
    D.primeCharacter p (D.generator (activeMarkedIdeal D i)) ^
      (-(2 * localExponent (d.rowDigit p) (D.exponent i.numeratorFrozen p) : ℤ))

def reflectedColumnFactor : ℂ :=
  (D.period i.c)⁻¹ *
  (∏ p ∈ i.activeFrozen, D.primeCharacter p (D.generator i.c) ^
    localExponent (d.rowDigit p) (D.exponent i.numeratorFrozen p)) *
  ∏ p ∈ D.support i.c,
    D.gamma p *
    (D.primeCharacter p (D.frequencyUnit i.unitSector) *
     D.primeCharacter p (D.generator i.numeratorFrozen) *
     D.primeCharacter p (D.generator (D.removePrime i.c p)) *
     D.primeCharacter p (D.generator (activeFrozenIdeal D i)) ^ (-2 : ℤ)) ^ 2

/-- Exactly the scalar prefactor preceding the Mellin kernel in reflectedTerm. -/
def reflectedCoefficient : ℂ :=
  (∏ p ∈ d.marks \ i.activeMarks, (D.primeNorm p : ℂ)⁻¹) *
  (Real.sqrt (D.normI (activeMarkedIdeal D i)) : ℂ)⁻¹ *
  frozenOmega D d i / (D.normI i.n : ℂ) *
  reflectedMarkFactor D d i * reflectedRowFactor D d i *
  reflectedColumnFactor D d i / (Real.sqrt (D.normI i.c) : ℂ) *
  D.idealCharacter d.moving (D.generator i.c * D.generator i.n) ^ 3 *
  D.idealCharacter (activeMarkedIdeal D i) (D.generator i.c) ^ (-2 : ℤ)

def frozenBound (f : Finset P) : ℝ :=
  ∏ p ∈ f, localWeylBound D p (d.rowDigit p)

def rowBound : ℝ :=
  ∏ p ∈ D.support d.moving, localWeylBound D p ⟨1, by decide⟩

theorem frozenBound_nonneg (f : Finset P) : 0 ≤ frozenBound D d f :=
  Finset.prod_nonneg (fun p _ => localWeylBound_nonneg D p _)

theorem rowBound_nonneg : 0 ≤ rowBound D d :=
  Finset.prod_nonneg (fun p _ => localWeylBound_nonneg D p _)

private theorem norm_mul_bound {z w : ℂ} {a b : ℝ}
    (hz : ‖z‖ ≤ a) (hw : ‖w‖ ≤ b) : ‖z * w‖ ≤ a * b := by
  rw [norm_mul]
  exact mul_le_mul hz hw (norm_nonneg _) ((norm_nonneg _).trans hz)

private theorem norm_prod_bound {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (b : ι → ℝ) (h : ∀ j ∈ s, ‖f j‖ ≤ b j) :
    ‖∏ j ∈ s, f j‖ ≤ ∏ j ∈ s, b j := by
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) h

private theorem norm_prod_le_one {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ j ∈ s, ‖f j‖ ≤ 1) : ‖∏ j ∈ s, f j‖ ≤ 1 := by
  simpa using norm_prod_bound s f (fun _ => 1) h

theorem frozenUnitFactor_zeroOrUnit (p : P) :
    ZeroOrUnitNorm
      ((D.primeCharacter p (D.frequencyUnit i.unitSector) *
        D.primeCharacter p (D.generator (D.removePrime i.numeratorFrozen p)) *
        D.primeCharacter p (D.generator i.n) ^ 3 *
        D.primeCharacter p (D.generator (D.removePrime (activeFrozenIdeal D i) p)) ^
          (-2 : ℤ)) ^ localExponent (d.rowDigit p) (D.exponent i.numeratorFrozen p)) :=
  ((((D.primeCharacter_zeroOrUnit p _).mul (D.primeCharacter_zeroOrUnit p _)).mul
    ((D.primeCharacter_zeroOrUnit p _).pow 3)).mul
    ((D.primeCharacter_zeroOrUnit p _).zpow (-2))).pow _

theorem norm_frozenOmega_le :
    ‖frozenOmega D d i‖ ≤ frozenBound D d i.activeFrozen := by
  have hI := norm_prod_le_one (d.frozenPrimes \ i.activeFrozen)
    (fun p => (1 : ℂ) - (D.primeNorm p : ℂ)⁻¹)
    (fun p _ => norm_one_sub_real_inverse_le_one (D.primeNorm_ge_one p))
  have hunit := norm_mul_bound (norm_mul_bound (norm_mul_bound hI
    (D.period_zeroOrUnit i.numeratorFrozen).inv.norm_le)
    ((D.period_zeroOrUnit i.n).zpow (-3)).norm_le)
    ((D.period_zeroOrUnit (activeFrozenIdeal D i)).pow 2).norm_le
  have hprod : ‖∏ p ∈ i.activeFrozen,
      let e := D.exponent i.numeratorFrozen p
      localWeyl D p (d.rowDigit p) e *
        (D.primeCharacter p (D.frequencyUnit i.unitSector) *
         D.primeCharacter p (D.generator (D.removePrime i.numeratorFrozen p)) *
         D.primeCharacter p (D.generator i.n) ^ 3 *
         D.primeCharacter p (D.generator (D.removePrime (activeFrozenIdeal D i) p)) ^
           (-2 : ℤ)) ^ localExponent (d.rowDigit p) e‖ ≤
      frozenBound D d i.activeFrozen := by
    apply norm_prod_bound
    intro p _
    dsimp only
    simpa only [mul_one] using norm_mul_bound (norm_localWeyl_le D p (d.rowDigit p) _)
      (frozenUnitFactor_zeroOrUnit D d i p).norm_le
  simpa only [frozenOmega, one_mul, mul_one] using norm_mul_bound hunit hprod

theorem rowUnitFactor_zeroOrUnit (p : P) :
    ZeroOrUnitNorm
      (D.primeCharacter p (D.frequencyUnit i.unitSector) *
       D.primeCharacter p (D.generator i.numeratorFrozen) *
       D.primeCharacter p (D.generator (D.removePrime d.moving p)) ^ (-2 : ℤ) *
       D.primeCharacter p (D.generator (activeFrozenIdeal D i)) ^ (-2 : ℤ)) :=
  (((D.primeCharacter_zeroOrUnit p _).mul (D.primeCharacter_zeroOrUnit p _)).mul
    ((D.primeCharacter_zeroOrUnit p _).zpow (-2))).mul
    ((D.primeCharacter_zeroOrUnit p _).zpow (-2))

theorem norm_reflectedRowFactor_le :
    ‖reflectedRowFactor D d i‖ ≤ rowBound D d := by
  have hfirst := ((D.period_zeroOrUnit d.moving).pow 2).norm_le
  have hprod : ‖∏ p ∈ D.support d.moving,
      localWeyl D p ⟨1, by decide⟩ 0 *
      (D.primeCharacter p (D.frequencyUnit i.unitSector) *
       D.primeCharacter p (D.generator i.numeratorFrozen) *
       D.primeCharacter p (D.generator (D.removePrime d.moving p)) ^ (-2 : ℤ) *
       D.primeCharacter p (D.generator (activeFrozenIdeal D i)) ^ (-2 : ℤ))‖ ≤
      rowBound D d := by
    apply norm_prod_bound
    intro p _
    simpa only [mul_one] using norm_mul_bound (norm_localWeyl_le D p ⟨1, by decide⟩ 0)
      (rowUnitFactor_zeroOrUnit D d i p).norm_le
  have hlast : ‖∏ p ∈ i.activeFrozen,
      D.primeCharacter p (D.generator d.moving) ^
        (-(2 * localExponent (d.rowDigit p) (D.exponent i.numeratorFrozen p) : ℤ))‖ ≤ 1 := by
    apply norm_prod_le_one
    intro p _
    exact ((D.primeCharacter_zeroOrUnit p _).zpow _).norm_le
  simpa only [reflectedRowFactor, one_mul, mul_one] using
    norm_mul_bound (norm_mul_bound hfirst hprod) hlast

theorem reflectedMarkFactor_zeroOrUnit :
    ZeroOrUnitNorm (reflectedMarkFactor D d i) := by
  unfold reflectedMarkFactor
  apply ZeroOrUnitNorm.mul
  · apply ZeroOrUnitNorm.mul
    · exact (D.period_zeroOrUnit _).pow 2
    · apply ZeroOrUnitNorm.finset_prod
      intro p _
      apply ZeroOrUnitNorm.mul
      · exact Or.inr (D.gamma_norm p)
      · apply ZeroOrUnitNorm.pow
        exact (((D.primeCharacter_zeroOrUnit p _).mul
          (D.primeCharacter_zeroOrUnit p _)).mul
          ((D.primeCharacter_zeroOrUnit p _).zpow (-2))).mul
          ((D.primeCharacter_zeroOrUnit p _).zpow (-2))
  · apply ZeroOrUnitNorm.finset_prod
    intro p _
    exact (D.primeCharacter_zeroOrUnit p _).zpow _

theorem reflectedColumnFactor_zeroOrUnit :
    ZeroOrUnitNorm (reflectedColumnFactor D d i) := by
  unfold reflectedColumnFactor
  apply ZeroOrUnitNorm.mul
  · apply ZeroOrUnitNorm.mul
    · exact (D.period_zeroOrUnit i.c).inv
    · apply ZeroOrUnitNorm.finset_prod
      intro p _
      exact (D.primeCharacter_zeroOrUnit p _).pow _
  · apply ZeroOrUnitNorm.finset_prod
    intro p _
    apply ZeroOrUnitNorm.mul
    · exact Or.inr (D.gamma_norm p)
    · apply ZeroOrUnitNorm.pow
      exact (((D.primeCharacter_zeroOrUnit p _).mul
        (D.primeCharacter_zeroOrUnit p _)).mul
        (D.primeCharacter_zeroOrUnit p _)).mul
        ((D.primeCharacter_zeroOrUnit p _).zpow (-2))

/-- The complete literal arithmetic prefactor is bounded independently of
all three moving ideal variables and the frequency unit. -/
theorem norm_reflectedCoefficient_le :
    ‖reflectedCoefficient D d i‖ ≤ frozenBound D d i.activeFrozen * rowBound D d := by
  have hmark := norm_prod_le_one (d.marks \ i.activeMarks)
    (fun p => (D.primeNorm p : ℂ)⁻¹)
    (fun p _ => norm_real_inv_le_one (D.primeNorm_ge_one p))
  have hsP := norm_real_sqrt_inv_le_one (D.normI_ge_one (activeMarkedIdeal D i))
  have hn := norm_real_inv_le_one (D.normI_ge_one i.n)
  have hc := norm_real_sqrt_inv_le_one (D.normI_ge_one i.c)
  have hmove := ((D.idealCharacter_zeroOrUnit d.moving
    (D.generator i.c * D.generator i.n)).pow 3).norm_le
  have hactive := ((D.idealCharacter_zeroOrUnit (activeMarkedIdeal D i)
    (D.generator i.c)).zpow (-2)).norm_le
  have h := norm_mul_bound (norm_mul_bound (norm_mul_bound (norm_mul_bound
    (norm_mul_bound (norm_mul_bound (norm_mul_bound (norm_mul_bound
      (norm_mul_bound hmark hsP) (norm_frozenOmega_le D d i)) hn)
      (reflectedMarkFactor_zeroOrUnit D d i).norm_le)
      (norm_reflectedRowFactor_le D d i))
      (reflectedColumnFactor_zeroOrUnit D d i).norm_le) hc) hmove) hactive
  simpa only [reflectedCoefficient, div_eq_mul_inv, mul_one, one_mul] using h

end ThetaGlobal.ReflectedCoefficientModel

