import HeckeGeneral.Analysis.PhysicalProbeRows
import HeckeSkeleton.HighBinSupport.ExceptionalSweptTube
import HeckeSkeleton.HighBinSupport.ExplicitEulerFamily
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Finite Laurent encodings of the actual local table interface

The output is the repository's `FiniteEulerRational`, not an unrestricted
function of s,w,z.  Evaluation is proved through a Laurent-algebra
homomorphism.  Consequently the four branches retain their values when a
Gauss polynomial vanishes; no division by such a polynomial occurs.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-30.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinFiniteTables

open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open HeckeSkeleton.HighBinContinuation
open scoped Classical

abbrev Exponent := ℤ × ℤ × ℤ
abbrev Laurent := AddMonoidAlgebra ℂ Exponent

/-- The finite support and coefficients are literally those required by
the existing project structure. -/
def toFinite (f : Laurent) : FiniteEulerPolynomial where
  powers := f.coeff.support
  coefficient := f.coeff

def exponentValue (e : Exponent) (s w z : ℂ) : ℂ :=
  -((e.1 : ℂ) * s + (e.2.1 : ℂ) * w + (e.2.2 : ℂ) * z)

def exponentialCharacter (q : ℝ) (hq : 0 < q) (s w z : ℂ) :
    Multiplicative Exponent →* ℂ where
  toFun e := (q : ℂ) ^ exponentValue e.toAdd s w z
  map_one' := by simp [exponentValue]
  map_mul' e f := by
    change (q : ℂ) ^ exponentValue (e.toAdd + f.toAdd) s w z = _
    rw [show exponentValue (e.toAdd + f.toAdd) s w z =
        exponentValue e.toAdd s w z + exponentValue f.toAdd s w z by
      simp only [exponentValue, Prod.fst_add, Prod.snd_add, Int.cast_add]
      ring]
    exact Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hq.ne')

def evaluate (q : ℝ) (hq : 0 < q) (s w z : ℂ) : Laurent →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ Exponent (exponentialCharacter q hq s w z)

theorem finiteValue_eq_evaluate (f : Laurent) (q : ℝ) (hq : 0 < q) (s w z : ℂ) :
    finiteEulerPolynomialValue (toFinite f) q s w z = evaluate q hq s w z f := by
  rw [evaluate, AddMonoidAlgebra.lift_apply']
  rfl

def monomial (e : Exponent) (c : ℂ) : Laurent := AddMonoidAlgebra.single e c

@[simp] theorem evaluate_monomial (q : ℝ) (hq : 0 < q) (s w z : ℂ)
    (e : Exponent) (c : ℂ) :
    evaluate q hq s w z (monomial e c) = c * (q : ℂ) ^ exponentValue e s w z := by
  simp [evaluate, monomial, exponentialCharacter, smul_eq_mul]

def constant (c : ℂ) : Laurent := monomial (0, 0, 0) c
def X : Laurent := monomial (1, 0, 0) 1
def Y : Laurent := monomial (0, 1, 0) 1
def V : Laurent := monomial (0, 0, 6) 1

@[simp] theorem evaluate_constant (q : ℝ) (hq : 0 < q) (s w z : ℂ) (c : ℂ) :
    evaluate q hq s w z (constant c) = c := by
  simp [constant, exponentValue]

@[simp] theorem evaluate_X (q : ℝ) (hq : 0 < q) (s w z : ℂ) :
    evaluate q hq s w z X = (q : ℂ) ^ (-s) := by
  simp [X, exponentValue]

@[simp] theorem evaluate_Y (q : ℝ) (hq : 0 < q) (s w z : ℂ) :
    evaluate q hq s w z Y = (q : ℂ) ^ (-w) := by
  simp [Y, exponentValue]

@[simp] theorem evaluate_V (q : ℝ) (hq : 0 < q) (s w z : ℂ) :
    evaluate q hq s w z V = coordV q z := by
  simp [V, exponentValue, coordV, neg_mul]

def monomialSW (q : ℝ) (c : ℂ) (r : ℝ) (m n : ℕ) : Laurent :=
  constant (c * (q : ℂ) ^ (r : ℂ)) * X ^ m * Y ^ n

theorem evaluate_monomialSW (q : ℝ) (hq : 0 < q) (s w z : ℂ)
    (c : ℂ) (r : ℝ) (m n : ℕ) :
    evaluate q hq s w z (monomialSW q c r m n) = phaseMonomial q c r s w m n := by
  rw [phaseMonomial_eq_factored q hq]
  simp [monomialSW]

def R (P : PhaseData) (q : ℝ) : Laurent :=
  constant (P.alpha ^ 2 * (q : ℂ) ^ 4) * X ^ 6 * V

theorem evaluate_R (P : PhaseData) (q : ℝ) (hq : 0 < q) (s w z : ℂ) :
    evaluate q hq s w z (R P q) = coordR P q s z := by
  rw [coordR_eq_original P q hq]
  simp [R]

def special (P : PhaseData) (q : ℝ) (j : Fin 5) : Laurent :=
  match j.val with
  | 0 => monomialSW q P.eta 1 1 1
  | 1 => monomialSW q P.c2 (3 / 2) 3 0
  | 2 => monomialSW q P.c31 2 3 1 - monomialSW q P.c32 2 4 0
  | 3 => -monomialSW q P.c4 (5 / 2) 4 1
  | _ => -monomialSW q (P.alpha ^ 2) 3 6 0

theorem evaluate_special (P : PhaseData) (q : ℝ) (hq : 0 < q)
    (s w z : ℂ) (j : Fin 5) :
    evaluate q hq s w z (special P q j) = specialTerm P q s w j := by
  fin_cases j <;> simp [special, specialTerm, evaluate_monomialSW]

/-- Unmarked denominator and numerator of the five ramified rows. -/
def ramifiedDenominator (P : PhaseData) (q : ℝ) : Laurent := 1 - R P q

def ramifiedNumerator (P : PhaseData) (q : ℝ) (j : Fin 5) : Laurent :=
  1 - R P q * constant (q : ℂ)⁻¹ -
    constant (P.eta * ((q : ℂ) - 1)) * X * Y +
    (1 - V) * special P q j

/-- Marking removes the completed-unit contribution before evaluating
the quotient. This is a subtraction of finite numerators, not a quotient
by a possibly zero Gauss factor. -/
def ramified (P : PhaseData) (q : ℝ) (j : Fin 5) (marked : Bool) : FiniteEulerRational where
  numerator := toFinite (ramifiedNumerator P q j -
    if marked then ramifiedDenominator P q else 0)
  denominator := toFinite (ramifiedDenominator P q)

theorem ramified_value (P : PhaseData) (q : ℝ) (hq : 0 < q)
    (s w z : ℂ) (j : Fin 5) (marked : Bool)
    (hR : 1 - coordR P q s z ≠ 0) :
    finiteEulerRationalValue (ramified P q j marked) q s w z =
      ramifiedTableValue P q s w z j - if marked then 1 else 0 := by
  unfold finiteEulerRationalValue ramified
  rw [finiteValue_eq_evaluate _ q hq, finiteValue_eq_evaluate _ q hq]
  cases marked <;>
    simp [ramifiedNumerator, ramifiedDenominator, evaluate_R, evaluate_special,
      ramifiedTableValue, div_eq_mul_inv] <;>
    field_simp [hR] <;> ring

/-- The unmarked finite table receives the already proved dynamic
estimate, with its exact coefficient and q-exponent. -/
theorem ramified_dynamic_bound (P : PhaseData) (q a e : ℝ)
    (hq : 2 ≤ q) (ha : 1 / 2 ≤ a) (he : 0 ≤ e)
    (s w z : ℂ) (hs : s.re = a + 16 * e) (hw : w.re = 1 - a - 6 * e)
    (hz : z.re = 17 / 50) (j : Fin 5) :
    ‖finiteEulerRationalValue (ramified P q j false) q s w z - 1‖ ≤
      9 * q ^ (-10 * e) := by
  rw [ramified_value P q (by linarith) s w z j false
    (one_sub_R_ne_zero _ (coordR_norm_le_half P q a e hq ha he s z hs hz))]
  simpa using ramified_table_dynamic_bound P q a e hq ha he s w z hs hw hz j

def W (cW : ℂ) : Laurent := constant cW * Y
def D (cD : ℂ) : Laurent := constant cD * X
def E (q : ℝ) (cE : ℂ) : Laurent := constant (cE * (q : ℂ) ^ 4) * X ^ 6 * V

def regularDenominator (q : ℝ) (cD cE : ℂ) : Laurent :=
  (1 - E q cE) * (1 - D cD)

def regularNumerator (q : ℝ) (cW cD cE : ℂ) : Laurent :=
  (1 - E q cE) * (1 - W cW * V) +
    E q cE * (1 - W cW) * ((1 - constant (q : ℂ)⁻¹) + W cW * (1 - V)) -
    D cD * (1 - W cW) * ((1 - V) + constant ((q : ℂ) - 1) * W cW * V)

def regular (q : ℝ) (cW cD cE : ℂ) (marked : Bool) : FiniteEulerRational where
  numerator := toFinite (regularNumerator q cW cD cE -
    if marked then (1 - E q cE) * (1 - W cW * V) else 0)
  denominator := toFinite (regularDenominator q cD cE)

theorem regular_value (q : ℝ) (hq : 0 < q) (cW cD cE : ℂ)
    (s w z : ℂ) (marked : Bool)
    (hD : 1 - cD * (q : ℂ) ^ (-s) ≠ 0)
    (hE : 1 - cE * (q : ℂ) ^ (4 - 6 * s) * (q : ℂ) ^ (-6 * z) ≠ 0) :
    finiteEulerRationalValue (regular q cW cD cE marked) q s w z =
      phaseRowEuler q cW cD cE s w z -
        if marked then unmarkedZeroPart q cW cD s w z else 0 := by
  have hpow : (q : ℂ) ^ 4 * ((q : ℂ) ^ (-s)) ^ 6 =
      (q : ℂ) ^ (4 - 6 * s) := by
    rw [← Complex.cpow_nat_mul, ← Complex.cpow_natCast, ← Complex.cpow_add _ _
      (Complex.ofReal_ne_zero.mpr hq.ne')]
    congr 1
    push_cast
    ring
  have hEvalE : evaluate q hq s w z (E q cE) =
      cE * (q : ℂ) ^ (4 - 6 * s) * (q : ℂ) ^ (-6 * z) := by
    simp only [E, map_mul, evaluate_constant, map_pow, evaluate_X, evaluate_V, coordV]
    rw [mul_assoc cE, hpow]
  unfold finiteEulerRationalValue regular
  rw [finiteValue_eq_evaluate _ q hq, finiteValue_eq_evaluate _ q hq]
  cases marked <;>
    simp only [Bool.false_eq_true, if_false, if_true,
      regularNumerator, regularDenominator, map_sub, map_add, map_mul, map_one, map_zero,
      hEvalE, W, D, evaluate_constant, evaluate_X, evaluate_Y, evaluate_V,
      phaseRowEuler, unmarkedZeroPart, rowEulerRationalValue, coordV, sub_zero]
  rw [sub_div, mul_div_mul_left _ _ hE]

#print axioms ramified_value
#print axioms ramified_dynamic_bound
#print axioms regular_value

end HeckeSkeleton.HighBinFiniteTables
