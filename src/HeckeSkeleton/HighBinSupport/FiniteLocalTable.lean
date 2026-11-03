import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-!
# Finite valuation computation behind the five ramified Euler rows

`valuationGauss` is the conductor table obtained by residue-field lifting.
The accompanying module `FiniteResidueFourier` proves the actual finite-ring
lifting and cancellation statements. This file proves the finite arithmetic
which takes that conductor table to the five closed rational local factors;
it does not assert that the uploaded number-field implementation has already
been connected to that table.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

noncomputable section
namespace HighBin.FiniteLocalTable
open scoped Classical BigOperators

/-- Gauss transform of a residue-field character inflated to a length-`t`
local quotient, at a frequency of valuation `J`. The index `r` records its
power in the sextic character. The principal character is the unit
indicator, so its two nonzero branches have values `q-1` and `-1`. -/
def valuationGauss (q : ℂ) (G : ℕ → ℂ) (ρ : ℂ) (t r J : ℕ) : ℂ :=
  q ^ (t - 1) *
    if 6 ∣ r then
      (if t ≤ J then q - 1 else if J = t - 1 then -1 else 0)
    else if J = t - 1 then ρ⁻¹ ^ r * G (r % 6) else 0

/-- Literal local convolution after the finite Fourier reduction.
For a positive completed-index valuation `t`, only denominator valuations
zero and one survive. In the `k=1` term the extra `1/q` is the normalization
in `finitePoissonFactor`. The field contains twelfth roots, hence the
sextic residue character takes value one at minus one. -/
def positiveConvolution (q : ℂ) (G : ℕ → ℂ) (ρ : ℂ) (t k J : ℕ) : ℂ :=
  if k = 0 then valuationGauss q G ρ t t J
  else if k = 1 then G 1 / q * valuationGauss q G ρ (t + 1) (t - 1) J
  else 0

/-- The actual theta/period coefficient in local variables X=q^-s, Y=q^-w,
V=q^-6z, with G(r) the unnormalized finite Gauss sums. -/
def weightedTerm (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ)
    (j e l k m : ℕ) : ℂ :=
  (G 2 / q) ^ e * θ ^ (e + 3 * l) / q ^ l *
    X ^ (e + 3 * l) * Y ^ k * V ^ m *
      positiveConvolution q G ρ (e + 3 * l) k (j + 6 * m)

/-- The three explicit `m` terms, the last representing the stable tail. -/
def baseAt (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ) (j e l : ℕ) : ℂ :=
  ∑ k : Fin 2,
    (weightedTerm q θ G ρ X Y V j e l k.val 0 +
      weightedTerm q θ G ρ X Y V j e l k.val 1 +
      weightedTerm q θ G ρ X Y V j e l k.val 2 / (1 - V))

/-- Four residue classes of e+3l, before the common geometric denominator. -/
def baseMarked (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ) (j : ℕ) : ℂ :=
  baseAt q θ G ρ X Y V j 0 2 + baseAt q θ G ρ X Y V j 1 0 +
    baseAt q θ G ρ X Y V j 0 1 + baseAt q θ G ρ X Y V j 1 1

/-- Arithmetic value of the target phase, before the global mixed-Gauss
calibration identifies it with the target's prime Hecke coefficient. -/
def eta (q θ : ℂ) (G : ℕ → ℂ) : ℂ := -(θ * G 1 * G 2 / q)

def ratio (q θ X V : ℂ) : ℂ := θ ^ 6 * q ^ 4 * X ^ 6 * V

def special (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y : ℂ) (j : Fin 5) : ℂ :=
  match j.val with
  | 0 => eta q θ G * q * X * Y
  | 1 => θ ^ 3 * q * G 3 * ρ⁻¹ ^ 3 * X ^ 3
  | 2 => θ ^ 3 * q * G 1 * G 2 * ρ⁻¹ ^ 2 * X ^ 3 * Y +
      θ ^ 4 * q * G 2 * G 4 * ρ⁻¹ ^ 4 * X ^ 4
  | 3 => θ ^ 4 * q * G 1 * G 2 * G 3 * ρ⁻¹ ^ 3 * X ^ 4 * Y
  | _ => -(θ ^ 6 * q ^ 3 * X ^ 6)

/-- The five-row numerator follows from exactly twenty-four finite table
entries, including both principal-character branches and every zero. -/
theorem baseMarked_five_rows (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ)
    (hq : q ≠ 0) (hρ : ρ ≠ 0) (hV : 1 - V ≠ 0) (j : Fin 5) :
    (1 - V) * baseMarked q θ G ρ X Y V (j.val + 1) =
      ratio q θ X V * (1 - q⁻¹) - eta q θ G * (q - 1) * X * Y +
        (1 - V) * special q θ G ρ X Y j := by
  fin_cases j <;>
    norm_num [baseMarked, baseAt, weightedTerm, positiveConvolution,
      valuationGauss, Fin.sum_univ_two, special, ratio, eta] <;>
    field_simp [hq, hρ, hV] <;> ring

/-- The finite-table correction, after the two geometric series are summed. -/
def finiteTableCorrection (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ) (j : Fin 5) : ℂ :=
  1 + (1 - V) * baseMarked q θ G ρ X Y V (j.val + 1) /
    (1 - ratio q θ X V)

/-- Exact quotient formula: no division by a Gauss polynomial occurs. -/
theorem finiteTableCorrection_eq (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ)
    (hq : q ≠ 0) (hρ : ρ ≠ 0) (hV : 1 - V ≠ 0) (hR : 1 - ratio q θ X V ≠ 0)
    (j : Fin 5) :
    finiteTableCorrection q θ G ρ X Y V j =
      (1 - ratio q θ X V / q - eta q θ G * (q - 1) * X * Y +
        (1 - V) * special q θ G ρ X Y j) / (1 - ratio q θ X V) := by
  rw [finiteTableCorrection, baseMarked_five_rows q θ G ρ X Y V hq hρ hV]
  field_simp [hq, hR]
  ring

#print axioms baseMarked_five_rows
#print axioms finiteTableCorrection_eq

end HighBin.FiniteLocalTable
