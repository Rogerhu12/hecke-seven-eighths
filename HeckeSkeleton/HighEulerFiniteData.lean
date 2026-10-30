import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic.Ring

/-!
Mathlib-only finite Euler data.  The raw structures are separate types with
the same fields as the supplied project API; the adapter copies those fields.

AI-assisted source: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
Reference: openai/math commit fd4aeeb2, HighRowsClosed and HighRowsRamified.
This module imports only Mathlib and can be checked independently.
Its project adapter is HighEulerTables.lean.

This file defines finite data only.  The parameters must be calibrated to the
actual local Gauss sums before the data can be used in `RowEulerData`.  It does
not claim the initial Fourier-series identity or a theorem on all number fields.

The reference valuation classes are 1 through 5; `j : Fin 5` represents j.val+1.
The `marked` flag means that the prime is required to divide the completed
index c*n^3, as in `wholeIndexMask`, not that the prime is deleted.
-/

noncomputable section

namespace HBEulerFiniteData

open scoped Classical BigOperators

abbrev Exponent := ℤ × ℤ × ℤ
abbrev Terms := List (Exponent × ℂ)


/-- Independent finite Laurent data, not the project's polynomial type. -/
structure RawPolynomial where
  powers : Finset Exponent
  coefficient : Exponent → ℂ

/-- Evaluation against an arbitrary weight, before specializing to powers. -/
def weightedValue (A : RawPolynomial) (weight : Exponent → ℂ) : ℂ :=
  ∑ e ∈ A.powers, A.coefficient e * weight e

/-- Same evaluation expression as the actual project's polynomial evaluator. -/
def polynomialValue (A : RawPolynomial) (q : ℝ) (s w z : ℂ) : ℂ :=
  ∑ e ∈ A.powers, A.coefficient e * (q : ℂ) ^
    (-((e.1 : ℂ) * s + (e.2.1 : ℂ) * w + (e.2.2 : ℂ) * z))

/-- Independent rational data whose numerator and denominator are finite. -/
structure RawRational where
  numerator : RawPolynomial
  denominator : RawPolynomial

def rationalValue (A : RawRational) (q : ℝ) (s w z : ℂ) : ℂ :=
  polynomialValue A.numerator q s w z / polynomialValue A.denominator q s w z

/-- Repeated exponent triples are added.  No term is overwritten. -/
def ofTerms (ts : Terms) : RawPolynomial where
  powers := (ts.map Prod.fst).toFinset
  coefficient := fun e => ((ts.filter fun t => t.1 = e).map Prod.snd).sum

/-- Direct evaluation of a finite term list, preserving multiplicities. -/
def termsValue (ts : Terms) (weight : Exponent → ℂ) : ℂ :=
  (ts.map fun t => t.2 * weight t.1).sum

@[simp] theorem termsValue_nil (weight : Exponent → ℂ) :
    termsValue [] weight = 0 := rfl

@[simp] theorem termsValue_cons (t : Exponent × ℂ) (ts : Terms)
    (weight : Exponent → ℂ) :
    termsValue (t :: ts) weight = t.2 * weight t.1 + termsValue ts weight := rfl

@[simp] theorem termsValue_append (xs ys : Terms) (weight : Exponent → ℂ) :
    termsValue (xs ++ ys) weight = termsValue xs weight + termsValue ys weight := by
  simp [termsValue, List.map_append, List.sum_append]

theorem ofTerms_coefficient_cons (t : Exponent × ℂ) (ts : Terms) (e : Exponent) :
    (ofTerms (t :: ts)).coefficient e =
      (if t.1 = e then t.2 else 0) + (ofTerms ts).coefficient e := by
  classical
  by_cases he : t.1 = e <;> simp [ofTerms, he]

/-- Grouping by exponents over any finite set containing their support. -/
private theorem sum_coefficients_supported (F : Finset Exponent)
    (weight : Exponent → ℂ) :
    ∀ ts : Terms, (∀ t ∈ ts, t.1 ∈ F) →
      (∑ e ∈ F, (ofTerms ts).coefficient e * weight e) = termsValue ts weight := by
  classical
  intro ts
  induction ts with
  | nil =>
      intro h
      simp [ofTerms, termsValue]
  | cons t ts ih =>
      intro h
      have ht : t.1 ∈ F := h t (by simp)
      have hts : ∀ b ∈ ts, b.1 ∈ F := by
        intro b hb
        exact h b (by simp [hb])
      have hsingle :
          (∑ e ∈ F, (if t.1 = e then t.2 else 0) * weight e) = t.2 * weight t.1 := by
        rw [Finset.sum_eq_single t.1]
        · simp
        · intro b hb hne
          simp [Ne.symm hne]
        · intro hnot
          exact (hnot ht).elim
      calc
        (∑ e ∈ F, (ofTerms (t :: ts)).coefficient e * weight e) =
            (∑ e ∈ F, (if t.1 = e then t.2 else 0) * weight e) +
              (∑ e ∈ F, (ofTerms ts).coefficient e * weight e) := by
                simp only [ofTerms_coefficient_cons, add_mul, Finset.sum_add_distrib]
        _ = t.2 * weight t.1 + termsValue ts weight := by rw [hsingle, ih hts]
        _ = termsValue (t :: ts) weight := rfl

/-- The finite data performs exactly the original list evaluation, even when
several original terms have the same exponent. -/
theorem weightedValue_ofTerms (ts : Terms) (weight : Exponent → ℂ) :
    weightedValue (ofTerms ts) weight = termsValue ts weight := by
  apply sum_coefficients_supported
  intro t ht
  change t.1 ∈ (ts.map Prod.fst).toFinset
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨t, ht, rfl⟩)

theorem polynomialValue_ofTerms (ts : Terms) (q : ℝ) (s w z : ℂ) :
    polynomialValue (ofTerms ts) q s w z =
      (ts.map fun t => t.2 * (q : ℂ) ^
        (-((t.1.1 : ℂ) * s + (t.1.2.1 : ℂ) * w + (t.1.2.2 : ℂ) * z))).sum := by
  exact weightedValue_ofTerms ts
    (fun e => (q : ℂ) ^ (-((e.1 : ℂ) * s + (e.2.1 : ℂ) * w + (e.2.2 : ℂ) * z)))

/-- Multiplication of a finite term list by c*X^a*Y^b*Z^d.
Here X=q^(-s), Y=q^(-w), and Z=q^(-z). -/
def shiftScale (e : Exponent) (c : ℂ) (ts : Terms) : Terms :=
  ts.map fun t =>
    ((e.1 + t.1.1, e.2.1 + t.1.2.1, e.2.2 + t.1.2.2), c * t.2)

/-- The D_j term of the five-row table.  q is the complex cast of the norm.
The symbols eta, A, C, omega, rho, and G_r are the literal local parameters.
In the reference normalization C is the conjugate normalized quadratic Gauss
sum, omega is the sextic character at -1, and rho is its value on the row unit.
-/
def ramifiedSpecialTerms (q eta A C omega rho G1 G2 G3 G4 : ℂ)
    (j : Fin 5) : Terms :=
  match j.val with
  | 0 => [((1, 1, 0), eta * q)]
  | 1 => [((3, 0, 0), rho⁻¹ ^ 3 * A * C * G3 * q)]
  | 2 => [((3, 1, 0), rho⁻¹ ^ 2 * A * C * G1 * G2 * q),
          ((4, 0, 0), -(eta * A * C * omega * rho⁻¹ ^ 4 * q ^ 2 * (G4 / G1)))]
  | 3 => [((4, 1, 0), -(eta * A * C * rho⁻¹ ^ 3 * q ^ 2 * G3))]
  | _ => [((6, 0, 0), -(A ^ 2 * q ^ 3))]

/-- Five ramified finite tables, including the whole-index marked versions.

Writing V=q^(-6z), R=A^2*q^4*q^(-6s)*V, and D_j for the special polynomial,
the unmarked value is
  [1 - R/q - eta*(q-1)*q^(-s-w) + (1-V)*D_j] / (1-R),
and the marked value is the unmarked value minus 1 whenever 1-R is nonzero.
This is data construction, not a calibration assertion.
-/
def ramifiedFiniteFactor (q eta A C omega rho G1 G2 G3 G4 : ℂ)
    (j : Fin 5) (marked : Bool) : RawRational :=
  let special := ramifiedSpecialTerms q eta A C omega rho G1 G2 G3 G4 j
  let common : Terms :=
    if marked then
      [((6, 0, 6), A ^ 2 * q ^ 3 * (q - 1)),
       ((1, 1, 0), -(eta * (q - 1)))]
    else
      [((0, 0, 0), 1),
       ((6, 0, 6), -(A ^ 2 * q ^ 3)),
       ((1, 1, 0), -(eta * (q - 1)))]
  { numerator := ofTerms (common ++ special ++ shiftScale (0, 0, 6) (-1) special)
    denominator := ofTerms
      [((0, 0, 0), 1), ((6, 0, 6), -(A ^ 2 * q ^ 4))] }

/-- The marked numerator is the unmarked numerator minus the common
denominator, for every weight, without a power-multiplication premise. -/
theorem ramified_marked_numerator_weighted
    (q eta A C omega rho G1 G2 G3 G4 : ℂ) (j : Fin 5)
    (weight : Exponent → ℂ) :
    weightedValue (ramifiedFiniteFactor q eta A C omega rho G1 G2 G3 G4 j true).numerator
        weight =
      weightedValue (ramifiedFiniteFactor q eta A C omega rho G1 G2 G3 G4 j false).numerator
        weight -
      weightedValue (ramifiedFiniteFactor q eta A C omega rho G1 G2 G3 G4 j false).denominator
        weight := by
  simp [ramifiedFiniteFactor, weightedValue_ofTerms, termsValue,
    List.map_append, List.sum_append] <;> ring

theorem ramified_marked_numerator_value
    (q eta A C omega rho G1 G2 G3 G4 : ℂ) (j : Fin 5)
    (norm : ℝ) (s w z : ℂ) :
    polynomialValue (ramifiedFiniteFactor q eta A C omega rho G1 G2 G3 G4 j true).numerator
        norm s w z =
      polynomialValue (ramifiedFiniteFactor q eta A C omega rho G1 G2 G3 G4 j false).numerator
        norm s w z -
      polynomialValue (ramifiedFiniteFactor q eta A C omega rho G1 G2 G3 G4 j false).denominator
        norm s w z := by
  exact ramified_marked_numerator_weighted q eta A C omega rho G1 G2 G3 G4 j
    (fun e => (norm : ℂ) ^ (-((e.1 : ℂ) * s + (e.2.1 : ℂ) * w + (e.2.2 : ℂ) * z)))

/-- The denominator hypothesis is necessary because Lean's division is
totalized.  This is a relation between the finite tables themselves. -/
theorem ramified_marked_value
    (q eta A C omega rho G1 G2 G3 G4 : ℂ) (j : Fin 5)
    (norm : ℝ) (s w z : ℂ)
    (hden : polynomialValue
      (ramifiedFiniteFactor q eta A C omega rho G1 G2 G3 G4 j false).denominator
      norm s w z ≠ 0) :
    rationalValue (ramifiedFiniteFactor q eta A C omega rho G1 G2 G3 G4 j true)
        norm s w z =
      rationalValue (ramifiedFiniteFactor q eta A C omega rho G1 G2 G3 G4 j false)
        norm s w z - 1 := by
  have he : polynomialValue
      (ramifiedFiniteFactor q eta A C omega rho G1 G2 G3 G4 j true).denominator norm s w z =
      polynomialValue
      (ramifiedFiniteFactor q eta A C omega rho G1 G2 G3 G4 j false).denominator norm s w z := rfl
  simp only [rationalValue]
  rw [ramified_marked_numerator_value, he, sub_div, div_self hden]

/-- A marked prime with unramified row character.

Put D=d*q^(-s), W=rho*q^(-w), E=A^2*q^4*q^(-6s-6z).
This is the finite rational datum
  (1-W) * [ E*(1-q^-1) + E*W*(1-V)
            - D*(1-V) - D*(q-1)*W*V ] / [(1-E)*(1-D)].
The parameter d must be the actual coefficient of psi*conjugate(chi).
At a common unramified prime it is eta*conjugate(rho).
-/
def unramifiedMarkedFiniteFactor (q A rho d : ℂ) : RawRational :=
  let inside : Terms :=
    [((6, 0, 6), A ^ 2 * q ^ 3 * (q - 1)),
     ((6, 1, 6), A ^ 2 * q ^ 4 * rho),
     ((6, 1, 12), -(A ^ 2 * q ^ 4 * rho)),
     ((1, 0, 0), -d),
     ((1, 0, 6), d),
     ((1, 1, 6), -(d * (q - 1) * rho))]
  { numerator := ofTerms (inside ++ shiftScale (0, 1, 0) (-rho) inside)
    denominator := ofTerms
      [((0, 0, 0), 1),
       ((6, 0, 6), -(A ^ 2 * q ^ 4)),
       ((1, 0, 0), -d),
       ((7, 0, 6), A ^ 2 * q ^ 4 * d)] }

/-!
## Evaluation and integration obligations

For a real q>0 put X=(q:ℂ)^(-s), Y=(q:ℂ)^(-w), V=(q:ℂ)^(-6*z),
R=A^2*(q:ℂ)^4*X^6*V, and let D_j be the evaluation of
`ramifiedSpecialTerms` with j.val+1 as the valuation class.

The finite-term evaluation identities to establish using the actual API are:

* `rationalValue (ramifiedFiniteFactor (q:ℂ) eta A C omega rho
    G1 G2 G3 G4 j false) q s w z`
  equals `[1 - A^2*q^3*X^6*V - eta*(q-1)*X*Y + (1-V)*D_j] / (1-R)`.

* With `true`, the numerator is
  `A^2*q^3*(q-1)*X^6*V - eta*(q-1)*X*Y + (1-V)*D_j`.
  If 1-R is nonzero, this value is the unmarked value minus 1.

* The evaluation of `unramifiedMarkedFiniteFactor` is the rational function
  displayed in its documentation.  Products of the exponential monomials
  use q>0; denominator divisions retain Lean's totalized convention.

These identities describe finite rational data.  The separate arithmetic
calibration must identify the parameters with the actual local Gauss sums,
prove the local coefficient expansion of `finitePoissonFactor`, and then
identify the local factor with this datum.  They are deliberately not
asserted as theorems in this source.

For an actual `RowEulerData` construction:
  - p in support(u), p not in Q: select the five-row unmarked datum;
  - p in support(u), p in Q: select its marked datum;
  - p not in support(u), p in Q: select the unramified marked datum.
The first two cases additionally require that the row character and its
target twist have zero local Euler coefficient.  The actual inducing
character product must be inspected before applying this simplification.
There is no `highEulerData` declaration without this arithmetic calibration.
-/

end HBEulerFiniteData

end

#print axioms HBEulerFiniteData.ramifiedFiniteFactor
#print axioms HBEulerFiniteData.unramifiedMarkedFiniteFactor
#print axioms HBEulerFiniteData.weightedValue_ofTerms
#print axioms HBEulerFiniteData.polynomialValue_ofTerms
#print axioms HBEulerFiniteData.ramified_marked_numerator_value
#print axioms HBEulerFiniteData.ramified_marked_value
