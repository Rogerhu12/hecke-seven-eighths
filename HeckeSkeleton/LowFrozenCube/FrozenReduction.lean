import HeckeSkeleton.LowFrozenCube.PrimeCoordinates
import HeckeSkeleton.LowFrozenCube.CoefficientSeparation
import HeckeSkeleton.LowFrozenCube.HybridExit

/-!
# The complete algebraic frozen reduction in prime coordinates

The source row below contains the three unfrozen coefficients, all three
mixed reciprocity phases, and the original complementary cube denominator.
Its equality to the normalized hybrid row is proved from canonical prime
coordinates. The support splitting, its uniqueness, and the mark/cube
coprimality are derived; none of those conclusions is an input field.
-/

namespace HeckeSkeleton.LowFrozenCube

open scoped BigOperators Classical

noncomputable section

namespace FrozenReduction

variable {ι A : Type*} [CommMonoid A]

/-- The raw arithmetic inputs: prime coordinates, the sextic symbol and
reciprocity, the fixed support, ordinary primes, and the frozen minimum.
There is no finite-row identity or energy estimate among these fields. -/
structure Data (ι A : Type*) [CommMonoid A] where
  coords : A ≃* Multiplicative (ι →₀ ℕ)
  symbol : A → A →* ℂ
  sixth : ∀ a b, (symbol a b) ^ 6 =
    if PrimeCoordinates.Coprime coords a b then (1 : ℂ) else 0
  reciprocal : ∀ a b, symbol a b = symbol b a
  /-- Fixed exclusions for original rows and active marked tuples. -/
  support : Finset ι
  /-- The active ordinary product `f₀`. Dual columns and complementary cubes
  avoid only this set, so inactive primes remain allowed in those variables. -/
  ordinary : Finset ι
  ordinary_subset : ordinary ⊆ support
  digit : ι → ℕ
  minimum : A
  minimum_ordinary : PrimeCoordinates.Supported coords ordinary minimum

namespace Data

variable (D : Data ι A)

theorem minimum_supported : PrimeCoordinates.Supported D.coords D.support D.minimum := by
  intro p hp
  exact D.minimum_ordinary p (fun ho => hp (D.ordinary_subset ho))

theorem avoids_ordinary_of_avoids_support (a : A)
    (ha : PrimeCoordinates.Avoids D.coords D.support a) :
    PrimeCoordinates.Avoids D.coords D.ordinary a := by
  intro p hp
  exact ha p (D.ordinary_subset hp)

def prime (p : ι) : A :=
  D.coords.symm (Multiplicative.ofAdd (Finsupp.single p 1))

def ordinarySymbol (p : ι) (a : A) : ℂ := D.symbol a (D.prime p)

def exponents (x : A) : ι → ℕ :=
  PrimeCoordinates.valuation D.coords (D.minimum * x ^ 3)

/-- The actual canonical minimum condition includes the exceptional zero
case, so no supported cube is hidden at a zero minimum exponent. -/
def CanonicalCube (x : A) : Prop :=
  ∀ p, CanonicalFrozenPair (PrimeCoordinates.valuation D.coords D.minimum p)
    (PrimeCoordinates.valuation D.coords x p)

theorem canonical_admissible (x : A) (hx : D.CanonicalCube x) :
    ∀ p, AdmissibleExponent (D.exponents x p) := by
  intro p
  apply canonicalPair_admissible (hx p)
  simp [exponents]

theorem canonical_minimum (x : A) (hx : D.CanonicalCube x) :
    frozenBase (D.exponents x) = fun p => PrimeCoordinates.valuation D.coords D.minimum p := by
  funext p
  have he : D.exponents x p = PrimeCoordinates.valuation D.coords D.minimum p +
      3 * PrimeCoordinates.valuation D.coords x p := by simp [exponents]
  exact (frozenExponent_unique (hx p) he).1.symm

theorem canonical_supported (x : A) (hx : D.CanonicalCube x) :
    PrimeCoordinates.Supported D.coords D.support x := by
  intro p hp
  have hm := D.minimum_supported p hp
  have hc := hx p
  unfold CanonicalFrozenPair at hc
  omega

theorem canonical_supported_ordinary (x : A) (hx : D.CanonicalCube x) :
    PrimeCoordinates.Supported D.coords D.ordinary x := by
  intro p hp
  have hm := D.minimum_ordinary p hp
  have hc := hx p
  unfold CanonicalFrozenPair at hc
  omega

theorem canonical_split (x n : A) (hx : D.CanonicalCube x)
    (hn : PrimeCoordinates.Avoids D.coords D.ordinary n) :
    PrimeCoordinates.cubeSplit D.coords D.ordinary (x * n) = (x, n) :=
  PrimeCoordinates.cubeSplit_mul D.coords D.ordinary x n (D.canonical_supported_ordinary x hx) hn

theorem canonical_coprime (P x : A) (hP : PrimeCoordinates.Avoids D.coords D.support P)
    (hx : D.CanonicalCube x) : PrimeCoordinates.Coprime D.coords P x :=
  PrimeCoordinates.coprime_of_avoids_supported D.coords D.support P x hP
    (D.canonical_supported x hx)

theorem canonical_coprime_ordinary (a x : A)
    (ha : PrimeCoordinates.Avoids D.coords D.ordinary a) (hx : D.CanonicalCube x) :
    PrimeCoordinates.Coprime D.coords a x :=
  PrimeCoordinates.coprime_of_avoids_supported D.coords D.ordinary a x ha
    (D.canonical_supported_ordinary x hx)

def mark (a₀ : A → ℂ) (P : A) : ℂ :=
  markCoefficient D.symbol D.ordinary D.ordinarySymbol D.digit
    (PrimeCoordinates.valuation D.coords D.minimum) a₀ D.minimum P

def rowFactor (ρ₀ : A → ℂ) (d : A) : ℂ :=
  rowCoefficient D.symbol D.ordinary D.ordinarySymbol D.digit
    (PrimeCoordinates.valuation D.coords D.minimum) ρ₀ D.minimum d

def column (lam : A → ℂ) (c : A) : ℂ :=
  columnCoefficient D.symbol D.ordinary D.ordinarySymbol D.digit
    (PrimeCoordinates.valuation D.coords D.minimum) lam D.minimum c

theorem mark_frozen (a₀ : A → ℂ) (P x : A)
    (hP : PrimeCoordinates.Avoids D.coords D.support P) (hx : D.CanonicalCube x) :
    markCoefficient D.symbol D.ordinary D.ordinarySymbol D.digit (D.exponents x)
      a₀ (D.minimum * x ^ 3) P = D.mark a₀ P := by
  have h := markCoefficient_frozen D.symbol (PrimeCoordinates.Coprime D.coords) D.sixth
    D.ordinary D.ordinarySymbol D.digit (D.exponents x)
    (D.canonical_admissible x hx) a₀ D.minimum x P (D.canonical_coprime P x hP hx)
  rw [D.canonical_minimum x hx] at h
  exact h

theorem rowFactor_frozen (ρ₀ : A → ℂ) (d x : A) (hx : D.CanonicalCube x) :
    rowCoefficient D.symbol D.ordinary D.ordinarySymbol D.digit (D.exponents x)
      ρ₀ (D.minimum * x ^ 3) d = D.rowFactor ρ₀ d * (D.symbol d x) ^ 3 := by
  have h := rowCoefficient_frozen D.symbol D.ordinary D.ordinarySymbol D.digit
    (D.exponents x) (D.canonical_admissible x hx) ρ₀ D.minimum x d
  rw [D.canonical_minimum x hx] at h
  exact h

theorem column_frozen (lam : A → ℂ) (c x : A)
    (hc : PrimeCoordinates.Avoids D.coords D.ordinary c) (hx : D.CanonicalCube x) :
    columnCoefficient D.symbol D.ordinary D.ordinarySymbol D.digit (D.exponents x)
      lam (D.minimum * x ^ 3) c = D.column lam c := by
  have h := columnCoefficient_frozen D.symbol (PrimeCoordinates.Coprime D.coords) D.sixth
    D.ordinary D.ordinarySymbol D.digit (D.exponents x)
    (D.canonical_admissible x hx) lam D.minimum x c (D.canonical_coprime_ordinary c x hc hx)
  rw [D.canonical_minimum x hx] at h
  exact h

/-- All three mixed phases before reciprocity. -/
def mixedPhase (d P c n : A) : ℂ :=
  ((D.symbol d P) ^ 4 * (D.symbol P d) ^ 2) *
    (D.symbol d c * (D.symbol c d) ^ 2) * (D.symbol d n) ^ 3 *
      ((D.symbol P c) ^ 2 * (D.symbol c P) ^ 2) *
        (if PrimeCoordinates.Coprime D.coords P n then (1 : ℂ) else 0)

theorem mixedPhase_eq (d P c n : A) :
    D.mixedPhase d P c n =
      (if PrimeCoordinates.Coprime D.coords P d then (1 : ℂ) else 0) *
        ((D.symbol d (c * n)) ^ 3 * (D.symbol P c) ^ 4 *
          (if PrimeCoordinates.Coprime D.coords P n then (1 : ℂ) else 0)) := by
  unfold mixedPhase
  rw [row_mark_phase D.symbol (PrimeCoordinates.Coprime D.coords) D.reciprocal D.sixth,
    row_column_phase D.symbol D.reciprocal,
    mark_column_phase D.symbol D.reciprocal,
    PrimeCoordinates.coprime_symm D.coords d P, map_mul, mul_pow]
  ring

/-- The source summand still carries all unfrozen coefficient factors. -/
def sourceTerm (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
    (Ω : A → A → A → ℂ) (d P c x n : A) : ℂ :=
  (markCoefficient D.symbol D.ordinary D.ordinarySymbol D.digit (D.exponents x)
      a₀ (D.minimum * x ^ 3) P / (Real.sqrt (normI P) : ℂ)) *
    rowCoefficient D.symbol D.ordinary D.ordinarySymbol D.digit (D.exponents x)
      ρ₀ (D.minimum * x ^ 3) d *
    columnCoefficient D.symbol D.ordinary D.ordinarySymbol D.digit (D.exponents x)
      lam (D.minimum * x ^ 3) c *
    (Ω c x n / (normI n : ℂ)) * D.mixedPhase d P c n

def sourceRow (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
    (Ω : A → A → A → ℂ) (marks columns : Finset A)
    (pairs : Finset (A × A)) (d : A) : ℂ :=
  ∑ P ∈ marks, ∑ c ∈ columns, ∑ q ∈ pairs,
    D.sourceTerm normI a₀ ρ₀ lam Ω d P c q.1 q.2

def residualCoefficient (normI : A → ℝ) (lam : A → ℂ)
    (Ω : A → A → A → ℂ) (c x n : A) : ℂ :=
  D.column lam c * (Ω c x n / (normI n : ℂ))

def beta (normI : A → ℝ) (lam : A → ℂ) (Ω : A → A → A → ℂ) :
    A → A → ℂ :=
  fullCubeCoefficient (PrimeCoordinates.cubeSplit D.coords D.ordinary)
    (D.residualCoefficient normI lam Ω)

/-- Freeze the three actual coefficient formulas and all mixed phases before
performing any cube reindexing. -/
theorem sourceRow_eq_frozen (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
    (Ω : A → A → A → ℂ) (marks columns : Finset A)
    (pairs : Finset (A × A))
    (hmarks : ∀ P ∈ marks, PrimeCoordinates.Avoids D.coords D.support P)
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hpairs : ∀ q ∈ pairs, D.CanonicalCube q.1) (d : A) :
    D.sourceRow normI a₀ ρ₀ lam Ω marks columns pairs d =
      D.rowFactor ρ₀ d * frozenSeparatedRow D.symbol (PrimeCoordinates.Coprime D.coords)
        (fun P => D.mark a₀ P / (Real.sqrt (normI P) : ℂ))
        (D.residualCoefficient normI lam Ω) marks columns pairs d := by
  unfold sourceRow frozenSeparatedRow frozenCubeInner
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro q hq
  unfold sourceTerm residualCoefficient
  rw [D.mark_frozen a₀ P q.1 (hmarks P hP) (hpairs q hq),
    D.rowFactor_frozen ρ₀ d q.1 (hpairs q hq),
    D.column_frozen lam c q.1 (hcolumns c hc) (hpairs q hq),
    D.mixedPhase_eq]
  ring

/-- The exact normalized hybrid row follows from canonical prime-coordinate
splitting. The hypotheses are elementary support/canonical-minimum conditions,
not a chosen split or an already separated row identity. -/
theorem sourceRow_eq_hybridRow (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
    (Ω : A → A → A → ℂ) (marks columns : Finset A)
    (pairs : Finset (A × A))
    (hmarks : ∀ P ∈ marks, PrimeCoordinates.Avoids D.coords D.support P)
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hpairs : ∀ q ∈ pairs, D.CanonicalCube q.1 ∧ PrimeCoordinates.Avoids D.coords D.ordinary q.2)
    (d : A) :
    D.sourceRow normI a₀ ρ₀ lam Ω marks columns pairs d =
      D.rowFactor ρ₀ d * HeckeSkeleton.LowHybrid.hybridRow
        (fun a b => D.symbol a b) (PrimeCoordinates.Coprime D.coords) normI
        (D.mark a₀) (D.beta normI lam Ω) marks columns (pairs.image cubeProduct) d := by
  rw [D.sourceRow_eq_frozen normI a₀ ρ₀ lam Ω marks columns pairs
    hmarks hcolumns (fun q hq => (hpairs q hq).1) d]
  have hsplit : ∀ q ∈ pairs,
      PrimeCoordinates.cubeSplit D.coords D.ordinary (cubeProduct q) = q := by
    intro q hq
    exact D.canonical_split q.1 q.2 (hpairs q hq).1 (hpairs q hq).2
  have hPx : ∀ P ∈ marks, ∀ q ∈ pairs, PrimeCoordinates.Coprime D.coords P q.1 := by
    intro P hP q hq
    exact D.canonical_coprime P q.1 (hmarks P hP) (hpairs q hq).1
  rw [frozenSeparatedRow_eq_hybrid D.symbol (PrimeCoordinates.Coprime D.coords) D.sixth
    marks columns pairs (PrimeCoordinates.cubeSplit D.coords D.ordinary) hsplit
    (fun P => D.mark a₀ P / (Real.sqrt (normI P) : ℂ))
    (D.residualCoefficient normI lam Ω) hPx d,
    hybridSeparatedRow_eq_normalizedRow D.symbol (PrimeCoordinates.Coprime D.coords) D.sixth]
  rfl

end Data

end FrozenReduction

end

end HeckeSkeleton.LowFrozenCube
