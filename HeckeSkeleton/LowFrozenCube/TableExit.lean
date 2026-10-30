import HeckeSkeleton.LowFrozenCube.FrozenBounds
import HeckeSkeleton.LowFrozenCube.LocalTable
import HeckeSkeleton.LowFrozenCube.PrimeProducts

/-!
# The explicit local table supplies the frozen hybrid normalization

This joins the literal local coefficients to the complete unfrozen source
row. The full coefficient majorant is proved from the local table and the
prime-product norm formula. It is not an input to the final theorem.
-/

namespace HeckeSkeleton.LowFrozenCube.FrozenReduction

open scoped BigOperators Classical

noncomputable section

variable {ι A : Type*} [CommMonoid A]

namespace Data

variable (D : Data ι A)

theorem prime_eq_primeElement (p : ι) :
    D.prime p = PrimeCoordinates.primeElement D.coords p := rfl

theorem canonical_residual (x : A) (hx : D.CanonicalCube x) :
    frozenCube (D.exponents x) = fun p => PrimeCoordinates.valuation D.coords x p := by
  funext p
  have he : D.exponents x p = PrimeCoordinates.valuation D.coords D.minimum p +
      3 * PrimeCoordinates.valuation D.coords x p := by simp [exponents]
  exact (frozenExponent_unique (hx p) he).2.symm

theorem canonical_supported_on (s : Finset ι)
    (hminimum : PrimeCoordinates.Supported D.coords s D.minimum)
    (x : A) (hx : D.CanonicalCube x) : PrimeCoordinates.Supported D.coords s x := by
  intro p hp
  have hm := hminimum p hp
  have hc := hx p
  unfold CanonicalFrozenPair at hc
  omega

/-- This fixed scalar uses only the table entries at the minimum exponents. -/
def tableMajorant (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) : ℝ :=
  ∏ p ∈ D.ordinary,
    ‖LocalTable.ordinaryScalar (normI (D.prime p) : ℂ) (first p) (prefactor p)
      (atZero p) (D.digit p) (PrimeCoordinates.valuation D.coords D.minimum p)‖

theorem tableMajorant_nonneg (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) : 0 ≤ D.tableMajorant normI first prefactor atZero :=
  Finset.prod_nonneg (fun _ _ => norm_nonneg _)

/-- The remaining column/cube character and norm phases are independent of
the row and marked variable, as in the explicit reflected coefficient. -/
def tableOmega (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ) (c x n : A) : ℂ :=
  phase c x n * LocalTable.localProduct D.ordinary (fun p => normI (D.prime p))
    first prefactor atZero D.digit (D.exponents x)

theorem table_minimumMajorant_eq (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (x : A) (hx : D.CanonicalCube x) :
    LocalTable.minimumMajorant D.ordinary (fun p => normI (D.prime p))
      first prefactor atZero D.digit (D.exponents x) =
      D.tableMajorant normI first prefactor atZero := by
  unfold LocalTable.minimumMajorant tableMajorant
  apply Finset.prod_congr rfl
  intro p hp
  have hm : frozenMin (D.exponents x p) =
      PrimeCoordinates.valuation D.coords D.minimum p :=
    congrFun (D.canonical_minimum x hx) p
  rw [hm]

/-- The product of the local cube denominators is the norm of the actual
supported cube factor, by unique prime-coordinate factorization. -/
theorem table_cubeNorm_eq (normI : A →* ℝ)
    (hminimum : PrimeCoordinates.Supported D.coords D.ordinary D.minimum)
    (x : A) (hx : D.CanonicalCube x) :
    LocalTable.cubeNorm D.ordinary (fun p => normI (D.prime p))
      (D.exponents x) = normI x := by
  unfold LocalTable.cubeNorm
  calc
    (∏ p ∈ D.ordinary, normI (D.prime p) ^ frozenCubeExp (D.exponents x p)) =
        ∏ p ∈ D.ordinary, normI (PrimeCoordinates.primeElement D.coords p) ^
          PrimeCoordinates.valuation D.coords x p := by
      apply Finset.prod_congr rfl
      intro p hp
      have hc : frozenCubeExp (D.exponents x p) =
          PrimeCoordinates.valuation D.coords x p :=
        congrFun (D.canonical_residual x hx) p
      rw [hc, D.prime_eq_primeElement]
    _ = normI x :=
      (PrimeCoordinates.norm_factorization D.coords D.ordinary x
        (D.canonical_supported_on D.ordinary hminimum x hx) normI).symm

/-- The desired C/N(x) estimate follows from the raw local table. -/
theorem tableOmega_norm_le (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
    (phase : A → A → A → ℂ)
    (hminimum : PrimeCoordinates.Supported D.coords D.ordinary D.minimum)
    (c x n : A) (hx : D.CanonicalCube x) (hphase : ‖phase c x n‖ ≤ 1) :
    ‖D.tableOmega normI first prefactor atZero phase c x n‖ ≤
      D.tableMajorant normI first prefactor atZero / normI x := by
  have h := LocalTable.phased_localProduct_norm_le D.ordinary
    (fun p => normI (D.prime p)) first prefactor atZero D.digit (D.exponents x)
    (fun p hp => hpos (D.prime p)) (fun p hp => D.canonical_admissible x hx p)
    (phase c x n) hphase
  rw [D.table_minimumMajorant_eq normI first prefactor atZero x hx,
    D.table_cubeNorm_eq normI hminimum x hx] at h
  exact h

/-- Complete local-table-to-hybrid exit. All three original coefficient
factors and the mixed phases are present in `sourceRow`; the full cube and
its coefficients are constructed. Both coefficient bounds and the exact
normalization identity are consequences of the primitive data. -/
theorem local_table_frozen_exit
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
    (phase : A → A → A → ℂ)
    (hminimum : PrimeCoordinates.Supported D.coords D.ordinary D.minimum)
    (a₀ ρ₀ lam : A → ℂ) (B : ℝ) (hB : 0 < B)
    (rows marks columns : Finset A) (pairs : Finset (A × A))
    (hrows : ∀ d ∈ rows, PrimeCoordinates.Avoids D.coords D.support d)
    (hρ₀ : ∀ d ∈ rows, ‖ρ₀ d‖ = 1)
    (hmarks : ∀ P ∈ marks, PrimeCoordinates.Avoids D.coords D.support P)
    (ha₀ : ∀ P ∈ marks, ‖a₀ P‖ ≤ 1)
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hlam : ∀ c ∈ columns, ‖lam c‖ ≤ 1)
    (hpairs : ∀ q ∈ pairs, D.CanonicalCube q.1 ∧
      PrimeCoordinates.Avoids D.coords D.ordinary q.2)
    (hphase : ∀ c ∈ columns, ∀ q ∈ pairs, ‖phase c q.1 q.2‖ ≤ 1)
    (hlower : ∀ q ∈ pairs, B ≤ normI (cubeProduct q)) :
    let Ω := D.tableOmega normI first prefactor atZero phase
    let C := D.tableMajorant normI first prefactor atZero
    (∀ P ∈ marks, ‖D.mark a₀ P‖ ≤ 1) ∧
    (∀ c ∈ columns, ∀ b ∈ pairs.image cubeProduct,
      ‖D.unitBeta normI lam Ω B C c b‖ ≤ 1) ∧
    (∑ d ∈ rows, ‖D.sourceRow normI a₀ ρ₀ lam Ω marks columns pairs d‖ ^ 2) =
      (C / B) ^ 2 * HeckeSkeleton.LowHybrid.hybridEnergy
        (fun a b => D.symbol a b) (PrimeCoordinates.Coprime D.coords) normI
        (D.mark a₀) (D.unitBeta normI lam Ω B C)
        rows marks columns (pairs.image cubeProduct) := by
  apply D.normalized_frozen_exit normI hpos a₀ ρ₀ lam
    (D.tableOmega normI first prefactor atZero phase) B
    (D.tableMajorant normI first prefactor atZero) hB
    (D.tableMajorant_nonneg normI first prefactor atZero)
    rows marks columns pairs hrows hρ₀ hmarks ha₀ hcolumns hlam hpairs
  · intro c hc q hq
    exact D.tableOmega_norm_le normI hpos first prefactor atZero phase hminimum
      c q.1 q.2 (hpairs q hq).1 (hphase c hc q hq)
  · exact hlower

end Data

end

end HeckeSkeleton.LowFrozenCube.FrozenReduction
