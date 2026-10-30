import HeckeSkeleton.LowFrozenCube.Valuations

/-!
# Multiplicative realization of valuation decompositions

These identities apply directly to finite products of prime ideals in any
commutative monoid.  Consequently the valuation decompositions are not only
equalities of exponent vectors: they give exact product, cube, and row
factorizations once the prime factorization of an ideal has been supplied.
-/

namespace HeckeSkeleton.LowFrozenCube

open scoped BigOperators Classical

variable {ι A : Type*} [CommMonoid A]

def valuationProduct (prime : ι → A) (s : Finset ι) (v : ι → ℕ) : A :=
  ∏ p ∈ s, prime p ^ v p

theorem valuationProduct_add (prime : ι → A) (s : Finset ι) (v w : ι → ℕ) :
    valuationProduct prime s (fun p => v p + w p) =
      valuationProduct prime s v * valuationProduct prime s w := by
  simp [valuationProduct, pow_add, Finset.prod_mul_distrib]

theorem valuationProduct_scale (prime : ι → A) (s : Finset ι)
    (v : ι → ℕ) (n : ℕ) :
    valuationProduct prime s (fun p => n * v p) = valuationProduct prime s v ^ n := by
  simp only [valuationProduct]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.mul_comm n (v p), pow_mul]

/-- The exact multiplicative identity `a' = a_min x^3`. -/
theorem frozen_product_decomposition (prime : ι → A) (s : Finset ι)
    (v : ι → ℕ) (hv : ∀ p, AdmissibleExponent (v p)) :
    valuationProduct prime s v =
      valuationProduct prime s (frozenBase v) * valuationProduct prime s (frozenCube v) ^ 3 := by
  calc
    valuationProduct prime s v =
        valuationProduct prime s (fun p => frozenBase v p + 3 * frozenCube v p) :=
      congrArg (valuationProduct prime s) (frozenValuation_decomposition v hv)
    _ = valuationProduct prime s (frozenBase v) *
        valuationProduct prime s (fun p => 3 * frozenCube v p) :=
      valuationProduct_add prime s (frozenBase v) (fun p => 3 * frozenCube v p)
    _ = _ := by rw [valuationProduct_scale]

/-- The exact multiplicative identity `b = x n'`. -/
theorem fullCube_product_decomposition [DecidableEq ι] (prime : ι → A)
    (primes frozen : Finset ι) (v : ι → ℕ) :
    valuationProduct prime primes v =
      valuationProduct prime primes (supportedPart frozen v) *
        valuationProduct prime primes (awayPart frozen v) := by
  calc
    valuationProduct prime primes v = valuationProduct prime primes
        (fun p => supportedPart frozen v p + awayPart frozen v p) :=
      congrArg (valuationProduct prime primes) (fullCube_decomposition frozen v)
    _ = _ := valuationProduct_add prime primes _ _

/-- The exact multiplicative identity `k = k_pow k_sup d`. -/
theorem row_product_decomposition [DecidableEq ι] (prime : ι → A)
    (primes frozen : Finset ι) (v : ι → ℕ) :
    valuationProduct prime primes v =
      valuationProduct prime primes (powerfulRowPart v) *
        valuationProduct prime primes (supportedRowPart frozen v) *
          valuationProduct prime primes (residualRowPart frozen v) := by
  calc
    valuationProduct prime primes v = valuationProduct prime primes
        (fun p => powerfulRowPart v p + supportedRowPart frozen v p +
          residualRowPart frozen v p) :=
      congrArg (valuationProduct prime primes) (row_decomposition frozen v)
    _ = _ := by rw [valuationProduct_add, valuationProduct_add]

/-- The prime-factor product of a powerful ideal is a square times a cube
whose exponent vector is squarefree. -/
theorem powerful_product_decomposition (prime : ι → A) (s : Finset ι)
    (v : ι → ℕ) (hv : ∀ p, v p = 0 ∨ 2 ≤ v p) :
    valuationProduct prime s v =
      valuationProduct prime s (fun p => powerfulSquareExp (v p)) ^ 2 *
        valuationProduct prime s (fun p => powerfulCubeDigit (v p)) ^ 3 := by
  have he : v = fun p => 2 * powerfulSquareExp (v p) + 3 * powerfulCubeDigit (v p) := by
    funext p
    exact powerfulExponent_decomposition (v p) (hv p)
  calc
    valuationProduct prime s v = valuationProduct prime s
        (fun p => 2 * powerfulSquareExp (v p) + 3 * powerfulCubeDigit (v p)) :=
      congrArg (valuationProduct prime s) he
    _ = _ := by rw [valuationProduct_add, valuationProduct_scale, valuationProduct_scale]

end HeckeSkeleton.LowFrozenCube
