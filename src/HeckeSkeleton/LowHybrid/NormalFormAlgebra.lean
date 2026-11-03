import HeckeSkeleton.LowHybrid.Rows
import HeckeSkeleton.LowHybrid.Normalization

/-!
# Algebraic data and local identities for the exact hybrid normal form

The fields below are elementary arithmetic laws, finite divisor data, and
the full Mobius coprimality identity. There is no norm or energy estimate in
this structure. In particular, the final row identity is proved from these
laws in `NormalForm.lean`, rather than included among the input fields.
-/

namespace HeckeSkeleton.LowHybrid.NormalForm

open scoped BigOperators Classical
noncomputable section

variable {I : Type*} [CommMonoid I]

structure Arithmetic (I : Type*) [CommMonoid I] where
  normI : I → ℝ
  norm_nonneg : ∀ x, 0 ≤ normI x
  norm_mul : ∀ x y, normI (x * y) = normI x * normI y
  symbol : I → I → ℂ
  symbol_mul_left : ∀ x y z, symbol (x * y) z = symbol x z * symbol y z
  symbol_mul_right : ∀ x y z, symbol x (y * z) = symbol x y * symbol x z
  cop : I → I → Prop
  cop_symm : ∀ x y, cop x y ↔ cop y x
  cop_mul_left : ∀ x y z, cop (x * y) z ↔ cop x z ∧ cop y z
  cop_mul_right : ∀ x y z, cop x (y * z) ↔ cop x y ∧ cop x z
  six : ∀ x y, symbol x y ^ 6 = if cop x y then 1 else 0
  divisors : I → Finset I
  mu : I → ℂ
  quotient : I → I → I
  divisor_dvd : ∀ x d, d ∈ divisors x → d ∣ x
  quotient_spec : ∀ d x, d ∣ x → d * quotient d x = x
  mobius_expansion : ∀ p k,
    (if cop p k then (1 : ℂ) else 0) =
      ∑ d ∈ divisors k, if d ∣ p then mu d else 0

namespace Arithmetic

variable (S : Arithmetic I)

def mask (x y : I) : ℂ := if S.cop x y then 1 else 0
def quadratic (x y : I) : ℂ := S.symbol x y ^ 3
def cubic (x y : I) : ℂ := S.symbol x y ^ (-2 : ℤ)
def weight (d : I) : ℂ := (Real.sqrt (S.normI d) : ℂ)⁻¹

theorem mask_symm (x y : I) : S.mask x y = S.mask y x := by
  simp only [mask, S.cop_symm x y]

theorem mask_mul_left (x y z : I) : S.mask (x * y) z = S.mask x z * S.mask y z := by
  simp only [mask, S.cop_mul_left]
  by_cases hx : S.cop x z <;> by_cases hy : S.cop y z <;> simp [hx, hy]

theorem mask_mul_right (x y z : I) : S.mask x (y * z) = S.mask x y * S.mask x z := by
  simp only [mask, S.cop_mul_right]
  by_cases hx : S.cop x y <;> by_cases hy : S.cop x z <;> simp [hx, hy]

theorem mask_square (x y : I) : S.mask x (y ^ 2) = S.mask x y := by
  simp only [mask, pow_two, S.cop_mul_right, and_self]

theorem symbol_zero (x y : I) (h : ¬ S.cop x y) : S.symbol x y = 0 := by
  have hz : S.symbol x y ^ 6 = 0 := by simpa only [if_neg h] using S.six x y
  exact (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hz

theorem quadratic_mul_left (x y z : I) :
    S.quadratic (x * y) z = S.quadratic x z * S.quadratic y z := by
  simp only [quadratic, S.symbol_mul_left, mul_pow]

theorem quadratic_mul_right (x y z : I) :
    S.quadratic x (y * z) = S.quadratic x y * S.quadratic x z := by
  simp only [quadratic, S.symbol_mul_right, mul_pow]

theorem cubic_mul_left (x y z : I) :
    S.cubic (x * y) z = S.cubic x z * S.cubic y z := by
  simp only [cubic, S.symbol_mul_left, mul_zpow]

theorem cubic_mul_right (x y z : I) :
    S.cubic x (y * z) = S.cubic x y * S.cubic x z := by
  simp only [cubic, S.symbol_mul_right, mul_zpow]

theorem cubic_mask (x y : I) : S.cubic x y * S.mask x y = S.cubic x y := by
  by_cases h : S.cop x y
  · simp only [mask, if_pos h, mul_one]
  · simp [cubic, mask, h, S.symbol_zero x y h]

theorem quadratic_square (x y : I) : S.quadratic x (y ^ 2) = S.mask x y := by
  unfold quadratic
  rw [pow_two, S.symbol_mul_right]
  calc
    (S.symbol x y * S.symbol x y) ^ 3 = S.symbol x y ^ 6 := by ring
    _ = S.mask x y := S.six x y

/-- Completing the square leaves both original collision masks. -/
theorem completed_quadratic (k t c m h : I) :
    S.quadratic k ((c * m) * (c * h * t ^ 2)) =
      S.quadratic k (m * h) * S.mask k c * S.mask k t := by
  have he : (c * m) * (c * h * t ^ 2) = (m * h) * (c * t) ^ 2 := by
    simp only [pow_two]
    ac_rfl
  rw [he, S.quadratic_mul_right, S.quadratic_square, S.mask_mul_right]
  ring

/-- The cubic kernel absorbs the redundant r,c masks, including their zeros. -/
theorem completed_cubic (p r t c m h : I) :
    S.cubic p (r * c * m) * S.mask p (r * c * h * t ^ 2) =
      S.cubic p r * S.cubic p (c * m) * S.mask p (h * t) := by
  simp only [S.cubic_mul_right, S.mask_mul_right, S.mask_square]
  calc
    _ = (S.cubic p r * S.mask p r) * (S.cubic p c * S.mask p c) *
        S.cubic p m * (S.mask p h * S.mask p t) := by ring
    _ = _ := by rw [S.cubic_mask, S.cubic_mask]; ring

theorem normalization_mul (d p : I) (a : ℂ) :
    a / (Real.sqrt (S.normI (d * p)) : ℂ) =
      S.weight d * (a / (Real.sqrt (S.normI p) : ℂ)) := by
  rw [S.norm_mul]
  exact divisor_column_normalization (S.normI d) (S.normI p)
    (S.norm_nonneg d) (S.norm_nonneg p) a

/-- Original mark support after extracting a fixed divisor. -/
def markQuotients (marks : Finset I) (d : I) : Finset I :=
  (marks.filter fun p => d ∣ p).image (S.quotient d)

/-- Exact divisor reindexing. It only uses reconstruction, so no arbitrary
choice of quotient can merge two distinct original indices. -/
theorem sum_divisor_reindex (marks : Finset I) (d : I) (F : I → ℂ) :
    (∑ p ∈ marks with d ∣ p, F p) =
      ∑ p ∈ S.markQuotients marks d, F (d * p) := by
  unfold markQuotients
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [S.quotient_spec d p (Finset.mem_filter.mp hp).2]
  · intro a ha b hb hab
    rw [← S.quotient_spec d a (Finset.mem_filter.mp ha).2,
      ← S.quotient_spec d b (Finset.mem_filter.mp hb).2, hab]

/-- Exact full mask expansion, keeping an arbitrary original-column value. -/
theorem mask_sum_expansion (marks : Finset I) (k : I) (F : I → ℂ) :
    (∑ p ∈ marks, S.mask p k * F p) =
      ∑ d ∈ S.divisors k, S.mu d * ∑ p ∈ marks with d ∣ p, F p := by
  calc
    _ = ∑ p ∈ marks, ∑ d ∈ S.divisors k,
        (if d ∣ p then S.mu d else 0) * F p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [mask, S.mobius_expansion, Finset.sum_mul]
    _ = ∑ d ∈ S.divisors k, ∑ p ∈ marks,
        (if d ∣ p then S.mu d else 0) * F p := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases h : d ∣ p <;> simp [h]

end Arithmetic

end
end HeckeSkeleton.LowHybrid.NormalForm
