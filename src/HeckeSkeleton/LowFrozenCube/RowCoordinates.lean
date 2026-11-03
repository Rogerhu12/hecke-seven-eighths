import HeckeSkeleton.LowFrozenCube.PrimeCoordinates

/-!
# The actual powerful, supported, and residual row factors

The three factors are obtained from the row's prime coordinates. Their
factorization, pairwise coprimality, squarefreeness, finite-block reindexing,
and residual norm bound are proved without a supplied row splitting oracle.
-/

namespace HeckeSkeleton.LowFrozenCube.PrimeCoordinates

open scoped BigOperators Classical

noncomputable section

variable {ι A : Type*} [CommMonoid A]
variable (coords : A ≃* Multiplicative (ι →₀ ℕ))

def powerfulRowFactor (k : A) : A :=
  mapExponents coords (fun e => if 2 ≤ e then e else 0) (by decide) k

def singleRowFactor (k : A) : A :=
  mapExponents coords (fun e => if e = 1 then 1 else 0) (by decide) k

def supportedRowFactor (s : Finset ι) (k : A) : A :=
  supportedFactor coords s (singleRowFactor coords k)

def residualRowFactor (s : Finset ι) (k : A) : A :=
  awayFactor coords s (singleRowFactor coords k)

@[simp] theorem valuation_powerfulRowFactor (k : A) (p : ι) :
    valuation coords (powerfulRowFactor coords k) p =
      powerfulRowPart (valuation coords k) p := by
  simp [powerfulRowFactor, powerfulRowPart]

@[simp] theorem valuation_supportedRowFactor (s : Finset ι) (k : A) (p : ι) :
    valuation coords (supportedRowFactor coords s k) p =
      supportedRowPart s (valuation coords k) p := by
  by_cases hp : p ∈ s <;> by_cases he : valuation coords k p = 1 <;>
    simp [supportedRowFactor, singleRowFactor, supportedRowPart, hp, he]

@[simp] theorem valuation_residualRowFactor (s : Finset ι) (k : A) (p : ι) :
    valuation coords (residualRowFactor coords s k) p =
      residualRowPart s (valuation coords k) p := by
  by_cases hp : p ∈ s <;> by_cases he : valuation coords k p = 1 <;>
    simp [residualRowFactor, singleRowFactor, residualRowPart, hp, he]

/-- Exact factorization of the original row, not just of its exponent vector. -/
theorem row_factorization (s : Finset ι) (k : A) :
    k = powerfulRowFactor coords k * supportedRowFactor coords s k *
      residualRowFactor coords s k := by
  apply valuation_injective coords
  ext p
  simp only [valuation_mul_apply, valuation_powerfulRowFactor,
    valuation_supportedRowFactor, valuation_residualRowFactor]
  exact congrFun (row_decomposition s (valuation coords k)) p

theorem powerfulRowFactor_powerful (k : A) (p : ι) :
    valuation coords (powerfulRowFactor coords k) p = 0 ∨
      2 ≤ valuation coords (powerfulRowFactor coords k) p := by
  simp only [valuation_powerfulRowFactor, powerfulRowPart]
  split_ifs with h
  · exact Or.inr h
  · exact Or.inl rfl

theorem supportedRowFactor_squarefree (s : Finset ι) (k : A) (p : ι) :
    valuation coords (supportedRowFactor coords s k) p ≤ 1 := by
  rw [valuation_supportedRowFactor]
  exact supportedRowPart_squarefree s (valuation coords k) p

theorem residualRowFactor_squarefree (s : Finset ι) (k : A) (p : ι) :
    valuation coords (residualRowFactor coords s k) p ≤ 1 := by
  rw [valuation_residualRowFactor]
  exact residualRowPart_squarefree s (valuation coords k) p

theorem supportedRowFactor_supported (s : Finset ι) (k : A) :
    Supported coords s (supportedRowFactor coords s k) :=
  supportedFactor_supported coords s (singleRowFactor coords k)

theorem residualRowFactor_avoids (s : Finset ι) (k : A) :
    Avoids coords s (residualRowFactor coords s k) :=
  awayFactor_avoids coords s (singleRowFactor coords k)

theorem row_factors_pairwise_coprime (s : Finset ι) (k : A) :
    Coprime coords (powerfulRowFactor coords k) (supportedRowFactor coords s k) ∧
    Coprime coords (powerfulRowFactor coords k) (residualRowFactor coords s k) ∧
    Coprime coords (supportedRowFactor coords s k) (residualRowFactor coords s k) := by
  have h := row_parts_pairwise_disjoint s (valuation coords k)
  refine ⟨?_, ?_, ?_⟩
  · intro p
    simpa only [valuation_powerfulRowFactor, valuation_supportedRowFactor] using h.1 p
  · intro p
    simpa only [valuation_powerfulRowFactor, valuation_residualRowFactor] using h.2.1 p
  · intro p
    simpa only [valuation_supportedRowFactor, valuation_residualRowFactor] using h.2.2 p

theorem norm_row_factorization (s : Finset ι) (k : A) (normI : A →* ℝ) :
    normI k = normI (powerfulRowFactor coords k) *
      normI (supportedRowFactor coords s k) * normI (residualRowFactor coords s k) := by
  simpa only [map_mul] using congrArg normI (row_factorization coords s k)

theorem norm_residualRowFactor (s : Finset ι) (k : A)
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a) :
    normI (residualRowFactor coords s k) = normI k /
      (normI (powerfulRowFactor coords k) * normI (supportedRowFactor coords s k)) := by
  apply (eq_div_iff (mul_ne_zero (ne_of_gt (hpos _)) (ne_of_gt (hpos _)))).mpr
  rw [norm_row_factorization coords s k normI]
  ring

theorem norm_residualRowFactor_le (s : Finset ι) (k : A)
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a) (K : ℝ) (hk : normI k ≤ K) :
    normI (residualRowFactor coords s k) ≤ K /
      (normI (powerfulRowFactor coords k) * normI (supportedRowFactor coords s k)) := by
  rw [norm_residualRowFactor coords s k normI hpos]
  exact div_le_div_of_nonneg_right hk (le_of_lt (mul_pos (hpos _) (hpos _)))

def powerfulSquareFactor (a : A) : A :=
  mapExponents coords powerfulSquareExp (by simp [powerfulSquareExp]) a

def powerfulCubeFactor (a : A) : A :=
  mapExponents coords powerfulCubeDigit (by simp [powerfulCubeDigit]) a

@[simp] theorem valuation_powerfulSquareFactor (a : A) (p : ι) :
    valuation coords (powerfulSquareFactor coords a) p =
      powerfulSquareExp (valuation coords a p) := by
  simp [powerfulSquareFactor]

@[simp] theorem valuation_powerfulCubeFactor (a : A) (p : ι) :
    valuation coords (powerfulCubeFactor coords a) p =
      powerfulCubeDigit (valuation coords a p) := by
  exact valuation_mapExponents coords powerfulCubeDigit (by simp [powerfulCubeDigit]) a p

theorem powerfulCubeFactor_squarefree (a : A) (p : ι) :
    valuation coords (powerfulCubeFactor coords a) p ≤ 1 := by
  rw [valuation_powerfulCubeFactor]
  exact powerfulCubeDigit_squarefree _

theorem powerful_factorization (a : A)
    (ha : ∀ p, valuation coords a p = 0 ∨ 2 ≤ valuation coords a p) :
    a = powerfulSquareFactor coords a ^ 2 * powerfulCubeFactor coords a ^ 3 := by
  apply valuation_injective coords
  ext p
  simp only [valuation_mul_apply, valuation_pow_apply,
    valuation_powerfulSquareFactor, valuation_powerfulCubeFactor]
  exact powerfulExponent_decomposition _ (ha p)

theorem powerful_factorization_unique (a u v : A)
    (hv : ∀ p, valuation coords v p ≤ 1) (ha : a = u ^ 2 * v ^ 3) :
    u = powerfulSquareFactor coords a ∧ v = powerfulCubeFactor coords a := by
  have he : ∀ p, valuation coords a p =
      2 * valuation coords u p + 3 * valuation coords v p := by
    intro p
    rw [ha]
    simp only [valuation_mul_apply, valuation_pow_apply]
  constructor
  · apply valuation_injective coords
    ext p
    rw [valuation_powerfulSquareFactor]
    exact (powerfulExponent_unique (hv p) (he p)).1
  · apply valuation_injective coords
    ext p
    rw [valuation_powerfulCubeFactor]
    exact (powerfulExponent_unique (hv p) (he p)).2

/-- A finite fixed row block freezes the first two factors and retains only
the squarefree residual row as the hybrid row variable. -/
def rowBlock (s : Finset ι) (pow sup : A) (rows : Finset A) : Finset A :=
  rows.filter fun k => powerfulRowFactor coords k = pow ∧
    supportedRowFactor coords s k = sup

def residualRows (s : Finset ι) (pow sup : A) (rows : Finset A) : Finset A :=
  (rowBlock coords s pow sup rows).image (residualRowFactor coords s)

theorem residualRowFactor_injOn (s : Finset ι) (pow sup : A) (rows : Finset A) :
    Set.InjOn (residualRowFactor coords s) (rowBlock coords s pow sup rows : Set A) := by
  intro k hk l hl hkl
  have hk' := (Finset.mem_filter.mp hk).2
  have hl' := (Finset.mem_filter.mp hl).2
  calc
    k = powerfulRowFactor coords k * supportedRowFactor coords s k *
        residualRowFactor coords s k := row_factorization coords s k
    _ = pow * sup * residualRowFactor coords s k := by rw [hk'.1, hk'.2]
    _ = pow * sup * residualRowFactor coords s l := by rw [hkl]
    _ = powerfulRowFactor coords l * supportedRowFactor coords s l *
        residualRowFactor coords s l := by rw [hl'.1, hl'.2]
    _ = l := (row_factorization coords s l).symm

theorem sum_rowBlock_reindex {R : Type*} [AddCommMonoid R]
    (s : Finset ι) (pow sup : A) (rows : Finset A) (F : A → R) :
    (∑ k ∈ rowBlock coords s pow sup rows, F (residualRowFactor coords s k)) =
      ∑ d ∈ residualRows coords s pow sup rows, F d := by
  unfold residualRows
  rw [Finset.sum_image (residualRowFactor_injOn coords s pow sup rows)]

theorem residualRows_avoids (s : Finset ι) (pow sup : A) (rows : Finset A)
    (d : A) (hd : d ∈ residualRows coords s pow sup rows) : Avoids coords s d := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
  exact residualRowFactor_avoids coords s k

theorem residualRows_squarefree (s : Finset ι) (pow sup : A) (rows : Finset A)
    (d : A) (hd : d ∈ residualRows coords s pow sup rows) :
    ∀ p, valuation coords d p ≤ 1 := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
  exact residualRowFactor_squarefree coords s k

theorem residualRows_norm_le (s : Finset ι) (pow sup : A) (rows : Finset A)
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a) (K : ℝ)
    (hrows : ∀ k ∈ rows, normI k ≤ K)
    (d : A) (hd : d ∈ residualRows coords s pow sup rows) :
    normI d ≤ K / (normI pow * normI sup) := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
  have hk' := Finset.mem_filter.mp hk
  have h := norm_residualRowFactor_le coords s k normI hpos K (hrows k hk'.1)
  simpa only [hk'.2.1, hk'.2.2] using h

end

end HeckeSkeleton.LowFrozenCube.PrimeCoordinates
