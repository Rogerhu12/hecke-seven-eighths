import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Four component-class slices preserve sieve coefficient independence

Freezing only the product of row, mark and column classes would couple the
coefficients.  We instead freeze each of the four classes.  The row mask
has one row argument, the mark mask one mark argument, and the column mask
has the two column arguments.  Thus multiplying the mark/column coefficients
by these masks preserves their original independence and their norm bounds.

The exact finite identity is followed by Cauchy--Schwarz with the explicit
factor `card G ^ 4`.  This is a fixed finite loss, not an assumed energy bound.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.ClassSlices
open scoped BigOperators

abbrev FourClasses (G : Type*) := (G × G) × (G × G)

def mask {G : Type*} (a b : G) : ℂ := by
  classical
  exact if a = b then 1 else 0

def rowMask {G : Type*} (q : FourClasses G) (r : G) : ℂ := mask q.1.1 r

def markMask {G : Type*} (q : FourClasses G) (m : G) : ℂ := mask q.1.2 m

def columnMask {G : Type*} (q : FourClasses G) (c n : G) : ℂ :=
  mask q.2.1 c * mask q.2.2 n

@[simp] theorem mask_self {G : Type*} (a : G) : mask a a = 1 := by
  simp [mask]

theorem norm_mask_le_one {G : Type*} (a b : G) : ‖mask a b‖ ≤ 1 := by
  classical
  by_cases h : a = b <;> simp [mask, h]

theorem norm_rowMask_le_one {G : Type*} (q : FourClasses G) (r : G) :
    ‖rowMask q r‖ ≤ 1 := norm_mask_le_one _ _

theorem norm_markMask_le_one {G : Type*} (q : FourClasses G) (m : G) :
    ‖markMask q m‖ ≤ 1 := norm_mask_le_one _ _

theorem norm_columnMask_le_one {G : Type*} (q : FourClasses G) (c n : G) :
    ‖columnMask q c n‖ ≤ 1 := by
  rw [columnMask, norm_mul]
  have h := mul_le_mul (norm_mask_le_one q.2.1 c) (norm_mask_le_one q.2.2 n)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simpa using h

/-- Masking a mark coefficient does not introduce a row or column argument. -/
theorem norm_mark_coefficient_le {G : Type*} (q : FourClasses G) (m : G) (a : ℂ) :
    ‖a * markMask q m‖ ≤ ‖a‖ := by
  rw [norm_mul]
  simpa using mul_le_mul_of_nonneg_left (norm_markMask_le_one q m) (norm_nonneg a)

/-- Masking a joint column coefficient does not introduce a row or mark argument. -/
theorem norm_column_coefficient_le {G : Type*} (q : FourClasses G) (c n : G) (b : ℂ) :
    ‖b * columnMask q c n‖ ≤ ‖b‖ := by
  rw [norm_mul]
  simpa using mul_le_mul_of_nonneg_left (norm_columnMask_le_one q c n) (norm_nonneg b)

theorem card_fourClasses (G : Type*) [Fintype G] :
    Fintype.card (FourClasses G) = Fintype.card G ^ 4 := by
  simp only [FourClasses, Fintype.card_prod]
  ring

/-- The exact four-slice expansion of an arbitrary class-dependent kernel.
No regularity or size assumption on `H` is required. -/
theorem class_expansion {G : Type*} [Fintype G]
    (H : G → G → G → G → ℂ) (r m c n : G) :
    H r m c n = ∑ q : FourClasses G,
      H q.1.1 q.1.2 q.2.1 q.2.2 * rowMask q r * markMask q m * columnMask q c n := by
  classical
  let q0 : FourClasses G := ((r, m), (c, n))
  symm
  calc
    _ = H q0.1.1 q0.1.2 q0.2.1 q0.2.2 *
        rowMask q0 r * markMask q0 m * columnMask q0 c n := by
      apply Finset.sum_eq_single q0
      · intro q _ hq
        by_cases hr : q.1.1 = r
        · by_cases hm : q.1.2 = m
          · by_cases hc : q.2.1 = c
            · by_cases hn : q.2.2 = n
              · have he : q = q0 := by
                  apply Prod.ext
                  · exact Prod.ext hr hm
                  · exact Prod.ext hc hn
                exact (hq he).elim
              · simp [rowMask, markMask, columnMask, mask, hn]
            · simp [rowMask, markMask, columnMask, mask, hc]
          · simp [rowMask, markMask, columnMask, mask, hm]
        · simp [rowMask, markMask, columnMask, mask, hr]
      · simp
    _ = _ := by simp [q0, rowMask, markMask, columnMask]

/-- The unmodified finite hybrid row with its class-dependent kernel. -/
def originalRow {G R M Q : Type*}
    (marks : Finset M) (columns : Finset Q)
    (rClass : R → G) (mClass : M → G) (cClass nClass : Q → G)
    (a : M → ℂ) (b : Q → ℂ) (χ : R → M → Q → ℂ)
    (H : G → G → G → G → ℂ) (r : R) : ℂ :=
  ∑ m ∈ marks, a m * ∑ q ∈ columns,
    b q * χ r m q * H (rClass r) (mClass m) (cClass q) (nClass q)

/-- The same row after freezing the four classes.  Its coefficients have
exactly the types required by the hybrid sieve: `a : M → ℂ`, `b : Q → ℂ`. -/
def slicedRow {G R M Q : Type*}
    (marks : Finset M) (columns : Finset Q)
    (rClass : R → G) (mClass : M → G) (cClass nClass : Q → G)
    (a : M → ℂ) (b : Q → ℂ) (χ : R → M → Q → ℂ)
    (s : FourClasses G) (r : R) : ℂ :=
  rowMask s (rClass r) * ∑ m ∈ marks,
    (a m * markMask s (mClass m)) * ∑ q ∈ columns,
      (b q * columnMask s (cClass q) (nClass q)) * χ r m q

/-- Finite expansion before row norms are taken. Surviving marked variables
remain summed inside each row. -/
theorem originalRow_eq_sliced {G R M Q : Type*} [Fintype G]
    (marks : Finset M) (columns : Finset Q)
    (rClass : R → G) (mClass : M → G) (cClass nClass : Q → G)
    (a : M → ℂ) (b : Q → ℂ) (χ : R → M → Q → ℂ)
    (H : G → G → G → G → ℂ) (r : R) :
    originalRow marks columns rClass mClass cClass nClass a b χ H r =
      ∑ s : FourClasses G, H s.1.1 s.1.2 s.2.1 s.2.2 *
        slicedRow marks columns rClass mClass cClass nClass a b χ s r := by
  classical
  let f : FourClasses G → M → Q → ℂ := fun s m q =>
    H s.1.1 s.1.2 s.2.1 s.2.2 * rowMask s (rClass r) *
      (a m * markMask s (mClass m)) *
      ((b q * columnMask s (cClass q) (nClass q)) * χ r m q)
  have hpoint (m : M) (q : Q) :
      a m * (b q * χ r m q * H (rClass r) (mClass m) (cClass q) (nClass q)) =
        ∑ s : FourClasses G, f s m q := by
    rw [class_expansion H (rClass r) (mClass m) (cClass q) (nClass q)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    dsimp [f]
    ring
  calc
    _ = ∑ m ∈ marks, ∑ q ∈ columns, ∑ s : FourClasses G, f s m q := by
      unfold originalRow
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro q _
      exact hpoint m q
    _ = ∑ m ∈ marks, ∑ s : FourClasses G, ∑ q ∈ columns, f s m q := by
      apply Finset.sum_congr rfl
      intro m _
      exact Finset.sum_comm
    _ = ∑ s : FourClasses G, ∑ m ∈ marks, ∑ q ∈ columns, f s m q :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [slicedRow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro q _
      dsimp [f]
      ring

/-- Ordinary finite Cauchy--Schwarz for complex rows. -/
theorem norm_sum_sq_le_card {A : Type*} (s : Finset A) (f : A → ℂ) :
    ‖∑ a ∈ s, f a‖ ^ 2 ≤ (s.card : ℝ) * ∑ a ∈ s, ‖f a‖ ^ 2 := by
  calc
    _ ≤ (∑ a ∈ s, ‖f a‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s f) 2
    _ ≤ _ := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun a => ‖f a‖)

/-- The explicit finite class loss after taking the physical row energy. -/
theorem four_class_energy {G R : Type*} [Fintype G]
    (rows : Finset R) (f : FourClasses G → R → ℂ) :
    (∑ r ∈ rows, ‖∑ s : FourClasses G, f s r‖ ^ 2) ≤
      (Fintype.card G : ℝ) ^ 4 * ∑ s : FourClasses G, ∑ r ∈ rows, ‖f s r‖ ^ 2 := by
  have hcard : (Fintype.card (FourClasses G) : ℝ) = (Fintype.card G : ℝ) ^ 4 := by
    exact_mod_cast card_fourClasses G
  calc
    _ ≤ ∑ r ∈ rows, (Fintype.card (FourClasses G) : ℝ) *
        ∑ s : FourClasses G, ‖f s r‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro r _
      simpa using norm_sum_sq_le_card (Finset.univ : Finset (FourClasses G)) (fun s => f s r)
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_comm, hcard]

/-- Applying the class expansion to the actual finite hybrid row costs at
most `|G|^4`; both marking and joint-column independence are retained. -/
theorem originalRow_energy_le {G R M Q : Type*} [Fintype G]
    (rows : Finset R) (marks : Finset M) (columns : Finset Q)
    (rClass : R → G) (mClass : M → G) (cClass nClass : Q → G)
    (a : M → ℂ) (b : Q → ℂ) (χ : R → M → Q → ℂ)
    (H : G → G → G → G → ℂ) :
    (∑ r ∈ rows, ‖originalRow marks columns rClass mClass cClass nClass a b χ H r‖ ^ 2) ≤
      (Fintype.card G : ℝ) ^ 4 * ∑ s : FourClasses G, ∑ r ∈ rows,
        ‖H s.1.1 s.1.2 s.2.1 s.2.2 *
          slicedRow marks columns rClass mClass cClass nClass a b χ s r‖ ^ 2 := by
  simp_rw [originalRow_eq_sliced]
  exact four_class_energy rows _

#print axioms class_expansion
#print axioms originalRow_eq_sliced
#print axioms originalRow_energy_le

end HeckeSkeleton.LowEnergy.ClassSlices
