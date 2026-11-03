module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The cube table and the surviving first-pass label

The finite exponent table and product reassembly from `FirstPassCubeLabels`
in openai/math `Arithmetic/SquarefreeDivisors.lean` at `fd4aeeb2` work in any
commutative monoid. The row hypotheses express that its values are zero or
sixth roots of unity. `LocalSource` instantiates these statements with the
repository's actual S-integer sextic ideal evaluation and its proved mask.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CubeAlgebra

open scoped BigOperators Classical

def bit (b : Bool) : ℕ := if b then 1 else 0

def parity (m : ℕ) : Bool := decide (m % 2 = 1)

/-- The primitive conductor digit at a cube prime. -/
def conductorExponent (parityBit ε₁ ε₂ : Bool) : ZMod 6 :=
  (bit ε₁ : ZMod 6) - (bit ε₂ : ZMod 6) + 3 * (bit parityBit : ZMod 6)

def crtExponent (side parityBit ε₁ ε₂ : Bool) : ℕ :=
  if conductorExponent parityBit ε₁ ε₂ = 0 then 0 else
    ((1 : ZMod 6) + if side then -conductorExponent parityBit ε₁ ε₂
      else conductorExponent parityBit ε₁ ε₂).val

def dilationExponent (parityBit ε₁ ε₂ : Bool) : ℕ :=
  if parityBit then bit ε₁ + bit ε₂ else 0

def retained (parityBit ε₁ ε₂ : Bool) : Bool := parityBit || (ε₁ && ε₂)

def evenDouble (m : ℕ) (ε₁ ε₂ : Bool) : Bool := !parity m && ε₁ && ε₂

def b0Exponent (m : ℕ) (ε₁ ε₂ : Bool) : ℕ :=
  m / 2 - bit (evenDouble m ε₁ ε₂)

theorem exponent_table (side parityBit ε₁ ε₂ : Bool) :
    (4 * bit (if side then ε₂ else ε₁) + crtExponent side parityBit ε₁ ε₂ +
      dilationExponent parityBit ε₁ ε₂) % 6 =
        if retained parityBit ε₁ ε₂ then 4 else 0 := by
  cases side <;> cases parityBit <;> cases ε₁ <;> cases ε₂ <;> decide

theorem bit_parity (m : ℕ) : bit (parity m) = m % 2 := by
  have hm := Nat.mod_lt m (by decide : 0 < 2)
  by_cases h : m % 2 = 1 <;> simp [bit, parity, h] <;> omega

theorem multiplicity_decomposition (m : ℕ) (ε₁ ε₂ : Bool) (hm : 0 < m) :
    2 * b0Exponent m ε₁ ε₂ + 2 * bit (evenDouble m ε₁ ε₂) +
      bit (parity m) = m := by
  have hmod := Nat.mod_lt m (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div m 2
  cases ε₁ <;> cases ε₂ <;> by_cases h : m % 2 = 1 <;>
    simp [b0Exponent, evenDouble, parity, bit, h] <;> omega

theorem b0Exponent_pos_of_not_retained (m : ℕ) (ε₁ ε₂ : Bool) (hm : 0 < m)
    (hret : retained (parity m) ε₁ ε₂ = false) :
    0 < b0Exponent m ε₁ ε₂ := by
  have hmod := Nat.mod_lt m (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div m 2
  cases ε₁ <;> cases ε₂ <;> by_cases h : m % 2 = 1 <;>
    simp_all [b0Exponent, evenDouble, parity, retained, bit] <;> omega

section Products

variable {R ι : Type*} [CommMonoid R]

def primeProduct (p : ι → R) (B : Finset ι) (v : ι → ℕ) : R :=
  ∏ i ∈ B, p i ^ v i

def cubeRadical (p : ι → R) (B : Finset ι) : R := ∏ i ∈ B, p i

def aLabel (p : ι → R) (B : Finset ι) (ε : ι → Bool) : R :=
  primeProduct p B (fun i => bit (ε i))

def crtLabel (p : ι → R) (B : Finset ι) (v : ι → ℕ)
    (ε₁ ε₂ : ι → Bool) (side : Bool) : R :=
  primeProduct p B (fun i => crtExponent side (parity (v i)) (ε₁ i) (ε₂ i))

def dilationLabel (p : ι → R) (B : Finset ι) (v : ι → ℕ)
    (ε₁ ε₂ : ι → Bool) : R :=
  primeProduct p B (fun i => dilationExponent (parity (v i)) (ε₁ i) (ε₂ i))

def jLabel (p : ι → R) (B : Finset ι) (v : ι → ℕ)
    (ε₁ ε₂ : ι → Bool) : R :=
  primeProduct p B (fun i => bit (retained (parity (v i)) (ε₁ i) (ε₂ i)))

def j2Label (p : ι → R) (B : Finset ι) (v : ι → ℕ)
    (ε₁ ε₂ : ι → Bool) : R :=
  primeProduct p B (fun i => bit (evenDouble (v i) (ε₁ i) (ε₂ i)))

def squarefreeLabel (p : ι → R) (B : Finset ι) (v : ι → ℕ) : R :=
  primeProduct p B (fun i => bit (parity (v i)))

def b0Label (p : ι → R) (B : Finset ι) (v : ι → ℕ)
    (ε₁ ε₂ : ι → Bool) : R :=
  primeProduct p B (fun i => b0Exponent (v i) (ε₁ i) (ε₂ i))

theorem cube_product_decomposition (p : ι → R) (B : Finset ι) (v : ι → ℕ)
    (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v i) :
    primeProduct p B v = b0Label p B v ε₁ ε₂ ^ 2 * j2Label p B v ε₁ ε₂ ^ 2 *
      squarefreeLabel p B v := by
  simp only [b0Label, j2Label, squarefreeLabel, primeProduct, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, ← pow_mul, ← pow_add]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  have h := multiplicity_decomposition (v i) (ε₁ i) (ε₂ i) (hv i hi)
  omega

theorem cube_pair_product_decomposition
    (p : ι → R) (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i + v₂ i) :
    primeProduct p B v₁ * primeProduct p B v₂ =
      b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂ ^ 2 *
      j2Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂ ^ 2 *
      squarefreeLabel p B (fun i => v₁ i + v₂ i) := by
  rw [← cube_product_decomposition p B (fun i => v₁ i + v₂ i) ε₁ ε₂ hv]
  simp only [primeProduct, pow_add, Finset.prod_mul_distrib]

theorem jLabel_eq_squarefree_mul_j2 (p : ι → R) (B : Finset ι) (v : ι → ℕ)
    (ε₁ ε₂ : ι → Bool) :
    jLabel p B v ε₁ ε₂ = squarefreeLabel p B v * j2Label p B v ε₁ ε₂ := by
  simp only [jLabel, squarefreeLabel, j2Label, primeProduct, ← Finset.prod_mul_distrib,
    ← pow_add]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  cases hp : parity (v i) <;> cases ε₁ i <;> cases ε₂ i <;>
    simp [bit, retained, evenDouble, hp]

theorem squarefree_j2_support_disjoint (B : Finset ι) (v : ι → ℕ)
    (ε₁ ε₂ : ι → Bool) :
    Disjoint (B.filter (fun i => parity (v i)))
      (B.filter (fun i => evenDouble (v i) (ε₁ i) (ε₂ i))) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have h := (Finset.mem_filter.mp hi).2
  have he := (Finset.mem_filter.mp hj).2
  simp [evenDouble, h] at he

end Products

section Rows

variable {R : Type*} [CommMonoid R] (χ : R →* ℂ)

/-- The exact zero/one mask attached to a sixth-root row. -/
def sixthMask (a : R) : ℂ := χ a ^ 6

theorem sixthMask_mul (a b : R) :
    sixthMask χ (a * b) = sixthMask χ a * sixthMask χ b := by
  simp only [sixthMask, map_mul, mul_pow]

theorem sixthMask_pow (a : R) (m : ℕ) :
    sixthMask χ (a ^ m) = sixthMask χ a ^ m := by
  simp only [sixthMask, map_pow, ← pow_mul, Nat.mul_comm]

theorem sixthMask_prod {ι : Type*} (B : Finset ι) (a : ι → R) :
    sixthMask χ (∏ i ∈ B, a i) = ∏ i ∈ B, sixthMask χ (a i) := by
  simp only [sixthMask, map_prod, Finset.prod_pow]

variable (hχ : ∀ a, χ a ^ 6 = 0 ∨ χ a ^ 6 = 1)

include hχ in
theorem row_power_mul_mask_power (a : R) (k m : ℕ) (hk : 0 < k) :
    χ a ^ k * sixthMask χ a ^ m = χ a ^ k := by
  rcases hχ a with h | h
  · have hz : χ a = 0 := (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp h
    simp [sixthMask, hz, Nat.ne_of_gt hk]
  · simp [sixthMask, h]

include hχ in
theorem row_self_pair (a : R) : χ a * star (χ a) = sixthMask χ a := by
  rcases hχ a with h | h
  · have hz : χ a = 0 := (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp h
    simp [sixthMask, hz]
  · have hn := Complex.norm_eq_one_of_pow_eq_one h (by decide : (6 : ℕ) ≠ 0)
    have hz : χ a ≠ 0 := by intro hz; simpa [hz] using h
    rw [sixthMask, h, Complex.star_def, ← Complex.inv_eq_conj hn, mul_inv_cancel₀ hz]

def localFactor (side parityBit ε₁ ε₂ : Bool) (a : R) : ℂ :=
  sixthMask χ a * χ a ^ (4 * bit (if side then ε₂ else ε₁)) *
    χ a ^ crtExponent side parityBit ε₁ ε₂ *
    χ a ^ dilationExponent parityBit ε₁ ε₂

include hχ in
theorem localFactor_eq (side parityBit ε₁ ε₂ : Bool) (a : R) :
    localFactor χ side parityBit ε₁ ε₂ a =
      if retained parityBit ε₁ ε₂ then χ a ^ 4 else sixthMask χ a := by
  rcases hχ a with h | h
  · have hz : χ a = 0 := (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp h
    simp [localFactor, sixthMask, hz]
  · simp only [localFactor, sixthMask, h, one_mul, ← pow_add]
    rw [pow_eq_pow_mod _ h, exponent_table]
    split <;> simp

include hχ in
theorem localFactor_eq_b0 (side ε₁ ε₂ : Bool) (a : R) (m : ℕ) (hm : 0 < m) :
    localFactor χ side (parity m) ε₁ ε₂ a =
      χ (a ^ bit (retained (parity m) ε₁ ε₂)) ^ 4 *
        sixthMask χ (a ^ b0Exponent m ε₁ ε₂) := by
  rw [localFactor_eq χ hχ, map_pow, sixthMask_pow]
  cases hr : retained (parity m) ε₁ ε₂
  · have hpos := b0Exponent_pos_of_not_retained m ε₁ ε₂ hm hr
    simp only [Bool.false_eq_true, ↓reduceIte, bit, pow_zero, one_pow, one_mul]
    rcases hχ a with h | h <;> simp [sixthMask, h, Nat.ne_of_gt hpos]
  · simp only [↓reduceIte, bit, pow_one]
    exact (row_power_mul_mask_power χ hχ a 4 _ (by decide)).symm

include hχ in
theorem first_pass_label_identity {ι : Type*}
    (p : ι → R) (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) (side : Bool) :
    sixthMask χ (cubeRadical p B) *
      χ (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      χ (crtLabel p B v ε₁ ε₂ side) * χ (dilationLabel p B v ε₁ ε₂) =
    χ (jLabel p B v ε₁ ε₂) ^ 4 * sixthMask χ (b0Label p B v ε₁ ε₂) := by
  simp only [cubeRadical, aLabel, crtLabel, dilationLabel, jLabel, b0Label,
    primeProduct, sixthMask_prod, map_prod, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [map_pow, map_pow, map_pow]
  convert localFactor_eq_b0 χ hχ side (ε₁ i) (ε₂ i) (p i) (v i) (hv i hi) using 1
  cases side <;> simp only [localFactor, Bool.false_eq_true, ↓reduceIte,
    ← pow_mul, Nat.mul_comm]

include hχ in
theorem radical_mask_absorbs {ι : Type*} (p : ι → R) (B : Finset ι) (v : ι → ℕ) :
    sixthMask χ (cubeRadical p B) * sixthMask χ (primeProduct p B v) =
      sixthMask χ (cubeRadical p B) := by
  simp only [cubeRadical, primeProduct, sixthMask_prod, sixthMask_pow,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rcases hχ (p i) with h | h <;> simp [sixthMask, h]

include hχ in
theorem masked_dual_dilation {ι : Type*}
    (p : ι → R) (B : Finset ι) (v : ι → ℕ) (z : R) (c : ℂ) :
    sixthMask χ (cubeRadical p B) * c * star (χ z) =
      (sixthMask χ (cubeRadical p B) * c * χ (primeProduct p B v)) *
        star (χ (z * primeProduct p B v)) := by
  rw [map_mul, star_mul]
  calc
    _ = (sixthMask χ (cubeRadical p B) * sixthMask χ (primeProduct p B v)) * c *
        star (χ z) := by rw [radical_mask_absorbs χ hχ]
    _ = _ := by rw [← row_self_pair χ hχ (primeProduct p B v)]; ring

include hχ in
theorem first_pass_after_dual_dilation {ι : Type*}
    (p : ι → R) (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) (side : Bool) (z : R) :
    (sixthMask χ (cubeRadical p B) *
      χ (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      χ (crtLabel p B v ε₁ ε₂ side)) * star (χ z) =
    (χ (jLabel p B v ε₁ ε₂) ^ 4 * sixthMask χ (b0Label p B v ε₁ ε₂)) *
      star (χ (z * dilationLabel p B v ε₁ ε₂)) := by
  have hd := masked_dual_dilation χ hχ p B
    (fun i => dilationExponent (parity (v i)) (ε₁ i) (ε₂ i)) z
    (χ (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      χ (crtLabel p B v ε₁ ε₂ side))
  change _ = (_ * χ (dilationLabel p B v ε₁ ε₂)) * _ at hd
  simp only [← mul_assoc] at hd
  rw [first_pass_label_identity χ hχ p B v ε₁ ε₂ hv side] at hd
  exact hd

end Rows

end HeckeSkeleton.Moments.MOM_INV_STEP.CubeAlgebra

end
