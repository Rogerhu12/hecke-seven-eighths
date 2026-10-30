import HeckePort.Moments.Canonical
import HeckePort.Moments.FirstPoisson

/-!
# Active and principal prime supports of a pair of moduli

Port of the formal part of openai/math `OAI/NumberTheory/DirichletL/Moments/Active.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

The sextic residue characters `actualSextic (P i) (hg i)` of the primes `P i` are arbitrary
characters `χ i : MulChar (𝓞 K ⧸ P i) ℂ` with `χ i ^ 6 = 1` (openai:
`actualSextic_order_six`; over a general field: the sextic symbol of `HeckeGeneral`), and the
character `idealRowHom z (∏ P i ^ c i)` of a product of prime powers is the product of the powers of
the local characters, `hrow`.  Ported: `netExponent`, `local_pair_reduction`, the active and
principal supports, `rowCoprimeMask` with `principal_product_eq_mask`, `common_ideal_pair_active`
and `activePrimes_pairwise_coprime`.  Not ported: `active_gauss_norm` and `common_ideal_pair_poisson`
(the normalized sextic Gauss sum `canonicalNormalizedGauss` and the radial Poisson formula for
`ℤ[ω]`).
-/

noncomputable section

namespace HeckePort.Moments.Active

open scoped NumberField BigOperators Classical

variable {K : Type*} [Field K] [NumberField K]

def netExponent (c d : ℕ) : ℕ := (c + 5 * d) % 6

theorem local_pair_reduction {R : Type*} [CommRing R] [Finite Rˣ] (χ : MulChar R ℂ) (h6 : χ ^ 6 = 1)
    (c d : ℕ) (x : R) :
    (χ ^ c) x * star ((χ ^ d) x) = (χ ^ netExponent c d) x := by
  have h5 : χ ^ 5 = χ⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using h6
  rw [MulChar.star_apply', ← MulChar.mul_apply]
  congr 1
  unfold netExponent
  have hmod : χ ^ ((c + 5 * d) % 6) = χ ^ (c + 5 * d) := by
    conv_rhs => rw [← Nat.mod_add_div (c + 5 * d) 6, pow_add, pow_mul, h6, one_pow, mul_one]
  rw [hmod, pow_add, pow_mul, h5, inv_pow]

def activeSupport {ι : Type*} (B : Finset ι) (c d : ι → ℕ) : Finset ι :=
  B.filter (fun i => netExponent (c i) (d i) ≠ 0)

def principalSupport {ι : Type*} (B : Finset ι) (c d : ι → ℕ) : Finset ι :=
  B.filter (fun i => netExponent (c i) (d i) = 0)

theorem netExponent_ne_zero {ι : Type*} (B : Finset ι) (c d : ι → ℕ)
    (i : activeSupport B c d) : netExponent (c i.val) (d i.val) ≠ 0 :=
  (Finset.mem_filter.mp i.property).2

theorem netExponent_lt_six (c d : ℕ) : netExponent c d < 6 := Nat.mod_lt _ (by decide)

/-- openai `CanonicalRowCompletion.rowCoprimeMask`: `0` if `z` lies in one of the primes. -/
def rowCoprimeMask {ι : Type*} (P : ι → Ideal (𝓞 K)) (B : Finset ι) (z : 𝓞 K) : ℂ :=
  if ∃ i ∈ B, z ∈ P i then 0 else 1

theorem principal_product_eq_mask {ι : Type*}
    (P : ι → Ideal (𝓞 K)) [∀ i, (P i).IsMaximal] (B : Finset ι) (z : 𝓞 K) :
    (∏ i ∈ B, (1 : MulChar (𝓞 K ⧸ P i) ℂ) (Ideal.Quotient.mk (P i) z)) =
      rowCoprimeMask P B z := by
  by_cases h : ∃ i ∈ B, z ∈ P i
  · simp only [rowCoprimeMask, h, ite_true]
    obtain ⟨i, hi, hz⟩ := h
    apply Finset.prod_eq_zero hi
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, MulChar.map_zero]
  · simp only [rowCoprimeMask, h, ite_false]
    apply Finset.prod_eq_one
    intro i hi
    apply MulChar.one_apply
    let : Field (𝓞 K ⧸ P i) := Ideal.Quotient.field (P i)
    apply isUnit_iff_ne_zero.mpr
    exact fun hz => h ⟨i, hi, Ideal.Quotient.eq_zero_iff_mem.mp hz⟩

variable {ι : Type*}

/-- openai `common_ideal_pair_active`; `hrow` is the multiplicativity
`idealRowHom z (∏ P i ^ c i) = ∏ (χ i ^ c i) z`. -/
theorem common_ideal_pair_active (P : ι → Ideal (𝓞 K)) [∀ i, (P i).IsMaximal]
    [∀ i, Finite (𝓞 K ⧸ P i)]
    (χ : ∀ i, MulChar (𝓞 K ⧸ P i) ℂ) (h6 : ∀ i, χ i ^ 6 = 1)
    (B : Finset ι) (c d : ι → ℕ) (rowC rowD : 𝓞 K → ℂ)
    (hrowC : ∀ z, rowC z = ∏ i ∈ B, (χ i ^ c i) (Ideal.Quotient.mk (P i) z))
    (hrowD : ∀ z, rowD z = ∏ i ∈ B, (χ i ^ d i) (Ideal.Quotient.mk (P i) z)) (z : 𝓞 K) :
    rowC z * star (rowD z) =
      rowCoprimeMask P (principalSupport B c d) z *
        ∏ i : activeSupport B c d,
          (χ i.val ^ netExponent (c i.val) (d i.val)) (Ideal.Quotient.mk (P i.val) z) := by
  let f := fun i => (χ i ^ netExponent (c i) (d i)) (Ideal.Quotient.mk (P i) z)
  have hlocal : rowC z * star (rowD z) = ∏ i ∈ B, f i := by
    rw [hrowC, hrowD, star_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    exact local_pair_reduction (χ i) (h6 i) (c i) (d i) _
  have hzero : (∏ i ∈ B.filter (fun i => netExponent (c i) (d i) = 0), f i) =
      rowCoprimeMask P (principalSupport B c d) z := by
    rw [← principal_product_eq_mask]
    apply Finset.prod_congr rfl
    intro i hi
    have he := (Finset.mem_filter.mp hi).2
    simp only [f, he, pow_zero]
  rw [hlocal, ← Finset.prod_filter_mul_prod_filter_not B
    (fun i => netExponent (c i) (d i) = 0) f, hzero]
  congr 1
  exact (Finset.prod_coe_sort (s := activeSupport B c d) (f := f)).symm

theorem activePrimes_pairwise_coprime (P : ι → Ideal (𝓞 K)) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (B : Finset ι) (c d : ι → ℕ) :
    Pairwise (Function.onFun IsCoprime (fun i : activeSupport B c d => P i.val)) := by
  intro i j hij
  apply Ideal.isCoprime_of_isMaximal
  exact fun he => hij (Subtype.ext (hinj he))

end HeckePort.Moments.Active

end
