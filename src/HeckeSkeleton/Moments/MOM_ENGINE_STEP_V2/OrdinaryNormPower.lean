module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralLocations
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The two original tilts on individual norm-profile occurrences

The complete ideal norm is the product of the same two plain norms and
every original prime occurrence. Its real power therefore factors into
the original scale product and the normalized single-occurrence powers.
The calculation includes an empty slot product and repeated primes.
Only the positive original scales are cancelled.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryNormPower

open HeckeSkeleton.Moments.EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis

variable {K : Type} [Field K] [NumberField K]

theorem product_rpow {ι : Type*} (s : Finset ι) (f : ι → ℝ) (e : ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∏ i ∈ s, f i) ^ e = ∏ i ∈ s, (f i) ^ e := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.prod_empty, Real.one_rpow]
  | @insert i s hi ih =>
    intro hf
    have hs : ∀ j ∈ s, 0 ≤ f j :=
      fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      Real.mul_rpow (hf i (Finset.mem_insert_self _ _)) (Finset.prod_nonneg hs),
      ih hs]

theorem scale_normalized_rpow (N a e : ℝ) (hN : 0 < N) (ha : 0 ≤ a) :
    N ^ e * (a / N) ^ e = a ^ e := by
  have hcancel : N * (a / N) = a := by field_simp [hN.ne']
  rw [← Real.mul_rpow hN.le (div_nonneg ha hN.le), hcancel]

/-- The scale contribution is factored once, before the two original
rectangles are subtracted. -/
theorem normalized_product {ι : Type*} [Fintype ι]
    (N₁ N₂ a₁ a₂ : ℝ) (N a : ι → ℝ) (e : ℝ)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hN : ∀ i, 0 < N i)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha : ∀ i, 0 ≤ a i) :
    (N₁ * N₂ * ∏ i, N i) ^ e *
        ((a₁ / N₁) ^ e * (a₂ / N₂) ^ e * ∏ i, (a i / N i) ^ e) =
      (a₁ * a₂ * ∏ i, a i) ^ e := by
  have hNP : 0 ≤ ∏ i, N i := Finset.prod_nonneg (fun i _ => (hN i).le)
  have haP : 0 ≤ ∏ i, a i := Finset.prod_nonneg (fun i _ => ha i)
  rw [Real.mul_rpow (mul_nonneg hN₁.le hN₂.le) hNP,
    Real.mul_rpow hN₁.le hN₂.le,
    product_rpow Finset.univ N e (fun i _ => (hN i).le)]
  calc
    (N₁ ^ e * N₂ ^ e * ∏ i, (N i) ^ e) *
        ((a₁ / N₁) ^ e * (a₂ / N₂) ^ e * ∏ i, (a i / N i) ^ e) =
        (N₁ ^ e * (a₁ / N₁) ^ e) * (N₂ ^ e * (a₂ / N₂) ^ e) *
          ∏ i, ((N i) ^ e * (a i / N i) ^ e) := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = a₁ ^ e * a₂ ^ e * ∏ i, (a i) ^ e := by
      rw [scale_normalized_rpow N₁ a₁ e hN₁ ha₁,
        scale_normalized_rpow N₂ a₂ e hN₂ ha₂]
      congr 1
      exact Finset.prod_congr rfl (fun i _ =>
        scale_normalized_rpow (N i) (a i) e (hN i) (ha i))
    _ = (a₁ * a₂ * ∏ i, a i) ^ e := by
      rw [Real.mul_rpow (mul_nonneg ha₁ ha₂) haP,
        Real.mul_rpow ha₁ ha₂, product_rpow Finset.univ a e (fun i _ => ha i)]

theorem allocation_norm {k : ℕ} (i : AllocationColumn K k) :
    (Ideal.absNorm (allocationColumnIdeal i) : ℝ) =
      (Ideal.absNorm i.1.1 : ℝ) * (Ideal.absNorm i.1.2 : ℝ) *
        ∏ j, (Ideal.absNorm (i.2 j).asIdeal : ℝ) := by
  simp only [allocationColumnIdeal, map_mul, map_prod, Nat.cast_mul, Nat.cast_prod]

/-- The actual whole ideal norm, including every original prime
occurrence, is recovered from the individual normalized profile powers. -/
theorem allocation_normalized_product {k : ℕ} (i : AllocationColumn K k)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ) (e : ℝ)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hZ : 0 < Z) :
    (N₁ * N₂ * ∏ j, Z ^ length j) ^ e *
        (((Ideal.absNorm i.1.1 : ℝ) / N₁) ^ e *
          ((Ideal.absNorm i.1.2 : ℝ) / N₂) ^ e *
          ∏ j, ((Ideal.absNorm (i.2 j).asIdeal : ℝ) / Z ^ length j) ^ e) =
      (Ideal.absNorm (allocationColumnIdeal i) : ℝ) ^ e := by
  rw [allocation_norm]
  exact normalized_product N₁ N₂ _ _ (fun j => Z ^ length j) _ e hN₁ hN₂
    (fun j => Real.rpow_pos_of_pos hZ (length j))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _)

theorem allocation_normalized_product_complex {k : ℕ} (i : AllocationColumn K k)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ) (e : ℝ)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hZ : 0 < Z) :
    (((N₁ * N₂ * ∏ j, Z ^ length j) ^ e : ℝ) : ℂ) *
        (((((Ideal.absNorm i.1.1 : ℝ) / N₁) ^ e : ℝ) : ℂ) *
          ((((Ideal.absNorm i.1.2 : ℝ) / N₂) ^ e : ℝ) : ℂ) *
          ∏ j, ((((Ideal.absNorm (i.2 j).asIdeal : ℝ) / Z ^ length j) ^ e : ℝ) : ℂ)) =
      (((Ideal.absNorm (allocationColumnIdeal i) : ℝ) ^ e : ℝ) : ℂ) := by
  exact_mod_cast allocation_normalized_product i N₁ N₂ Z length e hN₁ hN₂ hZ

theorem two_tilts (N t : ℝ) (hN : 0 < N) :
    N ^ (-1 + 2 * t) = N ^ t / N * N ^ t := by
  rw [show -1 + 2 * t = (t - 1) + t by ring,
    Real.rpow_add hN, Real.rpow_sub hN, Real.rpow_one]

theorem two_tilts_complex (N t : ℝ) (hN : 0 < N) :
    ((N ^ (-1 + 2 * t) : ℝ) : ℂ) =
      ((N ^ t : ℝ) : ℂ) / (N : ℂ) * ((N ^ t : ℝ) : ℂ) := by
  rw [two_tilts N t hN, Complex.ofReal_mul, Complex.ofReal_div]

/-- Multiplicativity keeps the actual pool norm factor visible. -/
theorem ideal_norm_rpow_mul (I J : Ideal (𝓞 K)) (e : ℝ) :
    (Ideal.absNorm (I * J) : ℝ) ^ e =
      (Ideal.absNorm I : ℝ) ^ e * (Ideal.absNorm J : ℝ) ^ e := by
  rw [map_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryNormPower

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryNormPower.allocation_normalized_product
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryNormPower.allocation_normalized_product_complex
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryNormPower.two_tilts_complex
