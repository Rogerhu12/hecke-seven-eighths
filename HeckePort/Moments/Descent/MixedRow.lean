import HeckePort.Moments.Descent.MarkedFourier
import HeckePort.Moments.Descent.LocalReflection

/-!
# Mixed prime functions

Port of the arithmetic part of openai/math `OAI/NumberTheory/DirichletL/Descent/MixedRow.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

The principal primes `Ideal.span {p i}` of openai are prime ideals `P i` of `𝓞 K`, and the
sextic residue character `actualSextic (span {p i}) (hg i)` is an arbitrary multiplicative
character `χ i : MulChar (𝓞 K ⧸ P i) ℂ` (over a general field: the sextic character of the
residue field; `HeckeGeneral.Characters`).  The bound `‖(χ i ^ j i) x‖ ≤ 1`
(`FiniteRayExpansion.norm_char_le_one`) is the hypothesis `hχ`.

Ported: `unmarkedTwist` (= `unmarkedSexticTwist`), `mixedPrimeFunction`, the norm bound, the
periodicity modulo `∏ P i` (stated as: it factors through the residue maps), and
`mixedPrimeFunction_product`.  Not ported: `markedThetaQuotient_mk` (a statement about the
cubic theta quotient `fixedThetaQuotient`).
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators

variable {K : Type*} [Field K] [NumberField K] {ι : Type*}

/-- openai `unmarkedSexticTwist`. -/
def unmarkedTwist (P : ι → Ideal (𝓞 K)) (χ : ∀ i, MulChar (𝓞 K ⧸ P i) ℂ) (j : ι → ℕ)
    (S : Finset ι) [Fintype ι] : 𝓞 K →* ℂ where
  toFun n := ∏ i ∈ (Finset.univ : Finset ι) \ S, (χ i ^ j i) (Ideal.Quotient.mk (P i) n)
  map_one' := by simp
  map_mul' x y := by simp only [map_mul, Finset.prod_mul_distrib]

/-- openai `mixedPrimeFunction`: the zero mark at the slots in `S`, the power of the
character elsewhere. -/
def mixedPrimeFunction (P : ι → Ideal (𝓞 K)) (χ : ∀ i, MulChar (𝓞 K ⧸ P i) ℂ) (j : ι → ℕ)
    (S : Finset ι) (i : ι) (x : 𝓞 K ⧸ P i) : ℂ :=
  if i ∈ S then (if x = 0 then 1 else 0) else (χ i ^ j i) x

theorem unmarkedTwist_norm [Fintype ι] (P : ι → Ideal (𝓞 K)) (χ : ∀ i, MulChar (𝓞 K ⧸ P i) ℂ)
    (j : ι → ℕ) (S : Finset ι) (hχ : ∀ i x, ‖(χ i ^ j i) x‖ ≤ 1) (n : 𝓞 K) :
    ‖unmarkedTwist P χ j S n‖ ≤ 1 := by
  change ‖∏ i ∈ (Finset.univ : Finset ι) \ S, (χ i ^ j i) (Ideal.Quotient.mk (P i) n)‖ ≤ 1
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun i hi => norm_nonneg _) (fun i hi => hχ i _)

/-- openai `unmarkedSexticTwist_periodic`: congruent elements modulo `∏ P i` have the same
value (`Q = ∏ P i` is contained in every `P i`). -/
theorem unmarkedTwist_periodic [Fintype ι] (P : ι → Ideal (𝓞 K))
    (χ : ∀ i, MulChar (𝓞 K ⧸ P i) ℂ) (j : ι → ℕ) (S : Finset ι) (x y : 𝓞 K)
    (hxy : x - y ∈ ∏ i, P i) : unmarkedTwist P χ j S x = unmarkedTwist P χ j S y := by
  change (∏ i ∈ (Finset.univ : Finset ι) \ S, _) = ∏ i ∈ (Finset.univ : Finset ι) \ S, _
  apply Finset.prod_congr rfl
  intro i hi
  have he : Ideal.Quotient.mk (P i) x = Ideal.Quotient.mk _ y := by
    apply Ideal.Quotient.eq.mpr
    exact (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ i))) hxy
  rw [he]

theorem mixedPrimeFunction_product [Fintype ι] (P : ι → Ideal (𝓞 K))
    (χ : ∀ i, MulChar (𝓞 K ⧸ P i) ℂ) (j : ι → ℕ) (S : Finset ι) (n : 𝓞 K) :
    (∏ i, mixedPrimeFunction P χ j S i (Ideal.Quotient.mk _ n)) =
      unmarkedTwist P χ j S n * ∏ i ∈ S, if n ∈ P i then (1 : ℂ) else 0 := by
  rw [← Finset.prod_sdiff (Finset.subset_univ S)]
  have hS : (∏ i ∈ S, mixedPrimeFunction P χ j S i (Ideal.Quotient.mk _ n)) =
      ∏ i ∈ S, if n ∈ P i then (1 : ℂ) else 0 := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [mixedPrimeFunction, hi, ite_true, Ideal.Quotient.eq_zero_iff_mem]
  rw [hS]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [mixedPrimeFunction, (Finset.mem_sdiff.mp hi).2, ite_false]

end HeckePort.Moments

end
