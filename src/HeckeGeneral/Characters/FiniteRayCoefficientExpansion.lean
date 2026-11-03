import HeckeGeneral.Characters.UnramifiedPrimeCoefficientAlgebra
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
Exact finite-character expansion of the identity-ray condition at a place
where the fixed filtering characters are unramified. Each twist is an
actual Hecke character and is finite order. The background character is
arbitrary, including ramified characters with their original zero values.
There is no analytic moment estimate or assertion about ramified places.

Orders are chosen once before the place and background character; a final
existence theorem makes those choices for any fixed finite-order Finset T.
Repeated resulting characters are retained as repeated summation labels.

-/

noncomputable section
namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]

theorem UnramifiedAt.finset_prod {ι : Type*} (F : Finset ι)
    (χ : ι → HeckeCharacter K) (p : HeightOneSpectrum (𝓞 K))
    (hχ : ∀ i ∈ F, UnramifiedAt K (χ i) p) :
    UnramifiedAt K (∏ i ∈ F, χ i) p := by
  classical
  revert hχ
  induction F using Finset.induction_on with
  | empty =>
    intro _hχ
    simpa only [Finset.prod_empty] using unramifiedAt_one K p
  | @insert i F hi ih =>
    intro hχ
    rw [Finset.prod_insert hi]
    exact (hχ i (Finset.mem_insert_self i F)).mul K
      (ih (fun j hj => hχ j (Finset.mem_insert_of_mem hj)))

theorem finiteOrder_finset_prod {ι : Type*} (F : Finset ι)
    (χ : ι → HeckeCharacter K) (hχ : ∀ i ∈ F, FiniteOrder (χ i)) :
    FiniteOrder (∏ i ∈ F, χ i) := by
  classical
  revert hχ
  induction F using Finset.induction_on with
  | empty =>
    intro _hχ
    simpa only [Finset.prod_empty] using (IsOfFinOrder.one : FiniteOrder (1 : HeckeCharacter K))
  | @insert i F hi ih =>
    intro hχ
    rw [Finset.prod_insert hi]
    exact (hχ i (Finset.mem_insert_self i F)).mul
      (ih (fun j hj => hχ j (Finset.mem_insert_of_mem hj)))

/-- Unlike unconditional Euler-coefficient multiplication, this product
identity keeps the actual local unramified hypotheses on every factor. -/
theorem primeCoefficient_finset_prod_of_unramified {ι : Type*} (F : Finset ι)
    (χ : ι → HeckeCharacter K) (p : HeightOneSpectrum (𝓞 K))
    (hχ : ∀ i ∈ F, UnramifiedAt K (χ i) p) :
    primeCoefficient K (∏ i ∈ F, χ i) p = ∏ i ∈ F, primeCoefficient K (χ i) p := by
  classical
  revert hχ
  induction F using Finset.induction_on with
  | empty =>
    intro _hχ
    simp only [Finset.prod_empty, primeCoefficient_one]
  | @insert i F hi ih =>
    intro hχ
    have hF : ∀ j ∈ F, UnramifiedAt K (χ j) p :=
      fun j hj => hχ j (Finset.mem_insert_of_mem hj)
    simp only [Finset.prod_insert hi]
    rw [primeCoefficient_mul_right_unramified K (χ i) (∏ j ∈ F, χ j) p
      (UnramifiedAt.finset_prod K F χ p hF), ih hF]

/-- A literal finite product in the actual Hecke-character group. -/
def cyclicRayTwist {ι : Type*} [Fintype ι] (χ : ι → HeckeCharacter K)
    (n : ι → ℕ) (e : ∀ i, Fin (n i)) : HeckeCharacter K :=
  ∏ i, χ i ^ (e i).val

theorem cyclicRayTwist_finiteOrder {ι : Type*} [Fintype ι]
    (χ : ι → HeckeCharacter K) (n : ι → ℕ) (e : ∀ i, Fin (n i))
    (hχ : ∀ i, FiniteOrder (χ i)) : FiniteOrder (cyclicRayTwist K χ n e) := by
  apply finiteOrder_finset_prod K Finset.univ (fun i => χ i ^ (e i).val)
  intro i _hi
  exact (hχ i).pow

theorem cyclicRayTwist_unramifiedAt {ι : Type*} [Fintype ι]
    (χ : ι → HeckeCharacter K) (n : ι → ℕ) (e : ∀ i, Fin (n i))
    (p : HeightOneSpectrum (𝓞 K)) (hχ : ∀ i, UnramifiedAt K (χ i) p) :
    UnramifiedAt K (cyclicRayTwist K χ n e) p := by
  apply UnramifiedAt.finset_prod K Finset.univ (fun i => χ i ^ (e i).val) p
  intro i _hi
  exact (hχ i).pow K (e i).val

theorem primeCoefficient_cyclicRayTwist {ι : Type*} [Fintype ι]
    (χ : ι → HeckeCharacter K) (n : ι → ℕ) (e : ∀ i, Fin (n i))
    (p : HeightOneSpectrum (𝓞 K)) (hχ : ∀ i, UnramifiedAt K (χ i) p) :
    primeCoefficient K (cyclicRayTwist K χ n e) p =
      ∏ i, (primeCoefficient K (χ i) p) ^ (e i).val := by
  unfold cyclicRayTwist
  rw [primeCoefficient_finset_prod_of_unramified K Finset.univ
    (fun i => χ i ^ (e i).val) p (fun i _ => (hχ i).pow K (e i).val)]
  apply Finset.prod_congr rfl
  intro i _hi
  exact primeCoefficient_pow_of_unramified K (χ i) p (hχ i) (e i).val

/-- The arbitrary background may be ramified; the right twist is known
unramified, so the true zero extension is preserved. -/
theorem primeCoefficient_mul_cyclicRayTwist {ι : Type*} [Fintype ι]
    (ψ : HeckeCharacter K) (χ : ι → HeckeCharacter K) (n : ι → ℕ)
    (e : ∀ i, Fin (n i)) (p : HeightOneSpectrum (𝓞 K))
    (hχ : ∀ i, UnramifiedAt K (χ i) p) :
    primeCoefficient K (ψ * cyclicRayTwist K χ n e) p =
      primeCoefficient K ψ p * ∏ i, (primeCoefficient K (χ i) p) ^ (e i).val := by
  rw [primeCoefficient_mul_right_unramified K ψ (cyclicRayTwist K χ n e) p
    (cyclicRayTwist_unramifiedAt K χ n e p hχ),
    primeCoefficient_cyclicRayTwist K χ n e p hχ]

theorem cyclicRayDenominator_ne_zero {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (hn : ∀ i, 0 < n i) : (∏ i, (n i : ℂ)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _hi
  exact Nat.cast_ne_zero.mpr (hn i).ne'

/-- The order need only annihilate chi; it need not be its exact order. -/
theorem cyclicPrimePowerAverage {n : ℕ} (χ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) (hχ : UnramifiedAt K χ p)
    (hn : 0 < n) (horder : χ ^ n = 1) :
    (∑ j : Fin n, (primeCoefficient K χ p) ^ j.val) / (n : ℂ) =
      (if primeCoefficient K χ p = 1 then 1 else 0) := by
  rw [Fin.sum_univ_eq_sum_range]
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hz : (primeCoefficient K χ p) ^ n = 1 :=
    primeCoefficient_pow_eq_one_of_unramified K χ p hχ horder
  by_cases hq : primeCoefficient K χ p = 1
  · simp [hq, hnC]
  · rw [geom_sum_eq hq n, hz, sub_self, zero_div, zero_div, if_neg hq]

/-- Finite character expansion of the identity ray at one place. Orders
and the entire twist-label set are fixed before psi and p. The background
psi is arbitrary; no false unconditional coefficient multiplication is used. -/
theorem finiteRayCoefficientExpansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (χ : ι → HeckeCharacter K) (n : ι → ℕ)
    (hn : ∀ i, 0 < n i) (horder : ∀ i, χ i ^ n i = 1)
    (ψ : HeckeCharacter K) (p : HeightOneSpectrum (𝓞 K))
    (hχ : ∀ i, UnramifiedAt K (χ i) p) :
    (∑ e : ∀ i, Fin (n i), primeCoefficient K (ψ * cyclicRayTwist K χ n e) p) /
        (∏ i, (n i : ℂ)) =
      primeCoefficient K ψ p * (if ∀ i, primeCoefficient K (χ i) p = 1 then 1 else 0) := by
  classical
  have hsum :
      (∑ e : ∀ i, Fin (n i), primeCoefficient K (ψ * cyclicRayTwist K χ n e) p) =
        primeCoefficient K ψ p * ∏ i, ∑ j : Fin (n i), (primeCoefficient K (χ i) p) ^ j.val := by
    calc
      _ = ∑ e : ∀ i, Fin (n i),
          primeCoefficient K ψ p * ∏ i, (primeCoefficient K (χ i) p) ^ (e i).val := by
        apply Finset.sum_congr rfl
        intro e _he
        exact primeCoefficient_mul_cyclicRayTwist K ψ χ n e p hχ
      _ = primeCoefficient K ψ p *
          ∑ e : ∀ i, Fin (n i), ∏ i, (primeCoefficient K (χ i) p) ^ (e i).val := by
        rw [Finset.mul_sum]
      _ = primeCoefficient K ψ p *
          ∏ i, ∑ j : Fin (n i), (primeCoefficient K (χ i) p) ^ j.val := by
        rw [Fintype.prod_sum]
  calc
    _ = (primeCoefficient K ψ p *
        ∏ i, ∑ j : Fin (n i), (primeCoefficient K (χ i) p) ^ j.val) /
          (∏ i, (n i : ℂ)) := by rw [hsum]
    _ = primeCoefficient K ψ p *
        ∏ i, ((∑ j : Fin (n i), (primeCoefficient K (χ i) p) ^ j.val) / (n i : ℂ)) := by
      rw [Finset.prod_div_distrib]
      ring
    _ = primeCoefficient K ψ p *
        ∏ i, (if primeCoefficient K (χ i) p = 1 then (1 : ℂ) else 0) := by
      congr 1
      apply Finset.prod_congr rfl
      intro i _hi
      exact cyclicPrimePowerAverage K (χ i) p (hχ i) (hn i) (horder i)
    _ = primeCoefficient K ψ p *
        (if ∀ i, primeCoefficient K (χ i) p = 1 then 1 else 0) := by
      simp only [Finset.prod_boole, Finset.mem_univ, forall_const]

/-- Every fixed finite family of finite-order actual Hecke characters
admits one choice of positive annihilating orders before psi and p. The
formula uses precisely the original all-characters identity-ray predicate. -/
theorem finiteRayCoefficientExpansion_of_finiteOrder
    (T : Finset (HeckeCharacter K)) (hT : ∀ χ ∈ T, FiniteOrder χ) :
    ∃ n : T → ℕ, (∀ χ : T, 0 < n χ) ∧ (∀ χ : T, χ.val ^ n χ = 1) ∧
      (∀ e : ∀ χ : T, Fin (n χ),
        FiniteOrder (cyclicRayTwist K (fun χ : T => χ.val) n e)) ∧
      ∀ (ψ : HeckeCharacter K) (p : HeightOneSpectrum (𝓞 K)),
        (∀ χ ∈ T, UnramifiedAt K χ p) →
        (∑ e : ∀ χ : T, Fin (n χ),
          primeCoefficient K (ψ * cyclicRayTwist K (fun χ : T => χ.val) n e) p) /
            (∏ χ : T, (n χ : ℂ)) =
          primeCoefficient K ψ p * (if ∀ χ ∈ T, primeCoefficient K χ p = 1 then 1 else 0) := by
  classical
  have hex : ∀ χ : T, ∃ m : ℕ, 0 < m ∧ χ.val ^ m = 1 :=
    fun χ => (finiteOrder_iff χ.val).mp (hT χ.val χ.property)
  choose n hn horder using hex
  refine ⟨n, hn, horder, ?_, ?_⟩
  · intro e
    exact cyclicRayTwist_finiteOrder K (fun χ : T => χ.val) n e
      (fun χ => hT χ.val χ.property)
  · intro ψ p hU
    have hiff : (∀ χ : T, primeCoefficient K χ.val p = 1) ↔
        ∀ χ ∈ T, primeCoefficient K χ p = 1 := by
      constructor
      · intro h χ hχ
        exact h ⟨χ, hχ⟩
      · intro h χ
        exact h χ.val χ.property
    simpa only [hiff] using
      finiteRayCoefficientExpansion K (fun χ : T => χ.val) n hn horder ψ p
        (fun χ => hU χ.val χ.property)

end HeckeGeneral.Characters
