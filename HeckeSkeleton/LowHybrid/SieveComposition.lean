import Mathlib.Analysis.Complex.Basic
import HeckeSkeleton.LowHybrid.CommonTactics

/-!
# Finite quadratic--cubic sieve composition

All theorems in this file are proved for arbitrary finite index sets. The
quadratic and cubic hypotheses are operator bounds for arbitrary coefficients,
not assumptions of the hybrid conclusion. The two product maps and their fiber
multiplicities remain visible. An arithmetic instantiation still needs the
actual `ExteriorIdeal` symbol, factorization and counting lemmas.

The shape of `positive_triple_enlarge` and `column_fiber_sieve` follows the
Apache-2.0-licensed OpenAI math source, commit fd4aeeb2,
`lean/OAI/NumberTheory/DirichletL/Descent/SieveComposition.lean`.
Here the elementary finite-energy proof is included, all sets are finite, and
the fixed-block theorem exposes both fiber losses explicitly.
-/

namespace HeckeSkeleton.LowHybrid

open scoped BigOperators

noncomputable section

/-- Cauchy--Schwarz on precisely the specified coefficient set. -/
theorem bounded_coefficient_sum_sq {I : Type*} (s : Finset I)
    (b f : I → ℂ) (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) :
    ‖∑ i ∈ s, b i * f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have hnorm : ‖∑ i ∈ s, b i * f i‖ ≤ ∑ i ∈ s, ‖f i‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_right (hb i hi) (norm_nonneg (f i))
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖f i‖)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  exact hsq.trans (by simpa using hc)

/-- Version of Cauchy with a specified upper bound for the number of terms. -/
theorem bounded_coefficient_sum_sq_of_card {I : Type*} (s : Finset I)
    (b f : I → ℂ) (D : ℝ) (hb : ∀ i ∈ s, ‖b i‖ ≤ 1)
    (hcard : (s.card : ℝ) ≤ D) :
    ‖∑ i ∈ s, b i * f i‖ ^ 2 ≤ D * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  exact (bounded_coefficient_sum_sq s b f hb).trans
    (mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-- A positive sum may be regrouped through a map with bounded fibers.
This is applied to `(c',m) ↦ c'm`, after the Cauchy step. -/
theorem positive_fiber_sum_le {X Y : Type*} [DecidableEq Y]
    (source : Finset X) (target : Finset Y) (phi : X → Y)
    (E : Y → ℝ) (D : ℝ)
    (hmap : ∀ x ∈ source, phi x ∈ target)
    (hE : ∀ y ∈ target, 0 ≤ E y)
    (hfiber : ∀ y ∈ target, ((source.filter fun x => phi x = y).card : ℝ) ≤ D) :
    (∑ x ∈ source, E (phi x)) ≤ D * ∑ y ∈ target, E y := by
  classical
  calc
    _ = ∑ y ∈ target, ∑ x ∈ source with phi x = y, E (phi x) :=
      (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ = ∑ y ∈ target, ((source.filter fun x => phi x = y).card : ℝ) * E y := by
      apply Finset.sum_congr rfl
      intro y hy
      calc
        _ = ∑ _x ∈ source with phi _x = y, E y := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
        _ = _ := by simp
    _ ≤ ∑ y ∈ target, D * E y := by
      exact Finset.sum_le_sum fun y hy =>
        mul_le_mul_of_nonneg_right (hfiber y hy) (hE y hy)
    _ = _ := (Finset.mul_sum ..).symm

/-- Collision of product columns costs their actual fiber multiplicity.
The coefficient remains inside each fiber until this Cauchy step. -/
theorem column_fiber_sieve {K X Y : Type*} [DecidableEq Y]
    (rows : Finset K) (source : Finset X) (target : Finset Y)
    (phi : X → Y) (q : K → Y → ℂ) (a : X → ℂ) (Q D : ℝ)
    (hQ : 0 ≤ Q) (hmap : ∀ x ∈ source, phi x ∈ target)
    (hfiber : ∀ y ∈ target, ((source.filter fun x => phi x = y).card : ℝ) ≤ D)
    (hsieve : ∀ f : Y → ℂ,
      (∑ k ∈ rows, ‖∑ y ∈ target, q k y * f y‖ ^ 2) ≤
        Q * ∑ y ∈ target, ‖f y‖ ^ 2) :
    (∑ k ∈ rows, ‖∑ x ∈ source, q k (phi x) * a x‖ ^ 2) ≤
      Q * D * ∑ x ∈ source, ‖a x‖ ^ 2 := by
  classical
  let f : Y → ℂ := fun y => ∑ x ∈ source with phi x = y, a x
  have he (k : K) : (∑ x ∈ source, q k (phi x) * a x) =
      ∑ y ∈ target, q k y * f y := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    apply Finset.sum_congr rfl
    intro y hy
    dsimp only [f]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  have hf : (∑ y ∈ target, ‖f y‖ ^ 2) ≤ D * ∑ x ∈ source, ‖a x‖ ^ 2 := by
    calc
      _ ≤ ∑ y ∈ target, D * ∑ x ∈ source with phi x = y, ‖a x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro y hy
        simpa only [one_mul, f] using
          bounded_coefficient_sum_sq_of_card
            (source.filter fun x => phi x = y) (fun _ => 1) a D
            (by simp) (hfiber y hy)
      _ = D * ∑ x ∈ source, ‖a x‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to hmap]
  simp_rw [he]
  exact (hsieve f).trans (by
    calc
      _ ≤ Q * (D * ∑ x ∈ source, ‖a x‖ ^ 2) := mul_le_mul_of_nonneg_left hf hQ
      _ = _ := by ring)

/-- Extend only a positive sum. Restrictions coupling `m`, `h`, and `c`
are not moved into a cubic-sieve coefficient. -/
theorem positive_triple_enlarge {M H C : Type*}
    [DecidableEq M] [DecidableEq H] [DecidableEq C]
    (pairs : Finset (M × H)) (cset : M → Finset C)
    (hs : Finset H) (mc : Finset (M × C)) (E : H → M → C → ℝ)
    (hh : ∀ p ∈ pairs, p.2 ∈ hs)
    (hm : ∀ p ∈ pairs, ∀ c ∈ cset p.1, (p.1, c) ∈ mc)
    (hE : ∀ h m c, 0 ≤ E h m c) :
    (∑ p ∈ pairs, ∑ c ∈ cset p.1, E p.2 p.1 c) ≤
      ∑ h ∈ hs, ∑ u ∈ mc, E h u.1 u.2 := by
  let f : (Σ _p : M × H, C) → H × (M × C) := fun p => (p.1.2, (p.1.1, p.2))
  have hf : Function.Injective f := by
    have hi : Function.LeftInverse
        (fun u : H × (M × C) => (⟨(u.2.1, u.1), u.2.2⟩ : Σ _p : M × H, C)) f := by
      rintro ⟨⟨m, h⟩, c⟩
      rfl
    exact hi.injective
  have hmapped : ((pairs.sigma (fun p => cset p.1)).image f) ⊆ hs ×ˢ mc := by
    intro u hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
    have hp' := Finset.mem_sigma.mp hp
    exact Finset.mem_product.mpr ⟨hh p.1 hp'.1, hm p.1 hp'.1 p.2 hp'.2⟩
  have hb := Finset.sum_le_sum_of_injOn f hf.injOn hmapped
    (f := fun p : Σ _p : M × H, C => E p.1.2 p.1.1 p.2)
    (g := fun u : H × (M × C) => E u.1 u.2.1 u.2.2)
    (by intros; exact le_rfl) (by intro u _ _; exact hE _ _ _)
  simpa only [Finset.sum_sigma, Finset.sum_product] using hb

/-- Pull a cubic row family back through its product map, after squares
have been taken. Only one fiber multiplicity occurs. -/
theorem row_fiber_sieve {X Y P : Type*} [DecidableEq Y]
    (source : Finset X) (target : Finset Y) (columns : Finset P)
    (phi : X → Y) (chi : P → Y → ℂ) (a : P → ℂ) (D S : ℝ)
    (hD : 0 ≤ D) (hmap : ∀ x ∈ source, phi x ∈ target)
    (hfiber : ∀ y ∈ target, ((source.filter fun x => phi x = y).card : ℝ) ≤ D)
    (hsieve : ∀ u : P → ℂ,
      (∑ y ∈ target, ‖∑ p ∈ columns, u p * chi p y‖ ^ 2) ≤
        S * ∑ p ∈ columns, ‖u p‖ ^ 2) :
    (∑ x ∈ source, ‖∑ p ∈ columns, a p * chi p (phi x)‖ ^ 2) ≤
      D * S * ∑ p ∈ columns, ‖a p‖ ^ 2 := by
  apply (positive_fiber_sum_le source target phi
    (fun y => ‖∑ p ∈ columns, a p * chi p y‖ ^ 2) D
    hmap (fun _ _ => sq_nonneg _) hfiber).trans
  calc
    _ ≤ D * (S * ∑ p ∈ columns, ‖a p‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hsieve a) hD
    _ = _ := by ring

/-- The fixed-block quadratic--cubic composition. `q` is already indexed by
the squarefree product `(m,h)`; its product-fiber reduction is supplied by
`column_fiber_sieve`. `phi (m,c)` is the cubic product `c*m`.

The coefficient `a h p` is independent of `m,c,k`. The coefficient `beta`
is independent of `p,k`. Those independences are enforced by the types.
The only Cauchy factor here is `Cbound`, before the cubic sieve is applied.
-/
theorem fixed_block_energy_of_two_sieves
    {K M H C J P : Type*}
    [DecidableEq M] [DecidableEq H] [DecidableEq C] [DecidableEq J]
    (rows : Finset K) (pairs : Finset (M × H))
    (cset : M → Finset C) (hset : Finset H) (mc : Finset (M × C))
    (jset : Finset J) (pset : Finset P)
    (q : K → M × H → ℂ) (phi : M × C → J) (chi : P → J → ℂ)
    (a : H → P → ℂ) (beta : C → M → H → ℂ)
    (Q S Cbound D Ebound : ℝ)
    (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hC : 0 ≤ Cbound) (hD : 0 ≤ D)
    (hcount : ∀ p ∈ pairs, ((cset p.1).card : ℝ) ≤ Cbound)
    (hbeta : ∀ p ∈ pairs, ∀ c ∈ cset p.1, ‖beta c p.1 p.2‖ ≤ 1)
    (hh : ∀ p ∈ pairs, p.2 ∈ hset)
    (hmc : ∀ p ∈ pairs, ∀ c ∈ cset p.1, (p.1, c) ∈ mc)
    (hmap : ∀ u ∈ mc, phi u ∈ jset)
    (hfiber : ∀ j ∈ jset, ((mc.filter fun u => phi u = j).card : ℝ) ≤ D)
    (hcoef : ∀ h ∈ hset, (∑ p ∈ pset, ‖a h p‖ ^ 2) ≤ Ebound)
    (hquadratic : ∀ f : M × H → ℂ,
      (∑ k ∈ rows, ‖∑ u ∈ pairs, q k u * f u‖ ^ 2) ≤
        Q * ∑ u ∈ pairs, ‖f u‖ ^ 2)
    (hcubic : ∀ u : P → ℂ,
      (∑ j ∈ jset, ‖∑ p ∈ pset, u p * chi p j‖ ^ 2) ≤
        S * ∑ p ∈ pset, ‖u p‖ ^ 2) :
    (∑ k ∈ rows, ‖∑ u ∈ pairs, q k u *
      (∑ c ∈ cset u.1, beta c u.1 u.2 *
        (∑ p ∈ pset, a u.2 p * chi p (phi (u.1, c))))‖ ^ 2) ≤
      Q * Cbound * (hset.card : ℝ) * D * S * Ebound := by
  classical
  let E (h : H) (m : M) (c : C) : ℝ :=
    ‖∑ p ∈ pset, a h p * chi p (phi (m, c))‖ ^ 2
  have hlocal (u : M × H) (hu : u ∈ pairs) :
      ‖∑ c ∈ cset u.1, beta c u.1 u.2 *
        (∑ p ∈ pset, a u.2 p * chi p (phi (u.1, c)))‖ ^ 2 ≤
        Cbound * ∑ c ∈ cset u.1, E u.2 u.1 c := by
    exact bounded_coefficient_sum_sq_of_card (cset u.1)
      (fun c => beta c u.1 u.2)
      (fun c => ∑ p ∈ pset, a u.2 p * chi p (phi (u.1, c)))
      Cbound (hbeta u hu) (hcount u hu)
  have hpositive := positive_triple_enlarge pairs cset hset mc E hh hmc
    (fun _ _ _ => sq_nonneg _)
  have htotal : (∑ u ∈ pairs, ∑ c ∈ cset u.1, E u.2 u.1 c) ≤
      (hset.card : ℝ) * (D * S * Ebound) := by
    apply hpositive.trans
    calc
      _ ≤ ∑ _h ∈ hset, D * S * Ebound := by
        apply Finset.sum_le_sum
        intro h hmem
        apply (row_fiber_sieve mc jset pset phi chi (a h) D S
          hD hmap hfiber hcubic).trans
        exact mul_le_mul_of_nonneg_left (hcoef h hmem) (mul_nonneg hD hS)
      _ = _ := by simp
  apply (hquadratic (fun u => ∑ c ∈ cset u.1, beta c u.1 u.2 *
    (∑ p ∈ pset, a u.2 p * chi p (phi (u.1, c))))).trans
  calc
    _ ≤ Q * ∑ u ∈ pairs, Cbound * ∑ c ∈ cset u.1, E u.2 u.1 c :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hlocal) hQ
    _ = Q * Cbound * (∑ u ∈ pairs, ∑ c ∈ cset u.1, E u.2 u.1 c) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ Q * Cbound * ((hset.card : ℝ) * (D * S * Ebound)) :=
      mul_le_mul_of_nonneg_left htotal (mul_nonneg hQ hC)
    _ = _ := by ring

/-- An explicit scalar version of the quadratic and cubic composition.
The product `T²*G = B` is the full-cube counting relation. -/
theorem fixed_block_scalar_ledger (T G C r B Q S A : ℝ)
    (hC : C ≠ 0) (hr : r ≠ 0) (hB : T ^ 2 * G = B) :
    T ^ 2 * Q * (C / r) * (G / C) * S * A =
      Q * (B / r) * S * A := by
  rw [← hB]
  field_simp
  <;> ring

#print axioms bounded_coefficient_sum_sq
#print axioms positive_fiber_sum_le
#print axioms column_fiber_sieve
#print axioms positive_triple_enlarge
#print axioms row_fiber_sieve
#print axioms fixed_block_energy_of_two_sieves
#print axioms fixed_block_scalar_ledger

end
end HeckeSkeleton.LowHybrid
