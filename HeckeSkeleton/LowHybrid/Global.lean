import HeckeSkeleton.LowHybrid.Assembly
import HeckeSkeleton.LowHybrid.Weighted

/-!
# Global assembly of the weighted hybrid normal form

This module handles the actual outer D,r sums after arithmetic factorization
and the complete Mobius expansions have produced the stated normal form.
Each block carries its two arbitrary-coefficient sieve hypotheses, positive
weights, pointwise support budget, and coefficient mass. Its energy bound is
proved here from those inputs.

The theorem does not assert that arbitrary ExteriorIdeal data already have
this normal form. That arithmetic instantiation remains separate.
-/

namespace HeckeSkeleton.LowHybrid

open scoped BigOperators
noncomputable section

universe u v uD uR

/-- All finite data of one weighted block. The types enforce the two
coefficient independences needed by the cubic step. -/
structure WeightedBlock (I : Type u) where
  T : Type v
  C : Type v
  M : Type v
  H : Type v
  P : Type v
  ts : Finset T
  cs : Finset C
  ms : Finset M
  hs : Finset H
  ps : Finset P
  q : I → M → H → ℂ
  chi : M → C → P → ℂ
  a : T → H → P → ℂ
  beta : T → C → M → H → ℂ
  rowMask : I → T → ℂ
  wt : T → ℝ
  wc : C → ℝ
  wh : H → ℝ

namespace WeightedBlock

variable {I : Type u} (b : WeightedBlock.{u, v} I)

/-- The actual finite row vector, before any norm estimate. -/
def row (i : I) : ℂ :=
  ∑ t ∈ b.ts, ∑ c ∈ b.cs, b.rowMask i t *
    (∑ m ∈ b.ms, ∑ h ∈ b.hs, b.q i m h *
      (b.beta t c m h * (∑ p ∈ b.ps, b.a t h p * b.chi m c p)))

def tHarmonic : ℝ := ∑ t ∈ b.ts, 1 / b.wt t
def cHarmonic : ℝ := ∑ c ∈ b.cs, 1 / b.wc c
def hHarmonic : ℝ := ∑ h ∈ b.hs, 1 / b.wh h

/-- Only the real block inputs are recorded. No block-energy conclusion
is a field. Q and S bound operators for arbitrary coefficients. -/
structure Admissible (rows : Finset I) (Q S Rbudget A : ℝ) : Prop where
  wt_pos : ∀ t ∈ b.ts, 0 < b.wt t
  wc_pos : ∀ c ∈ b.cs, 0 < b.wc c
  wh_pos : ∀ h ∈ b.hs, 0 < b.wh h
  mask : ∀ i ∈ rows, ∀ t ∈ b.ts, ‖b.rowMask i t‖ ≤ 1
  budget : ∀ t ∈ b.ts, ∀ c ∈ b.cs, ∀ m ∈ b.ms, ∀ h ∈ b.hs,
    b.wt t * b.wc c * ‖b.beta t c m h‖ ^ 2 ≤
      Rbudget / (b.wt t * b.wh h)
  column_mass : ∀ t ∈ b.ts, ∀ h ∈ b.hs,
    (∑ p ∈ b.ps, ‖b.a t h p‖ ^ 2) ≤ A
  quadratic : ∀ f : b.M → b.H → ℂ,
    (∑ i ∈ rows, ‖∑ m ∈ b.ms, ∑ h ∈ b.hs, b.q i m h * f m h‖ ^ 2) ≤
      Q * (∑ m ∈ b.ms, ∑ h ∈ b.hs, ‖f m h‖ ^ 2)
  cubic : ∀ f : b.P → ℂ,
    (∑ m ∈ b.ms, ∑ c ∈ b.cs, ‖∑ p ∈ b.ps, f p * b.chi m c p‖ ^ 2) ≤
      S * (∑ p ∈ b.ps, ‖f p‖ ^ 2)

theorem tHarmonic_nonneg (rows : Finset I) (Q S Rbudget A : ℝ)
    (hb : b.Admissible rows Q S Rbudget A) : 0 ≤ b.tHarmonic := by
  unfold tHarmonic
  apply Finset.sum_nonneg
  intro t ht
  exact le_of_lt (one_div_pos.mpr (hb.wt_pos t ht))

theorem cHarmonic_nonneg (rows : Finset I) (Q S Rbudget A : ℝ)
    (hb : b.Admissible rows Q S Rbudget A) : 0 ≤ b.cHarmonic := by
  unfold cHarmonic
  apply Finset.sum_nonneg
  intro c hc
  exact le_of_lt (one_div_pos.mpr (hb.wc_pos c hc))

theorem hHarmonic_nonneg (rows : Finset I) (Q S Rbudget A : ℝ)
    (hb : b.Admissible rows Q S Rbudget A) : 0 ≤ b.hHarmonic := by
  unfold hHarmonic
  apply Finset.sum_nonneg
  intro h hh
  exact le_of_lt (one_div_pos.mpr (hb.wh_pos h hh))

/-- The block energy is derived from its two sieve bounds. -/
theorem energy_le (rows : Finset I) (Q S Rbudget A : ℝ)
    (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hR : 0 ≤ Rbudget) (hA : 0 ≤ A)
    (hb : b.Admissible rows Q S Rbudget A) :
    (∑ i ∈ rows, ‖b.row i‖ ^ 2) ≤
      Q * S * Rbudget * A * b.tHarmonic ^ 2 * b.cHarmonic * b.hHarmonic := by
  simpa only [row, tHarmonic, cHarmonic, hHarmonic] using
    weighted_energy_of_two_sieves
      rows b.ts b.cs b.ms b.hs b.ps b.q b.chi b.a b.beta b.rowMask b.wt b.wc b.wh
      Q S Rbudget A hQ hS hR hA
      hb.wt_pos hb.wc_pos hb.wh_pos hb.mask hb.budget hb.column_mass hb.quadratic hb.cubic

/-- Replace the three actual harmonic sums by common nonnegative bounds. -/
theorem energy_le_uniform_harmonics (rows : Finset I) (Q S Rbudget A Ht Hc Hh : ℝ)
    (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hR : 0 ≤ Rbudget) (hA : 0 ≤ A)
    (hHt : 0 ≤ Ht) (hHc : 0 ≤ Hc) (hHh : 0 ≤ Hh)
    (hb : b.Admissible rows Q S Rbudget A)
    (ht : b.tHarmonic ≤ Ht) (hc : b.cHarmonic ≤ Hc) (hh : b.hHarmonic ≤ Hh) :
    (∑ i ∈ rows, ‖b.row i‖ ^ 2) ≤
      Q * S * Rbudget * A * Ht ^ 2 * Hc * Hh := by
  have ht0 := b.tHarmonic_nonneg rows Q S Rbudget A hb
  have hc0 := b.cHarmonic_nonneg rows Q S Rbudget A hb
  have hbase : 0 ≤ Q * S * Rbudget * A :=
    mul_nonneg (mul_nonneg (mul_nonneg hQ hS) hR) hA
  have htsq : b.tHarmonic ^ 2 ≤ Ht ^ 2 := by
    simpa only [pow_two] using mul_le_mul ht ht ht0 hHt
  apply (b.energy_le rows Q S Rbudget A hQ hS hR hA hb).trans
  calc
    _ ≤ Q * S * Rbudget * A * b.tHarmonic ^ 2 * b.cHarmonic * Hh :=
      mul_le_mul_of_nonneg_left hh
        (mul_nonneg (mul_nonneg hbase (sq_nonneg _)) hc0)
    _ ≤ Q * S * Rbudget * A * b.tHarmonic ^ 2 * Hc * Hh :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (mul_nonneg hbase (sq_nonneg _))) hHh
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htsq hbase) hHc) hHh

end WeightedBlock

/-- The original inverse square-root normalization yields exactly 1/ND
after taking the squared complex norm. -/
theorem inverse_sqrt_norm_sq (x : ℝ) (hx : 0 < x) :
    ‖(1 : ℂ) / (Real.sqrt x : ℂ)‖ ^ 2 = 1 / x := by
  rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg x), div_pow, one_pow,
    Real.sq_sqrt (le_of_lt hx)]

/-- Global D,r assembly for the arithmetic expansion's weighted normal form.

Each block's pointwise support budget has Rbudget=B/NR(r), and its column
mass is AD(d), independent of r. The two operator sieve bounds and all
positivity, support, harmonic and row-local cardinal assumptions are visible.
No block-energy or global hybrid-energy estimate is a hypothesis. -/
theorem hybrid_energy_of_weighted_blocks
    {I : Type u} {D : Type uD} {R : Type uR}
    [DecidableEq I] [DecidableEq D] [DecidableEq R]
    (rows : Finset I) (ds : Finset D) (rs : Finset R)
    (localBlocks : I → Finset (D × R))
    (block : D → R → WeightedBlock.{u, v} I)
    (mu : I → D × R → ℂ)
    (ND : D → ℝ) (NR : R → ℝ) (AD : D → ℝ)
    (Delta Q S B Ht Hc Hh : ℝ)
    (hDelta : 0 ≤ Delta) (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hB : 0 ≤ B)
    (hHt : 0 ≤ Ht) (hHc : 0 ≤ Hc) (hHh : 0 ≤ Hh)
    (hND : ∀ d ∈ ds, 0 < ND d) (hNR : ∀ r ∈ rs, 0 < NR r)
    (hAD : ∀ d ∈ ds, 0 ≤ AD d)
    (hlocal : ∀ i ∈ rows, localBlocks i ⊆ ds ×ˢ rs)
    (hmu : ∀ i ∈ rows, ∀ dr ∈ localBlocks i, ‖mu i dr‖ ≤ 1)
    (hcard : ∀ i ∈ rows, ((localBlocks i).card : ℝ) ≤ Delta)
    (hadmissible : ∀ d ∈ ds, ∀ r ∈ rs,
      (block d r).Admissible (rows.filter fun i => (d, r) ∈ localBlocks i)
        Q S (B / NR r) (AD d))
    (ht : ∀ d ∈ ds, ∀ r ∈ rs, (block d r).tHarmonic ≤ Ht)
    (hc : ∀ d ∈ ds, ∀ r ∈ rs, (block d r).cHarmonic ≤ Hc)
    (hh : ∀ d ∈ ds, ∀ r ∈ rs, (block d r).hHarmonic ≤ Hh) :
    (∑ i ∈ rows, ‖∑ dr ∈ localBlocks i, mu i dr *
      (((1 : ℂ) / (Real.sqrt (ND dr.1) : ℂ)) * (block dr.1 dr.2).row i)‖ ^ 2) ≤
      Delta * Q * S * B * Ht ^ 2 * Hc * Hh *
        (∑ d ∈ ds, AD d / ND d) * (∑ r ∈ rs, 1 / NR r) := by
  classical
  let weight : D × R → ℂ := fun dr => (1 : ℂ) / (Real.sqrt (ND dr.1) : ℂ)
  let value : I → D × R → ℂ := fun i dr => (block dr.1 dr.2).row i
  let bound : D × R → ℝ := fun dr =>
    Q * S * (B / NR dr.2) * AD dr.1 * Ht ^ 2 * Hc * Hh
  have hblock (dr : D × R) (hdr : dr ∈ ds ×ˢ rs) :
      (∑ i ∈ rows with dr ∈ localBlocks i, ‖value i dr‖ ^ 2) ≤ bound dr := by
    have hd := (Finset.mem_product.mp hdr).1
    have hr := (Finset.mem_product.mp hdr).2
    simpa only [value, bound] using
      (block dr.1 dr.2).energy_le_uniform_harmonics
        (rows.filter fun i => (dr.1, dr.2) ∈ localBlocks i)
        Q S (B / NR dr.2) (AD dr.1) Ht Hc Hh
        hQ hS (div_nonneg hB (le_of_lt (hNR dr.2 hr))) (hAD dr.1 hd)
        hHt hHc hHh (hadmissible dr.1 hd dr.2 hr)
        (ht dr.1 hd dr.2 hr) (hc dr.1 hd dr.2 hr) (hh dr.1 hd dr.2 hr)
  have hassembly := row_local_weighted_cauchy_of_block_bounds
    rows localBlocks (ds ×ˢ rs) mu weight value Delta bound hDelta hmu hcard
    (fun i hi dr hdr => hlocal i hi hdr) hblock
  have hmass :
      (∑ dr ∈ ds ×ˢ rs, ‖weight dr‖ ^ 2 * bound dr) =
      Q * S * B * Ht ^ 2 * Hc * Hh *
        (∑ d ∈ ds, AD d / ND d) * (∑ r ∈ rs, 1 / NR r) := by
    rw [Finset.sum_product]
    calc
      _ = ∑ d ∈ ds, ∑ r ∈ rs,
          (Q * S * B * Ht ^ 2 * Hc * Hh) * (AD d / ND d) * (1 / NR r) := by
        apply Finset.sum_congr rfl
        intro d hd
        apply Finset.sum_congr rfl
        intro r hr
        dsimp only [weight, bound]
        rw [inverse_sqrt_norm_sq (ND d) (hND d hd)]
        simp only [div_eq_mul_inv]
        ring
      _ = (∑ d ∈ ds, (Q * S * B * Ht ^ 2 * Hc * Hh) * (AD d / ND d)) *
          (∑ r ∈ rs, 1 / NR r) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro d hd
        exact (Finset.mul_sum ..).symm
      _ = _ := by rw [← Finset.mul_sum]
  calc
    _ ≤ Delta * ∑ dr ∈ ds ×ˢ rs, ‖weight dr‖ ^ 2 * bound dr := hassembly
    _ = Delta * (Q * S * B * Ht ^ 2 * Hc * Hh *
        (∑ d ∈ ds, AD d / ND d) * (∑ r ∈ rs, 1 / NR r)) := by rw [hmass]
    _ = _ := by ring

#print axioms WeightedBlock.tHarmonic_nonneg
#print axioms WeightedBlock.cHarmonic_nonneg
#print axioms WeightedBlock.hHarmonic_nonneg
#print axioms WeightedBlock.energy_le
#print axioms WeightedBlock.energy_le_uniform_harmonics
#print axioms inverse_sqrt_norm_sq
#print axioms hybrid_energy_of_weighted_blocks

end
end HeckeSkeleton.LowHybrid

