import HeckeSkeleton.LowEnergy.OriginalRowSupport
import HeckeSkeleton.LowEnergy.SquarefreeFibers
import HeckeSkeleton.LowHybrid.Global
import HeckeSkeleton.LowHybrid.WeightedSieveBounds

/-!
# Actual ideal weighted blocks and their two sieve operators

The fields of the weighted block are constructed from ordinary integral
ideal products, the exact extracted coefficients, and explicit zero
extensions. The block row is proved equal to the extracted row. Its energy
is then derived from the quadratic and cubic operators, not assumed.
-/

namespace HeckeSkeleton.LowEnergy.KeepOriginalRow

open NumberField Ideal HeckeSkeleton.LowHybrid
open scoped BigOperators NumberField Classical
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def goodQuadraticPairs (ms hs : Finset (Ideal (𝓞 K))) (N B : ℝ) :
    Finset (Ideal (𝓞 K) × Ideal (𝓞 K)) :=
  (ms ×ˢ hs).filter (fun x =>
    Squarefree (x.1 * x.2) ∧ (Ideal.absNorm (x.1 * x.2) : ℝ) ≤ N * B)

def goodCubicPairs (ms cs : Finset (Ideal (𝓞 K))) (N : ℝ) :
    Finset (Ideal (𝓞 K) × Ideal (𝓞 K)) :=
  (ms ×ˢ cs).filter (fun x =>
    Squarefree (x.2 * x.1) ∧ (Ideal.absNorm (x.2 * x.1) : ℝ) ≤ N)

def quadraticTargets (ms hs : Finset (Ideal (𝓞 K))) (N B : ℝ) :
    Finset (Ideal (𝓞 K)) :=
  (goodQuadraticPairs ms hs N B).image (fun x => x.1 * x.2)

def cubicTargets (ms cs : Finset (Ideal (𝓞 K))) (N : ℝ) :
    Finset (Ideal (𝓞 K)) :=
  (goodCubicPairs ms cs N).image (fun x => x.2 * x.1)

theorem quadraticTargets_support (ms hs : Finset (Ideal (𝓞 K))) (N B : ℝ)
    (J : Ideal (𝓞 K)) (hJ : J ∈ quadraticTargets ms hs N B) :
    Squarefree J ∧ (Ideal.absNorm J : ℝ) ≤ N * B := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hJ
  exact (Finset.mem_filter.mp hx).2

theorem cubicTargets_support (ms cs : Finset (Ideal (𝓞 K))) (N : ℝ)
    (J : Ideal (𝓞 K)) (hJ : J ∈ cubicTargets ms cs N) :
    Squarefree J ∧ (Ideal.absNorm J : ℝ) ≤ N := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hJ
  exact (Finset.mem_filter.mp hx).2

def concreteBlock
    (cubic quad : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (ts cs ms hs ps : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ)
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (N B : ℝ) (D r : Ideal (𝓞 K)) : WeightedBlock (Ideal (𝓞 K)) where
  T := Ideal (𝓞 K)
  C := Ideal (𝓞 K)
  M := Ideal (𝓞 K)
  H := Ideal (𝓞 K)
  P := Ideal (𝓞 K)
  ts := ts
  cs := quotientSupport r cs
  ms := ms
  hs := hs
  ps := quotientSupport D ps
  q := zeroExtendedQuadratic (goodQuadraticPairs ms hs N B)
    (fun x => x.1 * x.2) quad
  chi := zeroExtendedCubic (goodCubicPairs ms (quotientSupport r cs) N)
    (fun x => x.2 * x.1) cubic
  a := blockColumn cubic a D r
  beta := blockBeta cubic beta D r
  rowMask := mask
  wt := fun t => (Ideal.absNorm t : ℝ)
  wc := fun c => (Ideal.absNorm c : ℝ)
  wh := fun h => (Ideal.absNorm h : ℝ)

/-- The literal coefficient support makes both zero extensions exact. -/
theorem concreteBlock_row_eq
    (cubic quad : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (ts cs ms hs ps : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ)
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (N B : ℝ) (hsupport : ReconstructedSupport beta N B)
    (D r k : Ideal (𝓞 K)) :
    (concreteBlock cubic quad ts cs ms hs ps a beta N B D r).row k =
      extractedRow cubic quad ts cs ms hs ps a beta D r k := by
  classical
  unfold WeightedBlock.row extractedRow
  dsimp only [concreteBlock]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro c hc
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hz : blockBeta cubic beta D r t c m h = 0
  · simp only [hz, zero_mul, mul_zero]
  · have hg := hsupport.block_products cubic D r t c m h hz
    have hq : (m, h) ∈ goodQuadraticPairs ms hs N B :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm, hh⟩, hg.1⟩
    have hj : (m, c) ∈ goodCubicPairs ms (quotientSupport r cs) N :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm, hc⟩, hg.2⟩
    simp only [zeroExtendedQuadratic, zeroExtendedCubic, if_pos hq, if_pos hj]

/-- All finite scalar inputs of the weighted block are proved from its
actual coefficient and support data. The two operator inputs are the
arbitrary-coefficient quadratic and cubic sieve conclusions. -/
theorem concreteBlock_admissible
    (cubic quad : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hcubic_norm : ∀ P n, ‖cubic P n‖ ≤ 1)
    (rows ts cs ms hs ps : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ)
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (N B Q S Dq Dc A : ℝ) (D r : Ideal (𝓞 K))
    (hQ : 0 ≤ Q) (hDq : 0 ≤ Dq) (hDc : 0 ≤ Dc) (hB : 0 ≤ B)
    (hD : D ≠ ⊥) (hr : r ≠ ⊥)
    (hts : ∀ t ∈ ts, t ≠ ⊥) (hcs : ∀ c ∈ cs, c ≠ ⊥)
    (hhs : ∀ h ∈ hs, h ≠ ⊥)
    (ha : ∀ P ∈ ps, ‖a P‖ ≤ 1)
    (hbeta : ∀ t c m h, ‖beta t c m h‖ ≤ 1)
    (hsupport : ReconstructedSupport beta N B)
    (hA : (∑ P ∈ quotientSupport D ps, 1 / (Ideal.absNorm P : ℝ)) ≤ A)
    (hqfiber : ∀ J ∈ quadraticTargets ms hs N B,
      (((goodQuadraticPairs ms hs N B).filter (fun x => x.1 * x.2 = J)).card : ℝ) ≤ Dq)
    (hcfiber : ∀ J ∈ cubicTargets ms (quotientSupport r cs) N,
      (((goodCubicPairs ms (quotientSupport r cs) N).filter
        (fun x => x.2 * x.1 = J)).card : ℝ) ≤ Dc)
    (hquadratic : ∀ f : Ideal (𝓞 K) → ℂ,
      (∑ k ∈ rows, ‖∑ J ∈ quadraticTargets ms hs N B, quad k J * f J‖ ^ 2) ≤
        Q * ∑ J ∈ quadraticTargets ms hs N B, ‖f J‖ ^ 2)
    (hcubic : ∀ f : Ideal (𝓞 K) → ℂ,
      (∑ J ∈ cubicTargets ms (quotientSupport r cs) N,
        ‖∑ P ∈ quotientSupport D ps, f P * cubic P J‖ ^ 2) ≤
        S * ∑ P ∈ quotientSupport D ps, ‖f P‖ ^ 2) :
    (concreteBlock cubic quad ts cs ms hs ps a beta N B D r).Admissible
      rows (Q * Dq) (S * Dc) (B / (Ideal.absNorm r : ℝ)) A := by
  classical
  refine
    { wt_pos := ?_
      wc_pos := ?_
      wh_pos := ?_
      mask := ?_
      budget := ?_
      column_mass := ?_
      quadratic := ?_
      cubic := ?_ }
  · intro t ht
    exact HeckeSkeleton.LowEnergy.ideal_norm_pos K t (hts t ht)
  · intro c hc
    exact HeckeSkeleton.LowEnergy.ideal_norm_pos K c
      (quotientSupport_nezero r hr cs hcs c hc)
  · intro h hh
    exact HeckeSkeleton.LowEnergy.ideal_norm_pos K h (hhs h hh)
  · intro k hk t ht
    exact mask_norm_le k t
  · intro t ht c hc m hm h hh
    exact hsupport.block_budget cubic hcubic_norm hbeta D r t c m h
      hr (hts t ht) (hhs h hh) hB
  · intro t ht h hh
    exact (Finset.sum_le_sum (fun P hP =>
      blockColumn_sq_le_reciprocal cubic hcubic_norm a D r t h P
        (ha (D * P) ((mem_quotientSupport D P hD ps).mp hP)))).trans hA
  · intro f
    exact zero_extended_column_fiber_sieve rows ms hs (goodQuadraticPairs ms hs N B)
      (quadraticTargets ms hs N B) (fun x => x.1 * x.2) quad Q Dq hQ hDq
      (Finset.filter_subset _ _)
      (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      hqfiber hquadratic f
  · intro f
    exact zero_extended_row_fiber_sieve ms (quotientSupport r cs)
      (goodCubicPairs ms (quotientSupport r cs) N)
      (cubicTargets ms (quotientSupport r cs) N) (quotientSupport D ps)
      (fun x => x.2 * x.1) cubic S Dc hDc (Finset.filter_subset _ _)
      (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      hcfiber hcubic f

/-- Both product multiplicities are actual ideal counts with uniform
constants, and are bounded separately. -/
theorem concrete_product_fibers_small_power (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N B : ℝ, 1 ≤ N → 1 ≤ B →
      ∀ ms hs cs : Finset (Ideal (𝓞 K)),
      (∀ J ∈ quadraticTargets ms hs N B,
        (((goodQuadraticPairs ms hs N B).filter (fun x => x.1 * x.2 = J)).card : ℝ) ≤
          C * (N * B) ^ eps) ∧
      (∀ J ∈ cubicTargets ms cs N,
        (((goodCubicPairs ms cs N).filter (fun x => x.2 * x.1 = J)).card : ℝ) ≤
          C * N ^ eps) := by
  obtain ⟨C, hC, hb⟩ := HeckeSkeleton.LowEnergy.ideal_product_fibers_small_power K eps heps
  refine ⟨C, hC, ?_⟩
  intro N B hN hB ms hs cs
  constructor
  · intro J hJ
    have hsupport := quadraticTargets_support ms hs N B J hJ
    exact hb (N * B) (one_le_mul_of_one_le_of_one_le hN hB)
      (goodQuadraticPairs ms hs N B) J hsupport.1 hsupport.2
  · intro J hJ
    have hsupport := cubicTargets_support ms cs N J hJ
    simpa only [mul_comm] using hb N hN (goodCubicPairs ms cs N) J hsupport.1 hsupport.2

#print axioms concreteBlock_row_eq
#print axioms concreteBlock_admissible
#print axioms concrete_product_fibers_small_power

end
end HeckeSkeleton.LowEnergy.KeepOriginalRow
