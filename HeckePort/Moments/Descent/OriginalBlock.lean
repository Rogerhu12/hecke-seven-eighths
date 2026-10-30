import HeckePort.Moments.Descent.HybridReduction
import HeckePort.Moments.Descent.Quotients

/-!
# The original quotient block

Port of openai/math `OAI/NumberTheory/DirichletL/Descent/OriginalBlock.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

The same abstraction as in `Descent/Hybrid`, `Descent/Quotients` and `Descent/HybridReduction`
is used: the quadratic row `q`, the cubic kernel `κ`, the admissibility predicates
`RowAdm` (`CanonicalQuadraticSieve.Admissible`), `CubAdm` (`CubicSieve.Admissible`), `ColAdm`
(`Squarefree`), the exteriority predicate `Ext`, and the two large sieves as hypotheses
(`hsieve`, `hcubic` with the bound `sieveNorm N L`).  The counting constants `128` are
`idealCountConstant K` (`CenteredMomentCounting.card_le_idealCountConstant`), so the constant
`C * (128 * 128 * 256)` of openai becomes `C * (c * c * (2 * c))` for `c = idealCountConstant K`.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators
open HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

theorem hybrid_original_quotient_block {Ext : Ideal (𝓞 K) → Prop}
    (q κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (RowAdm ColAdm CubAdm : Ideal (𝓞 K) → Prop)
    (hκ : CubicKernelAxioms Ext κ) (hq : QuadraticRowAxioms RowAdm q)
    (hRowDvd : ∀ I J : Ideal (𝓞 K), RowAdm I → J ∣ I → RowAdm J)
    (hCubDvd : ∀ I J : Ideal (𝓞 K), CubAdm I → J ∣ I → CubAdm J)
    (hCol : ∀ J, ColAdm J → J ≠ ⊥) (hCub : ∀ J, CubAdm J → J ≠ ⊥)
    (hRow : ∀ J, RowAdm J → J ≠ ⊥)
    (hmul : ∀ k, RowAdm k → ∀ B J : Ideal (𝓞 K), q k (B * J) = q k B * q k J)
    (sieveNorm : ℝ → ℝ → ℝ) (hsieveNorm : ∀ N L, 0 ≤ sieveNorm N L)
    (hcubic : ∀ (Jset Pset : Finset (Ideal (𝓞 K))) (N L : ℝ),
      (∀ J ∈ Jset, CubAdm J ∧ (Ideal.absNorm J : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubAdm P ∧ (Ideal.absNorm P : ℝ) ≤ L) →
      ∀ a : Ideal (𝓞 K) → ℂ,
        (∑ J ∈ Jset, ‖∑ P ∈ Pset, a P * κ P J‖ ^ 2) ≤
          sieveNorm N L * ∑ P ∈ Pset, ‖a P‖ ^ 2)
    (ε : ℝ) (hε : 0 < ε) (Cq : ℝ) (hCq : 0 < Cq)
    (hsieve : ColumnEnergy q RowAdm ColAdm (ε / 2) Cq) :
    ∃ C : ℝ, 0 < C ∧ ∀ A X N L Bk H : ℝ,
      1 ≤ A → 1 ≤ X → 1 ≤ N → 1 ≤ Bk → 1 ≤ H →
    ∀ (R r t : Ideal (𝓞 K)), R ≠ ⊥ → r ≠ ⊥ →
    ∀ (rows nset Pset : Finset (Ideal (𝓞 K))) (pairs : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)))
      (cset : Ideal (𝓞 K) → Finset (Ideal (𝓞 K)))
      (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ),
      (∀ k ∈ rows, RowAdm k ∧ (Ideal.absNorm k : ℝ) ≤ A) →
      (∀ n ∈ nset, CubAdm n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubAdm P ∧
        L ≤ (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) →
      (∀ p ∈ pairs, ColAdm (p.1 * p.2) ∧
        (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
      (∀ p ∈ pairs, p.2 ≠ ⊥ ∧ (Ideal.absNorm p.2 : ℝ) ≤ H) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1,
        c ≠ ⊥ ∧ (Ideal.absNorm c : ℝ) ≤ Bk ∧ (r * c) * p.1 ∈ nset) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, ‖beta (r * c) p.1 p.2‖ ≤ 1) →
      (∑ k ∈ quotientSupport (R * r) rows,
        ‖(Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
          (∑ p ∈ pairs, q k (p.1 * p.2) *
            (∑ c ∈ cset p.1, hybridColumnCoefficient κ q R r beta c p.1 p.2 *
              (∑ P ∈ quotientSupport R Pset,
                hybridCubicCoefficient κ Ext R r p.2 t a P * κ P (c * p.1))))‖ ^ 2) ≤
      C * (A * X * N) ^ ε * (A + X) * Bk * H /
        (Ideal.absNorm R : ℝ) * sieveNorm N (2 * L) := by
  have hc0 : 0 < idealCountConstant K := zero_lt_one.trans_le (one_le_idealCountConstant K)
  obtain ⟨C, hC, hblock⟩ :=
    hybrid_fixed_block_sieve_norm q κ RowAdm ColAdm CubAdm hCol hCub hmul
      (fun k hk J => hq.norm_le_one k J) sieveNorm hsieveNorm hcubic ε hε Cq hCq hsieve
  refine ⟨C * (idealCountConstant K * idealCountConstant K * (2 * idealCountConstant K)),
    by positivity, ?_⟩
  intro A X N L Bk H hA hX hN hBk hH R r t hR hr rows nset Pset pairs cset a beta
    hrows hn hP ha hpairs hhs hcs hbeta
  let Hset := pairs.image Prod.snd
  let mc := (pairs.image Prod.fst).biUnion fun m => (cset m).image fun c => (m, c)
  have hRr : R * r ≠ ⊥ := mul_ne_zero hR hr
  have hn0 : ∀ n ∈ nset, n ≠ ⊥ := fun n hn' => hCub n (hn n hn').1
  have hP0 : ∀ P ∈ Pset, P ≠ ⊥ := fun P hP' => hCub P (hP P hP').1
  have hHcount : (Hset.card : ℝ) ≤ idealCountConstant K * H := by
    apply card_le_idealCountConstant K Hset H hH
    intro h hh
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
    exact (hhs p hp).2
  have hcCount : ∀ p ∈ pairs, ((cset p.1).card : ℝ) ≤ idealCountConstant K * Bk := by
    intro p hp
    exact card_le_idealCountConstant K (cset p.1) Bk hBk
      (fun c hc => (hcs p hp c hc).2.1)
  have hmc : ∀ p ∈ pairs, ∀ c ∈ cset p.1, (p.1, c) ∈ mc := by
    intro p hp c hc
    exact Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_image.mpr ⟨p, hp, rfl⟩,
      Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩
  have hmap : ∀ u ∈ mc, u.2 * (1 * u.1) ∈ quotientSupport r nset := by
    intro u hu
    obtain ⟨m, hm, cu⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp cu
    apply (mem_quotientSupport r (c * (1 * p.1)) hr nset).mpr
    simpa only [one_mul, mul_assoc] using (hcs p hp c hc).2.2
  have he := hblock A X N (2 * L) hA hX hN
    (quotientSupport (R * r) rows) pairs mc Hset (quotientSupport r nset)
    (quotientSupport R Pset)
    (fun k hk => ⟨quotientSupport_admissible RowAdm hRowDvd (R * r) hRr rows
        (fun k hk => (hrows k hk).1) k hk,
      quotientSupport_norm_le (R * r) hRr rows A
        (fun k hk => hRow k (hrows k hk).1) (fun k hk => (hrows k hk).2) k hk⟩)
    hpairs 1 1 cset (fun h => hybridCubicCoefficient κ Ext R r h t a)
    (hybridColumnCoefficient κ q R r beta) (idealCountConstant K * Bk) (2 * idealCountConstant K)
    (by positivity) hcCount
    (fun p hp c hc => hybridColumnCoefficient_norm_le_one hκ hq R r c p.1 p.2 beta (hbeta p hp c hc))
    (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩) hmc hmap
    (fun J hJ => ⟨quotientSupport_admissible CubAdm hCubDvd r hr nset (fun n hn' => (hn n hn').1) J hJ,
      quotientSupport_norm_le r hr nset N hn0 (fun n hn' => (hn n hn').2) J hJ⟩)
    (fun P hP' => ⟨quotientSupport_admissible CubAdm hCubDvd R hR Pset (fun P hP' => (hP P hP').1) P hP',
      quotientSupport_norm_le R hR Pset (2 * L) hP0 (fun P hP' => (hP P hP').2.2) P hP'⟩)
    (fun h _ => quotient_hybridCubicCoefficient_energy hκ R r h t hR Pset L hP0
      (fun P hP' => ⟨(hP P hP').2.1, (hP P hP').2.2⟩) a ha)
  simp only [one_mul] at he
  have hsqrt : ‖(Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹‖ ^ 2 =
      (Ideal.absNorm R : ℝ)⁻¹ := by
    rw [norm_inv, inv_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
  simp_rw [norm_mul, mul_pow, hsqrt]
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (Nat.cast_nonneg _))).trans
  calc
    _ ≤ (Ideal.absNorm R : ℝ)⁻¹ *
      (C * (A * X * N) ^ ε * (A + X) * (idealCountConstant K * Bk) *
        (idealCountConstant K * H) * sieveNorm N (2 * L) * (2 * idealCountConstant K)) := by
      gcongr
      exact hsieveNorm _ _
    _ = _ := by ring

end HeckePort.Moments

end
