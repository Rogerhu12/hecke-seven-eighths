import HeckePort.Moments.Descent.MaskedGrid
import HeckePort.Moments.Descent.OriginalBlock

/-!
# The extracted dyadic block

Port of openai/math `OAI/NumberTheory/DirichletL/Descent/DyadicBlock.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`, under the same abstraction as
`Descent/OriginalBlock` (abstract quadratic row `q` and cubic kernel `κ`, divisor-closed
admissibility predicates, the two large sieves as the hypotheses `hsieve`, `hcubic`).  The
extra hypothesis `hCubExt` says that cubic-admissible ideals satisfy `Ext` (openai:
`CubicSieve.Admissible P` gives `primaryGenerator P ≠ 0`).
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators

variable {K : Type} [Field K] [NumberField K]

theorem hybrid_extracted_dyadic_block_nonempty {Ext : Ideal (𝓞 K) → Prop}
    (q κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (RowAdm ColAdm CubAdm : Ideal (𝓞 K) → Prop)
    (hκ : CubicKernelAxioms Ext κ) (hq : QuadraticRowAxioms RowAdm q)
    (hRowDvd : ∀ I J : Ideal (𝓞 K), RowAdm I → J ∣ I → RowAdm J)
    (hCubDvd : ∀ I J : Ideal (𝓞 K), CubAdm I → J ∣ I → CubAdm J)
    (hCol : ∀ J, ColAdm J → J ≠ ⊥) (hCub : ∀ J, CubAdm J → J ≠ ⊥)
    (hRow : ∀ J, RowAdm J → J ≠ ⊥) (hCubExt : ∀ P, CubAdm P → Ext P)
    (hColSq : ∀ J : Ideal (𝓞 K), Squarefree J → ColAdm J)
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
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ Kr N B L C T : ℝ,
      1 ≤ Kr → 1 ≤ N → 1 ≤ B → 1 ≤ C → 1 ≤ T →
    ∀ (R r t : Ideal (𝓞 K)), R ≠ ⊥ → r ≠ ⊥ → T ≤ (Ideal.absNorm t : ℝ) →
    ∀ (rows nset Pset : Finset (Ideal (𝓞 K))) (D : Finset (HybridColumnData K))
      (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ),
      (∀ k ∈ rows, RowAdm k ∧ (Ideal.absNorm k : ℝ) ≤ Kr) →
      (∀ n ∈ nset, CubAdm n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubAdm P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) →
      (∀ d ∈ D, d.square = t ∧ C ≤ (Ideal.absNorm d.common : ℝ) ∧
        (Ideal.absNorm d.common : ℝ) ≤ 2 * C ∧ d.common * d.residualN ∈ nset ∧
        (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B) →
      (∀ d ∈ D, ‖beta d.common d.residualN d.residualB‖ ≤ 1) →
      (quotientGridSupport r (hybridGridSupport D)).Nonempty →
      (∑ k ∈ quotientSupport (R * r) rows,
        ‖gridDivisorHybridBlock q κ (hybridGridSupport D) Pset a beta t ((R * r) * k) R r‖ ^ 2) ≤
      C₀ * (Kr * (N * B) * N) ^ ε * (Kr + N * B) * B /
        ((Ideal.absNorm R : ℝ) * (Ideal.absNorm r : ℝ) * T ^ 2) *
          sieveNorm N (2 * L) := by
  obtain ⟨C₁, hC₁, hblock⟩ := hybrid_original_quotient_block (Ext := Ext) q κ RowAdm ColAdm CubAdm
    hκ hq hRowDvd hCubDvd hCol hCub hRow hmul sieveNorm hsieveNorm hcubic ε hε Cq hCq hsieve
  refine ⟨2 * C₁, by positivity, ?_⟩
  intro Kr N B L C T hK hN hB hC hT R r t hR hr ht rows nset Pset D a beta
    hrows hn hP ha hD hbeta hQ
  let Q := quotientGridSupport r (hybridGridSupport D)
  let X := N * B / (C ^ 2 * T ^ 2)
  let Ac := 2 * C / (Ideal.absNorm r : ℝ)
  let H := B / (C * T ^ 2)
  have hC0 : 0 < C := by linarith
  have hT0 : 0 < T := by linarith
  have hnr : 0 < (Ideal.absNorm r : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hr (Ideal.absNorm_eq_zero_iff.mp hz))
  have hnorm (d : HybridColumnData K) (hd : d ∈ D) :
      (Ideal.absNorm d.residualN : ℝ) ≤ N / C ∧
      (Ideal.absNorm d.residualB : ℝ) ≤ H ∧
      (Ideal.absNorm (d.residualN * d.residualB) : ℝ) ≤ X := by
    have hd' := hD d hd
    apply d.residual_norm_bounds N B C T (by linarith) (by linarith) hC0 hT0
      (hn _ hd'.2.2.2.1).2 hd'.2.2.2.2 hd'.2.1
    simpa only [hd'.1] using ht
  have hcBound (d : HybridColumnData K) (hd : d ∈ D) (c : Ideal (𝓞 K))
      (hdc : d.common = r * c) : c ≠ ⊥ ∧ (Ideal.absNorm c : ℝ) ≤ Ac := by
    have hcz : c ≠ ⊥ := by
      intro hz
      apply d.common_ne_zero
      simp [hdc, hz]
    refine ⟨hcz, (le_div_iff₀ hnr).mpr ?_⟩
    have hdcN := (hD d hd).2.2.1
    rw [hdc, map_mul, Nat.cast_mul] at hdcN
    simpa only [mul_comm] using hdcN
  have hpair (p : Ideal (𝓞 K) × Ideal (𝓞 K)) (hp : p ∈ Q.image Prod.fst) :
      Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X ∧
      p.2 ≠ ⊥ ∧ (Ideal.absNorm p.2 : ℝ) ≤ H := by
    obtain ⟨u, hu, hup⟩ := Finset.mem_image.mp hp
    obtain ⟨d, hd, he, hdc⟩ := quotientGridSupport_origin r hr D u.1 u.2 hu
    have he' : (d.residualN, d.residualB) = p := he.trans hup
    have hm := congrArg Prod.fst he'
    have hh := congrArg Prod.snd he'
    have hdB : d.residualB ≠ ⊥ :=
      ne_zero_of_dvd_ne_zero d.g_squarefree.ne_zero (dvd_mul_left _ _)
    exact ⟨by simpa only [← hm, ← hh] using d.residual_product_squarefree,
      by simpa only [← hm, ← hh] using (hnorm d hd).2.2,
      by simpa only [← hh] using hdB,
      by simpa only [← hh] using (hnorm d hd).2.1⟩
  have hcset (p : Ideal (𝓞 K) × Ideal (𝓞 K)) (hp : p ∈ Q.image Prod.fst)
      (c : Ideal (𝓞 K)) (hc : c ∈ gridCommonSupport Q p.1) :
      c ≠ ⊥ ∧ (Ideal.absNorm c : ℝ) ≤ Ac ∧ (r * c) * p.1 ∈ nset := by
    obtain ⟨d, hd, hm, hdc⟩ := quotientGridCommonSupport_origin r hr D p.1 c hc
    have hc' := hcBound d hd c hdc
    exact ⟨hc'.1, hc'.2, by simpa only [hdc, hm] using (hD d hd).2.2.2.1⟩
  obtain ⟨u₀, hu₀⟩ := hQ
  have hp₀ : u₀.1 ∈ Q.image Prod.fst := Finset.mem_image.mpr ⟨u₀, hu₀, rfl⟩
  have hc₀ : u₀.2 ∈ gridCommonSupport Q u₀.1.1 :=
    Finset.mem_image.mpr ⟨u₀, Finset.mem_filter.mpr ⟨hu₀, rfl⟩, rfl⟩
  have hX : 1 ≤ X :=
    (norm_one_le_of_ne_bot (hpair u₀.1 hp₀).1.ne_zero).trans (hpair u₀.1 hp₀).2.1
  have hH : 1 ≤ H :=
    (norm_one_le_of_ne_bot (hpair u₀.1 hp₀).2.2.1).trans (hpair u₀.1 hp₀).2.2.2
  have hA : 1 ≤ Ac :=
    (norm_one_le_of_ne_bot (hcset u₀.1 hp₀ u₀.2 hc₀).1).trans
      (hcset u₀.1 hp₀ u₀.2 hc₀).2.1
  have hbGrid : ∀ u ∈ hybridGridSupport D, ‖beta u.2 u.1.1 u.1.2‖ ≤ 1 := by
    intro u hu
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hu
    exact hbeta d hd
  have he := hblock Kr X N L Ac H hK hX hN hA hH R r t hR hr rows nset Pset
    (Q.image Prod.fst) (gridCommonSupport Q) a
    (extractedGridCoefficient (hybridGridSupport D) R t beta)
    hrows hn hP ha (fun p hp => ⟨hColSq _ (hpair p hp).1, (hpair p hp).2.1⟩)
    (fun p hp => (hpair p hp).2.2) hcset
    (fun p _ c _ => extractedGridCoefficient_norm_le_one _ R t beta hbGrid (r * c) p.1 p.2)
  have hrow (k : Ideal (𝓞 K)) (hk : k ∈ quotientSupport (R * r) rows) :=
    gridDivisorHybridBlock_extract hκ hq CubAdm hCubDvd hCubExt
      (hybridGridSupport D) Pset a beta t k R r hR hr
      (hrows _ ((mem_quotientSupport (R * r) k (mul_ne_zero hR hr) rows).mp hk)).1
      (fun P hP' => (hP P hP').1)
  have he' : (∑ k ∈ quotientSupport (R * r) rows,
      ‖gridDivisorHybridBlock q κ (hybridGridSupport D) Pset a beta t ((R * r) * k) R r‖ ^ 2) ≤
      C₁ * (Kr * X * N) ^ ε * (Kr + X) * Ac * H /
        (Ideal.absNorm R : ℝ) * sieveNorm N (2 * L) := by
    calc
      _ = _ := Finset.sum_congr rfl (fun k hk => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hrow k hk))
      _ ≤ _ := he
  have hXupper : X ≤ N * B := by
    apply div_le_self (by positivity : 0 ≤ N * B)
    have hC2 : 1 ≤ C ^ 2 := one_le_pow₀ hC
    have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ hT
    exact one_le_mul_of_one_le_of_one_le hC2 hT2
  apply he'.trans
  calc
    _ ≤ C₁ * (Kr * (N * B) * N) ^ ε * (Kr + N * B) * Ac * H /
        (Ideal.absNorm R : ℝ) * sieveNorm N (2 * L) := by
      have hs : 0 ≤ sieveNorm N (2 * L) := hsieveNorm _ _
      gcongr
    _ = _ := by
      dsimp only [Ac, H]
      field_simp

theorem hybrid_extracted_dyadic_block {Ext : Ideal (𝓞 K) → Prop}
    (q κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (RowAdm ColAdm CubAdm : Ideal (𝓞 K) → Prop)
    (hκ : CubicKernelAxioms Ext κ) (hq : QuadraticRowAxioms RowAdm q)
    (hRowDvd : ∀ I J : Ideal (𝓞 K), RowAdm I → J ∣ I → RowAdm J)
    (hCubDvd : ∀ I J : Ideal (𝓞 K), CubAdm I → J ∣ I → CubAdm J)
    (hCol : ∀ J, ColAdm J → J ≠ ⊥) (hCub : ∀ J, CubAdm J → J ≠ ⊥)
    (hRow : ∀ J, RowAdm J → J ≠ ⊥) (hCubExt : ∀ P, CubAdm P → Ext P)
    (hColSq : ∀ J : Ideal (𝓞 K), Squarefree J → ColAdm J)
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
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ Kr N B L C T : ℝ,
      1 ≤ Kr → 1 ≤ N → 1 ≤ B → 1 ≤ C → 1 ≤ T →
    ∀ (R r t : Ideal (𝓞 K)), R ≠ ⊥ → r ≠ ⊥ → T ≤ (Ideal.absNorm t : ℝ) →
    ∀ (rows nset Pset : Finset (Ideal (𝓞 K))) (D : Finset (HybridColumnData K))
      (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ),
      (∀ k ∈ rows, RowAdm k ∧ (Ideal.absNorm k : ℝ) ≤ Kr) →
      (∀ n ∈ nset, CubAdm n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubAdm P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) →
      (∀ d ∈ D, d.square = t ∧ C ≤ (Ideal.absNorm d.common : ℝ) ∧
        (Ideal.absNorm d.common : ℝ) ≤ 2 * C ∧ d.common * d.residualN ∈ nset ∧
        (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B) →
      (∀ d ∈ D, ‖beta d.common d.residualN d.residualB‖ ≤ 1) →
      (∑ k ∈ quotientSupport (R * r) rows,
        ‖gridDivisorHybridBlock q κ (hybridGridSupport D) Pset a beta t ((R * r) * k) R r‖ ^ 2) ≤
      C₀ * (Kr * (N * B) * N) ^ ε * (Kr + N * B) * B /
        ((Ideal.absNorm R : ℝ) * (Ideal.absNorm r : ℝ) * T ^ 2) *
          sieveNorm N (2 * L) := by
  obtain ⟨C₀, hC₀, he⟩ := hybrid_extracted_dyadic_block_nonempty (Ext := Ext) q κ RowAdm ColAdm
    CubAdm hκ hq hRowDvd hCubDvd hCol hCub hRow hCubExt hColSq hmul sieveNorm hsieveNorm hcubic ε hε
    Cq hCq hsieve
  refine ⟨C₀, hC₀, ?_⟩
  intro Kr N B L C T hK hN hB hC hT R r t hR hr ht rows nset Pset D a beta
    hrows hn hP ha hD hbeta
  by_cases hQ : (quotientGridSupport r (hybridGridSupport D)).Nonempty
  · exact he Kr N B L C T hK hN hB hC hT R r t hR hr ht
      rows nset Pset D a beta hrows hn hP ha hD hbeta hQ
  · have hQ' := Finset.not_nonempty_iff_eq_empty.mp hQ
    simp only [gridDivisorHybridBlock_eq_zero_of_quotientGrid_empty _ _ _ _ _ _ _ _ _ _ hQ',
      norm_zero, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero]
    have hs : 0 ≤ sieveNorm N (2 * L) := hsieveNorm _ _
    positivity

end HeckePort.Moments

end
