import HeckePort.Moments.Descent.IdealMasks
import HeckePort.Moments.Descent.Fibers
import HeckePort.CenteredMoment.Counting

/-!
# Hybrid cubic/quadratic columns

Port of openai/math `OAI/NumberTheory/DirichletL/Descent/Hybrid.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

openai's file is built on two `ℤ[ω]`-specific kernels:

* `inverseCubicKernel P n = star (eisEmbedding (idealSymbol P (primaryGenerator n)))`
  (the conjugate cubic residue symbol of `P` at the primary generator of `n`);
* `quadraticRow k (primaryGenerator J)` (the quadratic symbol of the admissible ideal `k` at the
  primary generator of `J`).

Here they are arbitrary functions `κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ` subject to exactly the
properties openai uses (`CubicKernelAxioms`, `QuadraticRowAxioms`: multiplicativity, norm at most
one, vanishing at non-coprime pairs); in the project they are instantiated by
`idealSymbol K S D` composed with `D.generator` (multiplicativity up to sixth powers of
S-units is `AllowedGeneratorInput.multiplicative`).  `Ext` is an arbitrary predicate playing the
role of "the primary generator is nonzero" (`IsExterior K S`).

* `dyadic_normalized_coefficient_energy`: the constant `256 = 128 * 2` becomes
  `2 * idealCountConstant K`.
* Not ported as stated: `inverseCubicKernel_eq_inverse_square` (an identity for the specific
  symbol), `hybrid_quadratic_square_mask`/`idealZeroMask_primary_indicator` (specific
  quadratic-row facts; `hybrid_original_kernel_decomposition` is ported with the square-mask
  identity as the hypothesis `hsq`).
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators
open UniqueFactorizationMonoid DedekindZetaZeroFree.LargeSieve HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

/-- The properties of `inverseCubicKernel` used by openai's `Descent/Hybrid.lean`. -/
structure CubicKernelAxioms (Ext : Ideal (𝓞 K) → Prop) (κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) :
    Prop where
  mul_left : ∀ R P n, κ (R * P) n = κ R n * κ P n
  mul_right : ∀ P n m, Ext P → κ P (n * m) = κ P n * κ P m
  norm_le_one : ∀ P n, ‖κ P n‖ ≤ 1
  eq_zero_of_not_coprime : ∀ P n, Ext P → Ext n → ¬ IsCoprime P n → κ P n = 0

/-- The properties of `quadraticRow · (primaryGenerator ·)` used by openai's file. -/
structure QuadraticRowAxioms (Adm : Ideal (𝓞 K) → Prop)
    (q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) : Prop where
  mul : ∀ k k' J, Adm (k * k') → q (k * k') J = q k J * q k' J
  norm_le_one : ∀ k J, ‖q k J‖ ≤ 1

def hybridCubicCoefficient (κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (Ext : Ideal (𝓞 K) → Prop) (R r h t : Ideal (𝓞 K)) (a : Ideal (𝓞 K) → ℂ)
    (P : Ideal (𝓞 K)) : ℂ :=
  (a (R * P) * κ P r * (if IsCoprime P (h * t) then 1 else 0)) /
    (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)

theorem dyadic_normalized_coefficient_energy
    (S : Finset (Ideal (𝓞 K))) (L : ℝ) (hL : 1 ≤ L)
    (hS : ∀ P ∈ S, L ≤ (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ 2 * L)
    (a : Ideal (𝓞 K) → ℂ) (ha : ∀ P ∈ S, ‖a P‖ ≤ 1) :
    (∑ P ∈ S, ‖a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)‖ ^ 2) ≤
      2 * idealCountConstant K := by
  have hL0 : 0 < L := by linarith
  have hP0 (P : Ideal (𝓞 K)) (hP : P ∈ S) : 0 < (Ideal.absNorm P : ℝ) :=
    hL0.trans_le (hS P hP).1
  have hcount : (S.card : ℝ) ≤ idealCountConstant K * (2 * L) :=
    card_le_idealCountConstant K S (2 * L) (by linarith) (fun P hP => (hS P hP).2)
  have hterm (P : Ideal (𝓞 K)) (hP : P ∈ S) :
      ‖a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)‖ ^ 2 ≤ 1 / L := by
    rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
    calc
      _ ≤ 1 / (Ideal.absNorm P : ℝ) :=
        div_le_div_of_nonneg_right
          (by simpa using pow_le_pow_left₀ (norm_nonneg _) (ha P hP) 2) (hP0 P hP).le
      _ ≤ _ := one_div_le_one_div_of_le hL0 (hS P hP).1
  calc
    _ ≤ ∑ _P ∈ S, (1 / L : ℝ) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) / L := by simp [div_eq_mul_inv]
    _ ≤ (idealCountConstant K * (2 * L)) / L := div_le_div_of_nonneg_right hcount hL0.le
    _ = 2 * idealCountConstant K := by field_simp

theorem hybridCubicCoefficient_energy {Ext : Ideal (𝓞 K) → Prop}
    {κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ} (hκ : CubicKernelAxioms Ext κ)
    (R r h t : Ideal (𝓞 K)) (S : Finset (Ideal (𝓞 K))) (L : ℝ) (hL : 1 ≤ L)
    (hS : ∀ P ∈ S, L ≤ (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ 2 * L)
    (a : Ideal (𝓞 K) → ℂ) (ha : ∀ P ∈ S, ‖a (R * P)‖ ≤ 1) :
    (∑ P ∈ S, ‖hybridCubicCoefficient κ Ext R r h t a P‖ ^ 2) ≤
      2 * idealCountConstant K := by
  apply dyadic_normalized_coefficient_energy S L hL hS
  intro P hP
  by_cases hc : IsCoprime P (h * t)
  · simp only [hc, ite_true, mul_one, norm_mul]
    exact (mul_le_mul (ha P hP) (hκ.norm_le_one P r)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  · simp [hc]

theorem inverseCubicKernel_quotients {Ext : Ideal (𝓞 K) → Prop}
    {κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ} (hκ : CubicKernelAxioms Ext κ)
    (R P' r c' m : Ideal (𝓞 K)) (hP' : Ext P') :
    κ (R * P') ((r * c') * m) =
      κ R ((r * c') * m) * κ P' r * κ P' (c' * m) := by
  rw [hκ.mul_left, mul_assoc r c' m, hκ.mul_right P' r (c' * m) hP']
  ring

theorem hybrid_cubic_column_mask {Ext : Ideal (𝓞 K) → Prop}
    {κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ} (hκ : CubicKernelAxioms Ext κ)
    (P n b c m h t : Ideal (𝓞 K))
    (hP : Ext P) (hngen : Ext n)
    (hn : n = c * m) (hb : b = (c * h) * t ^ 2) :
    κ P n * (if IsCoprime P b then 1 else 0) =
      κ P n * (if IsCoprime P (h * t) then 1 else 0) := by
  by_cases hc : IsCoprime P c
  · have he : IsCoprime P b ↔ IsCoprime P (h * t) := by
      rw [hb]
      simp only [IsCoprime.mul_right_iff, IsCoprime.pow_right_iff (by decide : 0 < 2),
        hc, true_and]
    simp only [he]
  · have hPn : ¬ IsCoprime P n := by
      rw [hn, IsCoprime.mul_right_iff]
      exact fun hcop => hc hcop.1
    rw [hκ.eq_zero_of_not_coprime P n hP hngen hPn]
    simp

/-- openai `hybrid_original_kernel_decomposition`; the square-mask identity
`hybrid_quadratic_square_mask` is the hypothesis `hsq`. -/
theorem hybrid_original_kernel_decomposition {Ext : Ideal (𝓞 K) → Prop}
    {κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ} (hκ : CubicKernelAxioms Ext κ)
    (k P n b c m h t : Ideal (𝓞 K))
    (hP : Ext P) (hngen : Ext n)
    (hn : n = c * m) (hb : b = (c * h) * t ^ 2)
    (hsq : q k (n * b) = (if IsCoprime k (c * t) then 1 else 0) * q k (m * h)) :
    q k (n * b) * κ P n * (if IsCoprime P b then 1 else 0) *
      (if IsCoprime k P then 1 else 0) =
    (if IsCoprime k t then 1 else 0) * (if IsCoprime k (P * c) then 1 else 0) *
      q k (m * h) * κ P n * (if IsCoprime P (h * t) then 1 else 0) := by
  have hm : ((if IsCoprime k P then (1 : ℂ) else 0) *
      (if IsCoprime k (c * t) then 1 else 0)) =
      (if IsCoprime k t then 1 else 0) * (if IsCoprime k (P * c) then 1 else 0) := by
    simp only [IsCoprime.mul_right_iff]
    by_cases hkp : IsCoprime k P <;> by_cases hkc : IsCoprime k c <;>
      by_cases hkt : IsCoprime k t <;> simp [hkp, hkc, hkt]
  calc
    _ = ((if IsCoprime k P then 1 else 0) * (if IsCoprime k (c * t) then 1 else 0)) *
        q k (m * h) * (κ P n * (if IsCoprime P b then 1 else 0)) := by
      rw [hsq]
      ring
    _ = _ := by rw [hm, hybrid_cubic_column_mask hκ P n b c m h t hP hngen hn hb]; ring

theorem hybrid_kernel_quotients {Ext : Ideal (𝓞 K) → Prop} {Adm : Ideal (𝓞 K) → Prop}
    {κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ} (hκ : CubicKernelAxioms Ext κ)
    (hq : QuadraticRowAxioms Adm q) (R r k' P' c' mh_m h : Ideal (𝓞 K))
    (hk : Adm ((R * r) * k')) (hP' : Ext P') :
    q ((R * r) * k') (mh_m * h) * κ (R * P') ((r * c') * mh_m) =
    (q (R * r) (mh_m * h) * κ R ((r * c') * mh_m)) * κ P' r *
      q k' (mh_m * h) * κ P' (c' * mh_m) := by
  rw [hq.mul (R * r) k' _ hk, inverseCubicKernel_quotients hκ R P' r c' mh_m hP']
  ring

def hybridColumnCoefficient (κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (R r : Ideal (𝓞 K))
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (c m h : Ideal (𝓞 K)) : ℂ :=
  beta (r * c) m h * q (R * r) (m * h) * κ R ((r * c) * m)

theorem hybridColumnCoefficient_norm_le_one {Ext : Ideal (𝓞 K) → Prop}
    {Adm : Ideal (𝓞 K) → Prop} {κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ}
    (hκ : CubicKernelAxioms Ext κ) (hq : QuadraticRowAxioms Adm q)
    (R r c m h : Ideal (𝓞 K))
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (hb : ‖beta (r * c) m h‖ ≤ 1) :
    ‖hybridColumnCoefficient κ q R r beta c m h‖ ≤ 1 := by
  simp only [hybridColumnCoefficient, norm_mul]
  have hfirst : ‖beta (r * c) m h‖ * ‖q (R * r) (m * h)‖ ≤ 1 := by
    exact (mul_le_mul hb (hq.norm_le_one _ _)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  exact (mul_le_mul hfirst (hκ.norm_le_one R ((r * c) * m))
    (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem normalized_ideal_product_weight (R P : Ideal (𝓞 K)) (z : ℂ) :
    z / (Real.sqrt (Ideal.absNorm (R * P) : ℝ) : ℂ) =
      (Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
        (z / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)) := by
  rw [map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem hybrid_extracted_block_identity {Ext : Ideal (𝓞 K) → Prop}
    {Adm : Ideal (𝓞 K) → Prop} {κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ}
    (hκ : CubicKernelAxioms Ext κ) (hq : QuadraticRowAxioms Adm q)
    (R r k' P' c m h t : Ideal (𝓞 K))
    (hk : Adm ((R * r) * k')) (hP' : Ext P')
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) :
    a (R * P') / (Real.sqrt (Ideal.absNorm (R * P') : ℝ) : ℂ) *
      beta (r * c) m h *
      (q ((R * r) * k') (m * h) * κ (R * P') ((r * c) * m)) *
      (if IsCoprime P' (h * t) then 1 else 0) =
    (Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
      hybridColumnCoefficient κ q R r beta c m h *
      q k' (m * h) *
      hybridCubicCoefficient κ Ext R r h t a P' * κ P' (c * m) := by
  rw [normalized_ideal_product_weight, hybrid_kernel_quotients hκ hq R r k' P' c m h hk hP']
  simp only [hybridColumnCoefficient, hybridCubicCoefficient, div_eq_mul_inv]
  ring

def hybridInner (κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (nset bset : Finset (Ideal (𝓞 K)))
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (k P : Ideal (𝓞 K)) : ℂ :=
  ∑ n ∈ nset, ∑ b ∈ bset,
    beta n b * q k (n * b) * κ P n * (if IsCoprime P b then 1 else 0)

def hybridRow (κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (Pset nset bset : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (k : Ideal (𝓞 K)) : ℂ :=
  ∑ P ∈ Pset, a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
    (if IsCoprime k P then 1 else 0) * hybridInner κ q nset bset beta k P

def hybridDivisorTerm (κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (Pset nset bset : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (k R : Ideal (𝓞 K)) : ℂ :=
  ∑ P ∈ Pset, if R ∣ P then
    a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * hybridInner κ q nset bset beta k P else 0

theorem hybridRow_mobius (κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (Pset nset bset : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (k : Ideal (𝓞 K)) (hk : k ≠ ⊥) :
    hybridRow κ q Pset nset bset a beta k =
      ∑ R ∈ idealDivisors k, (moebius R : ℂ) *
        ∑ P ∈ Pset, if R ∣ P then
          a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
            hybridInner κ q nset bset beta k P else 0 := by
  unfold hybridRow
  conv_lhs => simp only [ideal_coprime_mobius k _ hk, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro R hR
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hRP : R ∣ P <;> simp only [hRP, ite_true, ite_false, mul_zero, zero_mul]
  ring

theorem hybrid_first_mask_energy (κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y : ℝ), 1 ≤ Y →
      ∀ (rows Pset nset bset : Finset (Ideal (𝓞 K)))
        (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ),
      (∀ k ∈ rows, k ≠ ⊥ ∧ (Ideal.absNorm k : ℝ) ≤ Y) →
      (∑ k ∈ rows, ‖hybridRow κ q Pset nset bset a beta k‖ ^ 2) ≤
        C * Y ^ ε *
          ∑ R ∈ rows.biUnion idealDivisors, ∑ k ∈ rows,
            if R ∈ idealDivisors k then
              ‖hybridDivisorTerm κ q Pset nset bset a beta k R‖ ^ 2 else 0 := by
  obtain ⟨C, hC1, hdiv⟩ := ideal_divisor_count_le_rpow K ε hε
  have hC : 0 < C := by linarith
  refine ⟨C, hC, ?_⟩
  intro Y hY rows Pset nset bset a beta hrows
  have hrewrite : (∑ k ∈ rows, ‖hybridRow κ q Pset nset bset a beta k‖ ^ 2) =
      ∑ k ∈ rows, ‖∑ R ∈ idealDivisors k,
        (moebius R : ℂ) * hybridDivisorTerm κ q Pset nset bset a beta k R‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hybridRow_mobius κ q Pset nset bset a beta k (hrows k hk).1]
    rfl
  rw [hrewrite]
  apply finite_expansion_energy rows (rows.biUnion idealDivisors) idealDivisors
    (fun _ R => (moebius R : ℂ)) (hybridDivisorTerm κ q Pset nset bset a beta) (C * Y ^ ε)
  · intro k hk R hR
    exact Finset.mem_biUnion.mpr ⟨k, hk, hR⟩
  · intro k hk R hR
    exact HeckePort.IdealMobiusDivisorSum.norm_ideal_moebius_le_one R
  · intro k hk
    exact (hdiv k).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hrows k hk).2 hε.le) hC.le)

def doubleMaskRow (pairs : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)))
    (F : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (k : Ideal (𝓞 K)) : ℂ :=
  ∑ p ∈ pairs, (if IsCoprime k (p.1 * p.2) then 1 else 0) * F k p.1 p.2

def doubleMaskDivisorTerm (pairs : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)))
    (F : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (k : Ideal (𝓞 K))
    (D : Ideal (𝓞 K) × Ideal (𝓞 K)) : ℂ :=
  ∑ p ∈ pairs, if D.1 ∣ p.1 ∧ D.2 ∣ p.2 then F k p.1 p.2 else 0

theorem doubleMaskRow_mobius (pairs : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)))
    (F : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (k : Ideal (𝓞 K)) (hk : k ≠ ⊥) :
    doubleMaskRow pairs F k =
      ∑ D ∈ (idealDivisors k) ×ˢ (idealDivisors k),
        ((moebius D.1 : ℂ) * (moebius D.2 : ℂ)) * doubleMaskDivisorTerm pairs F k D := by
  have hm (P c : Ideal (𝓞 K)) :
      (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      ∑ D ∈ (idealDivisors k) ×ˢ (idealDivisors k),
        if D.1 ∣ P ∧ D.2 ∣ c then (moebius D.1 : ℂ) * (moebius D.2 : ℂ) else 0 := by
    rw [hybrid_double_mask_mobius k P c hk, Finset.sum_product]
  unfold doubleMaskRow
  conv_lhs => simp only [hm, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [doubleMaskDivisorTerm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : D.1 ∣ p.1 ∧ D.2 ∣ p.2 <;> simp [h]

theorem hybrid_double_mask_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y →
    ∀ (rows : Finset (Ideal (𝓞 K))) (pairs : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)))
      (F : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ),
      (∀ k ∈ rows, k ≠ ⊥ ∧ (Ideal.absNorm k : ℝ) ≤ Y) →
      (∑ k ∈ rows, ‖doubleMaskRow pairs F k‖ ^ 2) ≤
        C * Y ^ ε *
          ∑ D ∈ rows.biUnion (fun k => (idealDivisors k) ×ˢ (idealDivisors k)),
            ∑ k ∈ rows, if D ∈ (idealDivisors k) ×ˢ (idealDivisors k) then
              ‖doubleMaskDivisorTerm pairs F k D‖ ^ 2 else 0 := by
  obtain ⟨C, hC1, hdiv⟩ := ideal_divisor_count_le_rpow K (ε / 2) (by positivity)
  have hC : 0 < C := by linarith
  refine ⟨C ^ 2, pow_pos hC 2, ?_⟩
  intro Y hY rows pairs F hrows
  have he (k : Ideal (𝓞 K)) (hk : k ∈ rows) := doubleMaskRow_mobius pairs F k (hrows k hk).1
  simp_rw [Finset.sum_congr rfl (fun k hk => congrArg (fun z : ℂ => ‖z‖ ^ 2) (he k hk))]
  apply finite_expansion_energy rows
    (rows.biUnion (fun k => (idealDivisors k) ×ˢ (idealDivisors k)))
    (fun k => (idealDivisors k) ×ˢ (idealDivisors k))
    (fun _ D => (moebius D.1 : ℂ) * (moebius D.2 : ℂ))
    (doubleMaskDivisorTerm pairs F) (C ^ 2 * Y ^ ε)
  · intro k hk D hD
    exact Finset.mem_biUnion.mpr ⟨k, hk, hD⟩
  · intro k hk D hD
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul
        (HeckePort.IdealMobiusDivisorSum.norm_ideal_moebius_le_one D.1)
        (HeckePort.IdealMobiusDivisorSum.norm_ideal_moebius_le_one D.2) (norm_nonneg _)
        (by norm_num)
      _ = 1 := by norm_num
  · intro k hk
    have hd := (hdiv k).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hrows k hk).2 (by positivity)) hC.le)
    calc
      _ = ((idealDivisors k).card : ℝ) ^ 2 := by simp [Finset.card_product, pow_two]
      _ ≤ (C * Y ^ (ε / 2)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hd 2
      _ = C ^ 2 * Y ^ ε := by
        rw [mul_pow, pow_two (Y ^ (ε / 2)), ← Real.rpow_add (by linarith : 0 < Y)]
        congr 1
        congr 1
        ring

end HeckePort.Moments

end
