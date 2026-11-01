import HeckeSkeleton.LowEnergy.IdealDivisorMasks
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Preimage
import Lean.Elab.Tactic.Omega

/-!
# Pure actual-ideal canonical columns and raw hybrid reconstruction

The square extraction, uniqueness and finite row reconstruction proofs are
adapted from the supplied HeckePort `IdealMasks`, `Decomposition`, `Hybrid`
and `Reconstruction` files.  Only Mathlib and the independently proved
actual-ideal divisor module are imported.  Every ideal, product, gcd and
norm is the actual object in `𝓞 K`.
-/

noncomputable section
namespace HeckeSkeleton.LowEnergy.IdealCanonicalColumns

open NumberField Ideal UniqueFactorizationMonoid
open HeckeSkeleton.LowEnergy.KeepOriginalRow
open scoped NumberField Classical BigOperators
variable {K : Type} [Field K] [NumberField K]

theorem gcd_eq_iff_quotient_coprime (D I J : Ideal (𝓞 K)) (hD : D ≠ ⊥)
    (hDI : D ∣ I) (hDJ : D ∣ J) :
    gcd I J = D ↔ IsCoprime (idealQuotient D I) (idealQuotient D J) := by
  have he : gcd I J = D * gcd (idealQuotient D I) (idealQuotient D J) := by
    calc
      gcd I J = gcd (D * idealQuotient D I) (D * idealQuotient D J) := by
        rw [idealQuotient_mul hDI, idealQuotient_mul hDJ]
      _ = _ := by rw [_root_.gcd_mul_left, normalize_eq]
  rw [he, Ideal.isCoprime_iff_gcd]
  constructor
  · intro h
    exact mul_left_cancel₀ hD (h.trans (mul_one D).symm)
  · intro h
    rw [h, mul_one]

/-- Square part of an ideal (`I = squarePart I ^ 2 * squarefreePart I`). -/
def squarePart (I : Ideal (𝓞 K)) : Ideal (𝓞 K) := (exists_sq_mul_squarefree I).choose

def squarefreePart (I : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  (exists_sq_mul_squarefree I).choose_spec.choose

theorem squarePart_sq_mul_squarefreePart (I : Ideal (𝓞 K)) :
    squarePart I ^ 2 * squarefreePart I = I :=
  (exists_sq_mul_squarefree I).choose_spec.choose_spec.1

theorem squarefree_squarefreePart (I : Ideal (𝓞 K)) : Squarefree (squarefreePart I) :=
  (exists_sq_mul_squarefree I).choose_spec.choose_spec.2

theorem squarePart_ne_zero {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : squarePart I ≠ ⊥ := by
  intro hz
  have h := squarePart_sq_mul_squarefreePart I
  rw [hz, ← Ideal.zero_eq_bot, zero_pow (by decide : 2 ≠ 0), zero_mul] at h
  exact hI h.symm

theorem squarefree_decomposition_unique {A B D E : Ideal (𝓞 K)}
    (hA : A ≠ ⊥) (hB : B ≠ ⊥) (hD : Squarefree D) (hE : Squarefree E)
    (h : A ^ 2 * D = B ^ 2 * E) : A = B ∧ D = E := by
  have hf := congrArg normalizedFactors h
  rw [normalizedFactors_mul (pow_ne_zero _ hA) hD.ne_zero,
    normalizedFactors_mul (pow_ne_zero _ hB) hE.ne_zero,
    normalizedFactors_pow, normalizedFactors_pow] at hf
  have hd := (squarefree_iff_nodup_normalizedFactors hD.ne_zero).mp hD
  have he := (squarefree_iff_nodup_normalizedFactors hE.ne_zero).mp hE
  have hcount (P : Ideal (𝓞 K)) :
      (normalizedFactors A).count P = (normalizedFactors B).count P ∧
      (normalizedFactors D).count P = (normalizedFactors E).count P := by
    have hc := congrArg (Multiset.count P) hf
    simp only [Multiset.count_add, Multiset.count_nsmul] at hc
    have hd1 := Multiset.nodup_iff_count_le_one.mp hd P
    have he1 := Multiset.nodup_iff_count_le_one.mp he P
    omega
  constructor
  · apply associated_iff_eq.mp
    apply (associated_iff_normalizedFactors_eq_normalizedFactors hA hB).mpr
    exact Multiset.ext.mpr (fun P => (hcount P).1)
  · apply associated_iff_eq.mp
    apply (associated_iff_normalizedFactors_eq_normalizedFactors hD.ne_zero hE.ne_zero).mpr
    exact Multiset.ext.mpr (fun P => (hcount P).2)

theorem hybrid_column_decomposition
    (n b : Ideal (𝓞 K)) (hn : Squarefree n) (hb : b ≠ ⊥) :
    ∃ c m h t : Ideal (𝓞 K),
      n = c * m ∧ b = (c * h) * t ^ 2 ∧
      Squarefree c ∧ Squarefree m ∧ Squarefree h ∧
      IsRelPrime c m ∧ IsRelPrime c h ∧ IsCoprime m h ∧ t ≠ ⊥ := by
  let g := squarefreePart b
  let t := squarePart b
  let c := gcd n g
  let m := idealQuotient c n
  let h := idealQuotient c g
  have hg : Squarefree g := squarefree_squarefreePart b
  have hcn : c ∣ n := gcd_dvd_left n g
  have hcg : c ∣ g := gcd_dvd_right n g
  have hc : c ≠ ⊥ := ne_zero_of_dvd_ne_zero hn.ne_zero hcn
  have hnm : n = c * m := (idealQuotient_mul hcn).symm
  have hgh : g = c * h := (idealQuotient_mul hcg).symm
  have hbgt : b = g * t ^ 2 := by
    rw [mul_comm]
    exact (squarePart_sq_mul_squarefreePart b).symm
  obtain ⟨hcm, hcs, hms⟩ := squarefree_mul_iff.mp (hnm ▸ hn)
  obtain ⟨hch, _, hhs⟩ := squarefree_mul_iff.mp (hgh ▸ hg)
  have hmh : IsCoprime m h :=
    (gcd_eq_iff_quotient_coprime c n g hc hcn hcg).mp rfl
  exact ⟨c, m, h, t, hnm, by rw [hbgt, hgh], hcs, hms, hhs, hcm, hch, hmh,
    squarePart_ne_zero hb⟩


structure HybridColumnData (K : Type) [Field K] [NumberField K] where
  common : Ideal (𝓞 K)
  residualN : Ideal (𝓞 K)
  residualB : Ideal (𝓞 K)
  square : Ideal (𝓞 K)
  n_squarefree : Squarefree (common * residualN)
  g_squarefree : Squarefree (common * residualB)
  residual_coprime : IsCoprime residualN residualB
  square_ne_zero : square ≠ ⊥

def HybridColumnData.reconstruct (d : HybridColumnData K) : Ideal (𝓞 K) × Ideal (𝓞 K) :=
  (d.common * d.residualN, (d.common * d.residualB) * d.square ^ 2)

theorem HybridColumnData.common_ne_zero (d : HybridColumnData K) : d.common ≠ ⊥ :=
  ne_zero_of_dvd_ne_zero d.n_squarefree.ne_zero (dvd_mul_right _ _)

theorem HybridColumnData.common_eq_gcd (d : HybridColumnData K) :
    d.common = gcd (d.common * d.residualN) (d.common * d.residualB) := by
  rw [gcd_mul_left, normalize_eq, Ideal.isCoprime_iff_gcd.mp d.residual_coprime, mul_one]

theorem HybridColumnData.residual_product_squarefree (d : HybridColumnData K) :
    Squarefree (d.residualN * d.residualB) := by
  have hm := (squarefree_mul_iff.mp d.n_squarefree).2.2
  have hh := (squarefree_mul_iff.mp d.g_squarefree).2.2
  exact squarefree_mul_iff.mpr ⟨d.residual_coprime.isRelPrime, hm, hh⟩

theorem HybridColumnData.reconstruct_injective :
    Function.Injective (HybridColumnData.reconstruct (K := K)) := by
  intro d e he
  have hn : d.common * d.residualN = e.common * e.residualN := congrArg Prod.fst he
  have hb : d.square ^ 2 * (d.common * d.residualB) =
      e.square ^ 2 * (e.common * e.residualB) := by
    simpa only [HybridColumnData.reconstruct, mul_comm] using congrArg Prod.snd he
  obtain ⟨ht, hg⟩ := squarefree_decomposition_unique
    d.square_ne_zero e.square_ne_zero d.g_squarefree e.g_squarefree hb
  have hc : d.common = e.common := by
    calc
      _ = gcd (d.common * d.residualN) (d.common * d.residualB) := d.common_eq_gcd
      _ = gcd (e.common * e.residualN) (e.common * e.residualB) := by rw [hn, hg]
      _ = e.common := e.common_eq_gcd.symm
  rw [hc] at hn hg
  have hm := mul_left_cancel₀ e.common_ne_zero hn
  have hh := mul_left_cancel₀ e.common_ne_zero hg
  cases d
  cases e
  cases hc
  cases hm
  cases hh
  cases ht
  rfl

def HybridColumnData.toOriginal (d : HybridColumnData K) :
    {p : Ideal (𝓞 K) × Ideal (𝓞 K) // Squarefree p.1 ∧ p.2 ≠ ⊥} :=
  ⟨d.reconstruct, d.n_squarefree,
    mul_ne_zero d.g_squarefree.ne_zero (pow_ne_zero 2 d.square_ne_zero)⟩

theorem HybridColumnData.toOriginal_bijective :
    Function.Bijective (HybridColumnData.toOriginal (K := K)) := by
  constructor
  · intro d e he
    exact reconstruct_injective (congrArg Subtype.val he)
  · intro p
    obtain ⟨c, m, h, t, hn, hb, hcs, hms, hhs, hcm, hch, hmh, ht⟩ :=
      hybrid_column_decomposition p.val.1 p.val.2 p.property.1 p.property.2
    refine ⟨⟨c, m, h, t, ?_, ?_, hmh, ht⟩, ?_⟩
    · exact hn ▸ p.property.1
    · exact squarefree_mul_iff.mpr ⟨hch, hcs, hhs⟩
    · apply Subtype.ext
      exact Prod.ext hn.symm hb.symm

def hybridColumnEquiv : HybridColumnData K ≃
    {p : Ideal (𝓞 K) × Ideal (𝓞 K) // Squarefree p.1 ∧ p.2 ≠ ⊥} :=
  Equiv.ofBijective HybridColumnData.toOriginal HybridColumnData.toOriginal_bijective

theorem hybrid_column_reindex (f : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) :
    (∑' p : {p : Ideal (𝓞 K) × Ideal (𝓞 K) // Squarefree p.1 ∧ p.2 ≠ ⊥}, f p.val.1 p.val.2) =
      ∑' d : HybridColumnData K,
        f (d.common * d.residualN) ((d.common * d.residualB) * d.square ^ 2) := by
  exact (hybridColumnEquiv.tsum_eq (fun p => f p.val.1 p.val.2)).symm

def hybridColumnSupport (S : Finset (Ideal (𝓞 K) × Ideal (𝓞 K))) : Finset (HybridColumnData K) :=
  S.preimage HybridColumnData.reconstruct HybridColumnData.reconstruct_injective.injOn

@[simp] theorem mem_hybridColumnSupport (S : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)))
    (d : HybridColumnData K) :
    d ∈ hybridColumnSupport S ↔ d.reconstruct ∈ S := Finset.mem_preimage

theorem hybrid_finite_column_reindex {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)))
    (hS : ∀ p ∈ S, Squarefree p.1 ∧ p.2 ≠ ⊥)
    (f : Ideal (𝓞 K) × Ideal (𝓞 K) → A) :
    (∑ p ∈ S, f p) = ∑ d ∈ hybridColumnSupport S, f d.reconstruct := by
  symm
  apply Finset.sum_preimage
  intro p hp hn
  obtain ⟨d, hd⟩ := HybridColumnData.toOriginal_bijective.surjective ⟨p, hS p hp⟩
  exact (hn ⟨d, congrArg Subtype.val hd⟩).elim


structure CubicKernelAxioms (Ext : Ideal (𝓞 K) → Prop) (κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) :
    Prop where
  mul_left : ∀ R P n, κ (R * P) n = κ R n * κ P n
  mul_right : ∀ P n m, Ext P → κ P (n * m) = κ P n * κ P m
  norm_le_one : ∀ P n, ‖κ P n‖ ≤ 1
  eq_zero_of_not_coprime : ∀ P n, Ext P → Ext n → ¬ IsCoprime P n → κ P n = 0

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

def hybridInner (κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (nset bset : Finset (Ideal (𝓞 K)))
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (k P : Ideal (𝓞 K)) : ℂ :=
  ∑ n ∈ nset, ∑ b ∈ bset,
    beta n b * q k (n * b) * κ P n * (if IsCoprime P b then 1 else 0)

def hybridRow (κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (Pset nset bset : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (k : Ideal (𝓞 K)) : ℂ :=
  ∑ P ∈ Pset, a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
    (if IsCoprime k P then 1 else 0) * hybridInner κ q nset bset beta k P

def supportedHybridRow (κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (S : Finset (Ideal (𝓞 K) × Ideal (𝓞 K))) (Pset : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (k : Ideal (𝓞 K)) : ℂ :=
  ∑ p ∈ S, ∑ P ∈ Pset, a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * beta p.1 p.2 *
    (q k (p.1 * p.2) * κ P p.1 *
      (if IsCoprime P p.2 then 1 else 0) * (if IsCoprime k P then 1 else 0))

theorem supportedHybridRow_product (κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (nset bset Pset : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (k : Ideal (𝓞 K)) :
    supportedHybridRow κ q (nset ×ˢ bset) Pset a beta k = hybridRow κ q Pset nset bset a beta k := by
  simp only [supportedHybridRow, hybridRow, hybridInner, Finset.sum_product,
    Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext n
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  ring

def reconstructedHybridTerm (κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (a : Ideal (𝓞 K) → ℂ)
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (k : Ideal (𝓞 K)) (P : Ideal (𝓞 K))
    (d : HybridColumnData K) : ℂ :=
  a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
    beta (d.common * d.residualN) ((d.common * d.residualB) * d.square ^ 2) *
    ((if IsCoprime k d.square then 1 else 0) *
      (if IsCoprime k (P * d.common) then 1 else 0) *
      q k (d.residualN * d.residualB) *
      κ P (d.common * d.residualN) *
      (if IsCoprime P (d.residualB * d.square) then 1 else 0))

theorem supportedHybridRow_reconstruct {Ext : Ideal (𝓞 K) → Prop}
    {κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ} (hκ : CubicKernelAxioms Ext κ)
    (S : Finset (Ideal (𝓞 K) × Ideal (𝓞 K))) (Pset : Finset (Ideal (𝓞 K)))
    (hS : ∀ p ∈ S, Squarefree p.1 ∧ p.2 ≠ ⊥ ∧ Ext p.1 ∧ Ext p.2)
    (hP : ∀ P ∈ Pset, Ext P)
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (k : Ideal (𝓞 K))
    (hsq : ∀ d : HybridColumnData K, d.reconstruct ∈ S →
      q k ((d.common * d.residualN) * ((d.common * d.residualB) * d.square ^ 2)) =
        (if IsCoprime k (d.common * d.square) then 1 else 0) *
          q k (d.residualN * d.residualB)) :
    supportedHybridRow κ q S Pset a beta k =
      ∑ d ∈ hybridColumnSupport S, ∑ P ∈ Pset, reconstructedHybridTerm κ q a beta k P d := by
  unfold supportedHybridRow
  rw [hybrid_finite_column_reindex S (fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩)]
  apply Finset.sum_congr rfl
  intro d hd
  have hdS := (mem_hybridColumnSupport S d).mp hd
  have hdprim := hS d.reconstruct hdS
  apply Finset.sum_congr rfl
  intro P hPP
  unfold reconstructedHybridTerm
  exact congrArg
    (fun z : ℂ => a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
      beta (d.common * d.residualN) ((d.common * d.residualB) * d.square ^ 2) * z)
    (hybrid_original_kernel_decomposition hκ k P
    (d.common * d.residualN) ((d.common * d.residualB) * d.square ^ 2)
    d.common d.residualN d.residualB d.square (hP P hPP) hdprim.2.2.1 rfl rfl (hsq d hdS))


#print axioms HybridColumnData.reconstruct_injective
#print axioms hybrid_finite_column_reindex
#print axioms supportedHybridRow_reconstruct

end HeckeSkeleton.LowEnergy.IdealCanonicalColumns
end
