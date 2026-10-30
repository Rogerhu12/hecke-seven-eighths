import HeckePort.Moments.Descent.IdealMasks
import HeckePort.CenteredMoment.Generator
import Mathlib.Algebra.BigOperators.Group.Finset.Preimage

/-!
# Hybrid column decomposition

Port of openai/math `OAI/NumberTheory/DirichletL/Descent/Decomposition.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

The only changed statement is `HybridColumnData.primary_factors`. Over `ℤ[ω]` it says that the
primary generator of the factors is nonzero, i.e. the ideals are prime to `3`; over a general
field the corresponding condition is that the ideals are exterior (no prime factor in `S`), so it
becomes `HybridColumnData.exterior_factors` with `IsExterior K S`
(`HeckePort.CenteredMomentGenerator`).
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators
open UniqueFactorizationMonoid HeckePort.CenteredMomentGenerator

variable {K : Type} [Field K] [NumberField K]

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

/-- General-field form of openai's `HybridColumnData.primary_factors`: exteriority replaces
non-vanishing of the primary generator. -/
theorem HybridColumnData.exterior_factors (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (d : HybridColumnData K)
    (hn : IsExterior K S (d.common * d.residualN))
    (hb : IsExterior K S ((d.common * d.residualB) * d.square ^ 2)) :
    IsExterior K S d.common ∧ IsExterior K S d.residualN ∧ IsExterior K S d.residualB ∧
    IsExterior K S d.square ∧ IsExterior K S (d.common * d.square) := by
  obtain ⟨hc, hm⟩ := (isExterior_mul_iff K S).mp hn
  obtain ⟨hch, hsq⟩ := (isExterior_mul_iff K S).mp hb
  obtain ⟨_, hh⟩ := (isExterior_mul_iff K S).mp hch
  have ht : IsExterior K S d.square := by
    refine ⟨d.square_ne_zero, fun p hp => hsq.2 p (dvd_pow hp (by decide : (2 : ℕ) ≠ 0))⟩
  exact ⟨hc, hm, hh, ht, (isExterior_mul_iff K S).mpr ⟨hc, ht⟩⟩

theorem HybridColumnData.residual_norm_identity (d : HybridColumnData K) :
    (Ideal.absNorm (d.residualN * d.residualB) : ℝ) =
      ((Ideal.absNorm (d.common * d.residualN) : ℝ) *
        (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ)) /
      ((Ideal.absNorm d.common : ℝ) ^ 2 * (Ideal.absNorm d.square : ℝ) ^ 2) := by
  have hc : (Ideal.absNorm d.common : ℝ) ≠ 0 := by
    exact_mod_cast (fun hz => d.common_ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
  have ht : (Ideal.absNorm d.square : ℝ) ≠ 0 := by
    exact_mod_cast (fun hz => d.square_ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
  field_simp

theorem HybridColumnData.residual_norm_bounds (d : HybridColumnData K)
    (N B C T : ℝ) (hN : 0 ≤ N) (_hB : 0 ≤ B) (hC : 0 < C) (hT : 0 < T)
    (hn : (Ideal.absNorm (d.common * d.residualN) : ℝ) ≤ N)
    (hb : (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B)
    (hc : C ≤ (Ideal.absNorm d.common : ℝ))
    (ht : T ≤ (Ideal.absNorm d.square : ℝ)) :
    (Ideal.absNorm d.residualN : ℝ) ≤ N / C ∧
    (Ideal.absNorm d.residualB : ℝ) ≤ B / (C * T ^ 2) ∧
    (Ideal.absNorm (d.residualN * d.residualB) : ℝ) ≤ N * B / (C ^ 2 * T ^ 2) := by
  have hn' := hn
  have hb' := hb
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] at hn' hb'
  have hm : (Ideal.absNorm d.residualN : ℝ) ≤ N / C := by
    apply (le_div_iff₀ hC).mpr
    calc
      _ ≤ (Ideal.absNorm d.common : ℝ) * (Ideal.absNorm d.residualN : ℝ) := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hc
          (Nat.cast_nonneg (Ideal.absNorm d.residualN))
      _ ≤ N := hn'
  have hh : (Ideal.absNorm d.residualB : ℝ) ≤ B / (C * T ^ 2) := by
    apply (le_div_iff₀ (mul_pos hC (sq_pos_of_pos hT))).mpr
    calc
      _ ≤ (Ideal.absNorm d.common : ℝ) * (Ideal.absNorm d.residualB : ℝ) *
          (Ideal.absNorm d.square : ℝ) ^ 2 := by
        calc
          _ = C * (Ideal.absNorm d.residualB : ℝ) * T ^ 2 := by ring
          _ ≤ _ := by gcongr
      _ ≤ B := hb'
  refine ⟨hm, hh, ?_⟩
  calc
    _ = (Ideal.absNorm d.residualN : ℝ) * (Ideal.absNorm d.residualB : ℝ) := by
      rw [map_mul, Nat.cast_mul]
    _ ≤ (N / C) * (B / (C * T ^ 2)) :=
      mul_le_mul hm hh (Nat.cast_nonneg _) (div_nonneg hN hC.le)
    _ = N * B / (C ^ 2 * T ^ 2) := by ring

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

end HeckePort.Moments

end
