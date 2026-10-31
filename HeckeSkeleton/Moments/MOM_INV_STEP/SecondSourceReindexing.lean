import HeckeSkeleton.Moments.MOM_INV_STEP.ActualInverseFactors
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools

/-!
# Exact reindexing of the fresh second source

The common factor is computed from the two original squarefree source
ideals. Reconstruction is inverse to this computation only while the
two residual ideals are mutually coprime. The later full Möbius
extension keeps this common factor fixed.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceReindexing

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ActualInverseFactors CanonicalNormPools IdealMobiusMask FirstSourceDecomposition
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "Ext" => ExteriorIdeal K S

theorem squarefree_exteriorMul (g z : Ext)
    (hg : Squarefree g.val.val) (hz : Squarefree z.val.val)
    (hc : IsCoprime g.val.val z.val.val) :
    Squarefree (exteriorMul K S g z).val.val :=
  squarefree_mul_iff.mpr ⟨hc.isRelPrime, hg, hz⟩

theorem residuals_coprime (x₁ x₂ : Ext) :
    IsCoprime (residual K S x₁ x₂).val.val (residual K S x₂ x₁).val.val := by
  apply primeProduct_coprime
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_sdiff.mp hq).1

theorem common_of_products (g z₁ z₂ : Ext)
    (hg : Squarefree g.val.val) (hz₁ : Squarefree z₁.val.val)
    (hz₂ : Squarefree z₂.val.val) (hc₁ : IsCoprime g.val.val z₁.val.val)
    (hc₂ : IsCoprime g.val.val z₂.val.val) (hc : IsCoprime z₁.val.val z₂.val.val) :
    common K S (exteriorMul K S g z₁) (exteriorMul K S g z₂) = g := by
  apply Subtype.ext
  apply Subtype.ext
  rw [common_eq_gcd K S _ _ (squarefree_exteriorMul K S g z₁ hg hz₁ hc₁)
    (squarefree_exteriorMul K S g z₂ hg hz₂ hc₂)]
  change gcd (g.val.val * z₁.val.val) (g.val.val * z₂.val.val) = g.val.val
  rw [Ideal.gcd_eq_sup, ← Ideal.mul_sup, hc.sup_eq]
  exact mul_one _

theorem residual_of_products (g z₁ z₂ : Ext)
    (hg : Squarefree g.val.val) (hz₁ : Squarefree z₁.val.val)
    (hz₂ : Squarefree z₂.val.val) (hc₁ : IsCoprime g.val.val z₁.val.val)
    (hc₂ : IsCoprime g.val.val z₂.val.val) (hc : IsCoprime z₁.val.val z₂.val.val) :
    residual K S (exteriorMul K S g z₁) (exteriorMul K S g z₂) = z₁ := by
  have hf := common_mul_residual K S (exteriorMul K S g z₁) (exteriorMul K S g z₂)
    (squarefree_exteriorMul K S g z₁ hg hz₁ hc₁)
  rw [common_of_products K S g z₁ z₂ hg hz₁ hz₂ hc₁ hc₂ hc] at hf
  apply Subtype.ext
  apply Subtype.ext
  apply mul_left_cancel₀ (nonZeroDivisors.coe_ne_zero g.val)
  exact congrArg (fun x : Ext => x.val.val) hf

theorem factors_of_products (g z₁ z₂ : Ext)
    (hg : Squarefree g.val.val) (hz₁ : Squarefree z₁.val.val)
    (hz₂ : Squarefree z₂.val.val) (hc₁ : IsCoprime g.val.val z₁.val.val)
    (hc₂ : IsCoprime g.val.val z₂.val.val) (hc : IsCoprime z₁.val.val z₂.val.val) :
    common K S (exteriorMul K S g z₁) (exteriorMul K S g z₂) = g ∧
      residual K S (exteriorMul K S g z₁) (exteriorMul K S g z₂) = z₁ ∧
      residual K S (exteriorMul K S g z₂) (exteriorMul K S g z₁) = z₂ :=
  ⟨common_of_products K S g z₁ z₂ hg hz₁ hz₂ hc₁ hc₂ hc,
    residual_of_products K S g z₁ z₂ hg hz₁ hz₂ hc₁ hc₂ hc,
    residual_of_products K S g z₂ z₁ hg hz₂ hz₁ hc₂ hc₁ hc.symm⟩

def decomposePair (p : Ext × Ext) : Ext × Ext × Ext :=
  (common K S p.1 p.2, residual K S p.1 p.2, residual K S p.2 p.1)

def reconstructPair (p : Ext × Ext × Ext) : Ext × Ext :=
  (exteriorMul K S p.1 p.2.1, exteriorMul K S p.1 p.2.2)

theorem reconstruct_decompose (p : Ext × Ext)
    (hp₁ : Squarefree p.1.val.val) (hp₂ : Squarefree p.2.val.val) :
    reconstructPair K S (decomposePair K S p) = p := by
  apply Prod.ext
  · exact common_mul_residual K S p.1 p.2 hp₁
  · change exteriorMul K S (common K S p.1 p.2) (residual K S p.2 p.1) = p.2
    rw [common_comm]
    exact common_mul_residual K S p.2 p.1 hp₂

theorem decomposePair_injectiveOn_squarefree :
    Set.InjOn (decomposePair K S)
      {p : Ext × Ext | Squarefree p.1.val.val ∧ Squarefree p.2.val.val} := by
  intro p hp q hq he
  simpa only [reconstruct_decompose K S p hp.1 hp.2,
    reconstruct_decompose K S q hq.1 hq.2] using congrArg (reconstructPair K S) he


theorem common_height_le_left (x₁ x₂ : Ext) (hx₁ : Squarefree x₁.val.val) :
    height K S (common K S x₁ x₂) ≤ height K S x₁ := by
  have he := congrArg (height K S) (common_mul_residual K S x₁ x₂ hx₁)
  rw [height_mul] at he
  calc
    _ ≤ height K S (common K S x₁ x₂) * height K S (residual K S x₁ x₂) :=
      le_mul_of_one_le_right (height_pos K S _).le (height_one_le K S _)
    _ = _ := he

theorem residual_height (x₁ x₂ : Ext) (hx₁ : Squarefree x₁.val.val) :
    height K S (residual K S x₁ x₂) =
      height K S x₁ / height K S (common K S x₁ x₂) := by
  apply (eq_div_iff (height_pos K S _).ne').mpr
  rw [mul_comm, ← height_mul, common_mul_residual K S x₁ x₂ hx₁]

def compatible (g z₁ z₂ : Ext) : Prop :=
  IsCoprime g.val.val z₁.val.val ∧ IsCoprime g.val.val z₂.val.val ∧
    IsCoprime z₁.val.val z₂.val.val

def commonKeys (N : ℝ) : Finset (Σ _g : Ext, Ext × Ext) :=
  (squarefreePool K S N).sigma fun g =>
    ((squarefreePool K S (N / height K S g)) ×ˢ
      squarefreePool K S (N / height K S g)).filter
        (fun z => compatible K S g z.1 z.2)

def pairKey (p : Ext × Ext) : Σ _g : Ext, Ext × Ext :=
  ⟨common K S p.1 p.2, residual K S p.1 p.2, residual K S p.2 p.1⟩

def reconstructKey (k : Σ _g : Ext, Ext × Ext) : Ext × Ext :=
  (exteriorMul K S k.1 k.2.1, exteriorMul K S k.1 k.2.2)

theorem reconstruct_pairKey (p : Ext × Ext)
    (hp₁ : Squarefree p.1.val.val) (hp₂ : Squarefree p.2.val.val) :
    reconstructKey K S (pairKey K S p) = p :=
  reconstruct_decompose K S p hp₁ hp₂

theorem pairKey_mem (N : ℝ) (p : Ext × Ext)
    (hp : p ∈ squarefreePool K S N ×ˢ squarefreePool K S N) :
    pairKey K S p ∈ commonKeys K S N := by
  obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
  obtain ⟨hs₁, hn₁⟩ := (mem_squarefreePool K S N p.1).mp hp₁
  obtain ⟨hs₂, hn₂⟩ := (mem_squarefreePool K S N p.2).mp hp₂
  have hg : common K S p.1 p.2 ∈ squarefreePool K S N :=
    (mem_squarefreePool K S N _).mpr
      ⟨common_squarefree K S p.1 p.2, (common_height_le_left K S p.1 p.2 hs₁).trans hn₁⟩
  have hz₁ : residual K S p.1 p.2 ∈
      squarefreePool K S (N / height K S (common K S p.1 p.2)) := by
    apply (mem_squarefreePool K S _ _).mpr
    refine ⟨residual_squarefree K S _ _, ?_⟩
    rw [residual_height K S p.1 p.2 hs₁]
    calc
      _ ≤ (2 * N) / height K S (common K S p.1 p.2) :=
        div_le_div_of_nonneg_right hn₁ (height_pos K S _).le
      _ = _ := by ring
  have hz₂ : residual K S p.2 p.1 ∈
      squarefreePool K S (N / height K S (common K S p.1 p.2)) := by
    apply (mem_squarefreePool K S _ _).mpr
    refine ⟨residual_squarefree K S _ _, ?_⟩
    rw [residual_height K S p.2 p.1 hs₂, common_comm K S p.2 p.1]
    calc
      _ ≤ (2 * N) / height K S (common K S p.1 p.2) :=
        div_le_div_of_nonneg_right hn₂ (height_pos K S _).le
      _ = _ := by ring
  apply Finset.mem_sigma.mpr
  refine ⟨hg, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hz₁, hz₂⟩, ?_⟩⟩
  exact ⟨common_residual_coprime K S p.1 p.2,
    by rw [common_comm]; exact common_residual_coprime K S p.2 p.1,
    residuals_coprime K S p.1 p.2⟩

theorem reconstructKey_mem (N : ℝ) (k : Σ _g : Ext, Ext × Ext)
    (hk : k ∈ commonKeys K S N) :
    reconstructKey K S k ∈ squarefreePool K S N ×ˢ squarefreePool K S N := by
  obtain ⟨hg, hz⟩ := Finset.mem_sigma.mp hk
  obtain ⟨hz, hc⟩ := Finset.mem_filter.mp hz
  obtain ⟨hz₁, hz₂⟩ := Finset.mem_product.mp hz
  obtain ⟨hgs, _hgn⟩ := (mem_squarefreePool K S N k.1).mp hg
  obtain ⟨hz₁s, hz₁n⟩ := (mem_squarefreePool K S _ k.2.1).mp hz₁
  obtain ⟨hz₂s, hz₂n⟩ := (mem_squarefreePool K S _ k.2.2).mp hz₂
  have hn (z : Ext) (hz : height K S z ≤ 2 * (N / height K S k.1)) :
      height K S (exteriorMul K S k.1 z) ≤ 2 * N := by
    rw [height_mul]
    calc
      _ ≤ height K S k.1 * (2 * (N / height K S k.1)) :=
        mul_le_mul_of_nonneg_left hz (height_pos K S k.1).le
      _ = _ := by field_simp
  exact Finset.mem_product.mpr
    ⟨(mem_squarefreePool K S N _).mpr
      ⟨squarefree_exteriorMul K S k.1 k.2.1 hgs hz₁s hc.1, hn _ hz₁n⟩,
      (mem_squarefreePool K S N _).mpr
      ⟨squarefree_exteriorMul K S k.1 k.2.2 hgs hz₂s hc.2.1, hn _ hz₂n⟩⟩

theorem pairKey_reconstruct (N : ℝ) (k : Σ _g : Ext, Ext × Ext)
    (hk : k ∈ commonKeys K S N) :
    pairKey K S (reconstructKey K S k) = k := by
  obtain ⟨hg, hz⟩ := Finset.mem_sigma.mp hk
  obtain ⟨hz, hc⟩ := Finset.mem_filter.mp hz
  obtain ⟨hz₁, hz₂⟩ := Finset.mem_product.mp hz
  have hf := factors_of_products K S k.1 k.2.1 k.2.2
    ((mem_squarefreePool K S _ _).mp hg).1
    ((mem_squarefreePool K S _ _).mp hz₁).1
    ((mem_squarefreePool K S _ _).mp hz₂).1 hc.1 hc.2.1 hc.2.2
  cases k with
  | mk g z =>
    rcases z with ⟨z₁, z₂⟩
    simp only [pairKey, reconstructKey, hf.1, hf.2.1, hf.2.2]

/-- Exact finite reindexing of the original fresh pair.  The three
coprimality conditions are conclusions of its computed gcd splitting. -/
theorem sum_pairs_by_common (N : ℝ) (_hN : 0 ≤ N) (F : Ext → Ext → ℂ) :
    (∑ x₁ ∈ squarefreePool K S N, ∑ x₂ ∈ squarefreePool K S N, F x₁ x₂) =
      ∑ g ∈ squarefreePool K S N,
        ∑ z₁ ∈ squarefreePool K S (N / height K S g),
          ∑ z₂ ∈ squarefreePool K S (N / height K S g),
            if compatible K S g z₁ z₂ then
              F (exteriorMul K S g z₁) (exteriorMul K S g z₂) else 0 := by
  have he :
      (∑ p ∈ squarefreePool K S N ×ˢ squarefreePool K S N, F p.1 p.2) =
        ∑ k ∈ commonKeys K S N, F (reconstructKey K S k).1 (reconstructKey K S k).2 := by
    apply Finset.sum_bij (fun p _ => pairKey K S p)
    · intro p hp
      exact pairKey_mem K S N p hp
    · intro p hp q hq he
      have hp' := Finset.mem_product.mp hp
      have hq' := Finset.mem_product.mp hq
      have hr := congrArg (reconstructKey K S) he
      simpa only [reconstruct_pairKey K S p
        ((mem_squarefreePool K S _ _).mp hp'.1).1 ((mem_squarefreePool K S _ _).mp hp'.2).1,
        reconstruct_pairKey K S q
        ((mem_squarefreePool K S _ _).mp hq'.1).1 ((mem_squarefreePool K S _ _).mp hq'.2).1] using hr
    · intro k hk
      exact ⟨reconstructKey K S k, reconstructKey_mem K S N k hk, pairKey_reconstruct K S N k hk⟩
    · intro p hp
      obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
      rw [reconstruct_pairKey K S p
        ((mem_squarefreePool K S _ _).mp hp₁).1 ((mem_squarefreePool K S _ _).mp hp₂).1]
  simpa only [Finset.sum_product, commonKeys, Finset.sum_sigma, Finset.sum_filter,
    reconstructKey] using he
end HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceReindexing

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondDyadicReindexing

open HeckeGeneral.Arithmetic HeckeGeneral.ThetaSkeleton.Global

/-- Compatibility name for the fresh-pair factorization used by the
retained-source caller. -/
theorem factors_of_products := @SecondSourceReindexing.factors_of_products

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondDyadicReindexing

end
