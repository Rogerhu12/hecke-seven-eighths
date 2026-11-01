import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderSelectedTail
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionBlocks
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools

/-!
# Exact retained rectangles and their genuine complementary tail

Rectangles are selected by their two lower dyadic endpoints. Thus the
hybrid blocks keep separate full column sets. The complement is proved
to lie in the actual off-threshold range; no coupled column mask is
silently removed from a complex sum.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalRectangles

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools
open HeckeSkeleton.LowEnergy.ActualReflection
  HeckeSkeleton.LowEnergy.ActualReflectionReindex HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open CubeCompletionBlocks
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "Ext" => ExteriorIdeal K S

def indices (R : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.range (count (2 * max 1 R))) ×ˢ
    (Finset.range (count (2 * max 1 R)))).filter
      (fun j => scale j.1 * scale j.2 ^ 3 ≤ R)

def key (cb : Ext × Ext) : ℕ × ℕ :=
  (index (exteriorNorm K S cb.1), index (exteriorNorm K S cb.2))

def retained (R : ℝ) (cb : Ext × Ext) : Prop := key K S cb ∈ indices R

def pool (R : ℝ) : Finset Ext := boundedPool K S (max 1 R)

def annulus (R : ℝ) (j : ℕ) : Finset Ext :=
  CubeCompletionBlocks.block (pool K S R) (exteriorNorm K S) j

theorem mem_pool (R : ℝ) (I : Ext) :
    I ∈ pool K S R ↔ exteriorNorm K S I ≤ 2 * max 1 R := by
  simp only [pool, boundedPool, Finset.mem_preimage,
    DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals]
  rfl

theorem norm_one_le (I : Ext) : 1 ≤ exteriorNorm K S I :=
  height_one_le K S I

theorem retained_bounds (R : ℝ) (cb : Ext × Ext) (hcb : retained K S R cb) :
    exteriorNorm K S cb.1 ≤ 2 * max 1 R ∧
      exteriorNorm K S cb.2 ≤ 2 * max 1 R := by
  have hscale := (Finset.mem_filter.mp hcb).2
  have hc := norm_window (exteriorNorm K S cb.1) (norm_one_le K S cb.1)
  have hb := norm_window (exteriorNorm K S cb.2) (norm_one_le K S cb.2)
  have hc1 := scale_one_le (index (exteriorNorm K S cb.1))
  have hb1 := scale_one_le (index (exteriorNorm K S cb.2))
  change scale (index (exteriorNorm K S cb.1)) *
    scale (index (exteriorNorm K S cb.2)) ^ 3 ≤ R at hscale
  have hbp : scale (index (exteriorNorm K S cb.2)) ≤
      scale (index (exteriorNorm K S cb.2)) ^ 3 := le_self_pow₀ hb1 (by norm_num)
  have hcp : scale (index (exteriorNorm K S cb.1)) ≤ R :=
    (le_mul_of_one_le_right (scale_pos _).le (one_le_pow₀ hb1)).trans hscale
  have hbr : scale (index (exteriorNorm K S cb.2)) ≤ R :=
    hbp.trans ((le_mul_of_one_le_left (pow_nonneg (scale_pos _).le 3) hc1).trans hscale)
  exact ⟨hc.2.le.trans (by linarith [le_max_right 1 R]),
    hb.2.le.trans (by linarith [le_max_right 1 R])⟩

/-- Every point outside the selected rectangles has large full-cube
product, including points outside the finite norm pool. -/
theorem omitted_large (R : ℝ) (cb : Ext × Ext) (hcb : ¬retained K S R cb) :
    R < exteriorNorm K S cb.1 * exteriorNorm K S cb.2 ^ 3 := by
  by_contra hn
  have hprod := le_of_not_gt hn
  have hc1 := norm_one_le K S cb.1
  have hb1 := norm_one_le K S cb.2
  have hbp : exteriorNorm K S cb.2 ≤ exteriorNorm K S cb.2 ^ 3 :=
    le_self_pow₀ hb1 (by norm_num)
  have hcR : exteriorNorm K S cb.1 ≤ 2 * max 1 R := by
    have hh : exteriorNorm K S cb.1 ≤ R :=
      (le_mul_of_one_le_right (exteriorNorm_pos K S cb.1).le (one_le_pow₀ hb1)).trans hprod
    linarith [le_max_right 1 R, le_max_left 1 R]
  have hbR : exteriorNorm K S cb.2 ≤ 2 * max 1 R := by
    have hh : exteriorNorm K S cb.2 ≤ R :=
      hbp.trans ((le_mul_of_one_le_left
        (pow_nonneg (exteriorNorm_pos K S cb.2).le 3) hc1).trans hprod)
    linarith [le_max_right 1 R, le_max_left 1 R]
  apply hcb
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
  · exact Finset.mem_range.mpr (index_lt_count _ _ hc1 hcR)
  · exact Finset.mem_range.mpr (index_lt_count _ _ hb1 hbR)
  · exact (mul_le_mul (norm_window _ hc1).1
      (pow_le_pow_left₀ (scale_pos _).le (norm_window _ hb1).1 3)
      (pow_nonneg (scale_pos _).le 3) (exteriorNorm_pos K S cb.1).le).trans hprod

def retainedPool (R : ℝ) : Finset (Ext × Ext) :=
  ((pool K S R) ×ˢ (pool K S R)).filter (retained K S R)

theorem mem_retainedPool (R : ℝ) (cb : Ext × Ext) :
    cb ∈ retainedPool K S R ↔ retained K S R cb := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    obtain ⟨hc, hb⟩ := retained_bounds K S R cb h
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(mem_pool K S R cb.1).mpr hc, (mem_pool K S R cb.2).mpr hb⟩, h⟩

theorem fiber_eq_rectangle (R : ℝ) (j : ℕ × ℕ) (hj : j ∈ indices R) :
    (retainedPool K S R).filter (fun cb => key K S cb = j) =
      (annulus K S R j.1) ×ˢ (annulus K S R j.2) := by
  ext cb
  simp only [Finset.mem_filter, retainedPool, Finset.mem_product,
    annulus, CubeCompletionBlocks.mem_block, Prod.mk.injEq, key]
  constructor
  · rintro ⟨⟨⟨hc, hb⟩, hr⟩, hi, hj'⟩
    exact ⟨⟨hc, hi⟩, ⟨hb, hj'⟩⟩
  · rintro ⟨⟨hc, hi⟩, ⟨hb, hj'⟩⟩
    refine ⟨⟨⟨hc, hb⟩, ?_⟩, hi, hj'⟩
    change (index (exteriorNorm K S cb.1), index (exteriorNorm K S cb.2)) ∈ indices R
    simpa only [hi, hj'] using hj

theorem sum_retained_eq_rectangles (R : ℝ) (F : Ext × Ext → ℂ) :
    (∑ cb ∈ retainedPool K S R, F cb) =
      ∑ j ∈ indices R, ∑ c ∈ annulus K S R j.1,
        ∑ b ∈ annulus K S R j.2, F (c, b) := by
  have h := Finset.sum_fiberwise_of_maps_to
    (fun cb (hcb : cb ∈ retainedPool K S R) =>
      (mem_retainedPool K S R cb).mp hcb) F
  calc
    _ = ∑ j ∈ indices R,
        ∑ cb ∈ (retainedPool K S R).filter (fun cb => key K S cb = j), F cb := h.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [fiber_eq_rectangle K S R j hj, Finset.sum_product]

/-- Exact source identity. Every rectangular block is kept as a
complex sum, and the complementary range is separately summable. -/
theorem tsum_eq_rectangles_add_tail (R : ℝ) (F : Ext × Ext → ℂ) (hF : Summable F) :
    (∑' cb, F cb) =
      (∑ j ∈ indices R, ∑ c ∈ annulus K S R j.1,
        ∑ b ∈ annulus K S R j.2, F (c, b)) +
      ∑' cb, if ¬retained K S R cb then F cb else 0 := by
  let g : Ext × Ext → ℂ := fun cb => if cb ∈ retainedPool K S R then F cb else 0
  have hg : Summable g := summable_of_ne_finset_zero (s := retainedPool K S R)
    (fun cb hcb => if_neg hcb)
  have hrest : (fun cb => if ¬retained K S R cb then F cb else 0) = F - g := by
    funext cb
    simp only [Pi.sub_apply, g, mem_retainedPool]
    split_ifs <;> simp_all
  rw [hrest, hF.tsum_sub hg]
  have hgSum : (∑' cb, g cb) = ∑ cb ∈ retainedPool K S R, F cb := by
    rw [tsum_eq_sum (s := retainedPool K S R) (fun cb hcb => if_neg hcb)]
    exact Finset.sum_congr rfl (fun cb hcb => if_pos hcb)
  rw [hgSum, sum_retained_eq_rectangles K S R F]
  ring

theorem annulus_window {Z : ℝ} (hZ : 1 < Z) (R : ℝ) (j : ℕ)
    (I : Ext) (hI : I ∈ annulus K S R j) :
    GeneralReflectedEnergy.InAnnulus K S Z (Real.logb Z (scale j)) I := by
  rw [GeneralReflectedEnergy.InAnnulus,
    Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (scale_pos j)]
  exact block_window (pool K S R) (exteriorNorm K S) j
    (fun I _ => norm_one_le K S I) I hI

theorem retained_lengths {Z T : ℝ} (hZ : 1 < Z) (j : ℕ × ℕ)
    (hj : j ∈ indices (Z ^ T)) :
    Real.logb Z (scale j.1) + 3 * Real.logb Z (scale j.2) ≤ T := by
  have hp := (Finset.mem_filter.mp hj).2
  have hh := (Real.logb_le_iff_le_rpow hZ
    (mul_pos (scale_pos j.1) (pow_pos (scale_pos j.2) 3))).mpr hp
  simpa only [Real.logb_mul (scale_pos j.1).ne' (pow_pos (scale_pos j.2) 3).ne',
    Real.logb_pow, Nat.cast_ofNat] using hh

theorem indices_card_bound (R : ℝ) :
    ((indices R).card : ℝ) ≤ (count (2 * max 1 R) : ℝ) ^ 2 := by
  have h := Finset.card_le_card (Finset.filter_subset
    (fun j : ℕ × ℕ => scale j.1 * scale j.2 ^ 3 ≤ R)
    ((Finset.range (count (2 * max 1 R))) ×ˢ (Finset.range (count (2 * max 1 R)))))
  rw [Finset.card_product, Finset.card_range, Finset.card_range] at h
  have hc : ((indices R).card : ℝ) ≤
      (count (2 * max 1 R) : ℝ) * (count (2 * max 1 R) : ℝ) := by
    exact_mod_cast h
  simpa only [pow_two] using hc

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalRectangles

end
