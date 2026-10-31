import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalChildren
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools
import HeckeSkeleton.Moments.MOM_INV_STEP.SchwartzDilation

/-!
# Exact clipping of a canonical child at column length zero

The positive scale is replaced by its maximum with one. A genuine
Schwartz dilation compensates this change in every column term, and the
complete squarefree pool is enlarged only where that test is zero.
No residual column coefficient or label-dependent cutoff is introduced.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ClippedChildren

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools SchwartzDilation
open scoped Classical BigOperators nonZeroDivisors

theorem clipped_scale (Z N : ℝ) (hZ : 1 ≤ Z) :
    Z ^ max 0 N = max 1 (Z ^ N) := by
  by_cases hN : 0 ≤ N
  · rw [max_eq_right hN, max_eq_right (Real.one_le_rpow hZ hN)]
  · have hN' : N ≤ 0 := le_of_not_ge hN
    have hp : Z ^ N ≤ 1 := by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hZ hN'
    rw [max_eq_left hN', max_eq_left hp, Real.rpow_zero]

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "Ext" => ExteriorIdeal K S
variable {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

def clippedFamily (C : ColumnFamily K S σ Θ ψ) (hZ : 1 < C.base) :
    ColumnFamily K S σ Θ ψ :=
  { C with
    columns := fun γ => squarefreePool K S (2 * max 1 (C.base ^ C.columnLength γ))
    columns_squarefree := fun _ _ hn => squarefreePool_squarefree K S hn
    cutoff := fun γ =>
      dilate (max 1 (C.base ^ C.columnLength γ) / (C.base ^ C.columnLength γ))
        (div_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)) (C.cutoff γ)
    columnLength := fun γ => max 0 (C.columnLength γ) }

theorem clipped_length_nonneg (C : ColumnFamily K S σ Θ ψ) (hZ : 1 < C.base)
    (γ : OuterTriple K) : 0 ≤ (clippedFamily K S C hZ).columnLength γ := le_max_left _ _

theorem original_pool_subset (C : ColumnFamily K S σ Θ ψ) (hZ : 1 < C.base)
    (γ : OuterTriple K)
    (hpool : C.columns γ = squarefreePool K S (2 * C.base ^ C.columnLength γ)) :
    C.columns γ ⊆ (clippedFamily K S C hZ).columns γ := by
  intro n hn
  rw [hpool, mem_squarefreePool] at hn
  apply (mem_squarefreePool K S _ n).mpr
  refine ⟨hn.1, hn.2.trans ?_⟩
  have hh := le_max_right (1 : ℝ) (C.base ^ C.columnLength γ)
  nlinarith

theorem live_scale_bound (C : ColumnFamily K S σ Θ ψ) (γ : OuterTriple K)
    (hpool : C.columns γ = squarefreePool K S (2 * C.base ^ C.columnLength γ))
    (hlive : (C.columns γ).Nonempty) :
    1 ≤ 4 * C.base ^ C.columnLength γ := by
  obtain ⟨n, hn⟩ := hlive
  rw [hpool, mem_squarefreePool] at hn
  have hh := height_one_le K S n
  linarith [hn.2]

variable (D : ThetaArithmeticData K S)
variable {Sector : Type*} (sectorUnit : Sector → S.unit K)

theorem column_eq_clipped (C : ColumnFamily K S σ Θ ψ) (hZ : 1 < C.base)
    (γ : OuterTriple K) (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector)
    (hpool : C.columns γ = squarefreePool K S (2 * C.base ^ C.columnLength γ))
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc (0 : ℝ) 4) :
    column K S D C sectorUnit γ f k =
      column K S D (clippedFamily K S C hZ) sectorUnit γ f k := by
  let U := C.base ^ C.columnLength γ
  have hU : 0 < U := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  let a := max 1 U / U
  have ha : 0 < a := div_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hU
  let F : Ext → ℂ := fun n =>
    CoefficientCycle.canonicalCoefficient K S D C.lambda n *
      heckeIdealCoefficient K (C.background γ) n.val *
      (if IsCoprime n.val.val (childPuncture C.originalPuncture γ) then 1 else 0) *
      sectorRow K S D sectorUnit n k * labelRow K S D n f ^ 4 *
      divisorMark (C.survivors γ) C.primeLists C.primeWeights n.val.val
  change (∑ n ∈ C.columns γ, F n * C.cutoff γ (height K S n / U)) =
    ∑ n ∈ squarefreePool K S (2 * max 1 U),
      F n * dilate a ha (C.cutoff γ) (height K S n / C.base ^ max 0 (C.columnLength γ))
  rw [clipped_scale C.base (C.columnLength γ) hZ.le]
  simp_rw [clip_test_identity U hU]
  apply Finset.sum_subset (original_pool_subset K S C hZ γ hpool)
  intro n hn hnold
  have hsf := (mem_squarefreePool K S (2 * max 1 U) n).mp hn
  have hlarge : 4 * U < height K S n := by
    by_contra hh
    apply hnold
    rw [hpool, mem_squarefreePool]
    exact ⟨hsf.1, by dsimp only [U] at *; linarith⟩
  have hzero : C.cutoff γ (height K S n / U) = 0 := by
    by_contra hz
    have hh := hW (subset_closure (Function.mem_support.mpr hz))
    have hd : 4 < height K S n / U := (lt_div_iff₀ hU).mpr (by linarith)
    linarith [hh.2]
  rw [hzero, mul_zero]

theorem clipped_test_support (C : ColumnFamily K S σ Θ ψ) (hZ : 1 < C.base)
    (γ : OuterTriple K) (lo hi : ℝ) (hlo : 0 ≤ lo)
    (hpool : C.columns γ = squarefreePool K S (2 * C.base ^ C.columnLength γ))
    (hlive : (C.columns γ).Nonempty)
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc lo hi) :
    tsupport ((clippedFamily K S C hZ).cutoff γ) ⊆ Set.Icc (lo / 4) hi := by
  have hU := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (C.columnLength γ)
  have hb := clip_dilation_bounds _ hU (live_scale_bound K S C γ hpool hlive)
  exact tsupport_dilate_subset _ 4 lo hi
    (div_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hU)
    hb.1 hb.2 hlo (C.cutoff γ) hW

/-- Clipping has a fixed seminorm cost before any moving data. -/
theorem exists_clipped_test_seminorm_bound (s : Finset (ℕ × ℕ)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (C : ColumnFamily K S σ Θ ψ) (hZ : 1 < C.base)
      (γ : OuterTriple K),
      C.columns γ = squarefreePool K S (2 * C.base ^ C.columnLength γ) →
      (C.columns γ).Nonempty →
      s.sup (schwartzSeminormFamily ℝ ℝ ℂ) ((clippedFamily K S C hZ).cutoff γ) ≤
        A * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (C.cutoff γ) := by
  obtain ⟨A, hA, hb⟩ := finite_seminorm_dilate_le 4 (by norm_num) s
  refine ⟨A, hA, ?_⟩
  intro C hZ γ hpool hlive
  have hU := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (C.columnLength γ)
  have ha := clip_dilation_bounds _ hU (live_scale_bound K S C γ hpool hlive)
  exact hb _ (div_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hU)
    ha.1 ha.2 (C.cutoff γ)

/-- A nonempty genuine norm pool bounds the negative formal length.
The only size threshold is the fixed scalar four absorbed into eta. -/
theorem clipping_loss (C : ColumnFamily K S σ Θ ψ) (hZ : 1 < C.base)
    (γ : OuterTriple K) (eta : ℝ) (heta : 0 ≤ eta)
    (hfour : 4 ≤ C.base ^ (6 * eta))
    (hpool : C.columns γ = squarefreePool K S (2 * C.base ^ C.columnLength γ))
    (hlive : (C.columns γ).Nonempty) :
    max 0 (C.columnLength γ) - C.columnLength γ ≤ 6 * eta := by
  have hscale := live_scale_bound K S C γ hpool hlive
  have hpos := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (C.columnLength γ)
  have hh : C.base ^ (0 : ℝ) ≤ C.base ^ (C.columnLength γ + 6 * eta) := by
    rw [Real.rpow_zero, Real.rpow_add (zero_lt_one.trans hZ)]
    calc
      _ ≤ 4 * C.base ^ C.columnLength γ := hscale
      _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_right hfour hpos.le
  have he := (Real.rpow_le_rpow_left_iff hZ).mp hh
  rw [← max_sub_sub_right]
  exact max_le (by linarith) (by linarith)

end HeckeSkeleton.Moments.MOM_INV_STEP.ClippedChildren

end

