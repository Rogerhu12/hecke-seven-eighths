import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.RCLike
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto

/-!
Finite zero maxima for arbitrary meromorphic families.  Zeros are defined by
positive meromorphic order, so a totalized value at a pole never creates a
detector zero.  No arithmetic-specific zero-free estimate is used.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion

open Set Filter
open scoped Classical Topology

def zeroRectangle (lo hi T : ℝ) : Set ℂ :=
  {s | lo ≤ s.re ∧ s.re ≤ hi ∧ |s.im| ≤ T}

theorem zeroRectangle_compact (lo hi T : ℝ) :
    IsCompact (zeroRectangle lo hi T) := by
  have heq : zeroRectangle lo hi T = Set.Icc lo hi ×ℂ Set.Icc (-T) T := by
    ext z
    simp only [zeroRectangle, Set.mem_ofPred_eq, Complex.mem_reProdIm,
      Set.mem_Icc, abs_le]
    tauto
  rw [heq]
  exact isCompact_Icc.reProdIm isCompact_Icc

/-- Meromorphicity and one finite-order germ imply that a compact set contains
only finitely many genuine zeros.  This includes functions with poles. -/
theorem finite_positive_order_zeros {f : ℂ → ℂ}
    (hf : MeromorphicOn f Set.univ) {p : ℂ}
    (hp : meromorphicOrderAt f p ≠ ⊤) {C : Set ℂ} (hC : IsCompact C) :
    {z ∈ C | 0 < meromorphicOrderAt f z}.Finite := by
  have hfin := (MeromorphicOn.divisor f C).finiteSupport hC
  apply hfin.subset
  intro z hz
  rw [Function.mem_support,
    MeromorphicOn.divisor_apply (fun w _ => hf w (Set.mem_univ w)) hz.1]
  have hzfin : meromorphicOrderAt f z ≠ ⊤ :=
    hf.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ p) (Set.mem_univ z) hp
  intro hz0
  exact (WithTop.untop₀_eq_zero.mp hz0).elim (ne_of_gt hz.2) hzfin

structure MeromorphicFamily (ι : Type*) where
  function : ι → ℂ → ℂ
  meromorphic : ∀ i, MeromorphicOn (function i) Set.univ
  finite_at_two : ∀ i, meromorphicOrderAt (function i) (2 : ℂ) ≠ ⊤

variable {ι : Type*} [Fintype ι]

def MeromorphicFamily.zeroFinset (F : MeromorphicFamily ι) (lo hi T : ℝ)
    (i : ι) : Finset ℂ :=
  (finite_positive_order_zeros (F.meromorphic i) (F.finite_at_two i)
    (zeroRectangle_compact lo hi T)).toFinset

omit [Fintype ι] in
@[simp] theorem MeromorphicFamily.mem_zeroFinset
    (F : MeromorphicFamily ι) (lo hi T : ℝ) (i : ι) (s : ℂ) :
    s ∈ F.zeroFinset lo hi T i ↔
      lo ≤ s.re ∧ s.re ≤ hi ∧ |s.im| ≤ T ∧
        0 < meromorphicOrderAt (F.function i) s := by
  simp only [MeromorphicFamily.zeroFinset, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq, zeroRectangle]
  tauto

def MeromorphicFamily.familyZeros (F : MeromorphicFamily ι) (lo hi T : ℝ) :
    Finset (ι × ℂ) :=
  Finset.univ.biUnion fun i => (F.zeroFinset lo hi T i).image fun z => (i, z)

@[simp] theorem MeromorphicFamily.mem_familyZeros
    (F : MeromorphicFamily ι) (lo hi T : ℝ) (i : ι) (s : ℂ) :
    (i, s) ∈ F.familyZeros lo hi T ↔
      lo ≤ s.re ∧ s.re ≤ hi ∧ |s.im| ≤ T ∧
        0 < meromorphicOrderAt (F.function i) s := by
  simp [MeromorphicFamily.familyZeros]

def MeromorphicFamily.realParts (F : MeromorphicFamily ι) (lo hi T : ℝ) : Finset ℝ :=
  insert lo ((F.familyZeros lo hi T).image fun p => p.2.re)

def MeromorphicFamily.maximum (F : MeromorphicFamily ι) (lo hi T : ℝ) : ℝ :=
  (F.realParts lo hi T).max' (Finset.insert_nonempty _ _)

theorem MeromorphicFamily.maximum_mem (F : MeromorphicFamily ι) (lo hi T : ℝ) :
    F.maximum lo hi T ∈ F.realParts lo hi T :=
  Finset.max'_mem _ _

theorem MeromorphicFamily.maximum_bounds (F : MeromorphicFamily ι)
    {lo hi : ℝ} (h : lo ≤ hi) (T : ℝ) :
    lo ≤ F.maximum lo hi T ∧ F.maximum lo hi T ≤ hi := by
  constructor
  · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  · apply Finset.max'_le
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact h
    · obtain ⟨⟨i, s⟩, hs, rfl⟩ := Finset.mem_image.mp hx
      exact ((F.mem_familyZeros lo hi T i s).mp hs).2.1

theorem MeromorphicFamily.zero_re_le_maximum (F : MeromorphicFamily ι)
    {lo hi T : ℝ} {i : ι} {s : ℂ}
    (hlo : lo ≤ s.re) (hhi : s.re ≤ hi) (ht : |s.im| ≤ T)
    (hz : 0 < meromorphicOrderAt (F.function i) s) :
    s.re ≤ F.maximum lo hi T := by
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨(i, s), (F.mem_familyZeros lo hi T i s).mpr ⟨hlo, hhi, ht, hz⟩, rfl⟩)

/-- Every live maximum is attained by one of the actual family members. -/
theorem MeromorphicFamily.maximum_attained (F : MeromorphicFamily ι)
    {lo hi T : ℝ} (hmax : lo < F.maximum lo hi T) :
    ∃ i s, 0 < meromorphicOrderAt (F.function i) s ∧
      |s.im| ≤ T ∧ s.re = F.maximum lo hi T ∧ lo ≤ s.re ∧ s.re ≤ hi := by
  have hm := F.maximum_mem lo hi T
  rcases Finset.mem_insert.mp hm with hm | hm
  · exact False.elim ((ne_of_gt hmax) hm)
  · obtain ⟨⟨i, s⟩, hs, heq⟩ := Finset.mem_image.mp hm
    have hz := (F.mem_familyZeros lo hi T i s).mp hs
    exact ⟨i, s, hz.2.2.2, hz.2.2.1, heq, hz.1, hz.2.1⟩

theorem MeromorphicFamily.maximum_mono (F : MeromorphicFamily ι)
    {lo hi T T' : ℝ} (h : lo ≤ hi) (hT : T ≤ T') :
    F.maximum lo hi T ≤ F.maximum lo hi T' := by
  rcases lt_or_ge lo (F.maximum lo hi T) with hm | hm
  · obtain ⟨i, s, hz, ht, heq, hlo, hhi⟩ := F.maximum_attained hm
    rw [← heq]
    exact F.zero_re_le_maximum hlo hhi (ht.trans hT) hz
  · exact hm.trans (F.maximum_bounds h T').1

/-- A separate supplied common boundary can sharpen the maximum, without
changing its definition or discarding any zeros in the original strip. -/
theorem MeromorphicFamily.maximum_le_boundary (F : MeromorphicFamily ι)
    {lo hi T B : ℝ} (hlo : lo ≤ B)
    (hboundary : ∀ i s, lo ≤ s.re → s.re ≤ hi → |s.im| ≤ T →
      0 < meromorphicOrderAt (F.function i) s → s.re ≤ B) :
    F.maximum lo hi T ≤ B := by
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hlo
  · obtain ⟨⟨i, s⟩, hs, rfl⟩ := Finset.mem_image.mp hx
    have hz := (F.mem_familyZeros lo hi T i s).mp hs
    exact hboundary i s hz.1 hz.2.1 hz.2.2.1 hz.2.2.2

end Expansion
