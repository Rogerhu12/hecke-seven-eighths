import HeckeSkeleton.LowHybrid.NormalFormAlgebra

/-!
# Exact finite reindexings for the hybrid normal form

Completed indices are `(t,c,m,h)`. The only decomposition hypothesis is a
reconstruction identity for each original `(n,b)` in its finite support.
Every new support is explicitly the image of that support. Thus none of the
following equalities relies on an assumed analytic normal-form statement.
-/

namespace HeckeSkeleton.LowHybrid.NormalForm

open scoped BigOperators Classical
noncomputable section

variable {I : Type*} [CommMonoid I]

abbrev CompletedIndex (I : Type*) := I × I × I × I

def recombine (v : CompletedIndex I) : I × I :=
  (v.2.1 * v.2.2.1, v.2.1 * v.2.2.2 * v.1 ^ 2)

/-- A chosen canonical completion on the actual original finite support.
Reconstruction implies injectivity of the chosen split; no multiplicity is
introduced when its image becomes the new summation set. -/
structure Completion (columns cubes : Finset I) where
  split : I × I → CompletedIndex I
  reconstruct : ∀ x ∈ columns ×ˢ cubes, recombine (split x) = x

namespace Completion

variable {columns cubes : Finset I} (C : Completion columns cubes)

def support : Finset (CompletedIndex I) := (columns ×ˢ cubes).image C.split

theorem split_injective_on : Set.InjOn C.split ↑(columns ×ˢ cubes) := by
  intro x hx y hy hxy
  calc
    x = recombine (C.split x) := (C.reconstruct x hx).symm
    _ = recombine (C.split y) := congrArg recombine hxy
    _ = y := C.reconstruct y hy

theorem sum_reindex (F : I → I → ℂ) :
    (∑ n ∈ columns, ∑ b ∈ cubes, F n b) =
      ∑ v ∈ C.support, F (recombine v).1 (recombine v).2 := by
  calc
    _ = ∑ x ∈ columns ×ˢ cubes, F x.1 x.2 := (Finset.sum_product ..).symm
    _ = _ := by
      unfold support
      rw [Finset.sum_image C.split_injective_on]
      apply Finset.sum_congr rfl
      intro x hx
      rw [C.reconstruct x hx]

theorem mem_support_recombine {v : CompletedIndex I} (hv : v ∈ C.support) :
    recombine v ∈ columns ×ˢ cubes := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
  simpa only [C.reconstruct x hx] using hx

end Completion

namespace Arithmetic

variable (S : Arithmetic I)

def quotientCommon (r : I) (v : CompletedIndex I) : CompletedIndex I :=
  (v.1, S.quotient r v.2.1, v.2.2.1, v.2.2.2)

def restoreCommon (_S : Arithmetic I) (r : I) (v : CompletedIndex I) : CompletedIndex I :=
  (v.1, r * v.2.1, v.2.2.1, v.2.2.2)

theorem restore_quotient_common (r : I) (v : CompletedIndex I)
    (h : r ∣ v.2.1) : S.restoreCommon r (S.quotientCommon r v) = v := by
  rcases v with ⟨t, c, m, h'⟩
  simp only [restoreCommon, quotientCommon, S.quotient_spec r c h]

/-- This support is independent of the moving row and the moving mark. -/
def blockSupport (support : Finset (CompletedIndex I)) (r : I) :
    Finset (CompletedIndex I) :=
  (support.filter fun v => r ∣ v.2.1).image (S.quotientCommon r)

theorem sum_common_reindex (support : Finset (CompletedIndex I)) (r : I)
    (F : CompletedIndex I → ℂ) :
    (∑ v ∈ support with r ∣ v.2.1, F v) =
      ∑ v ∈ S.blockSupport support r, F (S.restoreCommon r v) := by
  unfold blockSupport
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro v hv
    rw [S.restore_quotient_common r v (Finset.mem_filter.mp hv).2]
  · intro v hv w hw h
    calc
      v = S.restoreCommon r (S.quotientCommon r v) :=
        (S.restore_quotient_common r v (Finset.mem_filter.mp hv).2).symm
      _ = S.restoreCommon r (S.quotientCommon r w) := congrArg (S.restoreCommon r) h
      _ = w := S.restore_quotient_common r w (Finset.mem_filter.mp hw).2

theorem blockSupport_restore_mem {support : Finset (CompletedIndex I)}
    {r : I} {v : CompletedIndex I} (hv : v ∈ S.blockSupport support r) :
    S.restoreCommon r v ∈ support := by
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
  rw [S.restore_quotient_common r w (Finset.mem_filter.mp hw).2]
  exact (Finset.mem_filter.mp hw).1

/-- Expand the second entire moving mask on the completed index set. -/
theorem mask_common_expansion (support : Finset (CompletedIndex I)) (k : I)
    (F : CompletedIndex I → ℂ) :
    (∑ v ∈ support, S.mask k v.2.1 * F v) =
      ∑ r ∈ S.divisors k, S.mu r * ∑ v ∈ support with r ∣ v.2.1, F v := by
  calc
    _ = ∑ v ∈ support, ∑ r ∈ S.divisors k,
        (if r ∣ v.2.1 then S.mu r else 0) * F v := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [S.mask_symm k v.2.1, mask, S.mobius_expansion, Finset.sum_mul]
    _ = ∑ r ∈ S.divisors k, ∑ v ∈ support,
        (if r ∣ v.2.1 then S.mu r else 0) * F v := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v hv
      by_cases h : r ∣ v.2.1 <;> simp [h]

end Arithmetic

def completedBox (ts cs ms hs : Finset I) : Finset (CompletedIndex I) :=
  ts ×ˢ (cs ×ˢ (ms ×ˢ hs))

/-- A completed support may be placed in a rectangle only by literal zero
extension. Its original joint support is retained in the coefficient. -/
theorem sum_zero_extend_box (support : Finset (CompletedIndex I))
    (ts cs ms hs : Finset I) (hsub : support ⊆ completedBox ts cs ms hs)
    (F : CompletedIndex I → ℂ) :
    (∑ v ∈ support, F v) =
      ∑ t ∈ ts, ∑ c ∈ cs, ∑ m ∈ ms, ∑ h ∈ hs,
        if (t, c, m, h) ∈ support then F (t, c, m, h) else 0 := by
  have hf : (completedBox ts cs ms hs).filter (fun v => v ∈ support) = support := by
    ext v
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  calc
    _ = ∑ v ∈ completedBox ts cs ms hs, if v ∈ support then F v else 0 := by
      rw [← Finset.sum_filter, hf]
    _ = _ := by simp only [completedBox, Finset.sum_product]

end
end HeckeSkeleton.LowHybrid.NormalForm
