import HeckeSkeleton.LowHybrid.NormalFormKernels

/-!
# Original support inherited by the exact normal-form coefficients

The original norm cutoffs are recovered from membership in the actual image
supports. These lemmas are used before discarding or estimating coefficients.
-/

namespace HeckeSkeleton.LowHybrid.NormalForm

open scoped BigOperators Classical
noncomputable section

variable {I : Type*} [CommMonoid I]

namespace Arithmetic

variable (S : Arithmetic I)

theorem markQuotients_mul_mem {marks : Finset I} {d p : I}
    (hp : p ∈ S.markQuotients marks d) : d * p ∈ marks := by
  obtain ⟨P, hP, hquot⟩ := Finset.mem_image.mp hp
  have hd := (Finset.mem_filter.mp hP).2
  have hmem := (Finset.mem_filter.mp hP).1
  rw [← hquot, S.quotient_spec d P hd]
  exact hmem

theorem blockSupport_original_mem {columns cubes : Finset I}
    (C : Completion columns cubes) {r : I} {v : CompletedIndex I}
    (hv : v ∈ S.blockSupport C.support r) :
    r * v.2.1 * v.2.2.1 ∈ columns ∧
      r * v.2.1 * v.2.2.2 * v.1 ^ 2 ∈ cubes := by
  have h := C.mem_support_recombine (S.blockSupport_restore_mem hv)
  simpa only [restoreCommon, recombine, Finset.mem_product] using h

theorem blockBeta_ne_zero_mem (beta : I → I → ℂ)
    (support : Finset (CompletedIndex I)) (d r t c m h : I)
    (hb : S.blockBeta beta support d r t c m h ≠ 0) :
    (t, c, m, h) ∈ S.blockSupport support r := by
  by_contra hn
  simp only [blockBeta, if_neg hn] at hb
  exact hb rfl

/-- Nonzero transformed coefficients retain both original support cutoffs. -/
theorem blockBeta_ne_zero_original_mem {columns cubes : Finset I}
    (C : Completion columns cubes) (beta : I → I → ℂ) (d r t c m h : I)
    (hb : S.blockBeta beta C.support d r t c m h ≠ 0) :
    r * c * m ∈ columns ∧ r * c * h * t ^ 2 ∈ cubes :=
  S.blockSupport_original_mem C (S.blockBeta_ne_zero_mem beta C.support d r t c m h hb)

/-- The exact cube norm relation needed for the weighted support budget. -/
theorem completed_cube_norm (r t c h : I) :
    S.normI (r * c * h * t ^ 2) =
      S.normI r * S.normI c * S.normI h * S.normI t ^ 2 := by
  simp only [pow_two, S.norm_mul]

theorem completed_column_norm (r c m : I) :
    S.normI (r * c * m) = S.normI r * S.normI c * S.normI m := by
  simp only [S.norm_mul]

theorem blockBeta_cube_support {columns cubes : Finset I}
    (C : Completion columns cubes) (beta : I → I → ℂ) (B : ℝ)
    (hB : ∀ b ∈ cubes, S.normI b ≤ B) (d r t c m h : I)
    (hb : S.blockBeta beta C.support d r t c m h ≠ 0) :
    S.normI r * S.normI c * S.normI h * S.normI t ^ 2 ≤ B := by
  have hm := (S.blockBeta_ne_zero_original_mem C beta d r t c m h hb).2
  simpa only [S.completed_cube_norm] using hB _ hm

theorem blockBeta_column_support {columns cubes : Finset I}
    (C : Completion columns cubes) (beta : I → I → ℂ) (N : ℝ)
    (hN : ∀ n ∈ columns, S.normI n ≤ N) (d r t c m h : I)
    (hb : S.blockBeta beta C.support d r t c m h ≠ 0) :
    S.normI r * S.normI c * S.normI m ≤ N := by
  have hm := (S.blockBeta_ne_zero_original_mem C beta d r t c m h hb).1
  simpa only [S.completed_column_norm] using hN _ hm

end Arithmetic

#print axioms Arithmetic.blockBeta_cube_support
#print axioms Arithmetic.blockBeta_column_support

end
end HeckeSkeleton.LowHybrid.NormalForm
