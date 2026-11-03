import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceScaleSup
import HeckeSkeleton.Moments.MOM_INV_STEP.FinalMellinTests
import HeckeSkeleton.Moments.MOM_INV_STEP.SchwartzTestPartition

/-!
# The actual fixed annular tests inside the scale-sup majorant

The ideal norm weight N(I)^(-1/2) is converted exactly to the usual
inverse-polynomial normalization at each dyadic scale.  The remaining
test is a fixed smooth annulus times the common Mellin phase and the
power y^(-1/2).  Its 24 supported pieces have one polynomial seminorm
bound selected before the row, scale and frequency.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceAnnularTests

open HeckeSkeleton.Moments.MOM_INV_STEP
open CommonKernel
open scoped Classical BigOperators

def annulus : SchwartzMap ℝ ℂ :=
  Expansion.Dyadic.annularProfile_compact.toSchwartzMap
    Expansion.Dyadic.annularProfile_smooth

@[simp] theorem annulus_apply (x : ℝ) : annulus x = Expansion.Dyadic.annularProfile x := rfl

def testCLM : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.smulLeftCLM ℂ annulus).restrictScalars ℝ

def test (t : ℝ) : SchwartzMap ℝ ℂ := testCLM (FinalMellinTests.weightedTest (-1 / 2) t)

@[simp] theorem test_apply (t x : ℝ) :
    test t x = Expansion.Dyadic.annularProfile x * FinalMellinTests.weightedTest (-1 / 2) t x := by
  exact SchwartzMap.smulLeftCLM_apply_apply annulus.hasTemperateGrowth _ _

theorem test_support (t : ℝ) : tsupport (test t) ⊆ Set.Icc (1 / 2 : ℝ) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hn : Expansion.Dyadic.annularProfile x ≠ 0 := by
    intro hz
    exact hx (by rw [test_apply, hz, zero_mul])
  exact Expansion.Dyadic.annularProfile_support hn

theorem test_wide_support (t : ℝ) : tsupport (test t) ⊆ Set.Icc (1 / 512 : ℝ) 4 := by
  intro x hx
  obtain ⟨hl, hu⟩ := test_support t hx
  exact ⟨by linarith, by linarith⟩

def piece (t : ℝ) (i : SchwartzTestPartition.Index) : SchwartzMap ℝ ℂ :=
  SchwartzTestPartition.piece (test t) (SchwartzTestPartition.exponent i)

theorem piece_support (t : ℝ) (i : SchwartzTestPartition.Index) :
    tsupport (piece t i) ⊆ Set.Icc (1 : ℝ) 2 :=
  SchwartzTestPartition.piece_support (test t) (test_wide_support t) _

theorem piece_polynomial_seminorm (q : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ∀ i : SchwartzTestPartition.Index,
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) (piece t i) ≤ C * (1 + |t|) ^ J := by
  obtain ⟨s, B, hB, hpiece⟩ := SchwartzTestPartition.exists_finite_seminorm_bound q
  let p : Seminorm ℝ (SchwartzMap ℝ ℂ) :=
    (s.sup (schwartzSeminormFamily ℝ ℝ ℂ)).comp testCLM.toLinearMap
  have hs : Continuous (fun F : SchwartzMap ℝ ℂ =>
      s.sup (schwartzSeminormFamily ℝ ℝ ℂ) F) :=
    Seminorm.continuous_finsetSup (fun i hi =>
      (schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm i)
  obtain ⟨v, A, hA, hmul⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ ℝ ℂ) p (hs.comp testCLM.continuous)
  obtain ⟨J, C, hC, htest⟩ := FinalMellinTests.finite_seminorm_polynomial_bound (-1 / 2) v
  refine ⟨J, B * (A : ℝ) * C, by positivity, ?_⟩
  intro t i
  have hm := Seminorm.le_def.mp hmul (FinalMellinTests.weightedTest (-1 / 2) t)
  change s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (test t) ≤
    (A : ℝ) * v.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (FinalMellinTests.weightedTest (-1 / 2) t) at hm
  calc
    _ ≤ B * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (test t) := hpiece (test t) i
    _ ≤ B * ((A : ℝ) * v.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (FinalMellinTests.weightedTest (-1 / 2) t)) := mul_le_mul_of_nonneg_left hm hB
    _ ≤ B * ((A : ℝ) * (C * (1 + |t|) ^ J)) := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact mul_le_mul_of_nonneg_left (htest t) A.property
    _ = _ := by ring

theorem rpow_neg_half {x : ℝ} (hx : 0 < x) :
    x ^ (-1 / 2 : ℝ) = (Real.sqrt x)⁻¹ := by
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]

/-- The scalar normalization is an equality, including points killed
by the fixed annular test. -/
theorem scaled_test (N U t : ℝ) (hN : 0 < N) (hU : 0 < U) :
    (Real.sqrt N : ℂ)⁻¹ * columnPhase t (Real.log N) *
        Expansion.Dyadic.annularProfile (N / U) =
      (Real.sqrt U : ℂ)⁻¹ * columnPhase t (Real.log U) * test t (N / U) := by
  by_cases hz : Expansion.Dyadic.annularProfile (N / U) = 0
  · rw [test_apply, hz, zero_mul, mul_zero, mul_zero]
  · have hs := Expansion.Dyadic.annularProfile_support hz
    have hp := FinalMellinTests.scaled_weighted_phase (-1 / 2) t N U hN hU
      (by linarith [hs.1]) (by linarith [hs.2])
    rw [rpow_neg_half hN, rpow_neg_half hU, Complex.ofReal_inv, Complex.ofReal_inv] at hp
    rw [hp, test_apply]
    ring

/-- The finite ideal coefficient and every arithmetic zero are unchanged
when the common prefix annulus is turned into the canonical test. -/
theorem finite_annular_eq {ι : Type*} (T : Finset ι) (a : ι → ℂ) (N : ι → ℝ)
    (hN : ∀ i ∈ T, 0 < N i) (j : ℕ) (t : ℝ) :
    SourceScaleSup.annularColumn T (fun i => a i * (Real.sqrt (N i) : ℂ)⁻¹) N j t =
      columnPhase t (Real.log ((2 : ℝ) ^ j)) * (Real.sqrt ((2 : ℝ) ^ j) : ℂ)⁻¹ *
        ∑ i ∈ T, a i * test t (N i / (2 : ℝ) ^ j) := by
  unfold SourceScaleSup.annularColumn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h := scaled_test (N i) ((2 : ℝ) ^ j) t (hN i hi) (by positivity)
  calc
    _ = a i * ((Real.sqrt (N i) : ℂ)⁻¹ * columnPhase t (Real.log (N i)) *
        Expansion.Dyadic.annularProfile (N i / (2 : ℝ) ^ j)) := by ring
    _ = _ := by rw [h]; ring

/-- The original fixed annulus is reconstructed by the actual 24
supported pieces.  The scales and the source coefficients remain exact. -/
theorem finite_test_eq_pieces {ι : Type*} (T : Finset ι) (a : ι → ℂ)
    (N : ι → ℝ) (U t : ℝ) :
    (∑ i ∈ T, a i * test t (N i / U)) =
      ∑ k : SchwartzTestPartition.Index, ∑ i ∈ T, a i *
        piece t k (N i / (SchwartzTestPartition.scale (SchwartzTestPartition.exponent k) * U)) :=
  SchwartzTestPartition.finite_source_reconstruct T a N U (test t) (test_wide_support t)

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceAnnularTests

end
