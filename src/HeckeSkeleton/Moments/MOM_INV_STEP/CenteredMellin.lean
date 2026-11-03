module

public import HeckeSkeleton.Moments.MOM_INV_STEP.PositiveIntervalMellin
public import HeckeSkeleton.Moments.MOM_INV_STEP.FinalMellinTests

/-!
# Complete Mellin separation at fixed annular centers

The physical extracted product may vary in its genuine dyadic box.
Both window constructions below are fixed before those products, rows,
or labels. The same fixed center is used in the column pool and its test.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CenteredMellin

open MeasureTheory CommonKernel MellinWeightedTests
open scoped Classical BigOperators FourierTransform

structure FixedWindow where
  cutoff : ℝ → ℂ
  test : ℝ → ℝ → SchwartzMap ℝ ℂ
  scale : ∀ a t u U : ℝ, 0 < u → 0 < U →
    ((U ^ a : ℝ) : ℂ) * columnPhase t (Real.log U) * test a t (u / U) =
      cutoff (u / U) * ((u ^ a : ℝ) : ℂ) * columnPhase t (Real.log u)

def firstWindow : FixedWindow where
  cutoff := WideMellinTests.cutoff
  test := WideMellinTests.weightedTest
  scale := WideMellinTests.scaled_weighted_phase_all

def finalWindow : FixedWindow where
  cutoff := FinalMellinTests.cutoff
  test := FinalMellinTests.weightedTest
  scale := FinalMellinTests.scaled_weighted_phase_all

section Density

variable (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
variable (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc lo hi)
local notation "ρ" => PositiveIntervalMellin.density lo hi hlo hhi W hW

theorem integrable_source (v u X : ℝ) :
    Integrable (fun t : ℝ => ρ t * columnPhase t (Real.log v) *
      columnPhase t (Real.log u) * columnPhase t (-Real.log X)) := by
  let d := PositiveIntervalMellin.density lo hi hlo hhi W hW
  change Integrable (fun t : ℝ => d t * columnPhase t (Real.log v) *
    columnPhase t (Real.log u) * columnPhase t (-Real.log X))
  apply d.integrable.norm.mono' (by
    exact (((d.continuous.mul (continuous_columnPhase _)).mul
      (continuous_columnPhase _)).mul (continuous_columnPhase _)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun t => by
    simp only [norm_mul, norm_columnPhase, mul_one]
    exact le_rfl

/-- The only window condition is its value on the actual live source.
The constructed fixed windows discharge this from real norm boxes. -/
theorem separated_source_centered (T : FixedWindow)
    (a τ v u X U : ℝ) (hv : 0 < v) (hu : 0 < u) (hX : 0 < X) (hU : 0 < U)
    (hcut : T.cutoff (u / U) * W (v * u / X) = W (v * u / X)) :
    W (v * u / X) * ((u ^ a : ℝ) : ℂ) * columnPhase τ (Real.log u) =
      ∫ t : ℝ, ρ t * columnPhase t (Real.log v) * columnPhase t (-Real.log X) *
        (((U ^ a : ℝ) : ℂ) * columnPhase (t + τ) (Real.log U) *
          T.test a (t + τ) (u / U)) := by
  calc
    _ = T.cutoff (u / U) *
        (W (v * u / X) * ((u ^ a : ℝ) : ℂ) * columnPhase τ (Real.log u)) := by
      rw [← mul_assoc, ← mul_assoc, hcut]
    _ = ∫ t : ℝ, T.cutoff (u / U) *
        (ρ t * columnPhase t (Real.log v) *
          columnPhase t (Real.log u) * columnPhase t (-Real.log X) *
          ((u ^ a : ℝ) : ℂ) * columnPhase τ (Real.log u)) := by
      rw [PositiveIntervalMellin.source_inverse lo hi hlo hhi W hW v u X hv hu hX,
        integral_const_mul, integral_mul_const, integral_mul_const]
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        dsimp only
        rw [T.scale a (t + τ) u U hu hU, ← columnPhase_frequency_add]
        ring

theorem integrable_centered (T : FixedWindow)
    (a τ v u X U : ℝ) (hu : 0 < u) (hU : 0 < U) :
    Integrable (fun t : ℝ => ρ t * columnPhase t (Real.log v) *
      columnPhase t (-Real.log X) *
      (((U ^ a : ℝ) : ℂ) * columnPhase (t + τ) (Real.log U) *
        T.test a (t + τ) (u / U))) := by
  have hh := (((integrable_source lo hi hlo hhi W hW v u X).mul_const
    ((u ^ a : ℝ) : ℂ)).mul_const (columnPhase τ (Real.log u))).const_mul (T.cutoff (u / U))
  convert hh using 1
  funext t
  rw [T.scale a (t + τ) u U hu hU, ← columnPhase_frequency_add]
  ring

theorem finite_source_centered (T : FixedWindow) {ι : Type*}
    (s : Finset ι) (weight : ι → ℂ) (height : ι → ℝ)
    (a τ v X U : ℝ) (hv : 0 < v) (hX : 0 < X) (hU : 0 < U)
    (hheight : ∀ i ∈ s, 0 < height i)
    (hcut : ∀ i ∈ s, T.cutoff (height i / U) * W (v * height i / X) =
      W (v * height i / X)) :
    (∑ i ∈ s, weight i * (W (v * height i / X) *
      ((height i ^ a : ℝ) : ℂ) * columnPhase τ (Real.log (height i)))) =
    ∫ t : ℝ, ρ t * columnPhase t (Real.log v) *
      columnPhase t (-Real.log X) *
      (((U ^ a : ℝ) : ℂ) * columnPhase (t + τ) (Real.log U)) *
      ∑ i ∈ s, weight i * T.test a (t + τ) (height i / U) := by
  let F : ι → ℝ → ℂ := fun i t => weight i *
    (ρ t * columnPhase t (Real.log v) * columnPhase t (-Real.log X) *
      (((U ^ a : ℝ) : ℂ) * columnPhase (t + τ) (Real.log U) *
        T.test a (t + τ) (height i / U)))
  have hF (i : ι) (himem : i ∈ s) : Integrable (F i) :=
    (integrable_centered lo hi hlo hhi W hW T a τ v (height i) X U
      (hheight i himem) hU).const_mul _
  calc
    _ = ∑ i ∈ s, ∫ t : ℝ, F i t := by
      apply Finset.sum_congr rfl
      intro i himem
      rw [separated_source_centered lo hi hlo hhi W hW T a τ v (height i) X U
        hv (hheight i himem) hX hU (hcut i himem), integral_const_mul]
    _ = ∫ t : ℝ, ∑ i ∈ s, F i t := (integral_finsetSum s hF).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        dsimp only [F]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring

end Density

/-- The genuine extracted product v is enclosed by a fixed center V.
A nonzero original test determines the whole live normalized range. -/
theorem live_centered_window (lo hi B vcenter v u X U : ℝ)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc lo hi)
    (hB : 0 < B) (hc : 0 < vcenter) (hu : 0 < u) (hU : 0 < U)
    (hvlo : vcenter ≤ v) (hvhi : v ≤ B * vcenter)
    (hscale : X = vcenter * U) (hsrc : W (v * u / X) ≠ 0) :
    lo / B ≤ u / U ∧ u / U ≤ hi := by
  have hs := hW (subset_closure (Function.mem_support.mpr hsrc))
  have he : v * u / X = (v / vcenter) * (u / U) := by
    rw [hscale]
    field_simp [hc.ne', hU.ne']
  rw [he] at hs
  have hklo : 1 ≤ v / vcenter := (le_div_iff₀ hc).mpr (by simpa using hvlo)
  have hkhi : v / vcenter ≤ B := (div_le_iff₀ hc).mpr hvhi
  have hq : 0 ≤ u / U := (div_pos hu hU).le
  have hl := hs.1.trans (mul_le_mul_of_nonneg_right hkhi hq)
  have hr := (mul_le_mul_of_nonneg_right hklo hq).trans hs.2
  exact ⟨(div_le_iff₀ hB).mpr (by simpa only [mul_comm] using hl),
    by simpa only [one_mul] using hr⟩

theorem first_cutoff_source (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (vcenter v u X U : ℝ) (hc : 0 < vcenter) (hu : 0 < u) (hU : 0 < U)
    (hvlo : vcenter ≤ v) (hvhi : v ≤ 2 * vcenter) (hscale : X = vcenter * U) :
    firstWindow.cutoff (u / U) * W (v * u / X) = W (v * u / X) := by
  by_cases hs : W (v * u / X) = 0
  · rw [hs, mul_zero]
  · have hw := live_centered_window 1 2 2 vcenter v u X U W hW
      (by norm_num) hc hu hU hvlo hvhi hscale hs
    change WideMellinTests.cutoff (u / U) * _ = _
    rw [WideMellinTests.cutoff_one (by linarith [hw.1]) (by linarith [hw.2]), one_mul]

theorem final_cutoff_source (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8))
    (vcenter v u X U : ℝ) (hc : 0 < vcenter) (hu : 0 < u) (hU : 0 < U)
    (hvlo : vcenter ≤ v) (hvhi : v ≤ 4 * vcenter) (hscale : X = vcenter * U) :
    finalWindow.cutoff (u / U) * W (v * u / X) = W (v * u / X) := by
  by_cases hs : W (v * u / X) = 0
  · rw [hs, mul_zero]
  · have hw := live_centered_window (1 / 8) (21 / 8) 4 vcenter v u X U W hW
      (by norm_num) hc hu hU hvlo hvhi hscale hs
    change FinalMellinTests.cutoff (u / U) * _ = _
    rw [FinalMellinTests.cutoff_one (by linarith [hw.1]) (by linarith [hw.2]), one_mul]

theorem density_eq_standard (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) :
    PositiveIntervalMellin.density 1 2 (by norm_num) (by norm_num) W hW =
      MellinSeparation.density W hW := by
  unfold PositiveIntervalMellin.density MellinSeparation.density
  congr 1
  ext s
  rw [PositiveIntervalMellin.logLift_apply, MellinSeparation.logLift_apply]

end HeckeSkeleton.Moments.MOM_INV_STEP.CenteredMellin

end

