import HeckeSkeleton.SmallRadius.SmallRadiusJointCompactBound
import HeckeGeneral.Analysis.TraceJointSchwartzCutoff

/-!
UNCOMPILED / native 0. Reconstruction of actual cutoff Schwartz seminorms
from the all-radius compact orbital bound. This uses the existing literal
cutoff-times-joint-kernel Schwartz function. Both columns remain present.
The Leibniz and support arguments follow the verified large-radius proof in
TraceJointSchwartzCutoff, now supplied by a bound with no radius threshold.
-/

noncomputable section

namespace HeckeGeneral.Analysis.SmallRadiusCutoffSeminormDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open SmallRadiusJointCompactDraft
open scoped Classical ContDiff BigOperators

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
  LanglandsTunnell.TateLocal.borelSpace_localBorel

variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : S, MeasurableSpace (v.val.adicCompletion K)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion K)ˣ]
variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Ω" => Set.prod (traceArchRegular K) (traceArchRegular K)

include Γ in
/-- Fixed compact regular cutoff, genuine joint orbital kernel, arbitrary
positive radius. The finite original seminorms and constant precede phi/R/n. -/
theorem exists_traceCutoffOrbitalSchwartz_seminorm_allRadius_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (χ : V × V → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupport : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (k J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, ∀ n : ℕ, n ≤ J →
        SchwartzMap.seminorm ℝ k n
          (traceCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport χ hχ hχsupport hχΩ φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-σ) := by
  obtain ⟨s, C, hCpos, hkernel⟩ := exists_traceJointOrbitalKernel_compact_allRadius_bound
    K S Γ ψ hψ hψsupport (tsupport χ) hχsupport hχΩ σ hσ hσ1 J
  have hC : 0 ≤ C := hCpos.le
  obtain ⟨L, hL, hcutoff⟩ := exists_traceCutoff_derivative_bound K χ hχ hχsupport J
  obtain ⟨H, hH⟩ := hχsupport.bddAbove_image (continuous_norm.continuousOn)
  let W : ℝ := max H 0
  have hW : 0 ≤ W := le_max_right _ _
  have hweight (p : V × V) (hp : p ∈ tsupport χ) : ‖p‖ ^ k ≤ W ^ k :=
    pow_le_pow_left₀ (norm_nonneg _)
      ((hH (Set.mem_image_of_mem _ hp)).trans (le_max_left _ _)) k
  have hfactor : 0 ≤ W ^ k * (2 : ℝ) ^ J * L * C :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hW _) (by positivity)) hL) hC
  refine ⟨s, W ^ k * (2 : ℝ) ^ J * L * C, hfactor, fun φ R n hn => ?_⟩
  let Q : ℝ := C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-σ)
  have hQ : 0 ≤ Q :=
    mul_nonneg (mul_nonneg hC (apply_nonneg _ _)) (Real.rpow_nonneg R.property.le _)
  have hnorm (p : V × V) (hp : p ∈ tsupport χ) :
      ‖iteratedFDeriv ℝ n (traceCutoffOrbitalKernel K S χ φ ψ R) p‖ ≤
        (2 : ℝ) ^ J * L * Q := by
    have hleib := norm_iteratedFDeriv_traceCutoffOrbitalKernel_le
      K S Γ χ hχ φ ψ hψ hψsupport R n (hχΩ hp)
    have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ p‖ *
          ‖iteratedFDeriv ℝ (n - i) (traceJointOrbitalKernel K S φ ψ R) p‖ := hleib
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * L * Q := by
        apply Finset.sum_le_sum
        intro i hi
        have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hcutoff i (hin.trans hn) p)
          (Nat.cast_nonneg _))
          (hkernel φ R p hp (n - i) ((Nat.sub_le n i).trans hn))
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hL)
      _ = (2 : ℝ) ^ n * L * Q := by rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
      _ ≤ (2 : ℝ) ^ J * L * Q :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hL) hQ
  have hfinal : 0 ≤ (W ^ k * (2 : ℝ) ^ J * L * C) *
      s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-σ) :=
    mul_nonneg (mul_nonneg hfactor (apply_nonneg _ _)) (Real.rpow_nonneg R.property.le _)
  apply SchwartzMap.seminorm_le_bound ℝ k n _ hfinal
  intro p
  change ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (traceCutoffOrbitalKernel K S χ φ ψ R) p‖ ≤ _
  by_cases hp : p ∈ tsupport χ
  · calc
      _ ≤ W ^ k * ((2 : ℝ) ^ J * L * Q) :=
        mul_le_mul (hweight p hp) (hnorm p hp) (norm_nonneg _) (pow_nonneg hW _)
      _ = (W ^ k * (2 : ℝ) ^ J * L * C) *
          s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-σ) := by dsimp [Q]; ring
  · rw [iteratedFDeriv_traceCutoffOrbitalKernel_zero K S χ φ ψ R n hp, norm_zero, mul_zero]
    exact hfinal

end HeckeGeneral.Analysis.SmallRadiusCutoffSeminormDraft
