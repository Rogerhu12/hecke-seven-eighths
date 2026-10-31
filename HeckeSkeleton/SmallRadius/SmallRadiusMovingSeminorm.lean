import HeckeSkeleton.SmallRadius.SmallRadiusCutoffSeminorm
import HeckeGeneral.Analysis.TraceMovingPhaseBounds

/-!
UNCOMPILED / native 0. The actual moving Mellin phase is included BEFORE
Fourier transformation. Uniform all-positive-radius control is obtained
from the cutoff bound and the proved compact derivative bounds of the
same phase. Constants and original test seminorms are selected before
nu, phi and R; the loss in nu is the actual polynomial (1+|nu|)^J.
The Leibniz argument is adapted from verified TraceMovingPhaseBounds.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeGeneral.Analysis.SmallRadiusMovingSeminormDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open SmallRadiusCutoffSeminormDraft
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
/-- Uniform moving-phase Schwartz seminorm bound with no radius threshold. -/
theorem exists_traceMovingCutoffOrbitalSchwartz_seminorm_allRadius_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (χ : V × V → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupport : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (k J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r},
      ∀ n : ℕ, n ≤ J →
        SchwartzMap.seminorm ℝ k n
          (traceMovingCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport χ hχ hχsupport hχΩ ν φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-σ) := by
  obtain ⟨s, C, hC, hcutoff⟩ := exists_traceCutoffOrbitalSchwartz_seminorm_allRadius_bound
    K S Γ ψ hψ hψsupport χ hχ hχsupport hχΩ σ hσ hσ1 k J
  obtain ⟨L, hL, hphase⟩ := exists_traceMovingPhase_compact_derivative_bound
    K (tsupport χ) hχsupport hχΩ J
  have hfactor : 0 ≤ (2 : ℝ) ^ J * L * C :=
    mul_nonneg (mul_nonneg (by positivity) hL) hC
  refine ⟨s, (2 : ℝ) ^ J * L * C, hfactor, fun ν φ R n hn => ?_⟩
  let P : ℝ := L * (1 + |ν|) ^ J
  let Q : ℝ := C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-σ)
  have hP : 0 ≤ P := mul_nonneg hL (pow_nonneg (by positivity) _)
  have hQ : 0 ≤ Q :=
    mul_nonneg (mul_nonneg hC (apply_nonneg _ _)) (Real.rpow_nonneg R.property.le _)
  have hfinal : 0 ≤ ((2 : ℝ) ^ J * L * C) *
      s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-σ) :=
    mul_nonneg (mul_nonneg (mul_nonneg hfactor (apply_nonneg _ _))
      (pow_nonneg (by positivity) _)) (Real.rpow_nonneg R.property.le _)
  apply SchwartzMap.seminorm_le_bound ℝ k n _ hfinal
  intro p
  change ‖p‖ ^ k * ‖iteratedFDeriv ℝ n
    (traceMovingCutoffOrbitalKernel K S ν χ φ ψ R) p‖ ≤ _
  by_cases hp : p ∈ tsupport χ
  · have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (traceMovingPhase K ν) p‖ *
          (‖p‖ ^ k * ‖iteratedFDeriv ℝ (n - i) (traceCutoffOrbitalKernel K S χ φ ψ R) p‖) :=
        weighted_norm_iteratedFDeriv_traceMovingCutoffOrbitalKernel_le
          K S Γ ν χ hχ hχΩ φ ψ hψ hψsupport R k n (hχΩ hp)
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * P * Q := by
        apply Finset.sum_le_sum
        intro i hi
        have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
        have hH : ‖p‖ ^ k * ‖iteratedFDeriv ℝ (n - i)
            (traceCutoffOrbitalKernel K S χ φ ψ R) p‖ ≤ Q :=
          (SchwartzMap.le_seminorm ℝ k (n - i)
            (traceCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport χ hχ hχsupport hχΩ φ R) p).trans
              (hcutoff φ R (n - i) ((Nat.sub_le n i).trans hn))
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hphase ν p hp i (hin.trans hn))
          (Nat.cast_nonneg _)) hH
          (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))
          (mul_nonneg (Nat.cast_nonneg _) hP)
      _ = (2 : ℝ) ^ n * P * Q := by rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
      _ ≤ (2 : ℝ) ^ J * P * Q :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hP) hQ
      _ = ((2 : ℝ) ^ J * L * C) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          (1 + |ν|) ^ J * R.val ^ (-σ) := by dsimp [P, Q]; ring
  · rw [iteratedFDeriv_traceMovingCutoffOrbitalKernel_zero K S ν χ φ ψ R n hp,
      norm_zero, mul_zero]
    exact hfinal


end HeckeGeneral.Analysis.SmallRadiusMovingSeminormDraft
