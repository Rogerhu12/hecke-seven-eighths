import HeckeSkeleton.SmallRadius.SmallRadiusMovingSeminorm
import HeckeGeneral.Analysis.TraceMovingFourierBounds

/-!
UNCOMPILED / native 0. All-positive-radius moving-cutoff seminorm bounds
are passed through the actual traceJointProductFourierCLM. The Fourier
operator supplies a finite set of input seminorms; a common derivative
order is selected before the moving frequency, original test and radius.
Their finite original-test seminorms and constants are aggregated with no
radius threshold. The original trace Fourier normalization is unchanged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Analysis.SmallRadiusMovingFourierSeminormDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open SmallRadiusMovingSeminormDraft
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
/-- Every target seminorm of the actual moving cutoff Fourier transform has
a single finite original-test seminorm bound, valid at every positive radius.
All choices precede nu, phi and R; there is no large-radius hypothesis. -/
theorem exists_traceMovingCutoffOrbitalFourier_seminorm_allRadius_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (χ : V × V → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupport : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (k n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, ∃ J : ℕ, 0 ≤ C ∧
      ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r},
        SchwartzMap.seminorm ℝ k n
          (traceMovingCutoffOrbitalFourier K S Γ ψ hψ hψsupport
            χ hχ hχsupport hχΩ ν φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-σ) := by
  obtain ⟨t, D, _hD, hFourier⟩ := traceJointProductFourier_real_seminorm_bound K k n
  let J0 : ℕ := t.sup (fun i => i.2)
  have hP (i : ↥t) :
      ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
        ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r},
          SchwartzMap.seminorm ℝ i.val.1 i.val.2
            (traceMovingCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport
              χ hχ hχsupport hχΩ ν φ R) ≤
            C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J0 * R.val ^ (-σ) := by
    obtain ⟨s, C, hC, hb⟩ :=
      exists_traceMovingCutoffOrbitalSchwartz_seminorm_allRadius_bound
        K S Γ ψ hψ hψsupport χ hχ hχsupport hχΩ σ hσ hσ1 i.val.1 J0
    exact ⟨s, C, hC, fun ν φ R => hb ν φ R i.val.2 (Finset.le_sup i.property)⟩
  choose s C hC hbound using hP
  let sall : Finset (ℕ × ℕ) := Finset.univ.biUnion s
  let Call : ℝ := ∑ i : ↥t, C i
  have hCall : 0 ≤ Call := Finset.sum_nonneg (fun i _ => hC i)
  have hCi (i : ↥t) : C i ≤ Call :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  have hsi (i : ↥t) (φ : SchwartzMap V ℂ) :
      (s i).sup (schwartzSeminormFamily ℝ V ℂ) φ ≤
        sall.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro j hj
    exact Seminorm.le_finset_sup_apply
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hj⟩)
  refine ⟨sall, (D : ℝ) * Call, J0,
    mul_nonneg (NNReal.coe_nonneg D) hCall, fun ν φ R => ?_⟩
  have hnonneg : 0 ≤ Call * sall.sup (schwartzSeminormFamily ℝ V ℂ) φ *
      (1 + |ν|) ^ J0 * R.val ^ (-σ) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCall (apply_nonneg _ _))
      (pow_nonneg (by positivity) _)) (Real.rpow_nonneg R.property.le _)
  have hsup : t.sup (schwartzSeminormFamily ℝ (V × V) ℂ)
      (traceMovingCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport
        χ hχ hχsupport hχΩ ν φ R) ≤
      Call * sall.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J0 * R.val ^ (-σ) := by
    apply Seminorm.finset_sup_apply_le hnonneg
    intro i hi
    calc
      _ ≤ C ⟨i, hi⟩ * (s ⟨i, hi⟩).sup (schwartzSeminormFamily ℝ V ℂ) φ *
          (1 + |ν|) ^ J0 * R.val ^ (-σ) := hbound ⟨i, hi⟩ ν φ R
      _ ≤ Call * sall.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          (1 + |ν|) ^ J0 * R.val ^ (-σ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul (hCi ⟨i, hi⟩) (hsi ⟨i, hi⟩ φ) (apply_nonneg _ _) hCall)
            (pow_nonneg (by positivity) _)) (Real.rpow_nonneg R.property.le _)
  calc
    _ ≤ (D : ℝ) * t.sup (schwartzSeminormFamily ℝ (V × V) ℂ)
        (traceMovingCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport
          χ hχ hχsupport hχΩ ν φ R) := hFourier _
    _ ≤ (D : ℝ) * (Call * sall.sup (schwartzSeminormFamily ℝ V ℂ) φ *
        (1 + |ν|) ^ J0 * R.val ^ (-σ)) :=
      mul_le_mul_of_nonneg_left hsup (NNReal.coe_nonneg D)
    _ = ((D : ℝ) * Call) * sall.sup (schwartzSeminormFamily ℝ V ℂ) φ *
        (1 + |ν|) ^ J0 * R.val ^ (-σ) := by ring

end HeckeGeneral.Analysis.SmallRadiusMovingFourierSeminormDraft
