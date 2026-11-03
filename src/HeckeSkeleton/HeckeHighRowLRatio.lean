import HeckeSkeleton.HeckePhysicalFamilyBufferedControl
import HeckeSkeleton.HeckeDynamicGammaBound

/-!
The actual high-row uncompleted L-ratio on the dynamic contour.
The numerator FE uses the actual entire reciprocal Gamma multiplier, and
buffered control is applied to the reflected row and the live denominator.
Finite actual row-character fibers remove pure norm exceptions above one
threshold. The target is an arbitrary continuous unitary Hecke character.

This statement retains the actual conductor scales. It does not identify
initial Euler series, bound moving finite Euler tables, remove fixed-S
Euler factors, or perform the full compensation/profile integration.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HeckeHighRowLRatio

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Bridge HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.ExplicitHeckeFunctionalEquation HeckeSkeleton.HeckeGammaReciprocal
open HeckeSkeleton.HeckeBufferedReciprocal
open HeckeSkeleton.HeckePhysicalFamilyBufferedControl HeckeSkeleton.HeckeDynamicGammaBound
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

set_option maxHeartbeats 1000000 in
/-- The constant and actual-row cutoff precede Z,d,u,a and all heights.
There is no L-ratio, Gamma bound or polynomial-growth premise. -/
theorem exists_uniform_high_row_LRatio_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ)
    (P : ProbeData K S) (E : RowEulerData K S P)
    (hFib : ∀ χ : HeckeCharacter K, Finite {u : FrequencyRow K S // E.rows.character u = χ})
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (hesmall : e ≤ 1 / 10000) (hε : 0 < ε) :
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → ∀ u : FrequencyRow K S,
      Z ^ d ≤ frequencyRowNorm K S u → ∀ a H Hupper : ℝ,
      51 / 100 ≤ a → a ≤ 1 → 0 ≤ H → H + 3 / 2 ≤ Hupper →
      rowZeroBelow K S ψ Θ P E u Hupper (a + 2 * e) →
      ∀ s w : ℂ, s.re = a + 16 * e → w.re = 1 - a - 6 * e →
      |s.im| ≤ H → |w.im| ≤ H →
        ‖heckeContinuation K (E.rows.character u) w‖ *
          ‖(heckeContinuation K (ψ * conjugate (E.rows.character u)) s)⁻¹‖ ≤
            C * heckeConductorScale K (E.rows.character u) ^ (a - 1 / 2 + 6 * e) *
              heckeConductorScale K ((E.rows.character u)⁻¹) ^ ε *
              heckeConductorScale K (ψ * conjugate (E.rows.character u)) ^ ε *
              (2 + Hupper) ^
                (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) +
                  2 * ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * ε) := by
  let v : InfinitePlace K := Classical.choice inferInstance
  obtain ⟨D, Z₁, hD, hZ₁, hbuffer⟩ := exists_uniform_high_physicalFamily_buffered_control
    K S hcomplex ψ Θ P E hFib v he he' hε
  obtain ⟨G, hG, hGamma⟩ := exists_uniform_finiteOrder_reflectedGamma_bound K hcomplex
  obtain ⟨Z₂, hZ₂, hnon⟩ :=
    HeckeSkeleton.HighNormBackgroundExclusion.high_rows_exclude_background_norm_twists
      K S P E.rows hFib v ({1} : Finset (HeckeCharacter K))
  let k : ℕ := 2 * Fintype.card (InfinitePlace K)
  refine ⟨G * D ^ 2, max Z₁ Z₂, by positivity,
    hZ₁.trans (le_max_left _ _), ?_⟩
  intro Z hZ d hd u hu a H Hupper ha ha' hH hpadding hbelow s w hs hw hsi hwi
  have hZZ₁ : Z₁ ≤ Z := (le_max_left _ _).trans hZ
  have hZZ₂ : Z₂ ≤ Z := (le_max_right _ _).trans hZ
  let χ := E.rows.character u
  let β := ψ * conjugate χ
  have hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t := by
    simpa only [one_mul] using
      (hnon Z hZZ₂ d hd u hu 1 (Finset.mem_singleton_self 1)).1
  have hχbar : conjugate χ ∈ physicalRowFamily K S ψ Θ P E u := by
    apply Finset.mem_biUnion.mpr
    refine ⟨1, hΘ, ?_⟩
    simp only [one_mul, Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (Or.inl rfl)
  have hβ : β ∈ physicalRowFamily K S ψ Θ P E u :=
    denominator_mem_physicalRowFamily K S ψ Θ P E u hΘ
  have hb := hbuffer Z hZZ₁ d hd u hu a H Hupper (by linarith) ha' hH hpadding hbelow
  have hbdual := hb (conjugate χ) hχbar (1 - w)
    (by simp only [Complex.sub_re, Complex.one_re, hw]; linarith)
    (by simp only [Complex.sub_re, Complex.one_re, hw]; linarith)
    (by simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using hwi)
  have hbden := hb β hβ s (by linarith) (by linarith) hsi
  have hdual : ‖heckeContinuation K χ⁻¹ (1 - w)‖ ≤
      D * heckeConductorScale K χ⁻¹ ^ ε *
        (2 + Hupper) ^ ((k : ℝ) * ε) := by
    have h := (le_add_of_nonneg_right
      (norm_nonneg ((heckeContinuation K (conjugate χ) (1 - w))⁻¹))).trans hbdual
    simpa only [conjugate] using h
  have hden : ‖(heckeContinuation K β s)⁻¹‖ ≤
      D * heckeConductorScale K β ^ ε * (2 + Hupper) ^ ((k : ℝ) * ε) := by
    exact (le_add_of_nonneg_left (norm_nonneg (heckeContinuation K β s))).trans hbden
  have hHU : 0 ≤ Hupper := by linarith
  have hT : 0 < 2 + Hupper := by linarith
  have hQβ : 0 ≤ heckeConductorScale K β := by unfold heckeConductorScale; positivity
  have hQdual : 0 ≤ heckeConductorScale K χ⁻¹ := by unfold heckeConductorScale; positivity
  have hGammab : ‖(canonicalHeckeGammaProfile K χ w)⁻¹ *
      canonicalHeckeGammaProfile K χ⁻¹ (1 - w)‖ ≤ G * (2 + Hupper) ^ k := by
    have hg := hGamma χ (E.rows.finite_order u) w ⟨by linarith, by linarith⟩
    apply hg.trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) k) hG.le
  obtain ⟨root, hroot, hQ, hFE⟩ := exists_uncompleted_functionalEquation_left_of_one K χ hχ
  have hre : (w - 1 / 2).re = -(a - 1 / 2 + 6 * e) := by simp [hw]; ring
  have hnorm : ‖heckeContinuation K χ w‖ =
      (‖(canonicalHeckeGammaProfile K χ w)⁻¹ *
          canonicalHeckeGammaProfile K χ⁻¹ (1 - w)‖ *
        ‖heckeContinuation K χ⁻¹ (1 - w)‖) *
          heckeConductorScale K χ ^ (a - 1 / 2 + 6 * e) := by
    rw [hFE w (by linarith), norm_div, norm_mul, norm_mul root, hroot, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ, hre, Real.rpow_neg hQ.le, div_inv_eq_mul]
  have hheight : (2 + Hupper) ^ k * (2 + Hupper) ^ ((k : ℝ) * ε) *
      (2 + Hupper) ^ ((k : ℝ) * ε) =
        (2 + Hupper) ^ ((k : ℝ) + 2 * (k : ℝ) * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hT, ← Real.rpow_add hT]
    congr 1
    ring
  change ‖heckeContinuation K χ w‖ * ‖(heckeContinuation K β s)⁻¹‖ ≤ _
  rw [hnorm]
  calc
    _ ≤ (((G * (2 + Hupper) ^ k) *
          (D * heckeConductorScale K χ⁻¹ ^ ε * (2 + Hupper) ^ ((k : ℝ) * ε))) *
            heckeConductorScale K χ ^ (a - 1 / 2 + 6 * e)) *
          (D * heckeConductorScale K β ^ ε * (2 + Hupper) ^ ((k : ℝ) * ε)) := by
      apply mul_le_mul _ hden (norm_nonneg _) (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hQ.le _)
      exact mul_le_mul hGammab hdual (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [← hheight]
      ring

end HeckeSkeleton.HeckeHighRowLRatio
