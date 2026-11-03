import HeckeGeneral.Analysis.HeckeContinuation
import HeckeGeneral.Analysis.HeckeConjugation
import HeckeGeneral.Analysis.MellinZeroDetector
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Conjugation of genuine meromorphic Hecke zero orders. The identity
is one of punctured germs and remains valid at norm-character poles. -/

noncomputable section
namespace HeckeGeneral.Analysis

open Set Filter
open HeckeGeneral.Characters
open scoped Topology ComplexConjugate

theorem analyticAt_doubleConjugate {f : ℂ → ℂ} {s : ℂ}
    (hf : AnalyticAt ℂ f s) : AnalyticAt ℂ (fun z => conj (f (conj z))) (conj s) := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt] at hf ⊢
  have hc : Tendsto (fun z : ℂ => conj z) (𝓝 (conj s)) (𝓝 s) := by
    simpa using Complex.continuous_conj.continuousAt.tendsto (x := conj s)
  filter_upwards [hc.eventually hf] with z hz
  simpa only [Function.comp_def, Complex.conj_conj] using hz.conj_conj

theorem meromorphicAt_doubleConjugate {f : ℂ → ℂ} {s : ℂ}
    (hf : MeromorphicAt f s) : MeromorphicAt (fun z => conj (f (conj z))) (conj s) := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n, ?_⟩
  simpa only [smul_eq_mul, map_mul, map_pow, map_sub, Complex.conj_conj]
    using analyticAt_doubleConjugate hn

theorem meromorphicOrderAt_doubleConjugate_of_ne_top {f : ℂ → ℂ} {s : ℂ}
    (hf : MeromorphicAt f s) (hfinite : meromorphicOrderAt f s ≠ ⊤) :
    meromorphicOrderAt (fun z => conj (f (conj z))) (conj s) = meromorphicOrderAt f s := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfinite
  obtain ⟨g, hg, hgne, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hn.symm
  rw [← hn]
  apply (meromorphicOrderAt_eq_int_iff (meromorphicAt_doubleConjugate hf)).mpr
  refine ⟨fun z => conj (g (conj z)), analyticAt_doubleConjugate hg, ?_, ?_⟩
  · simpa using hgne
  · rw [eventually_nhdsWithin_iff] at hfg ⊢
    have hc : Tendsto (fun z : ℂ => conj z) (𝓝 (conj s)) (𝓝 s) := by
      simpa using Complex.continuous_conj.continuousAt.tendsto (x := conj s)
    filter_upwards [hc.eventually hfg] with z hz hzs
    have hne : conj z ≠ s := by
      intro he
      have h := congrArg (fun w : ℂ => conj w) he
      exact hzs (by simpa using h)
    have he := congrArg (fun w : ℂ => conj w) (hz hne)
    simpa only [smul_eq_mul, map_mul, map_zpow₀, map_sub, Complex.conj_conj] using he

variable (K : Type) [Field K] [NumberField K]

theorem heckeContinuation_inv_eventuallyEq (χ : HeckeCharacter K) (s : ℂ) :
    (fun z => conj (heckeContinuation K χ (conj z))) =ᶠ[𝓝[≠] s]
      heckeContinuation K χ⁻¹ := by
  apply heckeContinuation_eventuallyEq_of_meromorphic K χ⁻¹
  · intro z _
    simpa using meromorphicAt_doubleConjugate
      (meromorphicOn_heckeContinuation K χ (conj z) (mem_univ _))
  · intro z hz
    rw [heckeContinuation_eq_series K χ (by simpa using hz)]
    simpa using (heckeLSeries_inv_conjugate K χ (conj z)).symm

theorem meromorphicOrderAt_heckeContinuation_inv (χ : HeckeCharacter K) (s : ℂ) :
    meromorphicOrderAt (heckeContinuation K χ⁻¹) (conj s) =
      meromorphicOrderAt (heckeContinuation K χ) s := by
  rw [← meromorphicOrderAt_congr (heckeContinuation_inv_eventuallyEq K χ (conj s))]
  exact meromorphicOrderAt_doubleConjugate_of_ne_top
    (meromorphicOn_heckeContinuation K χ s (mem_univ _))
    (meromorphicOrderAt_heckeContinuation_ne_top K χ s)

theorem zeroRealParts_heckeContinuation_inv (χ : HeckeCharacter K) :
    zeroRealParts (heckeContinuation K χ⁻¹) = zeroRealParts (heckeContinuation K χ) := by
  ext r
  constructor
  · rintro ⟨s, hsr, hs⟩
    refine ⟨conj s, by simpa using hsr, ?_⟩
    have he := meromorphicOrderAt_heckeContinuation_inv K χ (conj s)
    simp only [Complex.conj_conj] at he
    rwa [← he]
  · rintro ⟨s, hsr, hs⟩
    exact ⟨conj s, by simpa using hsr, by rwa [meromorphicOrderAt_heckeContinuation_inv]⟩

theorem heckeContinuation_inv_zeroFreeOn_iff (χ : HeckeCharacter K) (b : ℝ) :
    MeromorphicZeroFreeOn (heckeContinuation K χ⁻¹) (rightHalfPlane b) ↔
      MeromorphicZeroFreeOn (heckeContinuation K χ) (rightHalfPlane b) := by
  constructor
  · intro h
    refine ⟨fun s _ => meromorphicOn_heckeContinuation K χ s (mem_univ _), ?_⟩
    intro s hs
    have he := h.2 (conj s) (by simpa [rightHalfPlane] using hs)
    rwa [meromorphicOrderAt_heckeContinuation_inv] at he
  · intro h
    refine ⟨fun s _ => meromorphicOn_heckeContinuation K χ⁻¹ s (mem_univ _), ?_⟩
    intro s hs
    have he := h.2 (conj s) (by simpa [rightHalfPlane] using hs)
    have ho := meromorphicOrderAt_heckeContinuation_inv K χ (conj s)
    simpa only [Complex.conj_conj] using (ho.trans_le he)

end HeckeGeneral.Analysis
