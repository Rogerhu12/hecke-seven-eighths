import HeckeGeneral.Bridge.FLTDefinitions
import HeckeGeneral.Analysis.HeckeEulerProduct
import FLTReuse.M974319314547c0e9
import FLTReuse.M2c5e67fdd3cfcc89
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Actual meromorphic continuation of a unitary Hecke character

The archimedean parameters and both entire-function branches are obtained
from the proved global Tate theorems in the fixed FLT source. Their Euler
product is identified with the convergent ideal series by `FLTDefinitions`.
There are no additional analytic hypotheses in this construction.

The imported Tate statements quantify over `F : Type`, so this module uses
that same universe-zero scope explicitly. No universe transport is hidden.
For `heckeNormTwist F t`, the possible pole is `1 + t * I`, consistently with
the previously proved `s - t * I` shift. Existence of the entire pole-cleared
function does not assert that it is nonzero at this point or that the pole
is present or simple. Values assigned by total division at a pole do not
define meromorphic zeros.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField HeckeGeneral.Characters HeckeGeneral.Bridge Classical
open scoped nonZeroDivisors Topology

variable (F : Type) [Field F] [NumberField F]

/-- The exact real/complex Gamma product occurring in the Tate theorem. -/
def heckeGammaProfile (τ : InfinitePlace F → ℝ) (m : InfinitePlace F → ℤ)
    (s : ℂ) : ℂ :=
  ∏ v : InfinitePlace F,
    if v.IsReal then
      Complex.Gammaℝ (s + (τ v : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
    else
      Complex.Gammaℂ (s + (τ v : ℂ) * Complex.I + ((m v).natAbs : ℂ) / 2)

/-- The pole location in the positive ideal-norm twist convention. -/
def heckeNormPole (t : ℝ) : ℂ := 1 + (t : ℂ) * Complex.I

/-- Both analytic branches, with Gamma parameters supplied by the actual
continuous character classification theorem. -/
theorem exists_heckeContinuation_branches (χ : HeckeCharacter F) :
    ∃ (τ : InfinitePlace F → ℝ) (m : InfinitePlace F → ℤ),
      ((∀ t : ℝ, χ ≠ heckeNormTwist F t) →
        ∃ (L Λ : ℂ → ℂ), Differentiable ℂ L ∧ Differentiable ℂ Λ ∧
          (∀ s : ℂ, 1 < s.re → L s = heckeLSeries F χ s) ∧
          (∀ s : ℂ, 0 < s.re → Λ s = heckeGammaProfile F τ m s * L s)) ∧
      (∀ t : ℝ, χ = heckeNormTwist F t →
        ∃ (Q ΛQ : ℂ → ℂ), Differentiable ℂ Q ∧ Differentiable ℂ ΛQ ∧
          (∀ s : ℂ, 1 < s.re →
            Q s = (s - heckeNormPole t) * heckeLSeries F χ s) ∧
          (∀ s : ℂ, 0 < s.re →
            ΛQ s = (s - (t : ℂ) * Complex.I) * (heckeGammaProfile F τ m s * Q s))) := by
  obtain ⟨τ, m, hτ, hm, _hmreal⟩ :=
    NumberField.TateGlobal.exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar F
      (complexIdeleCharacter F χ) (complexIdeleCharacter_isUnitary F χ)
      (continuous_complexIdeleCharacter_coe F χ)
  have h :=
    NumberField.TateGlobal.exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq
      F (complexIdeleCharacter F χ) (continuous_complexIdeleCharacter_coe F χ)
      (complexIdeleCharacter_isUnitary F χ) (complexIdeleCharacter_isIdeleClass F χ)
      τ m hτ hm
  rcases h with ⟨hnon, hnorm⟩
  refine ⟨τ, m, ?_, ?_⟩
  · intro hχ
    obtain ⟨L, Λ, hL, hΛ, hLeq, hΛeq⟩ :=
      hnon ((complexIdeleCharacter_ne_normPow_iff F χ).mpr hχ)
    refine ⟨L, Λ, hL, hΛ, ?_, ?_⟩
    · intro s hs
      rw [hLeq s hs]
      exact (heckeLSeries_eq_fltEulerProduct F χ hs).symm
    · simpa only [heckeGammaProfile] using hΛeq
  · intro t hχ
    have ht : complexIdeleCharacter F χ = NumberField.TateGlobal.normPowChar F (-t) :=
      (complexIdeleCharacter_eq_normPow_iff F χ (-t)).mpr (by simpa using hχ)
    obtain ⟨Q, ΛQ, hQ, hΛQ, hQeq, hΛQeq⟩ := hnorm (-t) ht
    refine ⟨Q, ΛQ, hQ, hΛQ, ?_, ?_⟩
    · intro s hs
      have hP : Q s = (s - heckeNormPole t) * fltEulerProduct F χ s := by
        simpa only [heckeNormPole, fltEulerProduct, fltPrimeCoefficient,
          Complex.ofReal_neg, neg_mul, sub_neg_eq_add]
          using hQeq s hs
      rw [hP, ← heckeLSeries_eq_fltEulerProduct F χ hs]
    · simpa only [heckeGammaProfile, Complex.ofReal_neg, neg_mul, sub_eq_add_neg]
        using hΛQeq

/-- A non-norm Hecke character has an actual entire L-continuation. -/
theorem exists_entire_heckeContinuation (χ : HeckeCharacter F)
    (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist F t) :
    ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      ∀ s : ℂ, 1 < s.re → L s = heckeLSeries F χ s := by
  obtain ⟨τ, m, hnon, _hnorm⟩ := exists_heckeContinuation_branches F χ
  obtain ⟨L, _Λ, hL, _hΛ, hLeq, _hΛeq⟩ := hnon hχ
  exact ⟨L, hL, hLeq⟩

/-- Pure norm characters have an entire pole-cleared continuation. -/
theorem exists_poleCleared_heckeContinuation (χ : HeckeCharacter F) (t : ℝ)
    (hχ : χ = heckeNormTwist F t) :
    ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧
      ∀ s : ℂ, 1 < s.re → Q s = (s - heckeNormPole t) * heckeLSeries F χ s := by
  obtain ⟨τ, m, _hnon, hnorm⟩ := exists_heckeContinuation_branches F χ
  obtain ⟨Q, _ΛQ, hQ, _hΛQ, hQeq, _hΛQeq⟩ := hnorm t hχ
  exact ⟨Q, hQ, hQeq⟩

theorem sub_heckeNormPole_ne_zero {s : ℂ} (hs : 1 < s.re) (t : ℝ) :
    s - heckeNormPole t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re (sub_eq_zero.mp h)
  simp [heckeNormPole] at hre
  linarith

/-- Unconditional construction of an actual globally meromorphic continuation.
The entire branch is selected when the character is not a norm twist. -/
theorem exists_meromorphic_heckeContinuation (χ : HeckeCharacter F) :
    ∃ L : ℂ → ℂ, MeromorphicOn L Set.univ ∧
      (∀ s : ℂ, 1 < s.re → L s = heckeLSeries F χ s) ∧
      ((∀ t : ℝ, χ ≠ heckeNormTwist F t) → Differentiable ℂ L) ∧
      ((∃ t : ℝ, χ = heckeNormTwist F t) →
        ∃ (t : ℝ) (Q : ℂ → ℂ), χ = heckeNormTwist F t ∧ Differentiable ℂ Q ∧
          L = fun s => Q s / (s - heckeNormPole t)) := by
  by_cases hn : ∃ t : ℝ, χ = heckeNormTwist F t
  · obtain ⟨t, ht⟩ := hn
    obtain ⟨Q, hQ, hQeq⟩ := exists_poleCleared_heckeContinuation F χ t ht
    refine ⟨fun s => Q s / (s - heckeNormPole t), ?_, ?_, ?_, ?_⟩
    · intro s _hs
      exact (hQ.analyticAt s).meromorphicAt.div
        ((analyticAt_id.sub analyticAt_const).meromorphicAt)
    · intro s hs
      change Q s / (s - heckeNormPole t) = _
      rw [hQeq s hs]
      exact mul_div_cancel_left₀ _ (sub_heckeNormPole_ne_zero hs t)
    · intro hχ
      exact False.elim (hχ t ht)
    · intro _hχ
      exact ⟨t, Q, ht, hQ, rfl⟩
  · have hχ : ∀ t : ℝ, χ ≠ heckeNormTwist F t := fun t ht => hn ⟨t, ht⟩
    obtain ⟨L, hL, hLeq⟩ := exists_entire_heckeContinuation F χ hχ
    exact ⟨L, fun s _hs => (hL.analyticAt s).meromorphicAt, hLeq, fun _ => hL,
      fun hnorm => False.elim (hn hnorm)⟩

/-- A choice of the genuine continuation just constructed by global Tate theory. -/
def heckeContinuation (χ : HeckeCharacter F) : ℂ → ℂ :=
  Classical.choose (exists_meromorphic_heckeContinuation F χ)

theorem meromorphicOn_heckeContinuation (χ : HeckeCharacter F) :
    MeromorphicOn (heckeContinuation F χ) Set.univ :=
  (Classical.choose_spec (exists_meromorphic_heckeContinuation F χ)).1

theorem heckeContinuation_eq_series (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re) :
    heckeContinuation F χ s = heckeLSeries F χ s :=
  (Classical.choose_spec (exists_meromorphic_heckeContinuation F χ)).2.1 s hs

theorem differentiable_heckeContinuation_of_nonNorm (χ : HeckeCharacter F)
    (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist F t) :
    Differentiable ℂ (heckeContinuation F χ) :=
  (Classical.choose_spec (exists_meromorphic_heckeContinuation F χ)).2.2.1 hχ

/-- The chosen norm branch retains its genuine entire numerator and division
formula. This makes the possible singularity explicit without claiming it exists. -/
theorem heckeContinuation_normBranch (χ : HeckeCharacter F)
    (hχ : ∃ t : ℝ, χ = heckeNormTwist F t) :
    ∃ (t : ℝ) (Q : ℂ → ℂ), χ = heckeNormTwist F t ∧ Differentiable ℂ Q ∧
      heckeContinuation F χ = fun s => Q s / (s - heckeNormPole t) :=
  (Classical.choose_spec (exists_meromorphic_heckeContinuation F χ)).2.2.2 hχ

private theorem meromorphicOrderAt_entire_div_sub_ge_neg_one
    (Q : ℂ → ℂ) (hQ : Differentiable ℂ Q) (p : ℂ) :
    (-1 : WithTop ℤ) ≤ meromorphicOrderAt (fun s => Q s / (s - p)) p := by
  have hd : MeromorphicAt (fun s : ℂ => s - p) p :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  have h := meromorphicOrderAt_div (hQ.analyticAt p).meromorphicAt hd
  change meromorphicOrderAt (fun s => Q s / (s - p)) p =
    meromorphicOrderAt Q p - meromorphicOrderAt (fun s : ℂ => s - p) p at h
  rw [h, meromorphicOrderAt_id_sub_const]
  have hn := (hQ.analyticAt p).meromorphicOrderAt_nonneg
  simpa only [sub_eq_add_neg, zero_add, add_zero, add_comm]
    using add_le_add_right hn (-1)

/-- A norm branch is analytic away from its single possible pole location. -/
theorem heckeContinuation_normBranch_analyticAwayPole (χ : HeckeCharacter F)
    (hχ : ∃ t : ℝ, χ = heckeNormTwist F t) :
    ∃ t : ℝ, χ = heckeNormTwist F t ∧
      ∀ s : ℂ, s ≠ heckeNormPole t → AnalyticAt ℂ (heckeContinuation F χ) s := by
  obtain ⟨t, Q, ht, hQ, hL⟩ := heckeContinuation_normBranch F χ hχ
  refine ⟨t, ht, ?_⟩
  intro s hs
  rw [hL]
  exact (hQ.analyticAt s).div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs)

/-- The possible norm-character singularity has order at least `-1`.
The inequality includes removable singularities and zeros. -/
theorem heckeContinuation_normBranch_order_ge_neg_one (χ : HeckeCharacter F)
    (hχ : ∃ t : ℝ, χ = heckeNormTwist F t) :
    ∃ t : ℝ, χ = heckeNormTwist F t ∧
      (-1 : WithTop ℤ) ≤ meromorphicOrderAt (heckeContinuation F χ) (heckeNormPole t) := by
  obtain ⟨t, Q, ht, hQ, hL⟩ := heckeContinuation_normBranch F χ hχ
  refine ⟨t, ht, ?_⟩
  rw [hL]
  exact meromorphicOrderAt_entire_div_sub_ge_neg_one Q hQ (heckeNormPole t)

/-- The continuation remains holomorphic on the original convergence half-plane. -/
theorem analyticAt_heckeContinuation (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (heckeContinuation F χ) s := by
  apply (analyticAt_heckeLSeries F χ hs).congr
  have hnhds : {z : ℂ | 1 < z.re} ∈ nhds s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  filter_upwards [hnhds] with z hz
  exact (heckeContinuation_eq_series F χ hz).symm

theorem heckeContinuation_ne_zero (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re) :
    heckeContinuation F χ s ≠ 0 := by
  rw [heckeContinuation_eq_series F χ hs]
  exact heckeLSeries_ne_zero F χ hs

/-- Genuine meromorphic zero and pole orders vanish on the convergence half-plane. -/
theorem meromorphicOrderAt_heckeContinuation (χ : HeckeCharacter F)
    {s : ℂ} (hs : 1 < s.re) : meromorphicOrderAt (heckeContinuation F χ) s = 0 := by
  have h := analyticAt_heckeContinuation F χ hs
  rw [h.meromorphicOrderAt_eq,
    h.analyticOrderAt_eq_zero.mpr (heckeContinuation_ne_zero F χ hs)]
  simp

/-- The continuation has finite germ order everywhere: the Euler product at
`s = 2` rules out the identically zero meromorphic function globally. -/
theorem meromorphicOrderAt_heckeContinuation_ne_top (χ : HeckeCharacter F) (s : ℂ) :
    meromorphicOrderAt (heckeContinuation F χ) s ≠ ⊤ := by
  apply (meromorphicOn_heckeContinuation F χ).meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ (2 : ℂ)) (Set.mem_univ s)
  rw [meromorphicOrderAt_heckeContinuation F χ (s := 2) (by norm_num)]
  exact WithTop.coe_ne_top

/-- Every global meromorphic continuation agreeing with the ideal series on
the convergence half-plane defines the same punctured germ at every point.
This formulation allows arbitrary point values at poles. -/
theorem heckeContinuation_eventuallyEq_of_meromorphic (χ : HeckeCharacter F)
    (L : ℂ → ℂ) (hL : MeromorphicOn L Set.univ)
    (hLeq : ∀ s : ℂ, 1 < s.re → L s = heckeLSeries F χ s) (s : ℂ) :
    L =ᶠ[nhdsWithin s {s}ᶜ] heckeContinuation F χ := by
  have hd := hL.sub (meromorphicOn_heckeContinuation F χ)
  have h2 : meromorphicOrderAt (L - heckeContinuation F χ) (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hnhds : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [Filter.mem_of_superset (nhdsWithin_le_nhds hnhds) (fun z hz => hz)] with z hz
    exact sub_eq_zero.mpr ((hLeq z hz).trans (heckeContinuation_eq_series F χ hz).symm)
  have hs := hd.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ (2 : ℂ)) (Set.mem_univ s) h2
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hs] with z hz
  exact sub_eq_zero.mp hz

end HeckeGeneral.Analysis
