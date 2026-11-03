import HeckeSkeleton.BufferedReciprocal
import HeckeSkeleton.ActualEulerLogarithm
import HeckeGeneral.Analysis.TInputRanges

/-!
Actual Hecke specialization of the logarithmic-control theorem. A physical
zero upper bound supplies NONVANISHING rather than a new reciprocal-bound
assumption. The remaining polynomial strip growth and bounded Euler log
are explicit hypotheses, not claimed consequences of a fixed-bin record.
-/
set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HeckeBufferedReciprocal

open NumberField IsDedekindDomain Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical Topology

variable (K : Type) [Field K] [NumberField K]

/-- The literal zero upper bound in the nontrivial critical strip. -/
def ZeroUpperBound (χ : HeckeCharacter K) (H α : ℝ) : Prop :=
  ∀ ρ : ℂ, 0 < meromorphicOrderAt (heckeContinuation K χ) ρ →
    1 / 2 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ H → ρ.re ≤ α

/-- Entire non-norm continuation plus the actual upper-zero detector
excludes zeros throughout the retained right rectangle, including Re=1. -/
theorem continuation_ne_zero_of_upper (χ : HeckeCharacter K)
    (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (H α : ℝ) (hα : 1 / 2 ≤ α) (hupper : ZeroUpperBound K χ H α)
    (z : ℂ) (hz : α < z.re) (hheight : |z.im| ≤ H) :
    heckeContinuation K χ z ≠ 0 := by
  by_cases hright : 1 < z.re
  · exact heckeContinuation_ne_zero K χ hright
  intro hzero
  have hd := differentiable_heckeContinuation_of_nonNorm K χ hχ
  have hlim : Tendsto (heckeContinuation K χ) (𝓝[≠] z) (𝓝 0) := by
    simpa only [hzero] using
      ((hd.continuous.continuousAt : ContinuousAt (heckeContinuation K χ) z).tendsto.mono_left
        nhdsWithin_le_nhds)
  have hpos : 0 < meromorphicOrderAt (heckeContinuation K χ) z :=
    (tendsto_zero_iff_meromorphicOrderAt_pos
      ((hd.analyticAt z).meromorphicAt)).mp hlim
  exact (not_le_of_gt hz) (hupper z hpos (hα.trans hz.le)
    (le_of_not_gt hright) hheight)

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem zeroUpperBound_of_rowZeroBelow
    (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K))
    (P : ProbeData K S) (E : RowEulerData K S P) (u : FrequencyRow K S)
    (H α : ℝ) (hbelow : rowZeroBelow K S ψ Θ P E u H α)
    (χ : HeckeCharacter K) (hχ : χ ∈ physicalRowFamily K S ψ Θ P E u) :
    ZeroUpperBound K χ H α := hbelow χ hχ

/-- Including the identity companion suffices for the actual row numerator.
Whether the constructed companion set does contain it remains a separate
construction statement; finite membership alone is not silently inferred. -/
theorem numerator_mem_physicalRowFamily
    (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K))
    (P : ProbeData K S) (E : RowEulerData K S P) (u : FrequencyRow K S)
    (hΘ : (1 : HeckeCharacter K) ∈ Θ) :
    E.rows.character u ∈ physicalRowFamily K S ψ Θ P E u := by
  apply Finset.mem_biUnion.mpr
  refine ⟨1, hΘ, ?_⟩
  simp only [one_mul, Finset.mem_insert, Finset.mem_singleton, true_or]

theorem denominator_mem_physicalRowFamily
    (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K))
    (P : ProbeData K S) (E : RowEulerData K S P) (u : FrequencyRow K S)
    (hΘ : (1 : HeckeCharacter K) ∈ Θ) :
    ψ * conjugate (E.rows.character u) ∈ physicalRowFamily K S ψ Θ P E u := by
  apply Finset.mem_biUnion.mpr
  refine ⟨1, hΘ, ?_⟩
  simp only [one_mul, mul_one, Finset.mem_insert, Finset.mem_singleton, true_or, or_true]

/-- The actual Hecke continuation obeys the subpower reciprocal bound
once its polynomial strip growth and bounded Euler log are supplied.
In particular the zero-free rectangle is derived from orders/detection.
No L-ratio, functional equation, or high-bin estimate is a hypothesis. -/
theorem hecke_value_and_reciprocal_of_upper
    {e A M ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (a C H Hupper : ℝ) (χ : HeckeCharacter K) (Elog : ℂ → ℂ),
      1 / 2 ≤ a → a ≤ 1 → Real.exp 1 ≤ C →
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      H + 3 / 2 ≤ Hupper → ZeroUpperBound K χ Hupper (a + 2 * e) →
      (∀ z : ℂ, a + 2 * e < z.re → |z.im| ≤ Hupper →
        ‖heckeContinuation K χ z‖ ≤ C ^ M) →
      DifferentiableOn ℂ Elog {z : ℂ | 1 < z.re} →
      (∀ z : ℂ, 1 < z.re → Complex.exp (Elog z) = heckeContinuation K χ z) →
      (∀ z : ℂ, 151 / 100 ≤ z.re → ‖Elog z‖ ≤ A) →
      ∀ z : ℂ, a + 6 * e ≤ z.re → z.re ≤ 2 → |z.im| ≤ H →
        ‖heckeContinuation K χ z‖ + ‖(heckeContinuation K χ z)⁻¹‖ ≤ D * C ^ ε := by
  obtain ⟨D, hD, hbound⟩ :=
    HeckeSkeleton.BufferedReciprocal.buffered_value_and_reciprocal_of_rectangle
      he he' hA hM hε
  refine ⟨D, hD, ?_⟩
  intro a C H Hupper χ Elog ha ha' hC hχ hpadding hupper hpoly hE hEL hEb
  apply hbound a C H Hupper (heckeContinuation K χ) Elog ha ha' hC hpadding
    (differentiable_heckeContinuation_of_nonNorm K χ hχ).differentiableOn
  · intro z hz hh
    exact continuation_ne_zero_of_upper K χ hχ Hupper (a + 2 * e)
      (by linarith) hupper z hz hh
  · exact hpoly
  · exact hE
  · exact hEL
  · exact hEb

/-- The Euler-log premise has now been constructed uniformly in the actual
unitary character. Only the genuine polynomial strip bound remains an
analytic premise. Pure norm backgrounds still require their pole-cleared
branch; this theorem does not silently discard that case. -/
theorem hecke_subpower_of_upper_strip_growth
    {e M ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (a C H Hupper : ℝ) (χ : HeckeCharacter K),
      1 / 2 ≤ a → a ≤ 1 → Real.exp 1 ≤ C →
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      H + 3 / 2 ≤ Hupper → ZeroUpperBound K χ Hupper (a + 2 * e) →
      (∀ z : ℂ, a + 2 * e < z.re → |z.im| ≤ Hupper →
        ‖heckeContinuation K χ z‖ ≤ C ^ M) →
      ∀ z : ℂ, a + 6 * e ≤ z.re → z.re ≤ 2 → |z.im| ≤ H →
        ‖heckeContinuation K χ z‖ + ‖(heckeContinuation K χ z)⁻¹‖ ≤ D * C ^ ε := by
  obtain ⟨A, hA, hlog⟩ :=
    HeckeSkeleton.ActualEulerLogarithm.exists_uniform_heckeEulerLog_bound K
  obtain ⟨D, hD, hbound⟩ := hecke_value_and_reciprocal_of_upper K he he' hA hM hε
  refine ⟨D, hD, ?_⟩
  intro a C H Hupper χ ha ha' hC hχ hpadding hupper hpoly
  exact hbound a C H Hupper χ (HeckeSkeleton.ActualEulerLogarithm.heckeEulerLog K χ)
    ha ha' hC hχ hpadding hupper hpoly
    (HeckeSkeleton.ActualEulerLogarithm.heckeEulerLog_differentiableOn K χ)
    (HeckeSkeleton.ActualEulerLogarithm.exp_heckeEulerLog_eq_continuation K χ)
    (hlog χ)

end HeckeSkeleton.HeckeBufferedReciprocal
