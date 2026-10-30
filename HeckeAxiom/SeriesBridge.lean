import HeckeAxiom.RaySpan
import HeckeGeneral.Analysis.HeckeNormTwistZeros

/-!
# From AxiomMath's ray-character output to `heckeContinuation`

AxiomMath's `heckeL_ne_zero` produces, for a ray class character `η`, a function
`f` holomorphic away from `s = 1` (entire when `η` is nonprincipal), equal to the
ideal series on `Re s > 1`, and without zeros on `Re s > 31/32`.

This file shows that such an output for the ray class character of an actual
finite-order Hecke character `χ` gives the zero-free region for the actual
continuation `heckeContinuation χ`:

* away from `s = 1`, by the identity theorem on the connected set `ℂ \ {1}`;
* at `s = 1` for a nonprincipal ray character, where `f` is entire;
* at `s = 1` for a principal ray character, where the series is at least one on
  real `s > 1`, so the continuation cannot vanish there.

Nothing here depends on AxiomMath's analytic proofs; the output is a hypothesis.
-/

noncomputable section

namespace HeckeAxiom

open NumberField IsDedekindDomain Filter Topology
open HeckeGeneral.Characters HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open scoped nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- The Hecke ideal series summed over all integral ideals; the zero ideal
contributes zero. -/
theorem hasSum_idealCoefficient_all (χ : HeckeCharacter K) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : Ideal (𝓞 K) =>
      idealCoefficient (primeCoefficient K χ) I * (Ideal.absNorm I : ℂ) ^ (-s))
      (heckeLSeries K χ s) := by
  have hsupp : Function.support (fun I : Ideal (𝓞 K) =>
      idealCoefficient (primeCoefficient K χ) I * (Ideal.absNorm I : ℂ) ^ (-s)) ⊆
      ((Ideal (𝓞 K))⁰ : Set (Ideal (𝓞 K))) := by
    intro I hI
    by_contra hmem
    apply hI
    have hbot : I = ⊥ := by
      by_contra hne
      exact hmem (mem_nonZeroDivisors_of_ne_zero hne)
    simp [hbot]
  refine (hasSum_subtype_iff_of_support_subset hsupp).mp ?_
  convert hasSum_heckeLSeries K χ hs using 1
  funext I
  simp [Function.comp, dirichletTerm, heckeIdealCoefficient, nonzeroIdealCoefficient, idealNorm]

/-- A meromorphic continuation agreeing with an analytic function on the
convergence half-plane has the same punctured germ throughout a preconnected
open set containing `2`. -/
theorem heckeContinuation_eventuallyEq_of_analyticOnNhd (χ : HeckeCharacter K)
    (f : ℂ → ℂ) (U : Set ℂ) (hU : IsPreconnected U) (h2 : (2 : ℂ) ∈ U)
    (hf : AnalyticOnNhd ℂ f U) (hfeq : ∀ s : ℂ, 1 < s.re → f s = heckeLSeries K χ s)
    {z : ℂ} (hz : z ∈ U) :
    heckeContinuation K χ =ᶠ[𝓝[≠] z] f := by
  set g : ℂ → ℂ := heckeContinuation K χ - f with hgdef
  have hg : MeromorphicOn g U := fun w hw =>
    (meromorphicOn_heckeContinuation K χ w (Set.mem_univ w)).sub (hf w hw).meromorphicAt
  have hg2 : meromorphicOrderAt g 2 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have hnhds : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [nhdsWithin_le_nhds hnhds] with w hw
    simp only [hgdef, Pi.sub_apply, heckeContinuation_eq_series K χ hw, hfeq w hw, sub_self]
  have hgz : meromorphicOrderAt g z = ⊤ := by
    by_contra hne
    exact hg.meromorphicOrderAt_ne_top_of_isPreconnected hU hz h2 hne hg2
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hgz] with w hw
  simpa [hgdef, sub_eq_zero] using hw

/-- For a ray-principal character, the ideal series is at least one on real `s > 1`. -/
theorem one_le_re_heckeLSeries_of_principal (χ : HeckeCharacter K) (hχ : FiniteOrder χ)
    (hprin : (toRayClassCharacter K χ hχ).IsPrincipal) {σ : ℝ} (hσ : 1 < σ) :
    1 ≤ (heckeLSeries K χ σ).re := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  have hsum := Complex.hasSum_re (hasSum_idealCoefficient_all K χ hs)
  have hcoef : ∀ I : Ideal (𝓞 K),
      idealCoefficient (primeCoefficient K χ) I = 0 ∨
        idealCoefficient (primeCoefficient K χ) I = 1 := by
    intro I
    by_cases hz : idealCoefficient (primeCoefficient K χ) I = 0
    · exact Or.inl hz
    · right
      have hne := not_or.mp ((idealCoefficient_eq_zero_iff K χ I).not.mp hz)
      exact hprin I hne.1 (not_not.mp hne.2)
  have hterm : ∀ I : Ideal (𝓞 K),
      0 ≤ (idealCoefficient (primeCoefficient K χ) I *
        (Ideal.absNorm I : ℂ) ^ (-(σ : ℂ))).re := by
    intro I
    rcases hcoef I with h | h
    · simp [h]
    · rw [h, one_mul]
      have hreal : (Ideal.absNorm I : ℂ) ^ (-(σ : ℂ)) =
          (((Ideal.absNorm I : ℝ) ^ (-σ) : ℝ) : ℂ) := by
        rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg, Complex.ofReal_natCast]
      rw [hreal, Complex.ofReal_re]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have htop : (idealCoefficient (primeCoefficient K χ) ⊤ *
      (Ideal.absNorm (⊤ : Ideal (𝓞 K)) : ℂ) ^ (-(σ : ℂ))).re = 1 := by
    rw [idealCoefficient_top, Ideal.absNorm_top]
    simp
  calc (1 : ℝ) = (idealCoefficient (primeCoefficient K χ) ⊤ *
        (Ideal.absNorm (⊤ : Ideal (𝓞 K)) : ℂ) ^ (-(σ : ℂ))).re := htop.symm
    _ ≤ (heckeLSeries K χ σ).re := le_hasSum hsum ⊤ (fun I _ => hterm I)

/-- At `s = 1`, a ray-principal finite-order character has no zero. -/
theorem meromorphicOrderAt_one_nonpos_of_principal (χ : HeckeCharacter K) (hχ : FiniteOrder χ)
    (hprin : (toRayClassCharacter K χ hχ).IsPrincipal) :
    meromorphicOrderAt (heckeContinuation K χ) 1 ≤ 0 := by
  by_contra hpos
  have ht := tendsto_zero_of_meromorphicOrderAt_pos (not_le.mp hpos)
  have hmap : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h := (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      intro h
      have h' : σ = 1 := by exact_mod_cast Set.mem_singleton_iff.mp h
      exact (ne_of_gt hσ) h'
  have hcomp := ht.comp hmap
  have hsmall : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ), ‖heckeContinuation K χ (σ : ℂ)‖ < 1 :=
    hcomp.norm.eventually (gt_mem_nhds (by norm_num))
  have hbig : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ), 1 ≤ ‖heckeContinuation K χ (σ : ℂ)‖ := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ' : 1 < σ := hσ
    rw [heckeContinuation_eq_series K χ (by simpa using hσ')]
    exact (one_le_re_heckeLSeries_of_principal K χ hχ hprin hσ').trans (Complex.re_le_norm _)
  obtain ⟨σ, hs, hb⟩ := (hsmall.and hbig).exists
  linarith

/-- **Conditional transfer.** Any function with AxiomMath's four properties for the
ray class character of a finite-order `χ` yields the 31/32 region for the actual
continuation of `χ`. -/
theorem zeroFree_of_rayOutput (χ : HeckeCharacter K) (hχ : FiniteOrder χ) (f : ℂ → ℂ)
    (hfd : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hfent : ¬ (toRayClassCharacter K χ hχ).IsPrincipal → Differentiable ℂ f)
    (hfsum : ∀ s : ℂ, 1 < s.re → HasSum (fun I : Ideal (𝓞 K) =>
      toRayClassCharacter K χ hχ I * (Ideal.absNorm I : ℂ) ^ (-s)) (f s))
    (hfnz : ∀ s : ℂ, 31 / 32 < s.re → (s ≠ 1 ∨ ¬ (toRayClassCharacter K χ hχ).IsPrincipal) →
      f s ≠ 0) :
    MeromorphicZeroFreeOn (heckeContinuation K χ) (rightHalfPlane (31 / 32)) := by
  have hfeq : ∀ s : ℂ, 1 < s.re → f s = heckeLSeries K χ s := fun s hs =>
    (hfsum s hs).unique (hasSum_idealCoefficient_all K χ hs)
  refine ⟨fun s _ => meromorphicOn_heckeContinuation K χ s (Set.mem_univ _), ?_⟩
  intro z hz
  have hz' : 31 / 32 < z.re := hz
  by_cases hz1 : z = 1
  · subst hz1
    by_cases hprin : (toRayClassCharacter K χ hχ).IsPrincipal
    · exact meromorphicOrderAt_one_nonpos_of_principal K χ hχ hprin
    · have hent := hfent hprin
      have heq := heckeContinuation_eventuallyEq_of_analyticOnNhd K χ f Set.univ
        isPreconnected_univ (Set.mem_univ _) (fun w _ => hent.analyticAt w) hfeq
        (Set.mem_univ (1 : ℂ))
      have hfa : AnalyticAt ℂ f 1 := hent.analyticAt 1
      rw [meromorphicOrderAt_congr heq, hfa.meromorphicOrderAt_eq,
        hfa.analyticOrderAt_eq_zero.mpr (hfnz 1 hz' (Or.inr hprin))]
      simp
  · have hU : IsPreconnected ({1}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank
        (by rw [Complex.rank_real_complex]; norm_num) (1 : ℂ)).isPreconnected
    have hfan : AnalyticOnNhd ℂ f ({1}ᶜ) := hfd.analyticOnNhd isOpen_compl_singleton
    have heq := heckeContinuation_eventuallyEq_of_analyticOnNhd K χ f ({1}ᶜ) hU
      (by norm_num) hfan hfeq hz1
    have hfa : AnalyticAt ℂ f z := hfan z hz1
    rw [meromorphicOrderAt_congr heq, hfa.meromorphicOrderAt_eq,
      hfa.analyticOrderAt_eq_zero.mpr (hfnz z hz' (Or.inl hz1))]
    simp

end HeckeAxiom
