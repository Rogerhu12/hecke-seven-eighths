import HeckeGeneral.Analysis.HeckeContinuation
import FLTReuse.M5808d10d83f2fccd
import FLTReuse.Mfbd03b0511a8bca3

/-!
# Exact poles of actual unitary Hecke continuations

The trivial character's Euler product is the proved Dedekind zeta product.
The audited Dedekind theorem supplies an entire pole-cleared function whose
value at one is nonzero. Translation by the actual norm-twist parameter
therefore proves an order exactly minus one, not merely an upper bound on
pole multiplicity. Uniqueness of meromorphic continuation transfers this
order to the chosen Hecke continuation, independently of its point values.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Arithmetic
open scoped Topology

variable (F : Type) [Field F] [NumberField F]

theorem primeCoefficient_trivial (v : HeightOneSpectrum (𝓞 F)) :
    primeCoefficient F 1 v = 1 := by
  rw [primeCoefficient_of_unramified F 1 v (unramifiedAt_one F v)]
  rfl

/-- Identification uses uniqueness of the two actual convergent Euler products. -/
theorem heckeLSeries_trivial_eq_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    heckeLSeries F 1 s = NumberField.dedekindZeta F s := by
  have h := hasProd_heckeLSeries F 1 hs
  have h' := NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta F s hs
  apply HasProd.unique h
  convert h' using 1
  funext v
  simp only [heckeLocalEulerFactor, eulerPolynomial, primeCoefficient_trivial,
    one_mul, residueCard, Complex.ofReal_natCast]

/-- The norm branch has a genuinely nonvanishing pole-cleared numerator. -/
theorem exists_nonzero_poleCleared_normTwist (t : ℝ) :
    ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧ Q (heckeNormPole t) ≠ 0 ∧
      ∀ s : ℂ, 1 < s.re →
        Q s = (s - heckeNormPole t) * heckeLSeries F (heckeNormTwist F t) s := by
  obtain ⟨R, hR, hR1, hReq, _htrivial⟩ :=
    NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero F
  let Q : ℂ → ℂ := fun s => R (s - (t : ℂ) * Complex.I)
  refine ⟨Q, hR.comp (differentiable_id.sub_const _), ?_, fun s hs => ?_⟩
  · simpa [Q, heckeNormPole] using hR1
  · have hz : 1 < (s - (t : ℂ) * Complex.I).re := by simpa using hs
    have htwist := heckeLSeries_normTwist F 1 t s
    rw [one_mul] at htwist
    change R (s - (t : ℂ) * Complex.I) = _
    rw [hReq _ hz, ← heckeLSeries_trivial_eq_dedekindZeta F hz, ← htwist]
    congr 1
    unfold heckeNormPole
    ring

/-- Every actual pure norm twist has a simple pole at its prescribed point. -/
theorem meromorphicOrderAt_heckeContinuation_normTwist (t : ℝ) :
    meromorphicOrderAt (heckeContinuation F (heckeNormTwist F t))
      (heckeNormPole t) = (-1 : WithTop ℤ) := by
  obtain ⟨Q, hQ, hQ0, hQeq⟩ := exists_nonzero_poleCleared_normTwist F t
  let L : ℂ → ℂ := fun s => Q s / (s - heckeNormPole t)
  have hL : MeromorphicOn L Set.univ := by
    intro s _hs
    exact (hQ.analyticAt s).meromorphicAt.div
      (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hLeq : ∀ s : ℂ, 1 < s.re → L s = heckeLSeries F (heckeNormTwist F t) s := by
    intro s hs
    dsimp only [L]
    rw [hQeq s hs]
    exact mul_div_cancel_left₀ _ (sub_heckeNormPole_ne_zero hs t)
  have hsame := heckeContinuation_eventuallyEq_of_meromorphic F (heckeNormTwist F t)
    L hL hLeq (heckeNormPole t)
  rw [← meromorphicOrderAt_congr hsame]
  have hQorder : meromorphicOrderAt Q (heckeNormPole t) = 0 := by
    have ha := hQ.analyticAt (heckeNormPole t)
    rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr hQ0]
    simp
  dsimp only [L]
  change meromorphicOrderAt (Q / (id - fun _ : ℂ => heckeNormPole t))
    (heckeNormPole t) = (-1 : WithTop ℤ)
  rw [meromorphicOrderAt_div (hQ.analyticAt _).meromorphicAt
    (analyticAt_id.sub analyticAt_const).meromorphicAt,
    hQorder]
  change 0 - meromorphicOrderAt (fun s : ℂ => s - heckeNormPole t)
    (heckeNormPole t) = (-1 : WithTop ℤ)
  rw [meromorphicOrderAt_id_sub_const]
  norm_num

/-- Pole classification for every actual continuous unitary Hecke character. -/
theorem heckeContinuation_pole_iff (χ : HeckeCharacter F) (s : ℂ) :
    meromorphicOrderAt (heckeContinuation F χ) s < 0 ↔
      ∃ t : ℝ, χ = heckeNormTwist F t ∧ s = heckeNormPole t := by
  constructor
  · intro hs
    by_cases hχ : ∃ t : ℝ, χ = heckeNormTwist F t
    · obtain ⟨t, ht, ha⟩ := heckeContinuation_normBranch_analyticAwayPole F χ hχ
      refine ⟨t, ht, ?_⟩
      by_contra hne
      exact (not_lt_of_ge (ha s hne).meromorphicOrderAt_nonneg) hs
    · have hn : ∀ t : ℝ, χ ≠ heckeNormTwist F t := fun t ht => hχ ⟨t, ht⟩
      exact False.elim ((not_lt_of_ge
        ((differentiable_heckeContinuation_of_nonNorm F χ hn).analyticAt s).meromorphicOrderAt_nonneg) hs)
  · rintro ⟨t, rfl, rfl⟩
    rw [meromorphicOrderAt_heckeContinuation_normTwist]
    exact WithTop.coe_lt_coe.mpr (show (-1 : ℤ) < 0 by omega)

end HeckeGeneral.Analysis
