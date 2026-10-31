import HeckeSkeleton.WindowPIT.Counting
import HeckeSkeleton.WindowPIT.Envelope
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.IdealPool

/-!
# The one pool is supplied by the actual prime ideal theorem

The labels are distinct prime ideals in a fixed-ratio norm interval.
All fixed bad primes are excluded uniformly by the threshold.  The later
row and frozen-support deletions use `ideal_pool_eligible_count`, so no
fresh pool is chosen for a different row or for an amplifier error.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain HeckeSkeleton.WindowPIT

variable (K : Type) [Field K] [NumberField K]

/-- An unconditional pool of actual prime ideals with quantitative size.
The same `pool` is used for all rows at the chosen scale. -/
theorem exists_prime_ideal_pool (bad : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ c X₀ : ℝ, 0 < c ∧ 1 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∃ pool : Finset (Ideal (𝓞 K)),
        c * X / Real.log X ≤ (pool.card : ℝ) ∧
        (∀ p ∈ pool, Prime p ∧ X ≤ (Ideal.absNorm p : ℝ) ∧
          (Ideal.absNorm p : ℝ) ≤ 2 * X) ∧
        (∀ p ∈ pool, ∀ v ∈ bad, p ≠ v.asIdeal) := by
  obtain ⟨c, X₁, hc, hX₁, hcount⟩ :=
    primeCount_interval_lower K (5 / 4) (7 / 4) (by norm_num) (by norm_num)
  let R : ℝ := 1 + ∑ v ∈ bad, (v.asIdeal.absNorm : ℝ)
  refine ⟨c, max X₁ R, hc, hX₁.trans_le (le_max_left _ _), ?_⟩
  intro X hX
  have hXX₁ : X₁ ≤ X := (le_max_left _ _).trans hX
  have hRX : R ≤ X := (le_max_right _ _).trans hX
  have hXpos : 0 < X := (zero_lt_one.trans hX₁).trans_le hXX₁
  let Q := TauCeti.primesLE K ((7 / 4) * X) \ TauCeti.primesLE K ((5 / 4) * X)
  let pool := Q.image HeightOneSpectrum.asIdeal
  have hnorm (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ Q) :
      X < (v.asIdeal.absNorm : ℝ) ∧ (v.asIdeal.absNorm : ℝ) ≤ 2 * X := by
    obtain ⟨hupper, hlower⟩ := Finset.mem_sdiff.mp hv
    have hu := (TauCeti.mem_normLE
      (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal.absNorm)).mp hupper
    have hl : (5 / 4) * X < (v.asIdeal.absNorm : ℝ) := by
      apply lt_of_not_ge
      intro hn
      exact hlower ((TauCeti.mem_normLE
        (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal.absNorm)).mpr hn)
    constructor <;> linarith
  have hcard : c * X / Real.log X ≤ (Q.card : ℝ) := by
    have he := hcount X hXX₁
    rw [prime_interval_card K hXpos.le (by norm_num : (1 : ℝ) < 5 / 4)
      (by norm_num : (5 / 4 : ℝ) < 7 / 4)] at he
    exact he
  refine ⟨pool, ?_, ?_, ?_⟩
  · simpa only [pool, Finset.card_image_of_injective Q HeightOneSpectrum.asIdeal_injective]
      using hcard
  · intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨v.prime, (hnorm v hv).1.le, (hnorm v hv).2⟩
  · intro p hp v hv he
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    have hvnorm : (v.asIdeal.absNorm : ℝ) ≤ R := by
      have hs := Finset.single_le_sum (s := bad)
        (f := fun q : HeightOneSpectrum (𝓞 K) => (q.asIdeal.absNorm : ℝ))
        (fun q _ => Nat.cast_nonneg _) hv
      dsimp only [R]
      linarith
    have hwlarge := (hnorm w hw).1
    rw [he] at hwlarge
    linarith

/-- Combining the one PIT pool with the uniform deletion ledger gives
the exact cardinal input needed by the amplifier. -/
theorem pit_pool_after_uniform_deletions
    (pool : Finset (Ideal (𝓞 K))) (hp : ∀ p ∈ pool, Prime p)
    (frozen h : Ideal (𝓞 K)) (hfrozen : frozen ≠ 0) (hh : h ≠ 0)
    (Z ell B M density c X : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ p ∈ pool, Z ^ ell ≤ (Ideal.absNorm p : ℝ))
    (hfrozenNorm : (Ideal.absNorm frozen : ℝ) ≤ Z ^ B)
    (hrowNorm : (Ideal.absNorm h : ℝ) ≤ Z ^ M)
    (hcount : c * X / Real.log X ≤ (pool.card : ℝ))
    (hbudget : density + M / ell + B / ell ≤ c * X / Real.log X) :
    density ≤ ((pool.filter (idealPoolEligible frozen h)).card : ℝ) :=
  ideal_pool_eligible_count pool hp frozen h hfrozen hh Z ell B M density hZ hell
    hlower hfrozenNorm hrowNorm (hbudget.trans hcount)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.exists_prime_ideal_pool
