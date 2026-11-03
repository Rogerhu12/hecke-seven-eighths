import HeckeSkeleton.WindowPIT.Counting
import HeckeSkeleton.WindowPIT.Envelope
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.IdealPool
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

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

/-- The fixed-ratio PIT interval fits inside the power-scale interval,
and its logarithmic loss is absorbed by any positive exponent loss. -/
private theorem power_scale_pool_parameters (c ell eps X₀ : ℝ)
    (hc : 0 < c) (hell : 0 < ell) (heps : 0 < eps) (hX₀ : 1 < X₀) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      X₀ ≤ Z ^ ell / 2 ∧ Z ^ (ell / 2) ≤ Z ^ ell / 2 ∧
      Z ^ (ell - eps) ≤ c * (Z ^ ell / 2) / Real.log (Z ^ ell / 2) := by
  have hsmall : 0 < c / (2 * ell) := by positivity
  have hlog := (isLittleO_log_rpow_atTop heps).bound hsmall
  have hlarge := (tendsto_rpow_atTop hell).eventually
    (Filter.eventually_ge_atTop (2 * X₀))
  have hhalf := (tendsto_rpow_atTop (show 0 < ell / 2 by positivity)).eventually
    (Filter.eventually_ge_atTop (2 : ℝ))
  have hevent : ∀ᶠ Z : ℝ in Filter.atTop,
      1 < Z ∧ 2 * X₀ ≤ Z ^ ell ∧ 2 ≤ Z ^ (ell / 2) ∧
        Real.log Z ≤ c / (2 * ell) * Z ^ eps := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), hlarge, hhalf, hlog]
      with Z hZ hlarge hhalf hlog
    refine ⟨hZ, hlarge, hhalf, ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.log_pos hZ),
      abs_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) eps)] using hlog
  obtain ⟨Z₁, hZ₁⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨max Z₁ 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro Z hZ
  obtain ⟨hZ1, hlarge, hhalf, hlog⟩ := hZ₁ Z ((le_max_left _ _).trans hZ)
  have hZpos : 0 < Z := zero_lt_one.trans hZ1
  let X : ℝ := Z ^ ell / 2
  have hX₀X : X₀ ≤ X := by
    dsimp only [X]
    linarith
  have hX1 : 1 < X := hX₀.trans_le hX₀X
  have hXpos : 0 < X := zero_lt_one.trans hX1
  have hpow : 0 ≤ Z ^ ell := Real.rpow_nonneg hZpos.le ell
  have hsquare : Z ^ ell = (Z ^ (ell / 2)) ^ 2 := by
    calc
      Z ^ ell = Z ^ ((ell / 2) * (2 : ℝ)) := by congr 1 <;> ring
      _ = (Z ^ (ell / 2)) ^ 2 := Real.rpow_mul_natCast hZpos.le (ell / 2) 2
  have hlow : Z ^ (ell / 2) ≤ X := by
    have hprod := mul_nonneg (sub_nonneg.mpr hhalf)
      (Real.rpow_nonneg hZpos.le (ell / 2))
    dsimp only [X]
    rw [hsquare]
    nlinarith
  have hlogX : Real.log X ≤ ell * Real.log Z := by
    calc
      Real.log X ≤ Real.log (Z ^ ell) := Real.log_le_log hXpos (by
        dsimp only [X]
        linarith)
      _ = ell * Real.log Z := Real.log_rpow hZpos ell
  have hlogBound : Real.log X ≤ (c / 2) * Z ^ eps := by
    calc
      Real.log X ≤ ell * Real.log Z := hlogX
      _ ≤ ell * (c / (2 * ell) * Z ^ eps) :=
        mul_le_mul_of_nonneg_left hlog hell.le
      _ = (c / 2) * Z ^ eps := by field_simp [hell.ne'] <;> ring
  refine ⟨hX₀X, hlow, ?_⟩
  change Z ^ (ell - eps) ≤ c * X / Real.log X
  apply (le_div_iff₀ (Real.log_pos hX1)).mpr
  calc
    Z ^ (ell - eps) * Real.log X ≤
        Z ^ (ell - eps) * ((c / 2) * Z ^ eps) :=
      mul_le_mul_of_nonneg_left hlogBound (Real.rpow_nonneg hZpos.le _)
    _ = (c / 2) * Z ^ ((ell - eps) + eps) := by
      rw [Real.rpow_add hZpos]
      ring
    _ = c * X := by
      rw [sub_add_cancel]
      dsimp only [X]
      ring

/-- A single actual prime-ideal pool in the power window used by the
amplifier.  Both the cardinality and the exclusion of every fixed bad
prime follow from the prime ideal theorem; they are not input bounds.
Taking `ell = σ / 3` gives the norm window `[Z^(σ/6), Z^(σ/3)]`. -/
theorem exists_power_scale_prime_ideal_pool
    (bad : Finset (HeightOneSpectrum (𝓞 K))) (ell eps : ℝ)
    (hell : 0 < ell) (heps : 0 < eps) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∃ pool : Finset (Ideal (𝓞 K)),
        Z ^ (ell - eps) ≤ (pool.card : ℝ) ∧
        (∀ p ∈ pool, Prime p ∧ Z ^ (ell / 2) ≤ (Ideal.absNorm p : ℝ) ∧
          (Ideal.absNorm p : ℝ) ≤ Z ^ ell) ∧
        (∀ p ∈ pool, ∀ v ∈ bad, p ≠ v.asIdeal) := by
  obtain ⟨c, X₀, hc, hX₀, hpool⟩ := exists_prime_ideal_pool K bad
  obtain ⟨Z₀, hZ₀, hscale⟩ := power_scale_pool_parameters c ell eps X₀ hc hell heps hX₀
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZ
  obtain ⟨hX, hlower, hcard⟩ := hscale Z hZ
  obtain ⟨pool, hcount, hnorm, hbad⟩ := hpool (Z ^ ell / 2) hX
  refine ⟨pool, hcard.trans hcount, ?_, hbad⟩
  intro p hp
  obtain ⟨hprime, hpLower, hpUpper⟩ := hnorm p hp
  refine ⟨hprime, hlower.trans hpLower, ?_⟩
  have he : 2 * (Z ^ ell / 2) = Z ^ ell := by ring
  simpa only [he] using hpUpper

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
#print axioms HeckeSkeleton.Moments.EngineStep.exists_power_scale_prime_ideal_pool
