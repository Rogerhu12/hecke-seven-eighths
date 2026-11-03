import HeckeSkeleton.WindowPIT.Envelope
import HeckeSkeleton.WindowPIT.PositiveInterval
import HeckeSkeleton.WindowPIT.IntervalAsymptotics

/-! A positive smooth prime window is bounded below by the prime ideal count
on one fixed-ratio subinterval where its weight has a positive lower bound. -/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.WindowPIT

open NumberField IsDedekindDomain Filter Asymptotics
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem window_prime_lower_of_counting
    (hP : TauCeti.primeCount K Set.univ ~[atTop] (fun X : ℝ => X / Real.log X))
    (w : SmoothAnnularTest)
    (hre : ∀ y, (w.toFun y).im = 0) (hnn : ∀ y, 0 ≤ (w.toFun y).re)
    (hne : ∃ y, w.toFun y ≠ 0) (hsupp : Function.support w.toFun ⊆ Set.Ioo 1 2) :
    ∃ c X₀ : ℝ, 0 < c ∧ 1 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      c * X / Real.log X ≤
        ∑ p ∈ windowPrimes K S X, (w.toFun ((p.asIdeal.absNorm : ℝ) / X)).re := by
  obtain ⟨a, b, m, ha, hab, hb, hm, hweight⟩ :=
    exists_positive_interval w hre hnn hne hsupp
  obtain ⟨c₀, X₀, hc₀, hX₀, hcount⟩ :=
    interval_lower_of_equivalent (TauCeti.primeCount K Set.univ) hP a b ha hab
  obtain ⟨R, _hR, hnorm⟩ := exists_prime_norm_bound K S
  refine ⟨m * c₀, max X₀ R, mul_pos hm hc₀,
    hX₀.trans_le (le_max_left _ _), ?_⟩
  intro X hX
  have hXX₀ : X₀ ≤ X := (le_max_left _ _).trans hX
  have hRX : R ≤ X := (le_max_right _ _).trans hX
  have hXpos : 0 < X := by linarith
  have hS : ∀ p ∈ S, (p.asIdeal.absNorm : ℝ) ≤ X :=
    fun p hp => (hnorm p hp).trans hRX
  let Q := TauCeti.primesLE K (b * X) \ TauCeti.primesLE K (a * X)
  have hQ (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ Q) :
      p ∈ windowPrimes K S X ∧
        a ≤ (p.asIdeal.absNorm : ℝ) / X ∧
          (p.asIdeal.absNorm : ℝ) / X ≤ b :=
    prime_interval_mem K S hXpos ha hb hS p hp
  have hcard : c₀ * X / Real.log X ≤ (Q.card : ℝ) := by
    have h := hcount X hXX₀
    rw [prime_interval_card K hXpos.le ha hab] at h
    exact h
  have hsum : m * (Q.card : ℝ) ≤
      ∑ p ∈ Q, (w.toFun ((p.asIdeal.absNorm : ℝ) / X)).re := by
    calc
      m * (Q.card : ℝ) = ∑ _p ∈ Q, m := by simp [mul_comm]
      _ ≤ ∑ p ∈ Q, (w.toFun ((p.asIdeal.absNorm : ℝ) / X)).re :=
        Finset.sum_le_sum (fun p hp => hweight _ (hQ p hp).2)
  have hQsub : Q ⊆ windowPrimes K S X := fun p hp => (hQ p hp).1
  have hsum_window :
      (∑ p ∈ Q, (w.toFun ((p.asIdeal.absNorm : ℝ) / X)).re) ≤
        ∑ p ∈ windowPrimes K S X, (w.toFun ((p.asIdeal.absNorm : ℝ) / X)).re :=
    Finset.sum_le_sum_of_subset_of_nonneg hQsub (fun p _ _ => hnn _)
  calc
    (m * c₀) * X / Real.log X = m * (c₀ * X / Real.log X) := by ring
    _ ≤ m * (Q.card : ℝ) := mul_le_mul_of_nonneg_left hcard hm.le
    _ ≤ ∑ p ∈ Q, (w.toFun ((p.asIdeal.absNorm : ℝ) / X)).re := hsum
    _ ≤ ∑ p ∈ windowPrimes K S X, (w.toFun ((p.asIdeal.absNorm : ℝ) / X)).re := hsum_window

end HeckeSkeleton.WindowPIT
