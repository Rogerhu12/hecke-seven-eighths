import HeckeGeneral.Analysis.PhysicalProbePrincipal
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting

/-! The prime-window envelope and the inclusive prime-counting carriers use
the same height-one prime ideals and the same absolute norm. -/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.WindowPIT

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.Analysis.SquarefreeAmplification
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The exact envelope used by the prime normalizer. -/
def windowPrimes (X : ℝ) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (finitePrimeEnvelope K (dyadicIdealSupport K X)).filter (fun p => p ∉ S)

theorem mem_windowPrimes_of_norm_le {X : ℝ} (hX : 0 ≤ X)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S)
    (hnorm : (p.asIdeal.absNorm : ℝ) ≤ 2 * X) :
    p ∈ windowPrimes K S X := by
  let I : NonzeroIdeal K := ⟨p.asIdeal, mem_nonZeroDivisors_of_ne_zero p.ne_bot⟩
  have hI : I ∈ dyadicIdealSupport K X :=
    (mem_dyadicIdealSupport_iff K hX I).mpr hnorm
  have hpI : p ∈ idealPrimeSupport K I :=
    (mem_idealPrimeSupport_iff K I p).mpr dvd_rfl
  exact Finset.mem_filter.mpr
    ⟨idealPrimeSupport_subset_envelope K _ I hI hpI, hp⟩

/-- An interval count is the cardinality of the difference of the inclusive
cutoffs; the lower endpoint is excluded. -/
theorem prime_interval_card {X a b : ℝ} (hX : 0 ≤ X)
    (_ha : 1 < a) (hab : a < b) :
    TauCeti.primeCount K Set.univ (b * X) -
        TauCeti.primeCount K Set.univ (a * X) =
      ((TauCeti.primesLE K (b * X) \ TauCeti.primesLE K (a * X)).card : ℝ) := by
  have hcount (Y : ℝ) : TauCeti.primeCount K Set.univ Y =
      ((TauCeti.primesLE K Y).card : ℝ) := by
    simpa using TauCeti.primeCount_eq_card (K := K)
      (Set.univ : Set (HeightOneSpectrum (𝓞 K))) Y
  have hsub : TauCeti.primesLE K (a * X) ⊆ TauCeti.primesLE K (b * X) := by
    intro p hp
    apply (TauCeti.mem_normLE
      (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal.absNorm)).mpr
    exact ((TauCeti.mem_normLE
      (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal.absNorm)).mp hp).trans
      (mul_le_mul_of_nonneg_right hab.le hX)
  have hcard :
      ((TauCeti.primesLE K (b * X) \ TauCeti.primesLE K (a * X)).card : ℝ) +
        ((TauCeti.primesLE K (a * X)).card : ℝ) =
          ((TauCeti.primesLE K (b * X)).card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hsub
  rw [hcount, hcount]
  linarith

/-- Once the exceptional primes have norm at most `X`, every prime in an
interior fixed-ratio interval lies in the normalizer's window. -/
theorem prime_interval_mem {X a b : ℝ} (hX : 0 < X) (ha : 1 < a)
    (hb : b < 2)
    (hS : ∀ p ∈ S, (p.asIdeal.absNorm : ℝ) ≤ X)
    (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ TauCeti.primesLE K (b * X) \ TauCeti.primesLE K (a * X)) :
    p ∈ windowPrimes K S X ∧
      a ≤ (p.asIdeal.absNorm : ℝ) / X ∧
        (p.asIdeal.absNorm : ℝ) / X ≤ b := by
  obtain ⟨hpb, hpa⟩ := Finset.mem_sdiff.mp hp
  have hupper : (p.asIdeal.absNorm : ℝ) ≤ b * X :=
    (TauCeti.mem_normLE
      (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal.absNorm)).mp hpb
  have hlower : a * X < (p.asIdeal.absNorm : ℝ) := by
    apply lt_of_not_ge
    intro h
    exact hpa ((TauCeti.mem_normLE
      (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal.absNorm)).mpr h)
  have hpS : p ∉ S := by
    intro h
    have hsmall := hS p h
    have hXa : X < a * X := by nlinarith
    linarith
  refine ⟨mem_windowPrimes_of_norm_le K S hX.le p hpS
    (hupper.trans (mul_le_mul_of_nonneg_right hb.le hX.le)), ?_, ?_⟩
  · exact (le_div_iff₀ hX).mpr hlower.le
  · exact (div_le_iff₀ hX).mpr hupper

/-- A finite exceptional set has one real norm bound, chosen strictly above
one even when the exceptional set is empty. -/
theorem exists_prime_norm_bound [Fintype S] :
    ∃ R : ℝ, 1 < R ∧ ∀ p ∈ S, (p.asIdeal.absNorm : ℝ) ≤ R := by
  have hfin : ((fun p : HeightOneSpectrum (𝓞 K) =>
      (p.asIdeal.absNorm : ℝ)) '' S).Finite := (Set.toFinite S).image _
  obtain ⟨R, hR⟩ := hfin.bddAbove
  refine ⟨max R 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
    (le_max_right _ _), ?_⟩
  intro p hp
  exact (hR ⟨p, hp, rfl⟩).trans (le_max_left _ _)

end HeckeSkeleton.WindowPIT
