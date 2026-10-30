import HeckeSkeleton.HeckeBufferedReciprocal
import HeckeSkeleton.HighNormBackgroundExclusion
import ActualCanonicalRowConsumers
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
/-!
Actual s-slice holomorphy of the deleted row Euler continuation and the
full compensated physical kernel. The input concerns the correction
product on the swept domain; it is not a contour-shift or tail estimate.
This project-dependent module requires the original project import chain.
-/

set_option autoImplicit false
noncomputable section
namespace HighBinBoundary.ActualHolomorphy

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.HeckeBufferedReciprocal
open scoped Classical BigOperators Topology ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Actual deleted denominators are differentiable and nonzero above the
actual zero detector. The finite Euler deletion introduces no zero for Re(s)>0. -/
theorem deleted_denominator_regular
    (χ : HeckeCharacter K) (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (H α : ℝ) (hα : 1 / 2 ≤ α)
    (hupper : ZeroUpperBound K χ H α)
    (s : ℂ) (hs : α < s.re) (hheight : |s.im| ≤ H) :
    DifferentiableAt ℂ (heckeDeletedContinuation K χ (exceptionalPrimes K S)) s ∧
      heckeDeletedContinuation K χ (exceptionalPrimes K S) s ≠ 0 := by
  have hL := differentiable_heckeContinuation_of_nonNorm K χ hχ
  have hnon := continuation_ne_zero_of_upper K χ hχ H α hα hupper s hs hheight
  constructor
  · exact (heckeEulerDeletionPolynomial_analyticAt K χ (exceptionalPrimes K S) s).differentiableAt.mul
      (hL s)
  · exact mul_ne_zero
      (heckeEulerDeletionPolynomial_ne_zero K χ (exceptionalPrimes K S) (by linarith)) hnon

/-- Holomorphy of the actual Euler-continuation s-slice. Companion coverage
and the upper-zero height are explicit; they are not inferred from finiteness. -/
theorem rowEulerContinuation_differentiableAt_s
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E : RowEulerData K S P)
    (Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (hnorm : ∀ t : ℝ, ψ * conjugate (E.rows.character u) ≠ heckeNormTwist K t)
    (H α : ℝ) (hα : 1 / 2 ≤ α)
    (hbelow : rowZeroBelow K S ψ Θ P E u H α)
    (s w z : ℂ) (hs : α < s.re) (hheight : |s.im| ≤ H)
    (hcorr : DifferentiableAt ℂ (fun s => rowCorrection K S P ψ E Q u s w z) s) :
    DifferentiableAt ℂ (fun s => rowEulerContinuation K S P ψ E Q u s w z) s := by
  have hmem := denominator_mem_physicalRowFamily K S ψ Θ P E u hΘ
  have hupper : ZeroUpperBound K (ψ * conjugate (E.rows.character u)) H α :=
    hbelow _ hmem
  obtain ⟨hd, hn⟩ := deleted_denominator_regular K S
    (ψ * conjugate (E.rows.character u)) hnorm H α hα hupper s hs hheight
  exact ((differentiableAt_const _).div hd hn).mul hcorr

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S) → Measure (p.val.adicCompletion K))
variable [∀ p : S, (μ p).IsAddHaarMeasure]

/-- The complete compensated finite prime/slot sum is holomorphic in s.
Every marked Euler continuation remains in place, including zero terms. -/
theorem compensatedRowMellinKernel_differentiableAt_s
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E : RowEulerData K S P)
    (g : PrimeWindowGeometry) (T Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ)
    (u : FrequencyRow K S)
    (hnorm : ∀ t : ℝ, ψ * conjugate (E.rows.character u) ≠ heckeNormTwist K t)
    (H α : ℝ) (hα : 1 / 2 ≤ α)
    (hbelow : rowZeroBelow K S ψ Θ P E u H α)
    (Z : ℝ) (hZ : 0 < Z)
    (s w z : ℂ) (hs : α < s.re) (hheight : |s.im| ≤ H)
    (hcorr : ∀ Q : Finset (ExteriorPrime K S),
      DifferentiableAt ℂ (fun s => rowCorrection K S P ψ E Q u s w z) s) :
    DifferentiableAt ℂ (fun s => compensatedRowMellinKernel K S μ P ψ E g T u Z s w z) s := by
  have hrow (Q : Finset (ExteriorPrime K S)) :=
    rowEulerContinuation_differentiableAt_s K S P ψ E Θ hΘ Q u hnorm
      H α hα hbelow s w z hs hheight (hcorr Q)
  have hpow (J : ExteriorIdeal K S) :
      DifferentiableAt ℂ (fun s : ℂ => ((Z * exteriorNorm K S J : ℝ) : ℂ) ^ (s + z - 1)) s := by
    apply ((differentiableAt_id.add_const z).sub_const 1).const_cpow
    exact Or.inl (Complex.ofReal_ne_zero.mpr
      (mul_pos hZ (idealNorm_pos K J.val)).ne')
  have hsum : DifferentiableAt ℂ
      (fun s => ∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
        (∏ i : Fin g.slots, windowWeight K S g Z i (p i)) *
        ∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
          let selected := subsetPrimeIdeal K S p J
          let marked := subsetPrimeIdeal K S p (Finset.univ \ J)
          (-1 : ℂ) ^ J.card * (exteriorNorm K S selected : ℂ) ^ (-(3 / 2 : ℂ)) *
            conj (heckeIdealCoefficient K ψ marked.val) *
            ((Z ^ (17 / 48 : ℝ) / exteriorNorm K S selected : ℝ) : ℂ) ^ (1 / 2 - z) *
            ((Z * exteriorNorm K S marked : ℝ) : ℂ) ^ (s + z - 1) *
            ((Z ^ (23 / 48 : ℝ) / exteriorNorm K S selected : ℝ) : ℂ) ^ (w - 1) *
            rowEulerContinuation K S P ψ E ((Finset.univ \ J).image p) u s w z) s := by
    apply DifferentiableAt.fun_sum
    intro p _
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.fun_sum
    intro J _
    dsimp only
    exact (((hpow (subsetPrimeIdeal K S p (Finset.univ \ J))).const_mul _).mul_const _).mul
      (hrow ((Finset.univ \ J).image p))
  exact (((((differentiableAt_id.add_const z).sub_const 1).pow 2).cexp.mul_const _).mul_const _
    |>.mul_const _ |>.mul hsum).div_const _

/-- On all sufficiently high rows, finite character fibers remove the
background non-norm hypothesis. The cutoff precedes the row and heights. -/
theorem eventually_compensatedRowMellinKernel_differentiableAt_s
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E : RowEulerData K S P)
    (g : PrimeWindowGeometry) (T Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → ∀ u : FrequencyRow K S,
      Z ^ d ≤ frequencyRowNorm K S u →
      ∀ H α : ℝ, 1 / 2 ≤ α → rowZeroBelow K S ψ Θ P E u H α →
      ∀ s w z : ℂ, α < s.re → |s.im| ≤ H →
      (∀ Q : Finset (ExteriorPrime K S),
        DifferentiableAt ℂ (fun s => rowCorrection K S P ψ E Q u s w z) s) →
      DifferentiableAt ℂ (fun s => compensatedRowMellinKernel K S μ P ψ E g T u Z s w z) s := by
  have hFib := HeckeSkeleton.ActualCanonicalRowConsumers.rowCharacter_fiber_finite K S P E
  let v : InfinitePlace K := Classical.choice inferInstance
  obtain ⟨Z₀, hZ₀, hnon⟩ :=
    HeckeSkeleton.HighNormBackgroundExclusion.high_rows_exclude_background_norm_twists
      K S P E.rows hFib v ({ψ} : Finset (HeckeCharacter K))
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZ d hd u hu H α hα hbelow s w z hs hheight hcorr
  have hnorm := (hnon Z hZ d hd u hu ψ (Finset.mem_singleton_self ψ)).2
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one (hZ₀.trans hZ)
  exact compensatedRowMellinKernel_differentiableAt_s K S μ P ψ E g T Θ hΘ u
    hnorm H α hα hbelow Z hZpos s w z hs hheight hcorr

end HighBinBoundary.ActualHolomorphy
