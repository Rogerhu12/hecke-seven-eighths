import HeckeGeneral.Analysis.SIntegerMaskedOrbitalPoisson
import HeckeGeneral.Analysis.SIntegerPeriodicTruncation

/-!
# Finite dual approximations for the actual moving-mask orbital formula

Every mask divisor uses the same cutoff parameter, applied at its own actual
dual radius. The finite approximation retains the complete Moebius sum and
both additive zero terms. Its error is exactly the finite sum of the genuine
periodic tails. The fixed seminorm family and constant are selected before
the mask, modulus, periodic coefficient, radii, cutoff, and Schwartz function.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain UniqueFactorizationMonoid
  HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters MeasureTheory
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "T" => sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Q" => SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- A finite expression: each divisor's dual series is replaced by its actual
finite orbit cutoff, and its two original additive zero terms are retained. -/
def sIntegerMaskedPeriodicApproximation
    (c : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) (hc : c ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum OS))
    (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ)
    (hinv : ∀ u : Γ, ∀ a : OS,
      f (Ideal.Quotient.mk _
        (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K u.val).val * a)) =
          f (Ideal.Quotient.mk _ a)) (r : {r : ℝ // 0 < r}) (X : ℝ) : ℂ :=
  ∑ D ∈ M.powerset, (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
    (sIntegerMaskPoissonFactor K S c hc r (sIntegerMaskGenerator K _ D) *
      (∑ q ∈ sIntegerOrbitCutoff K S Γ
        (sIntegerMaskDualRadius K S c hc r (sIntegerMaskGenerator K _ D)) X,
        sIntegerPeriodicFourierProfileTerm K S Γ μv hS h φ c hc f hinv
          (sIntegerMaskGenerator K _ D).val
          (sIntegerMaskDualRadius K S c hc r (sIntegerMaskGenerator K _ D)) q) +
      ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
        (sIntegerMaskPoissonFactor K S c hc r (sIntegerMaskGenerator K _ D) *
            (sIntegerPeriodicDivisorFourier K _ hS c hc f
                (sIntegerMaskGenerator K _ D).val 0 *
              sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) h 0) -
          f 0 * sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0))

/-- The explicit finite coefficient mass in the truncation error. No unit,
Moebius magnitude, or Haar normalization is substituted for its actual value. -/
def sIntegerMaskedTruncationMass
    (c : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) (hc : c ≠ 0)
    (M : Finset (HeightOneSpectrum OS))
    (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (r : {r : ℝ // 0 < r}) : ℝ :=
  ∑ D ∈ M.powerset, ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
    ‖sIntegerMaskPoissonFactor K S c hc r (sIntegerMaskGenerator K _ D)‖ *
    sIntegerPeriodicResidueL1 K (S : Set (HeightOneSpectrum (𝓞 K))) c hc
      (fun a => f (Ideal.Quotient.mk _ (sIntegerMaskGenerator K _ D).val * a)) *
    (1 + (sIntegerMaskDualRadius K S c hc r (sIntegerMaskGenerator K _ D)).val⁻¹)

variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- Exact error identity, before estimating any tail. All zero terms cancel
between the full Poisson formula and its finite approximation. -/
theorem sIntegerMaskedPeriodicApproximation_error
    (c : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) (hc : c ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS))
    (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ)
    (hinv : ∀ u : Γ, ∀ a : OS,
      f (Ideal.Quotient.mk _
        (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K u.val).val * a)) =
          f (Ideal.Quotient.mk _ a)) (r : {r : ℝ // 0 < r}) (X : ℝ) :
    sIntegerWeightedOrbitalSeries K S Γ φ (sIntegerFiniteTestFunction K S h) r
        (fun q => sIntegerOrbitAvoidanceMask K _ Γ M q *
          sIntegerPeriodicOrbitWeight K _ Γ c f hinv q) -
      sIntegerMaskedPeriodicApproximation K S Γ μv c hc hS φ h M f hinv r X =
    ∑ D ∈ M.powerset,
      let d := sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D
      let ρ := sIntegerMaskDualRadius K S c hc r d
      let F := sIntegerPeriodicFourierProfileTerm K S Γ μv hS h φ c hc f hinv d.val ρ
      (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
        sIntegerMaskPoissonFactor K S c hc r d *
        ((∑' q : Q, F q) - ∑ q ∈ sIntegerOrbitCutoff K S Γ ρ X, F q) := by
  rw [sIntegerMaskedPeriodicOrbitalPoisson K S Γ c hc hS ν μv μ φ h hlc hcs M f hinv r]
  unfold sIntegerMaskedPeriodicApproximation
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro D _
  dsimp only
  unfold sIntegerWeightedOrbitalSeries sIntegerPeriodicFourierProfileTerm
  ring

include ν μ in
/-- A single seminorm family and constant control the finite masked
approximation for every moving mask, modulus, coefficient, and radius.
Summability of every dual summand is supplied by the actual periodic tail
theorem, rather than included among the hypotheses. -/
theorem exists_sIntegerMaskedPeriodicApproximation_bound
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (A : ℝ) (hA : 1 < A) (m : ℕ) (hm : Module.finrank ℤ L < m)
    (hOrder : (Module.finrank ℚ K : ℝ) * A ≤ m) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ M : Finset (HeightOneSpectrum OS),
      ∀ c : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K, ∀ hc : c ≠ 0,
      ∀ f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ,
      ∀ hinv : ∀ u : Γ, ∀ a : OS,
        f (Ideal.Quotient.mk _
          (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K u.val).val * a)) =
            f (Ideal.Quotient.mk _ a),
      ∀ r : {r : ℝ // 0 < r}, ∀ φ : SchwartzMap V ℂ, ∀ X : ℝ, 1 ≤ X →
        (∀ D ∈ M.powerset, Summable
          (sIntegerPeriodicFourierProfileTerm K S Γ μv hS h φ c hc f hinv
            (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val
            (sIntegerMaskDualRadius K S c hc r (sIntegerMaskGenerator K _ D)))) ∧
        ‖sIntegerWeightedOrbitalSeries K S Γ φ (sIntegerFiniteTestFunction K S h) r
            (fun q => sIntegerOrbitAvoidanceMask K _ Γ M q *
              sIntegerPeriodicOrbitWeight K _ Γ c f hinv q) -
          sIntegerMaskedPeriodicApproximation K S Γ μv c hc hS φ h M f hinv r X‖ ≤
          C * s.sup (schwartzSeminormFamily ℂ V ℂ) φ * X ^ (1 - A) *
            sIntegerMaskedTruncationMass K S c hc M f r := by
  obtain ⟨s, C, hC, hbound⟩ := exists_sIntegerPeriodicFourier_truncation_bound
    K S Γ ν μv hS h hlc hcs A hA m hm hOrder
  refine ⟨s, C, hC, ?_⟩
  intro M c hc f hinv r φ X hX
  refine ⟨?_, ?_⟩
  · intro D _
    exact (hbound c hc f hinv (sIntegerMaskGenerator K _ D).val φ
      (sIntegerMaskDualRadius K S c hc r (sIntegerMaskGenerator K _ D)) X hX).1
  · rw [sIntegerMaskedPeriodicApproximation_error K S Γ ν μv μ
      c hc hS φ h hlc hcs M f hinv r X]
    let e : Finset (HeightOneSpectrum OS) → ℂ := fun D =>
      let d := sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D
      let ρ := sIntegerMaskDualRadius K S c hc r d
      let F := sIntegerPeriodicFourierProfileTerm K S Γ μv hS h φ c hc f hinv d.val ρ
      (∑' q : Q, F q) - ∑ q ∈ sIntegerOrbitCutoff K S Γ ρ X, F q
    have he (D : Finset (HeightOneSpectrum OS)) : ‖e D‖ ≤
        sIntegerPeriodicResidueL1 K (S : Set (HeightOneSpectrum (𝓞 K))) c hc
          (fun a => f (Ideal.Quotient.mk _ (sIntegerMaskGenerator K _ D).val * a)) *
          C * s.sup (schwartzSeminormFamily ℂ V ℂ) φ *
            (1 + (sIntegerMaskDualRadius K S c hc r (sIntegerMaskGenerator K _ D)).val⁻¹) *
            X ^ (1 - A) :=
      (hbound c hc f hinv (sIntegerMaskGenerator K _ D).val φ
        (sIntegerMaskDualRadius K S c hc r (sIntegerMaskGenerator K _ D)) X hX).2.2
    change ‖∑ D ∈ M.powerset, (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
      sIntegerMaskPoissonFactor K S c hc r (sIntegerMaskGenerator K _ D) * e D‖ ≤ _
    calc
      _ ≤ ∑ D ∈ M.powerset,
          ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
          ‖sIntegerMaskPoissonFactor K S c hc r (sIntegerMaskGenerator K _ D)‖ * ‖e D‖ := by
        simpa only [norm_mul] using norm_sum_le M.powerset
          (fun D => (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
            sIntegerMaskPoissonFactor K S c hc r (sIntegerMaskGenerator K _ D) * e D)
      _ ≤ ∑ D ∈ M.powerset,
          ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
          ‖sIntegerMaskPoissonFactor K S c hc r (sIntegerMaskGenerator K _ D)‖ *
          (sIntegerPeriodicResidueL1 K (S : Set (HeightOneSpectrum (𝓞 K))) c hc
            (fun a => f (Ideal.Quotient.mk _ (sIntegerMaskGenerator K _ D).val * a)) *
            C * s.sup (schwartzSeminormFamily ℂ V ℂ) φ *
            (1 + (sIntegerMaskDualRadius K S c hc r (sIntegerMaskGenerator K _ D)).val⁻¹) *
            X ^ (1 - A)) := by
        apply Finset.sum_le_sum
        intro D _
        exact mul_le_mul_of_nonneg_left (he D) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by
        unfold sIntegerMaskedTruncationMass
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro D _
        ring

end HeckeGeneral.Analysis
