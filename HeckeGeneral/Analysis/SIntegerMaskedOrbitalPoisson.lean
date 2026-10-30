import HeckeGeneral.Analysis.SIntegerPeriodicOrbitalPoisson
import HeckeGeneral.Arithmetic.SIntegerOrbitMask

/-!
# Moving ideal masks in the actual periodic orbital Poisson formula

The prime-ideal avoidance mask is expanded before any Fourier transform.
Absolute summability follows from the genuine bounded-weight orbital
unfolding. Multiplication by a nonzero mask generator then enumerates exactly
the divisible orbits of the original subgroup, including every sector.

Only the choice of the mask generators uses a principal-ideal-ring instance
for the S-integers. Each divisor contributes at its actual norm-scaled radius;
the finite divisor transform retains nonunit dilation and its zero frequency.
The additive zero terms, discriminant factor, and actual Haar covolume remain
explicit. No Poisson, convergence, or decay estimate is an additional input.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain UniqueFactorizationMonoid
  HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters MeasureTheory
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) [Γ.FiniteIndex]

local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "N" => NonzeroRingElements OS
local notation "Q" => SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ

/-- The actual primal radius after substituting `a = d*b`. -/
def sIntegerMaskDilationRadius (r : {r : ℝ // 0 < r}) (d : N) :
    {r : ℝ // 0 < r} :=
  ⟨r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) d).val,
    mul_pos r.property (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) d).property⟩

/-- Bounded coefficients have genuine absolute orbital summability. -/
theorem summable_norm_sIntegerWeightedOrbitalProfile
    (φ : SchwartzMap V ℂ)
    (ψ : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (w : Q → ℂ) (B : ℝ) (hw : ∀ q, ‖w q‖ ≤ B) :
    Summable (fun q : Q => ‖w q *
      sUnitOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K))) φ ψ)
        ⟨r.val * (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val,
          mul_pos r.property (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).property⟩‖) :=
  (hasSum_sIntegerOrbitalProfile_weighted K (S : Set (HeightOneSpectrum (𝓞 K))) Γ
    φ ψ hψ hψsupport r w B hw).summable.norm

/-- The literal prime-ideal avoidance mask preserves absolute convergence. -/
theorem summable_norm_sIntegerMaskedOrbitalProfile
    (φ : SchwartzMap V ℂ)
    (ψ : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum OS))
    (w : Q → ℂ) (B : ℝ) (hw : ∀ q, ‖w q‖ ≤ B) :
    Summable (fun q : Q => ‖sIntegerOrbitAvoidanceMask K
      (S : Set (HeightOneSpectrum (𝓞 K))) Γ M q * w q *
      sUnitOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K))) φ ψ)
        ⟨r.val * (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val,
          mul_pos r.property (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).property⟩‖) := by
  apply summable_norm_sIntegerWeightedOrbitalProfile K S Γ φ ψ hψ hψsupport r
    (fun q => sIntegerOrbitAvoidanceMask K _ Γ M q * w q) B
  intro q
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖w q‖ := mul_le_mul_of_nonneg_right
      (norm_sIntegerOrbitAvoidanceMask_le_one K _ Γ M q) (norm_nonneg _)
    _ ≤ B := by simpa only [one_mul] using hw q

section Principal

variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

/-- Finite inclusion-exclusion and actual orbit dilation, before Poisson.
No finite-index condition on an enlarged group or primitivity of a divisor
is used. Summability of each summand is proved from the test functions. -/
theorem sIntegerMaskedOrbitalSeries_eq_divisor_sum
    (φ : SchwartzMap V ℂ)
    (ψ : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum OS))
    (w : Q → ℂ) (B : ℝ) (hw : ∀ q, ‖w q‖ ≤ B) :
    sIntegerWeightedOrbitalSeries K S Γ φ ψ r
        (fun q => sIntegerOrbitAvoidanceMask K
          (S : Set (HeightOneSpectrum (𝓞 K))) Γ M q * w q) =
      ∑ D ∈ M.powerset, (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
        sIntegerWeightedOrbitalSeries K S Γ φ ψ
          (sIntegerMaskDilationRadius K S r (sIntegerMaskGenerator K _ D))
          (fun q => w (sIntegerOrbitDilation K _ Γ (sIntegerMaskGenerator K _ D) q)) := by
  let P : Q → ℂ := fun q =>
    sUnitOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K))) φ ψ)
      ⟨r.val * (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val,
        mul_pos r.property (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).property⟩
  let F : Finset (HeightOneSpectrum OS) → Q → ℂ := fun D q =>
    (if sIntegerOrbitDivisible K (S : Set (HeightOneSpectrum (𝓞 K))) Γ
      (sIntegerMaskGenerator K _ D) q then 1 else 0) * w q * P q
  have hF (D : Finset (HeightOneSpectrum OS)) : Summable (F D) := by
    apply (hasSum_sIntegerOrbitalProfile_weighted K
      (S : Set (HeightOneSpectrum (𝓞 K))) Γ φ ψ hψ hψsupport r
      (fun q => (if sIntegerOrbitDivisible K _ Γ (sIntegerMaskGenerator K _ D) q
        then 1 else 0) * w q) B ?_).summable
    intro q
    rw [norm_mul]
    have hI : ‖(if sIntegerOrbitDivisible K _ Γ (sIntegerMaskGenerator K _ D) q
        then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> simp
    exact (mul_le_mul_of_nonneg_right hI (norm_nonneg _)).trans
      (by simpa only [one_mul] using hw q)
  have hexpand (q : Q) :
      sIntegerOrbitAvoidanceMask K (S : Set (HeightOneSpectrum (𝓞 K))) Γ M q *
        w q * P q =
      ∑ D ∈ M.powerset, (moebius (IdealMobiusMask.primeProduct D) : ℂ) * F D q := by
    rw [sIntegerOrbitAvoidanceMask_generator_expansion]
    simp only [Finset.sum_mul, F]
    apply Finset.sum_congr rfl
    intro D _
    ring
  have hreindex (D : Finset (HeightOneSpectrum OS)) :
      (∑' q : Q, F D q) = sIntegerWeightedOrbitalSeries K S Γ φ ψ
        (sIntegerMaskDilationRadius K S r (sIntegerMaskGenerator K _ D))
        (fun q => w (sIntegerOrbitDilation K _ Γ (sIntegerMaskGenerator K _ D) q)) := by
    rw [tsum_sIntegerOrbitDilation K (S : Set (HeightOneSpectrum (𝓞 K))) Γ
      (sIntegerMaskGenerator K _ D) (F D)
      (fun q hq => by simp only [F, if_neg hq, zero_mul])]
    unfold sIntegerWeightedOrbitalSeries
    apply tsum_congr
    intro q
    have hdiv : sIntegerOrbitDivisible K (S : Set (HeightOneSpectrum (𝓞 K))) Γ
        (sIntegerMaskGenerator K _ D)
        (sIntegerOrbitDilation K _ Γ (sIntegerMaskGenerator K _ D) q) :=
      (sIntegerOrbitDivisible_iff_exists K _ Γ _ _).mpr ⟨q, rfl⟩
    simp only [F, if_pos hdiv, one_mul, P, sIntegerOrbitNorm_dilation,
      sIntegerMaskDilationRadius]
    apply congrArg (fun t : {r : ℝ // 0 < r} =>
      w (sIntegerOrbitDilation K _ Γ (sIntegerMaskGenerator K _ D) q) *
        sUnitOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K)))
          (sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K))) φ ψ) t)
    apply Subtype.ext
    exact (mul_assoc _ _ _).symm
  change (∑' q : Q, sIntegerOrbitAvoidanceMask K
    (S : Set (HeightOneSpectrum (𝓞 K))) Γ M q * w q * P q) = _
  calc
    _ = ∑' q : Q, ∑ D ∈ M.powerset,
        (moebius (IdealMobiusMask.primeProduct D) : ℂ) * F D q :=
      tsum_congr hexpand
    _ = ∑ D ∈ M.powerset, ∑' q : Q,
        (moebius (IdealMobiusMask.primeProduct D) : ℂ) * F D q :=
      Summable.tsum_finsetSum (s := M.powerset) (fun D _ => (hF D).mul_left _)
    _ = _ := by simp_rw [tsum_mul_left, hreindex]

variable (c : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) (hc : c ≠ 0)
local notation "R" => OS ⧸ Ideal.span (Set.singleton c : Set OS)

/-- Literal periodic coefficients after orbit dilation are exactly `f(d*a)`;
this includes nonunit divisors and every original subgroup sector. -/
theorem sIntegerPeriodicOrbitWeight_dilation (f : R → ℂ)
    (hinv : ∀ u : Γ, ∀ a : OS,
      f (Ideal.Quotient.mk _ (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K
        u.val).val * a)) = f (Ideal.Quotient.mk _ a)) (d : N) (q : Q) :
    sIntegerPeriodicOrbitWeight K (S : Set (HeightOneSpectrum (𝓞 K))) Γ c f hinv
        (sIntegerOrbitDilation K _ Γ d q) =
      sIntegerPeriodicOrbitWeight K (S : Set (HeightOneSpectrum (𝓞 K))) Γ c
        (fun z : R => f (Ideal.Quotient.mk _ d.val * z))
        (sIntegerPeriodic_divisorPullback_literal_invariant K S Γ c f hinv d.val) q := by
  refine Quotient.inductionOn q ?_
  intro a
  simp only [sIntegerOrbitDilation_mk, sIntegerPeriodicOrbitWeight_mk,
    sIntegerNonzeroMul, map_mul]

include hc in
/-- Exact periodic mask expansion as a finite sum of genuinely convergent
periodic orbital series at the divisor-scaled radii. -/
theorem sIntegerMaskedPeriodicOrbitalSeries_eq_divisor_sum
    (φ : SchwartzMap V ℂ)
    (ψ : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum OS))
    (f : R → ℂ)
    (hinv : ∀ u : Γ, ∀ a : OS,
      f (Ideal.Quotient.mk _ (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K
        u.val).val * a)) = f (Ideal.Quotient.mk _ a)) :
    sIntegerWeightedOrbitalSeries K S Γ φ ψ r
        (fun q => sIntegerOrbitAvoidanceMask K _ Γ M q *
          sIntegerPeriodicOrbitWeight K _ Γ c f hinv q) =
      ∑ D ∈ M.powerset, (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
        sIntegerWeightedOrbitalSeries K S Γ φ ψ
          (sIntegerMaskDilationRadius K S r (sIntegerMaskGenerator K _ D))
          (sIntegerPeriodicOrbitWeight K _ Γ c
            (fun z : R => f (Ideal.Quotient.mk _ (sIntegerMaskGenerator K _ D).val * z))
            (sIntegerPeriodic_divisorPullback_literal_invariant K S Γ c f hinv
              (sIntegerMaskGenerator K _ D).val)) := by
  rw [sIntegerMaskedOrbitalSeries_eq_divisor_sum K S Γ φ ψ hψ hψsupport r M
    (sIntegerPeriodicOrbitWeight K _ Γ c f hinv)
    (sIntegerPeriodicResidueL1 K _ c hc f)
    (norm_sIntegerPeriodicOrbitWeight_le_L1 K _ Γ c hc f hinv)]
  apply Finset.sum_congr rfl
  intro D _
  congr 1
  apply congrArg (sIntegerWeightedOrbitalSeries K S Γ φ ψ
    (sIntegerMaskDilationRadius K S r (sIntegerMaskGenerator K _ D)))
  funext q
  exact sIntegerPeriodicOrbitWeight_dilation K S Γ c f hinv _ q

/-- The factor for a single mask divisor, retaining its actual norm. -/
def sIntegerMaskPoissonFactor (r : {r : ℝ // 0 < r}) (d : N) : ℂ :=
  ((sIntegerMaskDilationRadius K S r d).val : ℂ)⁻¹ *
    (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) *
    ((sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).val : ℂ)⁻¹

/-- The true Fourier-side norm radius for the same divisor. -/
def sIntegerMaskDualRadius (r : {r : ℝ // 0 < r}) (d : N) : {r : ℝ // 0 < r} :=
  ⟨((sIntegerMaskDilationRadius K S r d).val *
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).val)⁻¹,
    inv_pos.mpr (mul_pos (sIntegerMaskDilationRadius K S r d).property
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).property)⟩

variable (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- The actual moving-mask orbital Poisson formula. The finite Moebius sum
contains both genuine additive zero contributions for each divisor; it does
not evaluate an orbital profile at radius zero. -/
theorem sIntegerMaskedPeriodicOrbitalPoisson
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (f : R → ℂ)
    (hinv : ∀ u : Γ, ∀ a : OS,
      f (Ideal.Quotient.mk _ (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K
        u.val).val * a)) = f (Ideal.Quotient.mk _ a))
    (r : {r : ℝ // 0 < r}) :
    sIntegerWeightedOrbitalSeries K S Γ φ (sIntegerFiniteTestFunction K S h) r
        (fun q => sIntegerOrbitAvoidanceMask K _ Γ M q *
          sIntegerPeriodicOrbitWeight K _ Γ c f hinv q) =
      ∑ D ∈ M.powerset, (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
        (sIntegerMaskPoissonFactor K S c hc r (sIntegerMaskGenerator K _ D) *
          sIntegerWeightedOrbitalSeries K S Γ (traceSchwartzFourier K φ)
            (sIntegerFiniteFourierTestFunction K S μv h)
            (sIntegerMaskDualRadius K S c hc r (sIntegerMaskGenerator K _ D))
            (sIntegerPeriodicFourierOrbitWeight K _ hS Γ c hc f hinv
              (sIntegerMaskGenerator K _ D).val) +
          ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
            (sIntegerMaskPoissonFactor K S c hc r (sIntegerMaskGenerator K _ D) *
                (sIntegerPeriodicDivisorFourier K _ hS c hc f
                    (sIntegerMaskGenerator K _ D).val 0 *
                  sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) h 0) -
              f 0 * sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0)) := by
  rw [sIntegerMaskedPeriodicOrbitalSeries_eq_divisor_sum K S Γ c hc φ
    (sIntegerFiniteTestFunction K S h)
    (continuous_sIntegerFiniteTestFunction K S h hlc)
    (hasCompactSupport_sIntegerFiniteTestFunction K S h hcs) r M f hinv]
  apply Finset.sum_congr rfl
  intro D _
  congr 1
  unfold sIntegerMaskPoissonFactor sIntegerMaskDualRadius
  exact sIntegerPeriodicOrbitalPoisson K S Γ hS c hc ν μv μ φ h hlc hcs f hinv
    (sIntegerMaskGenerator K _ D).val
    (sIntegerMaskDilationRadius K S r (sIntegerMaskGenerator K _ D))

end Principal

end HeckeGeneral.Analysis
