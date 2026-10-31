import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalTailBound
import HeckeSkeleton.Moments.MOM_INV_STEP.AdaptiveFrequencyTail

/-! Actual primitive Poisson tails with source-local frozen cutoffs. -/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalAdaptiveTail

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton MeasureTheory
open ActualFiniteSource PrimitivePoissonSource PrimitiveFourier ConductorMasks CanonicalPoissonSplit
  FirstDualTruncation CanonicalTailBound ActualPoissonScale PrincipalSource
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
  [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Orbit" => SIntegerOrbits K Sset Γ
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

def dualRadius (B : PrimeBlock K Sset) (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (r : {r : ℝ // 0 < r}) (δ : Finset (HeightOneSpectrum OS)) : {r : ℝ // 0 < r} :=
  sIntegerMaskDualRadius K S (primitiveModulus K S D B t)
    (primitiveModulus_ne_zero K S D B t) r (sIntegerMaskGenerator K Sset δ)

/-- A literal retained dual sum with one radius per frozen divisor. -/
def retainedDual (b : ActualMaskedPoissonBlock K S Γ)
    (H : Finset (HeightOneSpectrum OS) → ℝ) : ℂ :=
  ∑ δ ∈ b.mask.powerset, b.divisorCoefficient δ *
    (b.prefactor δ * primitiveRetained K S D Γ μv b δ (H δ))

def dualTail (b : ActualMaskedPoissonBlock K S Γ)
    (H : Finset (HeightOneSpectrum OS) → ℝ) : ℂ :=
  ∑ δ ∈ b.mask.powerset, b.divisorCoefficient δ *
    (b.prefactor δ * primitiveTail K S D Γ μv b δ (H δ))

include ν in
theorem nonzeroDual_eq_retained_add_tail (b : ActualMaskedPoissonBlock K S Γ)
    (H : Finset (HeightOneSpectrum OS) → ℝ) :
    nonzeroDual K S D Γ μv b =
      retainedDual K S D Γ μv b H + dualTail K S D Γ μv b H := by
  unfold nonzeroDual retainedDual dualTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro δ hδ
  rw [dual_eq_retained_add_tail K S D Γ μv ν b δ (H δ)]
  ring

theorem dualTail_norm_le (b : ActualMaskedPoissonBlock K S Γ)
    (H : Finset (HeightOneSpectrum OS) → ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hb : ∀ δ ∈ b.mask.powerset,
      ‖b.prefactor δ * primitiveTail K S D Γ μv b δ (H δ)‖ ≤ U) :
    ‖dualTail K S D Γ μv b H‖ ≤ (2 : ℝ) ^ b.mask.card * U := by
  unfold dualTail
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ δ ∈ b.mask.powerset, U := by
      apply Finset.sum_le_sum
      intro δ hδ
      rw [norm_mul, divisorCoefficient_norm K S Γ b δ, one_mul]
      exact hb δ hδ
    _ = _ := by simp

include ν in
/-- The hypotheses concern the actual dual radius and cutoff, not an
assumed error estimate. The constant and seminorm precede all source
data. A small bare cutoff is allowed. -/
theorem exists_primitive_tail_bound_uniform
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (Rmax tauMin savingMax : ℝ) (hRmax : 0 ≤ Rmax)
    (htauMin : 0 < tauMin) (hsavingMax : 0 ≤ savingMax) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ (B : PrimeBlock K Sset) (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
      (φ : SchwartzMap V ℂ) (M : Finset (HeightOneSpectrum OS))
      (r : {r : ℝ // 0 < r}) (δ : Finset (HeightOneSpectrum OS))
      (Z tau saving H : ℝ),
      1 ≤ Z → tauMin ≤ tau → 0 ≤ saving → saving ≤ savingMax →
      Z ^ (-Rmax) ≤ (dualRadius K S D B t r δ).val →
      Z ^ tau ≤ (dualRadius K S D B t r δ).val * H →
      let b := block K S D Γ hΓ B t φ h hlc hcs M r
      ‖b.prefactor δ * primitiveTail K S D Γ μv b δ H‖ ≤
        A * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          (fieldConstant K / r.val) * Z ^ (-saving) := by
  have hfinite := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport
    K S ν μv h hlc hcs
  obtain ⟨m, C, hC, hb⟩ := AdaptiveFrequencyTail.exists_tail_bound
    K Sset Γ (sIntegerFiniteFourierTestFunction K S μv h)
    hfinite.1.continuous hfinite.2 Rmax tauMin savingMax hRmax htauMin hsavingMax
  obtain ⟨s, F, _hF, hFT⟩ := traceSchwartzFourier_real_seminorm_bound K m 0
  have hFT' (φ : SchwartzMap V ℂ) :
      SchwartzMap.seminorm ℂ m 0 (traceSchwartzFourier K φ) ≤
        (F : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    simpa only [SchwartzMap.seminorm_apply] using hFT φ
  refine ⟨s, C * (F : ℝ), mul_nonneg hC F.property, ?_⟩
  intro B t φ M r δ Z tau saving H hZ htau hsaving hsave hρ hcut
  dsimp only
  let b := block K S D Γ hΓ B t φ h hlc hcs M r
  let d := sIntegerMaskGenerator K Sset δ
  let rho := dualRadius K S D B t r δ
  let w : Orbit → ℂ := fun q => b.prefactor δ *
    sIntegerPeriodicFourierOrbitWeight K Sset D.different_outside Γ
      (primitiveModulus K S D B t) (primitiveModulus_ne_zero K S D B t)
      (primitiveCoefficient K S D B t) (primitiveCoefficient_invariant K S D Γ hΓ B t) d.val q
  have htail := hb (traceSchwartzFourier K φ) Z tau saving H rho hZ htau hsaving hsave
    hρ hcut w (fieldConstant K / r.val)
    (div_nonneg (fieldConstant_nonneg K) r.property.le)
    (fun q => prefactor_fourier_norm_le K S D Γ hΓ B t r d q)
  have he : b.prefactor δ * primitiveTail K S D Γ μv b δ H =
      ∑' q : {q : Orbit // H < (sIntegerOrbitNorm K Sset Γ q).val},
        w q.val * sUnitOrbitalProfile K Sset
          (sLocalTensorTestFunction K Sset (traceSchwartzFourier K φ)
            (sIntegerFiniteFourierTestFunction K S μv h))
          ⟨rho.val * (sIntegerOrbitNorm K Sset Γ q.val).val,
            mul_pos rho.property (sIntegerOrbitNorm K Sset Γ q.val).property⟩ := by
    rw [primitiveTail, ← tsum_mul_left]
    apply tsum_congr
    intro q
    dsimp only [dualTerm, sIntegerPeriodicFourierProfileTerm, w, b, block, d, rho, dualRadius]
    ring
  change ‖b.prefactor δ * primitiveTail K S D Γ μv b δ H‖ ≤ _
  rw [he]
  apply htail.2.trans
  calc
    _ ≤ (fieldConstant K / r.val) * C *
        ((F : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ) * Z ^ (-saving) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hZ) _)
      exact mul_le_mul_of_nonneg_left (hFT' φ)
        (mul_nonneg (div_nonneg (fieldConstant_nonneg K) r.property.le) hC)
    _ = _ := by ring

end HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalAdaptiveTail

end

