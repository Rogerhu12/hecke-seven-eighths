import HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalDiagonal
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualPoissonScale

/-!
# Both actual additive zero terms

The zero coefficient on each side of the genuine primitive Poisson
formula is the same principal-conductor indicator. The physical zero
subtraction is retained. The resulting bound contains the actual Haar
covolume, the actual two test values at zero, and the original mask.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalZero

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton MeasureTheory
open ActualFiniteSource ConductorMasks PrimitivePoissonSource PrimitiveFourier
  PrincipalLocus ActualPoissonScale
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

theorem primitiveCoefficient_zero_eq_indicator (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    primitiveCoefficient K S D B t 0 =
      if activeSupport B.support t = ∅ then 1 else 0 := by
  split_ifs with h
  · exact primitiveCoefficient_eq_one_of_empty K S D B t h 0
  · exact primitiveCoefficient_zero K S D B t (Finset.nonempty_iff_ne_empty.mpr h)

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [Γ.FiniteIndex]
  [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

def zeroEnvelope (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : {r : ℝ // 0 < r}) : ℝ :=
  (sUnitHaarCovolume K Sset Γ).toReal *
    (fieldConstant K / r.val *
        ‖sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) h 0‖ +
      ‖sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0‖)

theorem zeroEnvelope_nonneg (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : {r : ℝ // 0 < r}) : 0 ≤ zeroEnvelope K S Γ μv φ h r := by
  unfold zeroEnvelope
  exact mul_nonneg ENNReal.toReal_nonneg
    (add_nonneg (mul_nonneg (div_nonneg (fieldConstant_nonneg K) r.property.le)
      (norm_nonneg _)) (norm_nonneg _))

/-- Both terms vanish together off the principal locus. -/
theorem zeroContribution_eq (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M d : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) :
    (block K S D Γ hΓ B t φ h hlc hcs M r).zeroContribution μv D.different_outside d =
      if activeSupport B.support t = ∅ then
        ((sUnitHaarCovolume K Sset Γ).toReal : ℂ) *
          ((block K S D Γ hΓ B t φ h hlc hcs M r).prefactor d *
              sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) h 0 -
            sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0)
      else 0 := by
  simp only [ActualMaskedPoissonBlock.zeroContribution, block,
    divisor_fourier_zero, primitiveCoefficient_zero_eq_indicator]
  split_ifs <;> simp only [one_mul, zero_mul, sub_self, mul_zero]

theorem principal_prefactor_norm_le (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (hempty : activeSupport B.support t = ∅)
    (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS) :
    ‖sIntegerMaskPoissonFactor K S (primitiveModulus K S D B t)
      (primitiveModulus_ne_zero K S D B t) r d‖ ≤ fieldConstant K / r.val := by
  have he := primitive_prefactor_norm K S D B t r d
  rw [primitiveGauss_eq_one_of_empty K S D B t hempty, mul_one,
    (activeSupport_eq_empty_iff_primitiveIdeal_eq_one B.support t).mp hempty] at he
  simp only [map_one, Nat.cast_one, Real.sqrt_one, mul_one] at he
  rw [he]
  exact div_le_div_of_nonneg_left (fieldConstant_nonneg K) r.property
    (le_mul_of_one_le_right r.property.le (one_le_sIntegerElementNorm K Sset d))

theorem zeroContribution_norm_le (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M d : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) :
    ‖(block K S D Γ hΓ B t φ h hlc hcs M r).zeroContribution μv D.different_outside d‖ ≤
      if activeSupport B.support t = ∅ then zeroEnvelope K S Γ μv φ h r else 0 := by
  rw [zeroContribution_eq]
  split_ifs with he
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    apply (norm_sub_le _ _).trans
    rw [norm_mul]
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact principal_prefactor_norm_le K S D B t he r (sIntegerMaskGenerator K Sset d)
  · simp only [norm_zero, le_refl]

def principalContribution (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) : ℂ :=
  let b := block K S D Γ hΓ B t φ h hlc hcs M r
  ∑ d ∈ b.mask.powerset, b.divisorCoefficient d * b.zeroContribution μv D.different_outside d

/-- The original mask choices remain explicit in the principal bound. -/
theorem principalContribution_norm_le (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) :
    ‖principalContribution K S D Γ hΓ μv B t φ h hlc hcs M r‖ ≤
      if activeSupport B.support t = ∅ then
        (2 : ℝ) ^ (M ∪ principalMask K S B t).card * zeroEnvelope K S Γ μv φ h r
      else 0 := by
  let b := block K S D Γ hΓ B t φ h hlc hcs M r
  have hμ (d : Finset (HeightOneSpectrum OS)) : ‖b.divisorCoefficient d‖ = 1 := by
    rw [ActualMaskedPoissonBlock.divisorCoefficient,
      (IdealMobiusMask.squarefree_primeProduct d).moebius_eq,
      Int.cast_pow, Int.cast_neg, Int.cast_one, norm_pow]
    simp
  have hp (d : Finset (HeightOneSpectrum OS)) :
      ‖b.divisorCoefficient d * b.zeroContribution μv D.different_outside d‖ ≤
        if activeSupport B.support t = ∅ then zeroEnvelope K S Γ μv φ h r else 0 := by
    rw [norm_mul, hμ, one_mul]
    exact zeroContribution_norm_le K S D Γ hΓ μv B t φ h hlc hcs M d r
  unfold principalContribution
  change ‖∑ d ∈ b.mask.powerset, b.divisorCoefficient d *
    b.zeroContribution μv D.different_outside d‖ ≤ _
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun d _ => hp d)).trans
  split_ifs <;>
    simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat, b, block, Finset.sum_const_zero, le_refl]

end HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalZero

end
