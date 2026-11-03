import HeckeSkeleton.Moments.MOM_INV_STEP.FirstNormalizedSource
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstSecondErrorBridge

/-!
# The normalized live first source under the actual second transform

The source on the left is the arithmetic source in
`FirstNormalizedSource.normalized_freeTotal_eq`. The first physical
scalar, its two Mobius weights, its radial cost and its predetermined
row cap are therefore the original factors. The second cutoff is
constructed from those actual scales. Both resulting positive energies
and the complete error are the quantities produced by the second
Poisson theorem.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstNormalizedReduction

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools FirstParentRows
  FirstOuterCenters FirstToSecondData FirstPositiveSource FirstFreeMellinEnergy
  FirstErrorIntegration FirstCenteredErrorIntegrals CommonKernel InverseRowMajorant
  FirstCenteredPositiveEnergy
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
universe uσ

variable {σ : Type uσ} {ι : Type*} [DecidableEq σ] [Fintype ι]
variable (T : FirstParentEnergy.Data K S (σ := σ))
variable (H : OuterIndex K S D T → {r : ℝ // 0 < r}) (L : Finset (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K)))))
variable (grid : ι → {r : ℝ // 0 < r})
variable (centers : FirstOuterCenters.Centering K S D T grid)
variable (side : Bool)
variable (R : OuterIndex K S D T → {r : ℝ // 0 < r}) (massEps ε₁ : ℝ)
variable (Z r ell V tau : ℝ)
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (hbase : 1 < T.columns.base)
local notation "Idx" => FirstErrorSource.Index K S D T
local notation "U" k:max => centerScale T.scale (grid k)
local notation "weight" k:max o:max e:max =>
  FirstNormalizedSource.liveWeight K S D Γ T H L grid centers side R massEps ε₁
    Z r ell V k ⟨o,e⟩
local notation "cutoff" k:max => FirstSecondErrorBridge.cutoff K S D T R (U k) Z tau

def production (ε₂ : ℝ) (m₂ : ℕ) (k : ι) (J : Finset σ) (side₂ : Bool) (s : ℝ) : ℝ :=
  SecondProductionIntegral.actualTotal K S D Γ T Θ ψ G hν hG hbase R (U k) J s (cutoff k)
    (fun o e => weight k o e) ε₂ side m₂ side₂

variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

def error (k : ι) (J : Finset σ) (s : ℝ) : ℝ :=
  ∑ i : Idx, weight k i.1 i.2 * ‖mark K S D T side i J‖ ^ 2 *
    FirstSecondReduction.errorAt K S D Γ hΓ μv T Θ ψ G hν hG hbase R (U k) J s
      (cutoff k) i.1 i.2

theorem error_nonneg (hZ : 0 ≤ Z) (k : ι) (J : Finset σ) (s : ℝ) :
    0 ≤ error K S D Γ T H L grid centers side R massEps ε₁ Z r ell V tau
      Θ ψ G hν hG hbase hΓ μv k J s := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (mul_nonneg
    (FirstNormalizedSource.liveWeight_nonneg K S D Γ T H L grid centers side R massEps ε₁
      Z r ell V hZ k i) (sq_nonneg _))
    (FirstSecondReduction.errorAt_nonneg K S D Γ hΓ μv T Θ ψ G hν hG hbase
      R (U k) J s (cutoff k) i.1 i.2)

variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

/-- A field/background constant chosen before every source, scale,
frequency, test, original slot and prime list. -/
def reductionConstant (ε₂ : ℝ) (hε₂ : 0 < ε₂) (m₂ : ℕ) : ℝ :=
  Classical.choose (FirstSecondReduction.exists_weighted_free_bound.{uσ}
    K S D Γ hΓ hallowed μv ν μ ε₂ hε₂ m₂)

theorem reductionConstant_nonneg (ε₂ : ℝ) (hε₂ : 0 < ε₂) (m₂ : ℕ) :
    0 ≤ reductionConstant.{uσ} K S D Γ hΓ μv hallowed ν μ ε₂ hε₂ m₂ :=
  (Classical.choose_spec (FirstSecondReduction.exists_weighted_free_bound
    K S D Γ hΓ hallowed μv ν μ ε₂ hε₂ m₂)).1

/-- The actual second Poisson step applied to the unchanged first
normalized arithmetic source. No source identity or energy bound is
required as an additional premise. -/
theorem sourceAt_le (ε₂ : ℝ) (hε₂ : 0 < ε₂) (m₂ : ℕ)
    (hZ : 0 ≤ Z)
    (hcal : ThetaCalibrationInput K Sset D T.columns.lambda G)
    (hbg : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset →
      UnramifiedAt K T.columns.background p)
    (hprime : ∀ k ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists k, Prime p)
    (k : ι) (J : Finset σ) (s : ℝ) :
    FirstNormalizedSource.sourceAt K S D Γ T H L grid centers side R massEps ε₁
      Z r ell V Θ ψ G hν hG k J s ≤
    reductionConstant.{uσ} K S D Γ hΓ μv hallowed ν μ ε₂ hε₂ m₂ / 2 *
      (production K S D Γ T H L grid centers side R massEps ε₁ Z r ell V tau
        Θ ψ G hν hG hbase ε₂ m₂ k J false s +
       production K S D Γ T H L grid centers side R massEps ε₁ Z r ell V tau
        Θ ψ G hν hG hbase ε₂ m₂ k J true s) +
    error K S D Γ T H L grid centers side R massEps ε₁ Z r ell V tau
      Θ ψ G hν hG hbase hΓ μv k J s := by
  obtain ⟨-, hb⟩ := Classical.choose_spec (FirstSecondReduction.exists_weighted_free_bound.{uσ}
    K S D Γ hΓ hallowed μv ν μ ε₂ hε₂ m₂)
  have hs := hb T Θ ψ G hν hG hbase R (U k) J s (cutoff k)
    hcal hbg hprime (fun o e => weight k o e)
    (fun o e => FirstNormalizedSource.liveWeight_nonneg K S D Γ T H L grid centers side
      R massEps ε₁ Z r ell V hZ k ⟨o,e⟩) side
  simpa only [FirstNormalizedSource.sourceAt, FirstNormalizedSource.freeAt,
    Fintype.sum_sigma, production, error, reductionConstant,
    SecondProductionIntegral.firstMark, mark, FirstToSecondData.quotient] using hs

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstNormalizedReduction

end
