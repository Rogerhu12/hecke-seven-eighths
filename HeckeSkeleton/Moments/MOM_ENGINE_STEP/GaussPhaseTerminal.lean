import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GaussStagePhaseTransport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolStageTerminalBudget

/-!
# Original terminal controls survive the first Fourier phase

The first Fourier parameter is a scalar of norm one on each original
column. The second original profile has the corresponding Gram scalar,
also of norm one. Consequently the actual seminorm windows, zero-term
normalizations, norm cutoffs, and original factor encoding transport
without a frequency-dependent increase in their terminal constants.
The second Schwartz kernel remains the fixed earlier kernel.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory

variable {K : Type} [Field K] [NumberField K]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

theorem original_gram_seminorm_unit_multipliers
    (s : Finset (ℕ × ℕ)) (u v c d : ℂ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (φ : SchwartzMap V ℂ) :
    s.sup (schwartzSeminormFamily ℂ V ℂ) (((u * c) * star (v * d)) • φ) =
      s.sup (schwartzSeminormFamily ℂ V ℂ) ((c * star d) • φ) := by
  have he : ((u * c) * star (v * d)) • φ =
      (u * star v) • ((c * star d) • φ) := by
    rw [smul_smul, star_mul]
    congr 1
    ring
  rw [he, map_smul_eq_mul, norm_mul, norm_star, hu, hv, one_mul, one_mul]

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace ActualGaussStage.TerminalCalibration

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}

/-- The terminal calibration for every first Fourier phase is built
from the one original calibration. Its amplitudes are unchanged. -/
def withUnitMultiplier
    (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    (s.withMultiplier u).TerminalCalibration sTail sZero k Z Lmax Nsave decay where
  productExponent := T.productExponent
  profileExponent := T.profileExponent
  maskExponent := T.maskExponent
  inverseRadiusExponent := T.inverseRadiusExponent
  tailAmplitude := T.tailAmplitude
  zeroAmplitude := T.zeroAmplitude
  zeroAmplitude_nonneg := T.zeroAmplitude_nonneg
  windows :=
    { T.windows with
      profile_seminorm := by
        intro v hv
        change sTail.sup (schwartzSeminormFamily ℂ V ℂ)
          (((u v.2.1 * G.coefficient v.2.1) * star (u v.2.2 * G.coefficient v.2.2)) •
            s.profile) ≤ _
        rw [original_gram_seminorm_unit_multipliers sTail _ _ _ _
          (hu v.2.1) (hu v.2.2)]
        exact T.windows.profile_seminorm v hv }
  exponent_bound := T.exponent_bound
  cutoff_eq := T.cutoff_eq
  profile_zero := T.profile_zero
  zero_normalization := by
    intro v hv
    change sZero.sup (schwartzSeminormFamily ℂ V ℂ)
      (((u v.2.1 * G.coefficient v.2.1) * star (u v.2.2 * G.coefficient v.2.2)) •
        s.profile) * A.exteriorNorm (G.ideal v.2.1) *
      (∑ D ∈ s.mask.powerset, firstZeroDivisorWeight s.radius D) ≤ _
    rw [original_gram_seminorm_unit_multipliers sZero _ _ _ _
      (hu v.2.1) (hu v.2.2)]
    exact T.zero_normalization v hv

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

def fourierPhase
    (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (x : ι → W) (ξ : W) :
    (s.withMultiplier (fun i => jointPhase ξ (x i))).TerminalCalibration
      sTail sZero k Z Lmax Nsave decay :=
  T.withUnitMultiplier (fun i => jointPhase ξ (x i)) (fun i => norm_jointPhase ξ (x i))

end ActualGaussStage.TerminalCalibration
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.original_gram_seminorm_unit_multipliers
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.TerminalCalibration.fourierPhase
