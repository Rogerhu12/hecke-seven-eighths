import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredMellinEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCommonEnvelope

/-!
# The free first Mellin energy under the common Fourier measure

This is the literal inverse family on its complete squarefree pool,
with the fixed positive row majorant, the original unit subgroup and an
empty additional mask. Its true orbital energy has a bound independent
of the combined spectral frequency. Dominated integration then proves
continuity and all outer Fourier integrability used by the first parent.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstFreeMellinEnergy

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalBlock CanonicalNormPools FirstCenteredFamily
  FirstCenteredMellinEnergy MellinSeparation CommonKernel InverseRowMajorant
  FirstCommonEnvelope
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K

variable {σ : Type*}
variable (C : ColumnData K S σ)
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
variable (J : Finset σ) (U a : ℝ) (γ : OuterTriple K) (j : Ideal (𝓞 K))
  (d : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)

/-- The actual free positive orbital energy at one combined frequency. -/
def freeEnergyAt (H : {r : ℝ // 0 < r}) (s : ℝ) : ℝ :=
  (DivisorInverseColumn.weightedEnergy K S Γ D
    (family K S C Θ ψ G hν hG J U a s) γ j d
    (Physical.ActualGramMajorantDraft.rowBallArchTest K S 1)
    (Physical.ActualGramMajorantDraft.rowBallFiniteFamily K S 1) ∅ (rowRadius H)).re

theorem freeEnergyAt_eq (H : {r : ℝ // 0 < r}) (s : ℝ) :
    freeEnergyAt K S Γ D C Θ ψ G hν hG J U a γ j d H s =
      energy K S Γ D (squarefreePool K Sset (2 * U))
        (DivisorInverseColumn.coefficient K S D
          (family K S C Θ ψ G hν hG J U a s) γ j d) H :=
  free_weightedEnergy_re K S Γ D (family K S C Θ ψ G hν hG J U a s) γ j d H

theorem freeEnergyAt_nonneg (H : {r : ℝ // 0 < r}) (s : ℝ) :
    0 ≤ freeEnergyAt K S Γ D C Θ ψ G hν hG J U a γ j d H s := by
  rw [freeEnergyAt_eq]
  exact energy_nonneg K S Γ D _ _ H

theorem freeEnergyAt_continuous (H : {r : ℝ // 0 < r}) :
    Continuous (freeEnergyAt K S Γ D C Θ ψ G hν hG J U a γ j d H) := by
  change Continuous (fun s : ℝ => freeEnergyAt K S Γ D C Θ ψ G hν hG J U a γ j d H s)
  simp only [freeEnergyAt_eq]
  apply InverseSpectralEnergy.energy_continuous K S Γ D
    (squarefreePool K Sset (2 * U))
    (fun s => DivisorInverseColumn.coefficient K S D
      (family K S C Θ ψ G hν hG J U a s) γ j d)
    (fun n _ => ?_) (coefficientMass K S D C Θ ψ G hν hG J U a γ j d) (fun s => ?_) H
  · simpa only [add_zero] using
      coefficient_continuous K S D C Θ ψ G hν hG J U a γ j d n 0
  · simpa only [add_zero] using
      coefficient_mass_bound K S D C Θ ψ G hν hG J U a γ j d 0 s

/-- This envelope consists only of the actual finite coefficient mass
and the summable fixed orbital profile. It is independent of frequency. -/
def freeEnergyBound (H : {r : ℝ // 0 < r}) : ℝ :=
  (coefficientMass K S D C Θ ψ G hν hG J U a γ j d) ^ 2 *
    ∑' q, fixedProfile K S Γ H q

theorem freeEnergyBound_nonneg (H : {r : ℝ // 0 < r}) :
    0 ≤ freeEnergyBound K S Γ D C Θ ψ G hν hG J U a γ j d H :=
  mul_nonneg (sq_nonneg _)
    (tsum_nonneg (fun q => fixedProfile_nonneg K S Γ H q))

theorem freeEnergyAt_bound (H : {r : ℝ // 0 < r}) (s : ℝ) :
    freeEnergyAt K S Γ D C Θ ψ G hν hG J U a γ j d H s ≤
      freeEnergyBound K S Γ D C Θ ψ G hν hG J U a γ j d H := by
  rw [freeEnergyAt_eq]
  exact InverseSpectralEnergy.energy_bound K S Γ D
    (squarefreePool K Sset (2 * U))
    (fun t => DivisorInverseColumn.coefficient K S D
      (family K S C Θ ψ G hν hG J U a t) γ j d)
    (coefficientMass K S D C Θ ψ G hν hG J U a γ j d)
    (fun t => by simpa only [add_zero] using
      coefficient_mass_bound K S D C Θ ψ G hν hG J U a γ j d 0 t) H s

def freeMellinEnergy (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (H : {r : ℝ // 0 < r}) (τ : ℝ) : ℝ :=
  ∫ t : ℝ, ‖density W hW t‖ *
    freeEnergyAt K S Γ D C Θ ψ G hν hG J U a γ j d H (t + τ)

theorem freeMellin_integrand_integrable (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (H : {r : ℝ // 0 < r}) (τ : ℝ) :
    Integrable (fun t : ℝ => ‖density W hW t‖ *
      freeEnergyAt K S Γ D C Θ ψ G hν hG J U a γ j d H (t + τ)) :=
  free_energy_integrable K S Γ D C Θ ψ G hν hG J U a γ j d W hW τ H

theorem freeMellinEnergy_nonneg (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (H : {r : ℝ // 0 < r}) (τ : ℝ) :
    0 ≤ freeMellinEnergy K S Γ D C Θ ψ G hν hG J U a γ j d W hW H τ :=
  integral_nonneg (fun t => mul_nonneg (norm_nonneg _)
    (freeEnergyAt_nonneg K S Γ D C Θ ψ G hν hG J U a γ j d H (t + τ)))

theorem freeMellinEnergy_bound (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (H : {r : ℝ // 0 < r}) (τ : ℝ) :
    freeMellinEnergy K S Γ D C Θ ψ G hν hG J U a γ j d W hW H τ ≤
      freeEnergyBound K S Γ D C Θ ψ G hν hG J U a γ j d H *
        ∫ t : ℝ, ‖density W hW t‖ := by
  have hi := integral_mono
    (freeMellin_integrand_integrable K S Γ D C Θ ψ G hν hG J U a γ j d W hW H τ)
    ((density W hW).integrable.norm.mul_const
      (freeEnergyBound K S Γ D C Θ ψ G hν hG J U a γ j d H))
    (fun t => mul_le_mul_of_nonneg_left
      (freeEnergyAt_bound K S Γ D C Θ ψ G hν hG J U a γ j d H (t + τ))
      (norm_nonneg _))
  rw [integral_mul_const] at hi
  exact hi.trans_eq (mul_comm _ _)

theorem freeMellinEnergy_continuous (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (H : {r : ℝ // 0 < r}) :
    Continuous (freeMellinEnergy K S Γ D C Θ ψ G hν hG J U a γ j d W hW H) := by
  apply continuous_of_dominated
    (fun τ => (freeMellin_integrand_integrable K S Γ D C Θ ψ G hν hG J U a γ j d
      W hW H τ).aestronglyMeasurable)
    (bound := fun t => ‖density W hW t‖ *
      freeEnergyBound K S Γ D C Θ ψ G hν hG J U a γ j d H)
  · intro τ
    filter_upwards [] with t
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _)
      (freeEnergyAt_nonneg K S Γ D C Θ ψ G hν hG J U a γ j d H (t + τ)))]
    exact mul_le_mul_of_nonneg_left
      (freeEnergyAt_bound K S Γ D C Θ ψ G hν hG J U a γ j d H (t + τ))
      (norm_nonneg _)
  · exact (density W hW).integrable.norm.mul_const _
  · filter_upwards [] with t
    exact continuous_const.mul
      ((freeEnergyAt_continuous K S Γ D C Θ ψ G hν hG J U a γ j d H).comp
        (continuous_const.add continuous_id))

/-- The outer frequency weight can be any genuine integrable weight;
no integrability of the arithmetic energy is assumed. -/
theorem weighted_freeMellinEnergy_integrable (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (H : {r : ℝ // 0 < r})
    (w : LogPlane → ℝ) (hw : Integrable w)
    (coordinate : LogPlane → ℝ) (hc : Continuous coordinate) :
    Integrable (fun ξ : LogPlane => w ξ *
      freeMellinEnergy K S Γ D C Θ ψ G hν hG J U a γ j d W hW H (coordinate ξ)) := by
  apply hw.mul_bdd
    (c := freeEnergyBound K S Γ D C Θ ψ G hν hG J U a γ j d H *
      ∫ t : ℝ, ‖density W hW t‖)
    ((freeMellinEnergy_continuous K S Γ D C Θ ψ G hν hG J U a γ j d W hW H).comp
      hc).aestronglyMeasurable
  filter_upwards [] with ξ
  change ‖freeMellinEnergy K S Γ D C Θ ψ G hν hG J U a γ j d W hW H (coordinate ξ)‖ ≤
    freeEnergyBound K S Γ D C Θ ψ G hν hG J U a γ j d H * ∫ t : ℝ, ‖density W hW t‖
  rw [Real.norm_of_nonneg
    (freeMellinEnergy_nonneg K S Γ D C Θ ψ G hν hG J U a γ j d W hW H (coordinate ξ))]
  exact freeMellinEnergy_bound K S Γ D C Θ ψ G hν hG J U a γ j d W hW H (coordinate ξ)

theorem fourier_freeMellinEnergy_integrable (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (H : {r : ℝ // 0 < r})
    (m : ℕ) (coordinate : LogPlane → ℝ) (hc : Continuous coordinate) :
    Integrable (fun ξ : LogPlane => frequencyEnvelope m ξ *
      freeMellinEnergy K S Γ D C Θ ψ G hν hG J U a γ j d W hW H (coordinate ξ)) :=
  weighted_freeMellinEnergy_integrable K S Γ D C Θ ψ G hν hG J U a γ j d W hW H
    (frequencyEnvelope m) (frequencyEnvelope_integrable m) coordinate hc

theorem fourier_freeMellinEnergy_bound (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (H : {r : ℝ // 0 < r})
    (m : ℕ) (coordinate : LogPlane → ℝ) (hc : Continuous coordinate) :
    (∫ ξ : LogPlane, frequencyEnvelope m ξ *
      freeMellinEnergy K S Γ D C Θ ψ G hν hG J U a γ j d W hW H (coordinate ξ)) ≤
      (freeEnergyBound K S Γ D C Θ ψ G hν hG J U a γ j d H *
        ∫ t : ℝ, ‖density W hW t‖) * ∫ ξ : LogPlane, frequencyEnvelope m ξ := by
  have hi := integral_mono
    (fourier_freeMellinEnergy_integrable K S Γ D C Θ ψ G hν hG J U a γ j d
      W hW H m coordinate hc)
    ((frequencyEnvelope_integrable m).mul_const
      (freeEnergyBound K S Γ D C Θ ψ G hν hG J U a γ j d H *
        ∫ t : ℝ, ‖density W hW t‖))
    (fun ξ => mul_le_mul_of_nonneg_left
      (freeMellinEnergy_bound K S Γ D C Θ ψ G hν hG J U a γ j d W hW H (coordinate ξ))
      (frequencyEnvelope_nonneg m ξ))
  rw [integral_mul_const] at hi
  exact hi.trans_eq (mul_comm _ _)

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstFreeMellinEnergy

end
