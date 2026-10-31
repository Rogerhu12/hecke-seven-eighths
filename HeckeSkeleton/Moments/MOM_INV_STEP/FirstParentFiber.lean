import HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentRows
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstFreeMellinEnergy

/-!
# The whole original label-frequency fiber under both spectral measures

The source contains all original labels and all retained frequency ideals
with their original Γ sectors. The common old-label weight is pushed
through the actual f² E h map before any row enlargement. The output is
the genuine free inverse-family orbital energy with empty external mask.
The divisor constant is chosen before every source family and test.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentFiber

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory DedekindZetaZeroFree.LargeSieve
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools FirstCenteredFamily
  FirstCenteredMellinEnergy FirstFreeMellinEnergy FirstRowGeometry FirstParentRows
  InverseRowMajorant CommonKernel FirstCommonEnvelope
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)

include hallowed hΓ in
private theorem source_free_energy_of_divisor_bound
    (a : ℕ) (ε B : ℝ) (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (hdiv : ∀ I : Ideal (𝓞 K), ((idealDivisors I).card : ℝ) ^ (a + 1) ≤
      B * (I.absNorm : ℝ) ^ ε)
    {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}
    (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K) (j : Ideal (𝓞 K))
    (d : OS) (E : Ext) (T : Finset (FirstCanonicalLabel.SourcePair K S Γ))
    (w : Ideal (𝓞 K) → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hw : ∀ x ∈ T, w x.1.val.val ≤ A * ((idealDivisors x.1.val.val).card : ℝ) ^ a)
    (H : {r : ℝ // 0 < r})
    (hH : ∀ y ∈ T.image (row K S Γ E), (y.1.val.val.absNorm : ℝ) ≤ H.val) :
    (∑ x ∈ T, w x.1.val.val *
      ‖DivisorInverseColumn.oldAmplitude K S Γ D C γ j d E x‖ ^ 2) ≤
      (A * B * H.val ^ ε) * ((rowCovolume K S)⁻¹ *
        (DivisorInverseColumn.weightedEnergy K S Γ D C γ j d
          (Physical.ActualGramMajorantDraft.rowBallArchTest K S 1)
          (Physical.ActualGramMajorantDraft.rowBallFiniteFamily K S 1) ∅ (rowRadius H)).re) := by
  have hcost : 0 ≤ A * B * H.val ^ ε := by positivity
  calc
    _ ≤ ∑ y ∈ T.image (row K S Γ E),
        (A * ((idealDivisors y.1.val.val).card : ℝ) ^ (a + 1)) *
          ‖DivisorInverseColumn.column K S Γ D C γ j d (y.1.val.val,y.2)‖ ^ 2 :=
      FirstSpectralFiber.source_energy_typed K S Γ D hallowed C γ j d E T w a A hA hw
    _ ≤ ∑ y ∈ T.image (row K S Γ E),
        (A * B * H.val ^ ε) *
          ‖DivisorInverseColumn.column K S Γ D C γ j d (y.1.val.val,y.2)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro y hy
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact (mul_le_mul_of_nonneg_left
        ((hdiv y.1.val.val).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (hH y hy) hε) hB)) hA).trans_eq
        (by ring)
    _ = (A * B * H.val ^ ε) *
        ∑ y ∈ T.image (row K S Γ E),
          ‖DivisorInverseColumn.column K S Γ D C γ j d (y.1.val.val,y.2)‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (canonical_sector_rows_le_free_energy K S Γ D hΓ C γ j d H
        (T.image (row K S Γ E)) hH) hcost

variable {σ : Type*} (C : CanonicalBlock.ColumnData K S σ)
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
variable (J : Finset σ) (U α : ℝ) (γ : OuterTriple K) (j : Ideal (𝓞 K))
  (d : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)
variable (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)

def sourceMellinEnergy (E : Ext) (T : Finset (FirstCanonicalLabel.SourcePair K S Γ))
    (w : Ext → ℝ) (τ : ℝ) : ℝ :=
  ∑ x ∈ T, w x.1 * mellinEnergy K S Γ D C Θ ψ G hν hG J U α γ j d
    W hW (row K S Γ E x) τ

include hallowed hΓ in
theorem sourceMellinEnergy_eq (E : Ext) (T : Finset (FirstCanonicalLabel.SourcePair K S Γ))
    (w : Ext → ℝ) (τ : ℝ) :
    sourceMellinEnergy K S Γ D C Θ ψ G hν hG J U α γ j d W hW E T w τ =
      ∫ t : ℝ, ‖MellinSeparation.density W hW t‖ *
        ∑ x ∈ T, idealWeight K S w x.1.val.val *
          ‖DivisorInverseColumn.oldAmplitude K S Γ D
            (family K S C Θ ψ G hν hG J U α (t + τ)) γ j d E x‖ ^ 2 := by
  simp only [DivisorInverseColumn.oldAmplitude_eq K S Γ D hallowed,
    FirstRowGeometry.newRow_eq, idealWeight_apply]
  unfold sourceMellinEnergy mellinEnergy
  simp_rw [← integral_const_mul]
  rw [← integral_finset_sum T (fun x hx =>
    (column_energy_integrable K S Γ D C Θ ψ G hν hG J U α γ j d hΓ
      W hW (row K S Γ E x) τ).const_mul (w x.1))]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

include hΓ in
theorem sourceMellinEnergy_weighted_integrable
    (E : Ext) (T : Finset (FirstCanonicalLabel.SourcePair K S Γ)) (w : Ext → ℝ)
    (v : LogPlane → ℝ) (hv : Integrable v)
    (coordinate : LogPlane → ℝ) (hc : Continuous coordinate) :
    Integrable (fun ξ : LogPlane => v ξ *
      sourceMellinEnergy K S Γ D C Θ ψ G hν hG J U α γ j d W hW E T w (coordinate ξ)) := by
  simp only [sourceMellinEnergy, Finset.mul_sum]
  apply integrable_finset_sum
  intro x hx
  have hi := (fourier_mellinEnergy_integrable K S Γ D C Θ ψ G hν hG J U α γ j d hΓ
    W hW (row K S Γ E x) v hv coordinate hc).const_mul (w x.1)
  simpa only [mul_assoc, mul_left_comm] using hi

include hallowed hΓ in
theorem sourceMellinEnergy_le_of_divisor_bound
    (a : ℕ) (ε B : ℝ) (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (hdiv : ∀ I : Ideal (𝓞 K), ((idealDivisors I).card : ℝ) ^ (a + 1) ≤
      B * (I.absNorm : ℝ) ^ ε)
    (E : Ext) (T : Finset (FirstCanonicalLabel.SourcePair K S Γ))
    (w : Ext → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hw : ∀ x ∈ T, w x.1 ≤ A * ((idealDivisors x.1.val.val).card : ℝ) ^ a)
    (H : {r : ℝ // 0 < r})
    (hH : ∀ y ∈ T.image (row K S Γ E), (y.1.val.val.absNorm : ℝ) ≤ H.val)
    (τ : ℝ) :
    sourceMellinEnergy K S Γ D C Θ ψ G hν hG J U α γ j d W hW E T w τ ≤
      ((A * B * H.val ^ ε) * (rowCovolume K S)⁻¹) *
        freeMellinEnergy K S Γ D C Θ ψ G hν hG J U α γ j d W hW H τ := by
  rw [sourceMellinEnergy_eq K S Γ D hallowed hΓ]
  have hl : Integrable (fun t : ℝ => ‖MellinSeparation.density W hW t‖ *
      ∑ x ∈ T, idealWeight K S w x.1.val.val *
        ‖DivisorInverseColumn.oldAmplitude K S Γ D
          (family K S C Θ ψ G hν hG J U α (t + τ)) γ j d E x‖ ^ 2) := by
    simp only [Finset.mul_sum, idealWeight_apply]
    apply integrable_finset_sum
    intro x hx
    have hi := (FirstCenteredSpectralFiber.oldAmplitude_energy_integrable
      K S Γ D hallowed hΓ C Θ ψ G hν hG J U α γ j d W hW τ E x).const_mul (w x.1)
    simpa only [mul_assoc, mul_left_comm] using hi
  have hr := (freeMellin_integrand_integrable K S Γ D C Θ ψ G hν hG J U α γ j d
    W hW H τ).const_mul ((A * B * H.val ^ ε) * (rowCovolume K S)⁻¹)
  have hi := integral_mono hl hr (fun t => by
    have hb := source_free_energy_of_divisor_bound K S Γ D hallowed hΓ a ε B hε hB hdiv
      (family K S C Θ ψ G hν hG J U α (t + τ)) γ j d E T
      (idealWeight K S w) A hA (by simpa only [idealWeight_apply] using hw) H hH
    exact (mul_le_mul_of_nonneg_left hb (norm_nonneg (MellinSeparation.density W hW t))).trans_eq
      (by dsimp only [freeEnergyAt]; ring))
  rwa [integral_const_mul] at hi

include hallowed hΓ in
theorem sourceFourierEnergy_le_of_divisor_bound
    (a : ℕ) (ε B : ℝ) (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (hdiv : ∀ I : Ideal (𝓞 K), ((idealDivisors I).card : ℝ) ^ (a + 1) ≤
      B * (I.absNorm : ℝ) ^ ε)
    (E : Ext) (T : Finset (FirstCanonicalLabel.SourcePair K S Γ))
    (w : Ext → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hw : ∀ x ∈ T, w x.1 ≤ A * ((idealDivisors x.1.val.val).card : ℝ) ^ a)
    (H : {r : ℝ // 0 < r})
    (hH : ∀ y ∈ T.image (row K S Γ E), (y.1.val.val.absNorm : ℝ) ≤ H.val)
    (m : ℕ) (coordinate : LogPlane → ℝ) (hc : Continuous coordinate) :
    (∫ ξ : LogPlane, frequencyEnvelope m ξ *
      sourceMellinEnergy K S Γ D C Θ ψ G hν hG J U α γ j d W hW E T w (coordinate ξ)) ≤
      ((A * B * H.val ^ ε) * (rowCovolume K S)⁻¹) *
        ∫ ξ : LogPlane, frequencyEnvelope m ξ *
          freeMellinEnergy K S Γ D C Θ ψ G hν hG J U α γ j d W hW H (coordinate ξ) := by
  have hl := sourceMellinEnergy_weighted_integrable K S Γ D hΓ C Θ ψ G hν hG
    J U α γ j d W hW E T w (frequencyEnvelope m) (frequencyEnvelope_integrable m) coordinate hc
  have hr := (fourier_freeMellinEnergy_integrable K S Γ D C Θ ψ G hν hG
    J U α γ j d W hW H m coordinate hc).const_mul
      ((A * B * H.val ^ ε) * (rowCovolume K S)⁻¹)
  have hi := integral_mono hl hr (fun ξ => by
    have hb := sourceMellinEnergy_le_of_divisor_bound K S Γ D hallowed hΓ C Θ ψ G hν hG
      J U α γ j d W hW a ε B hε hB hdiv E T w A hA hw H hH (coordinate ξ)
    exact (mul_le_mul_of_nonneg_left hb (frequencyEnvelope_nonneg m ξ)).trans_eq (by ring))
  rwa [integral_const_mul] at hi

include hallowed hΓ in
/-- The fiber constant precedes all original coefficients, old-label
weights, source rows, center lengths and both spectral variables. -/
theorem exists_uniform_sourceFourierEnergy_bound (a : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {σ₀ : Type*} (C₀ : CanonicalBlock.ColumnData K S σ₀)
        (Θ₀ : Subgroup (HeckeCharacter K)) (ψ₀ G₀ : HeckeCharacter K)
        (hν₀ : BackgroundCycle.Admissible K Θ₀ ψ₀ C₀.background) (hG₀ : G₀ ∈ Θ₀)
        (J₀ : Finset σ₀) (U₀ α₀ : ℝ) (γ₀ : OuterTriple K) (j₀ : Ideal (𝓞 K)) (d₀ : OS)
        (W₀ : SchwartzMap ℝ ℂ) (hW₀ : tsupport W₀ ⊆ Set.Icc (1 : ℝ) 2)
        (E₀ : Ext) (T₀ : Finset (FirstCanonicalLabel.SourcePair K S Γ))
        (w₀ : Ext → ℝ) (A : ℝ), 0 ≤ A →
        (∀ x ∈ T₀, w₀ x.1 ≤ A * ((idealDivisors x.1.val.val).card : ℝ) ^ a) →
        ∀ (H : {r : ℝ // 0 < r}),
        (∀ y ∈ T₀.image (row K S Γ E₀), (y.1.val.val.absNorm : ℝ) ≤ H.val) →
        ∀ (m : ℕ) (coordinate : LogPlane → ℝ), Continuous coordinate →
        (∫ ξ : LogPlane, frequencyEnvelope m ξ *
          sourceMellinEnergy K S Γ D C₀ Θ₀ ψ₀ G₀ hν₀ hG₀ J₀ U₀ α₀ γ₀ j₀ d₀
            W₀ hW₀ E₀ T₀ w₀ (coordinate ξ)) ≤
          ((A * B * H.val ^ ε) * (rowCovolume K S)⁻¹) *
            ∫ ξ : LogPlane, frequencyEnvelope m ξ *
              freeMellinEnergy K S Γ D C₀ Θ₀ ψ₀ G₀ hν₀ hG₀ J₀ U₀ α₀ γ₀ j₀ d₀
                W₀ hW₀ H (coordinate ξ) := by
  obtain ⟨B, hB, hdiv⟩ := exists_divisor_power_bound (K := K) (a + 1) (by omega) ε hε
  refine ⟨B, hB, ?_⟩
  intro σ₀ C₀ Θ₀ ψ₀ G₀ hν₀ hG₀ J₀ U₀ α₀ γ₀ j₀ d₀ W₀ hW₀ E₀ T₀ w₀ A hA hw H hH m coordinate hc
  exact sourceFourierEnergy_le_of_divisor_bound K S Γ D hallowed hΓ
    C₀ Θ₀ ψ₀ G₀ hν₀ hG₀ J₀ U₀ α₀ γ₀ j₀ d₀ W₀ hW₀ a ε B hε.le
    (zero_le_one.trans hB) hdiv E₀ T₀ w₀ A hA hw H hH m coordinate hc

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentFiber

end
