import HeckeSkeleton.Moments.MOM_INV_STEP.FirstMellinEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstRowGeometry

/-!
# Actual first old-label fibres inside the spectral integral

The common original weight is pushed along (f,h,ξ) ↦ (f² E h,ξ).
The proved ideal-divisor fibre bound and genuine orbital majorant leave
an actual inverse-family energy with no old row or old label. Its first
Poisson divisor stays in the literal column throughout.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstSpectralFiber

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory DedekindZetaZeroFree.LargeSieve
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren FirstCompleteFamily FirstMellinEnergy
  FirstRowGeometry InverseRowMajorant
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

variable {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

include hallowed in
theorem source_energy_typed (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (j : Ideal (𝓞 K)) (d : OS) (E : Ext)
    (T : Finset (FirstCanonicalLabel.SourcePair K S Γ))
    (w : Ideal (𝓞 K) → ℝ) (a : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hw : ∀ x ∈ T, w x.1.val.val ≤ A * ((idealDivisors x.1.val.val).card : ℝ) ^ a) :
    (∑ x ∈ T, w x.1.val.val *
      ‖DivisorInverseColumn.oldAmplitude K S Γ D C γ j d E x‖ ^ 2) ≤
      ∑ y ∈ T.image (row K S Γ E),
        (A * ((idealDivisors y.1.val.val).card : ℝ) ^ (a + 1)) *
          ‖DivisorInverseColumn.column K S Γ D C γ j d (y.1.val.val,y.2)‖ ^ 2 := by
  have hb := DivisorInverseColumn.first_source_energy K S Γ D hallowed
    C γ j d E T w a A hA hw
  rw [image_newRow K S Γ E T, Finset.sum_image
    (fun _ _ _ _ h => forget_injective K S Γ h)] at hb
  exact hb

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]

include hallowed hΓ in
/-- The small-power constant precedes every source family, old label,
row set, sector, and physical row scale. -/
theorem exists_source_free_energy_bound (a : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
        (j : Ideal (𝓞 K)) (d : OS) (E : Ext)
        (T : Finset (FirstCanonicalLabel.SourcePair K S Γ))
        (w : Ideal (𝓞 K) → ℝ) (A : ℝ), 0 ≤ A →
        (∀ x ∈ T, w x.1.val.val ≤ A * ((idealDivisors x.1.val.val).card : ℝ) ^ a) →
        ∀ H : {r : ℝ // 0 < r},
        (∀ y ∈ T.image (row K S Γ E), (y.1.val.val.absNorm : ℝ) ≤ H.val) →
        (∑ x ∈ T, w x.1.val.val *
          ‖DivisorInverseColumn.oldAmplitude K S Γ D C γ j d E x‖ ^ 2) ≤
        (A * B * H.val ^ ε) *
          ((rowCovolume K S)⁻¹ *
            (DivisorInverseColumn.weightedEnergy K S Γ D C γ j d
              (Physical.ActualGramMajorantDraft.rowBallArchTest K S 1)
              (Physical.ActualGramMajorantDraft.rowBallFiniteFamily K S 1) ∅ (rowRadius H)).re) := by
  obtain ⟨B,hB,hdiv⟩ := exists_divisor_power_bound (K := K) (a + 1) (by omega) ε hε
  refine ⟨B,hB,fun C γ j d E T w A hA hw H hH => ?_⟩
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hcost : 0 ≤ A * B * H.val ^ ε :=
    mul_nonneg (mul_nonneg hA hB0) (Real.rpow_nonneg H.property.le ε)
  calc
    _ ≤ ∑ y ∈ T.image (row K S Γ E),
        (A * ((idealDivisors y.1.val.val).card : ℝ) ^ (a + 1)) *
          ‖DivisorInverseColumn.column K S Γ D C γ j d (y.1.val.val,y.2)‖ ^ 2 :=
      source_energy_typed K S Γ D hallowed C γ j d E T w a A hA hw
    _ ≤ ∑ y ∈ T.image (row K S Γ E), (A * B * H.val ^ ε) *
          ‖DivisorInverseColumn.column K S Γ D C γ j d (y.1.val.val,y.2)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro y hy
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      calc
        _ ≤ A * (B * (y.1.val.val.absNorm : ℝ) ^ ε) :=
          mul_le_mul_of_nonneg_left (hdiv _) hA
        _ ≤ A * (B * H.val ^ ε) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Nat.cast_nonneg _) (hH y hy) hε.le) hB0) hA
        _ = _ := by ring
    _ = (A * B * H.val ^ ε) *
        (∑ y ∈ T.image (row K S Γ E),
          ‖DivisorInverseColumn.column K S Γ D C γ j d (y.1.val.val,y.2)‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (canonical_sector_rows_le_free_energy K S Γ D hΓ C γ j d H
        (T.image (row K S Γ E)) hH) hcost

variable (C : CanonicalBlock.ColumnData K S σ)
variable (Θ₀ : Subgroup (HeckeCharacter K)) (ψ₀ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ₀ ψ₀ C.background) (hG : G ∈ Θ₀)
variable (J : Finset σ) (U α : ℝ) (γ : OuterTriple K) (j : Ideal (𝓞 K))
variable (d : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)
include d

include hallowed hΓ in
theorem oldAmplitude_energy_integrable (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (τ : ℝ) (E : Ext)
    (x : FirstCanonicalLabel.SourcePair K S Γ) :
    Integrable (fun t => ‖MellinSeparation.density W hW t‖ *
      ‖DivisorInverseColumn.oldAmplitude K S Γ D
        (family K S C Θ₀ ψ₀ G hν hG J U α (t + τ)) γ j d E x‖ ^ 2) := by
  simp only [DivisorInverseColumn.oldAmplitude_eq K S Γ D hallowed,
    FirstRowGeometry.newRow_eq]
  exact column_energy_integrable K S Γ D C Θ₀ ψ₀ G hν hG J U α γ j d hΓ
    W hW (row K S Γ E x) τ

include hallowed hΓ in
/-- The same literal original weight and fibre bound remain valid under
the genuine Mellin measure. Both sides have proved integrability. -/
theorem exists_integral_source_free_energy_bound (a : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
        (τ : ℝ) (E : Ext) (T : Finset (FirstCanonicalLabel.SourcePair K S Γ))
        (w : Ideal (𝓞 K) → ℝ) (A : ℝ), 0 ≤ A →
        (∀ x ∈ T, w x.1.val.val ≤ A * ((idealDivisors x.1.val.val).card : ℝ) ^ a) →
        ∀ H : {r : ℝ // 0 < r},
        (∀ y ∈ T.image (row K S Γ E), (y.1.val.val.absNorm : ℝ) ≤ H.val) →
        (∫ t : ℝ, ‖MellinSeparation.density W hW t‖ *
          ∑ x ∈ T, w x.1.val.val *
            ‖DivisorInverseColumn.oldAmplitude K S Γ D
              (family K S C Θ₀ ψ₀ G hν hG J U α (t + τ)) γ j d E x‖ ^ 2) ≤
        (A * B * H.val ^ ε) * ((rowCovolume K S)⁻¹ *
          ∫ t : ℝ, ‖MellinSeparation.density W hW t‖ *
            (DivisorInverseColumn.weightedEnergy K S Γ D
              (family K S C Θ₀ ψ₀ G hν hG J U α (t + τ)) γ j d
              (Physical.ActualGramMajorantDraft.rowBallArchTest K S 1)
              (Physical.ActualGramMajorantDraft.rowBallFiniteFamily K S 1) ∅ (rowRadius H)).re) := by
  obtain ⟨B,hB,hbound⟩ := exists_source_free_energy_bound
    K S Γ D hallowed hΓ (σ := σ) (Θ := Θ₀) (ψ := ψ₀) a ε hε
  refine ⟨B,hB,fun W hW τ E T w A hA hw H hH => ?_⟩
  have hleft : Integrable (fun t : ℝ => ‖MellinSeparation.density W hW t‖ *
      ∑ x ∈ T, w x.1.val.val *
        ‖DivisorInverseColumn.oldAmplitude K S Γ D
          (family K S C Θ₀ ψ₀ G hν hG J U α (t + τ)) γ j d E x‖ ^ 2) := by
    simp only [Finset.mul_sum, ← mul_assoc]
    apply integrable_finset_sum
    intro x hx
    have hi := (oldAmplitude_energy_integrable K S Γ D hallowed hΓ
      C Θ₀ ψ₀ G hν hG J U α γ j d W hW τ E x).const_mul (w x.1.val.val)
    simpa only [mul_left_comm, mul_assoc] using hi
  have hright := (free_energy_integrable K S Γ D C Θ₀ ψ₀ G hν hG J U α γ j d
    W hW τ H).const_mul ((A * B * H.val ^ ε) * (rowCovolume K S)⁻¹)
  have he := integral_mono hleft hright (fun t => by
    have hb := mul_le_mul_of_nonneg_left
      (hbound (family K S C Θ₀ ψ₀ G hν hG J U α (t + τ)) γ j d E T w A hA hw H hH)
      (norm_nonneg (MellinSeparation.density W hW t))
    convert hb using 1 <;> ring)
  rw [integral_const_mul] at he
  convert he using 1 <;> ring

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstSpectralFiber

end

