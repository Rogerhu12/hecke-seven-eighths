import HeckeSkeleton.Moments.MOM_INV_STEP.SecondParentRadialBudget
import HeckeSkeleton.Moments.MOM_INV_STEP.Normalization

/-!
# Exact row geometry of the genuine second source

The returned ideal is d₁ d₂ k, in first powers, and the original unit
sector is transported by the proved divisor translations. Its norm is
therefore bounded directly by the two actual mask norms and the bare
frequency cutoff. The physical exponent cancellation is stated separately
so that a finer common/divisor cutoff can be used without changing it.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondParentRows

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
  HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep HeckePort.Moments
open FixedTripleFibers CanonicalChildren CanonicalNormPools ActualDivisorSectors
  SecondSourceColumns SecondParentProduction
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset

omit [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] in
theorem newRow_norm (k : Ext) (d₁ d₂ : NonzeroRingElements OS) :
    height K Sset (newRowIdeal K S k d₁ d₂) =
      (sIntegerElementNorm K Sset d₁).val * (sIntegerElementNorm K Sset d₂).val *
        height K Sset k := by
  simp only [height, newRowIdeal_val, map_mul, Nat.cast_mul, divisorIdeal_norm]

variable {σ : Type*} [DecidableEq σ]
variable {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

theorem selectedRow_norm (T : Data K S σ Θ ψ) (i : Index K S D Γ T) :
    height K Sset (selectedRow K S D Γ T i) =
      (sIntegerElementNorm K Sset T.divisor).val *
        (sIntegerElementNorm K Sset (selectedDivisor K S D Γ T i)).val *
          height K Sset i.2.2.val.1 :=
  newRow_norm K S i.2.2.val.1 T.divisor (selectedDivisor K S D Γ T i)

theorem selectedRow_norm_le_cutoff (T : Data K S σ Θ ψ) (i : Index K S D Γ T) :
    height K Sset (selectedRow K S D Γ T i) ≤
      (sIntegerElementNorm K Sset T.divisor).val *
        (sIntegerElementNorm K Sset (selectedDivisor K S D Γ T i)).val * T.frequencyBound := by
  rw [selectedRow_norm]
  exact mul_le_mul_of_nonneg_left
    ((FirstDualTruncation.mem_sectorCutoff K S D Γ T.frequencyBound i.2.2.val).mp
      i.2.2.property)
    (mul_nonneg (sIntegerElementNorm K Sset T.divisor).property.le
      (sIntegerElementNorm K Sset (selectedDivisor K S D Γ T i)).property.le)

theorem selectedOrbit_norm_le_cutoff (T : Data K S σ Θ ψ) (i : Index K S D Γ T) :
    (sIntegerOrbitNorm K Sset Γ (CanonicalSectors.rowOrbit K Sset Γ D
      (selectedRow K S D Γ T i, selectedSector K S D Γ T i))).val ≤
      (sIntegerElementNorm K Sset T.divisor).val *
        (sIntegerElementNorm K Sset (selectedDivisor K S D Γ T i)).val * T.frequencyBound := by
  rw [CanonicalSectors.rowOrbit_norm]
  exact selectedRow_norm_le_cutoff K S D Γ T i

theorem selectedRow_rpow_bound (T : Data K S σ Θ ψ) (i : Index K S D Γ T)
    (Z d₁ d₂ H : ℝ) (hZ : 0 < Z)
    (hd₁ : (sIntegerElementNorm K Sset T.divisor).val ≤ Z ^ d₁)
    (hd₂ : (sIntegerElementNorm K Sset (selectedDivisor K S D Γ T i)).val ≤ Z ^ d₂)
    (hH : T.frequencyBound ≤ Z ^ H) :
    height K Sset (selectedRow K S D Γ T i) ≤ Z ^ (d₁ + d₂ + H) := by
  have hk := (FirstDualTruncation.mem_sectorCutoff K S D Γ T.frequencyBound i.2.2.val).mp
    i.2.2.property
  rw [selectedRow_norm]
  calc
    _ ≤ Z ^ d₁ * Z ^ d₂ * Z ^ H :=
      mul_le_mul
        (mul_le_mul hd₁ hd₂
          (sIntegerElementNorm K Sset (selectedDivisor K S D Γ T i)).property.le
          (Real.rpow_nonneg hZ.le d₁))
        (hk.trans hH) (height_pos K Sset i.2.2.val.1).le
        (mul_nonneg (Real.rpow_nonneg hZ.le d₁) (Real.rpow_nonneg hZ.le d₂))
    _ = _ := by rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]

/-- Cancellation of both first-divisor and extracted-common lengths.
The cutoff that supplies the left exponent is proved independently. -/
theorem physical_row_exponent (M r ell V delta A B j t g theta error : ℝ) :
    delta + theta + (2 * (r - A - B - t - g) + theta -
      firstPhysicalHeight M r ell V delta B j + error) =
      childM M ell A t g theta V j error := by
  unfold firstPhysicalHeight childM decrease
  ring

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondParentRows

end
