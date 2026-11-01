import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderNodes
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderFamily
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderShort

/-!
# Exact short and long completed contributions of an actual node

Both pieces use the original raw puncture and the entire original
product mark. They are extended by zero off exterior rows and labels,
exactly as the provider's canonical column is. The node's column and
averaged-label normalizations are retained without changing their scales.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalNodes

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOM_BASE HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP
open FixedTripleFibers FixedTripleEnergy CanonicalChildren CanonicalNormPools
open ProviderNodes
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K} {σ : Type*}
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

def period (x : Node K S Γ Θ ψ σ) : HeckeCharacter K :=
  x.family.background x.triple * x.family.lambda⁻¹

def mark (x : Node K S Γ Θ ψ σ) : Ideal (𝓞 K) → ℂ :=
  divisorMark (x.family.survivors x.triple) x.family.primeLists x.family.primeWeights

def rowTau (x : Node K S Γ Θ ψ σ) (f k : Ext) (ξ : Sector) : Ideal (𝓞 K) →* ℂ :=
  canonicalTau K Sset D (period K S Γ x)
    ((((Sset).unitEquivUnitsInteger K (CanonicalSectors.sectorUnit K Sset Γ ξ)).val *
      D.generator k) * D.generator f ^ 4) x.puncture

def shortValue (x : Node K S Γ Θ ψ σ) (T : ℝ)
    (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector) : ℂ :=
  if hf : IsExterior K Sset f then
    if hk : IsExterior K Sset k.1 then
      ∑' H : Ideal (𝓞 K), if cubeIdealNorm H < T then
        extractedCubeTerm (exteriorGamma K Sset D)
          (rowTau K S Γ D x (exteriorOf K Sset f hf) (exteriorOf K Sset k.1 hk) k.2)
          (mark K S Γ x) (canonicalVstar x.test) (x.family.base ^ x.columnLength) H
      else 0
    else 0
  else 0

def longValue (x : Node K S Γ Θ ψ σ) (T : ℝ)
    (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector) : ℂ :=
  if hf : IsExterior K Sset f then
    if hk : IsExterior K Sset k.1 then
      ∑' CB : Ideal (𝓞 K) × Ideal (𝓞 K),
        reopenedCubeCoefficient (fun H => T ≤ cubeIdealNorm H) CB.2 *
          canonicalCompletedTerm (exteriorGamma K Sset D)
            (rowTau K S Γ D x (exteriorOf K Sset f hf) (exteriorOf K Sset k.1 hk) k.2)
            (mark K S Γ x) (canonicalVstar x.test) (x.family.base ^ x.columnLength) CB
    else 0
  else 0

def shortEnergy (slotCap : ℕ) (x : Node K S Γ Θ ψ σ) (T : ℝ) : ℝ :=
  x.family.base ^ (-x.labelLength) * ∑ f ∈ x.labels, labelDivisorWeight slotCap f *
    ∑ k ∈ x.rows, ‖shortValue K S Γ D x T f k‖ ^ 2

def longEnergy (slotCap : ℕ) (x : Node K S Γ Θ ψ σ) (T : ℝ) : ℝ :=
  x.family.base ^ (-x.labelLength) * ∑ f ∈ x.labels, labelDivisorWeight slotCap f *
    ∑ k ∈ x.rows, ‖longValue K S Γ D x T f k‖ ^ 2

theorem column_normalization (Z N : ℝ) (hZ : 0 < Z) :
    ((Z ^ (-N / 2) : ℝ) : ℂ) = (Real.sqrt (Z ^ N) : ℂ)⁻¹ := by
  rw [← Complex.ofReal_inv]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ.le, ← Real.rpow_neg hZ.le]
  congr 1
  ring

/-- Exact source decomposition on every raw node row and label. The
nonexterior zeros and the full family puncture are part of the equality. -/
theorem normalized_column_short_long
    (Λ G : HeckeCharacter K) (slotCap : ℕ) (Z A c z lo hi : ℝ)
    (x : Node K S Γ Θ ψ σ) (hx : x.Admissible D Λ G slotCap Z A c z lo hi)
    (hZ : 0 < Z) (T : ℝ) (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector) :
    ((x.family.base ^ (-x.columnLength / 2) : ℝ) : ℂ) *
        column K Sset D x.family (CanonicalSectors.sectorUnit K Sset Γ) x.triple f k =
      shortValue K S Γ D x T f k + longValue K S Γ D x T f k := by
  have hb : 0 < x.family.base := hx.base_eq.symm ▸ hZ
  by_cases hf : IsExterior K Sset f
  · by_cases hk : IsExterior K Sset k.1
    · let f' := exteriorOf K Sset f hf
      let k' := exteriorOf K Sset k.1 hk
      have hpuncture : childPuncture x.family.originalPuncture x.triple ≠ 0 :=
        hx.puncture_nonzero
      let r : NonzeroIdeal K :=
        ⟨childPuncture x.family.originalPuncture x.triple, mem_nonZeroDivisors_of_ne_zero hpuncture⟩
      have hp : x.family.columns x.triple =
          squarefreePool K Sset (2 * x.family.base ^ x.columnLength) := by
        rw [hx.base_eq]
        exact hx.complete_pool
      have he := family_column_eq_completeCanonicalColumn K Sset D x.family x.triple
        (CanonicalSectors.sectorUnit K Sset Γ) k' f' k.2 hb hp hx.test_support
        hpuncture hx.calibration.lambda_unramified
      have hW : Function.support (x.family.cutoff x.triple) ⊆ Set.Iic 2 := by
        intro y hy
        exact (hx.test_support (subset_closure hy)).2
      rw [column_normalization _ _ hb]
      change (Real.sqrt (x.family.base ^ x.family.columnLength x.triple) : ℂ)⁻¹ *
          column K Sset D x.family (CanonicalSectors.sectorUnit K Sset Γ) x.triple
            f'.val.val (k'.val.val, k.2) = _
      rw [he, completeCanonicalColumn_short_long K Sset D _ _ _ _ _
        (x.family.cutoff x.triple) (x.family.base ^ x.family.columnLength x.triple) T
        (Real.rpow_pos_of_pos hb _) hW]
      simp only [canonicalTau_exteriorRadicalPuncture]
      simp only [shortValue, longValue, dif_pos hf, dif_pos hk, rowTau, period, mark,
        Node.columnLength, Node.test, Node.puncture, f', k', r]
    · simp only [column, sectorRow, dif_neg hk, mul_zero, zero_mul, Finset.sum_const_zero,
        shortValue, longValue, dif_pos hf, dif_neg hk, add_zero]
  · simp only [column, labelRow, dif_neg hf, zero_pow (by decide : (4 : ℕ) ≠ 0),
      mul_zero, zero_mul, Finset.sum_const_zero, shortValue, longValue, add_zero]

private theorem norm_add_sq_bound (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  calc
    _ ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
    _ ≤ _ := by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- The complete original energy is bounded by its two proved source
pieces. The one averaged-label normalization and divisor weight remain
on both sides. -/
theorem energy_le_short_long
    (Λ G : HeckeCharacter K) (slotCap : ℕ) (Z A c z lo hi : ℝ)
    (x : Node K S Γ Θ ψ σ) (hx : x.Admissible D Λ G slotCap Z A c z lo hi)
    (hZ : 0 < Z) (T : ℝ) :
    x.energy D slotCap ≤
      2 * (shortEnergy K S Γ D slotCap x T + longEnergy K S Γ D slotCap x T) := by
  have hb : 0 < x.family.base := hx.base_eq.symm ▸ hZ
  unfold Node.energy normalizedChildEnergy childValue shortEnergy longEnergy
  simp_rw [normalized_column_short_long K S Γ D Λ G slotCap Z A c z lo hi x hx hZ T]
  calc
    _ ≤ x.family.base ^ (-x.labelLength) *
        ∑ f ∈ x.labels, labelDivisorWeight slotCap f *
          ∑ k ∈ x.rows, 2 * (‖shortValue K S Γ D x T f k‖ ^ 2 +
            ‖longValue K S Γ D x T f k‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hb.le _)
      apply Finset.sum_le_sum
      intro f hf
      apply mul_le_mul_of_nonneg_left _ (labelDivisorWeight_nonneg slotCap f)
      exact Finset.sum_le_sum (fun k hk => norm_add_sq_bound _ _)
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
      congr 1
      all_goals
        apply Finset.sum_congr rfl
        intro f hf
        apply Finset.sum_congr rfl
        intro k hk
        ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalNodes

end
