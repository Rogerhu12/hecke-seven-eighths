import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderNode
import HeckeSkeleton.Moments.MOM_INV_STEP.DivisorRowMass

/-!
# The literal short node contribution and its label normalization

The short extracted series is reindexed directly over exterior ideals,
then each completed sum is identified with the actual theta source.
The raw puncture keeps its proved exterior-radical mask, and all original
nonexterior zeros remain explicit. No subtraction of the long piece is
used in this identity.

The final label sum uses the genuine divisor mass. Its small power is
chosen from the available saving and the fixed label-length capacity
before any labels, node or radial test are selected.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalNodeShort

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOM_BASE HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP
open FixedTripleEnergy CanonicalChildren CanonicalNormPools ProviderNodes TerminalNodes
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

section Completed

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- Direct identification of the restricted short series, including
its original signed cube scalar and whole-index mark. -/
theorem short_extracted_eq_completed
    (θ : HeckeCharacter K) (k : S.integer K) (f r : ExteriorIdeal K S)
    (mark : Ideal (𝓞 K) → ℂ) (W : ℝ → ℂ) (X T : ℝ)
    (hX : 0 < X) (hW : Function.support W ⊆ Set.Iic 2) :
    (∑' H : Ideal (𝓞 K), if cubeIdealNorm H < T then
      extractedCubeTerm (exteriorGamma K S D)
        (canonicalTau K S D θ (k * D.generator f ^ 4) r.val.val)
        mark (canonicalVstar W) X H else 0) =
      shortCompletedColumn K S D θ k f r mark W X T := by
  have hinj : Function.Injective (fun I : ExteriorIdeal K S => I.val.val) := by
    intro I J h
    exact Subtype.ext (Subtype.ext h)
  have hs : Function.support (fun H : Ideal (𝓞 K) => if cubeIdealNorm H < T then
      extractedCubeTerm (exteriorGamma K S D)
        (canonicalTau K S D θ (k * D.generator f ^ 4) r.val.val)
        mark (canonicalVstar W) X H else 0) ⊆
      Set.range (fun I : ExteriorIdeal K S => I.val.val) := by
    intro H hH
    have he : HeckePort.CenteredMomentGenerator.IsExterior K S H := by
      by_contra he
      have hz := canonicalTau_eq_zero_of_not_exterior K S D θ
        (k * D.generator f ^ 4) r.val.val H he
      exact hH (by simp [extractedCubeTerm, hz])
    exact ⟨HeckePort.CenteredMomentGenerator.toExterior K S H he, rfl⟩
  rw [← hinj.tsum_eq hs, shortCompletedColumn_eq_tsum K S D θ k f r mark W X T]
  apply tsum_congr
  intro H
  change (if exteriorNorm K S H < T then
      extractedCubeTerm (exteriorGamma K S D)
        (canonicalTau K S D θ (k * D.generator f ^ 4) r.val.val)
        mark (canonicalVstar W) X H.val.val else 0) = _
  by_cases hT : exteriorNorm K S H < T
  · simp only [if_pos hT]
    have hN : 0 < exteriorNorm K S H := idealNorm_pos K H.val
    have hscale : 0 < X / exteriorNorm K S H ^ 3 := div_pos hX (pow_pos hN 3)
    unfold extractedCubeTerm
    congr 1
    simpa only [wholeMarkWeight_empty, one_mul, cubeIdealNorm, exteriorNorm] using
      canonicalCompletedSum_eq_weightedTheta K S D θ (k * D.generator f ^ 4) r ∅
        (fun A => mark (H.val.val ^ 3 * A)) (canonicalVstar W)
        (X / exteriorNorm K S H ^ 3) 2 hscale (canonicalVstar_support_upper W 2 hW)
  · simp only [if_neg hT]

end Completed

section Nodes

variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K} {σ : Type*}
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

/-- The complete formula on raw row and label ideals retains the
original zero extension off the exterior support. -/
theorem shortValue_eq_extended_completed (x : Node K S Γ Θ ψ σ)
    (hbase : 0 < x.family.base) (hpuncture : x.puncture ≠ 0)
    (hW : Function.support x.test ⊆ Set.Iic 2)
    (T : ℝ) (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector) :
    let r : NonzeroIdeal K := ⟨x.puncture, mem_nonZeroDivisors_of_ne_zero hpuncture⟩
    shortValue K S Γ D x T f k =
      if hf : IsExterior K Sset f then
        if hk : IsExterior K Sset k.1 then
          shortCompletedColumn K Sset D (period K S Γ x)
            (((Sset).unitEquivUnitsInteger K (CanonicalSectors.sectorUnit K Sset Γ k.2)).val *
              D.generator (exteriorOf K Sset k.1 hk))
            (exteriorOf K Sset f hf) (exteriorRadicalPuncture K Sset r)
            (mark K S Γ x) x.test (x.family.base ^ x.columnLength) T
        else 0
      else 0 := by
  dsimp only
  by_cases hf : IsExterior K Sset f
  · by_cases hk : IsExterior K Sset k.1
    · simp only [shortValue, dif_pos hf, dif_pos hk]
      have he := short_extracted_eq_completed K Sset D (period K S Γ x)
        (((Sset).unitEquivUnitsInteger K (CanonicalSectors.sectorUnit K Sset Γ k.2)).val *
          D.generator (exteriorOf K Sset k.1 hk))
        (exteriorOf K Sset f hf)
        (exteriorRadicalPuncture K Sset
          ⟨x.puncture, mem_nonZeroDivisors_of_ne_zero hpuncture⟩)
        (mark K S Γ x) x.test (x.family.base ^ x.columnLength) T
        (Real.rpow_pos_of_pos hbase _) hW
      simpa only [canonicalTau_exteriorRadicalPuncture, rowTau] using he
    · simp only [shortValue, dif_pos hf, dif_neg hk]
  · simp only [shortValue, dif_neg hf]

/-- On actual exterior rows this is the exact short completed source
used by the terminal reflection, at its original column scale. -/
theorem shortValue_exterior (x : Node K S Γ Θ ψ σ)
    (hbase : 0 < x.family.base) (hpuncture : x.puncture ≠ 0)
    (hW : Function.support x.test ⊆ Set.Iic 2)
    (T : ℝ) (f k : Ext) (ξ : Sector) :
    let r : NonzeroIdeal K := ⟨x.puncture, mem_nonZeroDivisors_of_ne_zero hpuncture⟩
    shortValue K S Γ D x T f.val.val (k.val.val, ξ) =
      shortCompletedColumn K Sset D (period K S Γ x)
        (((Sset).unitEquivUnitsInteger K (CanonicalSectors.sectorUnit K Sset Γ ξ)).val * D.generator k)
        f (exteriorRadicalPuncture K Sset r) (mark K S Γ x) x.test
        (x.family.base ^ x.columnLength) T := by
  have hf : IsExterior K Sset f.val.val := ⟨nonZeroDivisors.coe_ne_zero f.val, f.property⟩
  have hk : IsExterior K Sset k.val.val := ⟨nonZeroDivisors.coe_ne_zero k.val, k.property⟩
  have hef : exteriorOf K Sset f.val.val hf = f := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hek : exteriorOf K Sset k.val.val hk = k := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  simpa only [dif_pos hf, dif_pos hk, hef, hek] using
    shortValue_eq_extended_completed K S Γ D x hbase hpuncture hW T f.val.val (k.val.val, ξ)

theorem shortValue_zero_of_nonexterior_label (x : Node K S Γ Θ ψ σ) (T : ℝ)
    (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector) (hf : ¬ IsExterior K Sset f) :
    shortValue K S Γ D x T f k = 0 := by
  simp only [shortValue, dif_neg hf]

theorem shortValue_zero_of_nonexterior_row (x : Node K S Γ Θ ψ σ) (T : ℝ)
    (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector) (hk : ¬ IsExterior K Sset k.1) :
    shortValue K S Γ D x T f k = 0 := by
  by_cases hf : IsExterior K Sset f
  · simp only [shortValue, dif_pos hf, dif_neg hk]
  · simp only [shortValue, dif_neg hf]

/-- The label divisor mass consumes half of an already proved saving.
Its constant precedes all actual labels, rows and profiles. -/
theorem exists_label_normalized_bound (slotCap : ℕ) (A saving : ℝ)
    (hA : 0 ≤ A) (hsaving : 0 < saving) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}
      (Z F B T : ℝ) (x : Node K S Γ Θ ψ σ),
      1 ≤ Z → x.family.base = Z → 0 ≤ x.labelLength → x.labelLength ≤ A →
      (∀ f ∈ x.labels, (f.absNorm : ℝ) ≤ Z ^ x.labelLength) → 0 ≤ B →
      (∀ f ∈ x.labels, (∑ k ∈ x.rows, ‖shortValue K S Γ D x T f k‖ ^ 2) ≤
        B * Z ^ (F - saving)) →
      shortEnergy K S Γ D slotCap x T ≤ C * B * Z ^ (F - saving / 2) := by
  let delta := saving / (2 * (A + 1))
  have hdelta : 0 < delta := div_pos hsaving (by positivity)
  obtain ⟨C, hC, hmass⟩ := DivisorRowMass.exists_label_mass_bound
    (K := K) (9 + 4 * slotCap) (by omega) delta hdelta
  refine ⟨C, hC, ?_⟩
  intro σ Θ ψ Z F B T x hZ hbase hV0 hV hlabels hB hrows
  have hZp := zero_lt_one.trans_le hZ
  have hC0 := zero_le_one.trans hC
  have hnorm : 1 ≤ Z ^ x.labelLength := Real.one_le_rpow hZ hV0
  have hm : (∑ f ∈ x.labels, labelDivisorWeight slotCap f) ≤
      C * (Z ^ x.labelLength) ^ (1 + delta) := hmass x.labels _ hnorm hlabels
  have hsmall : x.labelLength * delta ≤ saving / 2 := by
    dsimp only [delta]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (A + 1))).mpr
    nlinarith
  unfold shortEnergy
  rw [hbase]
  calc
    _ ≤ Z ^ (-x.labelLength) * ∑ f ∈ x.labels,
        labelDivisorWeight slotCap f * (B * Z ^ (F - saving)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hZp.le _)
      exact Finset.sum_le_sum (fun f hf => mul_le_mul_of_nonneg_left
        (hrows f hf) (labelDivisorWeight_nonneg slotCap f))
    _ = Z ^ (-x.labelLength) *
        (∑ f ∈ x.labels, labelDivisorWeight slotCap f) * (B * Z ^ (F - saving)) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ Z ^ (-x.labelLength) * (C * (Z ^ x.labelLength) ^ (1 + delta)) *
        (B * Z ^ (F - saving)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hZp.le _))
        (mul_nonneg hB (Real.rpow_nonneg hZp.le _))
    _ = C * B * Z ^ (F - saving + x.labelLength * delta) := by
      rw [← Real.rpow_mul hZp.le]
      calc
        _ = C * B * (Z ^ (-x.labelLength) * Z ^ (x.labelLength * (1 + delta)) *
            Z ^ (F - saving)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hZp, ← Real.rpow_add hZp]
          congr 2
          ring
    _ ≤ C * B * Z ^ (F - saving / 2) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
        (mul_nonneg hC0 hB)

end Nodes

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalNodeShort
