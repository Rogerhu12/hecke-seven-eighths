import HeckeSkeleton.Moments.MOM_INV_STEP.DivisorInverseColumn
import HeckeGeneral.Analysis.IdealMobiusReciprocal
import HeckeSkeleton.Moments.MOM_INV_STEP.CoefficientBounds
import HeckeGeneral.Analysis.IdealMobiusReciprocal

/-!
# Uniform bound for the literal intermediate inverse coefficient

The real coefficient keeps μ, its admissible Hecke background, original
puncture and label zeros, original mark weights and the retained divisor
character. Only its actual norm test is estimated by its zeroth seminorm.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.InverseCoefficientBounds

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CoefficientBounds
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset

theorem labelRow_norm_le_one (n : Ext) (j : Ideal (𝓞 K)) :
    ‖labelRow K Sset D n j‖ ≤ 1 := by
  unfold labelRow
  split_ifs with hj
  · exact idealSymbol_norm_le_one K S D n (D.generator (exteriorOf K Sset j hj))
  · simp only [norm_zero, zero_le_one]

variable {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

theorem coefficient_norm_le_mark (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS) (n : Ext) :
    ‖DivisorInverseColumn.coefficient K S D C γ j d n‖ ≤
      ‖divisorMark (C.survivors γ) C.primeLists C.primeWeights n.val.val‖ *
        SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ) := by
  have hμ := IdealMobiusReciprocal.norm_moebius_le_one K n.val
  have hν := norm_heckeIdealCoefficient_le_one K (C.background γ) n.val
  have hρ : ‖(if IsCoprime n.val.val (childPuncture C.originalPuncture γ)
      then 1 else 0 : ℂ)‖ ≤ 1 := by split_ifs <;> norm_num
  have hj := labelRow_norm_le_one K S D n j
  have hd := idealSymbol_norm_le_one K S D n d
  have hW := SchwartzMap.norm_le_seminorm ℝ (C.cutoff γ)
    ((n.val.val.absNorm : ℝ) / C.base ^ C.columnLength γ)
  unfold DivisorInverseColumn.coefficient FirstCanonicalLabel.inverseCoefficient
  simp only [norm_mul, norm_pow]
  calc
    _ ≤ 1 * 1 * 1 * 1 ^ 4 *
        ‖divisorMark (C.survivors γ) C.primeLists C.primeWeights n.val.val‖ *
        SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ) * 1 := by gcongr
    _ = _ := by ring

/-- The constant precedes the whole canonical family, its original
individual weights, puncture, row, label and support scale. -/
theorem exists_coefficient_bound (slotCap : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {σ : Type*} {Θ : Subgroup (HeckeCharacter K)}
      {ψ : HeckeCharacter K} (C : ColumnFamily K Sset σ Θ ψ)
      (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS) (n : Ext) (X : ℝ),
      C.originalSlots.card ≤ slotCap →
      (∀ i ∈ C.originalSlots, ∀ P ∈ C.primeLists i, ‖C.primeWeights i P‖ ≤ 1) →
      (n.val.val.absNorm : ℝ) ≤ X →
      ‖DivisorInverseColumn.coefficient K S D C γ j d n‖ ≤
        A * SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ) * X ^ ε := by
  obtain ⟨A, hA, hmark⟩ := exists_divisorMark_bound K slotCap ε hε
  refine ⟨A, hA, ?_⟩
  intro σ Θ ψ C γ j d n X hcap ha hn
  have hsurvive : (C.survivors γ).card ≤ slotCap :=
    (Finset.card_le_card (C.survivors_subset γ)).trans hcap
  have hmark' := hmark (C.survivors γ) C.primeLists C.primeWeights n.val.val
    (nonZeroDivisors.coe_ne_zero n.val) hsurvive
    (fun i hi P hP => ha i (C.survivors_subset γ hi) P hP)
  have hmarkX : ‖divisorMark (C.survivors γ) C.primeLists C.primeWeights n.val.val‖ ≤
      A * X ^ ε := hmark'.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hn hε.le)
      (le_trans zero_le_one hA))
  calc
    _ ≤ ‖divisorMark (C.survivors γ) C.primeLists C.primeWeights n.val.val‖ *
        SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ) :=
      coefficient_norm_le_mark K S D C γ j d n
    _ ≤ (A * X ^ ε) * SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ) :=
      mul_le_mul_of_nonneg_right hmarkX (apply_nonneg _ _)
    _ = _ := by ring

end HeckeSkeleton.Moments.MOM_INV_STEP.InverseCoefficientBounds

end
