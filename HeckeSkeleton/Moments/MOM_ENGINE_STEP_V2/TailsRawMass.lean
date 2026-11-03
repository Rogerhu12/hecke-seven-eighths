import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondTailBudget

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Coarse finite counts for the exact first and second tail masses

The residual coprimality gate assigns each original pair to exactly
one common label. Thus a crude column-pair count is enough for a tail:
the positive cutoff exponent will absorb every fixed polynomial loss.
Both estimates retain the complete original nonprimitive residue.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open EngineStep NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {ι κ : Type*}

theorem common_pair_card_le (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior) :
    ((firstZeroPairs left right fullI fullJ).card : ℝ) ≤
      (left.card : ℝ) * (right.card : ℝ) := by
  have hs : (firstZeroPairs left right fullI fullJ).image Prod.snd ⊆ left ×ˢ right := by
    intro ij hij
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hij
    have hm := (mem_firstZeroPairs left right fullI fullJ v).mp hv
    exact Finset.mem_product.mpr ⟨hm.1, hm.2.1⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injOn
    (firstZeroPairs_projection_injective left right fullI fullJ), Finset.card_product] at hc
  exact_mod_cast hc

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces} {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]

theorem first_tail_mass_count_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val)
    (orders : Finset (ℕ × ℕ))
    (profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (radius : {r : ℝ // 0 < r}) (mask : Finset (HeightOneSpectrum A.R))
    (Amp maskBound modulusBound : ℝ)
    (hAmp : 0 ≤ Amp) (hmaskBound : 0 ≤ maskBound) (hmodulusBound : 0 ≤ modulusBound)
    (hprofile : ∀ v ∈ firstZeroPairs left right fullI fullJ,
      orders.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
        (profiles v.2.1 v.2.2) ≤ Amp)
    (hmask : ∀ v ∈ firstZeroPairs left right fullI fullJ,
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          ((blocks v.1).mask mask))).val ≤ maskBound)
    (hmodulus : ∀ v ∈ firstZeroPairs left right fullI fullJ,
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        ⟨((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).modulus,
          ((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).modulus_ne_zero⟩).val ≤ modulusBound) :
    firstBlockTailMass hΓ C left right fullI fullJ blocks orders profiles radius mask ≤
      (left.card : ℝ) * (right.card : ℝ) * Amp *
        (firstTailFieldConstant K * maskBound * (radius.val⁻¹ + modulusBound)) := by
  let bound := firstTailFieldConstant K * maskBound * (radius.val⁻¹ + modulusBound)
  have hbound : 0 ≤ bound :=
    mul_nonneg (mul_nonneg firstTailFieldConstant_nonneg hmaskBound)
      (add_nonneg (inv_nonneg.mpr radius.property.le) hmodulusBound)
  have hpoint (v) (hv : v ∈ firstZeroPairs left right fullI fullJ) :
      orders.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
          (profiles v.2.1 v.2.2) *
        ((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).truncationMass
          ((blocks v.1).mask mask) radius ≤ Amp * bound := by
    have hm := ((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).truncationMass_le_mask_norm
      ((blocks v.1).residue_norm_le_one hΓ C profiles v.2.1 v.2.2)
      ((blocks v.1).mask mask) radius
    have hm' : ((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).truncationMass
        ((blocks v.1).mask mask) radius ≤ bound := by
      apply hm.trans
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hmask v hv) firstTailFieldConstant_nonneg)
        (add_le_add le_rfl (hmodulus v hv))
        (add_nonneg (inv_nonneg.mpr radius.property.le)
          (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
            ⟨((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).modulus,
              ((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).modulus_ne_zero⟩).property.le)
        (mul_nonneg firstTailFieldConstant_nonneg hmaskBound)
    exact (mul_le_mul_of_nonneg_left hm' (apply_nonneg _ _)).trans
      (mul_le_mul_of_nonneg_right (hprofile v hv) hbound)
  rw [firstBlockTailMass_eq_original_pairs]
  calc
    _ ≤ ∑ _v ∈ firstZeroPairs left right fullI fullJ, Amp * bound :=
      Finset.sum_le_sum hpoint
    _ = ((firstZeroPairs left right fullI fullJ).card : ℝ) * (Amp * bound) := by simp
    _ ≤ ((left.card : ℝ) * (right.card : ℝ)) * (Amp * bound) :=
      mul_le_mul_of_nonneg_right (common_pair_card_le left right fullI fullJ)
        (mul_nonneg hAmp hbound)
    _ = _ := by ring

variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)

theorem second_tail_mass_count_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val)
    (orders : Finset (ℕ × ℕ))
    (profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (radius : {r : ℝ // 0 < r}) (mask : Finset (HeightOneSpectrum A.R))
    (Amp maskBound modulusBound : ℝ)
    (hAmp : 0 ≤ Amp) (hmaskBound : 0 ≤ maskBound) (hmodulusBound : 0 ≤ modulusBound)
    (hprofile : ∀ v ∈ firstZeroPairs left right fullI fullJ,
      orders.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
        (profiles v.2.1 v.2.2) ≤ Amp)
    (hmask : (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) mask)).val ≤ maskBound)
    (hmodulus : ∀ v ∈ firstZeroPairs left right fullI fullJ,
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        ⟨((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).modulus,
          ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).modulus_ne_zero⟩).val ≤
        modulusBound) :
    secondBlockTailMass hΓ hDiff C left right fullI fullJ blocks orders profiles radius mask ≤
      (left.card : ℝ) * (right.card : ℝ) * Amp *
        (modulusBound * (firstTailFieldConstant K * maskBound *
          (radius.val⁻¹ + modulusBound))) := by
  let bound := modulusBound * (firstTailFieldConstant K * maskBound *
    (radius.val⁻¹ + modulusBound))
  have hbound : 0 ≤ bound := mul_nonneg hmodulusBound
    (mul_nonneg (mul_nonneg firstTailFieldConstant_nonneg hmaskBound)
      (add_nonneg (inv_nonneg.mpr radius.property.le) hmodulusBound))
  have hpoint (v) (hv : v ∈ firstZeroPairs left right fullI fullJ) :
      orders.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
          (profiles v.2.1 v.2.2) *
        ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).truncationMass
          mask radius ≤ Amp * bound := by
    have hm := ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).truncationMass_le_residue_bound
      modulusBound hmodulusBound
      (fun x => ((blocks v.1).second_residue_norm_le_modulus hΓ hDiff C profiles
        v.2.1 v.2.2 x).trans (hmodulus v hv)) mask radius
    have hm' : ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).truncationMass
        mask radius ≤ bound := by
      apply hm.trans
      apply mul_le_mul_of_nonneg_left _ hmodulusBound
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hmask firstTailFieldConstant_nonneg)
        (add_le_add le_rfl (hmodulus v hv))
        (add_nonneg (inv_nonneg.mpr radius.property.le)
          (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
            ⟨((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).modulus,
              ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).modulus_ne_zero⟩).property.le)
        (mul_nonneg firstTailFieldConstant_nonneg hmaskBound)
    exact (mul_le_mul_of_nonneg_left hm' (apply_nonneg _ _)).trans
      (mul_le_mul_of_nonneg_right (hprofile v hv) hbound)
  rw [secondBlockTailMass_eq_original_pairs]
  calc
    _ ≤ ∑ _v ∈ firstZeroPairs left right fullI fullJ, Amp * bound :=
      Finset.sum_le_sum hpoint
    _ = ((firstZeroPairs left right fullI fullJ).card : ℝ) * (Amp * bound) := by simp
    _ ≤ ((left.card : ℝ) * (right.card : ℝ)) * (Amp * bound) :=
      mul_le_mul_of_nonneg_right (common_pair_card_le left right fullI fullJ)
        (mul_nonneg hAmp hbound)
    _ = _ := by ring

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.first_tail_mass_count_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.second_tail_mass_count_bound
