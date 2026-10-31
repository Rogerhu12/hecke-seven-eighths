import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalAtomEnvelope
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildMass

/-!
# Uniform exceptional amplitude from original individual atom bounds

The finite products here are the computed original frozen atoms and
the actual retained prime counts.  A single original slot cap and
single-atom profile radius give an explicit polynomial upper bound for
the exceptional constant.  No source norm, row energy or terminal sum
is a hypothesis.  The resulting power of the profile radius can be
integrated against the same original nested Schwartz Fourier measure.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis

variable {F : Type} [Field F] [NumberField F]

private theorem exceptional_selected_product_le {I : Type*} [Fintype I]
    (s : Finset I) (f : I → ℝ) (B : ℝ) (cap : ℕ)
    (hB : 1 ≤ B) (hcap : Fintype.card I ≤ cap)
    (hnonneg : ∀ i ∈ s, 0 ≤ f i) (hbound : ∀ i ∈ s, f i ≤ B) :
    (∏ i ∈ s, f i) ≤ B ^ cap := by
  calc
    _ ≤ ∏ _i ∈ s, B := Finset.prod_le_prod₀ hnonneg hbound
    _ = B ^ s.card := by simp only [Finset.prod_const]
    _ ≤ B ^ cap := pow_le_pow_right₀ hB ((Finset.card_le_univ s).trans hcap)

private theorem exceptional_sqrt_pair_le (x y B : ℝ) (hB : 0 ≤ B)
    (hx : x ≤ B) (hy : y ≤ B) : Real.sqrt x * Real.sqrt y ≤ B := by
  calc
    _ ≤ Real.sqrt B * Real.sqrt B := mul_le_mul
      (Real.sqrt_le_sqrt hx) (Real.sqrt_le_sqrt hy) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = B := by nlinarith [Real.sq_sqrt hB]

namespace ExceptionalAtomicScales

variable {k l : ℕ} {left : ActualColumnAllocation F k} {right : ActualColumnAllocation F l}

/-- Every selected frozen and retained occurrence is charged once.
The statement includes the empty slot set without a separate case. -/
theorem pair_constant_le_from_atoms
    (UL : ExceptionalAtomicScales left) (UR : ExceptionalAtomicScales right)
    (cap : ℕ) (B : ℝ) (hB : 1 ≤ B) (hk : k ≤ cap) (hl : l ≤ cap)
    (hfreezeL : ∀ i ∈ Finset.univ \ left.keep, UL.annulus i * UL.profileSquare i ≤ B)
    (hfreezeR : ∀ i ∈ Finset.univ \ right.keep, UR.annulus i * UR.profileSquare i ≤ B)
    (hrootL : UL.rootConstant ≤ B) (hrootR : UR.rootConstant ≤ B)
    (hcutoffL : ∀ i, UL.cutoffConstant i ≤ B) (hcutoffR : ∀ i, UR.cutoffConstant i ≤ B)
    (hatomL : ∀ i, UL.atomConstant i ≤ B) (hatomR : ∀ i, UR.atomConstant i ≤ B) :
    UL.constant * UR.constant ≤
      B ^ (cap + 2) * (idealCountConstant F * B ^ 2) ^ (2 * cap) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hcount0 : 0 ≤ idealCountConstant F := zero_le_one.trans (one_le_idealCountConstant F)
  have hD : 1 ≤ idealCountConstant F * B ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_idealCountConstant F) (one_le_pow₀ hB)
  have hNL : UL.frozenNumerator ≤ B ^ cap :=
    exceptional_selected_product_le _ _ B cap hB (by simpa only [Fintype.card_fin] using hk)
      (fun i _ => mul_nonneg (UL.annulus_nonneg i) (UL.profileSquare_nonneg i)) hfreezeL
  have hNR : UR.frozenNumerator ≤ B ^ cap :=
    exceptional_selected_product_le _ _ B cap hB (by simpa only [Fintype.card_fin] using hl)
      (fun i _ => mul_nonneg (UR.annulus_nonneg i) (UR.profileSquare_nonneg i)) hfreezeR
  have hsqrt := exceptional_sqrt_pair_le _ _ _ (pow_nonneg hB0 cap) hNL hNR
  have hroots : UL.rootConstant * UR.rootConstant ≤ B ^ 2 := by
    simpa only [pow_two] using mul_le_mul hrootL hrootR UR.rootConstant_nonneg hB0
  have hliveL : (∏ i, (idealCountConstant F * UL.cutoffConstant i) * UL.atomConstant i) ≤
      (idealCountConstant F * B ^ 2) ^ cap := by
    apply exceptional_selected_product_le _ _ _ cap hD
    · simpa only [Fintype.card_fin] using
        (show left.keep.card ≤ cap from (Finset.card_le_univ _).trans
          (by simpa only [Fintype.card_fin] using hk))
    · intro i _
      exact mul_nonneg (mul_nonneg hcount0 (zero_le_one.trans (UL.cutoffConstant_one i)))
        (UL.atomConstant_nonneg i)
    · intro i _
      have hi := mul_le_mul (mul_le_mul_of_nonneg_left (hcutoffL i) hcount0)
        (hatomL i) (UL.atomConstant_nonneg i) (mul_nonneg hcount0 hB0)
      convert hi using 1 <;> ring
  have hliveR : (∏ i, (idealCountConstant F * UR.cutoffConstant i) * UR.atomConstant i) ≤
      (idealCountConstant F * B ^ 2) ^ cap := by
    apply exceptional_selected_product_le _ _ _ cap hD
    · simpa only [Fintype.card_fin] using
        (show right.keep.card ≤ cap from (Finset.card_le_univ _).trans
          (by simpa only [Fintype.card_fin] using hl))
    · intro i _
      exact mul_nonneg (mul_nonneg hcount0 (zero_le_one.trans (UR.cutoffConstant_one i)))
        (UR.atomConstant_nonneg i)
    · intro i _
      have hi := mul_le_mul (mul_le_mul_of_nonneg_left (hcutoffR i) hcount0)
        (hatomR i) (UR.atomConstant_nonneg i) (mul_nonneg hcount0 hB0)
      convert hi using 1 <;> ring
  have hlive0 : 0 ≤ ∏ i, (idealCountConstant F * UR.cutoffConstant i) * UR.atomConstant i :=
    Finset.prod_nonneg fun i _ =>
      mul_nonneg (mul_nonneg hcount0 (zero_le_one.trans (UR.cutoffConstant_one i)))
        (UR.atomConstant_nonneg i)
  have hprod := mul_le_mul hliveL hliveR hlive0 (pow_nonneg (zero_le_one.trans hD) cap)
  have hroot0 : 0 ≤ UL.rootConstant * UR.rootConstant :=
    mul_nonneg UL.rootConstant_nonneg UR.rootConstant_nonneg
  have hcombined := mul_le_mul
    (mul_le_mul hsqrt hroots hroot0 (pow_nonneg hB0 cap)) hprod
    (mul_nonneg
      (Finset.prod_nonneg fun i _ =>
        mul_nonneg (mul_nonneg hcount0 (zero_le_one.trans (UL.cutoffConstant_one i)))
          (UL.atomConstant_nonneg i)) hlive0)
    (mul_nonneg (pow_nonneg hB0 cap) (sq_nonneg B))
  convert hcombined using 1 <;>
    simp only [constant, pow_add, two_mul] <;> ring

end ExceptionalAtomicScales

namespace ActualSecondRowMass

variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS} {kLeft kRight : ℕ}

/-- This common-atom bound is independent of any ordinary child
calibration or capacity choice. -/
theorem commonEnvelope_le_from_atoms
    (W : ActualSecondRowMass R C kLeft kRight) (cap : ℕ) (B : ℝ)
    (hB : 1 ≤ B) (hkLeft : kLeft ≤ cap) (hkRight : kRight ≤ cap)
    (hprofile : W.profileBound ≤ B)
    (hleft : ∀ i ∈ Finset.univ \ W.leftAtoms.keep,
      W.leftAtoms.annulus i * W.leftAtoms.profile i ≤ B)
    (hright : ∀ i ∈ Finset.univ \ W.rightAtoms.keep,
      W.rightAtoms.annulus i * W.rightAtoms.profile i ≤ B) :
    W.commonEnvelope ≤ B ^ (cap + 1) := by
  have hL : W.leftAtoms.envelope ≤ B ^ cap :=
    exceptional_selected_product_le _ _ B cap hB
      (by simpa only [Fintype.card_fin] using hkLeft)
      (fun i _ => mul_nonneg (W.leftAtoms.annulus_nonneg i) (W.leftAtoms.profile_nonneg i)) hleft
  have hR : W.rightAtoms.envelope ≤ B ^ cap :=
    exceptional_selected_product_le _ _ B cap hB
      (by simpa only [Fintype.card_fin] using hkRight)
      (fun i _ => mul_nonneg (W.rightAtoms.annulus_nonneg i) (W.rightAtoms.profile_nonneg i)) hright
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hs := exceptional_sqrt_pair_le _ _ _ (pow_nonneg hB0 cap) hL hR
  have h := mul_le_mul hprofile hs
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hB0
  change W.profileBound * Real.sqrt W.leftAtoms.envelope * Real.sqrt W.rightAtoms.envelope ≤ _
  calc
    _ = W.profileBound * (Real.sqrt W.leftAtoms.envelope * Real.sqrt W.rightAtoms.envelope) := by ring
    _ ≤ B * B ^ cap := h
    _ = _ := by rw [pow_succ]; ring

end ActualSecondRowMass
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ExceptionalAtomicScales.pair_constant_le_from_atoms
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondRowMass.commonEnvelope_le_from_atoms
