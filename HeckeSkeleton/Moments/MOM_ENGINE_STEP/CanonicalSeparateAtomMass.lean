import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalCapacityKernelMass

/-!
# Frozen occurrence costs with the original row scalar paid once

The first common scalar and the pool reciprocity scalar have already
been extracted into the actual row profile. They remain a single factor
`W.profileBound` here. Only the individual common, allocated and removed
prime occurrences contribute to the power of the fixed atom bound.

The full-kappa producer has normalized prime bounds equal to one. Its
specialization below therefore pays only the common and allocated
occurrences. All frames, calibrations, selected children and removed
sets are the original ones.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.CanonicalSeparateAtomMass

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

private theorem selected_product_le {I : Type*} [Fintype I]
    (s : Finset I) (f : I → ℝ) (B : ℝ) (cap : ℕ)
    (hB : 1 ≤ B) (hcap : Fintype.card I ≤ cap)
    (hnonneg : ∀ i ∈ s, 0 ≤ f i) (hbound : ∀ i ∈ s, f i ≤ B) :
    (∏ i ∈ s, f i) ≤ B ^ cap := by
  calc
    _ ≤ ∏ _i ∈ s, B := Finset.prod_le_prod₀ hnonneg hbound
    _ = B ^ s.card := Finset.prod_const B
    _ ≤ B ^ cap := pow_le_pow_right₀ hB
      ((Finset.card_le_card (Finset.subset_univ s)).trans
        (by simpa only [Finset.card_univ] using hcap))

private theorem sqrt_pair_le {x y M : ℝ} (hM : 0 ≤ M)
    (hx : x ≤ M) (hy : y ≤ M) : Real.sqrt x * Real.sqrt y ≤ M := by
  have h := mul_le_mul (Real.sqrt_le_sqrt hx) (Real.sqrt_le_sqrt hy)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have he : Real.sqrt M * Real.sqrt M = M := by nlinarith [Real.sq_sqrt hM]
  exact h.trans_eq he

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [IsPrincipalIdealRing A.R]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {ω ψ : HeckeCharacter K} {k l kLeft kRight : ℕ}
variable (left : SecondSideFrame (V := V) C R Ray .left k)
variable (right : SecondSideFrame (V := V) C R Ray .right l)
variable (calL : left.source.Calibration (σ := σ) ω ψ)
variable (calR : right.source.Calibration (σ := σ) ω ψ)
variable (W : ActualSecondRowMass R C kLeft kRight)
variable (BL : left.source.FrozenAtomBounds) (BR : right.source.FrozenAtomBounds)
variable {li : (left.arithmeticCalibration calL W BL).CapacityInput}
variable {ri : (right.arithmeticCalibration calR W BR).CapacityInput}
variable (lc : (left.arithmeticCalibration calL W BL).CapacityChild li)
variable (rc : (right.arithmeticCalibration calR W BR).CapacityChild ri)

/-- The row profile is a single original factor. In particular a
constant extracted from a whole column is never raised to a slot count. -/
theorem commonEnvelope_le_separate (cap : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (hleft : kLeft ≤ cap) (hright : kRight ≤ cap)
    (hcommonL : ∀ i ∈ Finset.univ \ W.leftAtoms.keep,
      W.leftAtoms.annulus i * W.leftAtoms.profile i ≤ B)
    (hcommonR : ∀ i ∈ Finset.univ \ W.rightAtoms.keep,
      W.rightAtoms.annulus i * W.rightAtoms.profile i ≤ B) :
    W.commonEnvelope ≤ W.profileBound * B ^ cap := by
  have hl : W.leftAtoms.envelope ≤ B ^ cap :=
    selected_product_le _ _ B cap hB
      (by simpa only [Fintype.card_fin] using hleft)
      (fun i _ => mul_nonneg (W.leftAtoms.annulus_nonneg i)
        (W.leftAtoms.profile_nonneg i)) hcommonL
  have hr : W.rightAtoms.envelope ≤ B ^ cap :=
    selected_product_le _ _ B cap hB
      (by simpa only [Fintype.card_fin] using hright)
      (fun i _ => mul_nonneg (W.rightAtoms.annulus_nonneg i)
        (W.rightAtoms.profile_nonneg i)) hcommonR
  have h := mul_le_mul_of_nonneg_left
    (sqrt_pair_le (pow_nonneg (zero_le_one.trans hB) cap) hl hr)
    W.profileBound_nonneg
  simpa only [ActualSecondRowMass.commonEnvelope, mul_assoc] using h

/-- A pointwise original-atom estimate for the same selected children.
The original row-profile cost occurs exactly once. -/
theorem pairEnvelope_mul_common_le_separate
    (boundsL : Fin left.source.allocation.keep.card → ℝ)
    (boundsR : Fin right.source.allocation.keep.card → ℝ)
    (cap : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (hleft : k ≤ cap) (hright : l ≤ cap)
    (hcommonLeft : kLeft ≤ cap) (hcommonRight : kRight ≤ cap)
    (hcommonL : ∀ i ∈ Finset.univ \ W.leftAtoms.keep,
      W.leftAtoms.annulus i * W.leftAtoms.profile i ≤ B)
    (hcommonR : ∀ i ∈ Finset.univ \ W.rightAtoms.keep,
      W.rightAtoms.annulus i * W.rightAtoms.profile i ≤ B)
    (hfrozenL : ∀ i ∈ Finset.univ \ left.source.allocation.keep,
      BL.annulus i * BL.profile i ≤ B)
    (hfrozenR : ∀ i ∈ Finset.univ \ right.source.allocation.keep,
      BR.annulus i * BR.profile i ≤ B)
    (hBL : ∀ i, 0 ≤ boundsL i) (hBR : ∀ i, 0 ≤ boundsR i)
    (hremovedL : ∀ i, boundsL i ≤ B) (hremovedR : ∀ i, boundsR i ≤ B) :
    actualCapacityPairEnvelope left right calL calR W BL BR lc rc boundsL boundsR *
        W.commonEnvelope ≤
      (W.originalFiber : ℝ) * W.profileBound * B ^ (3 * cap) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hfL : BL.envelope ≤ B ^ cap :=
    selected_product_le _ _ B cap hB
      (by simpa only [Fintype.card_fin] using hleft)
      (fun i _ => mul_nonneg (BL.annulus_nonneg i) (BL.profile_nonneg i)) hfrozenL
  have hfR : BR.envelope ≤ B ^ cap :=
    selected_product_le _ _ B cap hB
      (by simpa only [Fintype.card_fin] using hright)
      (fun i _ => mul_nonneg (BR.annulus_nonneg i) (BR.profile_nonneg i)) hfrozenR
  have hkL : left.source.allocation.keep.card ≤ cap :=
    (Finset.card_le_univ _).trans (by simpa only [Fintype.card_fin] using hleft)
  have hkR : right.source.allocation.keep.card ≤ cap :=
    (Finset.card_le_univ _).trans (by simpa only [Fintype.card_fin] using hright)
  have hrL : (∏ i ∈ lc.removed, boundsL i) ≤ B ^ cap :=
    selected_product_le _ _ B cap hB
      (by simpa only [Fintype.card_fin] using hkL)
      (fun i _ => hBL i) (fun i _ => hremovedL i)
  have hrR : (∏ i ∈ rc.removed, boundsR i) ≤ B ^ cap :=
    selected_product_le _ _ B cap hB
      (by simpa only [Fintype.card_fin] using hkR)
      (fun i _ => hBR i) (fun i _ => hremovedR i)
  have hp := mul_le_mul
    (sqrt_pair_le (pow_nonneg hB0 cap) hfL hfR)
    (sqrt_pair_le (pow_nonneg hB0 cap) hrL hrR)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (pow_nonneg hB0 cap)
  have hpair :
      actualCapacityPairEnvelope left right calL calR W BL BR lc rc boundsL boundsR ≤
        (W.originalFiber : ℝ) * (B ^ cap * B ^ cap) := by
    apply (le_of_eq ?_).trans
      (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg W.originalFiber))
    unfold actualCapacityPairEnvelope
    ring
  have h := mul_le_mul hpair
    (commonEnvelope_le_separate W cap B hB hcommonLeft hcommonRight hcommonL hcommonR)
    W.commonEnvelope_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (pow_nonneg hB0 _) (pow_nonneg hB0 _)))
  apply h.trans_eq
  rw [show 3 * cap = cap + cap + cap by omega, pow_add, pow_add]
  ring

/-- The actual full-kappa producer uses bounds equal to one. Removed
slots then have no residual constant, so only two groups of original
prime occurrences remain in this cost. -/
theorem pairEnvelope_mul_common_le_one
    (cap : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (hleft : k ≤ cap) (hright : l ≤ cap)
    (hcommonLeft : kLeft ≤ cap) (hcommonRight : kRight ≤ cap)
    (hcommonL : ∀ i ∈ Finset.univ \ W.leftAtoms.keep,
      W.leftAtoms.annulus i * W.leftAtoms.profile i ≤ B)
    (hcommonR : ∀ i ∈ Finset.univ \ W.rightAtoms.keep,
      W.rightAtoms.annulus i * W.rightAtoms.profile i ≤ B)
    (hfrozenL : ∀ i ∈ Finset.univ \ left.source.allocation.keep,
      BL.annulus i * BL.profile i ≤ B)
    (hfrozenR : ∀ i ∈ Finset.univ \ right.source.allocation.keep,
      BR.annulus i * BR.profile i ≤ B) :
    actualCapacityPairEnvelope left right calL calR W BL BR lc rc
        (fun _ => 1) (fun _ => 1) * W.commonEnvelope ≤
      (W.originalFiber : ℝ) * W.profileBound * B ^ (2 * cap) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hfL : BL.envelope ≤ B ^ cap :=
    selected_product_le _ _ B cap hB
      (by simpa only [Fintype.card_fin] using hleft)
      (fun i _ => mul_nonneg (BL.annulus_nonneg i) (BL.profile_nonneg i)) hfrozenL
  have hfR : BR.envelope ≤ B ^ cap :=
    selected_product_le _ _ B cap hB
      (by simpa only [Fintype.card_fin] using hright)
      (fun i _ => mul_nonneg (BR.annulus_nonneg i) (BR.profile_nonneg i)) hfrozenR
  have hpair :
      actualCapacityPairEnvelope left right calL calR W BL BR lc rc
          (fun _ => 1) (fun _ => 1) ≤ (W.originalFiber : ℝ) * B ^ cap := by
    have h := mul_le_mul_of_nonneg_left
      (sqrt_pair_le (pow_nonneg hB0 cap) hfL hfR) (Nat.cast_nonneg W.originalFiber)
    simpa only [actualCapacityPairEnvelope, Finset.prod_const_one,
      Real.sqrt_one, mul_one, mul_assoc] using h
  have h := mul_le_mul hpair
    (commonEnvelope_le_separate W cap B hB hcommonLeft hcommonRight hcommonL hcommonR)
    W.commonEnvelope_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hB0 _))
  apply h.trans_eq
  rw [show 2 * cap = cap + cap by omega, pow_add]
  ring

end HeckeSkeleton.Moments.EngineStep.CanonicalSeparateAtomMass

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSeparateAtomMass.commonEnvelope_le_separate
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSeparateAtomMass.pairEnvelope_mul_common_le_separate
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSeparateAtomMass.pairEnvelope_mul_common_le_one
