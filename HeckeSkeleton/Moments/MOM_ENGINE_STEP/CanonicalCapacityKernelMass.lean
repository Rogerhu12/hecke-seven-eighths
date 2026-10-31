import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildMassBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedFourierChildren

/-!
# The mass of the actual arithmetically calibrated child kernel

The calibration and children are precisely those of `ActualChildMass`.
In particular the common extraction envelope is retained.  Its bound
is proved from the individual original annulus and profile bounds,
together with the original row profile bound.  The same argument
counts the actual frozen allocation factors and the actual removed
slots.  No bound for a row energy, child energy or total mass is an input.

The positive kernel uses both original Fourier measures and the exact
two pre-removal slot degrees.  A fixed finite set of original Schwartz
seminorms is chosen from weighted Fourier L1 before any moving data.
The outside scalar is left literal, so that the first Gauss factor,
both original phase/Mobius factors and the one pool average can be
attached by the actual finite-leaf construction.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalCapacityKernelMass

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments CommonSupportMass

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

section FourierChoice

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- This control is constructed below from the proved weighted Fourier
L1 theorem; it is not supplied by the producer. -/
structure FourierData (cap J₁ J₂ : ℕ) where
  leftSeminorms : Finset (ℕ × ℕ)
  rightSeminorms : Finset (ℕ × ℕ)
  constant : ℝ
  constant_pos : 0 < constant
  mass : ∀ (n₁ n₂ : ℕ), n₁ ≤ cap → n₂ ≤ cap →
    ∀ (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ)) (B₁ B₂ : ℝ), 0 ≤ B₁ → 0 ≤ B₂ →
      IsFiniteMeasure (normalizedPairMeasure F₁ F₂ n₁ n₂ B₁ B₂ J₁ J₂) ∧
      (normalizedPairMeasure F₁ F₂ n₁ n₂ B₁ B₂ J₁ J₂).real Set.univ ≤
        ((1 + B₁) ^ (cap + 2) * (1 + B₂) ^ (cap + 2)) * constant *
          leftSeminorms.sup (schwartzSeminormFamily ℝ U ℂ) F₁ *
            rightSeminorms.sup (schwartzSeminormFamily ℝ E ℂ) F₂

/-- The only parameters of this choice are the original dimensions,
fixed slot cap and fixed Fourier orders. -/
def fourierData (cap J₁ J₂ : ℕ) : FourierData (U := U) (E := E) cap J₁ J₂ := by
  have h : Nonempty (FourierData (U := U) (E := E) cap J₁ J₂) := by
    obtain ⟨s₁, s₂, C, hC, hmass⟩ :=
      normalizedPairMeasure_uniform_mass_upto (V := U) (E := E) cap J₁ J₂
    exact ⟨⟨s₁, s₂, C, hC, hmass⟩⟩
  exact Classical.choice h

end FourierChoice

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [IsPrincipalIdealRing A.R]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {ω ψ : HeckeCharacter F}
variable {k l kLeft kRight : ℕ}
variable (left : SecondSideFrame (V := V) C R Ray .left k)
variable (right : SecondSideFrame (V := V) C R Ray .right l)
variable (calL : left.source.Calibration (σ := σ) ω ψ)
variable (calR : right.source.Calibration (σ := σ) ω ψ)
variable (W : ActualSecondRowMass R C kLeft kRight)
variable (BL : left.source.FrozenAtomBounds) (BR : right.source.FrozenAtomBounds)

local notation "LC" => left.arithmeticCalibration calL W BL
local notation "RC" => right.arithmeticCalibration calR W BR

variable {li : (left.arithmeticCalibration calL W BL).CapacityInput} {ri : (right.arithmeticCalibration calR W BR).CapacityInput}
variable (lc : (left.arithmeticCalibration calL W BL).CapacityChild li) (rc : (right.arithmeticCalibration calR W BR).CapacityChild ri)
variable (boundsL : Fin left.source.allocation.keep.card → ℝ)
variable (boundsR : Fin right.source.allocation.keep.card → ℝ)

/-- Only original individual atom windows and original slot counts
occur here. The selected frozen/removed sets are not enlarged. -/
structure OriginalAtomWindow (cap : ℕ) (B : ℝ) where
  left_count : k ≤ cap
  right_count : l ≤ cap
  common_left_count : kLeft ≤ cap
  common_right_count : kRight ≤ cap
  row_profile : W.profileBound ≤ B
  common_left : ∀ i ∈ Finset.univ \ W.leftAtoms.keep,
    W.leftAtoms.annulus i * W.leftAtoms.profile i ≤ B
  common_right : ∀ i ∈ Finset.univ \ W.rightAtoms.keep,
    W.rightAtoms.annulus i * W.rightAtoms.profile i ≤ B
  frozen_left : ∀ i ∈ Finset.univ \ left.source.allocation.keep,
    BL.annulus i * BL.profile i ≤ B
  frozen_right : ∀ i ∈ Finset.univ \ right.source.allocation.keep,
    BR.annulus i * BR.profile i ≤ B
  removed_left : ∀ i, boundsL i ≤ B
  removed_right : ∀ i, boundsR i ≤ B

namespace OriginalAtomWindow

variable {left right W BL BR boundsL boundsR}
variable {cap : ℕ} {B : ℝ}
variable (P : OriginalAtomWindow left right W BL BR boundsL boundsR cap B)

theorem live_left_count : left.source.allocation.keep.card ≤ cap := by
  calc
    _ ≤ Fintype.card (Fin k) := Finset.card_le_univ _
    _ = k := Fintype.card_fin k
    _ ≤ cap := P.left_count

theorem live_right_count : right.source.allocation.keep.card ≤ cap := by
  calc
    _ ≤ Fintype.card (Fin l) := Finset.card_le_univ _
    _ = l := Fintype.card_fin l
    _ ≤ cap := P.right_count

/-- The common extraction amplitude is paid from its actual four
plain/prime dictionaries and the original row profile. -/
theorem commonEnvelope_le (hB : 1 ≤ B) : W.commonEnvelope ≤ B ^ (cap + 1) := by
  have hBL : W.leftAtoms.envelope ≤ B ^ cap :=
    selected_product_le _ _ B cap hB
      (by simpa only [Fintype.card_fin] using P.common_left_count)
      (fun i _ => mul_nonneg (W.leftAtoms.annulus_nonneg i) (W.leftAtoms.profile_nonneg i))
      P.common_left
  have hBR : W.rightAtoms.envelope ≤ B ^ cap :=
    selected_product_le _ _ B cap hB
      (by simpa only [Fintype.card_fin] using P.common_right_count)
      (fun i _ => mul_nonneg (W.rightAtoms.annulus_nonneg i) (W.rightAtoms.profile_nonneg i))
      P.common_right
  have hp := sqrt_pair_le (pow_nonneg (zero_le_one.trans hB) cap) hBL hBR
  have h := mul_le_mul P.row_profile hp
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (zero_le_one.trans hB)
  change W.profileBound * Real.sqrt W.leftAtoms.envelope * Real.sqrt W.rightAtoms.envelope ≤ _
  calc
    _ = W.profileBound * (Real.sqrt W.leftAtoms.envelope * Real.sqrt W.rightAtoms.envelope) := by ring
    _ ≤ B * B ^ cap := h
    _ = B ^ (cap + 1) := by rw [pow_succ]; ring

/-- Every square root of an original frozen product and of an actual
deleted product is charged once. The complete common envelope remains. -/
theorem pairEnvelope_mul_common_le (hB : 1 ≤ B)
    (hBL : ∀ i, 0 ≤ boundsL i) (hBR : ∀ i, 0 ≤ boundsR i) :
    actualCapacityPairEnvelope left right calL calR W BL BR lc rc boundsL boundsR *
        W.commonEnvelope ≤ (W.originalFiber : ℝ) * B ^ (3 * cap + 1) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hfL : BL.envelope ≤ B ^ cap :=
    selected_product_le _ _ B cap hB
      (by simpa only [Fintype.card_fin] using P.left_count)
      (fun i _ => mul_nonneg (BL.annulus_nonneg i) (BL.profile_nonneg i)) P.frozen_left
  have hfR : BR.envelope ≤ B ^ cap :=
    selected_product_le _ _ B cap hB
      (by simpa only [Fintype.card_fin] using P.right_count)
      (fun i _ => mul_nonneg (BR.annulus_nonneg i) (BR.profile_nonneg i)) P.frozen_right
  have hrL : (∏ i ∈ lc.removed, boundsL i) ≤ B ^ cap :=
    selected_product_le _ _ B cap hB
      (by simpa only [Fintype.card_fin] using P.live_left_count)
      (fun i _ => hBL i) (fun i _ => P.removed_left i)
  have hrR : (∏ i ∈ rc.removed, boundsR i) ≤ B ^ cap :=
    selected_product_le _ _ B cap hB
      (by simpa only [Fintype.card_fin] using P.live_right_count)
      (fun i _ => hBR i) (fun i _ => P.removed_right i)
  have hf := sqrt_pair_le (pow_nonneg hB0 cap) hfL hfR
  have hr := sqrt_pair_le (pow_nonneg hB0 cap) hrL hrR
  have hp := mul_le_mul hf hr
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (pow_nonneg hB0 cap)
  have hp' := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg W.originalFiber)
  have hfinal := mul_le_mul hp' (P.commonEnvelope_le hB) W.commonEnvelope_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (pow_nonneg hB0 _) (pow_nonneg hB0 _)))
  calc
    _ = ((W.originalFiber : ℝ) *
        ((Real.sqrt BL.envelope * Real.sqrt BR.envelope) *
          (Real.sqrt (∏ i ∈ lc.removed, boundsL i) *
            Real.sqrt (∏ i ∈ rc.removed, boundsR i)))) * W.commonEnvelope := by
      unfold actualCapacityPairEnvelope
      ring
    _ ≤ ((W.originalFiber : ℝ) * (B ^ cap * B ^ cap)) * B ^ (cap + 1) := hfinal
    _ = (W.originalFiber : ℝ) * B ^ (3 * cap + 1) := by
      rw [mul_assoc, ← pow_add, ← pow_add]
      congr 2
      omega

end OriginalAtomWindow

theorem pairWeight_nonneg (Z parentWidth : ℝ) (hZ : 0 < Z) :
    0 ≤ actualCapacityPairWeight left right calL calR W BL BR lc rc boundsL boundsR Z parentWidth := by
  unfold actualCapacityPairWeight
  exact div_nonneg
    (mul_nonneg (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) (Real.rpow_nonneg hZ.le _))
    (Real.rpow_nonneg hZ.le _)

/-- Original length windows cancel the original first allowance.
The common profile envelope remains in the bound at this stage. -/
theorem pairWeight_relative_allowance
    (Z : ℝ) (hZ : 1 < Z) (a₀ q wo w krow g ell parentWidth remaining : ℝ)
    (hBL : ∀ i, 0 ≤ boundsL i) (hBR : ∀ i, 0 ≤ boundsR i)
    (hdiv : left.source.allocation.divisor = right.source.allocation.divisor)
    (LL : ActualCapacityNormLengths li Z a₀ q wo w krow g ell
      W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val)
    (LR : ActualCapacityNormLengths ri Z a₀ q wo w krow g ell
      W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val)
    (NL : left.OriginalScaleWindow Z a₀) (NR : right.OriginalScaleWindow Z a₀)
    (hrow : Z ^ (-krow - g) ≤
      W.radius.val * (sIntegerElementNorm F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
        (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) W.mask)).val)
    (hremaining : a₀ + q + w + (LL.slack + LR.slack) / 2 + wo + ell - parentWidth ≤ remaining) :
    actualCapacityPairWeight left right calL calR W BL BR lc rc boundsL boundsR Z parentWidth ≤
      (actualCapacityPairEnvelope left right calL calR W BL BR lc rc boundsL boundsR *
        W.commonEnvelope * orbitalFieldFactor F) * Z ^ remaining /
        ((Ideal.absNorm left.source.allocation.divisor : ℝ) *
          (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ)) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have h := actual_capacity_pair_weight_le left right calL calR W BL BR lc rc boundsL boundsR
    Z hZ a₀ q wo w krow g ell parentWidth hBL hBR hdiv LL LR NL NR hrow
  have he : Z ^ (a₀ + q + w + (LL.slack + LR.slack) / 2) * Z ^ wo * Z ^ ell / Z ^ parentWidth =
      Z ^ (a₀ + q + w + (LL.slack + LR.slack) / 2 + wo + ell - parentWidth) := by
    rw [← Real.rpow_add hz, ← Real.rpow_add hz, ← Real.rpow_sub hz]
  have hc : 0 ≤ actualCapacityPairEnvelope left right calL calR W BL BR lc rc boundsL boundsR *
      W.commonEnvelope * orbitalFieldFactor F :=
    mul_nonneg
      (mul_nonneg (actualCapacityPairEnvelope_nonneg left right calL calR W BL BR lc rc boundsL boundsR)
        W.commonEnvelope_nonneg) (orbitalFieldFactor_nonneg F)
  apply h.trans
  calc
    _ = (actualCapacityPairEnvelope left right calL calR W BL BR lc rc boundsL boundsR *
        W.commonEnvelope * orbitalFieldFactor F) *
        (Z ^ (a₀ + q + w + (LL.slack + LR.slack) / 2) * Z ^ wo * Z ^ ell / Z ^ parentWidth) /
          ((Ideal.absNorm left.source.allocation.divisor : ℝ) *
            (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [he]
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le hremaining) hc)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

section Kernel

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- This is a measure attached to the already constructed children.
Only the upper bound will replace their exact pre-removal degrees by a cap. -/
def kernel (outer Z parentWidth : ℝ) (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ))
    (B₁ B₂ : ℝ) (J₁ J₂ : ℕ) : Measure (U × E) :=
  ENNReal.ofReal (outer *
    actualCapacityPairWeight left right calL calR W BL BR lc rc boundsL boundsR Z parentWidth) •
      normalizedPairMeasure F₁ F₂ left.source.allocation.keep.card right.source.allocation.keep.card
        B₁ B₂ J₁ J₂

theorem kernel_mass (outer Z parentWidth : ℝ) (houter : 0 ≤ outer) (hZ : 0 < Z)
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ)) (B₁ B₂ : ℝ) (J₁ J₂ : ℕ) :
    (kernel left right calL calR W BL BR lc rc boundsL boundsR outer Z parentWidth
      F₁ F₂ B₁ B₂ J₁ J₂).real Set.univ =
      outer * actualCapacityPairWeight left right calL calR W BL BR lc rc boundsL boundsR Z parentWidth *
        (normalizedPairMeasure F₁ F₂ left.source.allocation.keep.card right.source.allocation.keep.card
          B₁ B₂ J₁ J₂).real Set.univ := by
  rw [kernel, measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal
    (mul_nonneg houter (pairWeight_nonneg left right calL calR W BL BR lc rc boundsL boundsR Z parentWidth hZ))]

/-- Exact mass before the Fourier L1 estimate. Both original measures,
both source slot counts and the actual normalization scalar are visible. -/
theorem kernel_mass_original_integral
    (outer Z parentWidth : ℝ) (houter : 0 ≤ outer) (hZ : 0 < Z)
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ)) (B₁ B₂ : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (J₁ J₂ : ℕ) :
    (kernel left right calL calR W BL BR lc rc boundsL boundsR outer Z parentWidth
      F₁ F₂ B₁ B₂ J₁ J₂).real Set.univ =
      outer * actualCapacityPairWeight left right calL calR W BL BR lc rc boundsL boundsR Z parentWidth *
        ∫ z, canonicalProfileAmplitude B₁ J₁ J₂ z ^ (left.source.allocation.keep.card + 2) *
          canonicalProfileAmplitude B₂ J₁ J₂ z ^ (right.source.allocation.keep.card + 2)
            ∂nestedFourierMeasure F₁ F₂ := by
  rw [kernel_mass left right calL calR W BL BR lc rc boundsL boundsR outer Z parentWidth houter hZ]
  simpa only [normalizedPairMeasure, canonicalPairEnvelope] using
    congrArg (fun x : ℝ => outer *
      actualCapacityPairWeight left right calL calR W BL BR lc rc boundsL boundsR Z parentWidth * x)
      (weightedNestedFourierMeasure_mass_eq F₁ F₂ _
        (canonicalPairEnvelope_measurable _ _ B₁ B₂ J₁ J₂)
        (canonicalPairEnvelope_nonneg _ _ B₁ B₂ hB₁ hB₂ J₁ J₂))

/-- The full analytic/arithmetic bound is proved from the original
single-profile windows. In particular the common frozen profile
envelope is neither omitted nor asserted to be one. -/
theorem kernel_mass_le
    (cap J₁ J₂ : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (P : OriginalAtomWindow left right W BL BR boundsL boundsR cap B)
    (outer Z parentWidth remaining a₀ q wo w krow g ell : ℝ)
    (houter : 0 ≤ outer) (hZ : 1 < Z)
    (hBL : ∀ i, 0 ≤ boundsL i) (hBR : ∀ i, 0 ≤ boundsR i)
    (hdiv : left.source.allocation.divisor = right.source.allocation.divisor)
    (LL : ActualCapacityNormLengths li Z a₀ q wo w krow g ell
      W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val)
    (LR : ActualCapacityNormLengths ri Z a₀ q wo w krow g ell
      W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val)
    (NL : left.OriginalScaleWindow Z a₀) (NR : right.OriginalScaleWindow Z a₀)
    (hrow : Z ^ (-krow - g) ≤
      W.radius.val * (sIntegerElementNorm F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
        (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) W.mask)).val)
    (hremaining : a₀ + q + w + (LL.slack + LR.slack) / 2 + wo + ell - parentWidth ≤ remaining)
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ)) (B₁ B₂ : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hB₁B : B₁ ≤ B) (hB₂B : B₂ ≤ B)
    (kernelBound₁ kernelBound₂ : ℝ)
    (hkernel₁ : (fourierData (U := U) (E := E) cap J₁ J₂).leftSeminorms.sup
      (schwartzSeminormFamily ℝ U ℂ) F₁ ≤ kernelBound₁)
    (hkernel₂ : (fourierData (U := U) (E := E) cap J₁ J₂).rightSeminorms.sup
      (schwartzSeminormFamily ℝ E ℂ) F₂ ≤ kernelBound₂) :
    IsFiniteMeasure (kernel left right calL calR W BL BR lc rc boundsL boundsR
      outer Z parentWidth F₁ F₂ B₁ B₂ J₁ J₂) ∧
    (kernel left right calL calR W BL BR lc rc boundsL boundsR
      outer Z parentWidth F₁ F₂ B₁ B₂ J₁ J₂).real Set.univ ≤
      outer * ((W.originalFiber : ℝ) * B ^ (3 * cap + 1) * orbitalFieldFactor F) * Z ^ remaining /
        ((Ideal.absNorm left.source.allocation.divisor : ℝ) *
          (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ)) *
        ((1 + B) ^ (cap + 2) * (1 + B) ^ (cap + 2)) *
        (fourierData (U := U) (E := E) cap J₁ J₂).constant * kernelBound₁ * kernelBound₂ := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  let D := fourierData (U := U) (E := E) cap J₁ J₂
  have hf := D.mass left.source.allocation.keep.card right.source.allocation.keep.card
    P.live_left_count P.live_right_count F₁ F₂ B₁ B₂ hB₁ hB₂
  haveI := hf.1
  refine ⟨by unfold kernel; infer_instance, ?_⟩
  have hk₁ : 0 ≤ kernelBound₁ := (apply_nonneg _ F₁).trans hkernel₁
  have hk₂ : 0 ≤ kernelBound₂ := (apply_nonneg _ F₂).trans hkernel₂
  have hamp : (1 + B₁) ^ (cap + 2) * (1 + B₂) ^ (cap + 2) ≤
      (1 + B) ^ (cap + 2) * (1 + B) ^ (cap + 2) :=
    mul_le_mul
      (pow_le_pow_left₀ (by linarith) (by linarith) _)
      (pow_le_pow_left₀ (by linarith) (by linarith) _)
      (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)
  have hfc := mul_le_mul_of_nonneg_right hamp D.constant_pos.le
  have hfl := mul_le_mul hfc hkernel₁ (apply_nonneg _ F₁)
    (mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)) D.constant_pos.le)
  have hfr := mul_le_mul hfl hkernel₂ (apply_nonneg _ F₂)
    (mul_nonneg
      (mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)) D.constant_pos.le) hk₁)
  have hfourier := hf.2.trans hfr
  have hs := pairWeight_relative_allowance left right calL calR W BL BR lc rc boundsL boundsR
    Z hZ a₀ q wo w krow g ell parentWidth remaining hBL hBR hdiv LL LR NL NR hrow hremaining
  have ha := OriginalAtomWindow.pairEnvelope_mul_common_le
    (calL := calL) (calR := calR) (lc := lc) (rc := rc) P hB hBL hBR
  have hs' := hs.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ha (orbitalFieldFactor_nonneg F)) (Real.rpow_nonneg hz.le _))
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  have hout := mul_le_mul_of_nonneg_left hs' houter
  have hscalar0 : 0 ≤ outer *
      (((W.originalFiber : ℝ) * B ^ (3 * cap + 1) * orbitalFieldFactor F) * Z ^ remaining /
        ((Ideal.absNorm left.source.allocation.divisor : ℝ) *
          (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ))) :=
    mul_nonneg houter
      (div_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hB0 _))
          (orbitalFieldFactor_nonneg F)) (Real.rpow_nonneg hz.le _))
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  rw [kernel_mass left right calL calR W BL BR lc rc boundsL boundsR outer Z parentWidth houter hz]
  exact (mul_le_mul hout hfourier measureReal_nonneg hscalar0).trans_eq (by dsimp only [D]; ring)

end Kernel
end HeckeSkeleton.Moments.EngineStep.CanonicalCapacityKernelMass

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalCapacityKernelMass.OriginalAtomWindow.pairEnvelope_mul_common_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalCapacityKernelMass.pairWeight_relative_allowance
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalCapacityKernelMass.kernel_mass_le
