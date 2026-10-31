import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildMass

/-!
# The normalized weight of the same actual capacity children

The child cost is expanded from the canonical arithmetic calibration.
Original positive Gauss scales pay their separate normalization.
The original length fields imply the width-plus-allowance budget.
The genuine radius and local correlation then cancel to the second
common radical, while the independent second divisor remains visible.
The parent-width normalization is retained throughout.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments CommonSupportMass

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

namespace SecondSideFrame

variable {side : SecondColumnSide} {k : ℕ}
variable (f : SecondSideFrame (V := V) C R Ray side k)

/-- Each scale is the original single-factor Gauss normalization. -/
structure OriginalScaleWindow (Z a₀ : ℝ) where
  leftLength : ℝ
  rightLength : ℝ
  slotLength : Fin k → ℝ
  left_lower : Z ^ leftLength ≤ f.gaussScale₁
  right_lower : Z ^ rightLength ≤ f.gaussScale₂
  slot_lower : ∀ i, Z ^ slotLength i ≤ f.gaussSlotScale i
  degree : leftLength + rightLength + ∑ i, slotLength i = a₀

theorem OriginalScaleWindow.scale_lower {Z a₀ : ℝ}
    (W : f.OriginalScaleWindow Z a₀) (hZ : 0 < Z) :
    Z ^ a₀ ≤ f.normalizationScale := by
  have hp (S : Finset (Fin k)) :
      Z ^ (∑ i ∈ S, W.slotLength i) = ∏ i ∈ S, Z ^ W.slotLength i := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, Real.rpow_add hZ, ih]
  rw [← W.degree, Real.rpow_add hZ, Real.rpow_add hZ, hp Finset.univ]
  exact mul_le_mul
    (mul_le_mul W.left_lower W.right_lower (Real.rpow_nonneg hZ.le _) f.gaussScale₁_pos.le)
    (Finset.prod_le_prod₀ (fun _ _ => Real.rpow_nonneg hZ.le _) (fun i _ => W.slot_lower i))
    (Finset.prod_nonneg (fun _ _ => Real.rpow_nonneg hZ.le _))
    (mul_nonneg f.gaussScale₁_pos.le f.gaussScale₂_pos.le)

end SecondSideFrame

/-- All fields are literal original length identities. In particular no
bound for the resulting child weight is included. -/
structure ActualCapacityNormLengths
    {k : ℕ} {s : ActualAllocatedSource A V H k}
    {cal : s.Calibration (σ := σ) ω ψ} (input : cal.CapacityInput)
    (Z a₀ q wo w krow g ell : ℝ) (D E U N : Ideal (𝓞 F)) where
  base_eq : s.base = Z
  degree_eq : input.skeleton.A - input.skeleton.c - input.skeleton.w = a₀
  support_eq : input.skeleton.q + input.skeleton.R + input.skeleton.E = q
  moving_eq : input.skeleton.wo = wo
  removed_eq : input.skeleton.w = w
  row_eq : input.skeleton.Krow = krow
  enlargement_eq : input.skeleton.g = g
  gcd_eq : input.skeleton.g₂ = idealLogLength Z (gcd D E)
  unit_eq : input.skeleton.t₂ = idealLogLength Z U
  nonunit_eq : input.skeleton.V = idealLogLength Z N
  common_eq : input.b₂ = (idealLogLength Z D + idealLogLength Z E) / 2
  radical_eq : input.p₂ = idealLogLength Z (commonRadical D E)
  pool_eq : input.ell = ell

namespace ActualCapacityNormLengths

variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable {cal : s.Calibration (σ := σ) ω ψ} {input : cal.CapacityInput}
variable {Z a₀ q wo w krow g ell : ℝ} {D E U N : Ideal (𝓞 F)}
variable (L : ActualCapacityNormLengths input Z a₀ q wo w krow g ell D E U N)

def slack : ℝ :=
  input.boundary +
    (input.supportError + (input.rawClipError +
      (Real.log input.leftAnnulus + Real.log input.rightAnnulus) / Real.log Z) +
        input.widthError) / 6 +
      cal.parameters.κ * input.mesh + input.delta

theorem nominalWidth_eq :
    input.skeleton.nominalWidth = secondCommonChildWidth Z a₀ q wo krow g D E U N := by
  unfold NominalChildGeometry.nominalWidth NominalChildGeometry.nominalRow
    NominalChildGeometry.nominalSupport secondCommonChildWidth
  rw [L.degree_eq, L.support_eq, L.moving_eq, L.row_eq, L.enlargement_eq,
    L.gcd_eq, L.unit_eq, L.nonunit_eq]

theorem allowance_eq :
    input.exponent + input.delta = secondCommonChildAllowance Z w L.slack ell D E := by
  unfold ActualAllocatedSource.Calibration.CapacityInput.exponent slack
    secondCommonChildAllowance
  rw [L.base_eq, L.common_eq, L.radical_eq, L.removed_eq, L.pool_eq]
  ring

/-- This budget follows from the original nominal width and the actual
capacity output. The same removed slots and clipped parameters occur. -/
theorem child_budget (child : cal.CapacityChild input) :
    child.parameters.m + child.parameters.q + input.exponent ≤
      secondCommonChildWidth Z a₀ q wo krow g D E U N +
        secondCommonChildAllowance Z w L.slack ell D E := by
  have hw := input.actual_width
  have hc := child.width_eq
  change child.parameters.m + child.parameters.q = cal.parameters.m + cal.parameters.q at hc
  rw [L.nominalWidth_eq] at hw
  have ha := L.allowance_eq
  linarith

end ActualCapacityNormLengths

private theorem sqrt_rpow_half (Z : ℝ) (hZ : 0 < Z) (x : ℝ) :
    Real.sqrt (Z ^ x) = Z ^ (x / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ.le]
  congr 1
  ring

private theorem sqrt_canonical_cost (q E F B N Z d : ℝ)
    (hq : 0 ≤ q) (hE : 0 ≤ E) (hF : 0 ≤ F) (hB : 0 ≤ B)
    (hN : 0 ≤ N) (hZ : 0 < Z) :
    Real.sqrt ((q * (E / N) * F) * (B * Z ^ d)) =
      Real.sqrt q * Real.sqrt E * Real.sqrt F * Real.sqrt B * Z ^ (d / 2) / Real.sqrt N := by
  rw [Real.sqrt_mul (mul_nonneg (mul_nonneg hq (div_nonneg hE hN)) hF),
    Real.sqrt_mul (mul_nonneg hq (div_nonneg hE hN)),
    Real.sqrt_mul hq, Real.sqrt_mul hB, Real.sqrt_div hE, sqrt_rpow_half Z hZ]
  ring

private theorem canonical_pair_cost_identity
    (q EL ER F BL BR N NL NR Z dL dR mL mR parent : ℝ)
    (hq : 0 ≤ q) (hEL : 0 ≤ EL) (hER : 0 ≤ ER) (hF : 0 ≤ F)
    (hBL : 0 ≤ BL) (hBR : 0 ≤ BR) (hN : 0 ≤ N) (hZ : 0 < Z) :
    (Real.sqrt ((q * (EL / N) * F) * (BL * Z ^ dL)) *
      Real.sqrt ((q * (ER / N) * F) * (BR * Z ^ dR)) /
        (Real.sqrt NL * Real.sqrt NR)) * Z ^ ((mL + mR) / 2) / Z ^ parent =
      (F * Real.sqrt EL * Real.sqrt ER * Real.sqrt BL * Real.sqrt BR) /
        (N * Z ^ parent) *
      (q / (Real.sqrt NL * Real.sqrt NR) *
        Z ^ ((mL + mR + dL + dR) / 2)) := by
  rw [sqrt_canonical_cost q EL F BL N Z dL hq hEL hF hBL hN hZ,
    sqrt_canonical_cost q ER F BR N Z dR hq hER hF hBR hN hZ]
  have hq₂ : Real.sqrt q * Real.sqrt q = q := by nlinarith [Real.sq_sqrt hq]
  have hF₂ : Real.sqrt F * Real.sqrt F = F := by nlinarith [Real.sq_sqrt hF]
  have hN₂ : (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ = N⁻¹ := by
    rw [← mul_inv]
    congr 1
    nlinarith [Real.sq_sqrt hN]
  have hp : Z ^ (dL / 2) * Z ^ (dR / 2) * Z ^ ((mL + mR) / 2) =
      Z ^ ((mL + mR + dL + dR) / 2) := by
    rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
    congr 1
    ring
  simp only [div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (Real.sqrt q * Real.sqrt q) * (Real.sqrt F * Real.sqrt F) *
        (Real.sqrt EL * Real.sqrt ER * Real.sqrt BL * Real.sqrt BR) *
        ((Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹) *
        ((Real.sqrt NR)⁻¹ * (Real.sqrt NL)⁻¹) *
        (Z ^ (dL / 2) * Z ^ (dR / 2) * Z ^ ((mL + mR) / 2)) * (Z ^ parent)⁻¹ := by ring
    _ = _ := by rw [hq₂, hF₂, hN₂, hp]; ring

namespace ActualSecondRowMass

variable {kLeft kRight : ℕ} (W : ActualSecondRowMass R C kLeft kRight)

/-- The local bound is used only inside rowBound. The original radius
and extra original column scales pay the row and column exponents
separately; no pool average is inserted here. -/
theorem normalized_row_budget
    (Z : ℝ) (hZ : 1 < Z) (a₀ q wo w B krow g ell NL NR : ℝ)
    (hrow : Z ^ (-krow - g) ≤
      W.radius.val * (sIntegerElementNorm F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
        (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) W.mask)).val)
    (hcentral : Z ^ a₀ ≤ Real.sqrt NL * Real.sqrt NR) :
    W.rowBound / (Real.sqrt NL * Real.sqrt NR) *
        Z ^ (secondCommonChildWidth Z a₀ q wo krow g
            W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val +
          secondCommonChildAllowance Z w B ell W.leftIdeal W.rightIdeal) ≤
      W.commonEnvelope * (orbitalFieldFactor F * Z ^ (a₀ + q + w + B) * Z ^ wo * Z ^ ell /
        (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ)) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hs := second_source_normalized_scalar_bound Z hZ a₀ krow g NL NR
    W.radius W.mask hrow hcentral
  have hb := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hs W.correlationBound_nonneg)
      W.commonDenominator_nonneg)
    (Real.rpow_nonneg hz.le
      (secondCommonChildWidth Z a₀ q wo krow g
        W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val +
        secondCommonChildAllowance Z w B ell W.leftIdeal W.rightIdeal))
  have hD : W.leftIdeal ≠ 0 := (primePowerProduct R.primes R.leftMultiplicity).property.1
  have hE : W.rightIdeal ≠ 0 := (primePowerProduct R.primes R.rightMultiplicity).property.1
  have he := second_actual_scalar_budget_identity Z hZ (orbitalFieldFactor F)
    a₀ q wo w (B + ell) krow g 0 W.leftIdeal W.rightIdeal W.unitIdeal.val
    W.nonunitIdeal.val hD hE W.unitIdeal.property.1
  have hallow : secondCommonChildAllowance Z w (B + ell) 0 W.leftIdeal W.rightIdeal =
      secondCommonChildAllowance Z w B ell W.leftIdeal W.rightIdeal := by
    unfold secondCommonChildAllowance
    ring
  simp only [neg_zero, Real.rpow_zero, one_mul, hallow] at he
  have hnorm :
      ((orbitalFieldFactor F * Z ^ (krow + g - a₀)) * W.correlationBound /
        W.commonDenominator) *
        Z ^ (secondCommonChildWidth Z a₀ q wo krow g
          W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val +
          secondCommonChildAllowance Z w B ell W.leftIdeal W.rightIdeal) =
      orbitalFieldFactor F * Z ^ (a₀ + q + w + B) * Z ^ wo * Z ^ ell /
        (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ) := by
    unfold correlationBound commonDenominator
    rw [he]
    rw [show a₀ + q + wo + w + (B + ell) = (a₀ + q + w + B) + wo + ell by ring,
      Real.rpow_add hz, Real.rpow_add hz]
    ring
  calc
    _ = W.commonEnvelope *
        (((‖secondOrbitalScalar (K := F) (S := A.Sf) W.radius W.mask‖ /
          (Real.sqrt NL * Real.sqrt NR)) * W.correlationBound / W.commonDenominator) *
          Z ^ (secondCommonChildWidth Z a₀ q wo krow g
            W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val +
            secondCommonChildAllowance Z w B ell W.leftIdeal W.rightIdeal)) := by
      unfold rowBound
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb W.commonEnvelope_nonneg
    _ = _ := by rw [hnorm]

end ActualSecondRowMass

section Pair

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

/-- This is the literal weight multiplying the two normalized moments
of these same constructed children. -/
def actualCapacityPairWeight (Z parentWidth : ℝ) : ℝ :=
  (Real.sqrt (lc.envelopeFreeCost boundsL) * Real.sqrt (rc.envelopeFreeCost boundsR) /
      (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale)) *
    Z ^ ((lc.parameters.m + lc.parameters.q + (rc.parameters.m + rc.parameters.q)) / 2) /
      Z ^ parentWidth

def actualCapacityPairEnvelope : ℝ :=
  (W.originalFiber : ℝ) * Real.sqrt BL.envelope * Real.sqrt BR.envelope *
    Real.sqrt (∏ i ∈ lc.removed, boundsL i) *
    Real.sqrt (∏ i ∈ rc.removed, boundsR i)

theorem actualCapacityPairEnvelope_nonneg : 0 ≤
    actualCapacityPairEnvelope left right calL calR W BL BR lc rc boundsL boundsR := by
  unfold actualCapacityPairEnvelope
  positivity

/-- The parent normalization, both extra Gauss normalizers, the actual
removed-slot costs and the independent second divisor all occur once. -/
theorem actual_capacity_pair_weight_le
    (Z : ℝ) (hZ : 1 < Z) (a₀ q wo w krow g ell parentWidth : ℝ)
    (hBL : ∀ i, 0 ≤ boundsL i) (hBR : ∀ i, 0 ≤ boundsR i)
    (hdiv : left.source.allocation.divisor = right.source.allocation.divisor)
    (LL : ActualCapacityNormLengths li Z a₀ q wo w krow g ell
      W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val)
    (LR : ActualCapacityNormLengths ri Z a₀ q wo w krow g ell
      W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val)
    (NL : left.OriginalScaleWindow Z a₀) (NR : right.OriginalScaleWindow Z a₀)
    (hrow : Z ^ (-krow - g) ≤
      W.radius.val * (sIntegerElementNorm F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
        (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) W.mask)).val) :
    actualCapacityPairWeight left right calL calR W BL BR lc rc boundsL boundsR Z parentWidth ≤
      (actualCapacityPairEnvelope left right calL calR W BL BR lc rc boundsL boundsR /
        ((Ideal.absNorm left.source.allocation.divisor : ℝ) * Z ^ parentWidth)) *
      (W.commonEnvelope *
        (orbitalFieldFactor F * Z ^ (a₀ + q + w + (LL.slack + LR.slack) / 2) *
          Z ^ wo * Z ^ ell /
          (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ))) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hPL : 0 ≤ ∏ i ∈ lc.removed, boundsL i := Finset.prod_nonneg (fun i _ => hBL i)
  have hPR : 0 ≤ ∏ i ∈ rc.removed, boundsR i := Finset.prod_nonneg (fun i _ => hBR i)
  have hcentral := second_source_central_scale_lower Z hz a₀
    left.normalizationScale right.normalizationScale (NL.scale_lower hz) (NR.scale_lower hz)
  have hexp :
      (lc.parameters.m + lc.parameters.q + (rc.parameters.m + rc.parameters.q) +
        li.exponent + ri.exponent) / 2 ≤
      secondCommonChildWidth Z a₀ q wo krow g
        W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val +
        secondCommonChildAllowance Z w ((LL.slack + LR.slack) / 2) ell W.leftIdeal W.rightIdeal := by
    have hl := LL.child_budget lc
    have hr := LR.child_budget rc
    unfold secondCommonChildAllowance at *
    linarith
  have hbudget := W.normalized_row_budget Z hZ a₀ q wo w ((LL.slack + LR.slack) / 2)
    krow g ell left.normalizationScale right.normalizationScale hrow hcentral
  have hcoeff : 0 ≤ actualCapacityPairEnvelope left right calL calR W BL BR lc rc boundsL boundsR /
      ((Ideal.absNorm left.source.allocation.divisor : ℝ) * Z ^ parentWidth) :=
    div_nonneg (actualCapacityPairEnvelope_nonneg left right calL calR W BL BR lc rc boundsL boundsR)
      (mul_nonneg BL.divisorNorm_pos.le (Real.rpow_nonneg hz.le _))
  have hrowNonneg : 0 ≤ W.rowBound /
      (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale) :=
    div_nonneg W.rowBound_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  calc
    _ = (actualCapacityPairEnvelope left right calL calR W BL BR lc rc boundsL boundsR /
        ((Ideal.absNorm left.source.allocation.divisor : ℝ) * Z ^ parentWidth)) *
        (W.rowBound / (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale) *
          Z ^ ((lc.parameters.m + lc.parameters.q + (rc.parameters.m + rc.parameters.q) +
            li.exponent + ri.exponent) / 2)) := by
      unfold actualCapacityPairWeight actualCapacityPairEnvelope
      rw [left.arithmetic_child_cost calL W BL lc boundsL,
        right.arithmetic_child_cost calR W BR rc boundsR, LL.base_eq, LR.base_eq, ← hdiv]
      exact canonical_pair_cost_identity W.rowBound BL.envelope BR.envelope (W.originalFiber : ℝ)
        (∏ i ∈ lc.removed, boundsL i) (∏ i ∈ rc.removed, boundsR i)
        (Ideal.absNorm left.source.allocation.divisor : ℝ)
        left.normalizationScale right.normalizationScale Z li.exponent ri.exponent
        (lc.parameters.m + lc.parameters.q) (rc.parameters.m + rc.parameters.q) parentWidth
        W.rowBound_nonneg BL.envelope_nonneg BR.envelope_nonneg (Nat.cast_nonneg _) hPL hPR
        BL.divisorNorm_pos.le hz
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ.le hexp) hrowNonneg).trans hbudget) hcoeff

end Pair

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.OriginalScaleWindow.scale_lower
#print axioms HeckeSkeleton.Moments.EngineStep.ActualCapacityNormLengths.child_budget
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondRowMass.normalized_row_budget
#print axioms HeckeSkeleton.Moments.EngineStep.actual_capacity_pair_weight_le

