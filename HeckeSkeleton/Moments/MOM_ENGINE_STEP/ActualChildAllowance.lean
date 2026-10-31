import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildMassBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondAllowanceCancellation

/-!
# The actual capacity children pay the first allowance

The normalized weight is the weight of the same two children produced
by the actual arithmetic calibration.  The original extra Gauss
normalizers and the independent second divisor remain in that weight.
Dividing by the literal first Cauchy allowance cancels its complete
length exponent.  The remaining slack is computed from the two actual
capacity inputs; no branch-mass bound is assumed.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open CommonSupportMass

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

variable {li : LC.CapacityInput} {ri : RC.CapacityInput}
variable (lc : LC.CapacityChild li) (rc : RC.CapacityChild ri)
variable (boundsL : Fin left.source.allocation.keep.card → ℝ)
variable (boundsR : Fin right.source.allocation.keep.card → ℝ)

/-- The only premise about N is its raw original scale identity.
All bounds for the actual child weight are proved from the primitive
atom, radius and length fields by actual_capacity_pair_weight_le. -/
theorem actual_capacity_pair_relative_allowance_le
    (Z : ℝ) (hZ : 1 < Z) (a₀ q wo w krow g ell parentWidth B N : ℝ)
    (hN : N = Z ^ (a₀ + q + w + B))
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
    actualCapacityPairWeight left right calL calR W BL BR lc rc boundsL boundsR
        Z parentWidth / N ≤
      (actualCapacityPairEnvelope left right calL calR W BL BR lc rc boundsL boundsR *
        W.commonEnvelope * orbitalFieldFactor F *
        Z ^ ((LL.slack + LR.slack) / 2 - B) * Z ^ wo * Z ^ ell / Z ^ parentWidth) *
        (1 / (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ)) /
          (Ideal.absNorm left.source.allocation.divisor : ℝ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hNpos : 0 < N := by
    rw [hN]
    exact Real.rpow_pos_of_pos hz _
  have hcancel :
      Z ^ (a₀ + q + w + (LL.slack + LR.slack) / 2) / N =
        Z ^ ((LL.slack + LR.slack) / 2 - B) := by
    rw [hN, ← Real.rpow_sub hz]
    congr 1
    ring
  apply (div_le_div_of_nonneg_right
    (actual_capacity_pair_weight_le left right calL calR W BL BR lc rc boundsL boundsR
      Z hZ a₀ q wo w krow g ell parentWidth hBL hBR hdiv LL LR NL NR hrow)
    hNpos.le).trans_eq
  calc
    _ = (actualCapacityPairEnvelope left right calL calR W BL BR lc rc boundsL boundsR *
        W.commonEnvelope * orbitalFieldFactor F *
        (Z ^ (a₀ + q + w + (LL.slack + LR.slack) / 2) / N) *
        Z ^ wo * Z ^ ell / Z ^ parentWidth) *
        (1 / (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ)) /
          (Ideal.absNorm left.source.allocation.divisor : ℝ) := by ring
    _ = _ := by rw [hcancel]

/-- The left first allowance is the exact one supplied by the original
first normalization. There is no inverse first-divisor factor in N. -/
theorem actual_capacity_pair_first_left_allowance_le
    (Z : ℝ) (hZ : 1 < Z) (A₀ q wo w krow g ell parentWidth : ℝ)
    (D E : Ideal (𝓞 F))
    (hBL : ∀ i, 0 ≤ boundsL i) (hBR : ∀ i, 0 ≤ boundsR i)
    (hdiv : left.source.allocation.divisor = right.source.allocation.divisor)
    (LL : ActualCapacityNormLengths li Z (A₀ - idealLogLength Z D - w)
      q wo w krow g ell W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val)
    (LR : ActualCapacityNormLengths ri Z (A₀ - idealLogLength Z D - w)
      q wo w krow g ell W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val)
    (NL : left.OriginalScaleWindow Z (A₀ - idealLogLength Z D - w))
    (NR : right.OriginalScaleWindow Z (A₀ - idealLogLength Z D - w))
    (hrow : Z ^ (-krow - g) ≤
      W.radius.val * (sIntegerElementNorm F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
        (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) W.mask)).val) :
    actualCapacityPairWeight left right calL calR W BL BR lc rc boundsL boundsR
        Z parentWidth / firstLeftAllowance Z (A₀ + q) D E ≤
      (actualCapacityPairEnvelope left right calL calR W BL BR lc rc boundsL boundsR *
        W.commonEnvelope * orbitalFieldFactor F *
        Z ^ ((LL.slack + LR.slack) / 2 -
          firstAllowance (idealLogLength Z D) (idealLogLength Z E)
            (idealLogLength Z (firstActiveRadical D E))) *
        Z ^ wo * Z ^ ell / Z ^ parentWidth) *
        (1 / (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ)) /
          (Ideal.absNorm left.source.allocation.divisor : ℝ) :=
  actual_capacity_pair_relative_allowance_le left right calL calR W BL BR lc rc boundsL boundsR
    Z hZ (A₀ - idealLogLength Z D - w) q wo w krow g ell parentWidth
    (firstAllowance (idealLogLength Z D) (idealLogLength Z E)
      (idealLogLength Z (firstActiveRadical D E)))
    (firstLeftAllowance Z (A₀ + q) D E)
    (firstLeftAllowance_second_exponent Z A₀ q w D E)
    hBL hBR hdiv LL LR NL NR hrow

/-- The right first allowance uses the original right common length,
with the same complete actual-child and independent-divisor accounting. -/
theorem actual_capacity_pair_first_right_allowance_le
    (Z : ℝ) (hZ : 1 < Z) (A₀ q wo w krow g ell parentWidth : ℝ)
    (D E : Ideal (𝓞 F))
    (hBL : ∀ i, 0 ≤ boundsL i) (hBR : ∀ i, 0 ≤ boundsR i)
    (hdiv : left.source.allocation.divisor = right.source.allocation.divisor)
    (LL : ActualCapacityNormLengths li Z (A₀ - idealLogLength Z E - w)
      q wo w krow g ell W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val)
    (LR : ActualCapacityNormLengths ri Z (A₀ - idealLogLength Z E - w)
      q wo w krow g ell W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val)
    (NL : left.OriginalScaleWindow Z (A₀ - idealLogLength Z E - w))
    (NR : right.OriginalScaleWindow Z (A₀ - idealLogLength Z E - w))
    (hrow : Z ^ (-krow - g) ≤
      W.radius.val * (sIntegerElementNorm F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
        (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) W.mask)).val) :
    actualCapacityPairWeight left right calL calR W BL BR lc rc boundsL boundsR
        Z parentWidth / firstRightAllowance Z (A₀ + q) D E ≤
      (actualCapacityPairEnvelope left right calL calR W BL BR lc rc boundsL boundsR *
        W.commonEnvelope * orbitalFieldFactor F *
        Z ^ ((LL.slack + LR.slack) / 2 -
          firstAllowance (idealLogLength Z E) (idealLogLength Z D)
            (idealLogLength Z (firstActiveRadical D E))) *
        Z ^ wo * Z ^ ell / Z ^ parentWidth) *
        (1 / (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ)) /
          (Ideal.absNorm left.source.allocation.divisor : ℝ) :=
  actual_capacity_pair_relative_allowance_le left right calL calR W BL BR lc rc boundsL boundsR
    Z hZ (A₀ - idealLogLength Z E - w) q wo w krow g ell parentWidth
    (firstAllowance (idealLogLength Z E) (idealLogLength Z D)
      (idealLogLength Z (firstActiveRadical D E)))
    (firstRightAllowance Z (A₀ + q) D E)
    (firstRightAllowance_second_exponent Z A₀ q w D E)
    hBL hBR hdiv LL LR NL NR hrow

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_capacity_pair_relative_allowance_le
#print axioms HeckeSkeleton.Moments.EngineStep.actual_capacity_pair_first_left_allowance_le
#print axioms HeckeSkeleton.Moments.EngineStep.actual_capacity_pair_first_right_allowance_le

