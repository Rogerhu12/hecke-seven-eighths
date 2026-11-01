import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalHybridMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityRelativeScalar

/-!
# The actual normalized pair pays its original two-divisor label

The children below are the already selected normalized children of the
arithmetic calibration. Their raw presentation has exactly the same
removed slots. The common extraction envelope, frozen allocation atoms
and deleted prime factors are all charged from their original individual
windows. The first source coefficient and its actual Cauchy allowance
then supply the first radical, while the second radical and the true
independent second divisor remain in the same coefficient.

The last theorem is a pointwise arithmetic estimate used before summing
the actual finite image carrier. It assumes only original profile,
length, ideal and atom identities. No child moment, final mass, fibre
count, or branch estimate is an input.
-/

noncomputable section
open HeckePort.IdealMobiusDivisorSum
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree UniqueFactorizationMonoid
open HeckeGeneral.Characters HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments CommonSupportMass

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
variable (IL : (left.arithmeticCalibration calL W BL).CapacityInput)
variable (IR : (right.arithmeticCalibration calR W BR).CapacityInput)
variable (AL AR : V → ℝ) (hAL : ∀ ξ, 0 < AL ξ) (hAR : ∀ ξ, 0 < AR ξ)
variable (boundsL : Fin left.source.allocation.keep.card → ℝ)
variable (boundsR : Fin right.source.allocation.keep.card → ℝ)
variable (hBL : ∀ i, 0 ≤ boundsL i) (hBR : ∀ i, 0 ≤ boundsR i)
variable (hfL : ∀ ξ i, IL.primeBound ξ i = AL ξ ^ 2 * boundsL i)
variable (hfR : ∀ ξ i, IR.primeBound ξ i = AR ξ ^ 2 * boundsR i)
variable (lc : (IL.normalized AL hAL boundsL hBL hfL).Child)
variable (rc : (IR.normalized AR hAR boundsR hBR hfR).Child)

local notation "rawL" => IL.rawChild AL hAL boundsL hBL hfL lc
local notation "rawR" => IR.rawChild AR hAR boundsR hBR hfR rc

/-- Every real parameter is an original length or scale. In particular
the allowance is the literal positive first normalization, without an
extra inverse first-divisor norm. -/
structure OriginalPairAllowanceWindow (Z firstNormalization remaining : ℝ) where
  a₀ : ℝ
  q : ℝ
  wo : ℝ
  w : ℝ
  krow : ℝ
  g : ℝ
  ell : ℝ
  boundary : ℝ
  normalization : firstNormalization = Z ^ (a₀ + q + w + boundary)
  divisor : left.source.allocation.divisor = right.source.allocation.divisor
  leftLengths : ActualCapacityNormLengths IL Z a₀ q wo w krow g ell
    W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val
  rightLengths : ActualCapacityNormLengths IR Z a₀ q wo w krow g ell
    W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val
  leftScale : left.OriginalScaleWindow Z a₀
  rightScale : right.OriginalScaleWindow Z a₀
  radius : Z ^ (-krow - g) ≤
    W.radius.val * (sIntegerElementNorm F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
      (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) W.mask)).val
  margin : (leftLengths.slack + rightLengths.slack) / 2 - boundary + wo + ell ≤ remaining

variable {Z firstNormalization remaining : ℝ}
variable (L : OriginalPairAllowanceWindow left right calL calR W BL BR IL IR
  Z firstNormalization remaining)

include L in
/-- The actual normalized pair divided by the original first allowance
has the two genuine second harmonic factors. The original common atoms
are paid alongside, rather than omitted from, the frozen and removed
products. This works for every retained slot count, including zero. -/
theorem normalized_pair_original_allowance_from_atoms
    (hZ : 1 < Z) (cap : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (atoms : CanonicalCapacityKernelMass.OriginalAtomWindow
      left right W BL BR boundsL boundsR cap B) :
    normalizedCapacityPairWeight lc rc left.normalizer right.normalizer Z 0 /
        firstNormalization ≤
      ((W.originalFiber : ℝ) * B ^ (3 * cap + 1) * orbitalFieldFactor F) *
        Z ^ remaining *
          (1 / (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ)) /
            (Ideal.absNorm left.source.allocation.divisor : ℝ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hraw := actual_capacity_pair_relative_allowance_le
    left right calL calR W BL BR rawL rawR boundsL boundsR
    Z hZ L.a₀ L.q L.wo L.w L.krow L.g L.ell 0 L.boundary firstNormalization
    L.normalization hBL hBR L.divisor L.leftLengths L.rightLengths
    L.leftScale L.rightScale L.radius
  have hatoms := CanonicalCapacityKernelMass.OriginalAtomWindow.pairEnvelope_mul_common_le
    (calL := calL) (calR := calR) (lc := rawL) (rc := rawR) atoms hB hBL hBR
  have hconstant : 0 ≤ (W.originalFiber : ℝ) * B ^ (3 * cap + 1) * orbitalFieldFactor F :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans hB) _))
      (orbitalFieldFactor_nonneg F)
  have hscalar :
      actualCapacityPairEnvelope left right calL calR W BL BR rawL rawR boundsL boundsR *
        W.commonEnvelope * orbitalFieldFactor F *
        Z ^ ((L.leftLengths.slack + L.rightLengths.slack) / 2 - L.boundary) *
          Z ^ L.wo * Z ^ L.ell / Z ^ (0 : ℝ) ≤
        ((W.originalFiber : ℝ) * B ^ (3 * cap + 1) * orbitalFieldFactor F) * Z ^ remaining := by
    calc
      _ = (actualCapacityPairEnvelope left right calL calR W BL BR rawL rawR boundsL boundsR *
          W.commonEnvelope * orbitalFieldFactor F) *
            Z ^ ((L.leftLengths.slack + L.rightLengths.slack) / 2 - L.boundary + L.wo + L.ell) := by
        rw [Real.rpow_zero, div_one, Real.rpow_add hz, Real.rpow_add hz]
        ring
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_right hatoms (orbitalFieldFactor_nonneg F))
        (Real.rpow_le_rpow_of_exponent_le hZ.le L.margin)
        (Real.rpow_nonneg hz.le _) hconstant
  rw [normalized_pair_weight_eq_canonical left right calL calR W BL BR IL IR
    AL AR hAL hAR boundsL boundsR hBL hBR hfL hfR lc rc Z 0 hz]
  exact hraw.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hscalar (one_div_nonneg.mpr (Nat.cast_nonneg _)))
      (Nat.cast_nonneg _))

variable {branch : TwoDivisorCommonBranch (K := F)}
variable {Ray₁ Ray₂ : Type*} [CommGroup Ray₁] [Fintype Ray₁] [CommGroup Ray₂] [Fintype Ray₂]

include L in
/-- The full original scalar of the same normalized pair is bounded
by its original first-common/S/second-common/L/allocation index. Both
Möbius coefficients stay in the harmonic weight. The finite characters
are bounded only after their original coefficients have been retained.
The fibre and pool sums are performed separately on this same index. -/
theorem normalized_pair_original_index_weight
    (hZ : 1 < Z) (cap : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (atoms : CanonicalCapacityKernelMass.OriginalAtomWindow
      left right W BL BR boundsL boundsR cap B)
    (j : branch.Index)
    (hleft : W.leftIdeal = j.2.2.1.val.1.1)
    (hright : W.rightIdeal = j.2.2.1.val.1.2)
    (hdivisor : left.source.allocation.divisor = j.2.2.2.1.val)
    (parentWidth total rawProfile firstCost : ℝ)
    (hfirst : 0 ≤ firstCost)
    (hprofile : rawProfile ≤ firstCost * Z ^ (parentWidth - total))
    (hD : j.1.val.1.1 ≠ 0) (hE : j.1.val.1.2 ≠ 0)
    (hsupport : primeSupport j.1.val.1.1 = primeSupport j.1.val.1.2)
    (phase₁ : Ray₁ × Ray₁ → Circle) (χ₁ : (Ray₁ × Ray₁) →* Circle)
    (phase₂ : Ray₂ × Ray₂ → Circle) (χ₂ : (Ray₂ × Ray₂) →* Circle) :
    (firstOriginalAllowanceWeight Z parentWidth total rawProfile j.1.val.1.1 j.1.val.1.2 *
      ‖(moebius j.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
      ‖(moebius j.2.2.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₂ phase₂ χ₂‖) *
      (normalizedCapacityPairWeight lc rc left.normalizer right.normalizer Z 0 /
        firstNormalization) ≤
      firstCost * ((W.originalFiber : ℝ) * B ^ (3 * cap + 1) * orbitalFieldFactor F) *
        Z ^ remaining * branch.indexWeight j := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hN : 0 < firstNormalization := by
    rw [L.normalization]
    exact Real.rpow_pos_of_pos hz _
  have hsecond := normalized_pair_original_allowance_from_atoms
    left right calL calR W BL BR IL IR AL AR hAL hAR boundsL boundsR hBL hBR hfL hfR lc rc L
    hZ cap B hB atoms
  have hfirstWeight := firstOriginalAllowanceWeight_le_radical
    Z parentWidth total rawProfile firstCost hZ hfirst hprofile
    j.1.val.1.1 j.1.val.1.2 hD hE hsupport
  have hpair := mul_le_mul hfirstWeight hsecond
    (div_nonneg (normalizedCapacityPairWeight_nonneg lc rc
      left.normalizer right.normalizer Z 0 hz) hN.le)
    (div_nonneg hfirst (Nat.cast_nonneg _))
  have hcoeff :
      ‖(moebius j.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
        ‖(moebius j.2.2.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₂ phase₂ χ₂‖ ≤
      ‖(moebius j.2.1.val : ℂ)‖ * ‖(moebius j.2.2.2.1.val : ℂ)‖ := by
    have hc₁ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (fixed_phase_coefficient_norm Ray₁ phase₁ χ₁)
        (norm_nonneg (moebius j.2.1.val : ℂ)))
      (norm_nonneg (moebius j.2.2.2.1.val : ℂ))
    simpa only [mul_one] using mul_le_mul hc₁ (fixed_phase_coefficient_norm Ray₂ phase₂ χ₂)
      (norm_nonneg (fixedPhaseCoefficient Ray₂ phase₂ χ₂))
      (mul_nonneg (mul_nonneg (norm_nonneg (moebius j.2.1.val : ℂ)) zero_le_one)
        (norm_nonneg (moebius j.2.2.2.1.val : ℂ)))
  have hconstant : 0 ≤ (W.originalFiber : ℝ) * B ^ (3 * cap + 1) * orbitalFieldFactor F :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans hB) _))
      (orbitalFieldFactor_nonneg F)
  have hupper : 0 ≤ firstCost / (Ideal.absNorm (commonRadical j.1.val.1.1 j.1.val.1.2) : ℝ) *
      (((W.originalFiber : ℝ) * B ^ (3 * cap + 1) * orbitalFieldFactor F) * Z ^ remaining *
        (1 / (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ)) /
          (Ideal.absNorm left.source.allocation.divisor : ℝ)) :=
    mul_nonneg (div_nonneg hfirst (Nat.cast_nonneg _))
      (div_nonneg
        (mul_nonneg (mul_nonneg hconstant (Real.rpow_nonneg hz.le _))
          (one_div_nonneg.mpr (Nat.cast_nonneg _))) (Nat.cast_nonneg _))
  have h := mul_le_mul hpair hcoeff (by positivity) hupper
  simpa only [TwoDivisorCommonBranch.indexWeight, hleft, hright, hdivisor,
    div_eq_mul_inv, one_mul, mul_assoc, mul_left_comm, mul_comm] using h

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.normalized_pair_original_allowance_from_atoms
#print axioms HeckeSkeleton.Moments.EngineStep.normalized_pair_original_index_weight
