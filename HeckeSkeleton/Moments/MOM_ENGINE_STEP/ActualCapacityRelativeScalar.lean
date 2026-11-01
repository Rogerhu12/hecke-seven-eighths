import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityCanonicalBridge
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityScalarMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstAllowanceNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteBranchIndex

/-!
# Actual child costs relative to the original first Cauchy allowance

The original first normalization is a positive real number, retained
in the denominator.  Its exact exponent cancels the complete second
source allowance.  The remaining costs are the genuine moving norm,
the one pool allowance, and the explicit clipping/mesh margin.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree UniqueFactorizationMonoid
open HeckeGeneral.Characters HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments CommonSupportMass

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ} {ω ψ : HeckeCharacter F}
variable {V HL HR : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k l : ℕ}
variable {sL : ActualAllocatedSource A V HL k} {sR : ActualAllocatedSource A V HR l}
variable {DL : sL.Calibration (σ := σ) ω ψ} {DR : sR.Calibration (σ := σ) ω ψ}
variable {IL : DL.CapacityInput} {IR : DR.CapacityInput}

/-- The actual envelope-free coefficient, with the two original Gauss
normalizers, both child width normalizations and the original first
Cauchy allowance. -/
def originalAllowanceCapacityPairWeight (left : DL.CapacityChild IL) (right : DR.CapacityChild IR)
    (boundsL : Fin sL.allocation.keep.card → ℝ) (boundsR : Fin sR.allocation.keep.card → ℝ)
    (originalLeft originalRight : ℂ) (Z firstNormalization : ℝ) : ℝ :=
  ‖originalLeft‖ * ‖originalRight‖ * Real.sqrt (left.envelopeFreeCost boundsL) *
    Real.sqrt (right.envelopeFreeCost boundsR) *
    Real.sqrt (Z ^ (left.parameters.m + left.parameters.q)) *
    Real.sqrt (Z ^ (right.parameters.m + right.parameters.q)) / firstNormalization

theorem originalAllowanceCapacityPairWeight_nonneg
    (left : DL.CapacityChild IL) (right : DR.CapacityChild IR)
    (boundsL : Fin sL.allocation.keep.card → ℝ) (boundsR : Fin sR.allocation.keep.card → ℝ)
    (originalLeft originalRight : ℂ) (Z firstNormalization : ℝ) (hN : 0 ≤ firstNormalization) :
    0 ≤ originalAllowanceCapacityPairWeight left right boundsL boundsR originalLeft originalRight Z firstNormalization := by
  unfold originalAllowanceCapacityPairWeight
  positivity

theorem originalAllowanceCapacityPairWeight_eq_normalized
    (left : DL.CapacityChild IL) (right : DR.CapacityChild IR)
    (AL AR : V → ℝ) (hAL : ∀ ξ, 0 < AL ξ) (hAR : ∀ ξ, 0 < AR ξ)
    (BL : Fin sL.allocation.keep.card → ℝ) (BR : Fin sR.allocation.keep.card → ℝ)
    (hBL : ∀ i, 0 ≤ BL i) (hBR : ∀ i, 0 ≤ BR i)
    (hfL : ∀ ξ i, IL.primeBound ξ i = AL ξ ^ 2 * BL i)
    (hfR : ∀ ξ i, IR.primeBound ξ i = AR ξ ^ 2 * BR i)
    (originalLeft originalRight : ℂ) (Z p : ℝ) :
    originalAllowanceCapacityPairWeight left right BL BR originalLeft originalRight Z (Z ^ p) =
      normalizedCapacityPairWeight (IL.normalizedChild AL hAL BL hBL hfL left)
        (IR.normalizedChild AR hAR BR hBR hfR right) originalLeft originalRight Z p := rfl

section CommonCost

variable [IsPrincipalIdealRing A.R]

/-- The exact first allowance cancels the corresponding second-source
width exponent.  Only primitive field costs and original windows occur
as hypotheses. -/
theorem originalAllowanceCapacityPairWeight_relative_allowance
    (left : DL.CapacityChild IL) (right : DR.CapacityChild IR)
    (AL AR : V → ℝ) (hAL : ∀ ξ, 0 < AL ξ) (hAR : ∀ ξ, 0 < AR ξ)
    (BL : Fin sL.allocation.keep.card → ℝ) (BR : Fin sR.allocation.keep.card → ℝ)
    (hBL : ∀ i, 0 ≤ BL i) (hBR : ∀ i, 0 ≤ BR i)
    (hfL : ∀ ξ i, IL.primeBound ξ i = AL ξ ^ 2 * BL i)
    (hfR : ∀ ξ i, IR.primeBound ξ i = AR ξ ^ 2 * BR i)
    (originalLeft originalRight : ℂ) (Z : ℝ) (hZ : 1 < Z)
    (firstNormalization a₀ q wo w boundary krow g ell NL NR δ : ℝ)
    (hN : firstNormalization = Z ^ (a₀ + q + w + boundary))
    (r : {r : ℝ // 0 < r}) (mask : Finset (HeightOneSpectrum A.R))
    (D E T R L : Ideal (𝓞 F)) (hD : D ≠ 0) (hE : E ≠ 0) (hT : T ≠ 0) (hL : L ≠ 0)
    (hrow : Z ^ (-krow - g) ≤
      r.val * (sIntegerElementNorm F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
        (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) mask)).val)
    (hcentral : Z ^ a₀ ≤ Real.sqrt NL * Real.sqrt NR)
    (hnormalizers : ‖originalLeft‖ * ‖originalRight‖ = 1 / (Real.sqrt NL * Real.sqrt NR))
    (frozenCost fiberCost primeCost : ℝ) (cap : ℕ) (hfrozen : 1 ≤ frozenCost)
    (hbaseL : sL.base = Z) (hbaseR : sR.base = Z)
    (hrowL : DL.rowBound ≤ secondCommonRowCost (A := A) r mask D E T)
    (hrowR : DR.rowBound ≤ secondCommonRowCost (A := A) r mask D E T)
    (hscalarL : DL.scalarBound ≤ frozenCost ^ cap / (Ideal.absNorm L : ℝ))
    (hscalarR : DR.scalarBound ≤ frozenCost ^ cap / (Ideal.absNorm L : ℝ))
    (hfiberL : (DL.fiberBound : ℝ) ≤ fiberCost) (hfiberR : (DR.fiberBound : ℝ) ≤ fiberCost)
    (hprimeL : ∀ i, BL i ≤ primeCost) (hprimeR : ∀ i, BR i ≤ primeCost)
    (hprime : 1 ≤ primeCost)
    (hcapL : sL.allocation.keep.card ≤ cap) (hcapR : sR.allocation.keep.card ≤ cap)
    (hbudgetL : DL.parameters.m + DL.parameters.q + IL.exponent ≤
      secondCommonChildWidth Z a₀ q wo krow g D E T R +
        secondCommonChildAllowance Z w boundary ell D E + δ)
    (hbudgetR : DR.parameters.m + DR.parameters.q + IR.exponent ≤
      secondCommonChildWidth Z a₀ q wo krow g D E T R +
        secondCommonChildAllowance Z w boundary ell D E + δ) :
    originalAllowanceCapacityPairWeight left right BL BR originalLeft originalRight Z firstNormalization ≤
      (frozenCost ^ cap * fiberCost * primeCost ^ cap * orbitalFieldFactor F) *
        Z ^ (δ + wo + ell) / (Ideal.absNorm (commonRadical D E) : ℝ) /
          (Ideal.absNorm L : ℝ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  let lchild := IL.normalizedChild AL hAL BL hBL hfL left
  let rchild := IR.normalizedChild AR hAR BR hBR hfR right
  have hs := normalizedCapacityPairWeight_second_harmonic lchild rchild
    originalLeft originalRight Z hZ (a₀ + q) a₀ q wo w boundary krow g ell NL NR δ
    (w + boundary + δ) r mask D E T R L hD hE hT hL hrow hcentral hnormalizers
    frozenCost fiberCost primeCost cap hfrozen hbaseL hbaseR hrowL hrowR
    hscalarL hscalarR hfiberL hfiberR hprimeL hprimeR hprime hcapL hcapR
    hbudgetL hbudgetR rfl le_rfl
  have hN' : firstNormalization = Z ^ (a₀ + q) * Z ^ (w + boundary) := by
    rw [hN, ← Real.rpow_add hz]
    congr 1
    ring
  have he : Z ^ (w + boundary + δ + wo + ell) =
      Z ^ (δ + wo + ell) * Z ^ (w + boundary) := by
    rw [← Real.rpow_add hz]
    congr 1
    ring
  calc
    _ = normalizedCapacityPairWeight lchild rchild originalLeft originalRight Z (a₀ + q) /
        Z ^ (w + boundary) := by
      unfold originalAllowanceCapacityPairWeight
      rw [hN', div_mul_eq_div_div]
      rfl
    _ ≤ ((frozenCost ^ cap * fiberCost * primeCost ^ cap * orbitalFieldFactor F) *
        Z ^ (w + boundary + δ + wo + ell) / (Ideal.absNorm (commonRadical D E) : ℝ) /
          (Ideal.absNorm L : ℝ)) / Z ^ (w + boundary) :=
      div_le_div_of_nonneg_right hs (Real.rpow_nonneg hz.le _)
    _ = ((frozenCost ^ cap * fiberCost * primeCost ^ cap * orbitalFieldFactor F) *
        Z ^ (δ + wo + ell) / (Ideal.absNorm (commonRadical D E) : ℝ) /
          (Ideal.absNorm L : ℝ)) * (Z ^ (w + boundary) / Z ^ (w + boundary)) := by
      rw [he]
      ring
    _ = _ := by rw [div_self (Real.rpow_pos_of_pos hz _).ne', mul_one]

end CommonCost

/-- The actual first row coefficient with its two original Cauchy
allowances. The raw profile scalar is not replaced by a common bound
inside the positive kernel. -/
def firstOriginalAllowanceWeight (Z parentWidth total rawProfile : ℝ)
    (D E : Ideal (𝓞 F)) : ℝ :=
  (rawProfile * Real.sqrt (Ideal.absNorm (firstActiveRadical D E) : ℝ)) *
    Real.sqrt (firstLeftAllowance Z total D E) *
    Real.sqrt (firstRightAllowance Z total D E) / Z ^ parentWidth

theorem firstOriginalAllowanceWeight_nonneg (Z parentWidth total rawProfile : ℝ)
    (hZ : 0 < Z) (hprofile : 0 ≤ rawProfile) (D E : Ideal (𝓞 F)) :
    0 ≤ firstOriginalAllowanceWeight Z parentWidth total rawProfile D E := by
  unfold firstOriginalAllowanceWeight
  positivity

/-- This derives the first common-radical density from an original
profile window and the original individual ideal support identities. -/
theorem firstOriginalAllowanceWeight_le_radical
    (Z parentWidth total rawProfile profileCost : ℝ) (hZ : 1 < Z) (hcost : 0 ≤ profileCost)
    (hprofile : rawProfile ≤ profileCost * Z ^ (parentWidth - total))
    (D E : Ideal (𝓞 F)) (hD : D ≠ 0) (hE : E ≠ 0)
    (hsupport : primeSupport D = primeSupport E) :
    firstOriginalAllowanceWeight Z parentWidth total rawProfile D E ≤
      profileCost / (Ideal.absNorm (commonRadical D E) : ℝ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  calc
    _ ≤ (profileCost * Z ^ (parentWidth - total)) *
        Real.sqrt (Ideal.absNorm (firstActiveRadical D E) : ℝ) *
        Real.sqrt (firstLeftAllowance Z total D E) *
        Real.sqrt (firstRightAllowance Z total D E) / Z ^ parentWidth := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hprofile (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    _ = profileCost * firstCommonWeight Z D E := by
      rw [← first_allowance_scalar_identity Z total parentWidth hZ D E]
      ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left
      (firstCommonWeight_le_radical Z hZ D E hD hE hsupport) hcost).trans_eq (by ring)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.originalAllowanceCapacityPairWeight_relative_allowance
#print axioms HeckeSkeleton.Moments.EngineStep.firstOriginalAllowanceWeight_le_radical
