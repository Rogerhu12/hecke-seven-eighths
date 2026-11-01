import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityRelativeScalar
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedFourierChildren

/-!
# Total mass on the original decorated capacity-child carrier

The positive kernel below retains the actual first profile scalar,
both original first Cauchy allowances, both Möbius coefficients, both
finite Fourier coefficients, the two original Gauss normalizers and
the exact pre-deletion profile degrees.  Its two continuous measures
are the original Schwartz Fourier measures.

The finite carrier may contain arbitrary genuine support, row, sector
and rectangle decorations.  Their actual fibres over `TwoDivisorCommonBranch.Index`
are counted.  No inequality for a total child mass is supplied.
-/

noncomputable section
open HeckePort.IdealMobiusDivisorSum
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree UniqueFactorizationMonoid MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments CommonSupportMass

section FixedFourierConstants

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The analytic property used to choose the fixed original seminorms.
It is proved from the original weighted Fourier L1 theorem below. -/
def OriginalKernelFourierProperty (cap J₁ J₂ : ℕ)
    (data : Finset (ℕ × ℕ) × Finset (ℕ × ℕ) × ℝ) : Prop :=
  0 < data.2.2 ∧ ∀ (n₁ n₂ : ℕ), n₁ ≤ cap → n₂ ≤ cap →
    ∀ (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ)) (B₁ B₂ : ℝ), 0 ≤ B₁ → 0 ≤ B₂ →
      IsFiniteMeasure (normalizedPairMeasure F₁ F₂ n₁ n₂ B₁ B₂ J₁ J₂) ∧
      (normalizedPairMeasure F₁ F₂ n₁ n₂ B₁ B₂ J₁ J₂).real Set.univ ≤
        ((1 + B₁) ^ (cap + 2) * (1 + B₂) ^ (cap + 2)) * data.2.2 *
          data.1.sup (schwartzSeminormFamily ℝ U ℂ) F₁ *
            data.2.1.sup (schwartzSeminormFamily ℝ E ℂ) F₂

private theorem originalKernelFourier_exists (cap J₁ J₂ : ℕ) :
    ∃ data, OriginalKernelFourierProperty (U := U) (E := E) cap J₁ J₂ data := by
  obtain ⟨s₁, s₂, C, hC, hmass⟩ :=
    normalizedPairMeasure_uniform_mass_upto (V := U) (E := E) cap J₁ J₂
  exact ⟨(s₁, s₂, C), hC, hmass⟩

/-- These choices depend only on the original dimension, slot cap and
polynomial orders, and precede every source and finite decoration. -/
def originalKernelFourierData (cap J₁ J₂ : ℕ) :
    Finset (ℕ × ℕ) × Finset (ℕ × ℕ) × ℝ :=
  Classical.choose (originalKernelFourier_exists (U := U) (E := E) cap J₁ J₂)

theorem originalKernelFourierData_spec (cap J₁ J₂ : ℕ) :
    OriginalKernelFourierProperty (U := U) (E := E) cap J₁ J₂
      (originalKernelFourierData (U := U) (E := E) cap J₁ J₂) :=
  Classical.choose_spec (originalKernelFourier_exists (U := U) (E := E) cap J₁ J₂)

end FixedFourierConstants

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ} {ω ψ : HeckeCharacter F}
variable [IsPrincipalIdealRing A.R]
variable {V HL HR : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k l : ℕ}
variable {sL : ActualAllocatedSource A V HL k} {sR : ActualAllocatedSource A V HR l}
variable {branch : TwoDivisorCommonBranch (K := F)}

/-- Typed projections keep the original dependent index out of repeated field elaboration. -/
private def originalLabelFirstLeft (j : branch.Index) : Ideal (𝓞 F) := j.1.val.1.1
private def originalLabelFirstRight (j : branch.Index) : Ideal (𝓞 F) := j.1.val.1.2
private def originalLabelSecondLeft (j : branch.Index) : Ideal (𝓞 F) := j.2.2.1.val.1.1
private def originalLabelSecondRight (j : branch.Index) : Ideal (𝓞 F) := j.2.2.1.val.1.2
private def originalLabelSecondDivisor (j : branch.Index) : Ideal (𝓞 F) := j.2.2.2.1.val

/-- A ledger of original numerical windows and individual factor
costs.  It has no field asserting a source, child, or total-mass bound.
The producer chooses the calibration costs by `withAllocationCosts`
and transports its capacity input with `withCosts.capacityInput`. -/
structure OriginalLabelCostWindows (j : branch.Index)
    (DL : sL.Calibration (σ := σ) ω ψ) (DR : sR.Calibration (σ := σ) ω ψ)
    (IL : DL.CapacityInput) (IR : DR.CapacityInput)
    (BL : Fin sL.allocation.keep.card → ℝ) (BR : Fin sR.allocation.keep.card → ℝ)
    (originalLeft originalRight : ℂ)
    (Z firstCost frozenCost fiberCost primeCost remaining : ℝ) (cap : ℕ) : Type where
  firstRowWeight : ℝ
  firstProfile : ℝ
  firstParentWidth : ℝ
  firstTotal : ℝ
  first_profile_nonneg : 0 ≤ firstProfile
  first_row : firstRowWeight = firstProfile *
    Real.sqrt (Ideal.absNorm (firstActiveRadical
      (originalLabelFirstLeft (branch := branch) j)
      (originalLabelFirstRight (branch := branch) j)) : ℝ)
  first_profile : firstProfile ≤ firstCost * Z ^ (firstParentWidth - firstTotal)
  first_left_ne_zero : (originalLabelFirstLeft (branch := branch) j) ≠ 0
  first_right_ne_zero : (originalLabelFirstRight (branch := branch) j) ≠ 0
  first_support : primeSupport (originalLabelFirstLeft (branch := branch) j) =
    primeSupport (originalLabelFirstRight (branch := branch) j)
  firstNormalization : ℝ
  a₀ : ℝ
  q : ℝ
  wo : ℝ
  w : ℝ
  boundary : ℝ
  krow : ℝ
  g : ℝ
  ell : ℝ
  NL : ℝ
  NR : ℝ
  delta : ℝ
  radius : {r : ℝ // 0 < r}
  mask : Finset (HeightOneSpectrum A.R)
  unitRadical : Ideal (𝓞 F)
  boundaryRadical : Ideal (𝓞 F)
  first_normalization : firstNormalization = Z ^ (a₀ + q + w + boundary)
  second_left_ne_zero : (originalLabelSecondLeft (branch := branch) j) ≠ 0
  second_right_ne_zero : (originalLabelSecondRight (branch := branch) j) ≠ 0
  unit_ne_zero : unitRadical ≠ 0
  divisor_ne_zero : (originalLabelSecondDivisor (branch := branch) j) ≠ 0
  left_divisor : sL.allocation.divisor = (originalLabelSecondDivisor (branch := branch) j)
  right_divisor : sR.allocation.divisor = (originalLabelSecondDivisor (branch := branch) j)
  original_radius : Z ^ (-krow - g) ≤
    radius.val * (sIntegerElementNorm F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
      (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) mask)).val
  central_window : Z ^ a₀ ≤ Real.sqrt NL * Real.sqrt NR
  original_normalizers : ‖originalLeft‖ * ‖originalRight‖ =
    1 / (Real.sqrt NL * Real.sqrt NR)
  left_base : sL.base = Z
  right_base : sR.base = Z
  left_row_cost : DL.rowBound ≤ secondCommonRowCost (A := A) radius mask
    (originalLabelSecondLeft (branch := branch) j)
    (originalLabelSecondRight (branch := branch) j) unitRadical
  right_row_cost : DR.rowBound ≤ secondCommonRowCost (A := A) radius mask
    (originalLabelSecondLeft (branch := branch) j)
    (originalLabelSecondRight (branch := branch) j) unitRadical
  left_scalar_cost : DL.scalarBound ≤ frozenCost ^ cap /
    (Ideal.absNorm (originalLabelSecondDivisor (branch := branch) j) : ℝ)
  right_scalar_cost : DR.scalarBound ≤ frozenCost ^ cap /
    (Ideal.absNorm (originalLabelSecondDivisor (branch := branch) j) : ℝ)
  left_fibers : (DL.fiberBound : ℝ) ≤ fiberCost
  right_fibers : (DR.fiberBound : ℝ) ≤ fiberCost
  left_prime_cost : ∀ i, BL i ≤ primeCost
  right_prime_cost : ∀ i, BR i ≤ primeCost
  left_count : sL.allocation.keep.card ≤ cap
  right_count : sR.allocation.keep.card ≤ cap
  left_budget : DL.parameters.m + DL.parameters.q + IL.exponent ≤
    secondCommonChildWidth Z a₀ q wo krow g
      (originalLabelSecondLeft (branch := branch) j)
      (originalLabelSecondRight (branch := branch) j) unitRadical boundaryRadical +
        secondCommonChildAllowance Z w boundary ell
          (originalLabelSecondLeft (branch := branch) j)
          (originalLabelSecondRight (branch := branch) j) + delta
  right_budget : DR.parameters.m + DR.parameters.q + IR.exponent ≤
    secondCommonChildWidth Z a₀ q wo krow g
      (originalLabelSecondLeft (branch := branch) j)
      (originalLabelSecondRight (branch := branch) j) unitRadical boundaryRadical +
        secondCommonChildAllowance Z w boundary ell
          (originalLabelSecondLeft (branch := branch) j)
          (originalLabelSecondRight (branch := branch) j) + delta
  remaining_margin : delta + wo + ell ≤ remaining

namespace OriginalLabelCostWindows

variable {j : branch.Index}
variable {DL : sL.Calibration (σ := σ) ω ψ} {DR : sR.Calibration (σ := σ) ω ψ}
variable {IL : DL.CapacityInput} {IR : DR.CapacityInput}
variable {BL : Fin sL.allocation.keep.card → ℝ} {BR : Fin sR.allocation.keep.card → ℝ}
variable {originalLeft originalRight : ℂ}
variable {Z firstCost frozenCost fiberCost primeCost remaining : ℝ} {cap : ℕ}
variable (W : OriginalLabelCostWindows j DL DR IL IR BL BR originalLeft originalRight
  Z firstCost frozenCost fiberCost primeCost remaining cap)

def firstWeight : ℝ :=
  W.firstRowWeight * Real.sqrt (firstLeftAllowance Z W.firstTotal j.1.val.1.1 j.1.val.1.2) *
    Real.sqrt (firstRightAllowance Z W.firstTotal j.1.val.1.1 j.1.val.1.2) / Z ^ W.firstParentWidth

theorem firstWeight_nonneg (hZ : 0 < Z) : 0 ≤ W.firstWeight := by
  unfold firstWeight
  rw [W.first_row]
  exact firstOriginalAllowanceWeight_nonneg Z W.firstParentWidth W.firstTotal W.firstProfile
    hZ W.first_profile_nonneg _ _

theorem firstWeight_le (hZ : 1 < Z) (hfirst : 0 ≤ firstCost) :
    W.firstWeight ≤ firstCost / (Ideal.absNorm (commonRadical j.1.val.1.1 j.1.val.1.2) : ℝ) := by
  unfold firstWeight
  rw [W.first_row]
  exact firstOriginalAllowanceWeight_le_radical Z W.firstParentWidth W.firstTotal W.firstProfile
    firstCost hZ hfirst W.first_profile _ _ W.first_left_ne_zero W.first_right_ne_zero W.first_support

theorem firstNormalization_pos (hZ : 0 < Z) : 0 < W.firstNormalization := by
  rw [W.first_normalization]
  exact Real.rpow_pos_of_pos hZ _

variable {Ray₁ Ray₂ : Type*} [CommGroup Ray₁] [Fintype Ray₁] [CommGroup Ray₂] [Fintype Ray₂]

/-- Every original phase and Möbius coefficient remains in the label
scalar; their absolute values are bounded only in the proof. -/
def labelWeight (left : DL.CapacityChild IL) (right : DR.CapacityChild IR)
    (phase₁ : Ray₁ × Ray₁ → Circle) (χ₁ : (Ray₁ × Ray₁) →* Circle)
    (phase₂ : Ray₂ × Ray₂ → Circle) (χ₂ : (Ray₂ × Ray₂) →* Circle) : ℝ :=
  W.firstWeight * ‖(moebius j.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
    ‖(moebius j.2.2.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₂ phase₂ χ₂‖ *
    originalAllowanceCapacityPairWeight left right BL BR originalLeft originalRight Z W.firstNormalization

theorem labelWeight_nonneg (left : DL.CapacityChild IL) (right : DR.CapacityChild IR)
    (phase₁ : Ray₁ × Ray₁ → Circle) (χ₁ : (Ray₁ × Ray₁) →* Circle)
    (phase₂ : Ray₂ × Ray₂ → Circle) (χ₂ : (Ray₂ × Ray₂) →* Circle) (hZ : 0 < Z) :
    0 ≤ W.labelWeight left right phase₁ χ₁ phase₂ χ₂ := by
  have hfirst := W.firstWeight_nonneg hZ
  have hpair := originalAllowanceCapacityPairWeight_nonneg left right BL BR originalLeft originalRight
    Z W.firstNormalization (W.firstNormalization_pos hZ).le
  unfold labelWeight
  positivity

theorem labelWeight_le
    (left : DL.CapacityChild IL) (right : DR.CapacityChild IR)
    (AL AR : V → ℝ) (hAL : ∀ ξ, 0 < AL ξ) (hAR : ∀ ξ, 0 < AR ξ)
    (hBL : ∀ i, 0 ≤ BL i) (hBR : ∀ i, 0 ≤ BR i)
    (hfL : ∀ ξ i, IL.primeBound ξ i = AL ξ ^ 2 * BL i)
    (hfR : ∀ ξ i, IR.primeBound ξ i = AR ξ ^ 2 * BR i)
    (phase₁ : Ray₁ × Ray₁ → Circle) (χ₁ : (Ray₁ × Ray₁) →* Circle)
    (phase₂ : Ray₂ × Ray₂ → Circle) (χ₂ : (Ray₂ × Ray₂) →* Circle)
    (hZ : 1 < Z) (hfirst : 0 ≤ firstCost) (hfrozen : 1 ≤ frozenCost) (hprime : 1 ≤ primeCost) :
    W.labelWeight left right phase₁ χ₁ phase₂ χ₂ ≤
      firstCost * (frozenCost ^ cap * fiberCost * primeCost ^ cap * orbitalFieldFactor F) *
        Z ^ remaining * branch.indexWeight j := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hfiber : 0 ≤ fiberCost := (Nat.cast_nonneg DL.fiberBound).trans W.left_fibers
  have hfrozen0 : 0 ≤ frozenCost := zero_le_one.trans hfrozen
  have hprime0 : 0 ≤ primeCost := zero_le_one.trans hprime
  have hconstant : 0 ≤ frozenCost ^ cap * fiberCost * primeCost ^ cap * orbitalFieldFactor F :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hfrozen0 _) hfiber)
      (pow_nonneg hprime0 _)) (orbitalFieldFactor_nonneg F)
  have hs := originalAllowanceCapacityPairWeight_relative_allowance left right AL AR hAL hAR BL BR hBL hBR
    hfL hfR originalLeft originalRight Z hZ W.firstNormalization W.a₀ W.q W.wo W.w W.boundary
    W.krow W.g W.ell W.NL W.NR W.delta W.first_normalization W.radius W.mask
    j.2.2.1.val.1.1 j.2.2.1.val.1.2 W.unitRadical W.boundaryRadical j.2.2.2.1.val
    W.second_left_ne_zero W.second_right_ne_zero W.unit_ne_zero W.divisor_ne_zero
    W.original_radius W.central_window W.original_normalizers frozenCost fiberCost primeCost cap
    hfrozen W.left_base W.right_base W.left_row_cost W.right_row_cost W.left_scalar_cost
    W.right_scalar_cost W.left_fibers W.right_fibers W.left_prime_cost W.right_prime_cost
    hprime W.left_count W.right_count W.left_budget W.right_budget
  have hs' := hs.trans (div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ.le W.remaining_margin) hconstant)
      (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
  have hp := mul_le_mul (W.firstWeight_le hZ hfirst) hs'
    (originalAllowanceCapacityPairWeight_nonneg left right BL BR originalLeft originalRight Z
      W.firstNormalization (W.firstNormalization_pos hz).le)
    (div_nonneg hfirst (Nat.cast_nonneg _))
  have hc : ‖(moebius j.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
      ‖(moebius j.2.2.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₂ phase₂ χ₂‖ ≤
      ‖(moebius j.2.1.val : ℂ)‖ * ‖(moebius j.2.2.2.1.val : ℂ)‖ := by
    have hc₁ : ‖(moebius j.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
        ‖(moebius j.2.2.2.1.val : ℂ)‖ ≤
        ‖(moebius j.2.1.val : ℂ)‖ * ‖(moebius j.2.2.2.1.val : ℂ)‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (fixed_phase_coefficient_norm Ray₁ phase₁ χ₁)
          (norm_nonneg (moebius j.2.1.val : ℂ)))
        (norm_nonneg (moebius j.2.2.2.1.val : ℂ))
    simpa only [mul_one] using mul_le_mul hc₁ (fixed_phase_coefficient_norm Ray₂ phase₂ χ₂)
      (norm_nonneg (fixedPhaseCoefficient Ray₂ phase₂ χ₂))
      (mul_nonneg (norm_nonneg (moebius j.2.1.val : ℂ))
        (norm_nonneg (moebius j.2.2.2.1.val : ℂ)))
  have hp0 : 0 ≤ firstCost / (Ideal.absNorm (commonRadical j.1.val.1.1 j.1.val.1.2) : ℝ) *
      ((frozenCost ^ cap * fiberCost * primeCost ^ cap * orbitalFieldFactor F) *
        Z ^ remaining / (Ideal.absNorm (commonRadical j.2.2.1.val.1.1 j.2.2.1.val.1.2) : ℝ) /
          (Ideal.absNorm j.2.2.2.1.val : ℝ)) :=
    mul_nonneg (div_nonneg hfirst (Nat.cast_nonneg _))
      (div_nonneg (div_nonneg (mul_nonneg hconstant (Real.rpow_nonneg hz.le _))
        (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
  have hfinal := mul_le_mul hp hc (by positivity) hp0
  convert hfinal using 1 <;>
    dsimp only [labelWeight, TwoDivisorCommonBranch.indexWeight] <;> ring

end OriginalLabelCostWindows

section OriginalKernel

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {HL HR : Type*} {k l : ℕ}
variable {sL : ActualAllocatedSource A (WithLp 2 (U × E)) HL k}
variable {sR : ActualAllocatedSource A (WithLp 2 (U × E)) HR l}
variable {j : branch.Index}
variable {DL : sL.Calibration (σ := σ) ω ψ} {DR : sR.Calibration (σ := σ) ω ψ}
variable {IL : DL.CapacityInput} {IR : DR.CapacityInput}
variable {BL : Fin sL.allocation.keep.card → ℝ} {BR : Fin sR.allocation.keep.card → ℝ}
variable {originalLeft originalRight : ℂ}
variable {Z firstCost frozenCost fiberCost primeCost remaining : ℝ} {cap : ℕ}
variable (W : OriginalLabelCostWindows j DL DR IL IR BL BR originalLeft originalRight
  Z firstCost frozenCost fiberCost primeCost remaining cap)
variable {Ray₁ Ray₂ : Type*} [CommGroup Ray₁] [Fintype Ray₁] [CommGroup Ray₂] [Fintype Ray₂]

/-- `outer` is the literal pool/row scalar. In particular the one
factor `4 / poolDensity` can be kept outside this entire family. -/
def originalCapacityLabelKernel (outer : ℝ)
    (left : DL.CapacityChild IL) (right : DR.CapacityChild IR)
    (phase₁ : Ray₁ × Ray₁ → Circle) (χ₁ : (Ray₁ × Ray₁) →* Circle)
    (phase₂ : Ray₂ × Ray₂ → Circle) (χ₂ : (Ray₂ × Ray₂) →* Circle)
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ))
    (AL AR : WithLp 2 (U × E) → ℝ) : Measure (U × E) :=
  ENNReal.ofReal (outer * W.labelWeight left right phase₁ χ₁ phase₂ χ₂) •
    weightedNestedFourierMeasure F₁ F₂ (fun z =>
      AL (WithLp.toLp 2 z) ^ (sL.allocation.keep.card + 2) *
        AR (WithLp.toLp 2 z) ^ (sR.allocation.keep.card + 2))

theorem originalCapacityLabelKernel_eq_canonical (outer : ℝ)
    (left : DL.CapacityChild IL) (right : DR.CapacityChild IR)
    (phase₁ : Ray₁ × Ray₁ → Circle) (χ₁ : (Ray₁ × Ray₁) →* Circle)
    (phase₂ : Ray₂ × Ray₂ → Circle) (χ₂ : (Ray₂ × Ray₂) →* Circle)
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ))
    (AL AR : WithLp 2 (U × E) → ℝ) (B₁ B₂ : ℝ) (J₁ J₂ : ℕ)
    (hleftRadius : ∀ z, AL (WithLp.toLp 2 z) = canonicalProfileAmplitude B₁ J₁ J₂ z)
    (hrightRadius : ∀ z, AR (WithLp.toLp 2 z) = canonicalProfileAmplitude B₂ J₁ J₂ z) :
    originalCapacityLabelKernel W outer left right phase₁ χ₁ phase₂ χ₂ F₁ F₂ AL AR =
      ENNReal.ofReal (outer * W.labelWeight left right phase₁ χ₁ phase₂ χ₂) •
        normalizedPairMeasure F₁ F₂ sL.allocation.keep.card sR.allocation.keep.card B₁ B₂ J₁ J₂ := by
  have heq : (fun z => AL (WithLp.toLp 2 z) ^ (sL.allocation.keep.card + 2) *
      AR (WithLp.toLp 2 z) ^ (sR.allocation.keep.card + 2)) =
      canonicalPairEnvelope sL.allocation.keep.card sR.allocation.keep.card B₁ B₂ J₁ J₂ := by
    funext z
    simp only [canonicalPairEnvelope, hleftRadius, hrightRadius]
  simp only [originalCapacityLabelKernel, normalizedPairMeasure, heq]

theorem originalCapacityLabelKernel_mass (outer : ℝ) (houter : 0 ≤ outer)
    (left : DL.CapacityChild IL) (right : DR.CapacityChild IR)
    (phase₁ : Ray₁ × Ray₁ → Circle) (χ₁ : (Ray₁ × Ray₁) →* Circle)
    (phase₂ : Ray₂ × Ray₂ → Circle) (χ₂ : (Ray₂ × Ray₂) →* Circle)
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ))
    (AL AR : WithLp 2 (U × E) → ℝ) (hZ : 0 < Z) :
    (originalCapacityLabelKernel W outer left right phase₁ χ₁ phase₂ χ₂ F₁ F₂ AL AR).real Set.univ =
      outer * W.labelWeight left right phase₁ χ₁ phase₂ χ₂ *
        (weightedNestedFourierMeasure F₁ F₂ (fun z =>
          AL (WithLp.toLp 2 z) ^ (sL.allocation.keep.card + 2) *
            AR (WithLp.toLp 2 z) ^ (sR.allocation.keep.card + 2))).real Set.univ := by
  rw [originalCapacityLabelKernel, measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofReal (mul_nonneg houter (W.labelWeight_nonneg left right phase₁ χ₁ phase₂ χ₂ hZ))]

theorem originalCapacityLabelKernel_bound
    (outer control : ℝ) (houter : 0 ≤ outer) (hcontrol : 0 ≤ control)
    (left : DL.CapacityChild IL) (right : DR.CapacityChild IR)
    (AL AR : WithLp 2 (U × E) → ℝ) (hAL : ∀ ξ, 0 < AL ξ) (hAR : ∀ ξ, 0 < AR ξ)
    (hBL : ∀ i, 0 ≤ BL i) (hBR : ∀ i, 0 ≤ BR i)
    (hfL : ∀ ξ i, IL.primeBound ξ i = AL ξ ^ 2 * BL i)
    (hfR : ∀ ξ i, IR.primeBound ξ i = AR ξ ^ 2 * BR i)
    (phase₁ : Ray₁ × Ray₁ → Circle) (χ₁ : (Ray₁ × Ray₁) →* Circle)
    (phase₂ : Ray₂ × Ray₂ → Circle) (χ₂ : (Ray₂ × Ray₂) →* Circle)
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ)) (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (J₁ J₂ : ℕ)
    (hleftRadius : ∀ z, AL (WithLp.toLp 2 z) = canonicalProfileAmplitude B₁ J₁ J₂ z)
    (hrightRadius : ∀ z, AR (WithLp.toLp 2 z) = canonicalProfileAmplitude B₂ J₁ J₂ z)
    (hprofiles : ((1 + B₁) ^ (cap + 2) * (1 + B₂) ^ (cap + 2)) *
      (originalKernelFourierData (U := U) (E := E) cap J₁ J₂).1.sup
        (schwartzSeminormFamily ℝ U ℂ) F₁ *
      (originalKernelFourierData (U := U) (E := E) cap J₁ J₂).2.1.sup
        (schwartzSeminormFamily ℝ E ℂ) F₂ ≤ control)
    (hZ : 1 < Z) (hfirst : 0 ≤ firstCost) (hfrozen : 1 ≤ frozenCost) (hprime : 1 ≤ primeCost) :
    IsFiniteMeasure (originalCapacityLabelKernel W outer left right phase₁ χ₁ phase₂ χ₂
      F₁ F₂ AL AR) ∧
    (originalCapacityLabelKernel W outer left right phase₁ χ₁ phase₂ χ₂ F₁ F₂ AL AR).real Set.univ ≤
      outer * firstCost * (frozenCost ^ cap * fiberCost * primeCost ^ cap * orbitalFieldFactor F) *
        Z ^ remaining * (originalKernelFourierData (U := U) (E := E) cap J₁ J₂).2.2 *
          control * branch.indexWeight j := by
  have hfixed := originalKernelFourierData_spec (U := U) (E := E) cap J₁ J₂
  have hfourier := hfixed.2 sL.allocation.keep.card sR.allocation.keep.card
    W.left_count W.right_count F₁ F₂ B₁ B₂ hB₁ hB₂
  haveI := hfourier.1
  have heq := originalCapacityLabelKernel_eq_canonical W outer left right phase₁ χ₁ phase₂ χ₂
    F₁ F₂ AL AR B₁ B₂ J₁ J₂ hleftRadius hrightRadius
  refine ⟨by rw [heq]; infer_instance, ?_⟩
  have hmass : (normalizedPairMeasure F₁ F₂ sL.allocation.keep.card sR.allocation.keep.card
      B₁ B₂ J₁ J₂).real Set.univ ≤
      (originalKernelFourierData (U := U) (E := E) cap J₁ J₂).2.2 * control := by
    apply hfourier.2.trans
    convert mul_le_mul_of_nonneg_left hprofiles hfixed.1.le using 1 <;> ring
  have hscalar := W.labelWeight_le left right AL AR hAL hAR hBL hBR hfL hfR
    phase₁ χ₁ phase₂ χ₂ hZ hfirst hfrozen hprime
  rw [heq, measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal
    (mul_nonneg houter (W.labelWeight_nonneg left right phase₁ χ₁ phase₂ χ₂ (zero_lt_one.trans hZ)))]
  have hfiber : 0 ≤ fiberCost := (Nat.cast_nonneg DL.fiberBound).trans W.left_fibers
  have hfrozen0 : 0 ≤ frozenCost := zero_le_one.trans hfrozen
  have hprime0 : 0 ≤ primeCost := zero_le_one.trans hprime
  have hconstant : 0 ≤ outer * (firstCost *
      (frozenCost ^ cap * fiberCost * primeCost ^ cap * orbitalFieldFactor F) *
        Z ^ remaining * branch.indexWeight j) := by
    exact mul_nonneg houter (mul_nonneg
      (mul_nonneg (mul_nonneg hfirst (mul_nonneg
        (mul_nonneg (mul_nonneg (pow_nonneg hfrozen0 _) hfiber) (pow_nonneg hprime0 _))
        (orbitalFieldFactor_nonneg F))) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
      (branch.indexWeight_nonneg j))
  have h := mul_le_mul (mul_le_mul_of_nonneg_left hscalar houter) hmass
    (measureReal_nonneg) hconstant
  exact h.trans_eq (by ring)

end OriginalKernel

/-- The arithmetic constant is selected by the proved two-divisor
theorem before the scale, the moving ideals and the decorated carrier. -/
def originalCapacityArithmeticConstant (N : ℕ) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) : ℝ :=
  Classical.choose (TwoDivisorCommonBranch.uniform_mass (K := F) N B ε hB hε)

theorem originalCapacityArithmeticConstant_spec (N : ℕ) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    0 < originalCapacityArithmeticConstant (F := F) N B ε hB hε ∧
    ∀ Z : ℝ, 1 ≤ Z → ∀ old : Ideal (𝓞 F), Squarefree old → old ≠ 0 →
    ∀ b : TwoDivisorCommonBranch (K := F), b.Admissible N B Z old →
      b.mass ≤ originalCapacityArithmeticConstant (F := F) N B ε hB hε *
        Z ^ ε / (Ideal.absNorm old : ℝ) :=
  Classical.choose_spec (TwoDivisorCommonBranch.uniform_mass (K := F) N B ε hB hε)

section ActualFiniteCarrier

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Λ : Type*} [Fintype Λ] (index : Λ → branch.Index)
variable {LeftRow RightRow : Λ → Type} {leftSlots rightSlots : Λ → ℕ}
variable {sourcesL : ∀ i, ActualAllocatedSource A (WithLp 2 (U × E)) (LeftRow i) (leftSlots i)}
variable {sourcesR : ∀ i, ActualAllocatedSource A (WithLp 2 (U × E)) (RightRow i) (rightSlots i)}
variable {DL : ∀ i, (sourcesL i).Calibration (σ := σ) ω ψ}
variable {DR : ∀ i, (sourcesR i).Calibration (σ := σ) ω ψ}
variable {IL : ∀ i, (DL i).CapacityInput} {IR : ∀ i, (DR i).CapacityInput}
variable {BL : ∀ i, Fin (sourcesL i).allocation.keep.card → ℝ}
variable {BR : ∀ i, Fin (sourcesR i).allocation.keep.card → ℝ}
variable {originalLeft originalRight : Λ → ℂ}
variable {Z firstCost frozenCost fiberCost primeCost remaining : ℝ} {cap : ℕ}
variable (windows : ∀ i, OriginalLabelCostWindows (index i) (DL i) (DR i) (IL i) (IR i)
  (BL i) (BR i) (originalLeft i) (originalRight i) Z firstCost frozenCost fiberCost primeCost remaining cap)
variable (left : ∀ i, (DL i).CapacityChild (IL i)) (right : ∀ i, (DR i).CapacityChild (IR i))
variable {Ray₁ Ray₂ : Type*} [CommGroup Ray₁] [Fintype Ray₁] [CommGroup Ray₂] [Fintype Ray₂]
variable (phase₁ : Λ → Ray₁ × Ray₁ → Circle) (χ₁ : Λ → (Ray₁ × Ray₁) →* Circle)
variable (phase₂ : Λ → Ray₂ × Ray₂ → Circle) (χ₂ : Λ → (Ray₂ × Ray₂) →* Circle)
variable (F₁ : Λ → 𝓢(U, ℂ)) (F₂ : Λ → 𝓢(E, ℂ))
variable (AL AR : Λ → WithLp 2 (U × E) → ℝ)

/-- The finite family is indexed by the actual decorated source
carrier.  Every scalar and every pre-deletion profile exponent is
evaluated at the same label. -/
def originalCapacityFamilyKernel (outer : ℝ) (i : Λ) : Measure (U × E) :=
  originalCapacityLabelKernel (windows i) outer (left i) (right i)
    (phase₁ i) (χ₁ i) (phase₂ i) (χ₂ i) (F₁ i) (F₂ i) (AL i) (AR i)

local notation "kernel" => originalCapacityFamilyKernel index windows left right phase₁ χ₁ phase₂ χ₂ F₁ F₂ AL AR

theorem originalCapacityFamilyKernel_total_mass (outer : ℝ) (houter : 0 ≤ outer) (hZ : 0 < Z) :
    (∑ i : Λ, (kernel outer i).real Set.univ) =
      ∑ i : Λ, outer * (windows i).labelWeight (left i) (right i)
        (phase₁ i) (χ₁ i) (phase₂ i) (χ₂ i) *
          (weightedNestedFourierMeasure (F₁ i) (F₂ i) (fun z =>
            AL i (WithLp.toLp 2 z) ^ ((sourcesL i).allocation.keep.card + 2) *
              AR i (WithLp.toLp 2 z) ^ ((sourcesR i).allocation.keep.card + 2))).real Set.univ := by
  exact Finset.sum_congr rfl fun i _ => originalCapacityLabelKernel_mass
    (windows i) outer houter (left i) (right i) (phase₁ i) (χ₁ i) (phase₂ i) (χ₂ i)
    (F₁ i) (F₂ i) (AL i) (AR i) hZ

variable (B₁ B₂ : Λ → ℝ) (J₁ J₂ : ℕ)

/-- The exact finite kernel mass is now controlled by the official
two-divisor harmonic mass.  Profile control is an original finite
seminorm window; fibre control concerns the literal finite index map. -/
theorem originalCapacityFamilyKernel_mass_bound
    (outer control multiplicity : ℝ) (houter : 0 ≤ outer) (hcontrol : 0 ≤ control)
    (hcard : ∀ j, ((Finset.univ.filter (fun i => index i = j)).card : ℝ) ≤ multiplicity)
    (hAL : ∀ i ξ, 0 < AL i ξ) (hAR : ∀ i ξ, 0 < AR i ξ)
    (hBL : ∀ i t, 0 ≤ BL i t) (hBR : ∀ i t, 0 ≤ BR i t)
    (hfL : ∀ i ξ t, (IL i).primeBound ξ t = AL i ξ ^ 2 * BL i t)
    (hfR : ∀ i ξ t, (IR i).primeBound ξ t = AR i ξ ^ 2 * BR i t)
    (hB₁ : ∀ i, 0 ≤ B₁ i) (hB₂ : ∀ i, 0 ≤ B₂ i)
    (hleftRadius : ∀ i z, AL i (WithLp.toLp 2 z) = canonicalProfileAmplitude (B₁ i) J₁ J₂ z)
    (hrightRadius : ∀ i z, AR i (WithLp.toLp 2 z) = canonicalProfileAmplitude (B₂ i) J₁ J₂ z)
    (hprofiles : ∀ i, ((1 + B₁ i) ^ (cap + 2) * (1 + B₂ i) ^ (cap + 2)) *
      (originalKernelFourierData (U := U) (E := E) cap J₁ J₂).1.sup
        (schwartzSeminormFamily ℝ U ℂ) (F₁ i) *
      (originalKernelFourierData (U := U) (E := E) cap J₁ J₂).2.1.sup
        (schwartzSeminormFamily ℝ E ℂ) (F₂ i) ≤ control)
    (hZ : 1 < Z) (hfirst : 0 ≤ firstCost) (hfrozen : 1 ≤ frozenCost)
    (hfiber : 0 ≤ fiberCost) (hprime : 1 ≤ primeCost) :
    (∀ i, IsFiniteMeasure (kernel outer i)) ∧
    (∑ i : Λ, (kernel outer i).real Set.univ) ≤
      outer * firstCost * (frozenCost ^ cap * fiberCost * primeCost ^ cap * orbitalFieldFactor F) *
        Z ^ remaining * (originalKernelFourierData (U := U) (E := E) cap J₁ J₂).2.2 *
          control * multiplicity * branch.mass := by
  have hlabel (i : Λ) := originalCapacityLabelKernel_bound (windows i) outer control houter hcontrol
    (left i) (right i) (AL i) (AR i) (hAL i) (hAR i) (hBL i) (hBR i) (hfL i) (hfR i)
    (phase₁ i) (χ₁ i) (phase₂ i) (χ₂ i) (F₁ i) (F₂ i) (B₁ i) (B₂ i) (hB₁ i) (hB₂ i)
    J₁ J₂ (hleftRadius i) (hrightRadius i) (hprofiles i) hZ hfirst hfrozen hprime
  refine ⟨fun i => (hlabel i).1, ?_⟩
  let K : ℝ := outer * firstCost *
    (frozenCost ^ cap * fiberCost * primeCost ^ cap * orbitalFieldFactor F) *
      Z ^ remaining * (originalKernelFourierData (U := U) (E := E) cap J₁ J₂).2.2 * control
  have hK : 0 ≤ K := by
    have hfrozen0 : 0 ≤ frozenCost := zero_le_one.trans hfrozen
    have hprime0 : 0 ≤ primeCost := zero_le_one.trans hprime
    have hFourier := (originalKernelFourierData_spec (U := U) (E := E) cap J₁ J₂).1.le
    have hOrbital := orbitalFieldFactor_nonneg F
    have hz : 0 < Z := zero_lt_one.trans hZ
    dsimp only [K]
    positivity
  have hindex := sum_weighted_fibres_le index branch.indexWeight branch.indexWeight_nonneg
    multiplicity hcard
  rw [branch.sum_indexWeight] at hindex
  calc
    _ ≤ ∑ i : Λ, K * branch.indexWeight (index i) :=
      Finset.sum_le_sum fun i _ => (hlabel i).2
    _ = K * ∑ i : Λ, branch.indexWeight (index i) := by rw [Finset.mul_sum]
    _ ≤ K * (multiplicity * branch.mass) := mul_le_mul_of_nonneg_left hindex hK
    _ = _ := by dsimp only [K]; ring

/-- The uniform endpoint uses the genuine original norm/support
windows of the same `branch`. Its constant is selected above from
`TwoDivisorCommonBranch.uniform_mass`, never supplied as an aggregate
child-mass hypothesis. -/
theorem originalCapacityFamilyKernel_uniform_mass
    (N : ℕ) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε)
    (old : Ideal (𝓞 F)) (hold : Squarefree old) (hold0 : old ≠ 0)
    (hadmissible : branch.Admissible N B Z old)
    (outer control multiplicity : ℝ) (houter : 0 ≤ outer) (hcontrol : 0 ≤ control)
    (hmultiplicity : 0 ≤ multiplicity)
    (hcard : ∀ j, ((Finset.univ.filter (fun i => index i = j)).card : ℝ) ≤ multiplicity)
    (hAL : ∀ i ξ, 0 < AL i ξ) (hAR : ∀ i ξ, 0 < AR i ξ)
    (hBL : ∀ i t, 0 ≤ BL i t) (hBR : ∀ i t, 0 ≤ BR i t)
    (hfL : ∀ i ξ t, (IL i).primeBound ξ t = AL i ξ ^ 2 * BL i t)
    (hfR : ∀ i ξ t, (IR i).primeBound ξ t = AR i ξ ^ 2 * BR i t)
    (hB₁ : ∀ i, 0 ≤ B₁ i) (hB₂ : ∀ i, 0 ≤ B₂ i)
    (hleftRadius : ∀ i z, AL i (WithLp.toLp 2 z) = canonicalProfileAmplitude (B₁ i) J₁ J₂ z)
    (hrightRadius : ∀ i z, AR i (WithLp.toLp 2 z) = canonicalProfileAmplitude (B₂ i) J₁ J₂ z)
    (hprofiles : ∀ i, ((1 + B₁ i) ^ (cap + 2) * (1 + B₂ i) ^ (cap + 2)) *
      (originalKernelFourierData (U := U) (E := E) cap J₁ J₂).1.sup
        (schwartzSeminormFamily ℝ U ℂ) (F₁ i) *
      (originalKernelFourierData (U := U) (E := E) cap J₁ J₂).2.1.sup
        (schwartzSeminormFamily ℝ E ℂ) (F₂ i) ≤ control)
    (hZ : 1 < Z) (hfirst : 0 ≤ firstCost) (hfrozen : 1 ≤ frozenCost)
    (hfiber : 0 ≤ fiberCost) (hprime : 1 ≤ primeCost) :
    (∀ i, IsFiniteMeasure (kernel outer i)) ∧
    (∑ i : Λ, (kernel outer i).real Set.univ) ≤
      outer * firstCost * (frozenCost ^ cap * fiberCost * primeCost ^ cap * orbitalFieldFactor F) *
        (originalKernelFourierData (U := U) (E := E) cap J₁ J₂).2.2 * control * multiplicity *
          originalCapacityArithmeticConstant (F := F) N B ε hB hε *
            Z ^ (remaining + ε) / (Ideal.absNorm old : ℝ) := by
  have hfamily := originalCapacityFamilyKernel_mass_bound index windows left right
    phase₁ χ₁ phase₂ χ₂ F₁ F₂ AL AR B₁ B₂ J₁ J₂ outer control multiplicity houter hcontrol hcard
    hAL hAR hBL hBR hfL hfR hB₁ hB₂ hleftRadius hrightRadius hprofiles hZ hfirst hfrozen hfiber hprime
  refine ⟨hfamily.1, ?_⟩
  have hmass := (originalCapacityArithmeticConstant_spec (F := F) N B ε hB hε).2
    Z hZ.le old hold hold0 branch hadmissible
  have hfrozen0 : 0 ≤ frozenCost := zero_le_one.trans hfrozen
  have hprime0 : 0 ≤ primeCost := zero_le_one.trans hprime
  have hFourier := (originalKernelFourierData_spec (U := U) (E := E) cap J₁ J₂).1.le
  have hOrbital := orbitalFieldFactor_nonneg F
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hfactor : 0 ≤ outer * firstCost *
      (frozenCost ^ cap * fiberCost * primeCost ^ cap * orbitalFieldFactor F) *
        Z ^ remaining * (originalKernelFourierData (U := U) (E := E) cap J₁ J₂).2.2 *
          control * multiplicity := by positivity
  apply hfamily.2.trans ((mul_le_mul_of_nonneg_left hmass hfactor).trans_eq ?_)
  rw [Real.rpow_add hz]
  ring

end ActualFiniteCarrier

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalLabelCostWindows.labelWeight_le
#print axioms HeckeSkeleton.Moments.EngineStep.originalCapacityLabelKernel_bound
#print axioms HeckeSkeleton.Moments.EngineStep.originalCapacityFamilyKernel_total_mass
#print axioms HeckeSkeleton.Moments.EngineStep.originalCapacityFamilyKernel_uniform_mass
