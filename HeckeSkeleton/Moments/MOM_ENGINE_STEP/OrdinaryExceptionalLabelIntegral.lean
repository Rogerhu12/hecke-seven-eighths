import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OrdinaryExceptionalRelativeBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalOriginalIntegral

/-!
# Ordinary exceptional labels and their original Fourier integrals

The ordinary range uses absolute volume on the two original complete
columns.  Both finite-phase coefficients, both divisor factors, the
first allowance and the same full arithmetic allocation index remain
in the estimate.  All pointwise bounds follow from original atoms.

The ordinary estimate is uniform in the two Fourier parameters.  Its
integral therefore pays their original positive measure mass, with
fixed finite seminorms and no centered minimum or height premise.
-/

noncomputable section
open HeckePort.IdealMobiusDivisorSum HeckeGeneral.Arithmetic
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Characters HeckeGeneral.Analysis HeckePort.Moments
open HeckeGeneral.Analysis.ConditionalMoments CommonSupportMass
open UniqueFactorizationMonoid

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsPrincipalIdealRing A.R]
variable {C : A.GeneralArithmeticContext σ η hS}
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {kCommonLeft kCommonRight : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray] {k l : ℕ}

namespace SecondSideFrame

/-- The source's literal same-row exceptional magnitude. -/
def ordinaryExceptionalMagnitude
    (left : SecondSideFrame (V := V) C R Ray .left k)
    (right : SecondSideFrame (V := V) C R Ray .right l)
    {theta : Finset (HeckeCharacter F)} (Q : PairedFiniteCharacters theta H) (ξ : V) : ℝ :=
  jointColumnPairMagnitude (R.exceptionalRows Q) left.allocation.columns right.allocation.columns
    (fun h : R.live => R.weight h.val * R.correlation h.val)
    (fun h => left.coefficient h.val)
    (fun h => right.coefficient h.val)
    (fun h => rawSourceLocation (left.leftLocation h.val) (left.rightLocation h.val)
      (left.slotLocation h.val))
    (fun h => rawSourceLocation (right.leftLocation h.val) (right.rightLocation h.val)
      (right.slotLocation h.val)) ξ

theorem ordinaryExceptionalMagnitude_nonneg
    (left : SecondSideFrame (V := V) C R Ray .left k)
    (right : SecondSideFrame (V := V) C R Ray .right l)
    {theta : Finset (HeckeCharacter F)} (Q : PairedFiniteCharacters theta H) (ξ : V) :
    0 ≤ left.ordinaryExceptionalMagnitude right Q ξ :=
  jointColumnPairMagnitude_nonneg _ _ _ _ _ _ _ _ _

end SecondSideFrame

variable {ΨL ΨR : Ideal (𝓞 F) →* ℂ} {WL₁ WL₂ WR₁ WR₂ : ℝ → ℂ}
variable (HL : ExceptionalVolumeControl ΨL WL₁ WL₂) (HR : ExceptionalVolumeControl ΨR WR₁ WR₂)

namespace SecondSideFrame

/-- The original ordinary columns retain both divisor/phase coefficients
and the complete occurrence allocations.  The ordinary-range source
estimate is derived from its individual atoms before this scalar bound. -/
theorem ordinary_exceptional_original_label_from_atoms
    (left : SecondSideFrame (V := V) C R Ray .left k)
    (right : SecondSideFrame (V := V) C R Ray .right l)
    (W : ActualSecondRowMass R C kCommonLeft kCommonRight)
    {theta : Finset (HeckeCharacter F)} (Q : PairedFiniteCharacters theta H) (ξ : V)
    (TL : ∀ h : R.exceptionalRows Q, left.source.OrdinaryExceptionalAt (σ := σ) ΨL WL₁ WL₂ ξ h.val)
    (TR : ∀ h : R.exceptionalRows Q, right.source.OrdinaryExceptionalAt (σ := σ) ΨR WR₁ WR₂ ξ h.val)
    (UL : ExceptionalAtomicScales left.allocation) (UR : ExceptionalAtomicScales right.allocation)
    (Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v
      r₁ r₂ divisorLower slotError stepσ δ parentWidth remaining rowError widthError : ℝ)
    (hZ : 1 < Z) (hv : 0 ≤ v) (hr₁ : 0 ≤ r₁) (hdivisor : divisorLower - r₂ ≤ slotError)
    (hA : Aexp ≤ 5 * (m + q) / 6) (hc : 0 ≤ c) (hw : 0 ≤ w) (hb₂ : 0 ≤ b₂)
    (hleftAtoms : ∀ h, (TL h).source.AtomicControl Z UL)
    (hrightAtoms : ∀ h, (TR h).source.AtomicControl Z UR)
    (hexponent : UL.exponent + UR.exponent = Aexp - c - w - b₂ - r₁ - r₂)
    (hgcd : (Ideal.absNorm (gcd W.leftIdeal W.rightIdeal) : ℝ) ≤ Z ^ g₂)
    (hunit : Z ^ t₂ ≤ A.exteriorNorm W.unitIdeal)
    (base : Ideal (𝓞 F))
    (hclass : ∀ h : R.exceptionalRows Q, ∀ i ∈ multiplicityOneNonunitPrimes C R.primes
      R.leftMultiplicity R.rightMultiplicity (R.frequency h.val.val),
      6 ∣ (normalizedFactors (R.originalIdeal h.val.val).val).count (R.primes i).val.asIdeal)
    (hfactor : ∀ h : R.exceptionalRows Q, ∃ a : Ideal (𝓞 F),
      (R.extractedRow C h.val).ideal.val = base * a ^ 6)
    (hwindow : ∀ h : R.exceptionalRows Q, Z ^ v ≤ A.exteriorNorm
      (multiplicityOneNonunitRadical C R.primes R.leftMultiplicity R.rightMultiplicity
        (R.frequency h.val.val)))
    (hcutoff : ∀ h : R.exceptionalRows Q, A.exteriorNorm (R.originalIdeal h.val.val) ≤
      R.normFactor C h.val.val * Z ^ (2 * (Aexp - c - w) - K - g - g₂ - V₀))
    (hF₁ : 2 * (c + w) / 3 - 3 * stepσ - 5 * δ / 6 ≤
      firstSaving c (d + (2 * Aexp - c - d + R₀ + E₀ - m) - K)
        w (q + R₀ + E₀) wo Bcommon g ell)
    (hF₂ : 2 * b₂ / 3 ≤ 2 * b₂ - 5 * g₂ / 6 - p₂ + t₂ + V₀ / 6 + (2 * v) / 6)
    (hradius : Z ^ (-K - g) ≤
      W.radius.val * (sIntegerElementNorm F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
        (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) W.mask)).val)
    (hcentral : Z ^ (Aexp - c - w) ≤
      Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale)
    (hdyad : g₂ - t₂ ≤ idealLogLength Z (gcd W.leftIdeal W.rightIdeal) -
      idealLogLength Z W.unitIdeal.val + rowError)
    (hremaining : (Aexp - c - w) + (q + R₀ + E₀) + w + Bcommon + wo + ell + rowError -
      parentWidth ≤ remaining)
    (hwidth :
      ((2 * (Aexp - c - w) - K - g - g₂ - V₀) +
        (q + R₀ + E₀ + wo + t₂ + V₀) + (b₂ - p₂ + w + Bcommon + ell)) -
      (secondCommonChildWidth Z (Aexp - c - w) (q + R₀ + E₀) wo K g
          W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val +
        secondCommonChildAllowance Z w Bcommon ell W.leftIdeal W.rightIdeal) ≤ widthError)
    {branch : TwoDivisorCommonBranch (K := F)} (j : branch.Index)
    (S : Ideal (𝓞 F)) (hSindex : S = j.2.1.val)
    (hleftIdeal : W.leftIdeal = j.2.2.1.val.1.1)
    (hrightIdeal : W.rightIdeal = j.2.2.1.val.1.2)
    (hleftDivisor : left.allocation.divisor = j.2.2.2.1.val)
    (hrightDivisor : right.allocation.divisor = j.2.2.2.1.val)
    (hleftOccurrences : k + 2 ≤ branch.leftOccurrences
      j.1.val j.2.1.val j.2.2.1.val j.2.2.2.1.val)
    (hrightOccurrences : l + 2 ≤ branch.rightOccurrences
      j.1.val j.2.1.val j.2.2.1.val j.2.2.2.1.val)
    (hleftAllocation : HEq
      (AllocationMass.padSelection hleftOccurrences left.allocation.selection)
      j.2.2.2.2.1.val)
    (hrightAllocation : HEq
      (AllocationMass.padSelection hrightOccurrences right.allocation.selection)
      j.2.2.2.2.2.val)
    {Ray₁ : Type*} [CommGroup Ray₁] [Fintype Ray₁]
    (phase₁ : Ray₁ × Ray₁ → Circle) (χ₁ : (Ray₁ × Ray₁) →* Circle)
    (phase₂ : Ray × Ray → Circle)
    (hphase : right.phaseCharacter = left.phaseCharacter)
    (firstParentWidth firstTotal firstProfile firstCost : ℝ)
    (hfirstCost : 0 ≤ firstCost)
    (hfirstProfile : firstProfile ≤ firstCost * Z ^ (firstParentWidth - firstTotal))
    (hfirstLeft : j.1.val.1.1 ≠ 0) (hfirstRight : j.1.val.1.2 ≠ 0)
    (hfirstSupport : primeSupport j.1.val.1.1 = primeSupport j.1.val.1.2) :
    firstOriginalAllowanceWeight Z firstParentWidth firstTotal firstProfile j.1.val.1.1 j.1.val.1.2 *
      ‖(moebius S : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
      ‖(moebius left.allocation.divisor : ℂ)‖ *
      ‖fixedPhaseCoefficient Ray phase₂ left.phaseCharacter‖ *
      (left.ordinaryExceptionalMagnitude right Q ξ / Z ^ parentWidth) ≤
        firstCost *
          ((W.commonEnvelope * orbitalFieldFactor F) *
            ((W.originalFiber : ℝ) * ordinaryExceptionalConstant HL HR * (UL.constant * UR.constant))) *
          Z ^ (remaining + widthError +
            (3 * stepσ + 5 * δ / 6 + slotError)) *
          branch.exceptionalDyadWeight Z divisorLower j := by
  have hsecond := ordinary_exceptional_relative_terminal_from_atoms
    (HL := HL) (HR := HR) left right W Q ξ TL TR UL UR
    Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v
    r₁ r₂ divisorLower slotError stepσ δ parentWidth remaining rowError widthError
    hZ hv hr₁ hdivisor hA hc hw hb₂ hleftAtoms hrightAtoms hexponent hgcd hunit
    base hclass hfactor hwindow hcutoff hF₁ hF₂ hradius hcentral hdyad hremaining hwidth
  have hfirst := firstOriginalAllowanceWeight_le_radical Z firstParentWidth firstTotal
    firstProfile firstCost hZ hfirstCost hfirstProfile j.1.val.1.1 j.1.val.1.2
    hfirstLeft hfirstRight hfirstSupport
  rw [hleftIdeal, hrightIdeal] at hsecond
  rw [hSindex, hleftDivisor]
  apply original_exceptional_label_scalar j phase₁ χ₁ phase₂ left.phaseCharacter
    Z _ _ firstCost _ parentWidth _ divisorLower (zero_lt_one.trans hZ)
    (left.ordinaryExceptionalMagnitude_nonneg right Q ξ) hfirstCost hfirst
  exact hsecond

end SecondSideFrame
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.ordinary_exceptional_original_label_from_atoms

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis HeckePort.Moments
open HeckeGeneral.Analysis.ConditionalMoments CommonSupportMass
open UniqueFactorizationMonoid

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsPrincipalIdealRing A.R]
variable {C : A.GeneralArithmeticContext σ η hS}
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {kCommonLeft kCommonRight : ℕ}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray] {k l : ℕ}
local notation "V" => WithLp 2 (U × E)

namespace SecondSideFrame

theorem ordinaryExceptionalMagnitude_nested_integrable
    (left : SecondSideFrame (V := V) C R Ray .left k)
    (right : SecondSideFrame (V := V) C R Ray .right l)
    {theta : Finset (HeckeCharacter F)} (Q : PairedFiniteCharacters theta H)
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ)) :
    Integrable (fun z : U × E => left.ordinaryExceptionalMagnitude right Q (WithLp.toLp 2 z))
      (nestedFourierMeasure F₁ F₂) := by
  letI := nestedFourierMeasure_finite F₁ F₂
  exact nested_joint_magnitude_integrable _ _ _ _ _ _ _ _ _

variable {ΨL ΨR : Ideal (𝓞 F) →* ℂ} {WL₁ WL₂ WR₁ WR₂ : ℝ → ℂ}
variable (HL : ExceptionalVolumeControl ΨL WL₁ WL₂) (HR : ExceptionalVolumeControl ΨR WR₁ WR₂)

/-- Integrate the literal ordinary source against the same two original
Fourier kernels.  The absolute-volume estimate is uniform in their two
parameters, so the only Fourier cost is their proved total mass. -/
theorem ordinary_exceptional_original_label_integral_from_atoms
    (left : SecondSideFrame (V := V) C R Ray .left k)
    (right : SecondSideFrame (V := V) C R Ray .right l)
    (W : ActualSecondRowMass R C kCommonLeft kCommonRight)
    {theta : Finset (HeckeCharacter F)} (Q : PairedFiniteCharacters theta H)
    (TL : ∀ ξ : V, ∀ h : R.exceptionalRows Q, left.source.OrdinaryExceptionalAt (σ := σ) ΨL WL₁ WL₂ ξ h.val)
    (TR : ∀ ξ : V, ∀ h : R.exceptionalRows Q, right.source.OrdinaryExceptionalAt (σ := σ) ΨR WR₁ WR₂ ξ h.val)
    (UL : ExceptionalAtomicScales left.allocation) (UR : ExceptionalAtomicScales right.allocation)
    (Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v
      r₁ r₂ divisorLower slotError stepσ δ parentWidth remaining rowError widthError : ℝ)
    (hZ : 1 < Z) (hv : 0 ≤ v) (hr₁ : 0 ≤ r₁) (hdivisor : divisorLower - r₂ ≤ slotError)
    (hA : Aexp ≤ 5 * (m + q) / 6) (hc : 0 ≤ c) (hw : 0 ≤ w) (hb₂ : 0 ≤ b₂)
    (hleftAtoms : ∀ ξ h, (TL ξ h).source.AtomicControl Z UL)
    (hrightAtoms : ∀ ξ h, (TR ξ h).source.AtomicControl Z UR)
    (hexponent : UL.exponent + UR.exponent = Aexp - c - w - b₂ - r₁ - r₂)
    (hgcd : (Ideal.absNorm (gcd W.leftIdeal W.rightIdeal) : ℝ) ≤ Z ^ g₂)
    (hunit : Z ^ t₂ ≤ A.exteriorNorm W.unitIdeal)
    (base : Ideal (𝓞 F))
    (hclass : ∀ h : R.exceptionalRows Q, ∀ i ∈ multiplicityOneNonunitPrimes C R.primes
      R.leftMultiplicity R.rightMultiplicity (R.frequency h.val.val),
      6 ∣ (normalizedFactors (R.originalIdeal h.val.val).val).count (R.primes i).val.asIdeal)
    (hfactor : ∀ h : R.exceptionalRows Q, ∃ a : Ideal (𝓞 F),
      (R.extractedRow C h.val).ideal.val = base * a ^ 6)
    (hwindow : ∀ h : R.exceptionalRows Q, Z ^ v ≤ A.exteriorNorm
      (multiplicityOneNonunitRadical C R.primes R.leftMultiplicity R.rightMultiplicity
        (R.frequency h.val.val)))
    (hcutoff : ∀ h : R.exceptionalRows Q, A.exteriorNorm (R.originalIdeal h.val.val) ≤
      R.normFactor C h.val.val * Z ^ (2 * (Aexp - c - w) - K - g - g₂ - V₀))
    (hF₁ : 2 * (c + w) / 3 - 3 * stepσ - 5 * δ / 6 ≤
      firstSaving c (d + (2 * Aexp - c - d + R₀ + E₀ - m) - K)
        w (q + R₀ + E₀) wo Bcommon g ell)
    (hF₂ : 2 * b₂ / 3 ≤ 2 * b₂ - 5 * g₂ / 6 - p₂ + t₂ + V₀ / 6 + (2 * v) / 6)
    (hradius : Z ^ (-K - g) ≤
      W.radius.val * (sIntegerElementNorm F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
        (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) W.mask)).val)
    (hcentral : Z ^ (Aexp - c - w) ≤
      Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale)
    (hdyad : g₂ - t₂ ≤ idealLogLength Z (gcd W.leftIdeal W.rightIdeal) -
      idealLogLength Z W.unitIdeal.val + rowError)
    (hremaining : (Aexp - c - w) + (q + R₀ + E₀) + w + Bcommon + wo + ell + rowError -
      parentWidth ≤ remaining)
    (hwidth :
      ((2 * (Aexp - c - w) - K - g - g₂ - V₀) +
        (q + R₀ + E₀ + wo + t₂ + V₀) + (b₂ - p₂ + w + Bcommon + ell)) -
      (secondCommonChildWidth Z (Aexp - c - w) (q + R₀ + E₀) wo K g
          W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val +
        secondCommonChildAllowance Z w Bcommon ell W.leftIdeal W.rightIdeal) ≤ widthError)
    {branch : TwoDivisorCommonBranch (K := F)} (j : branch.Index)
    (S : Ideal (𝓞 F)) (hSindex : S = j.2.1.val)
    (hleftIdeal : W.leftIdeal = j.2.2.1.val.1.1)
    (hrightIdeal : W.rightIdeal = j.2.2.1.val.1.2)
    (hleftDivisor : left.allocation.divisor = j.2.2.2.1.val)
    (hrightDivisor : right.allocation.divisor = j.2.2.2.1.val)
    (hleftOccurrences : k + 2 ≤ branch.leftOccurrences
      j.1.val j.2.1.val j.2.2.1.val j.2.2.2.1.val)
    (hrightOccurrences : l + 2 ≤ branch.rightOccurrences
      j.1.val j.2.1.val j.2.2.1.val j.2.2.2.1.val)
    (hleftAllocation : HEq
      (AllocationMass.padSelection hleftOccurrences left.allocation.selection)
      j.2.2.2.2.1.val)
    (hrightAllocation : HEq
      (AllocationMass.padSelection hrightOccurrences right.allocation.selection)
      j.2.2.2.2.2.val)
    {Ray₁ : Type*} [CommGroup Ray₁] [Fintype Ray₁]
    (phase₁ : Ray₁ × Ray₁ → Circle) (χ₁ : (Ray₁ × Ray₁) →* Circle)
    (phase₂ : Ray × Ray → Circle)
    (hphase : right.phaseCharacter = left.phaseCharacter)
    (firstParentWidth firstTotal firstProfile firstCost : ℝ)
    (hfirstCost : 0 ≤ firstCost)
    (hfirstProfile : firstProfile ≤ firstCost * Z ^ (firstParentWidth - firstTotal))
    (hfirstLeft : j.1.val.1.1 ≠ 0) (hfirstRight : j.1.val.1.2 ≠ 0)
    (hfirstSupport : primeSupport j.1.val.1.1 = primeSupport j.1.val.1.2)
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ)) :
    (∫ z : U × E,
      firstOriginalAllowanceWeight Z firstParentWidth firstTotal firstProfile j.1.val.1.1 j.1.val.1.2 *
        ‖(moebius S : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
        ‖(moebius left.allocation.divisor : ℂ)‖ *
        ‖fixedPhaseCoefficient Ray phase₂ left.phaseCharacter‖ *
        (left.ordinaryExceptionalMagnitude right Q (WithLp.toLp 2 z) / Z ^ parentWidth)
      ∂nestedFourierMeasure F₁ F₂) ≤
      firstCost *
        ((W.commonEnvelope * orbitalFieldFactor F) *
          ((W.originalFiber : ℝ) * ordinaryExceptionalConstant HL HR * (UL.constant * UR.constant))) *
        Z ^ (remaining + widthError +
          (3 * stepσ + 5 * δ / 6 + slotError)) *
        branch.exceptionalDyadWeight Z divisorLower j *
        (exceptionalFourierControl (U := U) (E := E) 0 0).constant *
        (exceptionalFourierControl (U := U) (E := E) 0 0).leftSeminorms.sup
          (schwartzSeminormFamily ℝ U ℂ) F₁ *
        (exceptionalFourierControl (U := U) (E := E) 0 0).rightSeminorms.sup
          (schwartzSeminormFamily ℝ E ℂ) F₂ := by
  let major := firstCost *
    ((W.commonEnvelope * orbitalFieldFactor F) *
      ((W.originalFiber : ℝ) * ordinaryExceptionalConstant HL HR * (UL.constant * UR.constant))) *
    Z ^ (remaining + widthError + (3 * stepσ + 5 * δ / 6 + slotError)) *
    branch.exceptionalDyadWeight Z divisorLower j
  have hmajor : 0 ≤ major := by
    have hvolume := (ordinaryExceptionalConstant_pos HL HR).le
    have hcommon := W.commonEnvelope_nonneg
    have hfield := orbitalFieldFactor_nonneg F
    have hUL := UL.constant_nonneg
    have hUR := UR.constant_nonneg
    have hdyad0 := branch.exceptionalDyadWeight_nonneg Z divisorLower (zero_lt_one.trans hZ).le j
    dsimp only [major]
    positivity
  have hpoint (z : U × E) :
      firstOriginalAllowanceWeight Z firstParentWidth firstTotal firstProfile j.1.val.1.1 j.1.val.1.2 *
        ‖(moebius S : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
        ‖(moebius left.allocation.divisor : ℂ)‖ *
        ‖fixedPhaseCoefficient Ray phase₂ left.phaseCharacter‖ *
        (left.ordinaryExceptionalMagnitude right Q (WithLp.toLp 2 z) / Z ^ parentWidth) ≤
      major := by
    exact ordinary_exceptional_original_label_from_atoms (HL := HL) (HR := HR)
      left right W Q (WithLp.toLp 2 z) (TL _) (TR _) UL UR
      Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v
      r₁ r₂ divisorLower slotError stepσ δ parentWidth remaining rowError widthError
      hZ hv hr₁ hdivisor hA hc hw hb₂ (hleftAtoms _) (hrightAtoms _) hexponent hgcd hunit
      base hclass hfactor hwindow hcutoff hF₁ hF₂ hradius hcentral hdyad hremaining hwidth
      j S hSindex hleftIdeal hrightIdeal hleftDivisor hrightDivisor
      hleftOccurrences hrightOccurrences hleftAllocation hrightAllocation
      phase₁ χ₁ phase₂ hphase firstParentWidth firstTotal firstProfile firstCost hfirstCost
      hfirstProfile hfirstLeft hfirstRight hfirstSupport
  have hi := (left.ordinaryExceptionalMagnitude_nested_integrable right Q F₁ F₂).div_const
    (Z ^ parentWidth)
  have hsource := hi.const_mul
    (firstOriginalAllowanceWeight Z firstParentWidth firstTotal firstProfile j.1.val.1.1 j.1.val.1.2 *
      ‖(moebius S : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
      ‖(moebius left.allocation.divisor : ℂ)‖ *
      ‖fixedPhaseCoefficient Ray phase₂ left.phaseCharacter‖)
  calc
    _ ≤ ∫ z : U × E, major * ((1 + ‖z.1‖) ^ (0 : ℕ) * (1 + ‖z.2‖) ^ (0 : ℕ))
        ∂nestedFourierMeasure F₁ F₂ := by
      apply integral_mono hsource
        ((nestedFourierMeasure_mixed_polynomial_integrable F₁ F₂ 0 0).const_mul major)
      intro z
      simpa only [pow_zero, mul_one] using hpoint z
    _ = major * ∫ z : U × E, (1 + ‖z.1‖) ^ (0 : ℕ) * (1 + ‖z.2‖) ^ (0 : ℕ)
        ∂nestedFourierMeasure F₁ F₂ := by rw [integral_const_mul]
    _ ≤ major *
        ((exceptionalFourierControl (U := U) (E := E) 0 0).constant *
          (exceptionalFourierControl (U := U) (E := E) 0 0).leftSeminorms.sup
            (schwartzSeminormFamily ℝ U ℂ) F₁ *
          (exceptionalFourierControl (U := U) (E := E) 0 0).rightSeminorms.sup
            (schwartzSeminormFamily ℝ E ℂ) F₂) :=
      mul_le_mul_of_nonneg_left
        ((exceptionalFourierControl (U := U) (E := E) 0 0).bound F₁ F₂) hmajor
    _ = _ := by dsimp only [major]; ring

end SecondSideFrame
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.ordinaryExceptionalMagnitude_nested_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.ordinary_exceptional_original_label_integral_from_atoms
