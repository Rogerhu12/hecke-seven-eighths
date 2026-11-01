import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalOriginalLabel
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.WeightedNestedFourierMeasure
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NestedHybridKernel

/-!
# Integrate the actual exceptional source on its two original kernels

The exceptional character/profile charts are pointwise in the original
Fourier pair.  The source inequality is proved from those raw charts,
original atom windows, valuations and numerical scale ledger, not
supplied as a hypothesis.  Actual finite polynomials prove convergence.

The two controlling Fourier seminorms and their constant are selected
only from fixed dimensions and polynomial orders.  All original
Möbius factors, phase coefficients, first allowances and the genuine
second-divisor dyad remain in the integrated statement.
-/

noncomputable section
open HeckePort.IdealMobiusDivisorSum HeckeGeneral.Arithmetic
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

/-- Proved Fourier control; this is constructed from weighted L1,
never supplied by the source producer. -/
structure ExceptionalFourierControl (J₁ J₂ : ℕ) where
  leftSeminorms : Finset (ℕ × ℕ)
  rightSeminorms : Finset (ℕ × ℕ)
  constant : ℝ
  constant_pos : 0 < constant
  bound : ∀ (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ)),
    (∫ z : U × E, (1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂
      ∂nestedFourierMeasure F₁ F₂) ≤
      constant * leftSeminorms.sup (schwartzSeminormFamily ℝ U ℂ) F₁ *
        rightSeminorms.sup (schwartzSeminormFamily ℝ E ℂ) F₂

def exceptionalFourierControl (J₁ J₂ : ℕ) :
    ExceptionalFourierControl (U := U) (E := E) J₁ J₂ := by
  have h : Nonempty (ExceptionalFourierControl (U := U) (E := E) J₁ J₂) := by
    obtain ⟨s₁, s₂, C, hC, hmass⟩ :=
      nestedFourierMeasure_weighted_mass_bound (V := U) (E := E) J₁ J₂
    exact ⟨⟨s₁, s₂, C, hC, hmass⟩⟩
  exact Classical.choice h

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsPrincipalIdealRing A.R]
variable {C : A.GeneralArithmeticContext σ η hS}
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {kCommonLeft kCommonRight : ℕ}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray] {k l : ℕ}
local notation "ProductFourierSpace" => WithLp 2 (U × E)

namespace SecondSideFrame

theorem exceptionalMagnitude_nested_integrable
    (left : SecondSideFrame (V := ProductFourierSpace) C R Ray .left k)
    (right : SecondSideFrame (V := ProductFourierSpace) C R Ray .right l)
    (EL : SecondCoefficientComparison left.dictionary)
    (ER : SecondCoefficientComparison right.dictionary)
    {theta : Finset (HeckeCharacter F)} (Q : PairedFiniteCharacters theta H)
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ)) :
    Integrable (fun z : U × E => left.exceptionalMagnitude right EL ER Q (WithLp.toLp 2 z))
      (nestedFourierMeasure F₁ F₂) := by
  letI := nestedFourierMeasure_finite F₁ F₂
  exact nested_joint_magnitude_integrable _ _ _ _ _ _ _ _ _

variable {ΨL ΨR : Ideal (𝓞 F) →* ℂ} {WL₁ WL₂ WR₁ WR₂ : ℝ → ℂ}
variable (HL : ExceptionalVolumeControl ΨL WL₁ WL₂) (HR : ExceptionalVolumeControl ΨR WR₁ WR₂)
variable (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent)

/-- The complete actual source bound is integrated with both original
Fourier measures.  The extra window controls only the explicit real
height in the original single-ideal exceptional charts. -/
theorem exceptional_original_label_integral_from_atoms
    (left : SecondSideFrame (V := ProductFourierSpace) C R Ray .left k)
    (right : SecondSideFrame (V := ProductFourierSpace) C R Ray .right l)
    (EL : SecondCoefficientComparison left.dictionary)
    (ER : SecondCoefficientComparison right.dictionary)
    (W : ActualSecondRowMass R C kCommonLeft kCommonRight)
    {theta : Finset (HeckeCharacter F)} (Q : PairedFiniteCharacters theta H)
    (TL : ∀ ξ : ProductFourierSpace, ∀ h : R.exceptionalRows Q, left.source.ExceptionalAt (σ := σ) EL.scale₁ EL.scale₂
      (fun _ => EL.leftWeight) (fun _ => EL.rightWeight) ΨL WL₁ WL₂ ξ h.val)
    (TR : ∀ ξ : ProductFourierSpace, ∀ h : R.exceptionalRows Q, right.source.ExceptionalAt (σ := σ) ER.scale₁ ER.scale₂
      (fun _ => ER.leftWeight) (fun _ => ER.rightWeight) ΨR WR₁ WR₂ ξ h.val)
    (UL : ExceptionalAtomicScales left.allocation) (UR : ExceptionalAtomicScales right.allocation)
    (Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v vStar
      r₁ r₂ divisorLower slotError stepσ δ parentWidth remaining rowError widthError : ℝ)
    (height : ProductFourierSpace → ℝ)
    (hZ : 1 < Z) (hv : 0 ≤ v) (hr₁ : 0 ≤ r₁) (hdivisor : divisorLower - r₂ ≤ slotError)
    (hheight : ∀ ξ, 0 ≤ height ξ)
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
    (hvsum : vStar ≤ c + w + b₂)
    (hmask0 : ∀ ξ h, (TL ξ h).source.mask ≠ ⊥)
    (hmasknorm : ∀ ξ h, (Ideal.absNorm (TL ξ h).source.mask : ℝ) ≤ Z ^ maskExponent)
    (htime : ∀ ξ h, ‖(TL ξ h).source.time‖ ≤ height ξ)
    (hminimum : ∀ ξ h, Z ^ ((m + q) / 4 - vStar - r₁) ≤ (TL ξ h).source.lower)
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
    (J₁ J₂ : ℕ) (heightConstant : ℝ) (hheightConstant : 0 ≤ heightConstant)
    (hheightPolynomial : ∀ z : U × E,
      (1 + height (WithLp.toLp 2 z)) ^ exceptionalTerminalOrder (V := ProductFourierSpace) (σ := σ) (η := η) (hS := hS)
        HL HR ε maskExponent hε hmask ≤
      heightConstant * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂))
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ)) :
    (∫ z : U × E,
      firstOriginalAllowanceWeight Z firstParentWidth firstTotal firstProfile j.1.val.1.1 j.1.val.1.2 *
        ‖(moebius S : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
        ‖(moebius left.allocation.divisor : ℂ)‖ *
        ‖fixedPhaseCoefficient Ray phase₂ left.phaseCharacter‖ *
        (left.exceptionalMagnitude right EL ER Q (WithLp.toLp 2 z) / Z ^ parentWidth)
      ∂nestedFourierMeasure F₁ F₂) ≤
      firstCost *
        ((W.commonEnvelope * orbitalFieldFactor F) *
          ((W.originalFiber : ℝ) * exceptionalTerminalConstant (V := ProductFourierSpace) (σ := σ) (η := η) (hS := hS)
            HL HR ε maskExponent hε hmask * (UL.constant * UR.constant))) *
        Z ^ (remaining + widthError +
          (max (Aexp - (m + q)) 0 + 3 * stepσ + 5 * δ / 6 + ε + slotError)) *
        branch.exceptionalDyadWeight Z divisorLower j * heightConstant *
        (exceptionalFourierControl (U := U) (E := E) J₁ J₂).constant *
        (exceptionalFourierControl (U := U) (E := E) J₁ J₂).leftSeminorms.sup
          (schwartzSeminormFamily ℝ U ℂ) F₁ *
        (exceptionalFourierControl (U := U) (E := E) J₁ J₂).rightSeminorms.sup
          (schwartzSeminormFamily ℝ E ℂ) F₂ := by
  let major := firstCost *
    ((W.commonEnvelope * orbitalFieldFactor F) *
      ((W.originalFiber : ℝ) * exceptionalTerminalConstant (V := ProductFourierSpace) (σ := σ) (η := η) (hS := hS)
        HL HR ε maskExponent hε hmask * (UL.constant * UR.constant))) *
    Z ^ (remaining + widthError +
      (max (Aexp - (m + q)) 0 + 3 * stepσ + 5 * δ / 6 + ε + slotError)) *
    branch.exceptionalDyadWeight Z divisorLower j
  have hmajor : 0 ≤ major := by
    have hvolume := (exceptionalTerminalConstant_pos (V := ProductFourierSpace) (σ := σ) (η := η) (hS := hS)
      HL HR ε maskExponent hε hmask).le
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
        (left.exceptionalMagnitude right EL ER Q (WithLp.toLp 2 z) / Z ^ parentWidth) ≤
      major * (1 + height (WithLp.toLp 2 z)) ^
        exceptionalTerminalOrder (V := ProductFourierSpace) (σ := σ) (η := η) (hS := hS)
          HL HR ε maskExponent hε hmask := by
    have hs := exceptional_original_label_from_atoms
      (HL := HL) (HR := HR) (ε := ε) (maskExponent := maskExponent) (hε := hε) (hmask := hmask)
      left right EL ER W Q (WithLp.toLp 2 z) (TL _) (TR _) UL UR
      Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v vStar
      r₁ r₂ divisorLower slotError (height _) stepσ δ parentWidth remaining rowError widthError
      hZ hv hr₁ hdivisor (hheight _) (hleftAtoms _) (hrightAtoms _) hexponent hgcd hunit
      base hclass hfactor hwindow hcutoff hF₁ hF₂ hvsum (hmask0 _) (hmasknorm _)
      (htime _) (hminimum _) hradius hcentral hdyad hremaining hwidth
      j S hSindex hleftIdeal hrightIdeal hleftDivisor hrightDivisor
      hleftOccurrences hrightOccurrences hleftAllocation hrightAllocation
      phase₁ χ₁ phase₂ hphase firstParentWidth firstTotal firstProfile firstCost hfirstCost
      hfirstProfile hfirstLeft hfirstRight hfirstSupport
    convert hs using 1 <;> dsimp only [major] <;> ring
  have hi := (left.exceptionalMagnitude_nested_integrable right EL ER Q F₁ F₂).div_const
    (Z ^ parentWidth)
  have hsource := hi.const_mul
    (firstOriginalAllowanceWeight Z firstParentWidth firstTotal firstProfile j.1.val.1.1 j.1.val.1.2 *
      ‖(moebius S : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
      ‖(moebius left.allocation.divisor : ℂ)‖ *
      ‖fixedPhaseCoefficient Ray phase₂ left.phaseCharacter‖)
  calc
    _ ≤ ∫ z : U × E, major *
        (heightConstant * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂))
        ∂nestedFourierMeasure F₁ F₂ := by
      apply integral_mono hsource
        (((nestedFourierMeasure_mixed_polynomial_integrable F₁ F₂ J₁ J₂).const_mul
          heightConstant).const_mul major)
      intro z
      exact (hpoint z).trans (mul_le_mul_of_nonneg_left (hheightPolynomial z) hmajor)
    _ = major * (heightConstant *
        ∫ z : U × E, (1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂
          ∂nestedFourierMeasure F₁ F₂) := by
      rw [integral_const_mul, integral_const_mul]
    _ ≤ major * (heightConstant *
        ((exceptionalFourierControl (U := U) (E := E) J₁ J₂).constant *
          (exceptionalFourierControl (U := U) (E := E) J₁ J₂).leftSeminorms.sup
            (schwartzSeminormFamily ℝ U ℂ) F₁ *
          (exceptionalFourierControl (U := U) (E := E) J₁ J₂).rightSeminorms.sup
            (schwartzSeminormFamily ℝ E ℂ) F₂)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          ((exceptionalFourierControl (U := U) (E := E) J₁ J₂).bound F₁ F₂)
          hheightConstant) hmajor
    _ = _ := by dsimp only [major]; ring

end SecondSideFrame
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.exceptionalFourierControl
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.exceptional_original_label_integral_from_atoms
