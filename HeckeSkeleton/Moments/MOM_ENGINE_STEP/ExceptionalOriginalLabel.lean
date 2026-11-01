import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalRelativeBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityRelativeScalar
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocationPadding

/-!
# Both original divisor and finite-phase weights on an exceptional leaf

The actual first profile and two original Cauchy allowances are kept in
one scalar.  The actual second centered magnitude, with its own two
Gauss normalizers, is divided by the selected first allowance.  Both
Möbius factors and both finite Fourier coefficients are retained until
the proved single-coefficient bounds are used.

The source theorem consumes the original atom, valuation and numerical
window data.  It derives its second bound internally, and binds its
actual second divisor and both full allocation maps to the original
arithmetic index.  The result has exactly the exceptional dyad weight
whose same-carrier finite sum is proved in ExceptionalSameCarrierMass.
-/

noncomputable section
open HeckePort.IdealMobiusDivisorSum
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis HeckePort.Moments
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
def exceptionalMagnitude
    (left : SecondSideFrame (V := V) C R Ray .left k)
    (right : SecondSideFrame (V := V) C R Ray .right l)
    (EL : SecondCoefficientComparison left.dictionary)
    (ER : SecondCoefficientComparison right.dictionary)
    {theta : Finset (HeckeCharacter F)} (Q : PairedFiniteCharacters theta H) (ξ : V) : ℝ :=
  jointColumnPairMagnitude (R.exceptionalRows Q) left.allocation.columns right.allocation.columns
    (fun h : R.live => R.weight h.val * R.correlation h.val)
    (fun h => left.centeredCoefficient EL h.val)
    (fun h => right.centeredCoefficient ER h.val)
    (fun h => rawSourceLocation (left.leftLocation h.val) (left.rightLocation h.val)
      (left.slotLocation h.val))
    (fun h => rawSourceLocation (right.leftLocation h.val) (right.rightLocation h.val)
      (right.slotLocation h.val)) ξ

theorem exceptionalMagnitude_nonneg
    (left : SecondSideFrame (V := V) C R Ray .left k)
    (right : SecondSideFrame (V := V) C R Ray .right l)
    (EL : SecondCoefficientComparison left.dictionary)
    (ER : SecondCoefficientComparison right.dictionary)
    {theta : Finset (HeckeCharacter F)} (Q : PairedFiniteCharacters theta H) (ξ : V) :
    0 ≤ left.exceptionalMagnitude right EL ER Q ξ :=
  jointColumnPairMagnitude_nonneg _ _ _ _ _ _ _ _ _

end SecondSideFrame

private theorem exceptionalLabel_scalar_left
    (a m₁ c₁ m₂ c₂ t : ℝ) :
    a * m₁ * c₁ * m₂ * c₂ * t = (a * t) * (m₁ * c₁ * m₂ * c₂) := by
  ring

private theorem exceptionalLabel_scalar_right
    (a b x y n₁ n₂ m₁ m₂ : ℝ) :
    (a / n₁ * (b * x / n₂ * y)) * (m₁ * m₂) =
      a * b * x * (1 / n₁ * m₁ * (1 / n₂) * m₂ * y) := by
  ring

private theorem exceptionalLabel_denominator_transport
    {lhs numerator sourceDenominator targetDenominator saving : ℝ}
    (hdenominator : sourceDenominator = targetDenominator)
    (hbound : lhs ≤ numerator / sourceDenominator * saving) :
    lhs ≤ numerator / targetDenominator * saving :=
  hbound.trans_eq
    (congrArg (fun denominator : ℝ => numerator / denominator * saving) hdenominator)

private theorem exceptionalLabel_divisor_transport
    (firstWeight firstCoefficient secondCoefficient quotient bound : ℝ)
    {sourceFirst targetFirst sourceSecond targetSecond : ℝ}
    (hfirst : sourceFirst = targetFirst) (hsecond : sourceSecond = targetSecond)
    (hbound : firstWeight * targetFirst * firstCoefficient * targetSecond *
      secondCoefficient * quotient ≤ bound) :
    firstWeight * sourceFirst * firstCoefficient * sourceSecond *
      secondCoefficient * quotient ≤ bound :=
  (congrArg₂ (fun first second : ℝ => firstWeight * first * firstCoefficient *
    second * secondCoefficient * quotient) hfirst hsecond).le.trans hbound

private theorem exceptionalLabel_scalar_product_bound
    (weight quotient firstUpper secondUpper m₁ c₁ m₂ c₂ : ℝ)
    (hquotient : 0 ≤ quotient) (hfirstUpper : 0 ≤ firstUpper)
    (hfirst : weight ≤ firstUpper) (hsecond : quotient ≤ secondUpper)
    (hm₁ : 0 ≤ m₁) (hc₁ : 0 ≤ c₁) (hm₂ : 0 ≤ m₂) (hc₂ : 0 ≤ c₂)
    (hc₁one : c₁ ≤ 1) (hc₂one : c₂ ≤ 1) :
    (weight * quotient) * (m₁ * c₁ * m₂ * c₂) ≤
      (firstUpper * secondUpper) * (m₁ * m₂) := by
  have hp : weight * quotient ≤ firstUpper * secondUpper :=
    mul_le_mul hfirst hsecond hquotient hfirstUpper
  have hcFirst : m₁ * c₁ * m₂ ≤ m₁ * m₂ := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc₁one hm₁) hm₂
  have hc : m₁ * c₁ * m₂ * c₂ ≤ m₁ * m₂ := by
    simpa only [mul_one] using mul_le_mul hcFirst hc₂one hc₂ (mul_nonneg hm₁ hm₂)
  have hcoefficients : 0 ≤ m₁ * c₁ * m₂ * c₂ :=
    mul_nonneg (mul_nonneg (mul_nonneg hm₁ hc₁) hm₂) hc₂
  have huppers : 0 ≤ firstUpper * secondUpper :=
    mul_nonneg hfirstUpper (hquotient.trans hsecond)
  exact mul_le_mul hp hc hcoefficients huppers

theorem original_exceptional_label_scalar
    {branch : TwoDivisorCommonBranch (K := F)} (j : branch.Index)
    {Ray₁ Ray₂ : Type*} [CommGroup Ray₁] [Fintype Ray₁] [CommGroup Ray₂] [Fintype Ray₂]
    (phase₁ : Ray₁ × Ray₁ → Circle) (χ₁ : (Ray₁ × Ray₁) →* Circle)
    (phase₂ : Ray₂ × Ray₂ → Circle) (χ₂ : (Ray₂ × Ray₂) →* Circle)
    (Z firstWeight magnitude firstCost secondCost parentWidth remaining lower : ℝ)
    (hZ : 0 < Z) (hmagnitude : 0 ≤ magnitude) (hfirstCost : 0 ≤ firstCost)
    (hfirst : firstWeight ≤ firstCost /
      (Ideal.absNorm (commonRadical j.1.val.1.1 j.1.val.1.2) : ℝ))
    (hsecond : magnitude / Z ^ parentWidth ≤ secondCost * Z ^ remaining /
      (Ideal.absNorm (commonRadical j.2.2.1.val.1.1 j.2.2.1.val.1.2) : ℝ) * Z ^ (-lower)) :
    firstWeight * ‖(moebius j.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
      ‖(moebius j.2.2.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₂ phase₂ χ₂‖ *
      (magnitude / Z ^ parentWidth) ≤
        firstCost * secondCost * Z ^ remaining * branch.exceptionalDyadWeight Z lower j := by
  have hfinal :
      (firstWeight * (magnitude / Z ^ parentWidth)) *
          (‖(moebius j.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
            ‖(moebius j.2.2.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₂ phase₂ χ₂‖) ≤
        (firstCost / (Ideal.absNorm (commonRadical j.1.val.1.1 j.1.val.1.2) : ℝ) *
          (secondCost * Z ^ remaining /
            (Ideal.absNorm (commonRadical j.2.2.1.val.1.1 j.2.2.1.val.1.2) : ℝ) *
              Z ^ (-lower))) *
          (‖(moebius j.2.1.val : ℂ)‖ * ‖(moebius j.2.2.2.1.val : ℂ)‖) :=
    exceptionalLabel_scalar_product_bound firstWeight (magnitude / Z ^ parentWidth)
      (firstCost / (Ideal.absNorm (commonRadical j.1.val.1.1 j.1.val.1.2) : ℝ))
      (secondCost * Z ^ remaining /
        (Ideal.absNorm (commonRadical j.2.2.1.val.1.1 j.2.2.1.val.1.2) : ℝ) * Z ^ (-lower))
      ‖(moebius j.2.1.val : ℂ)‖ ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖
      ‖(moebius j.2.2.2.1.val : ℂ)‖ ‖fixedPhaseCoefficient Ray₂ phase₂ χ₂‖
      (div_nonneg hmagnitude (Real.rpow_nonneg hZ.le _))
      (div_nonneg hfirstCost (Nat.cast_nonneg _)) hfirst hsecond
      (norm_nonneg (moebius j.2.1.val : ℂ))
      (norm_nonneg (fixedPhaseCoefficient Ray₁ phase₁ χ₁))
      (norm_nonneg (moebius j.2.2.2.1.val : ℂ))
      (norm_nonneg (fixedPhaseCoefficient Ray₂ phase₂ χ₂))
      (fixed_phase_coefficient_norm Ray₁ phase₁ χ₁)
      (fixed_phase_coefficient_norm Ray₂ phase₂ χ₂)
  have hdyad :
      (1 / (Ideal.absNorm (commonRadical j.1.val.1.1 j.1.val.1.2) : ℝ)) *
        ‖(moebius j.2.1.val : ℂ)‖ *
        (1 / (Ideal.absNorm (commonRadical j.2.2.1.val.1.1 j.2.2.1.val.1.2) : ℝ)) *
        ‖(moebius j.2.2.2.1.val : ℂ)‖ * Z ^ (-lower) =
      branch.exceptionalDyadWeight Z lower j := rfl
  refine (exceptionalLabel_scalar_left firstWeight
    ‖(moebius j.2.1.val : ℂ)‖ ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖
    ‖(moebius j.2.2.2.1.val : ℂ)‖ ‖fixedPhaseCoefficient Ray₂ phase₂ χ₂‖
    (magnitude / Z ^ parentWidth)).le.trans (hfinal.trans_eq ?_)
  exact (exceptionalLabel_scalar_right firstCost secondCost (Z ^ remaining) (Z ^ (-lower))
    (Ideal.absNorm (commonRadical j.1.val.1.1 j.1.val.1.2) : ℝ)
    (Ideal.absNorm (commonRadical j.2.2.1.val.1.1 j.2.2.1.val.1.2) : ℝ)
    ‖(moebius j.2.1.val : ℂ)‖ ‖(moebius j.2.2.2.1.val : ℂ)‖).trans
      (congrArg (fun dyad : ℝ => firstCost * secondCost * Z ^ remaining * dyad) hdyad)


variable {ΨL ΨR : Ideal (𝓞 F) →* ℂ} {WL₁ WL₂ WR₁ WR₂ : ℝ → ℂ}
variable (HL : ExceptionalVolumeControl ΨL WL₁ WL₂) (HR : ExceptionalVolumeControl ΨR WR₁ WR₂)
variable (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent)

namespace SecondSideFrame

/-- The public source estimate has no per-leaf exceptional inequality
as a hypothesis.  It is produced from actual atom and valuation data,
then multiplied by the literal first/second divisor and phase factors.
The two allocation equalities prevent replacing the original full
allocations by unrelated labels merely having the same divisor. -/
theorem exceptional_original_label_from_atoms
    (left : SecondSideFrame (V := V) C R Ray .left k)
    (right : SecondSideFrame (V := V) C R Ray .right l)
    (EL : SecondCoefficientComparison left.dictionary)
    (ER : SecondCoefficientComparison right.dictionary)
    (W : ActualSecondRowMass R C kCommonLeft kCommonRight)
    {theta : Finset (HeckeCharacter F)} (Q : PairedFiniteCharacters theta H) (ξ : V)
    (TL : ∀ h : R.exceptionalRows Q, left.source.ExceptionalAt (σ := σ) EL.scale₁ EL.scale₂
      (fun _ => EL.leftWeight) (fun _ => EL.rightWeight) ΨL WL₁ WL₂ ξ h.val)
    (TR : ∀ h : R.exceptionalRows Q, right.source.ExceptionalAt (σ := σ) ER.scale₁ ER.scale₂
      (fun _ => ER.leftWeight) (fun _ => ER.rightWeight) ΨR WR₁ WR₂ ξ h.val)
    (UL : ExceptionalAtomicScales left.allocation) (UR : ExceptionalAtomicScales right.allocation)
    (Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v vStar
      r₁ r₂ divisorLower slotError height stepσ δ parentWidth remaining rowError widthError : ℝ)
    (hZ : 1 < Z) (hv : 0 ≤ v) (hr₁ : 0 ≤ r₁) (hdivisor : divisorLower - r₂ ≤ slotError)
    (hheight : 0 ≤ height)
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
    (hvsum : vStar ≤ c + w + b₂)
    (hmask0 : ∀ h, (TL h).source.mask ≠ ⊥)
    (hmasknorm : ∀ h, (Ideal.absNorm (TL h).source.mask : ℝ) ≤ Z ^ maskExponent)
    (htime : ∀ h, ‖(TL h).source.time‖ ≤ height)
    (hminimum : ∀ h, Z ^ ((m + q) / 4 - vStar - r₁) ≤ (TL h).source.lower)
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
      (left.exceptionalMagnitude right EL ER Q ξ / Z ^ parentWidth) ≤
        firstCost *
          ((W.commonEnvelope * orbitalFieldFactor F) *
            ((W.originalFiber : ℝ) * exceptionalTerminalConstant (V := V) (σ := σ) (η := η) (hS := hS)
              HL HR ε maskExponent hε hmask * (UL.constant * UR.constant) *
              (1 + height) ^ exceptionalTerminalOrder (V := V) (σ := σ) (η := η) (hS := hS)
                HL HR ε maskExponent hε hmask)) *
          Z ^ (remaining + widthError +
            (max (Aexp - (m + q)) 0 + 3 * stepσ + 5 * δ / 6 + ε + slotError)) *
          branch.exceptionalDyadWeight Z divisorLower j := by
  let firstWeight : ℝ := firstOriginalAllowanceWeight Z firstParentWidth firstTotal
    firstProfile j.1.val.1.1 j.1.val.1.2
  let magnitude : ℝ := left.exceptionalMagnitude right EL ER Q ξ
  let secondCost : ℝ :=
    (W.commonEnvelope * orbitalFieldFactor F) *
      ((W.originalFiber : ℝ) * exceptionalTerminalConstant (V := V) (σ := σ) (η := η) (hS := hS)
        HL HR ε maskExponent hε hmask * (UL.constant * UR.constant) *
        (1 + height) ^ exceptionalTerminalOrder (V := V) (σ := σ) (η := η) (hS := hS)
          HL HR ε maskExponent hε hmask)
  let exponent : ℝ := remaining + widthError +
    (max (Aexp - (m + q)) 0 + 3 * stepσ + 5 * δ / 6 + ε + slotError)
  have hsecond : magnitude / Z ^ parentWidth ≤
      secondCost * Z ^ exponent /
        (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ) * Z ^ (-divisorLower) :=
    exceptional_relative_terminal_from_atoms
      (F := F) (A := A) (σ := σ) (η := η) (hS := hS) (V := V)
      (H := H) (ι := ι) (R := R) (C := C) (Ray := Ray)
      (k := k) (l := l) (kCommonLeft := kCommonLeft) (kCommonRight := kCommonRight)
      (theta := theta)
      (HL := HL) (HR := HR) (ε := ε) (maskExponent := maskExponent) (hε := hε) (hmask := hmask)
      left right EL ER W Q ξ TL TR UL UR
      Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v vStar
      r₁ r₂ divisorLower slotError height stepσ δ parentWidth remaining rowError widthError
      hZ hv hr₁ hdivisor hheight hleftAtoms hrightAtoms hexponent hgcd hunit
      base hclass hfactor hwindow hcutoff hF₁ hF₂ hvsum hmask0 hmasknorm htime hminimum
      hradius hcentral hdyad hremaining hwidth
  have hfirst : firstWeight ≤
      firstCost / (Ideal.absNorm (commonRadical j.1.val.1.1 j.1.val.1.2) : ℝ) :=
    firstOriginalAllowanceWeight_le_radical (F := F) Z firstParentWidth firstTotal
      firstProfile firstCost hZ hfirstCost hfirstProfile j.1.val.1.1 j.1.val.1.2
      hfirstLeft hfirstRight hfirstSupport
  have hradical : (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ) =
      (Ideal.absNorm (commonRadical j.2.2.1.val.1.1 j.2.2.1.val.1.2) : ℝ) :=
    congrArg (fun I : Ideal (𝓞 F) => (Ideal.absNorm I : ℝ))
      (congrArg₂ (fun I J : Ideal (𝓞 F) => commonRadical I J) hleftIdeal hrightIdeal)
  have hsecondIndex : magnitude / Z ^ parentWidth ≤
      secondCost * Z ^ exponent /
        (Ideal.absNorm (commonRadical j.2.2.1.val.1.1 j.2.2.1.val.1.2) : ℝ) *
        Z ^ (-divisorLower) :=
    exceptionalLabel_denominator_transport hradical hsecond
  have hlabel : firstWeight * ‖(moebius j.2.1.val : ℂ)‖ *
      ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ * ‖(moebius j.2.2.2.1.val : ℂ)‖ *
      ‖fixedPhaseCoefficient Ray phase₂ left.phaseCharacter‖ * (magnitude / Z ^ parentWidth) ≤
      firstCost * secondCost * Z ^ exponent * branch.exceptionalDyadWeight Z divisorLower j :=
    original_exceptional_label_scalar (F := F) (branch := branch)
      (Ray₁ := Ray₁) (Ray₂ := Ray) j phase₁ χ₁ phase₂ left.phaseCharacter
      Z firstWeight magnitude firstCost secondCost parentWidth exponent divisorLower
      (zero_lt_one.trans hZ) (left.exceptionalMagnitude_nonneg right EL ER Q ξ)
      hfirstCost hfirst hsecondIndex
  have hdone : firstWeight * ‖(moebius S : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
      ‖(moebius left.allocation.divisor : ℂ)‖ *
      ‖fixedPhaseCoefficient Ray phase₂ left.phaseCharacter‖ * (magnitude / Z ^ parentWidth) ≤
      firstCost * secondCost * Z ^ exponent * branch.exceptionalDyadWeight Z divisorLower j :=
    exceptionalLabel_divisor_transport
      (sourceFirst := ‖(moebius S : ℂ)‖)
      (targetFirst := ‖(moebius j.2.1.val : ℂ)‖)
      (sourceSecond := ‖(moebius left.allocation.divisor : ℂ)‖)
      (targetSecond := ‖(moebius j.2.2.2.1.val : ℂ)‖)
      firstWeight
      ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ ‖fixedPhaseCoefficient Ray phase₂ left.phaseCharacter‖
      (magnitude / Z ^ parentWidth)
      (firstCost * secondCost * Z ^ exponent * branch.exceptionalDyadWeight Z divisorLower j)
      (congrArg (fun I : Ideal (𝓞 F) => ‖(moebius I : ℂ)‖) hSindex)
      (congrArg (fun I : Ideal (𝓞 F) => ‖(moebius I : ℂ)‖) hleftDivisor) hlabel
  simpa only [firstWeight, magnitude, secondCost, exponent] using hdone

end SecondSideFrame
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.exceptional_original_label_from_atoms
