import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OrdinaryExceptionalLabelIntegral
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ConstantCommonLeaf

/-!
# The ordinary exceptional terminal of the same literal hybrid leaf

The binding contains only original row, column, coefficient and
location identities.  Its coefficients are the two ordinary complete
columns.  Constant common-atom extraction preserves the actual outer
scalar and both original Fourier measures.

The ordinary-range terminal follows from the original individual atom
and valuation data.  Its bound retains both divisor/phase coefficients
and the actual full arithmetic index, without a centered minimum or
height window and without a per-leaf estimate as an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {H ι U V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
local notation "W" => WithLp 2 (U × V)

namespace ActualHybridLeaf

variable (leaf : ActualHybridLeaf K H U V)
variable (left : SecondSideFrame (V := W) C R Ray .left leaf.leftSlots)
variable (right : SecondSideFrame (V := W) C R Ray .right leaf.rightSlots)
variable {theta : Finset (HeckeCharacter K)} (Q : PairedFiniteCharacters theta H)

/-- These fields identify only raw finite atoms.  There is no magnitude,
integral, parent inequality, or terminal estimate among the premises. -/
structure OrdinaryExceptionalBinding : Prop where
  rows : leaf.rows = R.rows
  left_columns : leaf.left = left.allocation.columns
  right_columns : leaf.right = right.allocation.columns
  exceptional : ∀ h ∈ leaf.rows, leaf.exceptional h ↔ Q.exceptional h
  rowWeight : ∀ h ∈ leaf.rows, leaf.rowWeight h = R.weight h * R.correlation h
  leftCoefficient : ∀ h ∈ leaf.rows, ∀ i ∈ leaf.left,
    leaf.leftCoefficient h i = left.coefficient h i
  rightCoefficient : ∀ h ∈ leaf.rows, ∀ j ∈ leaf.right,
    star (leaf.rightCoefficient h j) = right.coefficient h j
  leftPoint : ∀ h ∈ leaf.rows, ∀ i ∈ leaf.left,
    WithLp.toLp 2 (leaf.leftFirst h i, leaf.leftSecond h i) =
      rawSourceLocation (left.leftLocation h) (left.rightLocation h) (left.slotLocation h) i
  rightPoint : ∀ h ∈ leaf.rows, ∀ j ∈ leaf.right,
    WithLp.toLp 2 (-leaf.rightFirst h j, leaf.rightSecond h j) =
      rawSourceLocation (right.leftLocation h) (right.rightLocation h) (right.slotLocation h) j

namespace OrdinaryExceptionalBinding

variable {leaf left right Q} (b : leaf.OrdinaryExceptionalBinding left right Q)

include b

theorem exceptional_rows :
    leaf.rows.filter leaf.exceptional = R.rows.filter Q.exceptional := by
  ext h
  constructor
  · intro hh
    obtain ⟨hm, he⟩ := Finset.mem_filter.mp hh
    exact Finset.mem_filter.mpr ⟨b.rows ▸ hm, (b.exceptional h hm).mp he⟩
  · intro hh
    obtain ⟨hm, he⟩ := Finset.mem_filter.mp hh
    have hl : h ∈ leaf.rows := b.rows.symm ▸ hm
    exact Finset.mem_filter.mpr ⟨hl, (b.exceptional h hl).mpr he⟩

/-- The two complete ordinary columns are compared before taking their
norms.  No Cauchy estimate is applied to the exceptional rows. -/
theorem exceptionalIntegrand_eq (z : U × V) :
    leaf.exceptionalIntegrand z =
      left.ordinaryExceptionalMagnitude right Q (WithLp.toLp 2 z) := by
  have hfull : leaf.exceptionalIntegrand z =
      jointColumnPairMagnitude (R.rows.filter Q.exceptional)
        left.allocation.columns right.allocation.columns
        (fun h => R.weight h * R.correlation h)
        (left.coefficient) (right.coefficient)
        (fun h => rawSourceLocation (left.leftLocation h) (left.rightLocation h)
          (left.slotLocation h))
        (fun h => rawSourceLocation (right.leftLocation h) (right.rightLocation h)
          (right.slotLocation h)) (WithLp.toLp 2 z) := by
    unfold ActualHybridLeaf.exceptionalIntegrand
    rw [← b.exceptional_rows, ← b.left_columns, ← b.right_columns]
    unfold jointColumnPairMagnitude
    apply Finset.sum_congr rfl
    intro h hh
    have hm := (Finset.mem_filter.mp hh).1
    have hl :
        jointFourierColumn leaf.left (leaf.leftCoefficient h)
          (fun i => WithLp.toLp 2 (leaf.leftFirst h i, leaf.leftSecond h i))
          (WithLp.toLp 2 z) =
        jointFourierColumn leaf.left (left.coefficient h)
          (rawSourceLocation (left.leftLocation h) (left.rightLocation h)
            (left.slotLocation h)) (WithLp.toLp 2 z) := by
      unfold jointFourierColumn
      apply Finset.sum_congr rfl
      intro i hi
      rw [b.leftCoefficient h hm i hi, b.leftPoint h hm i hi]
    have hr :
        jointFourierColumn leaf.right (fun j => star (leaf.rightCoefficient h j))
          (fun j => WithLp.toLp 2 (-leaf.rightFirst h j, leaf.rightSecond h j))
          (WithLp.toLp 2 z) =
        jointFourierColumn leaf.right (right.coefficient h)
          (rawSourceLocation (right.leftLocation h) (right.rightLocation h)
            (right.slotLocation h)) (WithLp.toLp 2 z) := by
      unfold jointFourierColumn
      apply Finset.sum_congr rfl
      intro j hj
      rw [b.rightCoefficient h hm j hj, b.rightPoint h hm j hj]
    rw [b.rowWeight h hm, hl, hr]
  exact hfull.trans (R.pair_magnitude_live
    left.allocation.columns right.allocation.columns
    (left.coefficient) (right.coefficient)
    (fun h => rawSourceLocation (left.leftLocation h) (left.rightLocation h)
      (left.slotLocation h))
    (fun h => rawSourceLocation (right.leftLocation h) (right.rightLocation h)
      (right.slotLocation h)) Q.exceptional (WithLp.toLp 2 z))

variable [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The literal exceptional cost is integrated against its own two
original kernels.  This equality is available before any volume bound. -/
theorem exceptionalCost_eq :
    leaf.exceptionalCost = leaf.weight *
      ∫ z : U × V, left.ordinaryExceptionalMagnitude right Q (WithLp.toLp 2 z)
        ∂nestedFourierMeasure leaf.firstKernel leaf.secondKernel := by
  unfold ActualHybridLeaf.exceptionalCost ActualHybridLeaf.measure
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall b.exceptionalIntegrand_eq)

end OrdinaryExceptionalBinding

namespace ConstantAtomExtraction

variable {leaf} (X : leaf.ConstantAtomExtraction)
variable (left : SecondSideFrame (V := W) C R Ray .left X.leaf.leftSlots)
variable (right : SecondSideFrame (V := W) C R Ray .right X.leaf.rightSlots)
variable [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Exact constant-atom extraction and the raw atom binding reach the
same original exceptional cost.  The outer weight and both measures
are unchanged by this already proved extraction. -/
theorem ordinaryExceptionalCost_eq_frames
    (b : X.leaf.OrdinaryExceptionalBinding left right Q) :
    leaf.exceptionalCost = leaf.weight *
      ∫ z : U × V, left.ordinaryExceptionalMagnitude right Q (WithLp.toLp 2 z)
        ∂nestedFourierMeasure leaf.firstKernel leaf.secondKernel :=
  X.exceptionalCost_eq.trans b.exceptionalCost_eq

end ConstantAtomExtraction
end ActualHybridLeaf

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.OrdinaryExceptionalBinding.exceptionalIntegrand_eq
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.OrdinaryExceptionalBinding.exceptionalCost_eq
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.ConstantAtomExtraction.ordinaryExceptionalCost_eq_frames

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
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
local notation "V" => WithLp 2 (U × E)
variable {ΨL ΨR : Ideal (𝓞 F) →* ℂ} {WL₁ WL₂ WR₁ WR₂ : ℝ → ℂ}
variable (HL : ExceptionalVolumeControl ΨL WL₁ WL₂) (HR : ExceptionalVolumeControl ΨR WR₁ WR₂)

/-- An exact outer scalar identity joins the actual source estimate to
this original leaf.  The complete occurrence allocations are identified
after their literal inclusion into the earlier arithmetic cap. -/
theorem ordinary_exceptional_cost_from_original_atoms
    (leaf : ActualHybridLeaf F H U E) (X : leaf.ConstantAtomExtraction)
    (left : SecondSideFrame (V := V) C R Ray .left leaf.leftSlots)
    (right : SecondSideFrame (V := V) C R Ray .right leaf.rightSlots)
    (W : ActualSecondRowMass R C kCommonLeft kCommonRight)
    {theta : Finset (HeckeCharacter F)} (Q : PairedFiniteCharacters theta H)
    (binding : X.leaf.OrdinaryExceptionalBinding left right Q)
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
    (hleftOccurrences : leaf.leftSlots + 2 ≤ branch.leftOccurrences
      j.1.val j.2.1.val j.2.2.1.val j.2.2.2.1.val)
    (hrightOccurrences : leaf.rightSlots + 2 ≤ branch.rightOccurrences
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
    (factor : ℝ) (hfactor0 : 0 ≤ factor)
    (houter : leaf.weight / Z ^ firstParentWidth =
      factor *
        (firstOriginalAllowanceWeight Z firstParentWidth firstTotal firstProfile
          j.1.val.1.1 j.1.val.1.2 *
          ‖(moebius S : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
          ‖(moebius left.allocation.divisor : ℂ)‖ *
          ‖fixedPhaseCoefficient Ray phase₂ left.phaseCharacter‖) / Z ^ parentWidth) :
    leaf.exceptionalCost / Z ^ firstParentWidth ≤
      factor * (firstCost *
        ((W.commonEnvelope * orbitalFieldFactor F) *
          ((W.originalFiber : ℝ) * ordinaryExceptionalConstant HL HR * (UL.constant * UR.constant))) *
        Z ^ (remaining + widthError +
          (3 * stepσ + 5 * δ / 6 + slotError)) *
        branch.exceptionalDyadWeight Z divisorLower j *
        (exceptionalFourierControl (U := U) (E := E) 0 0).constant *
        (exceptionalFourierControl (U := U) (E := E) 0 0).leftSeminorms.sup
          (schwartzSeminormFamily ℝ U ℂ) leaf.firstKernel *
        (exceptionalFourierControl (U := U) (E := E) 0 0).rightSeminorms.sup
          (schwartzSeminormFamily ℝ E ℂ) leaf.secondKernel) := by
  have hsource := SecondSideFrame.ordinary_exceptional_original_label_integral_from_atoms
    (HL := HL) (HR := HR) left right W Q TL TR UL UR
    Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v
    r₁ r₂ divisorLower slotError stepσ δ parentWidth remaining rowError widthError
    hZ hv hr₁ hdivisor hA hc hw hb₂ hleftAtoms hrightAtoms hexponent hgcd hunit
    base hclass hfactor hwindow hcutoff hF₁ hF₂ hradius hcentral hdyad hremaining hwidth
    j S hSindex hleftIdeal hrightIdeal hleftDivisor hrightDivisor
    hleftOccurrences hrightOccurrences hleftAllocation hrightAllocation
    phase₁ χ₁ phase₂ hphase firstParentWidth firstTotal firstProfile firstCost hfirstCost
    hfirstProfile hfirstLeft hfirstRight hfirstSupport leaf.firstKernel leaf.secondKernel
  have hbinding := ActualHybridLeaf.ConstantAtomExtraction.ordinaryExceptionalCost_eq_frames
    (X := X) (left := left) (right := right) (Q := Q) binding
  let scalar := firstOriginalAllowanceWeight Z firstParentWidth firstTotal firstProfile
      j.1.val.1.1 j.1.val.1.2 *
    ‖(moebius S : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
    ‖(moebius left.allocation.divisor : ℂ)‖ *
    ‖fixedPhaseCoefficient Ray phase₂ left.phaseCharacter‖
  calc
    _ = (leaf.weight / Z ^ firstParentWidth) *
        ∫ z : U × E, left.ordinaryExceptionalMagnitude right Q (WithLp.toLp 2 z)
          ∂nestedFourierMeasure leaf.firstKernel leaf.secondKernel := by
      rw [hbinding]
      ring
    _ = factor * ∫ z : U × E,
        scalar * (left.ordinaryExceptionalMagnitude right Q (WithLp.toLp 2 z) / Z ^ parentWidth)
          ∂nestedFourierMeasure leaf.firstKernel leaf.secondKernel := by
      rw [houter, integral_const_mul, integral_div]
      dsimp only [scalar]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsource hfactor0

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ordinary_exceptional_cost_from_original_atoms
