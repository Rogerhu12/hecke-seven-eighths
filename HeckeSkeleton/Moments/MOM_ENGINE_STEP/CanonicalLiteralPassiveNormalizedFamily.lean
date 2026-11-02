import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveFrameEnergy
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridNormalizedProduction

set_option linter.unusedSectionVars false
set_option quotPrecheck false

/-!
# The normalized family of independent passive allocations

The two passive divisors are independent.  The finite carrier consists
of the original nonzero left and right allocation labels and their two
rectangle choices.  Each side uses the frame already stored at that
label.  Its calibration and capacity are constructed before the common
active filter chooses any children.

Finite Minkowski is applied on the original row measure.  The resulting
family retains the original two Fourier variables, the full Gauss
normalizers, and both allocation divisors.  There is no identification
of the two new divisors with the earlier common second divisor.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

namespace CanonicalLiteralPassiveNormalizedFamily

open CanonicalLiteralPassiveSource CanonicalLiteralPassiveFrames
open CanonicalLiteralPassiveNonzero CanonicalLiteralPassiveFrameEnergy

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (R : ActualSecondCorrelationRows A σ H ι)
variable {k l : ℕ}
variable {leftAtoms : CanonicalLiteralRectangles.Atoms (K := K) k}
variable {rightAtoms : CanonicalLiteralRectangles.Atoms (K := K) l}
variable (leftProfiles : leftAtoms.ProfileData) (rightProfiles : rightAtoms.ProfileData)
variable (leftAllocation : ActualColumnAllocation K k)
variable (rightAllocation : ActualColumnAllocation K l)
variable (leftPaid : FixedChildCharacters K leftAllocation.keep.card)
variable (rightPaid : FixedChildCharacters K rightAllocation.keep.card)
variable (leftMask rightMask : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (leftSign rightSign : ℝ)

abbrev SideLabel {n : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) n}
    (W : d.ProfileData) (B : ActualColumnAllocation K n)
    (A : SArithmeticData K) (M : HeckeGeneral.Analysis.NonzeroIdeal K) :=
  (nonzeroLabels W B A M) × Bool

abbrev PairLabel :=
  SideLabel leftProfiles leftAllocation A leftMask ×
    SideLabel rightProfiles rightAllocation A rightMask

local notation "LeftLabel" => SideLabel leftProfiles leftAllocation A leftMask
local notation "RightLabel" => SideLabel rightProfiles rightAllocation A rightMask
local notation "Labels" => PairLabel (A := A) leftProfiles rightProfiles leftAllocation rightAllocation
  leftMask rightMask
local notation "leftFrame" => fun b : LeftLabel =>
  frame leftProfiles leftAllocation A leftPaid C R .left leftMask b.1.val leftSign b.2
local notation "rightFrame" => fun b : RightLabel =>
  frame rightProfiles rightAllocation A rightPaid C R .right rightMask b.1.val rightSign b.2

variable {ω ψ : HeckeCharacter K}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)}
variable (leftNormalization : ∀ b : SideLabel leftProfiles leftAllocation A leftMask,
  SecondSideNormalization
    (frame leftProfiles leftAllocation A leftPaid C R .left leftMask b.1.val leftSign b.2)
    ω ψ rowDomain heightDomain window orders)
variable (rightNormalization : ∀ b : SideLabel rightProfiles rightAllocation A rightMask,
  SecondSideNormalization
    (frame rightProfiles rightAllocation A rightPaid C R .right rightMask b.1.val rightSign b.2)
    ω ψ rowDomain heightDomain window orders)
variable (sameBase : rightAtoms.base = leftAtoms.base)

/-- The source, calibration and capacity fields refer to the same
stored independent allocation on each side. -/
def family : ActualNormalizedPairFamily A σ (WithLp 2 (ℝ × ℝ)) Labels ω ψ leftAtoms.base where
  LeftRow _ := R.live
  RightRow _ := R.live
  leftSlots _ := leftAllocation.keep.card
  rightSlots _ := rightAllocation.keep.card
  leftSource b := (leftFrame b.1).source
  rightSource b := (rightFrame b.2).source
  leftCalibration b := (leftNormalization b.1).calibration
  rightCalibration b := (rightNormalization b.2).calibration
  leftCapacity b := (leftNormalization b.1).normalizedCapacityData
  rightCapacity b := (rightNormalization b.2).normalizedCapacityData
  left_base _ := rfl
  right_base _ := sameBase
  leftNormalizer b := (leftFrame b.1).normalizer
  rightNormalizer b := (rightFrame b.2).normalizer

local notation "production" => family C R leftProfiles rightProfiles leftAllocation
  rightAllocation leftPaid rightPaid leftMask rightMask leftSign rightSign
  leftNormalization rightNormalization sameBase

theorem sourcePair (parentWidth : ℝ) (b : Labels) (ξ : WithLp 2 (ℝ × ℝ)) :
    (production).sourcePair parentWidth b ξ =
      Real.sqrt ((leftFrame b.1).energy ξ) * Real.sqrt ((rightFrame b.2).energy ξ) /
        leftAtoms.base ^ parentWidth := by
  sorry

theorem sum_sourcePair (parentWidth : ℝ) (ξ : WithLp 2 (ℝ × ℝ)) :
    (∑ b : Labels, (production).sourcePair parentWidth b ξ) =
      ((∑ b : LeftLabel, Real.sqrt ((leftFrame b).energy ξ)) *
        (∑ b : RightLabel, Real.sqrt ((rightFrame b).energy ξ))) /
          leftAtoms.base ^ parentWidth := by
  sorry

/-- The exact passive polynomials still contain their complete
centered difference and the original row weight. -/
def integrand (ξ : WithLp 2 (ℝ × ℝ)) : ℝ :=
  Real.sqrt (∑ h : R.live, ‖R.weight h.val * R.correlation h.val‖ *
      ‖passiveColumn (σ := σ) leftProfiles leftAllocation leftPaid leftMask
        (R.factor C h.val) (R.extractedRow C h).element leftSign false ξ‖ ^ 2) *
    Real.sqrt (∑ h : R.live, ‖R.weight h.val * R.correlation h.val‖ *
      ‖passiveColumn (σ := σ) rightProfiles rightAllocation rightPaid rightMask
        (-(R.factor C h.val)) (R.extractedRow C h).element rightSign true ξ‖ ^ 2)

/-- No source bound is an input: both finite Minkowski bounds are
proved on the fixed original row carrier. -/
theorem integrand_le_sourcePairs (parentWidth : ℝ) (ξ : WithLp 2 (ℝ × ℝ)) :
    integrand C R leftProfiles rightProfiles leftAllocation rightAllocation
      leftPaid rightPaid leftMask rightMask leftSign rightSign ξ / leftAtoms.base ^ parentWidth ≤
      ∑ b : Labels, (production).sourcePair parentWidth b ξ := by
  sorry

/-- The active filter is computed only after every passive label has
its actual capacity input. The children and removals precede ξ. -/
theorem integrand_le_normalized_family (parentWidth : ℝ) (ξ : WithLp 2 (ℝ × ℝ)) :
    integrand C R leftProfiles rightProfiles leftAllocation rightAllocation
      leftPaid rightPaid leftMask rightMask leftSign rightSign ξ / leftAtoms.base ^ parentWidth ≤
      ∑ b : (production).active Finset.univ,
        (production).weight Finset.univ parentWidth b * (production).envelope Finset.univ b ξ *
          (production).childPair Finset.univ b ξ := by
  sorry

theorem in_fixed_window
    (leftHeight : ∀ b ξ, (leftNormalization b).calibration.height ξ ∈ heightDomain)
    (rightHeight : ∀ b ξ, (rightNormalization b).calibration.height ξ ∈ heightDomain) :
    ∀ b : (production).active Finset.univ, ∀ ξ,
      InFixedProfileWindow rowDomain Set.univ window orders
        ((production).leftData Finset.univ b ξ) ∧
      InFixedProfileWindow rowDomain Set.univ window orders
        ((production).rightData Finset.univ b ξ) := by
  sorry

end CanonicalLiteralPassiveNormalizedFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveNormalizedFamily.family
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveNormalizedFamily.integrand_le_sourcePairs
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveNormalizedFamily.integrand_le_normalized_family
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveNormalizedFamily.in_fixed_window
