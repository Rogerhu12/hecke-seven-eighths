import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalExceptionalSavingCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalAtomEnvelope

set_option linter.unusedSectionVars false

/-!
# Original plain scales and the exact exceptional extraction lengths

The cancellation side is the one with the smaller actual second common
ideal length.  Its extraction length is the first common length plus
the actual amplifier valuation length plus that smaller second length.
All four original plain scales are divided by the same corresponding
plain ideal before and after the final divisor allocation.

The final extraction cost is read from the actual allocation: the sum
of the two plain-divisor lengths plus half the sum of the actual frozen
prime lengths and their original slot lengths.  This is the exponent
of the actual frozen coefficients and retained prime atoms.  It pays
both the minimum plain-scale loss and the final divisor count.  The
only error in the latter comes from individual frozen-prime annuli.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]

private theorem original_plain_log_mul (Z : ℝ) (I J : Ideal (𝓞 K))
    (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealLogLength Z (I * J) = idealLogLength Z I + idealLogLength Z J := by
  sorry

private theorem original_plain_log_le_of_dvd (Z : ℝ) (hZ : 1 < Z)
    (I J : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0) (h : I ∣ J) :
    idealLogLength Z I ≤ idealLogLength Z J := by
  sorry

namespace ActualColumnAllocation

variable {k : ℕ} (B : ActualColumnAllocation K k)

def plainExtractionLength (Z : ℝ) : ℝ :=
  idealLogLength Z (B.plainDivisor 0).val +
    idealLogLength Z (B.plainDivisor (Fin.succ 0)).val

def frozenPrimeLength (Z : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ \ B.keep, idealLogLength Z (B.witness.2 i).asIdeal

def frozenSlotLength (length : Fin k → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ \ B.keep, length i

/-- The exact cost of the frozen scalar, the rectangle product and
the retained centrally normalized prime atoms. -/
def rawExtractionLength (Z : ℝ) (length : Fin k → ℝ) : ℝ :=
  B.plainExtractionLength Z + (B.frozenPrimeLength Z + B.frozenSlotLength length) / 2

theorem frozenIdeal_length (Z : ℝ) :
    idealLogLength Z B.frozenIdeal = B.plainExtractionLength Z + B.frozenPrimeLength Z := by
  sorry

theorem slotLength_split (length : Fin k → ℝ) :
    (∑ i, length i) = B.frozenSlotLength length +
      ∑ j : Fin B.keep.card, length (SlotRestriction.index B.keep j) := by
  sorry

theorem plainExtractionLength_nonneg (Z : ℝ) (hZ : 1 < Z) :
    0 ≤ B.plainExtractionLength Z := by
  sorry

theorem frozenPrimeLength_nonneg (Z : ℝ) (hZ : 1 < Z) :
    0 ≤ B.frozenPrimeLength Z := by
  sorry

theorem rawExtractionLength_nonneg (Z : ℝ) (hZ : 1 < Z)
    (length : Fin k → ℝ) (hlength : ∀ i, 0 ≤ length i) :
    0 ≤ B.rawExtractionLength Z length := by
  sorry

theorem plainDivisor_length_le_rawExtraction (Z : ℝ) (hZ : 1 < Z)
    (length : Fin k → ℝ) (hlength : ∀ i, 0 ≤ length i) :
    idealLogLength Z (B.plainDivisor 0).val ≤ B.rawExtractionLength Z length ∧
    idealLogLength Z (B.plainDivisor (Fin.succ 0)).val ≤ B.rawExtractionLength Z length := by
  sorry

/-- Every prime of the actual second divisor is paid in the frozen
ideal; no divisor-count estimate is postulated. -/
theorem divisor_length_le_frozen (Z : ℝ) (hZ : 1 < Z)
    (hsq : Squarefree B.divisor)
    (hselection : B.selection ∈ AllocationMass.idealAllocations B.divisor (k + 2)) :
    idealLogLength Z B.divisor ≤ B.plainExtractionLength Z + B.frozenPrimeLength Z := by
  sorry

/-- Only the original upper annulus of each frozen prime is spent.
The actual frozen-slot error is the sum of these individual errors. -/
theorem divisor_window_of_prime_windows (Z : ℝ) (hZ : 1 < Z)
    (length error : Fin k → ℝ) (lower : ℝ)
    (hsq : Squarefree B.divisor)
    (hselection : B.selection ∈ AllocationMass.idealAllocations B.divisor (k + 2))
    (hdivisor : Z ^ lower ≤ (Ideal.absNorm B.divisor : ℝ))
    (hprime : ∀ i ∈ Finset.univ \ B.keep,
      (Ideal.absNorm (B.witness.2 i).asIdeal : ℝ) ≤ Z ^ (length i + 2 * error i)) :
    lower - B.rawExtractionLength Z length ≤ ∑ i ∈ Finset.univ \ B.keep, error i := by
  sorry

/-- The common lower scale is computed from all four literal scales;
formally impossible rectangles remain in this minimum. -/
def fourPlainLower (X₁ X₂ Y₁ Y₂ : ℝ) : ℝ :=
  min (min (X₁ / idealNorm K (B.plainDivisor 0))
      (X₂ / idealNorm K (B.plainDivisor (Fin.succ 0))))
    (min (Y₁ / idealNorm K (B.plainDivisor 0))
      (Y₂ / idealNorm K (B.plainDivisor (Fin.succ 0))))

theorem fourPlainLower_pos {X₁ X₂ Y₁ Y₂ : ℝ}
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    0 < B.fourPlainLower X₁ X₂ Y₁ Y₂ := by
  sorry

theorem fourPlainLower_lower {L X₁ X₂ Y₁ Y₂ : ℝ}
    (hX₁ : L ≤ X₁ / idealNorm K (B.plainDivisor 0))
    (hX₂ : L ≤ X₂ / idealNorm K (B.plainDivisor (Fin.succ 0)))
    (hY₁ : L ≤ Y₁ / idealNorm K (B.plainDivisor 0))
    (hY₂ : L ≤ Y₂ / idealNorm K (B.plainDivisor (Fin.succ 0))) :
    L ≤ B.fourPlainLower X₁ X₂ Y₁ Y₂ := by
  sorry

private theorem original_quotient_lower (Z : ℝ) (hZ : 1 < Z)
    (L v r X : ℝ) (D : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hX : Z ^ (L - v) ≤ X) (hD : idealLogLength Z D.val ≤ r) :
    Z ^ (L - v - r) ≤ X / idealNorm K D := by
  sorry

/-- This fills the minimum window from the four pre-allocation scales
and the computed cost of this very allocation. -/
theorem fourPlainLower_window (Z : ℝ) (hZ : 1 < Z)
    (length : Fin k → ℝ) (hlength : ∀ i, 0 ≤ length i)
    (L v X₁ X₂ Y₁ Y₂ : ℝ)
    (hX₁ : Z ^ (L - v) ≤ X₁) (hX₂ : Z ^ (L - v) ≤ X₂)
    (hY₁ : Z ^ (L - v) ≤ Y₁) (hY₂ : Z ^ (L - v) ≤ Y₂) :
    Z ^ (L - v - B.rawExtractionLength Z length) ≤ B.fourPlainLower X₁ X₂ Y₁ Y₂ := by
  sorry

/-- The actual atom exponents, with the original annulus and profile
constants kept in the constant rather than moved into a new length. -/
def originalAtomicScales (Z plainTotal : ℝ) (length : Fin k → ℝ)
    (hlength : ∀ i, 0 ≤ length i) (annulus profile : Fin k → ℝ)
    (hannulus : ∀ i, 1 ≤ annulus i) (hprofile : ∀ i, 0 ≤ profile i) :
    ExceptionalAtomicScales B where
  annulus := annulus
  profileSquare i := profile i ^ 2
  annulus_nonneg i := zero_le_one.trans (hannulus i)
  profileSquare_nonneg i := sq_nonneg _
  frozenExponent := idealLogLength Z B.frozenIdeal
  rootConstant := 1
  rootExponent := (plainTotal - B.plainExtractionLength Z) / 2
  rootConstant_nonneg := zero_le_one
  cutoffConstant j := annulus (SlotRestriction.index B.keep j)
  cutoffExponent j := length (SlotRestriction.index B.keep j)
  atomConstant j := profile (SlotRestriction.index B.keep j)
  atomExponent j := -length (SlotRestriction.index B.keep j) / 2
  cutoffConstant_one j := hannulus _
  cutoffExponent_nonneg j := hlength _
  atomConstant_nonneg j := hprofile _

theorem originalAtomicScales_exponent (Z plainTotal : ℝ) (length : Fin k → ℝ)
    (hlength : ∀ i, 0 ≤ length i) (annulus profile : Fin k → ℝ)
    (hannulus : ∀ i, 1 ≤ annulus i) (hprofile : ∀ i, 0 ≤ profile i) :
    (B.originalAtomicScales Z plainTotal length hlength annulus profile hannulus hprofile).exponent =
      (plainTotal + ∑ i, length i) / 2 - B.rawExtractionLength Z length := by
  sorry

theorem rectangle_product_eq_power (Z : ℝ) (hZ : 1 < Z)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    (X₁ / idealNorm K (B.plainDivisor 0)) *
        (X₂ / idealNorm K (B.plainDivisor (Fin.succ 0))) =
      Z ^ (Real.log (X₁ * X₂) / Real.log Z - B.plainExtractionLength Z) := by
  sorry

end ActualColumnAllocation

namespace AllocatedExceptionalSource

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Ψ : Ideal (𝓞 K) →* ℂ} {W₁ W₂ : ℝ → ℂ} {g h' : A.R} {k : ℕ}
variable (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h' k)

/-- The computed exponent dictionary satisfies the real atomic-control
record using only individual original coefficient, profile and annulus
bounds.  The frozen norm and rectangle-product fields are proved. -/
def atomicControlOfOriginalWindows
    (C : A.GeneralArithmeticContext σ η hS) (Z : ℝ) (hZ : 1 < Z)
    (hbase : s.Zslot = Z) (hX₁ : 0 < s.X₁) (hX₂ : 0 < s.X₂)
    (hlength : ∀ i, 0 ≤ s.length i) (annulus profile : Fin k → ℝ)
    (hannulus : ∀ i, 1 ≤ annulus i) (hprofile : ∀ i, 0 ≤ profile i)
    (hplain₁ : ‖sourcePlainCoefficient s.characters.plain s.characters.plainTwist
      s.characters.mask (s.allocation.plainDivisor 0)‖ ≤ 1)
    (hplain₂ : ‖sourcePlainCoefficient s.characters.plain s.characters.plainTwist
      s.characters.mask (s.allocation.plainDivisor (Fin.succ 0))‖ ≤ 1)
    (hfrozenCoefficient : ∀ i ∈ Finset.univ \ s.allocation.keep,
      ‖sourcePrimeCoefficient (s.characters.slot i) (s.characters.slotTwist i)
        s.characters.mask (s.allocation.witness.2 i)‖ ≤ 1)
    (hfrozenAnnulus : ∀ i ∈ Finset.univ \ s.allocation.keep,
      (Ideal.absNorm (s.allocation.witness.2 i).asIdeal : ℝ) ≤ annulus i * Z ^ s.length i)
    (hfrozenProfile : ∀ i ∈ Finset.univ \ s.allocation.keep,
      ‖s.w i (s.allocation.witness.2 i)‖ ≤ profile i)
    (hliveAnnulus : ∀ j, ∀ p ∈ s.allocation.childSlots j,
      (Ideal.absNorm p.asIdeal : ℝ) ≤ annulus (SlotRestriction.index s.allocation.keep j) *
        Z ^ s.length (SlotRestriction.index s.allocation.keep j))
    (hliveCoefficient : ∀ j, ∀ p ∈ s.allocation.childSlots j,
      ‖sourcePrimeCoefficient ((s.characters.restrictSlots s.allocation.keep).slot j)
        ((s.characters.restrictSlots s.allocation.keep).slotTwist j)
        (s.characters.restrictSlots s.allocation.keep).mask p‖ ≤ 1)
    (hliveProfile : ∀ j, ∀ p ∈ s.allocation.childSlots j,
      ‖s.w (SlotRestriction.index s.allocation.keep j) p‖ ≤
        profile (SlotRestriction.index s.allocation.keep j)) :
    s.AtomicControl Z (s.allocation.originalAtomicScales Z
      (Real.log (s.X₁ * s.X₂) / Real.log Z) s.length hlength annulus profile hannulus hprofile) where
  base_pos := by rw [hbase]; exact zero_lt_one.trans hZ
  plain₁ := hplain₁
  plain₂ := hplain₂
  frozen_prime := hfrozenCoefficient
  frozen_annulus := by simpa only [hbase] using hfrozenAnnulus
  frozen_profile i hi := pow_le_pow_left₀ (norm_nonneg _) (hfrozenProfile i hi) 2
  frozen_norm := (rpow_idealLogLength Z hZ s.allocation.frozenIdeal
    s.allocation.frozenIdeal_ne_zero).le
  rectangle_product := by
    change s.product ≤ 1 ^ 2 *
      Z ^ (2 * ((Real.log (s.X₁ * s.X₂) / Real.log Z -
        s.allocation.plainExtractionLength Z) / 2))
    rw [one_pow, one_mul,
      show 2 * ((Real.log (s.X₁ * s.X₂) / Real.log Z -
        s.allocation.plainExtractionLength Z) / 2) =
        Real.log (s.X₁ * s.X₂) / Real.log Z - s.allocation.plainExtractionLength Z by ring]
    exact (s.productX.symm.trans
      (s.allocation.rectangle_product_eq_power Z hZ s.X₁ s.X₂ hX₁ hX₂)).le
  prime_norm := hliveAnnulus
  prime_atom := by
    intro j p hp
    change ‖sourcePrimeTerm (σ := σ)
      ((s.characters.restrictSlots s.allocation.keep).slot j)
      ((s.characters.restrictSlots s.allocation.keep).slotTwist j)
      (s.characters.restrictSlots s.allocation.keep).mask g h'
      (s.w (SlotRestriction.index s.allocation.keep j))
      (s.Zslot ^ s.length (SlotRestriction.index s.allocation.keep j)) p‖ ≤
      profile (SlotRestriction.index s.allocation.keep j) *
        Z ^ (-s.length (SlotRestriction.index s.allocation.keep j) / 2)
    rw [hbase]
    apply sourcePrimeTerm_norm_le_power_from_profile C _ _ _ _ _ _ _ _ _ _
      (zero_lt_one.trans hZ) p (hliveCoefficient j p hp)
    simpa only [show -s.length (SlotRestriction.index s.allocation.keep j) / 2 +
      s.length (SlotRestriction.index s.allocation.keep j) / 2 = 0 by ring,
      Real.rpow_zero, mul_one] using hliveProfile j p hp

end AllocatedExceptionalSource

namespace ActualAllocatedSource.ExceptionalAt

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {k : ℕ}
variable {s : ActualAllocatedSource A V H k}
variable {Y₁ Y₂ : ℝ} {v₁ v₂ : H → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ}
variable {Ψ : Ideal (𝓞 K) →* ℂ} {W₁ W₂ : ℝ → ℂ} {ξ : V} {h : H}
variable (T : s.ExceptionalAt (σ := σ) Y₁ Y₂ v₁ v₂ Ψ W₁ W₂ ξ h)

/-- Replace only the auxiliary lower bound by the exact minimum of
the four already fixed scales. Every original atom dictionary remains
unchanged, and hence so does the whole actual centered polynomial. -/
def withFourPlainLower : s.ExceptionalAt (σ := σ) Y₁ Y₂ v₁ v₂ Ψ W₁ W₂ ξ h :=
  { T with
    lower := s.allocation.fourPlainLower s.scale₁ s.scale₂ Y₁ Y₂
    lower_pos := T.lower_pos.trans_le
      (s.allocation.fourPlainLower_lower T.X₁_lower T.X₂_lower T.Y₁_lower T.Y₂_lower)
    X₁_lower := (min_le_left _ _).trans (min_le_left _ _)
    X₂_lower := (min_le_left _ _).trans (min_le_right _ _)
    Y₁_lower := (min_le_right _ _).trans (min_le_left _ _)
    Y₂_lower := (min_le_right _ _).trans (min_le_right _ _) }

@[simp] theorem withFourPlainLower_source_value :
    T.withFourPlainLower.source.value = T.source.value := rfl

@[simp] theorem withFourPlainLower_lower :
    T.withFourPlainLower.source.lower = s.allocation.fourPlainLower s.scale₁ s.scale₂ Y₁ Y₂ := rfl

end ActualAllocatedSource.ExceptionalAt

/-- The original product identity fixes the scalar total.  It is not
an estimate for a source polynomial or for an exceptional contribution. -/
theorem exceptional_plain_total_of_product {k : ℕ}
    (Z : ℝ) (hZ : 1 < Z) (X₁ X₂ total : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (length : Fin k → ℝ)
    (hproduct : X₁ * X₂ * ∏ i, Z ^ length i = Z ^ total) :
    Real.log (X₁ * X₂) / Real.log Z + ∑ i, length i = total := by
  sorry

/-- Two original side totals give exactly the exponent requested by
the paired exceptional theorem.  Both extraction lengths are computed
from their actual allocations. -/
theorem original_atomic_paired_exponent {k l : ℕ}
    (left : ActualColumnAllocation K k) (right : ActualColumnAllocation K l)
    (Z A c₂ d₂ plainLeft plainRight : ℝ)
    (lengthL : Fin k → ℝ) (lengthR : Fin l → ℝ)
    (hlengthL : ∀ i, 0 ≤ lengthL i) (hlengthR : ∀ i, 0 ≤ lengthR i)
    (annulusL profileL : Fin k → ℝ) (annulusR profileR : Fin l → ℝ)
    (hannulusL : ∀ i, 1 ≤ annulusL i) (hprofileL : ∀ i, 0 ≤ profileL i)
    (hannulusR : ∀ i, 1 ≤ annulusR i) (hprofileR : ∀ i, 0 ≤ profileR i)
    (htotalL : plainLeft + ∑ i, lengthL i = A - c₂)
    (htotalR : plainRight + ∑ i, lengthR i = A - d₂) :
    (left.originalAtomicScales Z plainLeft lengthL hlengthL annulusL profileL
      hannulusL hprofileL).exponent +
      (right.originalAtomicScales Z plainRight lengthR hlengthR annulusR profileR
        hannulusR hprofileR).exponent =
      A - (c₂ + d₂) / 2 - left.rawExtractionLength Z lengthL -
        right.rawExtractionLength Z lengthR := by
  sorry

namespace OriginalNominalTag

/-- The literal removed ideal: one for direct/main, and the actual
prime to its original 1/6/7 valuation for an amplifier error. -/
def extractionIdeal (tag : OriginalNominalTag K) : HeckeGeneral.Analysis.NonzeroIdeal K :=
  match tag with
  | .direct | .main => 1
  | .error e p => ⟨p.asIdeal ^ e.multiplicity,
      mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ p.ne_bot)⟩

theorem extractionIdeal_length (tag : OriginalNominalTag K) (Z : ℝ) :
    idealLogLength Z tag.extractionIdeal.val = tag.removedLength Z := by
  sorry

end OriginalNominalTag

namespace OriginalNominalGeometry

variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)

def centeredExtractionLength : ℝ :=
  G.skeleton.c + G.skeleton.w +
    min (idealLogLength Z G.ideals.second.val) (idealLogLength Z G.ideals.secondOpposite.val)

/-- This is the smaller original common ideal.  The terminal proof
may exchange its two whole columns, preserving their exact product. -/
def centeredSecondIdeal : HeckeGeneral.Analysis.NonzeroIdeal K :=
  if idealLogLength Z G.ideals.second.val ≤ idealLogLength Z G.ideals.secondOpposite.val
  then G.ideals.second else G.ideals.secondOpposite

theorem centeredSecondIdeal_length :
    idealLogLength Z G.centeredSecondIdeal.val =
      min (idealLogLength Z G.ideals.second.val) (idealLogLength Z G.ideals.secondOpposite.val) := by
  sorry

def centeredCommonIdeal : HeckeGeneral.Analysis.NonzeroIdeal K :=
  G.ideals.first * G.tag.extractionIdeal * G.centeredSecondIdeal

theorem centeredCommonIdeal_length :
    idealLogLength Z G.centeredCommonIdeal.val = G.centeredExtractionLength := by
  sorry

theorem centeredExtractionLength_nonneg (hZ : 1 < Z) :
    0 ≤ G.centeredExtractionLength := by
  sorry

/-- The v-sum inequality is a theorem of the smaller actual second
common length; it is not a separately chosen numerical endpoint. -/
theorem centeredExtractionLength_le_halfSecond :
    G.centeredExtractionLength ≤ G.skeleton.c + G.skeleton.w + G.halfSecond := by
  sorry

/-- The upper bound for one extracted plain ideal follows from its
original divisibility inside the same chosen common product. -/
theorem prePlain_norm_le (hZ : 1 < Z) (pre : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hpre : pre.val ∣ G.centeredCommonIdeal.val) :
    idealNorm K pre ≤ Z ^ G.centeredExtractionLength := by
  sorry

theorem prePlain_scale_lower (hZ : 1 < Z) (pre : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hpre : pre.val ∣ G.centeredCommonIdeal.val) (L n : ℝ) (hn : L ≤ n) :
    Z ^ (L - G.centeredExtractionLength) ≤ Z ^ n / idealNorm K pre := by
  sorry

/-- The original four formal plain scales, with the actual same
pre-extractions and final divisors, satisfy the centered minimum window.
The comparison product is retained even if its finite sum is zero. -/
theorem fourPlain_minimum_window {k : ℕ} (B : ActualColumnAllocation K k)
    (hZ : 1 < Z) (pre₁ pre₂ : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hpre₁ : pre₁.val ∣ G.centeredCommonIdeal.val)
    (hpre₂ : pre₂.val ∣ G.centeredCommonIdeal.val)
    (length : Fin k → ℝ) (hlength : ∀ i, 0 ≤ length i)
    (L n₁ n₂ : ℝ) (hn₁ : L ≤ n₁) (hn₂ : L ≤ n₂) :
    Z ^ (L - G.centeredExtractionLength - B.rawExtractionLength Z length) ≤
      B.fourPlainLower
        (Z ^ n₁ / idealNorm K pre₁) (Z ^ n₂ / idealNorm K pre₂)
        (Z ^ L / idealNorm K pre₁) (Z ^ (n₁ + n₂ - L) / idealNorm K pre₂) := by
  sorry

/-- The original centered domain supplies all four quarter-width
lower lengths, for every slot count. -/
theorem fourPlain_minimum_window_of_domain {k : ℕ} (B : ActualColumnAllocation K k)
    {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ} {Y₁ Y₂ floor padding : ℝ}
    (domain : PairedEngineDomain true d a Z Y₁ Y₂ floor padding)
    (pre₁ pre₂ : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hpre₁ : pre₁.val ∣ G.centeredCommonIdeal.val)
    (hpre₂ : pre₂.val ∣ G.centeredCommonIdeal.val)
    (length : Fin k → ℝ) (hlength : ∀ i, 0 ≤ length i) :
    Z ^ ((a.m + a.q) / 4 - G.centeredExtractionLength - B.rawExtractionLength Z length) ≤
      B.fourPlainLower
        (Z ^ a.n₁ / idealNorm K pre₁) (Z ^ a.n₂ / idealNorm K pre₂)
        (Y₁ / idealNorm K pre₁) (Y₂ / idealNorm K pre₂) := by
  sorry

/-- Bind the preceding window to the four literal scales in the
actual centered source.  Each identity concerns one original plain
scale; no inequality for the minimum or for a polynomial is assumed. -/
theorem originalSource_minimum_window
    {A : SArithmeticData K} {σ : K →+* ℂ}
    {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {k : ℕ}
    {s : ActualAllocatedSource A V H k}
    {Y₁ Y₂ : ℝ} {v₁ v₂ : H → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ}
    {Ψ : Ideal (𝓞 K) →* ℂ} {W₁ W₂ : ℝ → ℂ} {ξ : V} {h : H}
    (T : s.ExceptionalAt (σ := σ) Y₁ Y₂ v₁ v₂ Ψ W₁ W₂ ξ h)
    {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ}
    {originalY₁ originalY₂ floor padding : ℝ}
    (domain : PairedEngineDomain true d a Z originalY₁ originalY₂ floor padding)
    (pre₁ pre₂ : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hpre₁ : pre₁.val ∣ G.centeredCommonIdeal.val)
    (hpre₂ : pre₂.val ∣ G.centeredCommonIdeal.val)
    (hlength : ∀ i, 0 ≤ s.length i)
    (hscale₁ : s.scale₁ = Z ^ a.n₁ / idealNorm K pre₁)
    (hscale₂ : s.scale₂ = Z ^ a.n₂ / idealNorm K pre₂)
    (hcomparison₁ : Y₁ = originalY₁ / idealNorm K pre₁)
    (hcomparison₂ : Y₂ = originalY₂ / idealNorm K pre₂) :
    Z ^ ((a.m + a.q) / 4 - G.centeredExtractionLength -
      s.allocation.rawExtractionLength Z s.length) ≤ T.withFourPlainLower.source.lower := by
  sorry

section ActualRows

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS} {kLeft kRight : ℕ}
variable (W : ActualSecondRowMass R C kLeft kRight)

/-- Directly fills the v-sum field of the actual exceptional numerical
label using the original common-ideal identities on its two sides. -/
theorem exceptionalNumbers_original_v_sum (r₁ r₂ slotError firstProfile : ℝ)
    (hleft : G.ideals.second.val = W.leftIdeal)
    (hright : G.ideals.secondOpposite.val = W.rightIdeal) :
    let n := G.exceptionalNumbers W G.centeredExtractionLength r₁ r₂ slotError firstProfile
    n.vStar ≤ n.c + n.w + n.b₂ := by
  sorry

/-- The same actual left allocation supplies the nonnegative r-one
field, including when it has no prime occurrences. -/
theorem exceptionalNumbers_original_r₁_nonneg {k : ℕ}
    (left : ActualColumnAllocation K k) (length : Fin k → ℝ)
    (hlength : ∀ i, 0 ≤ length i) (hZ : 1 < Z)
    (r₂ slotError firstProfile : ℝ) :
    0 ≤ (G.exceptionalNumbers W G.centeredExtractionLength
      (left.rawExtractionLength Z length) r₂ slotError firstProfile).r₁ := by
  sorry

/-- The second divisor window is proved from its true squarefree
allocation and the individual frozen-prime annuli.  The numerical
slot error is exactly the sum on this actual frozen set. -/
theorem exceptionalNumbers_original_divisor_window {k : ℕ}
    (right : ActualColumnAllocation K k) (length error : Fin k → ℝ)
    (hZ : 1 < Z) (r₁ firstProfile lower : ℝ)
    (hsq : Squarefree right.divisor)
    (hselection : right.selection ∈ AllocationMass.idealAllocations right.divisor (k + 2))
    (hdivisor : Z ^ lower ≤ (Ideal.absNorm right.divisor : ℝ))
    (hprime : ∀ i ∈ Finset.univ \ right.keep,
      (Ideal.absNorm (right.witness.2 i).asIdeal : ℝ) ≤ Z ^ (length i + 2 * error i)) :
    let n := G.exceptionalNumbers W G.centeredExtractionLength r₁
      (right.rawExtractionLength Z length)
      (∑ i ∈ Finset.univ \ right.keep, error i) firstProfile
    lower - n.r₂ ≤ n.slotError := by
  sorry

/-- The final atom-exponent field keeps the original first common
length and removed amplifier length.  Its only total identities are
the two products of the original plain and individual slot scales. -/
theorem exceptionalNumbers_original_atom_exponent {k l : ℕ}
    (left : ActualColumnAllocation K k) (right : ActualColumnAllocation K l)
    (lengthL : Fin k → ℝ) (lengthR : Fin l → ℝ)
    (hlengthL : ∀ i, 0 ≤ lengthL i) (hlengthR : ∀ i, 0 ≤ lengthR i)
    (annulusL profileL : Fin k → ℝ) (annulusR profileR : Fin l → ℝ)
    (hannulusL : ∀ i, 1 ≤ annulusL i) (hprofileL : ∀ i, 0 ≤ profileL i)
    (hannulusR : ∀ i, 1 ≤ annulusR i) (hprofileR : ∀ i, 0 ≤ profileR i)
    (XL₁ XL₂ XR₁ XR₂ slotError firstProfile : ℝ)
    (hZ : 1 < Z) (hXL₁ : 0 < XL₁) (hXL₂ : 0 < XL₂)
    (hXR₁ : 0 < XR₁) (hXR₂ : 0 < XR₂)
    (htotalL : XL₁ * XL₂ * ∏ i, Z ^ lengthL i =
      Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w - idealLogLength Z W.leftIdeal))
    (htotalR : XR₁ * XR₂ * ∏ i, Z ^ lengthR i =
      Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w - idealLogLength Z W.rightIdeal)) :
    let n := G.exceptionalNumbers W G.centeredExtractionLength
      (left.rawExtractionLength Z lengthL) (right.rawExtractionLength Z lengthR)
      slotError firstProfile
    (left.originalAtomicScales Z (Real.log (XL₁ * XL₂) / Real.log Z)
      lengthL hlengthL annulusL profileL hannulusL hprofileL).exponent +
      (right.originalAtomicScales Z (Real.log (XR₁ * XR₂) / Real.log Z)
        lengthR hlengthR annulusR profileR hannulusR hprofileR).exponent =
      n.Aexp - n.c - n.w - n.b₂ - n.r₁ - n.r₂ := by
  sorry

end ActualRows

end OriginalNominalGeometry

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualColumnAllocation.divisor_window_of_prime_windows
#print axioms HeckeSkeleton.Moments.EngineStep.ActualColumnAllocation.originalAtomicScales_exponent
#print axioms HeckeSkeleton.Moments.EngineStep.AllocatedExceptionalSource.atomicControlOfOriginalWindows
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.ExceptionalAt.withFourPlainLower_source_value
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.originalSource_minimum_window
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.exceptionalNumbers_original_v_sum
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.exceptionalNumbers_original_divisor_window
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.exceptionalNumbers_original_atom_exponent
