import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualExceptionalBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OrdinaryLiteralExceptionalLeaf

/-!
# Ordinary exceptional budget on the original amplified family

The ordinary terminal is assembled from the original absolute-volume
atom estimate, with its ordinary range and no centered minimum or
height assumption. Both actual Fourier kernels use the fixed (0,0)
control. Empty correlation classes are paid by their exact zero row
weights. The true source indices, two divisor sums, original tag weights
and finite source fibres are the same as in the centered assembly.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup HeckePort.Moments.Support
open HeckePort.CenteredMomentCounting CommonSupportMass UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {C : A.GeneralArithmeticContext σ η hS}
variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


variable {theta : Finset (HeckeCharacter K)}

namespace ExceptionalOriginalProfilePair

/-- The ordinary constant is fixed by the original two profile controls. -/
def ordinaryConstant (p : ExceptionalOriginalProfilePair K) : ℝ :=
  ordinaryExceptionalConstant p.leftVolume p.rightVolume

theorem ordinaryConstant_pos (p : ExceptionalOriginalProfilePair K) :
    0 < p.ordinaryConstant :=
  ordinaryExceptionalConstant_pos p.leftVolume p.rightVolume

end ExceptionalOriginalProfilePair

/-- Three powers for the first profile and the two original Fourier
kernels supplement the six-cap-plus-three original atom estimate. -/
def ordinaryExceptionalBudgetProfileDegree (cap degree : ℕ) : ℕ := degree * (6 * cap + 6)

/-- This constant is selected before every moving source and parameter. -/
def ordinaryExceptionalCatalogueConstant
    (profiles : theta × theta → ExceptionalOriginalProfilePair K) : ℝ :=
  finiteExceptionalConstant (fun χ => (profiles χ).ordinaryConstant)

theorem ordinaryExceptionalCatalogueConstant_pos
    (profiles : theta × theta → ExceptionalOriginalProfilePair K) :
    0 < ordinaryExceptionalCatalogueConstant profiles :=
  finiteExceptionalConstant_pos _ (fun χ => (profiles χ).ordinaryConstant_pos.le)

theorem ordinaryExceptionalCatalogueConstant_le
    (profiles : theta × theta → ExceptionalOriginalProfilePair K) (χ : theta × theta) :
    (profiles χ).ordinaryConstant ≤ ordinaryExceptionalCatalogueConstant profiles := by
  have hs := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (theta × theta))) =>
      (profiles j).ordinaryConstant_pos.le) (Finset.mem_univ χ)
  unfold ordinaryExceptionalCatalogueConstant finiteExceptionalConstant
  linarith

variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "V" => WithLp 2 (U × E)

/-- Raw data for one actual theta-class leaf. The original fibre cap
controls orbit-to-ideal and source-to-orbit multiplicities, before any
leaf is constructed. Exact source weights retain their two fibres and
the side factor one half. There is no cost, energy or mass bound field. -/
structure OrdinaryExceptionalLeafRawData
    (R : ActualSecondCorrelationRows A σ H ι)
    (p : ExceptionalOriginalProfilePair K)
    (cap degree fiberCap firstFiber : ℕ)
    (Z P m q loss lower tagWeight movingLength : ℝ)
    (leaf : ActualHybridLeaf K H U E)
    {branch : TwoDivisorCommonBranch (K := K)} (j : branch.Index)
    (Q : PairedFiniteCharacters theta H) where
  extraction : leaf.ConstantAtomExtraction
  left : SecondSideFrame (V := V) C R PUnit.{1} .left leaf.leftSlots
  right : SecondSideFrame (V := V) C R PUnit.{1} .right leaf.rightSlots
  commonLeftSlots : ℕ
  commonRightSlots : ℕ
  rowMass : ActualSecondRowMass R C commonLeftSlots commonRightSlots
  binding : extraction.leaf.OrdinaryExceptionalBinding left right Q
  leftCharts : ∀ ξ : V, ∀ h : R.exceptionalRows Q,
    left.source.OrdinaryExceptionalAt (σ := σ) p.leftCharacter p.leftPlain₁ p.leftPlain₂ ξ h.val
  rightCharts : ∀ ξ : V, ∀ h : R.exceptionalRows Q,
    right.source.OrdinaryExceptionalAt (σ := σ) p.rightCharacter p.rightPlain₁ p.rightPlain₂ ξ h.val
  leftScales : ExceptionalAtomicScales left.allocation
  rightScales : ExceptionalAtomicScales right.allocation
  numbers : ExceptionalOriginalNumbers
  v_nonneg : 0 ≤ numbers.v
  r₁_nonneg : 0 ≤ numbers.r₁
  divisor_window : lower - numbers.r₂ ≤ numbers.slotError
  ordinary_range : numbers.Aexp ≤ 5 * (m + q) / 6
  c_nonneg : 0 ≤ numbers.c
  w_nonneg : 0 ≤ numbers.w
  b₂_nonneg : 0 ≤ numbers.b₂
  left_atoms : ∀ ξ h, (leftCharts ξ h).source.AtomicControl Z leftScales
  right_atoms : ∀ ξ h, (rightCharts ξ h).source.AtomicControl Z rightScales
  atom_exponent : leftScales.exponent + rightScales.exponent =
    numbers.Aexp - numbers.c - numbers.w - numbers.b₂ - numbers.r₁ - numbers.r₂
  gcd_window : (Ideal.absNorm (gcd rowMass.leftIdeal rowMass.rightIdeal) : ℝ) ≤ Z ^ numbers.g₂
  unit_window : Z ^ numbers.t₂ ≤ A.exteriorNorm rowMass.unitIdeal
  base : Ideal (𝓞 K)
  valuation_class : ∀ h : R.exceptionalRows Q, ∀ i ∈ multiplicityOneNonunitPrimes C R.primes
    R.leftMultiplicity R.rightMultiplicity (R.frequency h.val.val),
    6 ∣ (normalizedFactors (R.originalIdeal h.val.val).val).count (R.primes i).val.asIdeal
  sixth_power : ∀ h : R.exceptionalRows Q, ∃ a : Ideal (𝓞 K),
    (R.extractedRow C h.val).ideal.val = base * a ^ 6
  radical_window : ∀ h : R.exceptionalRows Q, Z ^ numbers.v ≤ A.exteriorNorm
    (multiplicityOneNonunitRadical C R.primes R.leftMultiplicity R.rightMultiplicity
      (R.frequency h.val.val))
  cutoff_window : ∀ h : R.exceptionalRows Q, A.exteriorNorm (R.originalIdeal h.val.val) ≤
    R.normFactor C h.val.val *
      Z ^ (2 * (numbers.Aexp - numbers.c - numbers.w) - numbers.K₀ -
        numbers.g - numbers.g₂ - numbers.V₀)
  first_saving : 2 * (numbers.c + numbers.w) / 3 - 3 * numbers.stepσ - 5 * numbers.δ / 6 ≤
    firstSaving numbers.c
      (numbers.d + (2 * numbers.Aexp - numbers.c - numbers.d + numbers.R₀ + numbers.E₀ - m) - numbers.K₀)
      numbers.w (q + numbers.R₀ + numbers.E₀) numbers.wo numbers.Bcommon numbers.g numbers.ell
  second_saving : 2 * numbers.b₂ / 3 ≤ 2 * numbers.b₂ - 5 * numbers.g₂ / 6 -
    numbers.p₂ + numbers.t₂ + numbers.V₀ / 6 + (2 * numbers.v) / 6
  radius_window : Z ^ (-numbers.K₀ - numbers.g) ≤
    rowMass.radius.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) rowMass.mask)).val
  central_window : Z ^ (numbers.Aexp - numbers.c - numbers.w) ≤
    Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale
  dyad_window : numbers.g₂ - numbers.t₂ ≤ idealLogLength Z (gcd rowMass.leftIdeal rowMass.rightIdeal) -
    idealLogLength Z rowMass.unitIdeal.val + numbers.rowError
  remaining_window : (numbers.Aexp - numbers.c - numbers.w) + (q + numbers.R₀ + numbers.E₀) +
    numbers.w + numbers.Bcommon + numbers.wo + numbers.ell + numbers.rowError -
    numbers.parentWidth ≤ numbers.remaining
  width_window :
    ((2 * (numbers.Aexp - numbers.c - numbers.w) - numbers.K₀ - numbers.g - numbers.g₂ - numbers.V₀) +
      (q + numbers.R₀ + numbers.E₀ + numbers.wo + numbers.t₂ + numbers.V₀) +
      (numbers.b₂ - numbers.p₂ + numbers.w + numbers.Bcommon + numbers.ell)) -
      (secondCommonChildWidth Z (numbers.Aexp - numbers.c - numbers.w) (q + numbers.R₀ + numbers.E₀)
          numbers.wo numbers.K₀ numbers.g rowMass.leftIdeal rowMass.rightIdeal
          rowMass.unitIdeal.val rowMass.nonunitIdeal.val +
        secondCommonChildAllowance Z numbers.w numbers.Bcommon numbers.ell
          rowMass.leftIdeal rowMass.rightIdeal) ≤ numbers.widthError
  final_remainder : numbers.remaining + numbers.widthError +
    (3 * numbers.stepσ + 5 * numbers.δ / 6 + numbers.slotError) ≤
      loss + movingLength
  left_ideal : rowMass.leftIdeal = j.2.2.1.val.1.1
  right_ideal : rowMass.rightIdeal = j.2.2.1.val.1.2
  left_divisor : left.allocation.divisor = j.2.2.2.1.val
  right_divisor : right.allocation.divisor = j.2.2.2.1.val
  left_occurrences : leaf.leftSlots + 2 ≤ branch.leftOccurrences
    j.1.val j.2.1.val j.2.2.1.val j.2.2.2.1.val
  right_occurrences : leaf.rightSlots + 2 ≤ branch.rightOccurrences
    j.1.val j.2.1.val j.2.2.1.val j.2.2.2.1.val
  left_allocation : HEq (AllocationMass.padSelection left_occurrences left.allocation.selection)
    j.2.2.2.2.1.val
  right_allocation : HEq (AllocationMass.padSelection right_occurrences right.allocation.selection)
    j.2.2.2.2.2.val
  firstCharacter : (PUnit.{1} × PUnit.{1}) →* Circle
  first_profile : numbers.firstProfile ≤ P ^ degree * Z ^ ((m + q) - numbers.firstTotal)
  first_left_nonzero : j.1.val.1.1 ≠ 0
  first_right_nonzero : j.1.val.1.2 ≠ 0
  first_support : primeSupport j.1.val.1.1 = primeSupport j.1.val.1.2
  atoms : ExceptionalOriginalAtomWindow rowMass leftScales rightScales cap (P ^ degree)
  left_fourier : (exceptionalFourierControl (U := U) (E := E) 0 0).leftSeminorms.sup
    (schwartzSeminormFamily ℝ U ℂ) leaf.firstKernel ≤ P ^ degree
  right_fourier : (exceptionalFourierControl (U := U) (E := E) 0 0).rightSeminorms.sup
    (schwartzSeminormFamily ℝ E ℂ) leaf.secondKernel ≤ P ^ degree
  secondFiber : ℕ
  first_fiber : firstFiber ≤ fiberCap
  second_fiber : secondFiber ≤ fiberCap
  row_fiber : rowMass.originalFiber ≤ fiberCap
  outer : leaf.weight / Z ^ (m + q) =
    (((firstFiber : ℝ) * (secondFiber : ℝ) / 2) * tagWeight) *
      (firstOriginalAllowanceWeight Z (m + q) numbers.firstTotal numbers.firstProfile
        j.1.val.1.1 j.1.val.1.2 *
        ‖(moebius j.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient PUnit.{1} (fun _ => (1 : Circle)) firstCharacter‖ *
        ‖(moebius left.allocation.divisor : ℂ)‖ *
        ‖fixedPhaseCoefficient PUnit.{1} (fun _ => (1 : Circle)) left.phaseCharacter‖) / Z ^ numbers.parentWidth

namespace OrdinaryExceptionalLeafRawData

variable {R : ActualSecondCorrelationRows A σ H ι}
variable {p : ExceptionalOriginalProfilePair K}
variable {cap degree fiberCap firstFiber : ℕ}
variable {Z P m q loss lower tagWeight movingLength : ℝ}
variable {leaf : ActualHybridLeaf K H U E}
variable {branch : TwoDivisorCommonBranch (K := K)} {j : branch.Index}
variable {Q : PairedFiniteCharacters theta H}
variable (D : OrdinaryExceptionalLeafRawData (C := C) R p
  cap degree fiberCap firstFiber Z P m q loss lower tagWeight movingLength leaf j Q)

include D

/-- The bound on this literal leaf is derived from its raw atoms.
The volume constant comes from the earlier original catalogue. -/
theorem cost_le (hZ : 1 < Z) (hP : 1 ≤ P) (htag : 0 ≤ tagWeight)
    (volumeConstant : ℝ) (hvolume : 0 ≤ volumeConstant)
    (hconstant : p.ordinaryConstant ≤ volumeConstant) :
    leaf.exceptionalCost / Z ^ (m + q) ≤
      exceptionalBudgetAtomConstant (K := K) (U := U) (E := E)
        cap fiberCap 0 0 volumeConstant * P ^ ordinaryExceptionalBudgetProfileDegree cap degree *
        tagWeight * Z ^ (loss + movingLength) * branch.exceptionalDyadWeight Z lower j := by
  let n := D.numbers
  let vp := p.ordinaryConstant
  let Fourier := exceptionalFourierControl (U := U) (E := E) 0 0
  let fl := Fourier.leftSeminorms.sup (schwartzSeminormFamily ℝ U ℂ) leaf.firstKernel
  let fr := Fourier.rightSeminorms.sup (schwartzSeminormFamily ℝ E ℂ) leaf.secondKernel
  let fibres := ((firstFiber : ℝ) * (D.secondFiber : ℝ) / 2) * (D.rowMass.originalFiber : ℝ)
  let env := D.rowMass.commonEnvelope * (D.leftScales.constant * D.rightScales.constant)
  let exponent := n.remaining + n.widthError +
    (3 * n.stepσ + 5 * n.δ / 6 + n.slotError)
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hp : 0 ≤ P ^ degree := pow_nonneg (zero_le_one.trans hP) _
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hfirst : (firstFiber : ℝ) ≤ fiberCap := by exact_mod_cast D.first_fiber
  have hsecond : (D.secondFiber : ℝ) ≤ fiberCap := by exact_mod_cast D.second_fiber
  have hrow : (D.rowMass.originalFiber : ℝ) ≤ fiberCap := by exact_mod_cast D.row_fiber
  have hfibres : fibres ≤ (fiberCap : ℝ) ^ 3 := by
    have hpair := mul_le_mul hfirst hsecond (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hhalf : ((firstFiber : ℝ) * (D.secondFiber : ℝ) / 2) ≤
        (firstFiber : ℝ) * (D.secondFiber : ℝ) := by
      have hp0 : 0 ≤ (firstFiber : ℝ) * (D.secondFiber : ℝ) := by positivity
      linarith
    exact (mul_le_mul (hhalf.trans hpair) hrow (Nat.cast_nonneg _) (by positivity)).trans_eq (by ring)
  have henv : env ≤ idealCountConstant K ^ (2 * cap) * P ^ (degree * (6 * cap + 3)) :=
    D.atoms.envelope_le_profile_power hP degree
  have henv0 : 0 ≤ env := mul_nonneg D.rowMass.commonEnvelope_nonneg
    (mul_nonneg D.leftScales.constant_nonneg D.rightScales.constant_nonneg)
  have hi : 0 ≤ idealCountConstant K := zero_le_one.trans (one_le_idealCountConstant K)
  have ho : 0 ≤ orbitalFieldFactor K := orbitalFieldFactor_nonneg K
  have hvp : 0 ≤ vp := p.ordinaryConstant_pos.le
  have hfl : 0 ≤ fl := apply_nonneg _ _
  have hfr : 0 ≤ fr := apply_nonneg _ _
  have hFourier : 0 ≤ Fourier.constant := Fourier.constant_pos.le
  have hcoefficient :
      (fibres * env) * orbitalFieldFactor K * vp * Fourier.constant *
        P ^ degree * (fl * fr) ≤
      exceptionalBudgetAtomConstant (K := K) (U := U) (E := E)
        cap fiberCap 0 0 volumeConstant * P ^ ordinaryExceptionalBudgetProfileDegree cap degree := by
    have hbase := mul_le_mul hfibres henv henv0 (by positivity)
    have horb := mul_le_mul_of_nonneg_right hbase ho
    have hvol := mul_le_mul horb hconstant hvp (by positivity)
    have hfourier := mul_le_mul_of_nonneg_right hvol hFourier
    have hprofile := mul_le_mul_of_nonneg_right hfourier hp
    have hnorms := mul_le_mul D.left_fourier D.right_fourier hfr hp
    apply (mul_le_mul hprofile hnorms (mul_nonneg hfl hfr) (by positivity)).trans_eq
    dsimp only [exceptionalBudgetAtomConstant, ordinaryExceptionalBudgetProfileDegree, Fourier]
    rw [show degree * (6 * cap + 6) = degree * (6 * cap + 3) + degree + degree + degree by ring]
    simp only [pow_add]
    ring
  have hcost := ordinary_exceptional_cost_from_original_atoms
    (HL := p.leftVolume) (HR := p.rightVolume)
    leaf D.extraction D.left D.right D.rowMass Q D.binding
    D.leftCharts D.rightCharts D.leftScales D.rightScales
    Z n.Aexp m q n.c n.d n.R₀ n.E₀ n.K₀ n.w n.wo n.Bcommon n.g n.ell n.b₂ n.p₂ n.g₂ n.t₂ n.V₀ n.v
    n.r₁ n.r₂ lower n.slotError n.stepσ n.δ n.parentWidth n.remaining n.rowError n.widthError
    hZ D.v_nonneg D.r₁_nonneg D.divisor_window
    D.ordinary_range D.c_nonneg D.w_nonneg D.b₂_nonneg D.left_atoms D.right_atoms
    D.atom_exponent D.gcd_window D.unit_window D.base D.valuation_class D.sixth_power
    D.radical_window D.cutoff_window D.first_saving D.second_saving D.radius_window
    D.central_window D.dyad_window D.remaining_window D.width_window
    j j.2.1.val rfl D.left_ideal D.right_ideal D.left_divisor D.right_divisor
    D.left_occurrences D.right_occurrences D.left_allocation D.right_allocation
    (fun _ => (1 : Circle)) D.firstCharacter (fun _ => (1 : Circle)) (Subsingleton.elim _ _)
    (m + q) n.firstTotal n.firstProfile (P ^ degree) hp D.first_profile
    D.first_left_nonzero D.first_right_nonzero D.first_support
    (((firstFiber : ℝ) * (D.secondFiber : ℝ) / 2) * tagWeight) (by positivity) D.outer
  have hdyad := branch.exceptionalDyadWeight_nonneg Z lower hz.le j
  calc
    _ ≤ ((fibres * env) * orbitalFieldFactor K * vp * Fourier.constant *
          P ^ degree * (fl * fr)) *
        tagWeight * Z ^ exponent * branch.exceptionalDyadWeight Z lower j := by
      convert hcost using 1 <;>
        dsimp only [fibres, env, vp, fl, fr, Fourier, exponent, n,
          ExceptionalOriginalProfilePair.ordinaryConstant] <;> ring
    _ ≤ (exceptionalBudgetAtomConstant (K := K) (U := U) (E := E)
          cap fiberCap 0 0 volumeConstant * P ^ ordinaryExceptionalBudgetProfileDegree cap degree) *
        tagWeight * Z ^ exponent * branch.exceptionalDyadWeight Z lower j :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoefficient htag)
          (Real.rpow_nonneg hz.le _)) hdyad
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ.le D.final_remainder)
        (mul_nonneg (mul_nonneg
          (exceptionalBudgetAtomConstant_nonneg _ _ _ _ volumeConstant hvolume)
          (pow_nonneg (zero_le_one.trans hP) _)) htag)) hdyad

end OrdinaryExceptionalLeafRawData

/-- The actual source can have no nonzero correlation row.  Such a
class uses only its original constant-atom extraction and individual
zero row weights. Otherwise the original complete atom datum supplies
the numerical savings on either orientation of the same literal leaf.
The column transpose keeps both Fourier kernels, both divisor variables
and the original chosen children. No constructor takes a terminal bound. -/
inductive OrdinaryExceptionalLeafRawCase
    (R : ActualSecondCorrelationRows A σ H ι)
    (p : ExceptionalOriginalProfilePair K)
    (cap degree fiberCap firstFiber : ℕ)
    (Z P m q loss lower tagWeight movingLength : ℝ)
    (leaf : ActualHybridLeaf K H U E)
    {branch : TwoDivisorCommonBranch (K := K)} (j : branch.Index)
    (Q : PairedFiniteCharacters theta H) where
  | ofRowWeightsZero (extraction : leaf.ConstantAtomExtraction)
      (rowWeight_zero : ∀ h ∈ extraction.leaf.rows, extraction.leaf.rowWeight h = 0)
  | ofAtoms (data : OrdinaryExceptionalLeafRawData (C := C) R p
      cap degree fiberCap firstFiber Z P m q loss lower tagWeight movingLength
      leaf j Q)
  | ofTransposedAtoms (data : OrdinaryExceptionalLeafRawData (C := C) R p
      cap degree fiberCap firstFiber Z P m q loss lower tagWeight movingLength
      leaf.terminalTranspose (branch.swapSecondIndex j) Q)

namespace OrdinaryExceptionalLeafRawCase

variable {R : ActualSecondCorrelationRows A σ H ι}
variable {p : ExceptionalOriginalProfilePair K}
variable {cap degree fiberCap firstFiber : ℕ}
variable {Z P m q loss lower tagWeight movingLength : ℝ}
variable {leaf : ActualHybridLeaf K H U E}
variable {branch : TwoDivisorCommonBranch (K := K)} {j : branch.Index}
variable {Q : PairedFiniteCharacters theta H}
variable (D : OrdinaryExceptionalLeafRawCase (C := C) R p
  cap degree fiberCap firstFiber Z P m q loss lower tagWeight movingLength leaf j Q)

include D

/-- Every raw case gives the same bound on the same literal leaf.
The zero branch derives its cost identity internally, without needing
a numerical second saving or a live-row witness on an empty class.
The transposed branch uses exact cost and arithmetic-weight identities. -/
theorem cost_le (hZ : 1 < Z) (hP : 1 ≤ P) (htag : 0 ≤ tagWeight)
    (volumeConstant : ℝ) (hvolume : 0 ≤ volumeConstant)
    (hconstant : p.ordinaryConstant ≤ volumeConstant) :
    leaf.exceptionalCost / Z ^ (m + q) ≤
      exceptionalBudgetAtomConstant (K := K) (U := U) (E := E)
        cap fiberCap 0 0 volumeConstant * P ^ ordinaryExceptionalBudgetProfileDegree cap degree *
        tagWeight * Z ^ (loss + movingLength) * branch.exceptionalDyadWeight Z lower j := by
  cases D with
  | ofRowWeightsZero extraction hweight =>
      rw [extraction.exceptionalCost_eq,
        extraction.leaf.exceptionalCost_eq_zero_of_rowWeight_zero hweight, zero_div]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (exceptionalBudgetAtomConstant_nonneg _ _ _ _ volumeConstant hvolume)
              (pow_nonneg (zero_le_one.trans hP) _)) htag)
          (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
        (branch.exceptionalDyadWeight_nonneg Z lower (zero_lt_one.trans hZ).le j)
  | ofAtoms data =>
      exact data.cost_le hZ hP htag volumeConstant hvolume hconstant
  | ofTransposedAtoms data =>
      simpa only [ActualHybridLeaf.terminalTranspose_exceptionalCost,
        TwoDivisorCommonBranch.exceptionalDyadWeight_swapSecondIndex] using
        data.cost_le hZ hP htag volumeConstant hvolume hconstant

end OrdinaryExceptionalLeafRawCase

section Pooled

variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {pool : PowerScaleExteriorPool A bad Z ell eps}
variable {omega psi : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K omega psi} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualFirstSource (E := U) hΓ μv C pool finiteTest centered d a t Y₁ Y₂ X hX}
local notation "Orbit" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

namespace ActualFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal) {cap : ℕ} (hcap : L.slotCount ≤ cap)
variable (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
local notation "Labels" => R.arithmeticLabels L hcap exceptional N
local notation "Tags" => R.arithmeticTag L exceptional N
local notation "Main" => Labels.mainCarrier Tags
local notation "Errors" => Labels.errorCarrier Tags
local notation "Index" => R.arithmeticIndex L hcap exceptional N

/-- All leaves use the same earlier profile catalogue and the fixed
Fourier order zero. The rows are split by their actual inducing pair.
The raw datum's first orbit fibre is literally the parent's fibre. -/
structure OrdinaryExceptionalOriginalData
    (R : s.SecondStages (E := E) (hDiff := hDiff))
    (L : SourceCartesianAtlas s.columns s.ideal) (hcap : L.slotCount ≤ cap)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (profiles : theta × theta → ExceptionalOriginalProfilePair K)
    (degree fiberCap : ℕ) (M B P loss : ℝ)
    (lower : R.liveLeaves L exceptional N → ℝ) where
  characters : ∀ i : R.liveLeaves L exceptional N, PairedFiniteCharacters theta Orbit
  predicate : ∀ i, (R.parentLeaf L exceptional N i.val).exceptional = (characters i).exceptional
  localM : R.liveLeaves L exceptional N → ℝ
  localB : R.liveLeaves L exceptional N → ℝ
  localM_nonneg : ∀ i, 0 ≤ localM i
  localM_le : ∀ i, localM i ≤ M
  localB_le : ∀ i, localB i ≤ B
  primeIndex : (i : R.liveLeaves L exceptional N) → theta × theta → Type
  primeFintype : ∀ i χ, Fintype (primeIndex i χ)
  primeDecidableEq : ∀ i χ, DecidableEq (primeIndex i χ)
  rows : ∀ i χ,
    letI := primeFintype i χ
    letI := primeDecidableEq i χ
    ActualSecondCorrelationRows A σ Orbit (primeIndex i χ)
  atoms : ∀ i χ,
    letI := primeFintype i χ
    letI := primeDecidableEq i χ
    let labels := R.arithmeticLabels L hcap exceptional N
    let tags := R.arithmeticTag L exceptional N
    let index := R.arithmeticIndex L hcap exceptional N i
    OrdinaryExceptionalLeafRawCase (C := C) (rows i χ) (profiles χ)
      cap degree fiberCap s.fiber Z P a.m a.q loss (lower i)
      (AmplifiedCommonIndex.originalTagWeight pool (localM i) (localB i)
        (labels.mainCarrier tags) (labels.errorCarrier tags) index)
      (AmplifiedCommonIndex.movingLength pool (labels.mainCarrier tags) (labels.errorCarrier tags) index)
      ((R.parentLeaf L exceptional N i.val).thetaClassLeaf (characters i) χ)
      (AmplifiedCommonIndex.selectedIndex pool (labels.mainCarrier tags) (labels.errorCarrier tags) index)
      (characters i)

variable {R L hcap exceptional N}

/-- Internal finite theta assembly. Every summand bound is obtained
from its original atom datum, not supplied as a premise. -/
theorem ordinary_exceptional_parent_leaf_le
    (profiles : theta × theta → ExceptionalOriginalProfilePair K)
    (degree fiberCap : ℕ) (M B P loss : ℝ)
    (lower : R.liveLeaves L exceptional N → ℝ)
    (raw : R.OrdinaryExceptionalOriginalData L hcap exceptional N
      profiles degree fiberCap M B P loss lower)
    (hP : 1 ≤ P) (hell : 0 < ell) (hM : 0 ≤ M) (hdensity : 0 < pool.rowDensity M B)
    (i : R.liveLeaves L exceptional N) :
    (R.parentLeaf L exceptional N i.val).exceptionalCost / Z ^ (a.m + a.q) ≤
      ((Fintype.card (theta × theta) : ℝ) *
        exceptionalBudgetAtomConstant (K := K) (U := U) (E := E) cap fiberCap 0 0
          (ordinaryExceptionalCatalogueConstant profiles)) *
      P ^ ordinaryExceptionalBudgetProfileDegree cap degree * Z ^ loss *
        amplifiedExceptionalDyadWeight pool M B Main Errors (lower i) (Index i) := by
  let volume := ordinaryExceptionalCatalogueConstant profiles
  let atom := exceptionalBudgetAtomConstant (K := K) (U := U) (E := E) cap fiberCap 0 0 volume
  have hv : 0 ≤ volume := (ordinaryExceptionalCatalogueConstant_pos profiles).le
  have ha : 0 ≤ atom := exceptionalBudgetAtomConstant_nonneg _ _ _ _ volume hv
  have hp : 0 ≤ P ^ ordinaryExceptionalBudgetProfileDegree cap degree := pow_nonneg (zero_le_one.trans hP) _
  have htag := AmplifiedCommonIndex.originalTagWeight_nonneg
    pool (raw.localM i) (raw.localB i) Main Errors hell (raw.localM_nonneg i)
    (pool.rowDensity_pos_of_uniform (raw.localM_le i) (raw.localB_le i) hdensity).le (Index i)
  have htag_le := AmplifiedCommonIndex.originalTagWeight_mono_windows pool Main Errors
    (raw.localM_nonneg i) (raw.localM_le i) (raw.localB_le i) hdensity (Index i)
  have hleaf (χ : theta × theta) :
      ((R.parentLeaf L exceptional N i.val).thetaClassLeaf (raw.characters i) χ).exceptionalCost /
        Z ^ (a.m + a.q) ≤
      atom * P ^ ordinaryExceptionalBudgetProfileDegree cap degree * Z ^ loss *
        amplifiedExceptionalDyadWeight pool M B Main Errors (lower i) (Index i) := by
    letI := raw.primeFintype i χ
    letI := raw.primeDecidableEq i χ
    have hc := (raw.atoms i χ).cost_le pool.base_gt_one hP htag volume hv
      (ordinaryExceptionalCatalogueConstant_le profiles χ)
    rw [AmplifiedCommonIndex.selected_dyad] at hc
    have hglobal := hc.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htag_le (mul_nonneg ha hp))
        (Real.rpow_nonneg (zero_lt_one.trans pool.base_gt_one).le _))
      (AmplifiedCommonIndex.dyadWeight_nonneg pool Main Errors
        (zero_lt_one.trans pool.base_gt_one).le (lower i) (Index i)))
    exact AmplifiedCommonIndex.exceptional_pointwise_of_original_tag
      pool M B Main Errors pool.base_gt_one hell hM hdensity.le (Index i)
      _ atom (P ^ ordinaryExceptionalBudgetProfileDegree cap degree)
      (loss + AmplifiedCommonIndex.movingLength pool Main Errors (Index i)) loss (lower i)
      ha hp le_rfl hglobal
  rw [(R.parentLeaf L exceptional N i.val).exceptionalCost_eq_theta_sum
    (raw.characters i) (raw.predicate i), Finset.sum_div]
  calc
    _ ≤ ∑ _χ : theta × theta,
        atom * P ^ ordinaryExceptionalBudgetProfileDegree cap degree * Z ^ loss *
          amplifiedExceptionalDyadWeight pool M B Main Errors (lower i) (Index i) :=
      Finset.sum_le_sum fun χ _ => hleaf χ
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; dsimp only [atom, volume]; ring

end ActualFirstSource.SecondStages

variable {Θ : Type*} [Fintype Θ]

/-- The literal full exceptional budget of the amplified original
source. All uniform choices precede its scale, profile control and
source. The original two Fourier kernels are controlled separately by
the fixed zero-order Fourier controls. -/
theorem actual_amplified_ordinary_exceptionalBudget_from_original_atoms
    (profiles : theta × theta → ExceptionalOriginalProfilePair K)
    (cap dimension width degree fiberCap : ℕ)
    (normBox δ₁ δ₂ δ₃ ell eps Mmax Bmax loss : ℝ)
    (hbox : 0 ≤ normBox) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃)
    (hell : 0 < ell) (heps : 0 < eps) (hepsell : eps < ell)
    (hMmax : 0 ≤ Mmax) (hBmax : 0 ≤ Bmax) :
    ∃ Cex Z₀ : ℝ, 0 < Cex ∧ 1 < Z₀ ∧
    ∀ Z : ℝ, Z₀ ≤ Z → ∀ bad : Finset (HeightOneSpectrum (𝓞 K)),
    ∀ pool : PowerScaleExteriorPool A bad Z ell eps,
    ∀ M B P : ℝ, 0 ≤ M → M ≤ Mmax → B ≤ Bmax → 1 ≤ P →
    ∀ {omega psi : HeckeCharacter K} (centered : Bool) (d : MomentData K omega psi) (a : RealParameters)
      (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X)
      (s : ActualFirstSource (E := U) hΓ μv C pool finiteTest centered d a t Y₁ Y₂ X hX)
      (R : s.SecondStages (E := E) (hDiff := hDiff))
      (L : SourceCartesianAtlas s.columns s.ideal) (hcap : L.slotCount ≤ cap)
      (exceptional : R.supported.gated.CoverHybridPredicates L) (N : s.Normalization)
      (B₀ : ℝ), B₀ + 7 * ell ≤ normBox →
    ∀ rows : R.supported.gated.OriginalFibreRows Θ dimension width normBox Z,
    ∀ oldMask : Ideal (𝓞 K), Squarefree oldMask → oldMask ≠ 0 →
      (∀ i ∈ s.columns, oldMask ∣ (s.ideal i).val) →
    ∀ maskIdeal : Ideal (𝓞 K), maskIdeal ≠ 0 →
      OriginalMaskPrimeData s.mask maskIdeal →
      (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ normBox →
      (∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B₀) →
    ∀ (lower : R.supported.gated.liveLeaves L exceptional N → ℝ) (mesh : ℝ),
      (∀ i, (Ideal.absNorm (R.supported.gated.innerDivisor L i.val) : ℝ) ≤ Z ^ (lower i + mesh)) →
    ∀ raw : R.supported.gated.OrdinaryExceptionalOriginalData L hcap exceptional N
      profiles degree fiberCap M B P loss lower,
      R.supported.gated.exceptionalBudget L exceptional N / Z ^ (a.m + a.q) ≤
        Cex * P ^ ordinaryExceptionalBudgetProfileDegree cap degree *
          Z ^ (loss + δ₁ + δ₂ + δ₃ + eps + mesh) / (Ideal.absNorm oldMask : ℝ) := by
  obtain ⟨Ca, Za, hCa, hZa, hmass⟩ := actual_amplified_exceptional_index_mass
    (A := A) (C := C) (W := U) (E := E) (Θ := Θ)
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (finiteTest := finiteTest)
    cap dimension width normBox δ₁ δ₂ δ₃ ell eps Mmax Bmax
    hbox hδ₁ hδ₂ hδ₃ hell heps hepsell hMmax hBmax
  obtain ⟨Zp, hZp, hpool⟩ := uniform_pool_density_and_mass (A := A)
    ell eps Mmax Bmax hell heps hepsell hMmax hBmax
  let volume := ordinaryExceptionalCatalogueConstant profiles
  let atom := exceptionalBudgetAtomConstant (K := K) (U := U) (E := E) cap fiberCap 0 0 volume
  let total := (Fintype.card (theta × theta) : ℝ) * atom
  have hv : 0 ≤ volume := (ordinaryExceptionalCatalogueConstant_pos profiles).le
  have hatom : 0 ≤ atom := exceptionalBudgetAtomConstant_nonneg _ _ _ _ volume hv
  have ht : 0 ≤ total := mul_nonneg (Nat.cast_nonneg _) hatom
  refine ⟨(total + 1) * Ca, max Za Zp, mul_pos (by linarith) hCa,
    hZa.trans_le (le_max_left _ _), ?_⟩
  intro Z hZ bad pool M B P hM hMM hBB hP omega psi centered d a t Y₁ Y₂ X hX s R L hcap
    exceptional N B₀ hB₀ rows oldMask hs hs0 hmaskOld maskIdeal hmask0 mask hmaskN hN lower mesh hwindow raw
  have hza : Za ≤ Z := (le_max_left _ _).trans hZ
  have hzp : Zp ≤ Z := (le_max_right _ _).trans hZ
  have hz : 0 < Z := zero_lt_one.trans pool.base_gt_one
  obtain ⟨hdensity, _, _, _⟩ := hpool Z hzp bad pool M B hMM hBB
  have hm := hmass Z hza bad pool M B hM hMM hBB centered d a t Y₁ Y₂ X hX s R L hcap
    exceptional N B₀ hB₀ rows oldMask hs hs0 hmaskOld maskIdeal hmask0 mask hmaskN hN lower mesh hwindow
  let dyad := fun i : R.supported.gated.liveLeaves L exceptional N =>
    amplifiedExceptionalDyadWeight pool M B
      ((R.supported.gated.arithmeticLabels L hcap exceptional N).mainCarrier
        (R.supported.gated.arithmeticTag L exceptional N))
      ((R.supported.gated.arithmeticLabels L hcap exceptional N).errorCarrier
        (R.supported.gated.arithmeticTag L exceptional N)) (lower i)
      (R.supported.gated.arithmeticIndex L hcap exceptional N i)
  have hleaf (i : R.supported.gated.liveLeaves L exceptional N) :
      (R.supported.gated.parentLeaf L exceptional N i.val).exceptionalCost / Z ^ (a.m + a.q) ≤
        total * P ^ ordinaryExceptionalBudgetProfileDegree cap degree * Z ^ loss * dyad i :=
    ActualFirstSource.SecondStages.ordinary_exceptional_parent_leaf_le profiles
      degree fiberCap M B P loss lower raw hP hell hM hdensity i
  have hscalar : 0 ≤ total * P ^ ordinaryExceptionalBudgetProfileDegree cap degree * Z ^ loss :=
    mul_nonneg (mul_nonneg ht (pow_nonneg (zero_le_one.trans hP) _)) (Real.rpow_nonneg hz.le _)
  have hnorm : 0 < (Ideal.absNorm oldMask : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0))
  calc
    _ = ∑ i : R.supported.gated.liveLeaves L exceptional N,
        (R.supported.gated.parentLeaf L exceptional N i.val).exceptionalCost / Z ^ (a.m + a.q) := by
      rw [ActualFirstSource.SecondStages.exceptionalBudget, Finset.sum_div]
    _ ≤ ∑ i : R.supported.gated.liveLeaves L exceptional N,
        total * P ^ ordinaryExceptionalBudgetProfileDegree cap degree * Z ^ loss * dyad i :=
      Finset.sum_le_sum fun i _ => hleaf i
    _ = (total * P ^ ordinaryExceptionalBudgetProfileDegree cap degree * Z ^ loss) * ∑ i, dyad i :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (total * P ^ ordinaryExceptionalBudgetProfileDegree cap degree * Z ^ loss) *
        (Ca * Z ^ (δ₁ + δ₂ + δ₃ + eps + mesh) / (Ideal.absNorm oldMask : ℝ)) :=
      mul_le_mul_of_nonneg_left hm hscalar
    _ = (total * Ca) * P ^ ordinaryExceptionalBudgetProfileDegree cap degree *
        Z ^ (loss + δ₁ + δ₂ + δ₃ + eps + mesh) / (Ideal.absNorm oldMask : ℝ) := by
      rw [show loss + δ₁ + δ₂ + δ₃ + eps + mesh = loss + (δ₁ + δ₂ + δ₃ + eps + mesh) by ring,
        Real.rpow_add hz loss (δ₁ + δ₂ + δ₃ + eps + mesh)]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hCa.le)
          (pow_nonneg (zero_le_one.trans hP) _))
        (Real.rpow_nonneg hz.le _)) hnorm.le

end Pooled

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OrdinaryExceptionalLeafRawData.cost_le
#print axioms HeckeSkeleton.Moments.EngineStep.OrdinaryExceptionalLeafRawCase.cost_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.ordinary_exceptional_parent_leaf_le
#print axioms HeckeSkeleton.Moments.EngineStep.actual_amplified_ordinary_exceptionalBudget_from_original_atoms
