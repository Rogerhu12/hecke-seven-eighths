import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalPairBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OrdinaryExceptionalLabelIntegral

/-!
# The literal ordinary branch has no comparison column

The original centered flag sets the comparison left weight to zero.
Consequently the stored complete difference is exactly the original
ordinary coefficient, on the same frame and allocation. The identity
below permits the ordinary source bound to enter the same stored
exceptional integral without changing either row carrier or Fourier
location.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)

/-- The missing comparison is zero before any norm or sum is taken. -/
theorem ordinary_comparison_coefficient (phase : PUnit.{1} →* Circle)
    (hordinary : d.centered = false) (i : AllocationColumn K k) :
    (CanonicalLiteralExceptionalFactory.comparison d phase).centeredCoefficient
        (Real.sqrt d.gauss₁ : ℂ)⁻¹ (Real.sqrt d.gauss₂ : ℂ)⁻¹
        (fun j => (Real.sqrt (d.gaussSlot j) : ℂ)⁻¹) i =
      (d.dictionary phase false).normalizedCoefficient
        (Real.sqrt d.gauss₁ : ℂ)⁻¹ (Real.sqrt d.gauss₂ : ℂ)⁻¹
        (fun j => (Real.sqrt (d.gaussSlot j) : ℂ)⁻¹) i := by
  rw [d.exceptional_comparison_coefficient,
    SecondCoefficientTermDictionary.normalizedCoefficient_eq]
  change d.whole i = d.term false i
  simp only [whole, d.term_true i, hordinary, Bool.false_eq_true, if_false, sub_zero]

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Both original Fourier orientations retain the ordinary gate. -/
theorem exceptional_frame_coefficient_ordinary
    (R : ActualSecondCorrelationRows A σ H ι) (side : SecondColumnSide)
    (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
    (ideal : AllocationColumn K k → A.Exterior)
    (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
      (ideal i).val = allocationColumnIdeal i)
    (firstSign : ℝ) (L : Ideal (𝓞 K))
    (selection : primeSupport L → Finset (Fin (k + 2)))
    (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
      id id HeightOneSpectrum.asIdeal).Nonempty)
    (hordinary : d.centered = false) (h : H) (i : AllocationColumn K k) :
    ((d.factors R side χ ideal hideal firstSign false).frame C L selection hne).centeredCoefficient
          (CanonicalLiteralExceptionalFactory.comparison d (side.phase PUnit.{1} χ)) h i =
      ((d.factors R side χ ideal hideal firstSign false).frame C L selection hne).coefficient h i := by
  cases side <;>
    simp only [SecondSideFrame.centeredCoefficient, SecondSideFrame.coefficient,
      SecondRectangularFactors.frame, factors, d.ordinary_comparison_coefficient _ hordinary]

end CanonicalLiteralRectangles.Atoms

namespace CanonicalLiteralExceptionalOrdinaryMagnitude

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (rows : ActualSecondCorrelationRows A σ H ι)
variable {theta : Finset (HeckeCharacter K)}
variable (Q : PairedFiniteCharacters theta H)
variable {k l : ℕ}
variable (left : CanonicalLiteralRectangles.Atoms (K := K) k)
variable (right : CanonicalLiteralRectangles.Atoms (K := K) l)
variable (phase : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (leftIdeal : AllocationColumn K k → A.Exterior)
variable (rightIdeal : AllocationColumn K l → A.Exterior)
variable (hleftIdeal : ∀ i ∈ childCartesianColumns left.plain₁ left.plain₂ left.slots,
  (leftIdeal i).val = allocationColumnIdeal i)
variable (hrightIdeal : ∀ i ∈ childCartesianColumns right.plain₁ right.plain₂ right.slots,
  (rightIdeal i).val = allocationColumnIdeal i)
variable (firstLeftSign firstRightSign : ℝ) (L : Ideal (𝓞 K))
variable (leftSelection : primeSupport L → Finset (Fin (k + 2)))
variable (rightSelection : primeSupport L → Finset (Fin (l + 2)))
variable (hleftColumns : (pairedAllocatedColumns L leftSelection left.plain₁ left.plain₂
  left.slots id id HeightOneSpectrum.asIdeal).Nonempty)
variable (hrightColumns : (pairedAllocatedColumns L rightSelection right.plain₁ right.plain₂
  right.slots id id HeightOneSpectrum.asIdeal).Nonempty)

local notation "leftFrame" =>
  (left.factors rows .left phase leftIdeal hleftIdeal firstLeftSign false).frame
    C L leftSelection hleftColumns
local notation "rightFrame" =>
  (right.factors rows .right phase rightIdeal hrightIdeal firstRightSign false).frame
    C L rightSelection hrightColumns
local notation "EL" => CanonicalLiteralExceptionalFactory.comparison
  left (SecondColumnSide.left.phase PUnit.{1} phase)
local notation "ER" => CanonicalLiteralExceptionalFactory.comparison
  right (SecondColumnSide.right.phase PUnit.{1} phase)

/-- The same stored magnitude is the ordinary source magnitude when
both actual atom tables retain the original ordinary flag. -/
theorem pair_magnitude_eq (hleft : left.centered = false)
    (hright : right.centered = false) (ξ : WithLp 2 (ℝ × ℝ)) :
    leftFrame.exceptionalMagnitude rightFrame EL ER Q ξ =
      leftFrame.ordinaryExceptionalMagnitude rightFrame Q ξ := by
  have hL : leftFrame.centeredCoefficient EL = leftFrame.coefficient := by
    funext h i
    exact left.exceptional_frame_coefficient_ordinary rows .left phase leftIdeal hleftIdeal
      firstLeftSign L leftSelection hleftColumns hleft h i
  have hR : rightFrame.centeredCoefficient ER = rightFrame.coefficient := by
    funext h i
    exact right.exceptional_frame_coefficient_ordinary rows .right phase rightIdeal hrightIdeal
      firstRightSign L rightSelection hrightColumns hright h i
  simp only [SecondSideFrame.exceptionalMagnitude,
    SecondSideFrame.ordinaryExceptionalMagnitude, hL, hR]

end CanonicalLiteralExceptionalOrdinaryMagnitude
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ordinary_comparison_coefficient
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.exceptional_frame_coefficient_ordinary
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalOrdinaryMagnitude.pair_magnitude_eq
