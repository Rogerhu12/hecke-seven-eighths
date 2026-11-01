import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalBinding

/-!
# The same actual theta-class magnitude enters the paid source theorem

The first exact binding yields the complete two-column sum on the
original theta-class rows. The two literal atom tables now produce the
actual exceptional frames on precisely those rows. Only zero original
correlations are removed by the live-row identity.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPairBinding

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (rows : ActualSecondCorrelationRows A σ H ι)
variable {theta : Finset (HeckeCharacter K)}
variable (Q : PairedFiniteCharacters theta H) (thetaPair : theta × theta)
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
variable (firstSign : ℝ) (L : Ideal (𝓞 K))
variable (leftSelection : primeSupport L → Finset (Fin (k + 2)))
variable (rightSelection : primeSupport L → Finset (Fin (l + 2)))
variable (hleftColumns : (pairedAllocatedColumns L leftSelection left.plain₁ left.plain₂
  left.slots id id HeightOneSpectrum.asIdeal).Nonempty)
variable (hrightColumns : (pairedAllocatedColumns L rightSelection right.plain₁ right.plain₂
  right.slots id id HeightOneSpectrum.asIdeal).Nonempty)

local notation "S" => rows.restrictRows (Q.thetaClass thetaPair)
local notation "leftFrame" =>
  (left.factors S .left phase leftIdeal hleftIdeal firstSign false).frame
    C L leftSelection hleftColumns
local notation "rightFrame" =>
  (right.factors S .right phase rightIdeal hrightIdeal (-firstSign) false).frame
    C L rightSelection hrightColumns
local notation "EL" => CanonicalLiteralExceptionalFactory.comparison
  left (SecondColumnSide.left.phase PUnit.{1} phase)
local notation "ER" => CanonicalLiteralExceptionalFactory.comparison
  right (SecondColumnSide.right.phase PUnit.{1} phase)
local notation "leftPoint" => rawSourceLocation (CanonicalLiteralLocations.plain firstSign)
  (CanonicalLiteralLocations.plain firstSign) (CanonicalLiteralLocations.prime firstSign)
local notation "rightPoint" => rawSourceLocation (CanonicalLiteralLocations.plain (-firstSign))
  (CanonicalLiteralLocations.plain (-firstSign)) (CanonicalLiteralLocations.prime (-firstSign))

/-- The complete centered pair on one actual theta class is exactly
the magnitude estimated by the paid exceptional terminal. No new row,
column, divisor, frequency or Fourier location is chosen. -/
theorem theta_pair_magnitude (ξ : WithLp 2 (ℝ × ℝ)) :
    jointColumnPairMagnitude (rows.rows.filter (Q.thetaClass thetaPair))
      leftFrame.allocation.columns rightFrame.allocation.columns
      (fun h => rows.weight h * rows.correlation h)
      (secondAllocatedLeftCoefficient (σ := σ) PUnit.{1} leftIdeal rows.frequency
        (fun _ => PUnit.unit) phase left.whole)
      (secondAllocatedRightCoefficient (σ := σ) PUnit.{1} rightIdeal rows.frequency
        (fun _ => PUnit.unit) phase right.whole)
      (fun _ => leftPoint) (fun _ => rightPoint) ξ =
        leftFrame.exceptionalMagnitude rightFrame EL ER Q ξ := by
  have hrows : S.rows.filter Q.exceptional = rows.rows.filter (Q.thetaClass thetaPair) := by
    apply Finset.filter_eq_self.mpr
    intro h hh
    exact Q.thetaClass_exceptional thetaPair h (Finset.mem_filter.mp hh).2
  have hleft : leftFrame.centeredCoefficient EL =
      secondAllocatedLeftCoefficient (σ := σ) PUnit.{1} leftIdeal rows.frequency
        (fun _ => PUnit.unit) phase left.whole := by
    funext h i
    exact left.exceptional_frame_coefficient S .left phase leftIdeal hleftIdeal
      firstSign L leftSelection hleftColumns h i
  have hright : rightFrame.centeredCoefficient ER =
      secondAllocatedRightCoefficient (σ := σ) PUnit.{1} rightIdeal rows.frequency
        (fun _ => PUnit.unit) phase right.whole := by
    funext h i
    exact right.exceptional_frame_coefficient S .right phase rightIdeal hrightIdeal
      (-firstSign) L rightSelection hrightColumns h i
  have hp := S.pair_magnitude_live leftFrame.allocation.columns rightFrame.allocation.columns
    (leftFrame.centeredCoefficient EL) (rightFrame.centeredCoefficient ER)
    (fun h => rawSourceLocation (leftFrame.leftLocation h) (leftFrame.rightLocation h)
      (leftFrame.slotLocation h))
    (fun h => rawSourceLocation (rightFrame.leftLocation h) (rightFrame.rightLocation h)
      (rightFrame.slotLocation h)) Q.exceptional ξ
  change jointColumnPairMagnitude (S.rows.filter Q.exceptional)
      leftFrame.allocation.columns rightFrame.allocation.columns
      (fun h => rows.weight h * rows.correlation h)
      (leftFrame.centeredCoefficient EL) (rightFrame.centeredCoefficient ER)
      (fun _ => leftPoint) (fun _ => rightPoint) ξ =
        leftFrame.exceptionalMagnitude rightFrame EL ER Q ξ at hp
  rw [hrows, hleft, hright] at hp
  exact hp

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPairBinding

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPairBinding.theta_pair_magnitude
