import HeckeSkeleton.Moments.MOM_INV_STEP.ActualBoxGeometry
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualCenterGeometry
import HeckeSkeleton.Moments.MOM_INV_STEP.CenteredChildGeometry

/-!
# Actual source membership supplies the centered child length

The first center comes from the real extracted A-side times C times e.
The second center is computed from the fresh common ideal and the
independent full-Moebius overlap. A record in the actual norm box
therefore supplies both center windows and the precise error interval
for its literal child scale.

The lower bound on the child length follows already from membership
in the real overlap pool. It does not require a nonzero child column or
an assumption about the energy of a reconstructed packet.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualCenteredGeometry

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalNormPools FirstParentRows ActualProductionBoxes
  ActualBoxGeometry
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable {σ : Type*} [DecidableEq σ]
variable (T : FirstParentEnergy.Data K S (σ := σ)) (hmask : T.mask = ∅)
variable (X : ℝ) (H : ActualPositiveIndex.Cutoff K S D T X)
local notation "Idx" => ActualPositiveIndex.Index K S D Γ T X H
local notation "bare" => ActualPositiveIndex.bare K S D Γ T hmask X H

/-- The center parameter is the actual three-factor norm product,
with the first Cauchy side selected only here. -/
theorem extractedNorm_eq_coordinates (i : Idx) (side : Bool) :
    FirstOuterCenters.extractedNorm K S D T side i.1 i.2.1 =
      coordinateNorm K S D Γ (bare i) (extractedCoordinate side) *
        coordinateNorm K S D Γ (bare i) .firstCommon *
        coordinateNorm K S D Γ (bare i) .firstOverlap := by
  change (Ideal.absNorm
      (FirstSourceColumns.extractedFactor K S (bare i).refs.1 (bare i).refs.2
        (bare i).b₁ (bare i).b₂ side).val.val : ℝ) *
      height K Sset (bare i).quotient = _
  rw [FirstSourceColumns.extractedFactor_val K S D,
    CanonicalConductor.commonResidualIdeal_eq_C, map_mul, Nat.cast_mul]
  cases side <;> rfl

def secondBin (i : Idx) : SecondMobiusGeometry.Index X :=
  SecondMobiusGeometry.centerIndex K S X i.2.2.1.val i.2.2.2.2.2

def childLength (Z : ℝ) (i : Idx) : ℝ :=
  Real.logb Z (SecondMobiusGeometry.childScale X (secondBin K S D Γ T X H i))

/-- The second product window comes from the original overlap index,
before any reconstruction or energy bound. -/
theorem second_center_window (i : Idx) :
    DyadicSourcePartition.center (secondBin K S D Γ T X H i).val ≤
        coordinateNorm K S D Γ (bare i) .secondCommon *
          coordinateNorm K S D Γ (bare i) .secondOverlap ∧
      coordinateNorm K S D Γ (bare i) .secondCommon *
          coordinateNorm K S D Γ (bare i) .secondOverlap ≤
        4 * DyadicSourcePartition.center (secondBin K S D Γ T X H i).val :=
  SecondMobiusGeometry.centerIndex_bounds K S X i.2.2.1.val i.2.2.2.2.2

/-- Any actual overlap index forces the fixed child scale to be at
least one quarter. Empty source bins need no geometric witness. -/
theorem childScale_one_quarter_le (i : Idx) :
    (1 / 4 : ℝ) ≤
      SecondMobiusGeometry.childScale X (secondBin K S D Γ T X H i) := by
  have hc := (SecondMobiusGeometry.centerIndex_bounds K S X
    i.2.2.1.val i.2.2.2.2.2).1
  have hp := (SecondMobiusGeometry.product_bounds K S X
    i.2.2.1.val i.2.2.2.2.2).2
  unfold SecondMobiusGeometry.childScale
  apply (le_div_iff₀
    (DyadicSourcePartition.center_pos (secondBin K S D Γ T X H i).val)).mpr
  change DyadicSourcePartition.center (secondBin K S D Γ T X H i).val ≤ _ at hc
  linarith

theorem childLength_live_lower (Z h : ℝ) (hZ : 1 < Z) (hwidth : 2 ≤ Z ^ h)
    (i : Idx) : -2 * h ≤ childLength K S D Γ T X H Z i := by
  have hu := childScale_one_quarter_le K S D Γ T X H i
  have hu0 : 0 < SecondMobiusGeometry.childScale X (secondBin K S D Γ T X H i) :=
    (by norm_num : (0 : ℝ) < 1 / 4).trans_le hu
  apply CenteredChildGeometry.live_length_lower (1 : Ideal (𝓞 K)) one_ne_zero
    Z (childLength K S D Γ T X H Z i) h hZ hwidth
  dsimp only [childLength]
  rw [map_one, Nat.cast_one, Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) hu0]
  linarith

variable (P : Finset (ActualPositiveIndex.Index K S D Γ T X H))
variable (Z L h : ℝ) (hZ : 1 < Z) (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
variable (hb : ∀ b ∈ T.cubes,
  height K (S : Set (HeightOneSpectrum (𝓞 K))) b ≤ Z ^ L)
variable (hfirst : 2 * T.scale.val ≤ Z ^ L) (hsecond : 4 * X ≤ Z ^ L)
variable (j : BoxIndex Z L)

include hZ hh hwidth hb hfirst hsecond in
/-- The three numerical hypotheses used by the centered child budget
follow from one real source record, the first center assignment and the
literal division of the original scale by that center. -/
theorem source_child_length_bounds
    (r c₁ : ℝ) (hc₁ : 0 < c₁) (hscale : X = Z ^ r / c₁)
    (side : Bool) (i : Idx)
    (hi : i ∈ box K S D Γ T hmask X H P Z L j)
    (hcenter : c₁ ≤ FirstOuterCenters.extractedNorm K S D T side i.1 i.2.1 ∧
      FirstOuterCenters.extractedNorm K S D T side i.1 i.2.1 ≤ 2 * c₁) :
    secondFormalColumn r (extractedLength Z j side) (length Z j .firstCommon)
        (length Z j .firstOverlap) (length Z j .secondCommon)
        (length Z j .secondOverlap) - 5 * h ≤ childLength K S D Γ T X H Z i ∧
      childLength K S D Γ T X H Z i ≤
        secondFormalColumn r (extractedLength Z j side) (length Z j .firstCommon)
          (length Z j .firstOverlap) (length Z j .secondCommon)
          (length Z j .secondOverlap) + 8 * h ∧
      -2 * h ≤ childLength K S D Γ T X H Z i := by
  have ha := coordinate_annulus K S D Γ T hmask X H P Z L h hZ hh hwidth
    hb hfirst hsecond j i hi
  rw [extractedNorm_eq_coordinates K S D Γ T hmask X H i side] at hcenter
  have hs := ActualCenterGeometry.two_log_length_bounds Z r
    (extractedLength Z j side) (length Z j .firstCommon)
    (length Z j .firstOverlap) (length Z j .secondCommon)
    (length Z j .secondOverlap) h
    (coordinateNorm K S D Γ (bare i) (extractedCoordinate side))
    (coordinateNorm K S D Γ (bare i) .firstCommon)
    (coordinateNorm K S D Γ (bare i) .firstOverlap)
    (coordinateNorm K S D Γ (bare i) .secondCommon)
    (coordinateNorm K S D Γ (bare i) .secondOverlap) c₁
    (DyadicSourcePartition.center (secondBin K S D Γ T X H i).val)
    hZ hc₁ (DyadicSourcePartition.center_pos _) hwidth
    (ha (extractedCoordinate side)) (ha .firstCommon) (ha .firstOverlap)
    (ha .secondCommon) (ha .secondOverlap) hcenter
    (second_center_window K S D Γ T hmask X H i)
  have he : childLength K S D Γ T X H Z i =
      Real.logb Z ((Z ^ r / c₁) /
        DyadicSourcePartition.center (secondBin K S D Γ T X H i).val) := by
    change Real.logb Z (X / _) = _
    exact congrArg (fun x : ℝ => Real.logb Z (x /
      DyadicSourcePartition.center (secondBin K S D Γ T X H i).val)) hscale
  refine ⟨?_, ?_, childLength_live_lower K S D Γ T X H Z h hZ hwidth i⟩
  · simpa only [he, secondFormalColumn] using hs.1
  · simpa only [he, secondFormalColumn] using hs.2

include hZ hh hwidth hb hfirst hsecond in
/-- The production version uses the actual deterministic first-center
assignment. No window is asserted independently of the original source. -/
theorem source_child_length_from_assignment
    {ι : Type*} [Fintype ι] (grid : ι → {r : ℝ // 0 < r})
    (centers : FirstOuterCenters.Centering K S D T grid) (k : ι)
    (r : ℝ) (hscale : X = Z ^ r / (grid k).val)
    (side : Bool) (i : Idx)
    (hi : i ∈ box K S D Γ T hmask X H P Z L j)
    (hassign : centers.assignment side i.1 i.2.1 = k) :
    secondFormalColumn r (extractedLength Z j side) (length Z j .firstCommon)
        (length Z j .firstOverlap) (length Z j .secondCommon)
        (length Z j .secondOverlap) - 5 * h ≤ childLength K S D Γ T X H Z i ∧
      childLength K S D Γ T X H Z i ≤
        secondFormalColumn r (extractedLength Z j side) (length Z j .firstCommon)
          (length Z j .firstOverlap) (length Z j .secondCommon)
          (length Z j .secondOverlap) + 8 * h ∧
      -2 * h ≤ childLength K S D Γ T X H Z i := by
  exact source_child_length_bounds K S D Γ T hmask X H P Z L h hZ hh hwidth
    hb hfirst hsecond j r (grid k).val (grid k).property hscale side i hi
    ⟨by simpa only [hassign] using centers.lower side i.1 i.2.1,
      by simpa only [hassign] using centers.upper side i.1 i.2.1⟩

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualCenteredGeometry

end
