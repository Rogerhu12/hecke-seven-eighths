import HeckeSkeleton.Moments.MOM_INV_STEP.SecondProductionBudget
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondProductionRestriction
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualCenteredGeometry
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondParentRadialBudget
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstActualPrefactor
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondCenteredRows

/-!
# The actual first slice and second box supply the physical child budget

The first activity and center conditions are imposed on the original
source before its second bin and arithmetic norm box are reconstructed.
The child length is the logarithm of the literal second scale. Its
annulus and its lower bound follow from a real source witness. The
second physical scalar is estimated from the original common and
divisor norms, the prescribed first row cap, and the actual first center.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualSingleBoxBudget

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers FixedTripleEnergy FirstParentRows FirstToSecondData CommonKernel
  CanonicalNormPools ActualProductionBoxes ActualBoxGeometry
open scoped Classical BigOperators nonZeroDivisors

/-- The divisor-count exponent is chosen from the a priori bounded
window, before any source ideal or norm-box coordinate is known. -/
def countingExponent (L hcap pi : ℝ) : ℝ := pi / (9 * L + 6 * hcap + 1)

theorem countingExponent_pos (L hcap pi : ℝ)
    (hL : 0 ≤ L) (hhcap : 0 ≤ hcap) (hpi : 0 < pi) :
    0 < countingExponent L hcap pi := by
  unfold countingExponent
  exact div_pos hpi (by linarith)

theorem counting_loss_le (L hcap pi : ℝ)
    (hL : 0 ≤ L) (hhcap : 0 ≤ hcap) (hpi : 0 < pi)
    (Z : ℝ) (hZ : 1 < Z) (ell h : ℝ) (hell : ell ≤ L) (hh : h ≤ hcap)
    (j : BoxIndex Z L) :
    countingExponent L hcap pi *
      (secondCount ell (length Z j .activeConductor) (length Z j .cubeLabel)
        (length Z j .firstOverlap) (length Z j .secondCommon)
        (length Z j .secondDivisor) + 11 * h / 2) ≤ pi := by
  have he := countingExponent_pos L hcap pi hL hhcap hpi
  have hbound : secondCount ell (length Z j .activeConductor) (length Z j .cubeLabel)
      (length Z j .firstOverlap) (length Z j .secondCommon)
      (length Z j .secondDivisor) + 11 * h / 2 ≤ 9 * L + 6 * hcap + 1 := by
    have hR := (length_bounds Z L hZ hL j .activeConductor).2
    have hJ := (length_bounds Z L hZ hL j .cubeLabel).1
    have ht := (length_bounds Z L hZ hL j .firstOverlap).2
    have hg := (length_bounds Z L hZ hL j .secondCommon).2
    have htheta := (length_bounds Z L hZ hL j .secondDivisor).1
    unfold secondCount
    linarith
  calc
    _ ≤ countingExponent L hcap pi * (9 * L + 6 * hcap + 1) :=
      mul_le_mul_of_nonneg_left hbound he.le
    _ = pi := by
      unfold countingExponent
      field_simp [show 9 * L + 6 * hcap + 1 ≠ 0 by linarith]

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "OS" => Set.integer Sset K

/-- This epsilon is fixed before the first source, either frequency,
the actual second common ideal, its divisor, and the two prime lists. -/
theorem exists_uniform_radialWeight_bound (lengthCap pi : ℝ)
    (hcap : 0 ≤ lengthCap) (hpi : 0 < pi) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ {σ : Type*} [DecidableEq σ] (T : FirstParentEnergy.Data K S (σ := σ))
        (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
        (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
        (hbase : 1 < T.columns.base)
        (R : OuterIndex K S D T → {r : ℝ // 0 < r})
        (U : {r : ℝ // 0 < r}) (J : Finset σ) (s : ℝ)
        (H₂ : ∀ o : OuterIndex K S D T, Ext → Finset (HeightOneSpectrum OS) → ℝ)
        (Z Rexp Lexp : ℝ),
        1 ≤ Z → Rexp ≤ lengthCap → Lexp ≤ lengthCap →
        (∀ o, (InverseRowMajorant.rowRadius (R o)).val ≤ Z ^ Rexp) →
        U.val ≤ Z ^ Lexp →
        ∀ i : ProductionIndex K S D T Θ ψ G hν hG hbase R U J s Γ H₂,
        SecondProductionPacket.radialWeight K S D Γ T Θ ψ G hν hG hbase
          R U J s H₂ ε i ≤ Z ^ pi := by
  obtain ⟨ε,hε,hbound⟩ := SecondParentRadialBudget.exists_uniform_small_power
    K S D Γ lengthCap pi hcap hpi
  refine ⟨ε,hε,?_⟩
  intro σ _ T Θ ψ G hν hG hbase R U J s H₂ Z Rexp Lexp hZ hRexp hLexp hR hU i
  let Q := data K S D T Θ ψ G hν hG hbase R U J s i.1 i.2.1
  let Q' := SecondAdaptiveRetained.dataAt K S D Γ Q (H₂ i.1) i.2.2.1
  exact hbound Q' Z Rexp Lexp hZ hRexp hLexp (hR i.1)
    (by change sourceScale K S T U ≤ Z ^ Lexp
        rwa [sourceScale_eq K S T hbase U])
    (SecondAdaptiveRetained.oldIndexAt K S D Γ Q (H₂ i.1) i.2.2.1)

variable {σ : Type*} [DecidableEq σ]
variable (T : FirstParentEnergy.Data K S (σ := σ))
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (hbase : 1 < T.columns.base)
variable (R : OuterIndex K S D T → {r : ℝ // 0 < r})
variable (U : {r : ℝ // 0 < r}) (J₁ : Finset σ) (s : ℝ)
variable (H₂ : ∀ o : OuterIndex K S D T, Ext → Finset (HeightOneSpectrum OS) → ℝ)
variable (hmask : T.mask = ∅)
local notation "X" => sourceScale K S T U
local notation "Idx" => ProductionIndex K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂
local notation "Eidx" => indexEquiv K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂
local notation "Hraw" => actualCutoff K S D T U H₂
local notation "Bsrc" => FirstToSecondData.bare K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂ hmask

variable {ι : Type*} [Fintype ι]
variable (grid : ι → {r : ℝ // 0 < r})
variable (centers : FirstOuterCenters.Centering K S D T grid)
variable (alive : OuterIndex K S D T → Prop) (k : ι) (side₁ : Bool)
variable (P : Finset Idx) (b : SecondMobiusGeometry.Index X)

/-- The original normalized first Poisson and centered Mellin scalar.
It is evaluated before any arithmetic norm box is selected. -/
def firstScalar (Z r ell V : ℝ)
    (o : OuterIndex K S D T) (e : FirstOuterCenters.Overlap K S D T o) : ℝ :=
  FirstActualPrefactor.normalizedScalar K S D Z r ell V T.radius T.scale (grid k)
    (FirstLocalizedEnergy.divisor K S D T o)
    (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val
    (FirstToSecondData.quotient K S D T o e)

theorem firstScalar_nonneg (Z r ell V : ℝ) (hZ : 0 ≤ Z)
    (o : OuterIndex K S D T) (e : FirstOuterCenters.Overlap K S D T o) :
    0 ≤ firstScalar K S D T grid k Z r ell V o e := by
  unfold firstScalar FirstActualPrefactor.normalizedScalar FirstActualPrefactor.columnScale
  exact mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hZ _)
      (FirstPoissonNormalization.outerFactor_nonneg K S D T.radius
        (FirstLocalizedEnergy.divisor K S D T o) _ _ _ _))
    (mul_nonneg (inv_nonneg.mpr (height_pos K Sset _).le) (sq_nonneg _))

/-- The first indicator is part of the genuine source set before the
second arithmetic box is formed. -/
def slice : Finset Idx :=
  SecondProductionRestriction.firstSlice K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
    side₁ grid centers alive k
    (SecondProductionIntegral.bin K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ P b)

variable (Z L : ℝ) (j : BoxIndex Z L)

def boxedSource : Finset Idx :=
  SecondProductionBoxes.normBox K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    (slice K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ grid centers alive k side₁ P b) Z L j

local notation "Pslice" => slice K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
  grid centers alive k side₁ P b
local notation "Pbox" => boxedSource K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
  grid centers alive k side₁ P b Z L j

theorem source_membership (i : Idx) (hi : i ∈ Pbox) :
    i ∈ P ∧ alive i.1 ∧ centers.assignment side₁ i.1 i.2.1 = k ∧
      SecondProductionIntegral.selectedCenter K S D Γ T Θ ψ G hν hG hbase
        R U J₁ s H₂ i = b ∧
      ActualProductionBoxes.assignment K S D Γ T hmask X Hraw Z L (Eidx i) = j := by
  have h₁ := Finset.mem_filter.mp hi
  have h₂ := Finset.mem_filter.mp h₁.1
  have h₃ := Finset.mem_filter.mp h₂.1
  exact ⟨h₃.1,h₂.2.1,h₂.2.2,h₃.2,h₁.2⟩

theorem source_raw_box (i : Idx) (hi : i ∈ Pbox) :
    Eidx i ∈ ActualProductionBoxes.box K S D Γ T hmask X Hraw
      (Pslice.image Eidx) Z L j := by
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_image.mpr ⟨i, (Finset.mem_filter.mp hi).1, rfl⟩,
      (Finset.mem_filter.mp hi).2⟩

variable (h : ℝ) (hZ : 1 < Z) (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
variable (hb : ∀ c ∈ T.cubes, height K Sset c ≤ Z ^ L)
variable (hfirst : 2 * T.scale.val ≤ Z ^ L) (hsecond : 4 * X ≤ Z ^ L)

include hZ hh hwidth hb hfirst hsecond in
/-- The first mask, conductor, and extracted factor bounds are inherited
from this source box; none is supplied as an independent window. -/
theorem source_first_prefactor_le (M r ell V : ℝ)
    (hradius : T.radius.val = Z ^ (-M)) (hX : T.scale.val = Z ^ r)
    (i : Idx) (hi : i ∈ Pbox) :
    firstScalar K S D T grid k Z r ell V i.1 i.2.1 ≤
      ActualPoissonScale.fieldConstant K *
        Z ^ (firstKappa M r ell V (length Z j .firstDivisor)
          (extractedLength Z j side₁) (length Z j .firstCommon)
          (length Z j .activeConductor) + (9 / 2 : ℝ) * h) := by
  have hm := source_membership K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ P b Z L j i hi
  have hr := source_raw_box K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ P b Z L j i hi
  have ha := ActualProductionBoxes.coordinate_annulus K S D Γ T hmask X Hraw
    (Pslice.image Eidx) Z L h hZ hh hwidth hb hfirst hsecond j (Eidx i) hr
  have hconductor := (ActualBoxGeometry.cubeNorm_annulus K S D Γ T hmask X Hraw
    (Pslice.image Eidx) Z L h hZ hh hwidth hb hfirst hsecond j (Eidx i) hr).1
  have hextracted := (ActualBoxGeometry.extracted_factor_annulus K S D Γ T hmask X Hraw
    (Pslice.image Eidx) Z L h hZ hh hwidth hb hfirst hsecond j (Eidx i) hr side₁).2
  have hd : Z ^ (length Z j .firstDivisor - h) ≤
      (sIntegerElementNorm K Sset (FirstLocalizedEnergy.divisor K S D T i.1)).val := by
    have hdiv := (ha .firstDivisor).1
    change Z ^ (length Z j .firstDivisor - h) ≤
      ((ActualDivisorSectors.divisorIdeal K S
        (FirstLocalizedEnergy.divisor K S D T i.1)).val.val.absNorm : ℝ) at hdiv
    rwa [ActualDivisorSectors.divisorIdeal_norm] at hdiv
  have hc : (grid k).val ≤
      FirstColumnAssembly.extractedHeight K S
        (outerAnchor K S D T i.1).1 (outerAnchor K S D T i.1).2
        i.1.1.val i.1.2.1.val side₁ (FirstToSecondData.quotient K S D T i.1 i.2.1) := by
    simpa only [hm.2.2.1, FirstOuterCenters.extractedNorm] using
      centers.lower side₁ i.1 i.2.1
  have hp := FirstActualPrefactor.normalizedScalar_le K S D
    Z M r ell V (length Z j .firstDivisor) (extractedLength Z j side₁)
    (length Z j .firstCommon) (length Z j .activeConductor) h hZ.le hh
    T.radius T.scale (grid k) (FirstLocalizedEnergy.divisor K S D T i.1)
    (outerAnchor K S D T i.1).1 (outerAnchor K S D T i.1).2 i.1.1.val i.1.2.1.val
    (FirstToSecondData.quotient K S D T i.1 i.2.1) side₁ hradius hX hc hd
    hconductor hextracted
  convert hp using 1 <;> try rfl
  congr 2
  ring

include hZ hh hwidth hb hfirst hsecond in
/-- The literal child scale supplies the three length conditions used
by the finite physical budget. No child's nonzero value is needed. -/
theorem source_length_bounds (r : ℝ) (hscale : U.val = Z ^ r / (grid k).val)
    (i : Idx) (hi : i ∈ Pbox) :
    secondFormalColumn r (extractedLength Z j side₁) (length Z j .firstCommon)
        (length Z j .firstOverlap) (length Z j .secondCommon)
        (length Z j .secondOverlap) - 5 * h ≤
      Real.logb Z (SecondMobiusGeometry.childScale X b) ∧
    Real.logb Z (SecondMobiusGeometry.childScale X b) ≤
      secondFormalColumn r (extractedLength Z j side₁) (length Z j .firstCommon)
        (length Z j .firstOverlap) (length Z j .secondCommon)
        (length Z j .secondOverlap) + 8 * h ∧
    -2 * h ≤ Real.logb Z (SecondMobiusGeometry.childScale X b) := by
  have hm := source_membership K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ P b Z L j i hi
  have hr := source_raw_box K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ P b Z L j i hi
  have hb' : ActualCenteredGeometry.secondBin K S D Γ T X Hraw (Eidx i) = b := hm.2.2.2.1
  have hs := ActualCenteredGeometry.source_child_length_from_assignment K S D Γ T hmask X Hraw
    (Pslice.image Eidx) Z L h hZ hh hwidth hb hfirst hsecond j grid centers k r
    ((sourceScale_eq K S T hbase U).trans hscale) side₁ (Eidx i) hr hm.2.2.1
  simpa only [ActualCenteredGeometry.childLength, hb'] using hs

include hZ hh hwidth hb hfirst hsecond in
/-- The first center gives the true column scale used by the second
Poisson cost. The formal exponent is not substituted for that scale. -/
theorem source_scale_bounds (r : ℝ) (hscale : U.val = Z ^ r / (grid k).val)
    (i : Idx) (hi : i ∈ Pbox) :
    Z ^ (r - extractedLength Z j side₁ - length Z j .firstCommon -
      length Z j .firstOverlap - 3 * h) ≤ U.val ∧
    U.val ≤ Z ^ (r - extractedLength Z j side₁ - length Z j .firstCommon -
      length Z j .firstOverlap + 4 * h) := by
  have hm := source_membership K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ P b Z L j i hi
  have hr := source_raw_box K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ P b Z L j i hi
  have ha := ActualProductionBoxes.coordinate_annulus K S D Γ T hmask X Hraw
    (Pslice.image Eidx) Z L h hZ hh hwidth hb hfirst hsecond j (Eidx i) hr
  have hc : (grid k).val ≤ FirstOuterCenters.extractedNorm K S D T side₁ i.1 i.2.1 ∧
      FirstOuterCenters.extractedNorm K S D T side₁ i.1 i.2.1 ≤ 2 * (grid k).val :=
    ⟨by simpa only [hm.2.2.1] using centers.lower side₁ i.1 i.2.1,
      by simpa only [hm.2.2.1] using centers.upper side₁ i.1 i.2.1⟩
  have he := ActualCenteredGeometry.extractedNorm_eq_coordinates
    K S D Γ T hmask X Hraw (Eidx i) side₁
  change FirstOuterCenters.extractedNorm K S D T side₁ i.1 i.2.1 = _ at he
  rw [he] at hc
  rw [hscale]
  exact ActualCenterGeometry.first_scale_bounds Z r
    (extractedLength Z j side₁) (length Z j .firstCommon) (length Z j .firstOverlap) h
    (coordinateNorm K S D Γ (Bsrc i) (extractedCoordinate side₁))
    (coordinateNorm K S D Γ (Bsrc i) .firstCommon)
    (coordinateNorm K S D Γ (Bsrc i) .firstOverlap) (grid k).val
    (zero_lt_one.trans hZ) (grid k).property hwidth
    (ha (extractedCoordinate side₁)) (ha .firstCommon) (ha .firstOverlap) hc

include hZ hh hwidth hb hfirst hsecond in
/-- Every numerical factor in the second physical cost is the original
source factor. Only the prescribed first physical row cap is an input. -/
theorem source_physicalCost_le (M r ell V tau : ℝ)
    (hscale : U.val = Z ^ r / (grid k).val)
    (i : Idx) (hi : i ∈ Pbox)
    (hrow : (R i.1).val ≤
      Z ^ (firstPhysicalHeight M r ell V (length Z j .firstDivisor)
        (length Z j .firstCommon) (length Z j .cubeLabel) + 12 * h + tau)) :
    FirstProductionWeight.physicalCost K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask i ≤
      ActualPoissonScale.fieldConstant K *
        Z ^ (secondLambda M r ell V (length Z j .firstDivisor)
          (extractedLength Z j side₁) (length Z j .firstCommon) (length Z j .cubeLabel)
          (length Z j .firstOverlap) (length Z j .secondCommon) (length Z j .secondDivisor) +
            18 * h + tau) := by
  have hr := source_raw_box K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ P b Z L j i hi
  have ha := ActualProductionBoxes.coordinate_annulus K S D Γ T hmask X Hraw
    (Pslice.image Eidx) Z L h hZ hh hwidth hb hfirst hsecond j (Eidx i) hr
  have hscale' := source_scale_bounds K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ P b Z L j h hZ hh hwidth hb hfirst hsecond r hscale i hi
  rw [FirstProductionWeight.physicalCost_eq]
  exact ActualProductionBoxes.source_physicalCost_le K S D Γ (Bsrc i)
    Z M r ell V (length Z j .firstDivisor) (extractedLength Z j side₁)
    (length Z j .firstCommon) (length Z j .cubeLabel) (length Z j .firstOverlap)
    (length Z j .secondCommon) (length Z j .secondDivisor) h tau (R i.1).val U.val
    hZ.le hh (R i.1).property.le U.property hrow hscale'.1
    (ha .secondDivisor).1 (ha .secondCommon).2

include hZ hh hwidth hb hfirst hsecond in
/-- The actual fine second cutoff bounds the literal reconstructed row.
The first cap is the one prescribed before forming the free inverse
energy, and the first center supplies the column upper window. -/
theorem source_row_bound (M r ell V tau : ℝ)
    (hscale : U.val = Z ^ r / (grid k).val)
    (hcutoff : H₂ = FirstToSecondData.fineCutoff K S D T R U Z tau)
    (i : Idx) (hi : i ∈ Pbox)
    (hrow : (R i.1).val =
      Z ^ (firstPhysicalHeight M r ell V (length Z j .firstDivisor)
        (length Z j .firstCommon) (length Z j .cubeLabel) + 12 * h + tau)) :
    (Ideal.absNorm (Bsrc i).newRow.1 : ℝ) ≤
      Z ^ (childM M ell (extractedLength Z j side₁) (length Z j .firstOverlap)
        (length Z j .secondCommon) (length Z j .secondDivisor) V
        (length Z j .cubeLabel) (5 * h)) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hr := source_raw_box K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ P b Z L j i hi
  have ha := ActualProductionBoxes.coordinate_annulus K S D Γ T hmask X Hraw
    (Pslice.image Eidx) Z L h hZ hh hwidth hb hfirst hsecond j (Eidx i) hr
  have hs := (source_scale_bounds K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ P b Z L j h hZ hh hwidth hb hfirst hsecond r hscale i hi).2
  have hd₁ : (sIntegerElementNorm K Sset (FirstLocalizedEnergy.divisor K S D T i.1)).val ≤
      Z ^ (length Z j .firstDivisor + h) := by
    have hd := (ha .firstDivisor).2
    change ((ActualDivisorSectors.divisorIdeal K S
      (FirstLocalizedEnergy.divisor K S D T i.1)).val.val.absNorm : ℝ) ≤ _ at hd
    rwa [ActualDivisorSectors.divisorIdeal_norm] at hd
  have hd₂ : (sIntegerElementNorm K Sset
      (sIntegerMaskGenerator K Sset i.2.2.1.2.1.val)).val ≤
      Z ^ (length Z j .secondDivisor + h) := by
    have hd := (ha .secondDivisor).2
    change ((ActualDivisorSectors.divisorIdeal K S
      (sIntegerMaskGenerator K Sset i.2.2.1.2.1.val)).val.val.absNorm : ℝ) ≤ _ at hd
    rwa [ActualDivisorSectors.divisorIdeal_norm] at hd
  have hk := (FirstDualTruncation.mem_sectorCutoff K S D Γ
    (H₂ i.1 i.2.2.1.1.val i.2.2.1.2.1.val) i.2.2.1.2.2.val).mp i.2.2.1.2.2.property
  have hcut := congrArg
    (fun f => f i.1 i.2.2.1.1.val i.2.2.1.2.1.val) hcutoff
  rw [hcut] at hk
  have hρ : (InverseRowMajorant.rowRadius (R i.1)).val ≤
      Z ^ (-(firstPhysicalHeight M r ell V (length Z j .firstDivisor)
        (length Z j .firstCommon) (length Z j .cubeLabel) + 12 * h + tau)) := by
    change (R i.1).val⁻¹ ≤ _
    rw [hrow, Real.rpow_neg hz.le]
  have hbound := SecondAdaptiveRows.centered_child_row_bound K S
    (InverseRowMajorant.rowRadius (R i.1)) X Z M r ell V
    (length Z j .firstDivisor) (extractedLength Z j side₁)
    (length Z j .firstCommon) (length Z j .cubeLabel) (length Z j .firstOverlap)
    (length Z j .secondCommon) (length Z j .secondDivisor) h tau
    (by rw [sourceScale_eq K S T hbase U]; exact U.property) hZ.le hwidth
    i.2.2.1.1.val i.2.2.1.2.2.val.1 (FirstLocalizedEnergy.divisor K S D T i.1)
    i.2.2.1.2.1.val hρ
    (by simpa only [sourceScale_eq K S T hbase U] using hs)
    (ha .secondCommon).1 hd₁ hd₂ hk
  rw [← FirstToSecondData.bare_newRow K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂ hmask i]
  exact hbound

variable (w : ∀ o : OuterIndex K S D T, FirstOuterCenters.Overlap K S D T o → ℝ)
variable (ε : ℝ)
variable (hprime : ∀ q ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists q, Prime p)
variable (hweights : ∀ q ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists q,
  ‖T.columns.primeWeights q p‖ ≤ 1)
variable (hJ₁ : J₁ ⊆ T.columns.slots) (J₂ : Finset σ) (hJ₂ : J₂ ⊆ T.columns.slots)
variable (slotCap : ℕ) (hcap : T.columns.slots.card ≤ slotCap)
local notation "packet" => SecondProductionPacket.packet K S D Γ T Θ ψ G hν hG hbase
  R U J₁ s H₂ hmask hprime hweights hJ₁ J₂ hJ₂ Pbox side₁ slotCap hcap
local notation "Nactual" => Real.logb Z (SecondMobiusGeometry.childScale X b)
local notation "ALen" => extractedLength Z j side₁
local notation "BLen" => length Z j .firstCommon
local notation "RLen" => length Z j .activeConductor
local notation "JLen" => length Z j .cubeLabel
local notation "deltaLen" => length Z j .firstDivisor
local notation "tLen" => length Z j .firstOverlap
local notation "gLen" => length Z j .secondCommon
local notation "thetaLen" => length Z j .secondDivisor
local notation "vLen" => length Z j .secondOverlap

/-- This finite image is proved from the original production index;
it is useful for transferring all source geometry to packet members. -/
theorem sourceOn_eq_bare_image :
    FirstProductionChildren.sourceOn K S D Γ T Θ ψ G hν hG hbase
      R U J₁ s H₂ hmask Pbox = Pbox.image Bsrc := by
  simp only [FirstProductionChildren.sourceOn, ActualPositiveIndex.source, Finset.image_image]
  rfl

include hZ hh hwidth hb hfirst hsecond in
/-- Every packet row has a genuine source witness in the same first
slice and fixed box, so it inherits the proved physical row decrease. -/
theorem packet_rows_bound (M r ell V tau : ℝ)
    (hscale : U.val = Z ^ r / (grid k).val)
    (hcutoff : H₂ = FirstToSecondData.fineCutoff K S D T R U Z tau)
    (hrow : ∀ i ∈ Pbox, (R i.1).val =
      Z ^ (firstPhysicalHeight M r ell V deltaLen BLen JLen + 12 * h + tau)) :
    ∀ y ∈ packet.rows, (Ideal.absNorm y.1 : ℝ) ≤
      Z ^ (childM M ell ALen tLen gLen thetaLen V JLen (5 * h)) := by
  intro y hy
  apply ActualPacketProvenance.rows_norm_bound K S T.columns D Γ hprime hweights
    J₁ J₂ hJ₁ hJ₂
    (FirstProductionChildren.sourceOn K S D Γ T Θ ψ G hν hG hbase
      R U J₁ s H₂ hmask Pbox) side₁ slotCap hcap _ ?_ y hy
  intro B hB
  rw [sourceOn_eq_bare_image K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ P b Z L j] at hB
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
  exact source_row_bound K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ P b Z L j h hZ hh hwidth hb hfirst hsecond
    M r ell V tau hscale hcutoff i hi (hrow i hi)

include hZ hh hwidth hb hfirst hsecond in
/-- The puncture budget belongs to each actual frozen triple and is
inherited before applying any child induction hypothesis. -/
theorem packet_puncture_bound (ell Q V : ℝ)
    (hcube : ∀ c ∈ T.cubes, height K Sset c ≤ Z ^ (ell + h))
    (hV : 0 ≤ V) (hL : 0 ≤ L)
    (Rho : Ideal (𝓞 K)) (hRho : Rho ≠ 0)
    (hRhoNorm : (Ideal.absNorm Rho.radical : ℝ) ≤ Z ^ Q) :
    ∀ γ ∈ packet.triples,
      Real.logb Z (Ideal.absNorm (childPuncture Rho γ).radical : ℝ) ≤
        Q + decrease ell ALen tLen gLen thetaLen V + 4 * h := by
  intro γ hγ
  obtain ⟨B,hB,rfl⟩ := ActualPacketProvenance.triple_member K S T.columns D Γ
    hprime hweights J₁ J₂ hJ₁ hJ₂
    (FirstProductionChildren.sourceOn K S D Γ T Θ ψ G hν hG hbase
      R U J₁ s H₂ hmask Pbox) side₁ slotCap hcap γ hγ
  rw [sourceOn_eq_bare_image K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ P b Z L j] at hB
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
  have hr := source_raw_box K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ P b Z L j i hi
  exact ActualBoxGeometry.source_puncture_bound K S D Γ T hmask X Hraw
    (Pslice.image Eidx) Z L ell h hZ hh hwidth hb hfirst hsecond hcube j
    Rho hRho Q V hV hL hRhoNorm side₁ (Eidx i) hr

include hZ in
theorem packet_puncture_nonneg (Rho : Ideal (𝓞 K)) (hRho : Rho ≠ 0) :
    ∀ γ ∈ packet.triples,
      0 ≤ Real.logb Z (Ideal.absNorm (childPuncture Rho γ).radical : ℝ) := by
  intro γ hγ
  obtain ⟨B,hB,rfl⟩ := ActualPacketProvenance.triple_member K S T.columns D Γ
    hprime hweights J₁ J₂ hJ₁ hJ₂
    (FirstProductionChildren.sourceOn K S D Γ T Θ ψ G hν hG hbase
      R U J₁ s H₂ hmask Pbox) side₁ slotCap hcap γ hγ
  have hp : childPuncture Rho B.outer ≠ 0 :=
    mul_ne_zero hRho (SourceLengths.radical_ne_zero _
      (mul_ne_zero (mul_ne_zero B.outer_nonzero.1 B.outer_nonzero.2.1) B.outer_nonzero.2.2))
  have hn : 0 < Ideal.absNorm (childPuncture Rho B.outer).radical :=
    Nat.pos_of_ne_zero (fun he => SourceLengths.radical_ne_zero _ hp
      (Ideal.absNorm_eq_zero_iff.mp he))
  exact Real.logb_nonneg hZ (by exact_mod_cast hn)

include hZ hh hwidth hb hfirst hsecond in
/-- Every real frozen triple has the two canonical margins and strict
row-length decrease. The center errors, lower live scale, common gap,
label length and puncture are all supplied by its actual source. -/
theorem packet_child_geometry (M r ell V Q z c d eta : ℝ)
    (hscale : U.val = Z ^ r / (grid k).val)
    (hcube : ∀ q ∈ T.cubes, height K Sset q ≤ Z ^ (ell + h))
    (hell : 0 ≤ ell) (hV : 0 ≤ V) (hL : 0 ≤ L)
    (hmesh : h ≤ eta / 16) (hstep : eta ≤ d / 16)
    (hparent : HeckePort.Moments.CanonicalMargins (r + 3 * ell + V) M Q z c)
    (hnonterminal : d ≤ ell + V)
    (Rho : Ideal (𝓞 K)) (hRho : Rho ≠ 0)
    (hRhoNorm : (Ideal.absNorm Rho.radical : ℝ) ≤ Z ^ Q) :
    ∀ γ ∈ packet.triples,
      let Fc := max 0 Nactual + secondFormalLabel BLen thetaLen vLen JLen + 4 * h
      let Mc := childM M ell ALen tLen gLen thetaLen V JLen (5 * h)
      let Qc := Real.logb Z (Ideal.absNorm (childPuncture Rho γ).radical : ℝ)
      c - 5 * eta ≤ Fc - Mc - Qc - z ∧
        c - 7 * eta ≤ 4 * Fc - 3 * Mc - 6 * z ∧
        3 * d / 2 ≤ M - Mc ∧ Fc ≤ r + 3 * ell + V + 11 * eta := by
  intro γ hγ
  have hpuncture := packet_puncture_bound K S D Γ T Θ ψ G hν hG hbase
    R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j h hZ hh hwidth hb hfirst hsecond
    hprime hweights hJ₁ J₂ hJ₂ slotCap hcap ell Q V hcube hV hL Rho hRho hRhoNorm γ hγ
  obtain ⟨B,hB,hγB⟩ := ActualPacketProvenance.triple_member K S T.columns D Γ
    hprime hweights J₁ J₂ hJ₁ hJ₂
    (FirstProductionChildren.sourceOn K S D Γ T Θ ψ G hν hG hbase
      R U J₁ s H₂ hmask Pbox) side₁ slotCap hcap γ hγ
  rw [sourceOn_eq_bare_image K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ P b Z L j] at hB
  obtain ⟨i,hi,hBi⟩ := Finset.mem_image.mp hB
  have hr := source_raw_box K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ P b Z L j i hi
  have hn := source_length_bounds K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ P b Z L j h hZ hh hwidth hb hfirst hsecond r hscale i hi
  have hcommon := ActualBoxGeometry.source_common_and_label K S D Γ T hmask X Hraw
    (Pslice.image Eidx) Z L ell h hZ hh hwidth hb hfirst hsecond hcube j (Eidx i) hr
  exact CenteredChildGeometry.centered_step M r ell V Q
    (Real.logb Z (Ideal.absNorm (childPuncture Rho γ).radical : ℝ)) z c d
    ALen BLen tLen gLen thetaLen vLen JLen h eta Nactual
    (childM M ell ALen tLen gLen thetaLen V JLen (5 * h)) hparent hh hmesh hstep
    hell (extractedLength_nonneg Z L hZ hL j side₁)
    (length_bounds Z L hZ hL j .firstOverlap).1 hV
    (length_bounds Z L hZ hL j .cubeLabel).1 hcommon.1 hcommon.2 hpuncture
    hnonterminal hn.1 hn.2.1 hn.2.2 le_rfl

include hZ hh hwidth hb hfirst hsecond in
/-- The actual restricted source integral satisfies the child bound.
The physical cost and all three actual-length premises are discharged
from source membership. The two remaining numerical inputs isolate the
first outer weight and the second radial small power; their estimates
do not concern an energy or a source reconstruction identity. -/
theorem sourceIntegral_le_smaller_children
    (M r ell V eta tau pi eps Cweight Cradial massEps : ℝ)
    (hmassEps : 0 < massEps) (hmesh : h ≤ eta / 16)
    (hscale : U.val = Z ^ r / (grid k).val)
    (hcube : ∀ c ∈ T.cubes, height K Sset c ≤ Z ^ (ell + h))
    (hCweight : 0 ≤ Cweight) (hCradial : 0 ≤ Cradial)
    (hloss : massEps * (secondCount ell RLen JLen tLen gLen thetaLen + 11 * h / 2) ≤ pi)
    (hrow : ∀ i ∈ Pbox, (R i.1).val ≤
      Z ^ (firstPhysicalHeight M r ell V deltaLen BLen JLen + 12 * h + tau))
    (hw : ∀ i ∈ Pbox, 0 ≤ w i.1 i.2.1)
    (hweight : ∀ i ∈ Pbox, w i.1 i.2.1 ≤
      Cweight * Z ^ (firstKappa M r ell V deltaLen ALen BLen RLen + (9 / 2 : ℝ) * h))
    (hradial : ∀ i ∈ Pbox,
      SecondProductionPacket.radialWeight K S D Γ T Θ ψ G hν hG hbase
        R U J₁ s H₂ ε i ≤ Cradial)
    (m : ℕ) (side₂ : Bool)
    (Cchild : LogPlane × ℝ → ℝ) (hCchild : ∀ p, 0 ≤ Cchild p)
    (htest : Integrable
      (fun p : LogPlane × ℝ => SecondProductionIntegral.jointDensity s m p * Cchild p)
      ((volume : Measure LogPlane).prod (volume : Measure ℝ)))
    (hchild : ∀ p : LogPlane × ℝ, ∀ γ ∈ packet.triples,
      normalizedChildEnergy Z (max 0 Nactual)
        (secondFormalLabel BLen thetaLen vLen JLen + 4 * h)
        slotCap packet.labels packet.rows
        (SecondProductionPacket.childFunction K S D Γ T Θ ψ hν U J₁ J₂ side₂ b p) γ ≤
      Cchild p * Z ^ (max 0 Nactual + secondFormalLabel BLen thetaLen vLen JLen + 4 * h + eps)) :
    SecondProductionIntegral.sourceIntegral K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
      w ε side₁ m side₂ Pbox b J₂ ≤
      ((Cweight * Cradial * ActualPoissonScale.fieldConstant K) *
        SecondProductionBudget.massConstant K S D Γ slotCap massEps hmassEps *
          Z ^ (r + 3 * ell + V + 40 * eta + tau + pi + eps)) *
        ∫ p : LogPlane × ℝ, SecondProductionIntegral.jointDensity s m p * Cchild p
          ∂((volume : Measure LogPlane).prod (volume : Measure ℝ)) := by
  have hCphysical : 0 ≤ Cweight * Cradial * ActualPoissonScale.fieldConstant K :=
    mul_nonneg (mul_nonneg hCweight hCradial) (ActualPoissonScale.fieldConstant_nonneg K)
  by_cases hne : Pbox.Nonempty
  · obtain ⟨i,hi⟩ := hne
    have hlength := source_length_bounds K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
      grid centers alive k side₁ P b Z L j h hZ hh hwidth hb hfirst hsecond r hscale i hi
    apply SecondProductionBudget.sourceIntegral_le_smaller_children
      K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε hmask
      Pslice Z L ell h j hprime hweights hJ₁ J₂ hJ₂ side₁ slotCap hcap
      M r V eta tau pi eps Nactual
      (Cweight * Cradial * ActualPoissonScale.fieldConstant K) massEps
      hmassEps hZ hh hmesh hwidth hb hfirst hsecond hcube hCphysical
      hlength.1 hlength.2.1 hlength.2.2 hloss m side₂ b hw
      _ Cchild hCchild htest hchild
    intro i hi
    have hphysical := source_physicalCost_le K S D Γ T Θ ψ G hν hG hbase
      R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j
      h hZ hh hwidth hb hfirst hsecond M r ell V tau hscale i hi (hrow i hi)
    have hsmall := mul_le_mul (hweight i hi) (hradial i hi)
      (SecondProductionPacket.radialWeight_nonneg K S D Γ T Θ ψ G hν hG hbase
        R U J₁ s H₂ ε i)
      (mul_nonneg hCweight (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
    have hbound := mul_le_mul hsmall hphysical
      (FirstProductionWeight.physicalCost_nonneg K S D Γ T Θ ψ G hν hG hbase
        R U J₁ s H₂ hmask i)
      (mul_nonneg
        (mul_nonneg hCweight (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) hCradial)
    exact hbound.trans_eq (by ring)
  · have hempty : Pbox = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [SecondProductionIntegral.sourceIntegral_eq_sum, hempty, Finset.sum_empty]
    apply mul_nonneg
    · exact mul_nonneg
        (mul_nonneg hCphysical
          (SecondProductionBudget.massConstant_pos K S D Γ slotCap massEps hmassEps).le)
        (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    · exact integral_nonneg (fun p =>
        mul_nonneg (SecondProductionIntegral.jointDensity_nonneg s m p) (hCchild p))

/-- Exact full production assembly with the first activity and center
indicator moved into every reconstructed box. No outer source count is
introduced, and all second bin and mark choices are retained. -/
theorem actualTotal_weightOn_eq_boxes (m : ℕ) (side₂ : Bool) :
    SecondProductionIntegral.actualTotal K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
      (SecondProductionRestriction.weightOn K S D T w
        (fun o e => alive o ∧ centers.assignment side₁ o e = k))
      ε side₁ m side₂ =
      SecondProductionIntegral.cauchyMass K S T J₁ s *
        ∑ b : SecondMobiusGeometry.Index X, ∑ J₂ ∈ (T.columns.slots \ J₁).powerset,
          ∑ j : BoxIndex Z L,
            SecondProductionIntegral.sourceIntegral K S D Γ T Θ ψ G hν hG hbase
              R U J₁ s H₂ w ε side₁ m side₂
              (boxedSource K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
                grid centers alive k side₁ Finset.univ b Z L j) b J₂ := by
  rw [SecondProductionRestriction.actualTotal_weightOn]
  apply congrArg (fun z : ℝ => SecondProductionIntegral.cauchyMass K S T J₁ s * z)
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro J₂ hJ₂
  exact SecondProductionBoxes.sourceIntegral_eq_normBoxes K S D Γ T Θ ψ G hν hG hbase
    R U J₁ s H₂ hmask w ε side₁ m side₂
    (slice K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ grid centers alive k side₁ Finset.univ b)
    b J₂ Z L

/-- A numerical majorant may be summed over the actual boxes after the
source theorem has supplied it. This finite aggregation retains each
original second marked subset and each actual frequency bin. -/
theorem actualTotal_weightOn_le_boxes (m : ℕ) (side₂ : Bool)
    (B : SecondMobiusGeometry.Index X → Finset σ → BoxIndex Z L → ℝ)
    (hB : ∀ b : SecondMobiusGeometry.Index X, ∀ J₂ ∈ (T.columns.slots \ J₁).powerset,
      ∀ j : BoxIndex Z L,
        SecondProductionIntegral.sourceIntegral K S D Γ T Θ ψ G hν hG hbase
          R U J₁ s H₂ w ε side₁ m side₂
          (boxedSource K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
            grid centers alive k side₁ Finset.univ b Z L j) b J₂ ≤ B b J₂ j) :
    SecondProductionIntegral.actualTotal K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
      (SecondProductionRestriction.weightOn K S D T w
        (fun o e => alive o ∧ centers.assignment side₁ o e = k))
      ε side₁ m side₂ ≤
      SecondProductionIntegral.cauchyMass K S T J₁ s *
        ∑ b : SecondMobiusGeometry.Index X, ∑ J₂ ∈ (T.columns.slots \ J₁).powerset,
          ∑ j : BoxIndex Z L, B b J₂ j := by
  rw [actualTotal_weightOn_eq_boxes K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ Z L w ε m side₂]
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Nat.cast_nonneg _)
      (SecondMellinEnergy.mellinMass_nonneg
        (SecondProductionIntegral.mellinTest s) (SecondProductionIntegral.mellinTest_support s)))
  apply Finset.sum_le_sum
  intro b hb
  apply Finset.sum_le_sum
  intro J₂ hJ₂
  exact Finset.sum_le_sum (fun j _ => hB b J₂ hJ₂ j)

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualSingleBoxBudget

end
