import HeckeSkeleton.Moments.MOM_INV_STEP.ActualProductionBoxes
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualPacketProvenance

/-!
# Descent geometry of the actual nonempty norm boxes

The two extracted lengths remain separate until the first Cauchy side
is selected. The common-divisor gap, cube-label restriction and new
puncture bound follow from actual source ideals. Every triple in the
canonical packet inherits these facts through its source witness.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualBoxGeometry

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep HeckePort.Moments
open FixedTripleFibers CanonicalNormPools FirstParentRows ActualProductionBoxes
open scoped Classical BigOperators nonZeroDivisors

def extractedCoordinate (side : Bool) : Coordinate :=
  if side then .extractedRight else .extractedLeft

def extractedLength (Z : ℝ) {L : ℝ} (j : BoxIndex Z L) (side : Bool) : ℝ :=
  length Z j (extractedCoordinate side)

theorem extractedLength_nonneg (Z L : ℝ) (hZ : 1 < Z) (hL : 0 ≤ L)
    (j : BoxIndex Z L) (side : Bool) : 0 ≤ extractedLength Z j side :=
  (length_bounds Z L hZ hL j (extractedCoordinate side)).1

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
variable {σ : Type*} [DecidableEq σ]
variable (T : FirstParentEnergy.Data K S (σ := σ)) (hmask : T.mask = ∅)
variable (X : ℝ) (H : ActualPositiveIndex.Cutoff K S D T X)
local notation "Idx" => ActualPositiveIndex.Index K S D Γ T X H
local notation "bare" => ActualPositiveIndex.bare K S D Γ T hmask X H

variable (P : Finset (ActualPositiveIndex.Index K S D Γ T X H))
variable (Z L ell h : ℝ) (hZ : 1 < Z) (hh : 0 ≤ h)
variable (hwidth : 2 ≤ Z ^ h)
variable (hb : ∀ b ∈ T.cubes,
  height K (S : Set (HeightOneSpectrum (𝓞 K))) b ≤ Z ^ L)
variable (hfirst : 2 * T.scale.val ≤ Z ^ L) (hsecond : 4 * X ≤ Z ^ L)
variable (hcube : ∀ b ∈ T.cubes,
  height K (S : Set (HeightOneSpectrum (𝓞 K))) b ≤ Z ^ (ell + h))
variable (j : BoxIndex Z L)

theorem cubeNorm_eq_coordinate (i : Idx) :
    FirstPoissonNormalization.cubeNorm K S D
      (bare i).refs.1 (bare i).refs.2 (bare i).b₁ (bare i).b₂ =
      coordinateNorm K S D Γ (bare i) .activeConductor := by
  exact congrArg (fun J : Ideal (𝓞 K) => (Ideal.absNorm J : ℝ))
    (CanonicalGroupedGauss.cubeIdeal_val K S D
      (bare i).refs.1 (bare i).refs.2 (bare i).b₁ (bare i).b₂)

include hZ hh hwidth hb hfirst hsecond in
/-- The physical first Poisson denominator uses exactly the same
active-conductor coordinate as the automatic source partition. -/
theorem cubeNorm_annulus (i : Idx)
    (hi : i ∈ box K S D Γ T hmask X H P Z L j) :
    Z ^ (length Z j .activeConductor - h) ≤
      FirstPoissonNormalization.cubeNorm K S D
        (bare i).refs.1 (bare i).refs.2 (bare i).b₁ (bare i).b₂ ∧
      FirstPoissonNormalization.cubeNorm K S D
        (bare i).refs.1 (bare i).refs.2 (bare i).b₁ (bare i).b₂ ≤
          Z ^ (length Z j .activeConductor + h) := by
  rw [cubeNorm_eq_coordinate K S D Γ T hmask X H]
  exact coordinate_annulus K S D Γ T hmask X H P Z L h hZ hh hwidth
    hb hfirst hsecond j i hi .activeConductor

include hZ hh hwidth hb hfirst hsecond in
/-- The original first-side extracted factor is A_side C. Its two
actual norm windows supply the precise two-error annulus. -/
theorem extracted_factor_annulus (i : Idx)
    (hi : i ∈ box K S D Γ T hmask X H P Z L j) (side : Bool) :
    Z ^ (extractedLength Z j side + length Z j .firstCommon - 2 * h) ≤
      (Ideal.absNorm
        (FirstSourceColumns.extractedFactor K S (bare i).refs.1 (bare i).refs.2
          (bare i).b₁ (bare i).b₂ side).val.val : ℝ) ∧
      (Ideal.absNorm
        (FirstSourceColumns.extractedFactor K S (bare i).refs.1 (bare i).refs.2
          (bare i).b₁ (bare i).b₂ side).val.val : ℝ) ≤
        Z ^ (extractedLength Z j side + length Z j .firstCommon + 2 * h) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have ha := coordinate_annulus K S D Γ T hmask X H P Z L h hZ hh hwidth
    hb hfirst hsecond j i hi
  have he :
      (Ideal.absNorm
        (FirstSourceColumns.extractedFactor K S (bare i).refs.1 (bare i).refs.2
          (bare i).b₁ (bare i).b₂ side).val.val : ℝ) =
      coordinateNorm K S D Γ (bare i) (extractedCoordinate side) *
        coordinateNorm K S D Γ (bare i) .firstCommon := by
    rw [FirstSourceColumns.extractedFactor_val K S D,
      CanonicalConductor.commonResidualIdeal_eq_C, map_mul, Nat.cast_mul]
    cases side <;> rfl
  rw [he]
  constructor
  · have hp := mul_le_mul (ha (extractedCoordinate side)).1 (ha .firstCommon).1
      (Real.rpow_nonneg hz.le _) (by
        unfold coordinateNorm
        exact Nat.cast_nonneg _)
    convert hp using 1
    rw [← Real.rpow_add hz]
    congr 1
    dsimp only [extractedLength]
    ring
  · have hp := mul_le_mul (ha (extractedCoordinate side)).2 (ha .firstCommon).2
      (by
        unfold coordinateNorm
        exact Nat.cast_nonneg _)
      (Real.rpow_nonneg hz.le _)
    apply hp.trans_eq
    rw [← Real.rpow_add hz]
    congr 1
    dsimp only [extractedLength]
    ring

include hZ hh hwidth hb hfirst hsecond hcube in
/-- The common gap and cube-label length are certified by any real
source in the box; no child energy is used to assert either relation. -/
theorem source_common_and_label (i : Idx)
    (hi : i ∈ box K S D Γ T hmask X H P Z L j) :
    -2 * h ≤ length Z j .secondCommon - length Z j .secondDivisor ∧
      length Z j .cubeLabel ≤ 2 * ell + 3 * h := by
  let B := bare i
  have ha := coordinate_annulus K S D Γ T hmask X H P Z L h hZ hh hwidth
    hb hfirst hsecond j i hi
  constructor
  · exact SourceLengths.common_gap B.valid (nonZeroDivisors.coe_ne_zero B.common.val)
      Z (length Z j .secondCommon) (length Z j .secondDivisor) h hZ
      (ha .secondDivisor).1 (ha .secondCommon).2
  · exact SourceLengths.cube_label_length B.valid B.newLabel_ne_zero B.outer_nonzero.1
      Z ell (length Z j .cubeLabel) h hZ
      (hcube _ i.1.1.property) (hcube _ i.1.2.1.property) (ha .cubeLabel).1

include hZ hh hwidth hb hfirst hsecond hcube in
theorem nonempty_common_and_label
    (hne : (box K S D Γ T hmask X H P Z L j).Nonempty) :
    -2 * h ≤ length Z j .secondCommon - length Z j .secondDivisor ∧
      length Z j .cubeLabel ≤ 2 * ell + 3 * h := by
  obtain ⟨i,hi⟩ := hne
  exact source_common_and_label K S D Γ T hmask X H P Z L ell h hZ hh hwidth
    hb hfirst hsecond hcube j i hi

include hZ hh hwidth hb hfirst hsecond hcube in
/-- The puncture belongs to the frozen triple alone. Its budget uses
the separate coarse cube-quotient bound, not the sharper counting box. -/
theorem source_puncture_bound (Rho : Ideal (𝓞 K)) (hRho : Rho ≠ 0)
    (Q V : ℝ) (hV : 0 ≤ V) (hL : 0 ≤ L)
    (hR : (Ideal.absNorm Rho.radical : ℝ) ≤ Z ^ Q)
    (side : Bool) (i : Idx)
    (hi : i ∈ box K S D Γ T hmask X H P Z L j) :
    Real.logb Z (Ideal.absNorm (childPuncture Rho (bare i).outer).radical : ℝ) ≤
      Q + decrease ell (extractedLength Z j side) (length Z j .firstOverlap)
        (length Z j .secondCommon) (length Z j .secondDivisor) V + 4 * h := by
  let B := bare i
  have ha := coordinate_annulus K S D Γ T hmask X H P Z L h hZ hh hwidth
    hb hfirst hsecond j i hi
  simpa only [decrease] using
    SourceLengths.puncture_length_from_source B.valid B.newLabel_ne_zero Rho hRho
      B.outer_nonzero.1 B.outer_nonzero.2.1 B.outer_nonzero.2.2
      Z Q ell (extractedLength Z j side) (length Z j .firstOverlap)
      (length Z j .secondCommon) (length Z j .secondDivisor) V h
      hZ (extractedLength_nonneg Z L hZ hL j side) hV hR
      (hcube _ i.1.1.property) (hcube _ i.1.2.1.property)
      (ha .firstOverlap).2 (ha .secondDivisor).1 (ha .secondCommon).2

include hZ hh hwidth hb hfirst hsecond hcube in
/-- Every automatically reconstructed packet triple receives the actual
puncture bound from its original source record. The prime lists, marks
and original unit sectors remain exactly those of the packet. -/
theorem packet_puncture_bound
    (hprime : ∀ k ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists k, Prime p)
    (hweights : ∀ k ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists k,
      ‖T.columns.primeWeights k p‖ ≤ 1)
    (J₁ J₂ : Finset σ) (hJ₁ : J₁ ⊆ T.columns.slots) (hJ₂ : J₂ ⊆ T.columns.slots)
    (side : Bool) (slotCap : ℕ) (hcap : T.columns.slots.card ≤ slotCap)
    (Rho : Ideal (𝓞 K)) (hRho : Rho ≠ 0)
    (Q V : ℝ) (hV : 0 ≤ V) (hL : 0 ≤ L)
    (hR : (Ideal.absNorm Rho.radical : ℝ) ≤ Z ^ Q) :
    let packet := ActualTwoPassChildren.packet K S T.columns D Γ hprime hweights
      J₁ J₂ hJ₁ hJ₂
      (ActualPositiveIndex.source K S D Γ T hmask X H
        (box K S D Γ T hmask X H P Z L j)) side slotCap hcap
    ∀ γ ∈ packet.triples,
      Real.logb Z (Ideal.absNorm (childPuncture Rho γ).radical : ℝ) ≤
        Q + decrease ell (extractedLength Z j side) (length Z j .firstOverlap)
          (length Z j .secondCommon) (length Z j .secondDivisor) V + 4 * h := by
  intro packet γ hγ
  obtain ⟨B,hB,rfl⟩ := ActualPacketProvenance.triple_member K S T.columns D Γ
    hprime hweights J₁ J₂ hJ₁ hJ₂
    (ActualPositiveIndex.source K S D Γ T hmask X H
      (box K S D Γ T hmask X H P Z L j)) side slotCap hcap γ hγ
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
  exact source_puncture_bound K S D Γ T hmask X H P Z L ell h hZ hh hwidth
    hb hfirst hsecond hcube j Rho hRho Q V hV hL hR side i hi

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualBoxGeometry

end

