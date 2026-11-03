import HeckeSkeleton.Moments.MOM_INV_STEP.FirstOuterPhysicalCap
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstNormalizedSource
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorBudget
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualBoxGeometry
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualCenterGeometry

/-!
# The actual first error source in the predetermined norm boxes

The partition uses exactly `FirstOuterPhysicalCap.errorAssignment`, so
the previously chosen physical row cap is constant in each box. The
unique first center is retained as a function of the original source.
All annuli and the first physical scalar follow from the actual ideals.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorBoxes

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open CanonicalNormPools FirstParentRows FirstOuterCenters ActualProductionBoxes
  ActualBoxGeometry
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable {σ : Type*} (T : FirstParentEnergy.Data K S (σ := σ))
variable (hmask : T.mask = ∅)
local notation "Idx" => FirstErrorSource.Index K S D T
local notation "bare" i => FirstErrorSource.bare K S D Γ T hmask i

def box (I : Finset Idx) (Z L : ℝ) (j : BoxIndex Z L) : Finset Idx :=
  I.filter (fun i => FirstOuterPhysicalCap.errorAssignment K S D Γ T hmask Z L i = j)

@[simp] theorem mem_box (I : Finset Idx) (Z L : ℝ) (j : BoxIndex Z L) (i : Idx) :
    i ∈ box K S D Γ T hmask I Z L j ↔
      i ∈ I ∧ FirstOuterPhysicalCap.errorAssignment K S D Γ T hmask Z L i = j := by
  simp only [box, Finset.mem_filter]

theorem sum_boxes {A : Type*} [AddCommMonoid A]
    (I : Finset Idx) (Z L : ℝ) (F : Idx → A) :
    (∑ i ∈ I, F i) =
      ∑ j : BoxIndex Z L, ∑ i ∈ box K S D Γ T hmask I Z L j, F i := by
  simp only [box, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem coordinate_eq_outer_of_ne_overlap (i : Idx) (c : Coordinate)
    (hc : c ≠ .firstOverlap) :
    coordinateNorm K S D Γ (bare i) c = coordinateNorm K S D Γ
      (FirstOuterPhysicalCap.outerBare K S D Γ T hmask i.1) c := by
  cases c <;> try rfl
  exact (hc rfl).elim

theorem coordinate_cap (Y : ℝ) (hY : 1 ≤ Y)
    (hb : ∀ b ∈ T.cubes, height K Sset b ≤ Y)
    (hfirst : 2 * T.scale.val ≤ Y) (i : Idx) (c : Coordinate) :
    coordinateNorm K S D Γ (bare i) c ≤ Y ^ 3 := by
  by_cases hc : c = .firstOverlap
  · subst c
    have he : height K Sset (bare i).quotient ≤ 2 * T.scale.val :=
      FirstExtractedGeometry.overlap_height_le K S D T.scale _ _ _ _ i.2
    have hy2 : Y ≤ Y ^ 2 := by nlinarith
    have hy3 : Y ^ 2 ≤ Y ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_left hY (sq_nonneg Y)]
    exact he.trans (hfirst.trans (hy2.trans hy3))
  · rw [coordinate_eq_outer_of_ne_overlap K S D Γ T hmask i c hc]
    exact FirstOuterPhysicalCap.coordinate_cap K S D Γ T hmask Y hY hb hfirst i.1 c

theorem coordinate_annulus (I : Finset Idx) (Z L h : ℝ) (hZ : 1 < Z) (hL : 0 ≤ L)
    (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hb : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ L)
    (hfirst : 2 * T.scale.val ≤ Z ^ L) (j : BoxIndex Z L) (i : Idx)
    (hi : i ∈ box K S D Γ T hmask I Z L j) (c : Coordinate) :
    Z ^ (length Z j c - h) ≤ coordinateNorm K S D Γ (bare i) c ∧
      coordinateNorm K S D Γ (bare i) c ≤ Z ^ (length Z j c + h) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hcap := coordinate_cap K S D Γ T hmask (Z ^ L)
    (Real.one_le_rpow hZ.le hL) hb hfirst i c
  have hpow : (Z ^ L) ^ 3 = Z ^ (3 * L + 0) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
    congr 1
    ring
  rw [hpow] at hcap
  have ha := DyadicSourcePartition.label_bounds Z (3 * L) 0
    (coordinateNorm K S D Γ (bare i) c) (one_le_coordinateNorm K S D Γ _ c) hcap
  have hj := congrArg (fun f : BoxIndex Z L => f c) (Finset.mem_filter.mp hi).2
  change DyadicSourcePartition.label Z (3 * L) 0
    (coordinateNorm K S D Γ (bare i) c) = j c at hj
  rw [hj, DyadicSourcePartition.center_eq_rpow Z hZ] at ha
  change Z ^ length Z j c ≤ _ ∧ _ ≤ 2 * Z ^ length Z j c at ha
  refine ⟨(Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)).trans ha.1, ?_⟩
  calc
    _ ≤ 2 * Z ^ length Z j c := ha.2
    _ ≤ Z ^ h * Z ^ length Z j c :=
      mul_le_mul_of_nonneg_right hwidth (Real.rpow_nonneg hz.le _)
    _ = _ := by rw [← Real.rpow_add hz]; congr 1; ring

theorem radius_eq_of_box (I : Finset Idx) (Z L M r ell V h tau : ℝ)
    (hZ : 0 < Z) (j : BoxIndex Z L) (i : Idx)
    (hi : i ∈ box K S D Γ T hmask I Z L j) :
    (FirstOuterPhysicalCap.radius K S D Γ T hmask Z L M r ell V h tau hZ i.1).val =
      Z ^ (firstPhysicalHeight M r ell V (length Z j .firstDivisor)
        (length Z j .firstCommon) (length Z j .cubeLabel) + 12 * h + tau) := by
  rw [FirstOuterPhysicalCap.radius_eq_errorAssignment K S D Γ T hmask
    Z L M r ell V h tau hZ i, (Finset.mem_filter.mp hi).2]

theorem count_windows (I : Finset Idx) (Z L ell h : ℝ) (hZ : 1 < Z) (hL : 0 ≤ L)
    (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hb : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ L)
    (hfirst : 2 * T.scale.val ≤ Z ^ L)
    (hcube : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ (ell + h))
    (j : BoxIndex Z L) (i : Idx) (hi : i ∈ box K S D Γ T hmask I Z L j) :
    ((bare i).b₁.val.val.absNorm : ℝ) ≤ Z ^ (ell + h) ∧
    ((bare i).b₂.val.val.absNorm : ℝ) ≤ Z ^ (ell + h) ∧
    ((FirstErrorBudget.cubeConductor K S D Γ T hmask i).absNorm : ℝ) ≤
      Z ^ (length Z j .activeConductor + h) ∧
    Z ^ (length Z j .cubeLabel - h) ≤ ((bare i).cubeJ.absNorm : ℝ) ∧
    ((bare i).cubeJ.absNorm : ℝ) ≤ Z ^ (length Z j .cubeLabel + h) ∧
    ((bare i).firstCommon.absNorm : ℝ) ≤ Z ^ (length Z j .firstCommon + h) ∧
    ((bare i).quotient.val.val.absNorm : ℝ) ≤ Z ^ (length Z j .firstOverlap + h) := by
  have ha := coordinate_annulus K S D Γ T hmask I Z L h hZ hL hh hwidth hb hfirst j i hi
  exact ⟨hcube _ i.1.1.property, hcube _ i.1.2.1.property,
    (ha .activeConductor).2, (ha .cubeLabel).1, (ha .cubeLabel).2,
    (ha .firstCommon).2, (ha .firstOverlap).2⟩

theorem extracted_factor_annulus (I : Finset Idx) (Z L h : ℝ) (hZ : 1 < Z)
    (hL : 0 ≤ L) (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hb : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ L)
    (hfirst : 2 * T.scale.val ≤ Z ^ L) (j : BoxIndex Z L) (i : Idx)
    (hi : i ∈ box K S D Γ T hmask I Z L j) (side : Bool) :
    Z ^ (extractedLength Z j side + length Z j .firstCommon - 2 * h) ≤
      (Ideal.absNorm (FirstSourceColumns.extractedFactor K S (bare i).refs.1
        (bare i).refs.2 (bare i).b₁ (bare i).b₂ side).val.val : ℝ) ∧
    (Ideal.absNorm (FirstSourceColumns.extractedFactor K S (bare i).refs.1
      (bare i).refs.2 (bare i).b₁ (bare i).b₂ side).val.val : ℝ) ≤
      Z ^ (extractedLength Z j side + length Z j .firstCommon + 2 * h) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have ha := coordinate_annulus K S D Γ T hmask I Z L h hZ hL hh hwidth hb hfirst j i hi
  have he : (Ideal.absNorm (FirstSourceColumns.extractedFactor K S (bare i).refs.1
      (bare i).refs.2 (bare i).b₁ (bare i).b₂ side).val.val : ℝ) =
      coordinateNorm K S D Γ (bare i) (extractedCoordinate side) *
        coordinateNorm K S D Γ (bare i) .firstCommon := by
    rw [FirstSourceColumns.extractedFactor_val K S D,
      CanonicalConductor.commonResidualIdeal_eq_C, map_mul, Nat.cast_mul]
    cases side <;> rfl
  rw [he]
  have hn (c : Coordinate) : 0 ≤ coordinateNorm K S D Γ (bare i) c := Nat.cast_nonneg _
  constructor
  · have hp := mul_le_mul (ha (extractedCoordinate side)).1 (ha .firstCommon).1
      (Real.rpow_nonneg hz.le _) (hn _)
    convert hp using 1
    rw [← Real.rpow_add hz]
    congr 1
    dsimp only [extractedLength]
    ring
  · apply (mul_le_mul (ha (extractedCoordinate side)).2 (ha .firstCommon).2
      (hn _) (Real.rpow_nonneg hz.le _)).trans_eq
    rw [← Real.rpow_add hz]
    congr 1
    dsimp only [extractedLength]
    ring

variable {ι : Type*} [Fintype ι]
variable (grid : ι → {r : ℝ // 0 < r})
variable (centers : FirstOuterCenters.Centering K S D T grid) (side : Bool)

def assignedScale (i : Idx) : {r : ℝ // 0 < r} :=
  FirstCenteredPositiveEnergy.centerScale T.scale (grid (centers.assignment side i.1 i.2))

theorem assignedScale_bounds (I : Finset Idx) (Z L r h : ℝ) (hZ : 1 < Z) (hL : 0 ≤ L)
    (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hb : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ L)
    (hfirst : 2 * T.scale.val ≤ Z ^ L) (hscale : T.scale.val = Z ^ r)
    (j : BoxIndex Z L) (i : Idx) (hi : i ∈ box K S D Γ T hmask I Z L j) :
    Z ^ (r - extractedLength Z j side - length Z j .firstCommon -
      length Z j .firstOverlap - 3 * h) ≤ (assignedScale K S D T grid centers side i).val ∧
    (assignedScale K S D T grid centers side i).val ≤
      Z ^ (r - extractedLength Z j side - length Z j .firstCommon -
        length Z j .firstOverlap + 4 * h) := by
  have ha := coordinate_annulus K S D Γ T hmask I Z L h hZ hL hh hwidth hb hfirst j i hi
  have hc := And.intro (centers.lower side i.1 i.2) (centers.upper side i.1 i.2)
  have he : FirstOuterCenters.extractedNorm K S D T side i.1 i.2 =
      coordinateNorm K S D Γ (bare i) (extractedCoordinate side) *
        coordinateNorm K S D Γ (bare i) .firstCommon *
        coordinateNorm K S D Γ (bare i) .firstOverlap := by
    change (Ideal.absNorm (FirstSourceColumns.extractedFactor K S (bare i).refs.1
      (bare i).refs.2 (bare i).b₁ (bare i).b₂ side).val.val : ℝ) *
      height K Sset (bare i).quotient = _
    rw [FirstSourceColumns.extractedFactor_val K S D,
      CanonicalConductor.commonResidualIdeal_eq_C, map_mul, Nat.cast_mul]
    cases side <;> rfl
  rw [he] at hc
  change _ ≤ T.scale.val / _ ∧ T.scale.val / _ ≤ _
  rw [hscale]
  exact ActualCenterGeometry.first_scale_bounds Z r (extractedLength Z j side)
    (length Z j .firstCommon) (length Z j .firstOverlap) h
    (coordinateNorm K S D Γ (bare i) (extractedCoordinate side))
    (coordinateNorm K S D Γ (bare i) .firstCommon)
    (coordinateNorm K S D Γ (bare i) .firstOverlap)
    (grid (centers.assignment side i.1 i.2)).val
    (zero_lt_one.trans hZ) (grid _).property hwidth
    (ha (extractedCoordinate side)) (ha .firstCommon) (ha .firstOverlap) hc

theorem assigned_firstScalar_le (I : Finset Idx) (Z L M r ell V h : ℝ)
    (hZ : 1 < Z) (hL : 0 ≤ L) (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hb : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ L)
    (hfirst : 2 * T.scale.val ≤ Z ^ L)
    (hradius : T.radius.val = Z ^ (-M)) (hscale : T.scale.val = Z ^ r)
    (j : BoxIndex Z L) (i : Idx) (hi : i ∈ box K S D Γ T hmask I Z L j) :
    FirstNormalizedSource.firstScalar K S D T grid Z r ell V
      (centers.assignment side i.1 i.2) i ≤
      ActualPoissonScale.fieldConstant K *
        Z ^ (firstKappa M r ell V (length Z j .firstDivisor)
          (extractedLength Z j side) (length Z j .firstCommon)
          (length Z j .activeConductor) + 9 * h / 2) := by
  have ha := coordinate_annulus K S D Γ T hmask I Z L h hZ hL hh hwidth hb hfirst j i hi
  have hd : Z ^ (length Z j .firstDivisor - h) ≤
      (sIntegerElementNorm K Sset (FirstLocalizedEnergy.divisor K S D T i.1)).val := by
    have hd := (ha .firstDivisor).1
    change Z ^ (length Z j .firstDivisor - h) ≤
      ((ActualDivisorSectors.divisorIdeal K S
        (FirstLocalizedEnergy.divisor K S D T i.1)).val.val.absNorm : ℝ) at hd
    rwa [ActualDivisorSectors.divisorIdeal_norm] at hd
  have hconductor : Z ^ (length Z j .activeConductor - h) ≤
      FirstPoissonNormalization.cubeNorm K S D (outerAnchor K S D T i.1).1
        (outerAnchor K S D T i.1).2 i.1.1.val i.1.2.1.val := by
    rw [← FirstErrorBudget.cubeConductor_norm K S D Γ T hmask i]
    exact (ha .activeConductor).1
  exact FirstActualPrefactor.normalizedScalar_le K S D Z M r ell V
    (length Z j .firstDivisor) (extractedLength Z j side) (length Z j .firstCommon)
    (length Z j .activeConductor) h hZ.le hh T.radius T.scale
    (grid (centers.assignment side i.1 i.2)) (FirstLocalizedEnergy.divisor K S D T i.1)
    (outerAnchor K S D T i.1).1 (outerAnchor K S D T i.1).2 i.1.1.val i.1.2.1.val
    (FirstToSecondData.quotient K S D T i.1 i.2) side hradius hscale
    (centers.lower side i.1 i.2) hd hconductor
    (extracted_factor_annulus K S D Γ T hmask I Z L h hZ hL hh hwidth hb hfirst j i hi side).2

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorBoxes

end
