import HeckeSkeleton.Moments.MOM_INV_STEP.FirstProductionChildren
import HeckeSkeleton.Moments.MOM_INV_STEP.SourceLengths

/-!
# Fixed norm boxes for the genuine two-pass production source

The twelve coordinates are the actual cube ideals, extracted factors,
first common factor and divisor, first overlap, fresh second common
factor and divisor, independent second overlap, cube label and active
cube conductor. They are computed from the production index; there is
no separately supplied list of source labels.

All coordinate caps follow from the original cube cap and the two
complete source pools. The finite grid is fixed before any new row or
label. Exact finite regrouping and its arbitrarily small-power box count
are proved, together with the sharp three-dimensional counting box.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualProductionBoxes

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalNormPools FirstParentRows FirstSourceDecomposition
  IdealMobiusMask
open scoped Classical BigOperators nonZeroDivisors

inductive Coordinate
  | cubeLeft | cubeRight | extractedLeft | extractedRight | firstCommon
  | firstDivisor | firstOverlap | secondCommon | secondDivisor | secondOverlap
  | cubeLabel | activeConductor
  deriving DecidableEq

instance coordinateFintype : Fintype Coordinate where
  elems := {.cubeLeft, .cubeRight, .extractedLeft, .extractedRight, .firstCommon,
    .firstDivisor, .firstOverlap, .secondCommon, .secondDivisor, .secondOverlap,
    .cubeLabel, .activeConductor}
  complete := by
    intro c
    cases c <;> simp

@[simp] theorem card_coordinate : Fintype.card Coordinate = 12 := by
  first
    | rfl
    | decide

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset

section Source

variable {N : Finset (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K))))} {X : ℝ}
local notation "Bare" => PositiveAssignedSource.BareSource
  (K := K) (S := S) (D := D) (Γ := Γ) (N := N) (X := X)

def activeConductor (B : Bare) : Ideal (𝓞 K) :=
  CubeLabels.R1 B.b₁.val B.b₂.val
    (PositiveReconstruction.Source.epsilon B.refs.1)
    (PositiveReconstruction.Source.epsilon B.refs.2)

def coordinateIdeal (B : Bare) : Coordinate → Ideal (𝓞 K)
  | .cubeLeft => B.b₁.val.val
  | .cubeRight => B.b₂.val.val
  | .extractedLeft => A B.refs.1.val B.b₁.val B.b₂.val
  | .extractedRight => A B.refs.2.val B.b₁.val B.b₂.val
  | .firstCommon => B.firstCommon
  | .firstDivisor => B.dk.val.val
  | .firstOverlap => B.quotient.val.val
  | .secondCommon => B.common.val.val
  | .secondDivisor => B.d₂.val.val
  | .secondOverlap => B.overlap.val.val
  | .cubeLabel => B.cubeJ
  | .activeConductor => activeConductor K S D Γ B

theorem coordinateIdeal_ne_zero (B : Bare) (c : Coordinate) :
    coordinateIdeal K S D Γ B c ≠ 0 := by
  cases c with
  | cubeLeft => exact nonZeroDivisors.coe_ne_zero B.b₁.val
  | cubeRight => exact nonZeroDivisors.coe_ne_zero B.b₂.val
  | extractedLeft => exact primeProduct_ne_bot _
  | extractedRight => exact primeProduct_ne_bot _
  | firstCommon => exact primeProduct_ne_bot _
  | firstDivisor => exact nonZeroDivisors.coe_ne_zero B.dk.val
  | firstOverlap => exact nonZeroDivisors.coe_ne_zero B.quotient.val
  | secondCommon => exact nonZeroDivisors.coe_ne_zero B.common.val
  | secondDivisor => exact nonZeroDivisors.coe_ne_zero B.d₂.val
  | secondOverlap => exact nonZeroDivisors.coe_ne_zero B.overlap.val
  | cubeLabel => exact B.cubeJ_ne_zero
  | activeConductor => exact primeProduct_ne_bot _

def coordinateNorm (B : Bare) (c : Coordinate) : ℝ :=
  (Ideal.absNorm (coordinateIdeal K S D Γ B c) : ℝ)

/-- Changing the bare frequency or its original Γ-sector does not
change any arithmetic box coordinate. -/
theorem coordinateNorm_frequency (B : Bare)
    (y : Ext × CanonicalSectors.UnitClasses K Sset Γ) (c : Coordinate) :
    coordinateNorm K S D Γ {B with frequency := y} c =
      coordinateNorm K S D Γ B c := by
  cases c <;> rfl

theorem one_le_coordinateNorm (B : Bare) (c : Coordinate) :
    1 ≤ coordinateNorm K S D Γ B c :=
  SourceLengths.one_le_norm_cap _ (coordinateIdeal_ne_zero K S D Γ B c) _ le_rfl

theorem norm_le_of_dvd (I J : Ideal (𝓞 K)) (hJ : J ≠ 0) (h : I ∣ J) :
    (Ideal.absNorm I : ℝ) ≤ Ideal.absNorm J := by
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz)))
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp h))

theorem activeConductor_dvd (B : Bare) :
    activeConductor K S D Γ B ∣ B.b₁.val.val * B.b₂.val.val := by
  apply dvd_trans (b := (B.b₁.val.val * B.b₂.val.val).radical)
  · change primeProduct ((CubeLabels.cubePrimeSupport B.b₁.val B.b₂.val).filter _) ∣ _
    rw [show (B.b₁.val.val * B.b₂.val.val).radical =
      primeProduct (CubeLabels.cubePrimeSupport B.b₁.val B.b₂.val) from
      radical_eq_primeProduct (B.b₁.val * B.b₂.val)]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  · exact Ideal.dvd_iff_le.mpr Ideal.le_radical

theorem oddSupport_dvd_active (B : Bare) :
    B.cubeS ∣ activeConductor K S D Γ B :=
  CubeLabels.s_dvd_R1 B.b₁.val B.b₂.val _ _

/-- The only large coordinate is the actual first mask divisor:
its three factors explain the cubic coarse cap. -/
theorem coordinateNorm_le_cube (B : Bare) (Y : ℝ) (hY : 1 ≤ Y)
    (hb₁ : height K Sset B.b₁ ≤ Y) (hb₂ : height K Sset B.b₂ ≤ Y)
    (hA₁ : (Ideal.absNorm (A B.refs.1.val B.b₁.val B.b₂.val) : ℝ) ≤ Y)
    (hA₂ : (Ideal.absNorm (A B.refs.2.val B.b₁.val B.b₂.val) : ℝ) ≤ Y)
    (hC : (Ideal.absNorm B.firstCommon : ℝ) ≤ Y)
    (he : height K Sset B.quotient ≤ Y)
    (hg : height K Sset B.common ≤ Y) (hv : height K Sset B.overlap ≤ Y)
    (c : Coordinate) : coordinateNorm K S D Γ B c ≤ Y ^ 3 := by
  have hy0 : 0 ≤ Y := zero_le_one.trans hY
  have hy2 : Y ≤ Y ^ 2 := by nlinarith
  have hy3 : Y ^ 2 ≤ Y ^ 3 := by
    calc
      Y ^ 2 = Y ^ 2 * 1 := (mul_one _).symm
      _ ≤ Y ^ 2 * Y := mul_le_mul_of_nonneg_left hY (sq_nonneg Y)
      _ = _ := by ring
  have hy : Y ≤ Y ^ 3 := hy2.trans hy3
  have hprod : (Ideal.absNorm (B.b₁.val.val * B.b₂.val.val) : ℝ) ≤ Y ^ 2 := by
    rw [map_mul, Nat.cast_mul]
    exact (mul_le_mul hb₁ hb₂ (height_pos K Sset B.b₂).le hy0).trans_eq (by ring)
  have hrad := (norm_le_of_dvd K (B.b₁.val.val * B.b₂.val.val).radical
    (B.b₁.val.val * B.b₂.val.val)
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero B.b₁.val)
      (nonZeroDivisors.coe_ne_zero B.b₂.val))
    (Ideal.dvd_iff_le.mpr Ideal.le_radical)).trans hprod
  have hd₁ : (Ideal.absNorm B.dk.val.val : ℝ) ≤ Y ^ 3 := by
    have h := norm_le_of_dvd K B.dk.val.val
      (B.firstCommon * (B.b₁.val.val * B.b₂.val.val).radical)
      (mul_ne_zero (primeProduct_ne_bot _)
        (SourceLengths.radical_ne_zero _
          (mul_ne_zero (nonZeroDivisors.coe_ne_zero B.b₁.val)
            (nonZeroDivisors.coe_ne_zero B.b₂.val)))) B.dk_dvd
    rw [map_mul, Nat.cast_mul] at h
    exact h.trans ((mul_le_mul hC hrad (Nat.cast_nonneg _) hy0).trans_eq (by ring))
  have hd₂ := (norm_le_of_dvd K B.d₂.val.val B.common.val.val
    (nonZeroDivisors.coe_ne_zero B.common.val) B.d₂_dvd).trans hg
  have hJdvd : B.cubeJ ∣ B.b₁.val.val * B.b₂.val.val := by
    refine ⟨B.cubeQ ^ 2 * B.cubeJ2, ?_⟩
    change B.b₁.val.val * B.b₂.val.val =
      CubeLabels.J B.b₁.val B.b₂.val (PositiveReconstruction.Source.epsilon B.refs.1)
        (PositiveReconstruction.Source.epsilon B.refs.2) * (B.cubeQ ^ 2 * B.cubeJ2)
    rw [CubeLabels.J_eq_s_mul_J2, CubeLabels.actual_cube_decomposition]
    unfold PositiveReconstruction.Source.cubeQ PositiveReconstruction.Source.cubeJ2
    ring
  have hJ := (norm_le_of_dvd K B.cubeJ (B.b₁.val.val * B.b₂.val.val)
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero B.b₁.val)
      (nonZeroDivisors.coe_ne_zero B.b₂.val)) hJdvd).trans hprod
  have hR := (norm_le_of_dvd K (activeConductor K S D Γ B)
    (B.b₁.val.val * B.b₂.val.val)
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero B.b₁.val)
      (nonZeroDivisors.coe_ne_zero B.b₂.val))
    (activeConductor_dvd K S D Γ B)).trans hprod
  cases c with
  | cubeLeft => exact hb₁.trans hy
  | cubeRight => exact hb₂.trans hy
  | extractedLeft => exact hA₁.trans hy
  | extractedRight => exact hA₂.trans hy
  | firstCommon => exact hC.trans hy
  | firstDivisor => exact hd₁
  | firstOverlap => exact he.trans hy
  | secondCommon => exact hg.trans hy
  | secondDivisor => exact hd₂.trans hy
  | secondOverlap => exact hv.trans hy
  | cubeLabel => exact hJ.trans hy3
  | activeConductor => exact hR.trans hy3

/-- The literal second physical cost is bounded from the actual
common/divisor ideals and the two genuine scale inequalities. The
normalization of the common factor is charged exactly once. -/
theorem source_physicalCost_le (B : Bare)
    (Z M r ell V delta A BLen j t g theta h tau rowCap scale : ℝ)
    (hZ : 1 ≤ Z) (hh : 0 ≤ h) (hrow0 : 0 ≤ rowCap) (hscale : 0 < scale)
    (hrow : rowCap ≤ Z ^ (firstPhysicalHeight M r ell V delta BLen j + 12 * h + tau))
    (hscaleLower : Z ^ (r - A - BLen - t - 3 * h) ≤ scale)
    (hd : Z ^ (theta - h) ≤ (Ideal.absNorm B.d₂.val.val : ℝ))
    (hg : (Ideal.absNorm B.common.val.val : ℝ) ≤ Z ^ (g + h)) :
    ActualPoissonScale.fieldConstant K * height K Sset B.commonResidual * rowCap / scale ≤
      ActualPoissonScale.fieldConstant K *
        Z ^ (secondLambda M r ell V delta A BLen j t g theta + 18 * h + tau) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hres := SourceLengths.common_residual_bound B.valid Z g theta h hz hd hg
  have hnum := mul_le_mul hres hrow hrow0 (Real.rpow_nonneg hz.le _)
  have he : Z ^ (g - theta + 2 * h) *
      Z ^ (firstPhysicalHeight M r ell V delta BLen j + 12 * h + tau) =
      Z ^ (secondLambda M r ell V delta A BLen j t g theta + 17 * h + tau) *
        Z ^ (r - A - BLen - t - 3 * h) := by
    rw [← Real.rpow_add hz, ← Real.rpow_add hz]
    congr 1
    unfold secondLambda
    ring
  have hratio : height K Sset B.commonResidual * rowCap / scale ≤
      Z ^ (secondLambda M r ell V delta A BLen j t g theta + 17 * h + tau) := by
    apply (div_le_iff₀ hscale).mpr
    exact hnum.trans (he.le.trans
      (mul_le_mul_of_nonneg_left hscaleLower (Real.rpow_nonneg hz.le _)))
  have hratio' : height K Sset B.commonResidual * rowCap / scale ≤
      Z ^ (secondLambda M r ell V delta A BLen j t g theta + 18 * h + tau) :=
    hratio.trans (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
  have hb := mul_le_mul_of_nonneg_left hratio'
    (ActualPoissonScale.fieldConstant_nonneg K)
  convert hb using 1 <;> ring

end Source

section Production

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable {σ : Type*}
variable (T : FirstParentEnergy.Data K S (σ := σ)) (hmask : T.mask = ∅)
variable (X : ℝ) (H : ActualPositiveIndex.Cutoff K S D T X)
local notation "Idx" => ActualPositiveIndex.Index K S D Γ T X H
local notation "bare" => ActualPositiveIndex.bare K S D Γ T hmask X H

/-- All extracted coordinates are bounded by the original complete
source pools, rather than by an assumed coordinate bound. -/
theorem actual_coordinate_cap (Y : ℝ) (hY : 1 ≤ Y)
    (hb : ∀ b ∈ T.cubes, height K Sset b ≤ Y)
    (hfirst : 2 * T.scale.val ≤ Y) (hsecond : 4 * X ≤ Y)
    (i : Idx) (c : Coordinate) :
    coordinateNorm K S D Γ (bare i) c ≤ Y ^ 3 := by
  let B := bare i
  have hm := FirstOuterCenters.anchor_mem K S D T i.1
  have hn₁ := (mem_dyadicPool K Sset T.scale.val B.refs.1).mp hm.1
  have hn₂ := (mem_dyadicPool K Sset T.scale.val B.refs.2).mp hm.2
  have hf := first_decomposition B.refs.1.val B.refs.2.val B.b₁.val B.b₂.val hn₁.1 hn₂.1
  have hA₁ : A B.refs.1.val B.b₁.val B.b₂.val ∣ B.refs.1.val.val :=
    ⟨C B.refs.1.val B.refs.2.val B.b₁.val B.b₂.val *
      u B.refs.1.val B.refs.2.val B.b₁.val B.b₂.val, hf.1.trans (by ring)⟩
  have hA₂ : A B.refs.2.val B.b₁.val B.b₂.val ∣ B.refs.2.val.val :=
    ⟨C B.refs.1.val B.refs.2.val B.b₁.val B.b₂.val *
      u B.refs.2.val B.refs.1.val B.b₁.val B.b₂.val, hf.2.trans (by ring)⟩
  have hC : B.firstCommon ∣ B.refs.1.val.val := by
    refine ⟨A B.refs.1.val B.b₁.val B.b₂.val *
      u B.refs.1.val B.refs.2.val B.b₁.val B.b₂.val, ?_⟩
    exact hf.1.trans (by change _ = C _ _ _ _ * _; ring)
  have he : height K Sset B.quotient ≤ 2 * T.scale.val :=
    FirstExtractedGeometry.overlap_height_le K S D T.scale _ _ _ _ i.2.1
  have hg : height K Sset B.common ≤ 4 * X := by
    have hg := (mem_squarefreePool K Sset (2 * X) B.common).mp B.common_mem
    nlinarith [hg.2]
  have hv : height K Sset B.overlap ≤ 4 * X := by
    have hp := SecondMobiusGeometry.product_bounds K S X B.common i.2.2.2.2.2
    have hlow := le_mul_of_one_le_left (height_pos K Sset B.overlap).le
      (height_one_le K Sset B.common)
    exact hlow.trans hp.2
  exact coordinateNorm_le_cube K S D Γ B Y hY
    (hb _ i.1.1.property) (hb _ i.1.2.1.property)
    ((norm_le_of_dvd K _ _ (nonZeroDivisors.coe_ne_zero B.refs.1.val) hA₁).trans
      (hn₁.2.2.trans hfirst))
    ((norm_le_of_dvd K _ _ (nonZeroDivisors.coe_ne_zero B.refs.2.val) hA₂).trans
      (hn₂.2.2.trans hfirst))
    ((norm_le_of_dvd K _ _ (nonZeroDivisors.coe_ne_zero B.refs.1.val) hC).trans
      (hn₁.2.2.trans hfirst))
    (he.trans hfirst) (hg.trans hsecond) (hv.trans hsecond) c

abbrev BoxIndex (Z L : ℝ) := Coordinate → DyadicSourcePartition.Index Z (3 * L) 0

def assignment (Z L : ℝ) (i : Idx) : BoxIndex Z L :=
  fun c => DyadicSourcePartition.label Z (3 * L) 0 (coordinateNorm K S D Γ (bare i) c)

def box (P : Finset Idx) (Z L : ℝ) (j : BoxIndex Z L) : Finset Idx :=
  P.filter (fun i => assignment K S D Γ T hmask X H Z L i = j)

@[simp] theorem mem_box (P : Finset Idx) (Z L : ℝ) (j : BoxIndex Z L) (i : Idx) :
    i ∈ box K S D Γ T hmask X H P Z L j ↔
      i ∈ P ∧ assignment K S D Γ T hmask X H Z L i = j := by
  simp only [box, Finset.mem_filter]

/-- This is valid for the original signed coefficients as well as for
the later positive source. No source term is discarded by the boxes. -/
theorem sum_boxes {A : Type*} [AddCommMonoid A]
    (P : Finset Idx) (Z L : ℝ) (F : Idx → A) :
    (∑ i ∈ P, F i) =
      ∑ j : BoxIndex Z L, ∑ i ∈ box K S D Γ T hmask X H P Z L j, F i := by
  simp only [box, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

def length (Z : ℝ) {L : ℝ} (j : BoxIndex Z L) (c : Coordinate) : ℝ :=
  DyadicSourcePartition.centerLength Z (j c).val

theorem length_bounds (Z L : ℝ) (hZ : 1 < Z) (hL : 0 ≤ L)
    (j : BoxIndex Z L) (c : Coordinate) :
    0 ≤ length Z j c ∧ length Z j c ≤ 3 * L := by
  simpa only [length, add_zero] using
    DyadicSourcePartition.centerLength_bounds Z (3 * L) 0 hZ (by positivity) (j c)

theorem coordinate_annulus (P : Finset Idx) (Z L h : ℝ) (hZ : 1 < Z)
    (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hb : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ L)
    (hfirst : 2 * T.scale.val ≤ Z ^ L) (hsecond : 4 * X ≤ Z ^ L)
    (j : BoxIndex Z L) (i : Idx)
    (hi : i ∈ box K S D Γ T hmask X H P Z L j) (c : Coordinate) :
    Z ^ (length Z j c - h) ≤ coordinateNorm K S D Γ (bare i) c ∧
      coordinateNorm K S D Γ (bare i) c ≤ Z ^ (length Z j c + h) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hone : 1 ≤ Z ^ L :=
    (height_one_le K Sset i.1.1.val).trans (hb _ i.1.1.property)
  have hcap := actual_coordinate_cap K S D Γ T hmask X H
    (Z ^ L) hone hb hfirst hsecond i c
  have hpow : (Z ^ L) ^ 3 = Z ^ (3 * L) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
    congr 1
    ring
  rw [hpow] at hcap
  have hj := congrArg (fun f : BoxIndex Z L => f c) (Finset.mem_filter.mp hi).2
  have hbnd := DyadicSourcePartition.label_bounds Z (3 * L) 0
    (coordinateNorm K S D Γ (bare i) c)
    (one_le_coordinateNorm K S D Γ (bare i) c) (by simpa only [add_zero] using hcap)
  change DyadicSourcePartition.label Z (3 * L) 0
    (coordinateNorm K S D Γ (bare i) c) = j c at hj
  rw [hj, DyadicSourcePartition.center_eq_rpow Z hZ] at hbnd
  change Z ^ length Z j c ≤ coordinateNorm K S D Γ (bare i) c ∧
    coordinateNorm K S D Γ (bare i) c ≤ 2 * Z ^ length Z j c at hbnd
  refine ⟨(Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)).trans hbnd.1, ?_⟩
  calc
    _ ≤ 2 * Z ^ length Z j c := hbnd.2
    _ ≤ Z ^ h * Z ^ length Z j c :=
      mul_le_mul_of_nonneg_right hwidth (Real.rpow_nonneg hz.le _)
    _ = _ := by rw [← Real.rpow_add hz]; congr 1; ring

/-- The frozen triple is constrained by the exact cube identity and
the actual second common/divisor relation. There are three distinct
norm coordinates, rather than an additional source-row count. -/
theorem triple_norm_box (P : Finset Idx) (Z L ell h : ℝ) (hZ : 1 < Z)
    (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hb : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ L)
    (hfirst : 2 * T.scale.val ≤ Z ^ L) (hsecond : 4 * X ≤ Z ^ L)
    (hcube : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ (ell + h))
    (j : BoxIndex Z L) (i : Idx)
    (hi : i ∈ box K S D Γ T hmask X H P Z L j) :
    (Ideal.absNorm (bare i).outer.q0 : ℝ) ≤
        Z ^ (ell + length Z j .activeConductor / 2 - length Z j .cubeLabel + 5 * h / 2) ∧
      (Ideal.absNorm (bare i).outer.quotient : ℝ) ≤ Z ^ (length Z j .firstOverlap + h) ∧
      (Ideal.absNorm (bare i).outer.residual : ℝ) ≤
        Z ^ (length Z j .secondCommon - length Z j .secondDivisor + 2 * h) := by
  let B := bare i
  have ha := coordinate_annulus K S D Γ T hmask X H P Z L h hZ hh hwidth
    hb hfirst hsecond j i hi
  refine ⟨?_, (ha .firstOverlap).2, ?_⟩
  · exact SourceLengths.cube_quotient_sharp_bound B.valid
      (activeConductor K S D Γ B)
      (coordinateIdeal_ne_zero K S D Γ B .activeConductor)
      (oddSupport_dvd_active K S D Γ B)
      Z ell (length Z j .activeConductor) (length Z j .cubeLabel) h
      (zero_lt_one.trans hZ)
      (hcube _ i.1.1.property) (hcube _ i.1.2.1.property)
      (ha .activeConductor).2 (ha .cubeLabel).1
  · exact SourceLengths.common_residual_bound B.valid Z
      (length Z j .secondCommon) (length Z j .secondDivisor) h
      (zero_lt_one.trans hZ) (ha .secondDivisor).1 (ha .secondCommon).2

/-- A nonempty arithmetic box forces each of its three counting caps
to be at least one. No numerical nonemptiness condition is assumed. -/
theorem triple_caps_one_of_nonempty (P : Finset Idx) (Z L ell h : ℝ) (hZ : 1 < Z)
    (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hb : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ L)
    (hfirst : 2 * T.scale.val ≤ Z ^ L) (hsecond : 4 * X ≤ Z ^ L)
    (hcube : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ (ell + h))
    (j : BoxIndex Z L) (hne : (box K S D Γ T hmask X H P Z L j).Nonempty) :
    1 ≤ Z ^ (ell + length Z j .activeConductor / 2 - length Z j .cubeLabel + 5 * h / 2) ∧
      1 ≤ Z ^ (length Z j .firstOverlap + h) ∧
      1 ≤ Z ^ (length Z j .secondCommon - length Z j .secondDivisor + 2 * h) := by
  obtain ⟨i,hi⟩ := hne
  have hbnd := triple_norm_box K S D Γ T hmask X H P Z L ell h hZ hh hwidth
    hb hfirst hsecond hcube j i hi
  exact SourceLengths.norm_box_caps_one (bare i).outer _ _ _
    (bare i).outer_nonzero.1 (bare i).outer_nonzero.2.1 (bare i).outer_nonzero.2.2 hbnd

/-- Squarefree live labels inherit the same bound; the bound itself is
valid even for a source whose original retained zero is zero. -/
theorem newLabel_norm_bound (P : Finset Idx) (Z L h : ℝ) (hZ : 1 < Z)
    (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hb : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ L)
    (hfirst : 2 * T.scale.val ≤ Z ^ L) (hsecond : 4 * X ≤ Z ^ L)
    (j : BoxIndex Z L) (i : Idx)
    (hi : i ∈ box K S D Γ T hmask X H P Z L j) :
    (Ideal.absNorm (bare i).newLabel : ℝ) ≤
      Z ^ (length Z j .firstCommon + length Z j .secondDivisor +
        length Z j .secondOverlap + length Z j .cubeLabel + 4 * h) := by
  have ha := coordinate_annulus K S D Γ T hmask X H P Z L h hZ hh hwidth
    hb hfirst hsecond j i hi
  have h₁ := mul_le_mul (ha .cubeLabel).2 (ha .firstCommon).2
    (Nat.cast_nonneg _) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  have h₂ := mul_le_mul h₁ (ha .secondDivisor).2
    (Nat.cast_nonneg _) (by positivity)
  have h₃ := mul_le_mul h₂ (ha .secondOverlap).2
    (Nat.cast_nonneg _) (by positivity)
  simpa only [PositiveReconstruction.Source.newLabel, map_mul, Nat.cast_mul,
    coordinateNorm, coordinateIdeal, ← Real.rpow_add (zero_lt_one.trans hZ),
    show (length Z j .cubeLabel + h + (length Z j .firstCommon + h) +
      (length Z j .secondDivisor + h) + (length Z j .secondOverlap + h)) =
      length Z j .firstCommon + length Z j .secondDivisor +
        length Z j .secondOverlap + length Z j .cubeLabel + 4 * h by ring] using h₃

end Production

/-- The twelve-dimensional grid costs one preassigned arbitrarily
small power, with a constant independent of Z and every source ideal. -/
theorem exists_box_count_bound (L pi : ℝ) (hL : 0 ≤ L) (hpi : 0 < pi) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Z : ℝ, 1 ≤ Z →
      (Fintype.card (BoxIndex Z L) : ℝ) ≤ C * Z ^ pi := by
  obtain ⟨C, hC, hb⟩ := DyadicSourcePartition.exists_bin_count_bound
    (3 * L) 0 (pi / 12) (by positivity) (by positivity)
  refine ⟨C ^ 12, one_le_pow₀ hC, ?_⟩
  intro Z hZ
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg _) (hb Z hZ) 12
  have he : (C * Z ^ (pi / 12)) ^ 12 = C ^ 12 * Z ^ pi := by
    rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hZ)]
    congr 1
    congr 1
    ring
  simpa only [BoxIndex, Fintype.card_fun, card_coordinate, Nat.cast_pow, he] using hp

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualProductionBoxes

end

