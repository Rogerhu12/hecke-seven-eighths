import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialSource
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialGeometry

/-!
# Actual initial norm boxes and their geometric source witnesses

Only the actual common ideal, actual divisor and independent overlap
select these three coordinates. A separate fixed bin is the provider's
real Mellin center. Every source record is present exactly once.
The row, label and frozen puncture bounds below are consequences of
membership in those actual boxes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialBoxes

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP
open FixedTripleFibers FixedTripleEnergy CanonicalNormPools ActualDivisorSectors
open ProviderInitialSource
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
variable (X : ℝ) (H : Cutoff K S)
local notation "Idx" => ProviderInitialSource.Index K S D Γ X H

def coordinate (i : Idx) (c : Fin 3) : Ext :=
  if c = 0 then common K S D Γ X H i
  else if c = 1 then divisor K S D Γ X H i else overlap K S D Γ X H i

def coordinateNorm (i : Idx) (c : Fin 3) : ℝ := height K Sset (coordinate K S D Γ X H i c)

theorem coordinateNorm_one_le (i : Idx) (c : Fin 3) :
    1 ≤ coordinateNorm K S D Γ X H i c := height_one_le K Sset _

theorem divisor_norm_le (i : Idx) :
    height K Sset (divisor K S D Γ X H i) ≤ height K Sset (common K S D Γ X H i) :=
  FirstMaskGeometry.absNorm_le_of_dvd K _ _
    (nonZeroDivisors.coe_ne_zero (common K S D Γ X H i).val)
    (divisor_dvd_common K S D Γ X H i)

theorem coordinateNorm_le (i : Idx) (c : Fin 3) :
    coordinateNorm K S D Γ X H i c ≤ 4 * X := by
  have hg : height K Sset (common K S D Γ X H i) ≤ 4 * X := by
    have hn := ((mem_squarefreePool K Sset (2 * X) i.1.val).mp i.1.property).2
    change height K Sset (common K S D Γ X H i) ≤ 2 * (2 * X) at hn
    linarith
  have hv : height K Sset (overlap K S D Γ X H i) ≤ 4 * X := by
    have hp := (SecondMobiusGeometry.product_bounds K S X i.1.val i.2.2.2).2
    exact (le_mul_of_one_le_left (height_pos K Sset _).le
      (height_one_le K Sset i.1.val)).trans hp
  fin_cases c
  · exact hg
  · exact (divisor_norm_le K S D Γ X H i).trans hg
  · exact hv

abbrev BoxIndex (Z A : ℝ) := Fin 3 → DyadicSourcePartition.Index Z A 0

def assignment (Z A : ℝ) (i : Idx) : BoxIndex Z A :=
  fun c => DyadicSourcePartition.label Z A 0 (coordinateNorm K S D Γ X H i c)

def box (P : Finset Idx) (Z A : ℝ) (j : BoxIndex Z A) : Finset Idx :=
  P.filter (fun i => assignment K S D Γ X H Z A i = j)

def binIndex (i : Idx) : SecondMobiusGeometry.Index X :=
  SecondMobiusGeometry.centerIndex K S X i.1.val i.2.2.2

def bin (P : Finset Idx) (b : SecondMobiusGeometry.Index X) : Finset Idx :=
  P.filter (fun i => binIndex K S D Γ X H i = b)

def boxed (P : Finset Idx) (b : SecondMobiusGeometry.Index X)
    (Z A : ℝ) (j : BoxIndex Z A) : Finset Idx :=
  box K S D Γ X H (bin K S D Γ X H P b) Z A j

theorem sum_boxes {B : Type*} [AddCommMonoid B]
    (P : Finset Idx) (Z A : ℝ) (F : Idx → B) :
    (∑ i ∈ P, F i) = ∑ j : BoxIndex Z A, ∑ i ∈ box K S D Γ X H P Z A j, F i := by
  simp only [box, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem sum_bins {B : Type*} [AddCommMonoid B] (P : Finset Idx) (F : Idx → B) :
    (∑ i ∈ P, F i) = ∑ b : SecondMobiusGeometry.Index X,
      ∑ i ∈ bin K S D Γ X H P b, F i := by
  simp only [bin, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem sum_boxed {B : Type*} [AddCommMonoid B]
    (P : Finset Idx) (Z A : ℝ) (F : Idx → B) :
    (∑ i ∈ P, F i) = ∑ b : SecondMobiusGeometry.Index X,
      ∑ j : BoxIndex Z A, ∑ i ∈ boxed K S D Γ X H P b Z A j, F i := by
  rw [sum_bins K S D Γ X H P F]
  exact Finset.sum_congr rfl (fun b _ => sum_boxes K S D Γ X H _ Z A F)

def length (Z : ℝ) {A : ℝ} (j : BoxIndex Z A) (c : Fin 3) : ℝ :=
  DyadicSourcePartition.centerLength Z (j c).val

theorem length_bounds (Z A : ℝ) (hZ : 1 < Z) (hA : 0 ≤ A)
    (j : BoxIndex Z A) (c : Fin 3) : 0 ≤ length Z j c ∧ length Z j c ≤ A := by
  simpa only [length, add_zero] using
    DyadicSourcePartition.centerLength_bounds Z A 0 hZ (by simpa using hA) (j c)

variable (P : Finset Idx) (b : SecondMobiusGeometry.Index X)
variable (Z A h : ℝ) (hZ : 1 < Z) (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
variable (hcap : 4 * X ≤ Z ^ A) (j : BoxIndex Z A)
local notation "Pbox" => boxed K S D Γ X H P b Z A j

include hZ hh hwidth hcap in
theorem coordinate_annulus (i : Idx) (hi : i ∈ Pbox) (c : Fin 3) :
    Z ^ (length Z j c - h) ≤ coordinateNorm K S D Γ X H i c ∧
      coordinateNorm K S D Γ X H i c ≤ Z ^ (length Z j c + h) := by
  have hz := zero_lt_one.trans hZ
  have hj := congrArg (fun f : BoxIndex Z A => f c) (Finset.mem_filter.mp hi).2
  have hb := DyadicSourcePartition.label_bounds Z A 0 (coordinateNorm K S D Γ X H i c)
    (coordinateNorm_one_le K S D Γ X H i c)
    (by simpa only [add_zero] using (coordinateNorm_le K S D Γ X H i c).trans hcap)
  change DyadicSourcePartition.label Z A 0 (coordinateNorm K S D Γ X H i c) = j c at hj
  rw [hj, DyadicSourcePartition.center_eq_rpow Z hZ] at hb
  change Z ^ length Z j c ≤ coordinateNorm K S D Γ X H i c ∧
    coordinateNorm K S D Γ X H i c ≤ 2 * Z ^ length Z j c at hb
  refine ⟨(Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)).trans hb.1, ?_⟩
  calc
    _ ≤ 2 * Z ^ length Z j c := hb.2
    _ ≤ Z ^ h * Z ^ length Z j c :=
      mul_le_mul_of_nonneg_right hwidth (Real.rpow_nonneg hz.le _)
    _ = _ := by rw [← Real.rpow_add hz]; congr 1; ring

include hZ hh hwidth hcap in

theorem common_gap (i : Idx) (hi : i ∈ Pbox) : -2 * h ≤ length Z j 0 - length Z j 1 := by
  have hg := coordinate_annulus K S D Γ X H P b Z A h hZ hh hwidth hcap j i hi 0
  have hd := coordinate_annulus K S D Γ X H P b Z A h hZ hh hwidth hcap j i hi 1
  have he := (Real.rpow_le_rpow_left_iff hZ).mp
    (hd.1.trans ((divisor_norm_le K S D Γ X H i).trans hg.2))
  linarith

include hZ hh hwidth hcap in

theorem label_norm (i : Idx) (hi : i ∈ Pbox) :
    ((newLabel K S D Γ X H i).absNorm : ℝ) ≤
      Z ^ ProviderInitialGeometry.labelLength (length Z j 1) (length Z j 2) h := by
  have hd := coordinate_annulus K S D Γ X H P b Z A h hZ hh hwidth hcap j i hi 1
  have hv := coordinate_annulus K S D Γ X H P b Z A h hZ hh hwidth hcap j i hi 2
  have hb := (ActualCenterGeometry.product_two_bounds Z
    (height K Sset (divisor K S D Γ X H i)) (height K Sset (overlap K S D Γ X H i))
    (length Z j 1) (length Z j 2) h (zero_lt_one.trans hZ) hd hv).2
  simpa only [newLabel, map_mul, Nat.cast_mul, height, ProviderInitialGeometry.labelLength] using hb

include hZ hh hwidth hcap in

theorem residual_norm (i : Idx) (hi : i ∈ Pbox) :
    height K Sset (residual K S D Γ X H i) ≤ Z ^ (length Z j 0 - length Z j 1 + 2 * h) := by
  have hz := zero_lt_one.trans hZ
  have hg := (coordinate_annulus K S D Γ X H P b Z A h hZ hh hwidth hcap j i hi 0).2
  have hd := (coordinate_annulus K S D Γ X H P b Z A h hZ hh hwidth hcap j i hi 1).1
  have he : height K Sset (divisor K S D Γ X H i) * height K Sset (residual K S D Γ X H i) =
      height K Sset (common K S D Γ X H i) := by
    have he := congrArg (fun I : Ideal (𝓞 K) => (I.absNorm : ℝ))
      (common_factorization K S D Γ X H i)
    simpa only [map_mul, Nat.cast_mul, height] using he
  calc
    _ ≤ Z ^ (length Z j 0 + h) / Z ^ (length Z j 1 - h) := by
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hz _)).mpr
      calc
        _ ≤ height K Sset (residual K S D Γ X H i) * height K Sset (divisor K S D Γ X H i) :=
          mul_le_mul_of_nonneg_left hd (height_pos K Sset _).le
        _ = height K Sset (common K S D Γ X H i) := by rw [mul_comm, he]
        _ ≤ _ := hg
    _ = _ := by rw [← Real.rpow_sub hz]; congr 1; ring

include hZ hh hwidth hcap in

theorem row_norm (rho : {r : ℝ // 0 < r}) (m L tau : ℝ)
    (hscale : X = Z ^ L) (hrho : rho.val ≤ Z ^ (-m))
    (hcutoff : H = SecondAdaptiveCutoff.fineCutoff K S rho X Z tau)
    (i : Idx) (hi : i ∈ Pbox) :
    ((newRow K S D Γ X H i).1.absNorm : ℝ) ≤
      Z ^ ProviderInitialGeometry.rowLength m L (length Z j 0) (length Z j 1) h tau := by
  have hg := (coordinate_annulus K S D Γ X H P b Z A h hZ hh hwidth hcap j i hi 0).1
  have hd := (coordinate_annulus K S D Γ X H P b Z A h hZ hh hwidth hcap j i hi 1).2
  have hk := (FirstDualTruncation.mem_sectorCutoff K S D Γ
    (H i.1.val i.2.1.val) i.2.2.1.val).mp i.2.2.1.property
  rw [hcutoff, hscale] at hk
  have hb := ProviderInitialGeometry.actual_row_bound K S rho Z m L
    (length Z j 0) (length Z j 1) h tau hZ hwidth i.1.val i.2.2.1.val.1
    (unitDivisor K S) i.2.1.val hrho (unitDivisor_norm K S) hg
    (by simpa only [coordinateNorm, coordinate, if_pos rfl, if_neg (by decide : (1 : Fin 3) ≠ 0),
      divisor, mask, height, divisorIdeal_norm] using hd) hk
  rw [newRow_actual]
  exact hb

include hZ hh hwidth hcap in

theorem child_length (L : ℝ) (hscale : X = Z ^ L) (i : Idx) (hi : i ∈ Pbox) :
    let N := Real.logb Z (SecondMobiusGeometry.childScale X b)
    ProviderInitialGeometry.formalColumn L (length Z j 0) (length Z j 2) - 2 * h ≤ N ∧
      N ≤ ProviderInitialGeometry.formalColumn L (length Z j 0) (length Z j 2) + 4 * h ∧
      -2 * h ≤ N := by
  have hbin : binIndex K S D Γ X H i = b :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
  have hg := coordinate_annulus K S D Γ X H P b Z A h hZ hh hwidth hcap j i hi 0
  have hv := coordinate_annulus K S D Γ X H P b Z A h hZ hh hwidth hcap j i hi 2
  have hb := SecondMobiusGeometry.centerIndex_bounds K S X i.1.val i.2.2.2
  change DyadicSourcePartition.center (binIndex K S D Γ X H i).val ≤ _ ∧
    _ ≤ 4 * DyadicSourcePartition.center (binIndex K S D Γ X H i).val at hb
  rw [hbin] at hb
  have hlen := ProviderInitialGeometry.center_log_bounds Z L (length Z j 0) (length Z j 2) h
    (height K Sset (common K S D Γ X H i)) (height K Sset (overlap K S D Γ X H i))
    (DyadicSourcePartition.center b.val) hZ (DyadicSourcePartition.center_pos _) hwidth hg hv hb
  have hU : 0 < SecondMobiusGeometry.childScale X b :=
    SecondMobiusGeometry.childScale_pos X (by rw [hscale]; exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) b
  have hlive : 1 ≤ 4 * SecondMobiusGeometry.childScale X b := by
    have hp := (SecondMobiusGeometry.product_bounds K S X i.1.val i.2.2.2).2
    unfold SecondMobiusGeometry.childScale
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (DyadicSourcePartition.center_pos b.val)).mpr
    linarith [hb.1]
  have hlower : -2 * h ≤ Real.logb Z (SecondMobiusGeometry.childScale X b) := by
    apply CenteredChildGeometry.live_length_lower (1 : Ideal (𝓞 K)) one_ne_zero Z _ h hZ hwidth
    rw [map_one, Nat.cast_one, Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) hU]
    exact hlive
  refine ⟨?_, ?_, hlower⟩
  · simpa only [SecondMobiusGeometry.childScale, hscale] using hlen.1
  · simpa only [SecondMobiusGeometry.childScale, hscale] using hlen.2

/-- Three arithmetic norm coordinates cost one preassigned small power. -/
theorem exists_box_count_bound (A pi : ℝ) (hA : 0 ≤ A) (hpi : 0 < pi) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Z : ℝ, 1 ≤ Z →
      (Fintype.card (BoxIndex Z A) : ℝ) ≤ C * Z ^ pi := by
  obtain ⟨C, hC, hb⟩ := DyadicSourcePartition.exists_bin_count_bound A 0 (pi / 3)
    (by simpa using hA) (by positivity)
  refine ⟨C ^ 3, one_le_pow₀ hC, ?_⟩
  intro Z hZ
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg _) (hb Z hZ) 3
  have he : (C * Z ^ (pi / 3)) ^ 3 = C ^ 3 * Z ^ pi := by
    rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hZ)]
    congr 1
    congr 1
    ring
  simpa only [BoxIndex, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, he] using hp

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialBoxes

end
