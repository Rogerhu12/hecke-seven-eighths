import HeckeSkeleton.Moments.MOM_INV_STEP.FirstPhysicalCaps
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualProductionBoxes
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorSource

/-!
# The prescribed first physical cap is constructed before production

The three lengths used for the free row radius are dyadic labels of
the actual first divisor, first common factor and cube label. They
depend only on the original outer source. A dummy unit completion is
used solely to share the arithmetic coordinate definitions; it never
serves as a Poisson source. Every actual second source has exactly the
same three coordinates, so its later norm box recovers the previously
chosen radius without reversing an inverse-radius inequality.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstOuterPhysicalCap

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open CanonicalNormPools FirstParentRows FirstOuterCenters FirstSourceDecomposition
  FirstInversePoisson ActualProductionBoxes
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
variable {σ : Type*} (T : FirstParentEnergy.Data K S (σ := σ))
variable (hmask : T.mask = ∅)

private theorem unit_common :
    unitIdeal K S ∈ squarefreePool K Sset (2 * (1 : ℝ)) := by
  rw [mem_squarefreePool]
  simp [height]

private theorem unit_overlap :
    (unitIdeal K S).val.val ∈ SecondMobiusGeometry.overlapPool K S 1 (unitIdeal K S) := by
  apply FullMobius.mem_divisorPool
  · change unitIdeal K S ∈ squarefreePool K Sset
      (2 * (1 : ℝ) / height K Sset (unitIdeal K S))
    simpa [height] using unit_common K S
  · exact (mem_idealDivisors (nonZeroDivisors.coe_ne_zero (unitIdeal K S).val)).mpr
      (dvd_refl _)

def outerBare (o : OuterIndex K S D T) :
    PositiveAssignedSource.BareSource (K := K) (S := S) (D := D) (Γ := Γ)
      (N := FirstParentEnergy.columnPool K S T) (X := 1) where
  b₁ := o.1.val
  b₂ := o.2.1.val
  extraction := o.2.2.1.val
  extraction_mem := o.2.2.1.property
  quotient := unitIdeal K S
  common := unitIdeal K S
  common_mem := unit_common K S
  overlap := unitIdeal K S
  overlap_mem := unit_overlap K S
  firstDivisor := o.2.2.2.val
  first_mem := by
    have ho := Finset.mem_powerset.mp o.2.2.2.property
    simpa only [FirstParentRetained.actualMask, FirstSourcePartition.actualMask, hmask]
      using ho
  secondDivisor := ∅
  second_mem := Finset.empty_subset _
  frequency := (unitIdeal K S, 1)
  oldAssigned := fun j => Fin.elim0 j
  newAssigned := fun j => Fin.elim0 j
  old_mem := fun j => Fin.elim0 j
  new_mem := fun j => Fin.elim0 j
  old_dvd := fun j => Fin.elim0 j
  new_dvd := fun j => Fin.elim0 j

def assignment (Z L : ℝ) (o : OuterIndex K S D T) : ActualProductionBoxes.BoxIndex Z L :=
  fun c => DyadicSourcePartition.label Z (3 * L) 0
    (coordinateNorm K S D Γ (outerBare K S D Γ T hmask o) c)

theorem firstDivisor_norm (o : OuterIndex K S D T) :
    coordinateNorm K S D Γ (outerBare K S D Γ T hmask o) .firstDivisor =
      (sIntegerElementNorm K Sset (FirstLocalizedEnergy.divisor K S D T o)).val := by
  exact ActualDivisorSectors.divisorIdeal_norm K S _

theorem firstCommon_norm (o : OuterIndex K S D T) :
    coordinateNorm K S D Γ (outerBare K S D Γ T hmask o) .firstCommon =
      FirstLocalizedRows.commonNorm K S
        (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val := by
  simp only [coordinateNorm, coordinateIdeal, PositiveReconstruction.Source.firstCommon,
    FirstLocalizedRows.commonNorm, height, FirstSourceColumns.commonIdeal_val,
    CanonicalConductor.commonResidualIdeal_eq_C]
  rfl

theorem cubeLabel_norm (o : OuterIndex K S D T) :
    coordinateNorm K S D Γ (outerBare K S D Γ T hmask o) .cubeLabel =
      FirstLocalizedRows.labelNorm K S
        (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val := by
  rfl

/-- Bounds for the original outer coordinate grid use only the parent
cube and complete column pools. There is no second source in this lemma. -/
theorem coordinate_cap (Y : ℝ) (hY : 1 ≤ Y)
    (hb : ∀ b ∈ T.cubes, height K Sset b ≤ Y)
    (hfirst : 2 * T.scale.val ≤ Y)
    (o : OuterIndex K S D T) (c : Coordinate) :
    coordinateNorm K S D Γ (outerBare K S D Γ T hmask o) c ≤ Y ^ 3 := by
  let B := outerBare K S D Γ T hmask o
  have hm := FirstOuterCenters.anchor_mem K S D T o
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
  have hunit : height K Sset (unitIdeal K S) ≤ Y := by
    simpa only [height, unitIdeal_val, map_one, Nat.cast_one] using hY
  exact coordinateNorm_le_cube K S D Γ B Y hY
    (hb _ o.1.property) (hb _ o.2.1.property)
    ((norm_le_of_dvd K _ _ (nonZeroDivisors.coe_ne_zero B.refs.1.val) hA₁).trans
      (hn₁.2.2.trans hfirst))
    ((norm_le_of_dvd K _ _ (nonZeroDivisors.coe_ne_zero B.refs.2.val) hA₂).trans
      (hn₂.2.2.trans hfirst))
    ((norm_le_of_dvd K _ _ (nonZeroDivisors.coe_ne_zero B.refs.1.val) hC).trans
      (hn₁.2.2.trans hfirst)) hunit hunit hunit c

theorem coordinate_annulus (Z L h : ℝ) (hZ : 1 < Z) (hL : 0 ≤ L)
    (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hb : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ L)
    (hfirst : 2 * T.scale.val ≤ Z ^ L)
    (o : OuterIndex K S D T) (c : Coordinate) :
    Z ^ (length Z (assignment K S D Γ T hmask Z L o) c - h) ≤
      coordinateNorm K S D Γ (outerBare K S D Γ T hmask o) c ∧
    coordinateNorm K S D Γ (outerBare K S D Γ T hmask o) c ≤
      Z ^ (length Z (assignment K S D Γ T hmask Z L o) c + h) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hcap := coordinate_cap K S D Γ T hmask (Z ^ L)
    (Real.one_le_rpow hZ.le hL) hb hfirst o c
  have hpow : (Z ^ L) ^ 3 = Z ^ (3 * L + 0) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
    congr 1
    norm_num
    ring
  rw [hpow] at hcap
  have ha := DyadicSourcePartition.label_bounds Z (3 * L) 0
    (coordinateNorm K S D Γ (outerBare K S D Γ T hmask o) c)
    (one_le_coordinateNorm K S D Γ _ c) hcap
  rw [DyadicSourcePartition.center_eq_rpow Z hZ] at ha
  change Z ^ length Z (assignment K S D Γ T hmask Z L o) c ≤ _ ∧
    _ ≤ 2 * Z ^ length Z (assignment K S D Γ T hmask Z L o) c at ha
  refine ⟨(Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)).trans ha.1, ?_⟩
  calc
    _ ≤ 2 * Z ^ length Z (assignment K S D Γ T hmask Z L o) c := ha.2
    _ ≤ Z ^ h * Z ^ length Z (assignment K S D Γ T hmask Z L o) c :=
      mul_le_mul_of_nonneg_right hwidth (Real.rpow_nonneg hz.le _)
    _ = _ := by rw [← Real.rpow_add hz]; congr 1; ring

def radius (Z L M r ell V h tau : ℝ) (hZ : 0 < Z) :
    OuterIndex K S D T → {r : ℝ // 0 < r} :=
  FirstPhysicalCaps.physicalCap K S D T Z M r ell V h tau hZ
    (fun o => length Z (assignment K S D Γ T hmask Z L o) .firstDivisor)
    (fun o => length Z (assignment K S D Γ T hmask Z L o) .firstCommon)
    (fun o => length Z (assignment K S D Γ T hmask Z L o) .cubeLabel)

/-- The actual first row fits the radius chosen from these original
three coordinates, before any second common ideal or frequency exists. -/
theorem rowCap_le_radius (Z L M r ell V h tau : ℝ) (hZ : 1 < Z) (hL : 0 ≤ L)
    (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hb : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ L)
    (hfirst : 2 * T.scale.val ≤ Z ^ L)
    (hcube : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ (ell + h))
    (hradius : T.radius.val = Z ^ (-M)) (hscale : T.scale.val = Z ^ r)
    (F : {r : ℝ // 0 < r}) (hF : F.val ≤ Z ^ (V + h))
    (o : OuterIndex K S D T) :
    (rowCap K S (cubeDilation K S (outerAnchor K S D T o).1
      (outerAnchor K S D T o).2 o.1.val o.2.1.val) F
      (FirstLocalizedCutoff.sourceCutoff K S D T Z tau (zero_lt_one.trans hZ) o)).val ≤
    (radius K S D Γ T hmask Z L M r ell V h tau (zero_lt_one.trans hZ) o).val := by
  apply FirstPhysicalCaps.rowCap_le_physicalCap K S D T F
    Z M r ell V h tau hZ.le hh hwidth hradius hscale hF
    (fun o => length Z (assignment K S D Γ T hmask Z L o) .firstDivisor)
    (fun o => length Z (assignment K S D Γ T hmask Z L o) .firstCommon)
    (fun o => length Z (assignment K S D Γ T hmask Z L o) .cubeLabel)
    ?_ hcube ?_ ?_ o
  · intro o
    simpa only [firstDivisor_norm] using
      (coordinate_annulus K S D Γ T hmask Z L h hZ hL hh hwidth hb hfirst o .firstDivisor).2
  · intro o
    simpa only [firstCommon_norm] using
      (coordinate_annulus K S D Γ T hmask Z L h hZ hL hh hwidth hb hfirst o .firstCommon).1
  · intro o
    simpa only [cubeLabel_norm] using
      (coordinate_annulus K S D Γ T hmask Z L h hZ hL hh hwidth hb hfirst o .cubeLabel).1

def errorAssignment (Z L : ℝ) (i : FirstErrorSource.Index K S D T) :
    ActualProductionBoxes.BoxIndex Z L :=
  fun c => DyadicSourcePartition.label Z (3 * L) 0
    (coordinateNorm K S D Γ (FirstErrorSource.bare K S D Γ T hmask i) c)

theorem radius_eq_errorAssignment (Z L M r ell V h tau : ℝ) (hZ : 0 < Z)
    (i : FirstErrorSource.Index K S D T) :
    (radius K S D Γ T hmask Z L M r ell V h tau hZ i.1).val =
      Z ^ (firstPhysicalHeight M r ell V
        (length Z (errorAssignment K S D Γ T hmask Z L i) .firstDivisor)
        (length Z (errorAssignment K S D Γ T hmask Z L i) .firstCommon)
        (length Z (errorAssignment K S D Γ T hmask Z L i) .cubeLabel) + 12 * h + tau) := rfl

section Production

variable [MeasurableSpace (sLocalNormOneGroup K Sset)]
  [BorelSpace (sLocalNormOneGroup K Sset)] [Γ.FiniteIndex]
variable (X : ℝ) (H : ActualPositiveIndex.Cutoff K S D T X)

theorem radius_eq_actualAssignment (Z L M r ell V h tau : ℝ) (hZ : 0 < Z)
    (i : ActualPositiveIndex.Index K S D Γ T X H) :
    (radius K S D Γ T hmask Z L M r ell V h tau hZ i.1).val =
      Z ^ (firstPhysicalHeight M r ell V
        (length Z (ActualProductionBoxes.assignment K S D Γ T hmask X H Z L i) .firstDivisor)
        (length Z (ActualProductionBoxes.assignment K S D Γ T hmask X H Z L i) .firstCommon)
        (length Z (ActualProductionBoxes.assignment K S D Γ T hmask X H Z L i) .cubeLabel) +
          12 * h + tau) := rfl

/-- A later actual source box recovers exactly the previously selected
first cap. No numerical row-cap premise remains to be chosen per box. -/
theorem radius_eq_of_box (P : Finset (ActualPositiveIndex.Index K S D Γ T X H))
    (Z L M r ell V h tau : ℝ) (hZ : 0 < Z) (j : ActualProductionBoxes.BoxIndex Z L)
    (i : ActualPositiveIndex.Index K S D Γ T X H)
    (hi : i ∈ ActualProductionBoxes.box K S D Γ T hmask X H P Z L j) :
    (radius K S D Γ T hmask Z L M r ell V h tau hZ i.1).val =
      Z ^ (firstPhysicalHeight M r ell V
        (length Z j .firstDivisor) (length Z j .firstCommon) (length Z j .cubeLabel) +
          12 * h + tau) := by
  have hj := (ActualProductionBoxes.mem_box K S D Γ T hmask X H P Z L j i).mp hi
  rw [radius_eq_actualAssignment K S D Γ T hmask X H Z L M r ell V h tau hZ i, hj.2]

end Production

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstOuterPhysicalCap

end
