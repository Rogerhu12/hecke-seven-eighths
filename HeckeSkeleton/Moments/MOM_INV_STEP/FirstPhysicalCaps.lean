import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCappedFreeEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedRows

/-!
# Prescribed physical first row caps from the actual source

The free inverse radius is selected from the physical exponent before
the second transform. Its admissibility is proved from the true first
cube-digit geometry, actual source norm windows and frozen mask divisor.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstPhysicalCaps

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FirstParentRows FirstOuterCenters FirstLocalizedRows FirstLocalizedCutoff
  CanonicalNormPools
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
variable {σ : Type*} (T : FirstParentEnergy.Data K S (σ := σ))

def physicalCap (Z M r ell V eta tau : ℝ) (hZ : 0 < Z)
    (delta B j : OuterIndex K S D T → ℝ) (o : OuterIndex K S D T) :
    {r : ℝ // 0 < r} :=
  ⟨Z ^ (firstPhysicalHeight M r ell V (delta o) (B o) (j o) + 12 * eta + tau),
    Real.rpow_pos_of_pos hZ _⟩

theorem rowCap_le_physicalCap (F : {r : ℝ // 0 < r})
    (Z M r ell V eta tau : ℝ) (hZ : 1 ≤ Z) (heta : 0 ≤ eta)
    (hwidth : 2 ≤ Z ^ eta) (hr : T.radius.val = Z ^ (-M))
    (hX : T.scale.val = Z ^ r) (hF : F.val ≤ Z ^ (V + eta))
    (delta B j : OuterIndex K S D T → ℝ)
    (hd : ∀ o, (sIntegerElementNorm K Sset (FirstLocalizedEnergy.divisor K S D T o)).val ≤
      Z ^ (delta o + eta))
    (hb : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ (ell + eta))
    (hC : ∀ o, Z ^ (B o - eta) ≤
      commonNorm K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val)
    (hJ : ∀ o, Z ^ (j o - eta) ≤
      labelNorm K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val)
    (o : OuterIndex K S D T) :
    (rowCap K S
      (cubeDilation K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val)
      F (sourceCutoff K S D T Z tau (zero_lt_one.trans_le hZ) o)).val ≤
    (physicalCap K S D T Z M r ell V eta tau (zero_lt_one.trans_le hZ) delta B j o).val := by
  exact fine_row_rpow_bound K S D T.radius T.scale F Z M r ell V
    (delta o) (B o) (j o) eta tau hZ heta hwidth hr hX hF
    (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val
    o.2.2.2.val (hd o) (hb o.1.val o.1.property) (hb o.2.1.val o.2.1.property) (hC o) (hJ o)

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) [Γ.FiniteIndex]

theorem actual_rows_le_physicalCap (L : Finset Ext) (F : {r : ℝ // 0 < r})
    (hL : ∀ f ∈ L, height K Sset f ≤ F.val)
    (Z M r ell V eta tau : ℝ) (hZ : 1 ≤ Z) (heta : 0 ≤ eta)
    (hwidth : 2 ≤ Z ^ eta) (hr : T.radius.val = Z ^ (-M))
    (hX : T.scale.val = Z ^ r) (hF : F.val ≤ Z ^ (V + eta))
    (delta B j : OuterIndex K S D T → ℝ)
    (hd : ∀ o, (sIntegerElementNorm K Sset (FirstLocalizedEnergy.divisor K S D T o)).val ≤
      Z ^ (delta o + eta))
    (hb : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ (ell + eta))
    (hC : ∀ o, Z ^ (B o - eta) ≤
      commonNorm K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val)
    (hJ : ∀ o, Z ^ (j o - eta) ≤
      labelNorm K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val)
    (o : OuterIndex K S D T)
    (x : Ext × CanonicalSectors.UnitClasses K Sset Γ)
    (hx : x ∈ (sourceRows K S D Γ L
      (sourceCutoff K S D T Z tau (zero_lt_one.trans_le hZ) o).val).image
      (FirstRowGeometry.row K S Γ (cubeDilation K S
        (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val))) :
    (x.1.val.val.absNorm : ℝ) ≤
    (physicalCap K S D T Z M r ell V eta tau (zero_lt_one.trans_le hZ) delta B j o).val := by
  exact (sourceRows_row_bound K S D Γ L
    (cubeDilation K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val)
    F (sourceCutoff K S D T Z tau (zero_lt_one.trans_le hZ) o) hL x hx).trans
      (rowCap_le_physicalCap K S D T F Z M r ell V eta tau hZ heta hwidth hr hX hF
        delta B j hd hb hC hJ o)

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstPhysicalCaps

end

