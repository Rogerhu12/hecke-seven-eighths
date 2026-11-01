import Expansion.PhysicalRecipeSchedule
import Expansion.ActualOuterComponents
import Expansion.ActualFiniteRowHeightBudget
import Expansion.PowerHeightTailAlgebra

/-!
# Literal remainders of the actual finite recipe schedule

The two scheduled sums keep the original selected rows and the same
global clipping endpoint as the large-row cutoff.  Their definitions have
no scale or height guard.  The first moves the initial contour to the
actual starting contour of the whole-bin move; the second is the literal
difference between that starting box and the final scheduled box.

The uniform moderate-face estimate sums the actual row envelope exactly
once.  It therefore has no factor equal to the number of shells, buffered
indices or sectors.  Its constants precede the scale, the height and all
of the selected rows.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler
open ExpansionInterfaces
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

local instance physicalRemainder_sectorFintype : Fintype (SixthUnitClasses K Sset) :=
  Fintype.ofFinite _

variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
local notation "muS" => (fun p : Sset => mu (Subtype.val p))
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]

variable (P : ProbeData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (E : RowEulerData K (S : Set (HeightOneSpectrum (𝓞 K))) P)
variable (omega psi : HeckeCharacter K)
variable {B e : ℝ} (hpsi : psi ∈ HeckePacket K omega)
variable (hB0 : 51 / 100 ≤ B) (hB1 : B ≤ 1) (he : 0 < e)
variable (hboundary : ∀ chi : HeckePacketIndex K omega,
  ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)

private theorem sum_selectedRows_value {Row Label M : Type*}
    [Fintype Label] [AddCommMonoid M]
    (rows : Finset Row) (select : Row → Label) (value : Row → M) :
    (∑ label, ∑ u ∈ selectedRows rows select label, value u) =
      ∑ u ∈ rows, value u := by
  simp only [selectedRows, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp

/-- Every selected schedule row is an original nonprincipal row below
the original global cutoff.  The assertion holds even at small scales. -/
theorem physicalRecipeRows_global_bounds (zeta Z H : ℝ)
    (j : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)))
    (c : PhysicalRecipeChoice K Sset B e) (u : FrequencyRow K Sset)
    (hu : u ∈ physicalRecipeRows K Sset P E omega psi hpsi hB0 hB1 he hboundary
      zeta Z H j c) :
    ¬principalFrequencyRow K Sset u ∧
      frequencyRowNorm K Sset u ≤ Z ^ (13 / 16 + zeta) := by
  simp only [physicalRecipeRows, clippedSelectedPhysicalRows, selectedRows,
    retainedShellRows, Finset.mem_filter] at hu
  exact ⟨hu.1.1.1.2.2, hu.1.1.2⟩

/-- The shell, buffered index and sector schedule counts every retained
row once, for arbitrary values in an additive commutative monoid. -/
theorem sum_physicalRecipeRows {M : Type*} [AddCommMonoid M]
    (zeta Z H : ℝ) (hZ : 1 < Z) (value : FrequencyRow K Sset → M) :
    (∑ j : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)),
      ∑ c : PhysicalRecipeChoice K Sset B e,
        ∑ u ∈ physicalRecipeRows K Sset P E omega psi hpsi hB0 hB1 he hboundary
          zeta Z H j c, value u) =
      ∑ u ∈ retainedGlobalRows K Sset Z (1 / 16) (13 / 16 + zeta), value u := by
  calc
    _ = ∑ j : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)),
        ∑ u ∈ physicalShellRows K Sset Z (1 / 16) (13 / 16 + zeta) j, value u := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Fintype.sum_prod_type]
      have hsector (b : RowBufferIndex B e) :
          (∑ d : SixthUnitClasses K Sset,
            ∑ u ∈ (clippedSelectedPhysicalRows K Sset omega psi {1} P E hpsi
              (physicalRecipe_trivial_twists K) hB0 hB1 he hboundary
              (Z ^ shellExponent Z (1 / 16) j.val) (Z ^ (13 / 16 + zeta)) H b).filter
                (fun u => u.sector = d), value u) =
            ∑ u ∈ clippedSelectedPhysicalRows K Sset omega psi {1} P E hpsi
              (physicalRecipe_trivial_twists K) hB0 hB1 he hboundary
              (Z ^ shellExponent Z (1 / 16) j.val) (Z ^ (13 / 16 + zeta)) H b,
                value u := by
        exact sum_selectedRows_value _ (fun u : FrequencyRow K Sset => u.sector) value
      simp only [physicalRecipeRows]
      simp_rw [hsector]
      exact sum_selectedRows_value _ _ value
    _ = _ := by
      rw [← biUnion_physicalShellRows K Sset hZ]
      symm
      apply Finset.sum_biUnion
      intro i _ j _ hij
      exact physicalShellRows_disjoint K Sset hZ hij

variable (g : PrimeWindowGeometry)

/-- The original initial-to-moderate horizontal faces on all scheduled
fixed rows.  There is no scale or height guard in this definition. -/
def physicalScheduledModerateFaces (zeta Z H : ℝ) : ℂ :=
  ∑ j : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)),
    ∑ c : PhysicalRecipeChoice K Sset B e,
      actualModerateInitialFaces K S mu P psi g
        (physicalRecipeRows K Sset P E omega psi hpsi hB0 hB1 he hboundary
          zeta Z H j c) Z H B e c.1.center

/-- The literal whole-bin difference, with the original kernel and the
same fixed rows at both endpoints.  The last shell remains clipped. -/
def physicalScheduledWholeBoundary (zeta Z H : ℝ) : ℂ :=
  ∑ j : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)),
    ∑ c : PhysicalRecipeChoice K Sset B e,
      ∑ u ∈ physicalRecipeRows K Sset P E omega psi hpsi hB0 hB1 he hboundary
        zeta Z H j c,
        (rowContourBox K Sset muS P psi E g ∅ u Z H
          (B + 20 * e) (1 - c.1.center - 6 * e) (17 / 50) -
          rowContourBox K Sset muS P psi E g ∅ u Z H
            (c.1.center + 16 * e) (1 - c.1.center - 6 * e) (17 / 50))

include nu in
/-- The original moderate initial block is the scheduled final block
sum plus its two literal contour differences.  Only the original common
packet boundary is used for the initial move. -/
theorem physicalScheduled_moderate_initial_transport
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hB : 7 / 8 < B) (he1 : e ≤ 1 / 10000)
    (zeta Z H : ℝ) (hZ : 1 < Z) (hH : 0 ≤ H) :
    finiteRowContourBlock K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
      g ∅ Z H (Z ^ (1 / 16 : ℝ)) (Z ^ (13 / 16 + zeta)) 5 5 3 =
      (∑ j : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)),
        ∑ c : PhysicalRecipeChoice K Sset B e,
          physicalRecipeBlockValue K Sset P (arithmeticHighEulerData K Sset P psi)
            omega psi hpsi hB0 hB1 he hboundary muS g ∅ zeta Z H j c) +
        physicalScheduledModerateFaces K S mu P (arithmeticHighEulerData K Sset P psi)
          omega psi hpsi hB0 hB1 he hboundary g zeta Z H +
        physicalScheduledWholeBoundary K S mu P (arithmeticHighEulerData K Sset P psi)
          omega psi hpsi hB0 hB1 he hboundary g zeta Z H := by
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  calc
    _ = ∑ j : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)),
        ∑ c : PhysicalRecipeChoice K Sset B e,
          ∑ u ∈ physicalRecipeRows K Sset P (arithmeticHighEulerData K Sset P psi)
            omega psi hpsi hB0 hB1 he hboundary zeta Z H j c,
            rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
              g ∅ u Z H 5 5 3 := by
      simpa only [finiteRowContourBlock, retainedGlobalRows] using
        (sum_physicalRecipeRows K S P (arithmeticHighEulerData K Sset P psi)
          omega psi hpsi hB0 hB1 he hboundary zeta Z H hZ
          (fun u => rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
            g ∅ u Z H 5 5 3)).symm
    _ = _ := by
      unfold physicalRecipeBlockValue physicalScheduledModerateFaces
        physicalScheduledWholeBoundary actualModerateInitialFaces
      simp_rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro u hu
      have hnon := (physicalRecipeRows_global_bounds K S P
        (arithmeticHighEulerData K Sset P psi) omega psi hpsi hB0 hB1 he hboundary
        zeta Z H j c u hu).1
      have ha := rowBufferIndex_center_range hB0 he c.1
      have hm := actual_moderate_row_initial_finite_transport K S mu nu P omega psi
        hpsi hAllowed g ∅ u hnon hB hB1 ha.1 ha.2 he he1 hZpos hH hboundary
      rw [← hm]
      ring

include nu in
/-- Summing the actual scheduled faces uses each original row once.
The constants precede zeta, Z, H and all selected finite bins. -/
theorem exists_physicalScheduledModerateFaces_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hB : 7 / 8 < B) (he1 : e ≤ 1 / 10000) (n : ℕ) :
    ∃ C Z0 : ℝ, 0 < C ∧ 2 ≤ Z0 ∧ ∀ zeta Z H : ℝ,
      0 ≤ zeta → Z0 ≤ Z → 0 ≤ H →
      ‖physicalScheduledModerateFaces K S mu P E omega psi hpsi hB0 hB1 he hboundary
        g zeta Z H‖ ≤
        C * Z ^ (moderateBoundaryScalePower + (13 / 16 + zeta) * (163 / 50)) /
          (1 + H) ^ n := by
  obtain ⟨Cr, Z0, hCr, hZ0, hr⟩ := exists_actual_moderate_horizontal_row_bound
    K S mu nu hcomplex P omega psi hpsi hAllowed g hB hB1 he he1 hboundary n
  obtain ⟨Cc, hCc, hcount⟩ := exists_finite_frequencyRow_power_count K Sset
  refine ⟨Cr * Cc, max Z0 2, mul_pos hCr hCc, le_max_right _ _, ?_⟩
  intro zeta Z H hzeta hZ hH
  have hZr : Z0 ≤ Z := (le_max_left _ _).trans hZ
  have hZ2 : 2 ≤ Z := (le_max_right _ _).trans hZ
  have hZ1 : 1 < Z := by linarith
  have hZpos : 0 < Z := zero_lt_one.trans hZ1
  have hU : 1 ≤ Z ^ (13 / 16 + zeta) :=
    Real.one_le_rpow hZ1.le (by linarith)
  let rows := retainedGlobalRows K Sset Z (1 / 16) (13 / 16 + zeta)
  have hcut : ∀ u ∈ rows, frequencyRowNorm K Sset u ≤ Z ^ (13 / 16 + zeta) := by
    intro u hu
    exact (mem_frequencyRows_iff K Sset _
      (Real.rpow_pos_of_pos hZpos _).le u).mp (Finset.mem_filter.mp hu).1
  have hmass := hcount (Z ^ (13 / 16 + zeta)) (113 / 50) hU (by norm_num) rows hcut
  norm_num only [show (113 / 50 : ℝ) + 1 = 163 / 50 by norm_num] at hmass
  have hscale : Z ^ moderateBoundaryScalePower *
      (Z ^ (13 / 16 + zeta)) ^ (163 / 50 : ℝ) =
      Z ^ (moderateBoundaryScalePower + (13 / 16 + zeta) * (163 / 50)) := by
    rw [← Real.rpow_mul hZpos.le, ← Real.rpow_add hZpos]
  unfold physicalScheduledModerateFaces actualModerateInitialFaces
  calc
    _ ≤ ∑ j : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)),
        ∑ c : PhysicalRecipeChoice K Sset B e,
          ∑ u ∈ physicalRecipeRows K Sset P E omega psi hpsi hB0 hB1 he hboundary
            zeta Z H j c,
            ‖actualOuterHorizontalFaces K S mu P psi g ∅ u Z H
              (B + 20 * e) (1 - c.1.center - 6 * e) (17 / 50)‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro c _
      exact norm_sum_le _ _
    _ ≤ ∑ j : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)),
        ∑ c : PhysicalRecipeChoice K Sset B e,
          ∑ u ∈ physicalRecipeRows K Sset P E omega psi hpsi hB0 hB1 he hboundary
            zeta Z H j c,
            Cr * Z ^ moderateBoundaryScalePower *
              frequencyRowNorm K Sset u ^ (113 / 50 : ℝ) / (1 + H) ^ n := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro c _
      apply Finset.sum_le_sum
      intro u hu
      have hnon := (physicalRecipeRows_global_bounds K S P E omega psi hpsi hB0 hB1 he
        hboundary zeta Z H j c u hu).1
      have ha := rowBufferIndex_center_range hB0 he c.1
      exact hr Z H hZr hH c.1.center ha.1 ha.2 u hnon
    _ = ∑ u ∈ rows, Cr * Z ^ moderateBoundaryScalePower *
        frequencyRowNorm K Sset u ^ (113 / 50 : ℝ) / (1 + H) ^ n :=
      sum_physicalRecipeRows K S P E omega psi hpsi hB0 hB1 he hboundary zeta Z H hZ1 _
    _ = (Cr * Z ^ moderateBoundaryScalePower / (1 + H) ^ n) *
        ∑ u ∈ rows, frequencyRowNorm K Sset u ^ (113 / 50 : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ ≤ (Cr * Z ^ moderateBoundaryScalePower / (1 + H) ^ n) *
        (Cc * (Z ^ (13 / 16 + zeta)) ^ (163 / 50 : ℝ)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (Cr * Cc) * (Z ^ moderateBoundaryScalePower *
        (Z ^ (13 / 16 + zeta)) ^ (163 / 50 : ℝ)) / (1 + H) ^ n := by ring
    _ = _ := by rw [hscale]

include nu in
/-- The scheduled moderate faces satisfy the external height-tail
contract with a fixed scale power, before tau or the requested order. -/
theorem physicalScheduledModerateFaces_powerHeightTailBound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hB : 7 / 8 < B) (he1 : e ≤ 1 / 10000)
    {zeta : ℝ} (hzeta : 0 ≤ zeta) :
    PowerHeightTailBound (physicalScheduledModerateFaces K S mu P E omega psi
      hpsi hB0 hB1 he hboundary g zeta) := by
  apply PowerHeightTailBound.of_uniform_decay (A := 0)
    (R := moderateBoundaryScalePower + (13 / 16 + zeta) * (163 / 50)) le_rfl
  intro n
  obtain ⟨C, Z0, hC, hZ0, hb⟩ := exists_physicalScheduledModerateFaces_bound
    K S mu nu P E omega psi hpsi hB0 hB1 he hboundary g hcomplex hAllowed hB he1 n
  refine ⟨C, Z0, hC, by linarith, ?_⟩
  intro Z H hZ hH
  have hZpos : 0 < Z := by linarith
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hinv : ((1 + H) ^ n)⁻¹ ≤ H ^ (-(n : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by linarith : 0 ≤ 1 + H)]
    exact Real.rpow_le_rpow_of_nonpos hHpos (by linarith)
      (neg_nonpos.mpr (Nat.cast_nonneg n))
  calc
    _ ≤ C * Z ^ (moderateBoundaryScalePower + (13 / 16 + zeta) * (163 / 50)) /
        (1 + H) ^ n := hb zeta Z H hzeta hZ hHpos.le
    _ ≤ C * Z ^ (moderateBoundaryScalePower + (13 / 16 + zeta) * (163 / 50)) *
        H ^ (-(n : ℝ)) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv (mul_nonneg hC.le (Real.rpow_nonneg hZpos.le _))
    _ = _ := by rw [Real.rpow_zero, mul_one]

end Expansion.Project

#print axioms Expansion.Project.sum_physicalRecipeRows
#print axioms Expansion.Project.physicalScheduledModerateFaces
#print axioms Expansion.Project.physicalScheduledWholeBoundary
#print axioms Expansion.Project.physicalScheduled_moderate_initial_transport
#print axioms Expansion.Project.exists_physicalScheduledModerateFaces_bound
#print axioms Expansion.Project.physicalScheduledModerateFaces_powerHeightTailBound
