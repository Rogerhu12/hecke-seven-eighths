import HeckeSkeleton.HighBinSupport.ActualEulerRegion
import HeckeSkeleton.HighBinSupport.ActualNormFormFullCorrection

/-!
# Complete physical compensation on the whole Euler region

The finite-subset algebra used on dynamic contours also holds on the
principal residue rectangle. These proofs use the genuine local tables
and their proved product convergence on `rowEulerRegion`; the selected
local nonvanishing premise is subsequently supplied by a fixed prime cutoff.
No initial Fourier identity, contour move, or size estimate is assumed.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain Set Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HighBinVerified HighBinVerified.NormFormActual HighBinVerified.NormFormFullCorrection
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

private theorem regular_compensation_algebra (q qi V W D E H M c Y : ℂ)
    (hE : 1 - E ≠ 0) (hD : 1 - D ≠ 0) (hH : H ≠ 0)
    (hvalue : H = rowEulerRationalValue q qi V W D E)
    (hMD : M * D = c) (hcW : c * W = Y) :
    (M * (H - (1 - W * V) / (1 - D)) - Y * H) / H =
      -c + (1 - W) *
        (M * E * ((1 - qi) + W * (1 - V)) +
          c * ((1 - E) * (1 - D) * H - ((1 - V) + (q - 1) * W * V))) /
        ((1 - E) * (1 - D) * H) := by
  have hmarked : H - (1 - W * V) / (1 - D) =
      (1 - W) *
        (E * ((1 - qi) + W * (1 - V)) -
          D * ((1 - V) + (q - 1) * W * V)) / ((1 - E) * (1 - D)) := by
    rw [hvalue]
    unfold rowEulerRationalValue
    field_simp [hE, hD] <;> ring
  rw [hmarked, ← hcW]
  have hnum : M * ((1 - W) *
      (E * ((1 - qi) + W * (1 - V)) - D * ((1 - V) + (q - 1) * W * V))) =
      (1 - W) * (M * E * ((1 - qi) + W * (1 - V)) -
        c * ((1 - V) + (q - 1) * W * V)) := by
    calc
      _ = (1 - W) * (M * E * ((1 - qi) + W * (1 - V)) -
          (M * D) * ((1 - V) + (q - 1) * W * V)) := by ring
      _ = _ := by rw [hMD]
  rw [← mul_div_assoc, hnum]
  field_simp [hE, hD, hH] <;> ring

theorem actualLocalCompensation_regular_main_region (P : ProbeData K S)
    (psi : HeckeCharacter K) (u : FrequencyRow K S)
    (s w z : ℂ) (hv : (s, w, z) ∈ rowEulerRegion) (p : ExteriorPrime K S)
    (hp : p ∉ exteriorSupport K S u.ideal) (hpsi : UnramifiedAt K psi p.val)
    (hH : actualLocalUnmarked K S P psi u s w z p ≠ 0) :
    actualLocalCompensation K S P psi u s w z p =
      (p.val.asIdeal.absNorm : ℂ) ^ (z - 1) *
        (-conj (primeCoefficient K (arithmeticRowCharacter K S P u) p.val) +
          actualRegularCompensationError K S P psi u s w z p) := by
  let q : ℝ := (p.val.asIdeal.absNorm : ℝ)
  let V := (q : ℂ) ^ (-6 * z)
  let W := rowW K S P u p * (q : ℂ) ^ (-w)
  let D := rowD K S P psi u p * (q : ℂ) ^ (-s)
  let E := rowE K S P psi p * (q : ℂ) ^ (4 - 6 * s) * V
  let H := actualLocalUnmarked K S P psi u s w z p
  let M := conj (primeCoefficient K psi p.val) * (q : ℂ) ^ s
  let c := conj (rowW K S P u p)
  let Y := (q : ℂ) ^ (-w)
  have hq : 2 ≤ q := exteriorPrime_norm_two_le K S p
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith : q ≠ 0)
  have hcast : (q : ℂ) = (p.val.asIdeal.absNorm : ℂ) := by simp only [q, Complex.ofReal_natCast]
  have hpsiUnit : conj (primeCoefficient K psi p.val) * primeCoefficient K psi p.val = 1 := by
    rw [primeCoefficient_of_unramified K psi p.val hpsi,
      ← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  have hrowNorm : ‖rowW K S P u p‖ = 1 := by
    unfold rowW
    rw [← rowPrimeUnit_character_of_not_mem_row K S P u p hp]
    exact HighBin.ActualGaussPhases.unitPhase_norm _ _
  have hrowUnit : conj (rowW K S P u p) * rowW K S P u p = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hrowNorm]
    norm_num
  have hpow : (q : ℂ) ^ s * (q : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add _ _ hq0, add_neg_cancel, Complex.cpow_zero]
  have hMD : M * D = c := by
    dsimp only [M, D, c, rowD]
    calc
      _ = (conj (primeCoefficient K psi p.val) * primeCoefficient K psi p.val) *
          conj (rowW K S P u p) * ((q : ℂ) ^ s * (q : ℂ) ^ (-s)) := by ring
      _ = _ := by rw [hpsiUnit, hpow]; ring
  have hcW : c * W = Y := by
    dsimp only [c, W, Y]
    rw [← mul_assoc, hrowUnit, one_mul]
  have hden := phaseRowEuler_denominators_ne_zero_of_re (by linarith : 1 < q)
    (rowD K S P psi u p) (rowE K S P psi p) s z
    (rowD_norm K S P psi u p) (rowE_norm K S P psi p) (by linarith [hv.1]) (by linarith [hv.2.2.2.2.1])
  have hvalue : H = rowEulerRationalValue (q : ℂ) (q : ℂ)⁻¹ V W D E := by
    dsimp only [H, actualLocalUnmarked]
    rw [localFactor_eq_explicit_rowEulerRegion K S P psi ∅ u p (s, w, z) hv]
    simp only [explicitLocalEuler, if_neg hp, Finset.notMem_empty, if_false, sub_zero] <;> rfl
  have hmarked : actualLocalMarked K S P psi u s w z p = H - (1 - W * V) / (1 - D) := by
    dsimp only [actualLocalMarked]
    rw [localFactor_eq_explicit_rowEulerRegion K S P psi {p} u p (s, w, z) hv, hvalue]
    simp only [explicitLocalEuler, if_neg hp, Finset.mem_singleton, if_pos rfl] <;> rfl
  have hA : slotMarkedScalar K S psi s z p = (q : ℂ) ^ (z - 1) * M := by
    unfold slotMarkedScalar
    rw [← hcast, show s + z - 1 = (z - 1) + s by ring, Complex.cpow_add _ _ hq0]
    dsimp only [M]
    ring
  have hB : slotSelectedScalar K S w z p = (q : ℂ) ^ (z - 1) * Y := by
    unfold slotSelectedScalar
    rw [← hcast, show z - w - 1 = (z - 1) + -w by ring, Complex.cpow_add _ _ hq0]
  have hid := regular_compensation_algebra (q : ℂ) (q : ℂ)⁻¹ V W D E H M c Y
    hden.2 hden.1 hH hvalue hMD hcW
  unfold actualLocalCompensation
  rw [hA, hB, hmarked]
  calc
    _ = (q : ℂ) ^ (z - 1) * ((M * (H - (1 - W * V) / (1 - D)) - Y * H) / H) := by ring
    _ = _ := by
      rw [hid]
      change (q : ℂ) ^ (z - 1) *
        (-c + actualRegularCompensationError K S P psi u s w z p) = _
      rw [hcast]
      rfl

theorem actual_localFactor_splice_region (P : ProbeData K S) (psi : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (s w z : ℂ) (hv : (s, w, z) ∈ rowEulerRegion) (p : ExteriorPrime K S) :
    localFactor K S P psi Q u p (s, w, z) =
      if p ∈ Q then actualLocalMarked K S P psi u s w z p
      else actualLocalUnmarked K S P psi u s w z p := by
  unfold actualLocalMarked actualLocalUnmarked
  rw [localFactor_eq_explicit_rowEulerRegion K S P psi Q u p (s, w, z) hv,
    localFactor_eq_explicit_rowEulerRegion K S P psi {p} u p (s, w, z) hv,
    localFactor_eq_explicit_rowEulerRegion K S P psi ∅ u p (s, w, z) hv]
  by_cases hR : p ∈ exteriorSupport K S u.ideal <;>
    by_cases hQ : p ∈ Q <;> simp [explicitLocalEuler, hR, hQ]

theorem actual_rowCorrection_eq_markedProduct_region (P : ProbeData K S) (psi : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (s w z : ℂ) (hv : (s, w, z) ∈ rowEulerRegion) :
    rowCorrection K S P psi (arithmeticHighEulerData K S P psi) Q u s w z =
      NormForm.markedEulerProduct (actualLocalUnmarked K S P psi u s w z)
        (actualLocalMarked K S P psi u s w z) Q := by
  change (∏' p : ExteriorPrime K S, localFactor K S P psi Q u p (s, w, z)) = _
  unfold NormForm.markedEulerProduct
  apply tprod_congr
  intro p
  exact actual_localFactor_splice_region K S P psi Q u s w z hv p

/-- Genuine convergence on the whole positive Euler region. -/
theorem actual_unmarked_hasProd_region (P : ProbeData K S) (psi : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) (hv : (s, w, z) ∈ rowEulerRegion) :
    HasProd (actualLocalUnmarked K S P psi u s w z)
      (rowCorrection K S P psi (arithmeticHighEulerData K S P psi) ∅ u s w z) := by
  exact (rowCorrection_multipliable_rowEulerRegion K S P psi
    (arithmeticHighEulerData K S P psi) ∅ u (s, w, z) hv).hasProd

theorem actual_compensation_tuple_factorization_region (P : ProbeData K S)
    (psi : HeckeCharacter K) (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z : ℝ)
    (s w z : ℂ) (hv : (s, w, z) ∈ rowEulerRegion)
    (p : Fin g.slots → ExteriorPrime K S)
    (hp : ∀ i, p i ∈ primeWindow K S g T Z i)
    (hne : ∀ i, actualLocalUnmarked K S P psi u s w z (p i) ≠ 0) :
    (∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
      let selected := subsetPrimeIdeal K S p J
      let marked := subsetPrimeIdeal K S p (Finset.univ \ J)
      (-1 : ℂ) ^ J.card * (exteriorNorm K S selected : ℂ) ^ (z - w - 1) *
        conj (heckeIdealCoefficient K psi marked.val) *
        (exteriorNorm K S marked : ℂ) ^ (s + z - 1) *
        rowCorrection K S P psi (arithmeticHighEulerData K S P psi)
          ((Finset.univ \ J).image p) u s w z) =
      rowCorrection K S P psi (arithmeticHighEulerData K S P psi) ∅ u s w z *
        ∏ i : Fin g.slots, actualLocalCompensation K S P psi u s w z (p i) := by
  have hinj := actual_primeWindow_tuple_injective K S g T Z p hp
  let A : Fin g.slots → ℂ := fun i => slotMarkedScalar K S psi s z (p i)
  let B : Fin g.slots → ℂ := fun i => slotSelectedScalar K S w z (p i)
  let H := actualLocalUnmarked K S P psi u s w z
  let M := actualLocalMarked K S P psi u s w z
  let total := rowCorrection K S P psi (arithmeticHighEulerData K S P psi) ∅ u s w z
  have hprod : HasProd H total := actual_unmarked_hasProd_region K S P psi u s w z hv
  calc
    _ = ∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
        (∏ i ∈ J, -B i) * (∏ i ∈ Finset.univ \ J, A i) *
          NormForm.markedEulerProduct H M ((Finset.univ \ J).image p) := by
      apply Finset.sum_congr rfl
      intro J hJ
      dsimp only
      rw [subsetPrimeIdeal_norm_cpow K S g p hinj J,
        subsetPrimeIdeal_coefficient_eq_prod K S g psi p hinj (Finset.univ \ J),
        subsetPrimeIdeal_norm_cpow K S g p hinj (Finset.univ \ J),
        actual_rowCorrection_eq_markedProduct_region K S P psi ((Finset.univ \ J).image p) u
          s w z hv]
      simp only [map_prod, A, B, H, M, slotMarkedScalar, slotSelectedScalar,
        Finset.prod_neg, Finset.prod_mul_distrib]
      ring
    _ = _ := NormForm.indexed_compensation_factorization
      (Finset.univ : Finset (Fin g.slots)) p hinj H M A B total hprod
        (fun i _ => hne i)

/-- Exact complete-slot decomposition of the actual finite correction.
Only local nonvanishing on the selected windows occurs in this algebraic
lemma; the next theorem supplies it uniformly from the actual tables. -/
theorem actualFullCorrection_eq_product_region (P : ProbeData K S) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z : ℝ)
    (s w z : ℂ) (hv : (s, w, z) ∈ rowEulerRegion)
    (hne : ∀ i : Fin g.slots, ∀ p ∈ primeWindow K S g T Z i,
      actualLocalUnmarked K S P psi u s w z p ≠ 0) :
    compensatedRowFullCorrection K S P psi (arithmeticHighEulerData K S P psi) g T u Z s w z =
      rowCorrection K S P psi (arithmeticHighEulerData K S P psi) ∅ u s w z *
        ∏ i : Fin g.slots, actualFullCorrectionSlot K S P psi g T u Z s w z i := by
  unfold compensatedRowFullCorrection actualFullCorrectionSlot
  conv_rhs => rw [Finset.prod_univ_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Fintype.mem_piFinset.mp hp
  rw [actual_compensation_tuple_factorization_region K S P psi g T u Z s w z hv p hp'
    (fun i => hne i (p i) (hp' i)), Finset.prod_mul_distrib]
  ring

end Expansion.Project

#print axioms Expansion.Project.actualLocalCompensation_regular_main_region
#print axioms Expansion.Project.actual_unmarked_hasProd_region
#print axioms Expansion.Project.actualFullCorrection_eq_product_region
