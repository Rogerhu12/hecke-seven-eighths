import HeckeSkeleton.HighBinSupport.ActualEulerProduct
import HeckeSkeleton.HighBinSupport.ActualNormFormPrimeDeficit
import HeckeSkeleton.HighBinSupport.ActualNormFormPrimeCap
import HeckeSkeleton.HighBinSupport.ActualRowPrimeCharacter
import HeckeSkeleton.HighBinSupport.HighCorrectionAlgebra
import HeckeSkeleton.HighBinSupport.ActualGaussCalibration
import HeckeSkeleton.HighBinSupport.SelectedCompensation
import HeckeGeneral.Analysis.CompensatedRowKernelFactorization
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Literal slot factorization of the complete arithmetic correction.

All marked and unmarked branches are taken from the constructed actual
Euler provider. The large-prime cutoff makes only the selected local H
factors nonzero. The unselected product can vanish, and no Gauss
polynomial is divided out. The final identity retains every subset of
every original finite prime-window tuple.
-/

noncomputable section
namespace HighBinVerified.NormFormFullCorrection

open NumberField IsDedekindDomain Set Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open NormFormActual
open scoped Classical BigOperators Topology ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def actualLocalUnmarked (P : ProbeData K S) (psi : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) (p : ExteriorPrime K S) : ℂ :=
  localFactor K S P psi ∅ u p (s, w, z)

def actualLocalMarked (P : ProbeData K S) (psi : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) (p : ExteriorPrime K S) : ℂ :=
  localFactor K S P psi {p} u p (s, w, z)

def slotMarkedScalar (psi : HeckeCharacter K) (s z : ℂ) (p : ExteriorPrime K S) : ℂ :=
  conj (primeCoefficient K psi p.val) * (p.val.asIdeal.absNorm : ℂ) ^ (s + z - 1)

def slotSelectedScalar (w z : ℂ) (p : ExteriorPrime K S) : ℂ :=
  (p.val.asIdeal.absNorm : ℂ) ^ (z - w - 1)

def actualLocalCompensation (P : ProbeData K S) (psi : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) (p : ExteriorPrime K S) : ℂ :=
  (slotMarkedScalar K S psi s z p * actualLocalMarked K S P psi u s w z p -
    slotSelectedScalar K S w z p * actualLocalUnmarked K S P psi u s w z p) /
      actualLocalUnmarked K S P psi u s w z p

/-- This is the complete actual slot value, including all correction
terms. It is not the bare prime polynomial. -/
def actualFullCorrectionSlot (P : ProbeData K S) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z : ℝ) (s w z : ℂ) (i : Fin g.slots) : ℂ :=
  ∑ p ∈ primeWindow K S g T Z i,
    windowWeight K S g Z i p * actualLocalCompensation K S P psi u s w z p

def actualCompensationMainSlot (P : ProbeData K S) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (u : FrequencyRow K S) (Z : ℝ)
    (z : ℂ) (i : Fin g.slots) : ℂ :=
  ∑ p ∈ primeWindow K S g T Z i, windowWeight K S g Z i p *
    conj (primeCoefficient K (arithmeticRowCharacter K S P u) p.val) *
      (p.val.asIdeal.absNorm : ℂ) ^ (z - 1)

def actualRegularErrorSlot (P : ProbeData K S) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z : ℝ) (s w z : ℂ) (i : Fin g.slots) : ℂ :=
  ∑ p ∈ (primeWindow K S g T Z i).filter (fun p => p ∉ exteriorSupport K S u.ideal),
    windowWeight K S g Z i p *
      (actualLocalCompensation K S P psi u s w z p +
        (p.val.asIdeal.absNorm : ℂ) ^ (z - 1) *
          conj (primeCoefficient K (arithmeticRowCharacter K S P u) p.val))

def actualValuationOneSlot (P : ProbeData K S) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z : ℝ) (s w z : ℂ) (i : Fin g.slots) : ℂ :=
  ∑ p ∈ (primeWindow K S g T Z i).filter (fun p => primeExponents u.ideal.val p.val = 1),
    windowWeight K S g Z i p * actualLocalCompensation K S P psi u s w z p

def actualRepeatedSlot (P : ProbeData K S) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z : ℝ) (s w z : ℂ) (i : Fin g.slots) : ℂ :=
  ∑ p ∈ repeatedPrimeWindow K S u g T Z i,
    windowWeight K S g Z i p * actualLocalCompensation K S P psi u s w z p

/-- The actual complete slot, with the genuine character main term and
all three disjoint error classes retained. The prime coefficient is
proved zero at every row prime by the repository's arithmetic row theorem. -/
theorem actualFullCorrectionSlot_decomposition (P : ProbeData K S)
    (psi : HeckeCharacter K) (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z : ℝ) (s w z : ℂ) (i : Fin g.slots) :
    actualFullCorrectionSlot K S P psi g T u Z s w z i =
      -actualCompensationMainSlot K S P g T u Z z i +
        actualRegularErrorSlot K S P psi g T u Z s w z i +
        actualValuationOneSlot K S P psi g T u Z s w z i +
        actualRepeatedSlot K S P psi g T u Z s w z i := by
  unfold actualFullCorrectionSlot actualCompensationMainSlot actualRegularErrorSlot
    actualValuationOneSlot actualRepeatedSlot repeatedPrimeWindow
  simp only [Finset.sum_filter, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hrow : p ∈ exteriorSupport K S u.ideal ↔ primeExponents u.ideal.val p.val ≠ 0 := by
    rw [mem_exteriorSupport_iff, ← mem_idealPrimeSupport_iff]
    exact Finsupp.mem_support_iff
  by_cases hmem : p ∈ exteriorSupport K S u.ideal
  · have hn : primeExponents u.ideal.val p.val ≠ 0 := hrow.mp hmem
    have hzero : primeCoefficient K (arithmeticRowCharacter K S P u) p.val = 0 :=
      RowPrimeCharacter.row_primeCoefficient_eq_zero_of_dvd K S P
        (arithmeticRowCharacterInput K S P) u p ((mem_exteriorSupport_iff K S u.ideal p).mp hmem)
    by_cases hone : primeExponents u.ideal.val p.val = 1
    · simp [hmem, hone, hzero]
    · have htwo : 2 ≤ primeExponents u.ideal.val p.val := by omega
      simp only [hmem, not_true_eq_false, ite_false, hone, htwo, ite_true,
        hzero, map_zero, mul_zero, zero_mul, neg_zero, zero_add, add_zero]
  · have hval : primeExponents u.ideal.val p.val = 0 := by
      by_contra hn
      exact hmem (hrow.mpr hn)
    simp [hmem, hval] <;> ring

/-- The literal regular error after the two leading terms have cancelled.
The denominator consists only of the genuine Euler denominators and the
selected local unmarked factor. -/
def actualRegularCompensationError (P : ProbeData K S) (psi : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) (p : ExteriorPrime K S) : ℂ :=
  let q : ℝ := (p.val.asIdeal.absNorm : ℝ)
  let V := (q : ℂ) ^ (-6 * z)
  let W := rowW K S P u p * (q : ℂ) ^ (-w)
  let D := rowD K S P psi u p * (q : ℂ) ^ (-s)
  let E := rowE K S P psi p * (q : ℂ) ^ (4 - 6 * s) * V
  let H := actualLocalUnmarked K S P psi u s w z p
  let A := (1 - (q : ℂ)⁻¹) + W * (1 - V)
  let B := (1 - V) + ((q : ℂ) - 1) * W * V
  (1 - W) *
    (conj (primeCoefficient K psi p.val) * (q : ℂ) ^ s * E * A +
      conj (rowW K S P u p) * ((1 - E) * (1 - D) * H - B)) /
    ((1 - E) * (1 - D) * H)

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

/-- Exact regular main term from the constructed arithmetic provider.
The row unit and target unit are the genuine local Hecke coefficients;
no phase identification or compensation identity is supplied as data. -/
theorem actualLocalCompensation_regular_main (P : ProbeData K S)
    (psi : HeckeCharacter K) (u : FrequencyRow K S)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (he : 0 ≤ e)
    (s w z : ℂ) (hv : (s, w, z) ∈ sweptTube a e) (p : ExteriorPrime K S)
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
  have hden := phaseRowEuler_denominators_ne_zero hq ha he
    (rowD K S P psi u p) (rowE K S P psi p) s z
    (rowD_norm K S P psi u p) (rowE_norm K S P psi p) hv.1.le hv.2.2.le
  have hvalue : H = rowEulerRationalValue (q : ℂ) (q : ℂ)⁻¹ V W D E := by
    dsimp only [H, actualLocalUnmarked]
    rw [localFactor_eq_explicit K S P psi ∅ u ha he p (s, w, z) hv]
    simp only [explicitLocalEuler, if_neg hp, Finset.notMem_empty, if_false, sub_zero] <;> rfl
  have hmarked : actualLocalMarked K S P psi u s w z p = H - (1 - W * V) / (1 - D) := by
    dsimp only [actualLocalMarked]
    rw [localFactor_eq_explicit K S P psi {p} u ha he p (s, w, z) hv, hvalue]
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

/-- The ramified branch is exactly the previously proved selected finite
table, including its original Gauss phases and target coefficient. -/
theorem actualLocalCompensation_ramified_eq (P : ProbeData K S)
    (psi : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
    (u : FrequencyRow K S) {a e : ℝ} (ha : 51 / 100 ≤ a) (he : 0 ≤ e)
    (s w z : ℂ) (hv : (s, w, z) ∈ sweptTube a e) (p : ExteriorPrime K S)
    (hp : p ∈ exteriorSupport K S u.ideal)
    (hH : ramifiedTableValue (rowPhaseData K S P psi u p)
      (p.val.asIdeal.absNorm : ℝ) s w z (rowIndex K S u p) ≠ 0) :
    actualLocalCompensation K S P psi u s w z p =
      (p.val.asIdeal.absNorm : ℂ) ^ (z - 1) *
        HighBin.SelectedCompensation.normalizedCompensation
          (rowPhaseData K S P psi u p).eta ((p.val.asIdeal.absNorm : ℂ) ^ s)
          ((p.val.asIdeal.absNorm : ℂ) ^ (-w))
          (ramifiedTableValue (rowPhaseData K S P psi u p)
            (p.val.asIdeal.absNorm : ℝ) s w z (rowIndex K S u p)) := by
  have hq0 : (p.val.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (lt_trans Nat.zero_lt_one (one_lt_primeIdeal_absNorm K p.val)).ne'
  unfold actualLocalCompensation actualLocalMarked actualLocalUnmarked
  rw [localFactor_eq_explicit K S P psi {p} u ha he p (s, w, z) hv,
    localFactor_eq_explicit K S P psi ∅ u ha he p (s, w, z) hv]
  simp only [explicitLocalEuler, if_pos hp, Finset.mem_singleton, if_pos rfl,
    Finset.notMem_empty, if_false, sub_zero, ite_true]
  rw [rowPhaseData_eta K S P psi hcal u p]
  unfold slotMarkedScalar slotSelectedScalar HighBin.SelectedCompensation.normalizedCompensation
  rw [show s + z - 1 = (z - 1) + s by ring,
    show z - w - 1 = (z - 1) + -w by ring,
    Complex.cpow_add _ _ hq0, Complex.cpow_add _ _ hq0]
  field_simp [hH] <;> ring

/-- Every actual ramified slot factor has the repeated-prime loss from
the finite table. The phase normalization is discharged by arithmetic
calibration; only the explicit scalar prime cutoff remains. -/
theorem actualLocalCompensation_ramified_bound (P : ProbeData K S)
    (psi : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
    (u : FrequencyRow K S) {a e : ℝ} (ha : 51 / 100 ≤ a) (he : 0 < e)
    (s w z : ℂ) (hs : s.re = a + 16 * e)
    (hw : w.re = 1 - a - 6 * e) (hz : z.re = 17 / 50)
    (p : ExteriorPrime K S) (hp : p ∈ exteriorSupport K S u.ideal)
    (hcut : 9 * (p.val.asIdeal.absNorm : ℝ) ^ (-10 * e) ≤ 1 / 2) :
    ‖actualLocalCompensation K S P psi u s w z p‖ ≤
      19 * (p.val.asIdeal.absNorm : ℝ) ^ (a - 33 / 50 + 6 * e) := by
  have hq := exteriorPrime_norm_two_le K S p
  have hq0 : (0 : ℝ) < p.val.asIdeal.absNorm := by linarith
  have hv := swept_contour_mem_tube he le_rfl s w z hs hw hz
  have hclose := (ramified_table_dynamic_bound (rowPhaseData K S P psi u p)
    (p.val.asIdeal.absNorm : ℝ) a e hq (by linarith) he.le s w z hs hw hz
    (rowIndex K S u p)).trans hcut
  have hH : ramifiedTableValue (rowPhaseData K S P psi u p)
      (p.val.asIdeal.absNorm : ℝ) s w z (rowIndex K S u p) ≠ 0 := by
    intro hzero
    simp only [hzero, zero_sub, norm_neg, norm_one] at hclose
    norm_num at hclose
  rw [actualLocalCompensation_ramified_eq K S P psi hcal u ha he.le s w z hv p hp hH,
    norm_mul]
  have hb := HighBin.SelectedCompensation.all_rows_selected_bound
    (rowPhaseData K S P psi u p) (p.val.asIdeal.absNorm : ℝ) a e hq
    (by linarith) he.le s w z hs hw hz (rowIndex K S u p) hcut
  have hpow : ‖(p.val.asIdeal.absNorm : ℂ) ^ (z - 1)‖ =
      (p.val.asIdeal.absNorm : ℝ) ^ (-(33 / 50 : ℝ)) := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
    congr 1
    simp only [Complex.sub_re, Complex.one_re, hz]
    ring
  rw [hpow]
  calc
    _ ≤ (p.val.asIdeal.absNorm : ℝ) ^ (-(33 / 50 : ℝ)) *
        (19 * (p.val.asIdeal.absNorm : ℝ) ^ (a + 6 * e)) :=
      mul_le_mul_of_nonneg_left (by simpa only [Complex.ofReal_natCast] using hb)
        (Real.rpow_nonneg hq0.le _)
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_add hq0]
      congr 2
      ring

/-- Valuation one is handled by its exact finite-table cancellation and
has no repeated-prime loss. The index-zero premise is derived from the
actual prime multiplicity of the row ideal. -/
theorem actualLocalCompensation_valuation_one_bound (P : ProbeData K S)
    (psi : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
    (u : FrequencyRow K S) {a e : ℝ} (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1)
    (he : 0 < e) (he1 : e ≤ 1 / 12)
    (s w z : ℂ) (hs : s.re = a + 16 * e)
    (hw : w.re = 1 - a - 6 * e) (hz : z.re = 17 / 50)
    (p : ExteriorPrime K S) (hp : p ∈ exteriorSupport K S u.ideal)
    (hval : primeExponents u.ideal.val p.val = 1)
    (hcut : 9 * (p.val.asIdeal.absNorm : ℝ) ^ (-10 * e) ≤ 1 / 2) :
    ‖actualLocalCompensation K S P psi u s w z p‖ ≤
      13 * (p.val.asIdeal.absNorm : ℝ) ^ (-(4 / 25 : ℝ)) := by
  have hq := exteriorPrime_norm_two_le K S p
  have hq0 : (0 : ℝ) < p.val.asIdeal.absNorm := by linarith
  have hv := swept_contour_mem_tube he le_rfl s w z hs hw hz
  have hj : rowIndex K S u p = 0 := by
    unfold rowIndex
    rw [dif_pos hp]
    apply Fin.ext
    simp only [rowRamifiedIndex_val, hval, Nat.sub_self, Fin.val_zero]
  have hclose := (ramified_table_dynamic_bound (rowPhaseData K S P psi u p)
    (p.val.asIdeal.absNorm : ℝ) a e hq (by linarith) he.le s w z hs hw hz
    (rowIndex K S u p)).trans hcut
  have hH : ramifiedTableValue (rowPhaseData K S P psi u p)
      (p.val.asIdeal.absNorm : ℝ) s w z (rowIndex K S u p) ≠ 0 := by
    intro hzero
    simp only [hzero, zero_sub, norm_neg, norm_one] at hclose
    norm_num at hclose
  rw [actualLocalCompensation_ramified_eq K S P psi hcal u ha he.le s w z hv p hp hH,
    hj, norm_mul]
  have hb := HighBin.SelectedCompensation.row_one_selected_bound
    (rowPhaseData K S P psi u p) (p.val.asIdeal.absNorm : ℝ) a e hq
    (by linarith) ha1 he.le he1 s w z hs hw hz hcut
  have hpow : ‖(p.val.asIdeal.absNorm : ℂ) ^ (z - 1)‖ =
      (p.val.asIdeal.absNorm : ℝ) ^ (-(33 / 50 : ℝ)) := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
    congr 1
    simp only [Complex.sub_re, Complex.one_re, hz]
    ring
  rw [hpow]
  calc
    _ ≤ (p.val.asIdeal.absNorm : ℝ) ^ (-(33 / 50 : ℝ)) *
        (13 * (p.val.asIdeal.absNorm : ℝ) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (by simpa only [Complex.ofReal_natCast] using hb)
        (Real.rpow_nonneg hq0.le _)
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_add hq0]
      norm_num

def regularCompensationErrorConstant : ℝ :=
  (32 + 16 * (11 / sweptTubeEulerMargin)) / sweptTubeEulerMargin

theorem regularCompensationErrorConstant_pos : 0 < regularCompensationErrorConstant := by
  unfold regularCompensationErrorConstant
  exact div_pos (by have := sweptTubeEulerMargin_pos; positivity) sweptTubeEulerMargin_pos

set_option maxHeartbeats 1200000 in
/-- The displayed error is genuinely smaller by a square root. All
coordinate estimates are read from the actual dynamic contour, and the
actual unmarked Euler error supplies the remaining term. -/
theorem actualRegularCompensationError_norm_le (P : ProbeData K S)
    (psi : HeckeCharacter K) (u : FrequencyRow K S)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1)
    (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (s w z : ℂ) (hs : s.re = a + 16 * e)
    (hw : w.re = 1 - a - 6 * e) (hz : z.re = 17 / 50)
    (p : ExteriorPrime K S) (hp : p ∉ exteriorSupport K S u.ideal)
    (hclose : ‖actualLocalUnmarked K S P psi u s w z p - 1‖ ≤ 1 / 2) :
    ‖actualRegularCompensationError K S P psi u s w z p‖ ≤
      regularCompensationErrorConstant * (p.val.asIdeal.absNorm : ℝ) ^ (-(1 / 2 : ℝ)) := by
  let q : ℝ := (p.val.asIdeal.absNorm : ℝ)
  let V := (q : ℂ) ^ (-6 * z)
  let W := rowW K S P u p * (q : ℂ) ^ (-w)
  let D := rowD K S P psi u p * (q : ℂ) ^ (-s)
  let E := rowE K S P psi p * (q : ℂ) ^ (4 - 6 * s) * V
  let H := actualLocalUnmarked K S P psi u s w z p
  let M := conj (primeCoefficient K psi p.val) * (q : ℂ) ^ s
  let c := conj (rowW K S P u p)
  let A := (1 - (q : ℂ)⁻¹) + W * (1 - V)
  let B := (1 - V) + ((q : ℂ) - 1) * W * V
  let den := (1 - E) * (1 - D)
  let C0 : ℝ := 11 / sweptTubeEulerMargin
  let b : ℝ := q ^ (-(1 / 2 : ℝ) - 7 * e)
  have hq : 2 ≤ q := exteriorPrime_norm_two_le K S p
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hC0 : 0 ≤ C0 := div_nonneg (by norm_num) sweptTubeEulerMargin_pos.le
  have hb : 0 ≤ b := Real.rpow_nonneg hq0.le _
  have hv := swept_contour_mem_tube he le_rfl s w z hs hw hz
  obtain ⟨hV, hW, hD, hE⟩ := phase_coordinate_bounds hq
    (rowW K S P u p) (rowD K S P psi u p) (rowE K S P psi p) s w z
    (rowW_norm K S P u p) (rowD_norm K S P psi u p) (rowE_norm K S P psi p)
    hv.1.le hv.2.1.le hv.2.2.le
  change ‖V‖ ≤ q ^ (-(51 / 25 : ℝ) + 6 * e) at hV
  change ‖W‖ ≤ q ^ (a - 1 + 7 * e) at hW
  change ‖D‖ ≤ q ^ (-a - 15 * e) at hD
  change ‖E‖ ≤ q ^ (49 / 25 - 6 * a - 84 * e) at hE
  have hc : ‖c‖ ≤ 1 := by
    simpa only [c, Complex.norm_conj] using rowW_norm K S P u p
  have hM : ‖M‖ ≤ q ^ (a + 16 * e) := by
    dsimp only [M]
    rw [norm_mul, Complex.norm_conj, Complex.norm_cpow_eq_rpow_re_of_pos hq0, hs]
    exact (mul_le_mul_of_nonneg_right (norm_primeCoefficient_le_one K psi p.val)
      (Real.rpow_nonneg hq0.le _)).trans_eq (one_mul _)
  have mul_bound {X Y : ℂ} {x y : ℝ}
      (hX : ‖X‖ ≤ q ^ x) (hY : ‖Y‖ ≤ q ^ y) : ‖X * Y‖ ≤ q ^ (x + y) := by
    rw [norm_mul, Real.rpow_add hq0]
    exact mul_le_mul hX hY (norm_nonneg _) (Real.rpow_nonneg hq0.le _)
  have lower {X : ℂ} {x : ℝ} (hX : ‖X‖ ≤ q ^ x)
      (hx : x ≤ -(1 / 2 : ℝ) - 7 * e) : ‖X‖ ≤ b :=
    hX.trans (Real.rpow_le_rpow_of_exponent_le hq1 hx)
  have hWsmall : ‖W‖ ≤ q ^ (7 * e) := hW.trans
    (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith))
  have hWone : 1 ≤ q ^ (7 * e) := Real.one_le_rpow hq1 (by linarith)
  have hVone : ‖V‖ ≤ 1 := hV.trans (by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hq1
      (show -(51 / 25 : ℝ) + 6 * e ≤ 0 by linarith))
  have hDone : ‖D‖ ≤ 1 := hD.trans (by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hq1
      (show -a - 15 * e ≤ 0 by linarith))
  have hEone : ‖E‖ ≤ 1 := hE.trans (by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hq1
      (show 49 / 25 - 6 * a - 84 * e ≤ 0 by linarith))
  have h1W : ‖1 - W‖ ≤ 2 * q ^ (7 * e) := by
    have h := norm_sub_le (1 : ℂ) W
    rw [norm_one] at h
    linarith
  have h1V : ‖1 - V‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) V
    rw [norm_one] at h
    linarith
  have hA : ‖A‖ ≤ 3 * q ^ (7 * e) := by
    have hterm := (norm_mul W (1 - V)).trans_le
      (mul_le_mul hWsmall h1V (norm_nonneg _) (Real.rpow_nonneg hq0.le _))
    have h := norm_add_le ((1 : ℂ) - (q : ℂ)⁻¹) (W * (1 - V))
    have hqi := norm_one_sub_inv_le_one q hq1
    change ‖A‖ ≤ _ at h
    linarith
  have hdenUpper : ‖den‖ ≤ 4 := by
    have h1E : ‖1 - E‖ ≤ 2 := by
      have h := norm_sub_le (1 : ℂ) E
      rw [norm_one] at h
      linarith
    have h1D : ‖1 - D‖ ≤ 2 := by
      have h := norm_sub_le (1 : ℂ) D
      rw [norm_one] at h
      linarith
    dsimp only [den]
    rw [norm_mul]
    exact (mul_le_mul h1E h1D (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hDd : ‖D‖ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (hD.trans (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith))).trans
      (Real.rpow_le_rpow_of_nonpos (by norm_num) hq (by norm_num))
  have hEe : ‖E‖ ≤ (1 / 2 : ℝ) := by
    apply (hE.trans (Real.rpow_le_rpow_of_exponent_le hq1
      (show 49 / 25 - 6 * a - 84 * e ≤ -1 by linarith))).trans
    simpa only [Real.rpow_neg_one, one_div] using
      Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 2) hq
        (by norm_num : (-1 : ℝ) ≤ 0)
  have hdenLower : sweptTubeEulerMargin ≤ ‖den‖ := by
    have hEgap : 1 - (1 / 2 : ℝ) ≤ ‖1 - E‖ := by
      have h := norm_sub_norm_le (1 : ℂ) E
      rw [norm_one] at h
      linarith
    have hDgap : 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ ‖1 - D‖ := by
      have h := norm_sub_norm_le (1 : ℂ) D
      rw [norm_one] at h
      linarith
    have hgap : 0 ≤ 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have := Real.rpow_lt_one_of_one_lt_of_neg
        (by norm_num : (1 : ℝ) < 2) (by norm_num : (-(1 / 2 : ℝ)) < 0)
      linarith
    dsimp only [den, sweptTubeEulerMargin]
    rw [norm_mul, mul_comm (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))]
    exact mul_le_mul hEgap hDgap hgap (norm_nonneg _)
  have hHerr : ‖H - 1‖ ≤ C0 * q ^ (-1 - 8 * e) := by
    dsimp only [H, actualLocalUnmarked]
    rw [localFactor_eq_explicit K S P psi ∅ u ha he.le p (s, w, z) hv]
    simp only [explicitLocalEuler, if_neg hp, Finset.notMem_empty, if_false, sub_zero]
    exact phaseRowEuler_sweptTube_bound hq ha ha1 he.le he1
      (rowW K S P u p) (rowD K S P psi u p) (rowE K S P psi p)
      (rowW_norm K S P u p) (rowD_norm K S P psi u p) (rowE_norm K S P psi p)
      (s, w, z) hv
  have hdenErr : ‖den * (H - 1)‖ ≤ (4 * C0) * b := by
    rw [norm_mul]
    calc
      _ ≤ 4 * (C0 * q ^ (-1 - 8 * e)) :=
        mul_le_mul hdenUpper hHerr (norm_nonneg _) (by norm_num)
      _ = (4 * C0) * q ^ (-1 - 8 * e) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)) (by positivity)
  have hqm : ‖(q : ℂ) - 1‖ ≤ q ^ (1 : ℝ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : 0 ≤ q - 1), Real.rpow_one]
    linarith
  have hEb : ‖E‖ ≤ b := lower hE (by linarith)
  have hDb : ‖D‖ ≤ b := lower hD (by linarith)
  have hEDb : ‖E * D‖ ≤ b := lower (mul_bound hE hD) (by linarith)
  have hVb : ‖V‖ ≤ b := lower hV (by linarith)
  have hWVb : ‖((q : ℂ) - 1) * W * V‖ ≤ b :=
    lower (mul_bound (mul_bound hqm hW) hV) (by linarith)
  have hrest : ‖den * H - B‖ ≤ (4 * C0 + 5) * b := by
    have heq : den * H - B =
        den * (H - 1) - E - D + E * D + V - ((q : ℂ) - 1) * W * V := by
      dsimp only [den, B]
      ring
    rw [heq]
    have h1 := norm_sub_le (den * (H - 1)) E
    have h2 := norm_sub_le (den * (H - 1) - E) D
    have h3 := norm_add_le (den * (H - 1) - E - D) (E * D)
    have h4 := norm_add_le (den * (H - 1) - E - D + E * D) V
    have h5 := norm_sub_le (den * (H - 1) - E - D + E * D + V) (((q : ℂ) - 1) * W * V)
    nlinarith
  have hMEA : ‖M * E * A‖ ≤ 3 * b := by
    rw [norm_mul (M * E) A]
    calc
      _ ≤ q ^ ((a + 16 * e) + (49 / 25 - 6 * a - 84 * e)) *
          (3 * q ^ (7 * e)) :=
        mul_le_mul (mul_bound hM hE) hA (norm_nonneg _) (Real.rpow_nonneg hq0.le _)
      _ = 3 * q ^ (((a + 16 * e) + (49 / 25 - 6 * a - 84 * e)) + 7 * e) := by
        rw [mul_left_comm, ← Real.rpow_add hq0]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)) (by norm_num)
  have hinner : ‖M * E * A + c * (den * H - B)‖ ≤ (8 + 4 * C0) * b := by
    have hcRest : ‖c * (den * H - B)‖ ≤ (4 * C0 + 5) * b := by
      rw [norm_mul]
      exact (mul_le_mul hc hrest (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    have h := norm_add_le (M * E * A) (c * (den * H - B))
    nlinarith
  have hnum : ‖(1 - W) * (M * E * A + c * (den * H - B))‖ ≤
      (16 + 8 * C0) * q ^ (-(1 / 2 : ℝ)) := by
    rw [norm_mul]
    calc
      _ ≤ (2 * q ^ (7 * e)) * ((8 + 4 * C0) * b) :=
        mul_le_mul h1W hinner (norm_nonneg _) (by positivity)
      _ = (16 + 8 * C0) * (q ^ (7 * e) * q ^ (-(1 / 2 : ℝ) - 7 * e)) := by
        dsimp only [b]
        ring
      _ = _ := by
        rw [← Real.rpow_add hq0]
        congr 2
        ring
  have hdenH : sweptTubeEulerMargin / 2 ≤ ‖den * H‖ := by
    rw [norm_mul]
    have hHlow := HighBin.SelectedCompensation.norm_lower_of_close_one H hclose
    have h := mul_le_mul hdenLower hHlow (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (norm_nonneg den)
    simpa only [div_eq_mul_inv, one_div, one_mul] using h
  change ‖((1 - W) * (M * E * A + c * (den * H - B))) / (den * H)‖ ≤ _
  rw [norm_div]
  calc
    _ ≤ ((16 + 8 * C0) * q ^ (-(1 / 2 : ℝ))) / (sweptTubeEulerMargin / 2) :=
      div_le_div₀ (by positivity) hnum (half_pos sweptTubeEulerMargin_pos) hdenH
    _ = _ := by
      dsimp only [regularCompensationErrorConstant, C0, q]
      field_simp [sweptTubeEulerMargin_pos.ne'] <;> ring

/-- The complete regular local factor equals its genuine prime-character
main term with an error of order q^(-29/25) on the final contour. -/
theorem actualLocalCompensation_regular_error_bound (P : ProbeData K S)
    (psi : HeckeCharacter K) (u : FrequencyRow K S)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1)
    (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (s w z : ℂ) (hs : s.re = a + 16 * e)
    (hw : w.re = 1 - a - 6 * e) (hz : z.re = 17 / 50)
    (p : ExteriorPrime K S) (hp : p ∉ exteriorSupport K S u.ideal)
    (hpsi : UnramifiedAt K psi p.val)
    (hclose : ‖actualLocalUnmarked K S P psi u s w z p - 1‖ ≤ 1 / 2) :
    ‖actualLocalCompensation K S P psi u s w z p +
      (p.val.asIdeal.absNorm : ℂ) ^ (z - 1) *
        conj (primeCoefficient K (arithmeticRowCharacter K S P u) p.val)‖ ≤
      regularCompensationErrorConstant * (p.val.asIdeal.absNorm : ℝ) ^ (-(29 / 25 : ℝ)) := by
  have hq := exteriorPrime_norm_two_le K S p
  have hq0 : (0 : ℝ) < p.val.asIdeal.absNorm := by linarith
  have hH : actualLocalUnmarked K S P psi u s w z p ≠ 0 := by
    intro hzero
    simp only [hzero, zero_sub, norm_neg, norm_one] at hclose
    norm_num at hclose
  have hv := swept_contour_mem_tube he le_rfl s w z hs hw hz
  rw [actualLocalCompensation_regular_main K S P psi u ha he.le s w z hv p hp hpsi hH]
  have heq : (p.val.asIdeal.absNorm : ℂ) ^ (z - 1) *
        (-conj (primeCoefficient K (arithmeticRowCharacter K S P u) p.val) +
          actualRegularCompensationError K S P psi u s w z p) +
      (p.val.asIdeal.absNorm : ℂ) ^ (z - 1) *
        conj (primeCoefficient K (arithmeticRowCharacter K S P u) p.val) =
      (p.val.asIdeal.absNorm : ℂ) ^ (z - 1) *
        actualRegularCompensationError K S P psi u s w z p := by ring
  rw [heq, norm_mul, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hq0]
  have hb := actualRegularCompensationError_norm_le K S P psi u ha ha1 he he1
    s w z hs hw hz p hp hclose
  have hre : (z - 1).re = -(33 / 50 : ℝ) := by
    simp only [Complex.sub_re, Complex.one_re, hz]
    ring
  rw [hre]
  calc
    _ ≤ (p.val.asIdeal.absNorm : ℝ) ^ (-(33 / 50 : ℝ)) *
        (regularCompensationErrorConstant * (p.val.asIdeal.absNorm : ℝ) ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hq0.le _)
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_add hq0]
      norm_num

def regularPrimeErrorMass (delta : ℝ) : ℝ :=
  (∑' p : ExteriorPrime K S, (p.val.asIdeal.absNorm : ℝ) ^ (-(1 + delta))) + 1

theorem regularPrimeErrorMass_pos (delta : ℝ) : 0 < regularPrimeErrorMass K S delta := by
  apply add_pos_of_nonneg_of_pos
  · exact tsum_nonneg (fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · exact zero_lt_one

/-- The regular local error is summed using ideal-norm summability,
not a prime-counting estimate. Its entire prime window costs an
arbitrarily small power beyond P^(-4/25). -/
theorem regular_prime_error_sum_le (F : Finset (ExteriorPrime K S))
    {P delta : ℝ} (hP : 0 < P) (hdelta : 0 < delta) (hdelta1 : delta ≤ 4 / 25)
    (hF : ∀ p ∈ F, P ≤ (p.val.asIdeal.absNorm : ℝ)) :
    (∑ p ∈ F, (p.val.asIdeal.absNorm : ℝ) ^ (-(29 / 25 : ℝ))) ≤
      regularPrimeErrorMass K S delta * P ^ (-(4 / 25 : ℝ) + delta) := by
  have hp : Summable (fun p : HeightOneSpectrum (𝓞 K) =>
      (p.asIdeal.absNorm : ℝ) ^ (-(1 + delta))) := by
    simpa only [Function.comp_def, primeNonzeroIdeal] using
      (summable_nonzeroIdeal_norm_rpow K (show 1 < 1 + delta by linarith)).comp_injective
        (primeNonzeroIdeal_injective K)
  have hs : Summable (fun p : ExteriorPrime K S =>
      (p.val.asIdeal.absNorm : ℝ) ^ (-(1 + delta))) := hp.comp_injective Subtype.val_injective
  have hterm : ∀ p ∈ F, (p.val.asIdeal.absNorm : ℝ) ^ (-(29 / 25 : ℝ)) ≤
      P ^ (-(4 / 25 : ℝ) + delta) * (p.val.asIdeal.absNorm : ℝ) ^ (-(1 + delta)) := by
    intro p hmem
    have hq : (0 : ℝ) < p.val.asIdeal.absNorm := hP.trans_le (hF p hmem)
    calc
      _ = (p.val.asIdeal.absNorm : ℝ) ^ (-(4 / 25 : ℝ) + delta) *
          (p.val.asIdeal.absNorm : ℝ) ^ (-(1 + delta)) := by
        rw [← Real.rpow_add hq]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hP (hF p hmem) (by linarith))
        (Real.rpow_nonneg hq.le _)
  calc
    _ ≤ ∑ p ∈ F, P ^ (-(4 / 25 : ℝ) + delta) *
        (p.val.asIdeal.absNorm : ℝ) ^ (-(1 + delta)) := Finset.sum_le_sum hterm
    _ = P ^ (-(4 / 25 : ℝ) + delta) *
        ∑ p ∈ F, (p.val.asIdeal.absNorm : ℝ) ^ (-(1 + delta)) := (Finset.mul_sum ..).symm
    _ ≤ P ^ (-(4 / 25 : ℝ) + delta) * regularPrimeErrorMass K S delta := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hP.le _)
      exact (hs.sum_le_tsum F (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans
        (le_add_of_nonneg_right zero_le_one)
    _ = _ := mul_comm _ _

theorem actual_localFactor_splice (P : ProbeData K S) (psi : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (he : 0 ≤ e)
    (s w z : ℂ) (hv : (s, w, z) ∈ sweptTube a e) (p : ExteriorPrime K S) :
    localFactor K S P psi Q u p (s, w, z) =
      if p ∈ Q then actualLocalMarked K S P psi u s w z p
      else actualLocalUnmarked K S P psi u s w z p := by
  unfold actualLocalMarked actualLocalUnmarked
  rw [localFactor_eq_explicit K S P psi Q u ha he p (s, w, z) hv,
    localFactor_eq_explicit K S P psi {p} u ha he p (s, w, z) hv,
    localFactor_eq_explicit K S P psi ∅ u ha he p (s, w, z) hv]
  by_cases hR : p ∈ exteriorSupport K S u.ideal <;>
    by_cases hQ : p ∈ Q <;> simp [explicitLocalEuler, hR, hQ]

theorem actual_rowCorrection_eq_markedProduct (P : ProbeData K S) (psi : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (he : 0 ≤ e)
    (s w z : ℂ) (hv : (s, w, z) ∈ sweptTube a e) :
    rowCorrection K S P psi (arithmeticHighEulerData K S P psi) Q u s w z =
      NormForm.markedEulerProduct (actualLocalUnmarked K S P psi u s w z)
        (actualLocalMarked K S P psi u s w z) Q := by
  change (∏' p : ExteriorPrime K S, localFactor K S P psi Q u p (s, w, z)) = _
  unfold NormForm.markedEulerProduct
  apply tprod_congr
  intro p
  exact actual_localFactor_splice K S P psi Q u ha he s w z hv p

theorem actual_unmarked_hasProd (P : ProbeData K S) (psi : HeckeCharacter K)
    (u : FrequencyRow K S) {a e : ℝ} (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1)
    (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (s w z : ℂ) (hv : (s, w, z) ∈ sweptTube a e) :
    HasProd (actualLocalUnmarked K S P psi u s w z)
      (rowCorrection K S P psi (arithmeticHighEulerData K S P psi) ∅ u s w z) := by
  have h := (explicitEuler_hasProdLocallyUniformlyOn (exteriorSupport K S u.ideal) ∅
    (fun p : ExteriorPrime K S => (p.val.asIdeal.absNorm : ℝ))
    (rowW K S P u) (rowD K S P psi u) (rowE K S P psi)
    (rowPhaseData K S P psi u) (rowIndex K S u)
    (exteriorPrime_norm_two_le K S) ha ha1 he.le he1
    (rowW_norm K S P u) (rowD_norm K S P psi u) (rowE_norm K S P psi)
    (summable_exteriorPrime_swept_error K S he)).hasProd hv
  rw [rowCorrection_eq_explicitEuler K S P psi ∅ u ha he.le (s, w, z) hv]
  have hf : actualLocalUnmarked K S P psi u s w z =
      fun p : ExteriorPrime K S => explicitLocalEuler (exteriorSupport K S u.ideal) ∅
        (fun p : ExteriorPrime K S => (p.val.asIdeal.absNorm : ℝ))
        (rowW K S P u) (rowD K S P psi u) (rowE K S P psi)
        (rowPhaseData K S P psi u) (rowIndex K S u) p (s, w, z) := by
    funext p
    exact localFactor_eq_explicit K S P psi ∅ u ha he.le p (s, w, z) hv
  rw [hf]
  exact h

theorem actual_unmarked_norm_sub_one_le (P : ProbeData K S) (psi : HeckeCharacter K)
    (u : FrequencyRow K S) {a e : ℝ} (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1)
    (he : 0 ≤ e) (he1 : e ≤ 1 / 10000)
    (s w z : ℂ) (hv : (s, w, z) ∈ sweptTube a e) (p : ExteriorPrime K S) :
    ‖actualLocalUnmarked K S P psi u s w z p - 1‖ ≤
      (9 + 11 / sweptTubeEulerMargin) * (p.val.asIdeal.absNorm : ℝ) ^ (-8 * e) := by
  have hq := exteriorPrime_norm_two_le K S p
  have hq0 : (0 : ℝ) ≤ p.val.asIdeal.absNorm := by linarith
  have hq1 : (1 : ℝ) ≤ p.val.asIdeal.absNorm := by linarith
  have hc : 0 ≤ 11 / sweptTubeEulerMargin := div_nonneg (by norm_num) sweptTubeEulerMargin_pos.le
  unfold actualLocalUnmarked
  rw [localFactor_eq_explicit K S P psi ∅ u ha he p (s, w, z) hv]
  by_cases hR : p ∈ exteriorSupport K S u.ideal
  · simp only [explicitLocalEuler, if_pos hR, Finset.notMem_empty, if_false, sub_zero]
    have h := ramifiedTable_swept_bound (rowPhaseData K S P psi u p)
      (p.val.asIdeal.absNorm : ℝ) a e hq (by linarith) he he1 s w z
      hv.1.le hv.2.1.le hv.2.2.le (rowIndex K S u p)
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hq0 _))
  · simp only [explicitLocalEuler, if_neg hR, Finset.notMem_empty, if_false, sub_zero]
    have h := phaseRowEuler_sweptTube_bound hq ha ha1 he he1
      (rowW K S P u p) (rowD K S P psi u p) (rowE K S P psi p)
      (rowW_norm K S P u p) (rowD_norm K S P psi u p) (rowE_norm K S P psi p)
      (s, w, z) hv
    exact h.trans ((mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -1 - 8 * e ≤ -8 * e)) hc).trans
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hq0 _)))

/-- One scale cutoff supplies both the actual local denominator margin
and the explicit scalar cutoff in every ramified finite-table bound. -/
theorem exists_window_local_cutoff (g : PrimeWindowGeometry)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (P : ProbeData K S) (psi : HeckeCharacter K) (T : Finset (HeckeCharacter K))
        (u : FrequencyRow K S) (a : ℝ), 51 / 100 ≤ a → a ≤ 1 →
      ∀ s w z : ℂ, (s, w, z) ∈ sweptTube a e →
      ∀ i : Fin g.slots, ∀ p ∈ primeWindow K S g T Z i,
        ‖actualLocalUnmarked K S P psi u s w z p - 1‖ ≤ 1 / 2 ∧
          9 * (p.val.asIdeal.absNorm : ℝ) ^ (-10 * e) ≤ 1 / 2 := by
  let B : ℝ := 9 + 11 / sweptTubeEulerMargin
  have ht : Tendsto (fun q : ℝ => B * q ^ (-8 * e)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < 8 * e by linarith)).const_mul B
    simpa only [mul_zero, neg_mul] using h
  have hev : ∀ᶠ q : ℝ in atTop, B * q ^ (-8 * e) ≤ 1 / 2 :=
    (ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono (fun _ h => h.le)
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp hev
  have hj : (0 : ℝ) < g.slots := by exact_mod_cast g.slots_pos
  have halpha : 0 < (1 / 6 : ℝ) / g.slots := div_pos (by norm_num) hj
  obtain ⟨Z0, hZ0⟩ := (tendsto_atTop_atTop.mp (tendsto_rpow_atTop halpha)) X0
  refine ⟨max 1 Z0, le_max_left _ _, ?_⟩
  intro Z hZ P psi T u a ha ha1 s w z hv i p hp
  have hX : X0 ≤ primeScale g Z := hZ0 Z ((le_max_right _ _).trans hZ)
  have hq : X0 ≤ (p.val.asIdeal.absNorm : ℝ) :=
    hX.trans (actual_primeWindow_norm_range K S g T Z i p hp).2.1.le
  have hb := (actual_unmarked_norm_sub_one_le K S P psi u ha ha1 he.le he1 s w z hv p).trans
    (hX0 _ hq)
  refine ⟨hb, ?_⟩
  have hq1 : (1 : ℝ) ≤ p.val.asIdeal.absNorm :=
    (by norm_num : (1 : ℝ) ≤ 2).trans (exteriorPrime_norm_two_le K S p)
  calc
    _ ≤ 9 * (p.val.asIdeal.absNorm : ℝ) ^ (-8 * e) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)) (by norm_num)
    _ ≤ B * (p.val.asIdeal.absNorm : ℝ) ^ (-8 * e) :=
      mul_le_mul_of_nonneg_right (by
        dsimp only [B]
        have := div_nonneg (by norm_num : (0 : ℝ) ≤ 11) sweptTubeEulerMargin_pos.le
        linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ _ := hX0 _ hq

/-- Every selected local denominator is nonzero after one fixed scale
cutoff, including the repeated and valuation-one row primes. -/
theorem exists_window_unmarked_nonzero (g : PrimeWindowGeometry)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (P : ProbeData K S) (psi : HeckeCharacter K) (T : Finset (HeckeCharacter K))
        (u : FrequencyRow K S) (a : ℝ), 51 / 100 ≤ a → a ≤ 1 →
      ∀ s w z : ℂ, (s, w, z) ∈ sweptTube a e →
      ∀ i : Fin g.slots, ∀ p ∈ primeWindow K S g T Z i,
        actualLocalUnmarked K S P psi u s w z p ≠ 0 := by
  obtain ⟨Z0, hZ0, hbound⟩ := exists_window_local_cutoff K S g he he1
  refine ⟨Z0, hZ0, ?_⟩
  intro Z hZ P psi T u a ha ha1 s w z hv i p hp
  have hb := (hbound Z hZ P psi T u a ha ha1 s w z hv i p hp).1
  intro hz
  rw [hz, zero_sub, norm_neg, norm_one] at hb
  norm_num at hb

/-- All three actual local cases, with one common cutoff fixed before
the target, row, contour and selected prime. Target unramifiedness is the
original outside-S arithmetic property; no local norm estimate is an
input. -/
theorem exists_actual_local_compensation_bounds (g : PrimeWindowGeometry)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (P : ProbeData K S) (psi : HeckeCharacter K),
      ThetaCalibrationInput K S P.arithmetic P.Lambda P.G →
      (∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val) →
      ∀ (T : Finset (HeckeCharacter K)) (u : FrequencyRow K S)
        (a : ℝ), 51 / 100 ≤ a → a ≤ 1 →
      ∀ s w z : ℂ, s.re = a + 16 * e → w.re = 1 - a - 6 * e → z.re = 17 / 50 →
      ∀ i : Fin g.slots, ∀ p ∈ primeWindow K S g T Z i,
        (p ∉ exteriorSupport K S u.ideal →
          ‖actualLocalCompensation K S P psi u s w z p +
            (p.val.asIdeal.absNorm : ℂ) ^ (z - 1) *
              conj (primeCoefficient K (arithmeticRowCharacter K S P u) p.val)‖ ≤
            regularCompensationErrorConstant *
              (p.val.asIdeal.absNorm : ℝ) ^ (-(29 / 25 : ℝ))) ∧
        (primeExponents u.ideal.val p.val = 1 →
          ‖actualLocalCompensation K S P psi u s w z p‖ ≤
            13 * (p.val.asIdeal.absNorm : ℝ) ^ (-(4 / 25 : ℝ))) ∧
        (2 ≤ primeExponents u.ideal.val p.val →
          ‖actualLocalCompensation K S P psi u s w z p‖ ≤
            19 * (p.val.asIdeal.absNorm : ℝ) ^ (a - 33 / 50 + 6 * e)) := by
  obtain ⟨Z0, hZ0, hcut⟩ := exists_window_local_cutoff K S g he he1
  refine ⟨Z0, hZ0, ?_⟩
  intro Z hZ P psi hcal hpsi T u a ha ha1 s w z hs hw hz i p hp
  have hv := swept_contour_mem_tube he le_rfl s w z hs hw hz
  obtain ⟨hclose, hscalar⟩ := hcut Z hZ P psi T u a ha ha1 s w z hv i p hp
  have hrow (hn : primeExponents u.ideal.val p.val ≠ 0) :
      p ∈ exteriorSupport K S u.ideal := by
    apply (mem_exteriorSupport_iff K S u.ideal p).mpr
    apply (mem_idealPrimeSupport_iff K u.ideal.val p.val).mp
    exact Finsupp.mem_support_iff.mpr hn
  refine ⟨?_, ?_, ?_⟩
  · intro hreg
    exact actualLocalCompensation_regular_error_bound K S P psi u ha ha1 he he1
      s w z hs hw hz p hreg (hpsi p) hclose
  · intro hone
    exact actualLocalCompensation_valuation_one_bound K S P psi hcal u ha ha1 he
      (by linarith) s w z hs hw hz p (hrow (by omega)) hone hscalar
  · intro hrepeat
    exact actualLocalCompensation_ramified_bound K S P psi hcal u ha he
      s w z hs hw hz p (hrow (by omega)) hscalar

/-- The main slot of the actual full correction consumes the actual
zero-free prime cap. Membership of the conjugate row is derived from
the original companion 1 and the constructed Euler provider. -/
theorem exists_actualCompensationMainSlot_cap
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (hcomp : (1 : HeckeCharacter K) ∈ companions)
    (P : ProbeData K S) (g : PrimeWindowGeometry)
    {e eps kappa : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (heps : 0 < eps) (hkappa : 0 < kappa) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧
      ∀ Z T : ℝ, Z0 ≤ Z → ∀ d : ℝ, (1 / 16 : ℝ) ≤ d →
      ∀ u : FrequencyRow K S, Z ^ d ≤ frequencyRowNorm K S u →
      ∀ a U : ℝ, ∀ z : ℂ, 1 / 2 ≤ a → a ≤ 1 → z.re = 17 / 50 →
      NormForm.internalHeight Z T kappa + |z.im| + 2 ≤ U →
      rowZeroBelow K S psi companions P (arithmeticHighEulerData K S P psi) u U (a + 2 * e) →
      ∀ i : Fin g.slots,
        ‖actualCompensationMainSlot K S P g ∅ u Z z i‖ ≤
          C * (u.ideal.val.val.radical.absNorm : ℝ) ^ eps *
            (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) *
            (primeScale g Z) ^ (a - 33 / 50 + 8 * e) := by
  obtain ⟨C, Z0, hC, hZ0, hcap⟩ := NormFormPrimeCap.exists_actual_compensation_main_cap
    K S psi companions P (arithmeticHighEulerData K S P psi) g he he' heps hkappa
  refine ⟨C, Z0, hC, hZ0, ?_⟩
  intro Z T hZ d hd u hu a U z ha ha1 hz hU hbelow i
  have hmem : conjugate (arithmeticRowCharacter K S P u) ∈
      physicalRowFamily K S psi companions P (arithmeticHighEulerData K S P psi) u := by
    apply Finset.mem_biUnion.mpr
    refine ⟨1, hcomp, ?_⟩
    simp
  have h := hcap Z T hZ d hd u hu a U z ha ha1 hz hU hbelow
    (conjugate (arithmeticRowCharacter K S P u)) hmem i
  simpa only [actualCompensationMainSlot, conjugate, primeCoefficient_inv] using h

theorem exists_actualRegularErrorSlot_bound (g : PrimeWindowGeometry)
    {e eta : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000) (heta : 0 < eta) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (P : ProbeData K S) (psi : HeckeCharacter K),
      (∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val) →
      ∀ (T : Finset (HeckeCharacter K)) (u : FrequencyRow K S)
        (a : ℝ), 51 / 100 ≤ a → a ≤ 1 →
      ∀ s w z : ℂ, s.re = a + 16 * e → w.re = 1 - a - 6 * e → z.re = 17 / 50 →
      ∀ i : Fin g.slots,
        ‖actualRegularErrorSlot K S P psi g T u Z s w z i‖ ≤
          C * (primeScale g Z) ^ (-(4 / 25 : ℝ) + eta) := by
  obtain ⟨Z1, hZ1, hcut⟩ := exists_window_local_cutoff K S g he he1
  obtain ⟨Z2, hZ2, hscale⟩ := NormFormPrimeCap.exists_primeScale_cutoff g
  obtain ⟨M, hM, hprofile⟩ := exists_primeWindow_profile_norm_bound g
  let delta : ℝ := min eta (2 / 25)
  have hdelta : 0 < delta := lt_min heta (by norm_num)
  have hdelta1 : delta ≤ 4 / 25 := (min_le_right eta (2 / 25)).trans (by norm_num)
  let C : ℝ := M * regularCompensationErrorConstant * regularPrimeErrorMass K S delta
  have hC : 0 < C := mul_pos (mul_pos hM regularCompensationErrorConstant_pos)
    (regularPrimeErrorMass_pos K S delta)
  refine ⟨C, max Z1 Z2, hC, hZ1.trans (le_max_left _ _), ?_⟩
  intro Z hZ P psi hpsi T u a ha ha1 s w z hs hw hz i
  have hZZ1 : Z1 ≤ Z := (le_max_left _ _).trans hZ
  have hZZ2 : Z2 ≤ Z := (le_max_right _ _).trans hZ
  have hP1 : 1 ≤ primeScale g Z := (by norm_num : (1 : ℝ) ≤ 2).trans (hscale Z hZZ2)
  have hP0 : 0 < primeScale g Z := zero_lt_one.trans_le hP1
  have hv := swept_contour_mem_tube he le_rfl s w z hs hw hz
  let F := (primeWindow K S g T Z i).filter (fun p => p ∉ exteriorSupport K S u.ideal)
  have hterm : ∀ p ∈ F,
      ‖windowWeight K S g Z i p *
        (actualLocalCompensation K S P psi u s w z p +
          (p.val.asIdeal.absNorm : ℂ) ^ (z - 1) *
            conj (primeCoefficient K (arithmeticRowCharacter K S P u) p.val))‖ ≤
      (M * regularCompensationErrorConstant) *
        (p.val.asIdeal.absNorm : ℝ) ^ (-(29 / 25 : ℝ)) := by
    intro p hp
    obtain ⟨hpw, hreg⟩ := Finset.mem_filter.mp hp
    have hclose := (hcut Z hZZ1 P psi T u a ha ha1 s w z hv i p hpw).1
    have hb := actualLocalCompensation_regular_error_bound K S P psi u ha ha1 he he1
      s w z hs hw hz p hreg (hpsi p) hclose
    have hwgt : ‖windowWeight K S g Z i p‖ ≤ M := hprofile i _
    rw [norm_mul]
    exact (mul_le_mul hwgt hb (norm_nonneg _) hM.le).trans_eq (by ring)
  have hsum := regular_prime_error_sum_le K S F hP0 hdelta hdelta1 (fun p hp =>
    (actual_primeWindow_norm_range K S g T Z i p (Finset.mem_filter.mp hp).1).2.1.le)
  change ‖∑ p ∈ F, windowWeight K S g Z i p *
      (actualLocalCompensation K S P psi u s w z p +
        (p.val.asIdeal.absNorm : ℂ) ^ (z - 1) *
          conj (primeCoefficient K (arithmeticRowCharacter K S P u) p.val))‖ ≤ _
  calc
    _ ≤ ∑ p ∈ F, ‖windowWeight K S g Z i p *
        (actualLocalCompensation K S P psi u s w z p +
          (p.val.asIdeal.absNorm : ℂ) ^ (z - 1) *
            conj (primeCoefficient K (arithmeticRowCharacter K S P u) p.val))‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ F, (M * regularCompensationErrorConstant) *
        (p.val.asIdeal.absNorm : ℝ) ^ (-(29 / 25 : ℝ)) := Finset.sum_le_sum hterm
    _ = (M * regularCompensationErrorConstant) *
        ∑ p ∈ F, (p.val.asIdeal.absNorm : ℝ) ^ (-(29 / 25 : ℝ)) := (Finset.mul_sum ..).symm
    _ ≤ (M * regularCompensationErrorConstant) *
        (regularPrimeErrorMass K S delta * (primeScale g Z) ^ (-(4 / 25 : ℝ) + delta)) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hM.le regularCompensationErrorConstant_pos.le)
    _ = C * (primeScale g Z) ^ (-(4 / 25 : ℝ) + delta) := by dsimp only [C]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hP1 (by
        dsimp only [delta]
        linarith [min_le_left eta (2 / 25)])) hC.le

theorem exists_actualValuationOneSlot_bound (g : PrimeWindowGeometry)
    {e eta : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000) (heta : 0 < eta) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (P : ProbeData K S) (psi : HeckeCharacter K),
      ThetaCalibrationInput K S P.arithmetic P.Lambda P.G →
      ∀ (T : Finset (HeckeCharacter K)) (u : FrequencyRow K S)
        (a : ℝ), 51 / 100 ≤ a → a ≤ 1 →
      ∀ s w z : ℂ, s.re = a + 16 * e → w.re = 1 - a - 6 * e → z.re = 17 / 50 →
      ∀ i : Fin g.slots,
        ‖actualValuationOneSlot K S P psi g T u Z s w z i‖ ≤
          C * frequencyRowNorm K S u ^ eta * (primeScale g Z) ^ (-(4 / 25 : ℝ)) := by
  obtain ⟨Z1, hZ1, hcut⟩ := exists_window_local_cutoff K S g he he1
  obtain ⟨Z2, hZ2, hscale⟩ := NormFormPrimeCap.exists_primeScale_cutoff g
  obtain ⟨M, hM, hprofile⟩ := exists_primeWindow_profile_norm_bound g
  refine ⟨M * 13 * repeatedTupleConstant 1 eta, max Z1 Z2,
    mul_pos (mul_pos hM (by norm_num)) (repeatedTupleConstant_pos 1 heta),
    hZ1.trans (le_max_left _ _), ?_⟩
  intro Z hZ P psi hcal T u a ha ha1 s w z hs hw hz i
  have hZZ1 : Z1 ≤ Z := (le_max_left _ _).trans hZ
  have hZZ2 : Z2 ≤ Z := (le_max_right _ _).trans hZ
  have hP0 : 0 < primeScale g Z :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (hscale Z hZZ2)
  have hv := swept_contour_mem_tube he le_rfl s w z hs hw hz
  let F := (primeWindow K S g T Z i).filter (fun p => primeExponents u.ideal.val p.val = 1)
  have hsupport : F.image Subtype.val ⊆ (primeExponents u.ideal.val).support := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact Finsupp.mem_support_iff.mpr (by
      rw [(Finset.mem_filter.mp hq).2]
      norm_num)
  have hcardNat : F.card ≤ (primeExponents u.ideal.val).support.card := by
    calc
      _ = (F.image Subtype.val).card := (Finset.card_image_of_injective F Subtype.val_injective).symm
      _ ≤ _ := Finset.card_le_card hsupport
  have hcard : (F.card : ℝ) ≤ repeatedTupleConstant 1 eta * frequencyRowNorm K S u ^ eta := by
    have hc : (F.card : ℝ) ≤ ((primeExponents u.ideal.val).support.card : ℝ) := by
      exact_mod_cast hcardNat
    have ht := actual_support_tuple_count_subpower K u.ideal.val 1 heta
    simp only [pow_one] at ht
    exact hc.trans ((le_add_of_nonneg_right zero_le_one).trans ht)
  have hterm : ∀ p ∈ F,
      ‖windowWeight K S g Z i p * actualLocalCompensation K S P psi u s w z p‖ ≤
        M * 13 * (primeScale g Z) ^ (-(4 / 25 : ℝ)) := by
    intro p hp
    obtain ⟨hpw, hone⟩ := Finset.mem_filter.mp hp
    have hrow : p ∈ exteriorSupport K S u.ideal := by
      apply (mem_exteriorSupport_iff K S u.ideal p).mpr
      apply (mem_idealPrimeSupport_iff K u.ideal.val p.val).mp
      exact Finsupp.mem_support_iff.mpr (by rw [hone]; norm_num)
    have hscalar := (hcut Z hZZ1 P psi T u a ha ha1 s w z hv i p hpw).2
    have hb := actualLocalCompensation_valuation_one_bound K S P psi hcal u ha ha1 he
      (by linarith) s w z hs hw hz p hrow hone hscalar
    have hpow : (p.val.asIdeal.absNorm : ℝ) ^ (-(4 / 25 : ℝ)) ≤
        (primeScale g Z) ^ (-(4 / 25 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hP0
        (actual_primeWindow_norm_range K S g T Z i p hpw).2.1.le (by norm_num)
    rw [norm_mul]
    calc
      _ ≤ M * (13 * (p.val.asIdeal.absNorm : ℝ) ^ (-(4 / 25 : ℝ))) :=
        mul_le_mul (hprofile i _) hb (norm_nonneg _) hM.le
      _ ≤ M * (13 * (primeScale g Z) ^ (-(4 / 25 : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by norm_num)) hM.le
      _ = _ := by ring
  change ‖∑ p ∈ F, windowWeight K S g Z i p * actualLocalCompensation K S P psi u s w z p‖ ≤ _
  calc
    _ ≤ ∑ p ∈ F, ‖windowWeight K S g Z i p * actualLocalCompensation K S P psi u s w z p‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ F, M * 13 * (primeScale g Z) ^ (-(4 / 25 : ℝ)) := Finset.sum_le_sum hterm
    _ = (F.card : ℝ) * (M * 13 * (primeScale g Z) ^ (-(4 / 25 : ℝ))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (repeatedTupleConstant 1 eta * frequencyRowNorm K S u ^ eta) *
        (M * 13 * (primeScale g Z) ^ (-(4 / 25 : ℝ))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-- The repeated primes remain a literal finite sum. This is the form
needed to allocate their distinct-prime product against the actual row
radical before summing over choices. -/
theorem exists_actualRepeatedSlot_bound (g : PrimeWindowGeometry)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (P : ProbeData K S) (psi : HeckeCharacter K),
      ThetaCalibrationInput K S P.arithmetic P.Lambda P.G →
      ∀ (T : Finset (HeckeCharacter K)) (u : FrequencyRow K S)
        (a : ℝ), 51 / 100 ≤ a → a ≤ 1 →
      ∀ s w z : ℂ, s.re = a + 16 * e → w.re = 1 - a - 6 * e → z.re = 17 / 50 →
      ∀ i : Fin g.slots,
        ‖actualRepeatedSlot K S P psi g T u Z s w z i‖ ≤
          C * (primeScale g Z) ^ (-(4 / 25 : ℝ)) *
            ∑ p ∈ repeatedPrimeWindow K S u g T Z i,
              (p.val.asIdeal.absNorm : ℝ) ^ (a - 1 / 2 + 6 * e) := by
  obtain ⟨Z1, hZ1, hcut⟩ := exists_window_local_cutoff K S g he he1
  obtain ⟨Z2, hZ2, hscale⟩ := NormFormPrimeCap.exists_primeScale_cutoff g
  obtain ⟨M, hM, hprofile⟩ := exists_primeWindow_profile_norm_bound g
  refine ⟨M * 19, max Z1 Z2, mul_pos hM (by norm_num),
    hZ1.trans (le_max_left _ _), ?_⟩
  intro Z hZ P psi hcal T u a ha ha1 s w z hs hw hz i
  have hZZ1 : Z1 ≤ Z := (le_max_left _ _).trans hZ
  have hZZ2 : Z2 ≤ Z := (le_max_right _ _).trans hZ
  have hP0 : 0 < primeScale g Z :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (hscale Z hZZ2)
  have hv := swept_contour_mem_tube he le_rfl s w z hs hw hz
  have hterm : ∀ p ∈ repeatedPrimeWindow K S u g T Z i,
      ‖windowWeight K S g Z i p * actualLocalCompensation K S P psi u s w z p‖ ≤
        (M * 19 * (primeScale g Z) ^ (-(4 / 25 : ℝ))) *
          (p.val.asIdeal.absNorm : ℝ) ^ (a - 1 / 2 + 6 * e) := by
    intro p hp
    obtain ⟨hpw, hrepeat⟩ := Finset.mem_filter.mp hp
    have hrow : p ∈ exteriorSupport K S u.ideal := by
      apply (mem_exteriorSupport_iff K S u.ideal p).mpr
      apply (mem_idealPrimeSupport_iff K u.ideal.val p.val).mp
      exact Finsupp.mem_support_iff.mpr (by omega)
    have hq0 : (0 : ℝ) < p.val.asIdeal.absNorm :=
      hP0.trans (actual_primeWindow_norm_range K S g T Z i p hpw).2.1
    have hscalar := (hcut Z hZZ1 P psi T u a ha ha1 s w z hv i p hpw).2
    have hb := actualLocalCompensation_ramified_bound K S P psi hcal u ha he
      s w z hs hw hz p hrow hscalar
    have hpow : (p.val.asIdeal.absNorm : ℝ) ^ (-(4 / 25 : ℝ)) ≤
        (primeScale g Z) ^ (-(4 / 25 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hP0
        (actual_primeWindow_norm_range K S g T Z i p hpw).2.1.le (by norm_num)
    rw [norm_mul]
    calc
      _ ≤ M * (19 * (p.val.asIdeal.absNorm : ℝ) ^ (a - 33 / 50 + 6 * e)) :=
        mul_le_mul (hprofile i _) hb (norm_nonneg _) hM.le
      _ = (M * 19 * (p.val.asIdeal.absNorm : ℝ) ^ (-(4 / 25 : ℝ))) *
          (p.val.asIdeal.absNorm : ℝ) ^ (a - 1 / 2 + 6 * e) := by
        rw [mul_assoc (M * 19), ← Real.rpow_add hq0]
        rw [show -(4 / 25 : ℝ) + (a - 1 / 2 + 6 * e) = a - 33 / 50 + 6 * e by ring]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by positivity)) (Real.rpow_nonneg hq0.le _)
  unfold actualRepeatedSlot
  calc
    _ ≤ ∑ p ∈ repeatedPrimeWindow K S u g T Z i,
        ‖windowWeight K S g Z i p * actualLocalCompensation K S P psi u s w z p‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ repeatedPrimeWindow K S u g T Z i,
        (M * 19 * (primeScale g Z) ^ (-(4 / 25 : ℝ))) *
          (p.val.asIdeal.absNorm : ℝ) ^ (a - 1 / 2 + 6 * e) := Finset.sum_le_sum hterm
    _ = _ := (Finset.mul_sum ..).symm

/-- One estimate for the actual complete slot. The three analytic
contributions are the zero-free character main term, the summable and
valuation-one errors, and the literal repeated-prime choices. All
constants and cutoffs precede the scale, row, height and contour point.
No lower bound for the prime normalizer is used here. -/
theorem exists_actualFullCorrectionSlot_bound
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (hcomp : (1 : HeckeCharacter K) ∈ companions)
    (P : ProbeData K S) (g : PrimeWindowGeometry)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
    (hpsi : ∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val)
    {e eps eta kappa : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (heps : 0 < eps) (heta : 0 < eta) (hkappa : 0 < kappa) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧
      ∀ Z T : ℝ, Z0 ≤ Z → ∀ d : ℝ, (1 / 16 : ℝ) ≤ d →
      ∀ u : FrequencyRow K S, Z ^ d ≤ frequencyRowNorm K S u →
      ∀ a U : ℝ, 51 / 100 ≤ a → a ≤ 1 →
      ∀ s w z : ℂ, s.re = a + 16 * e → w.re = 1 - a - 6 * e → z.re = 17 / 50 →
      NormForm.internalHeight Z T kappa + |z.im| + 2 ≤ U →
      rowZeroBelow K S psi companions P (arithmeticHighEulerData K S P psi) u U (a + 2 * e) →
      ∀ i : Fin g.slots,
        ‖actualFullCorrectionSlot K S P psi g ∅ u Z s w z i‖ ≤ C *
          ((u.ideal.val.val.radical.absNorm : ℝ) ^ eps *
              (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) *
              (primeScale g Z) ^ (a - 33 / 50 + 8 * e) +
            frequencyRowNorm K S u ^ eta * (primeScale g Z) ^ (-(4 / 25 : ℝ) + eta) +
            (primeScale g Z) ^ (-(4 / 25 : ℝ)) *
              ∑ p ∈ repeatedPrimeWindow K S u g ∅ Z i,
                (p.val.asIdeal.absNorm : ℝ) ^ (a - 1 / 2 + 6 * e)) := by
  obtain ⟨CM, ZM, hCM, hZM, hmain⟩ := exists_actualCompensationMainSlot_cap
    K S psi companions hcomp P g he (by linarith) heps hkappa
  obtain ⟨CR, ZR, hCR, hZR, hregular⟩ := exists_actualRegularErrorSlot_bound K S g he he1 heta
  obtain ⟨CV, ZV, hCV, hZV, hvaluation⟩ := exists_actualValuationOneSlot_bound K S g he he1 heta
  obtain ⟨CQ, ZQ, hCQ, hZQ, hrepeated⟩ := exists_actualRepeatedSlot_bound K S g he he1
  obtain ⟨ZX, hZX, hscale⟩ := NormFormPrimeCap.exists_primeScale_cutoff g
  let C : ℝ := CM + CR + CV + CQ
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C, max ZM (max ZR (max ZV (max ZQ ZX))), hC,
    hZM.trans (le_max_left _ _), ?_⟩
  intro Z T hZ d hd u hu a U ha ha1 s w z hs hw hz hU hbelow i
  have hZZM : ZM ≤ Z := (le_max_left _ _).trans hZ
  have hZZR : ZR ≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans hZ)
  have hZZV : ZV ≤ Z := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hZZQ : ZQ ≤ Z := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ)))
  have hZZX : ZX ≤ Z := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ)))
  have hZ1 : 1 ≤ Z := hZM.trans hZZM
  have hX1 : 1 ≤ primeScale g Z := (by norm_num : (1 : ℝ) ≤ 2).trans (hscale Z hZZX)
  have hX0 : 0 < primeScale g Z := zero_lt_one.trans_le hX1
  have hNu1 : 1 ≤ frequencyRowNorm K S u := one_le_idealNorm K u.ideal.val
  have hNu0 : 0 < frequencyRowNorm K S u := zero_lt_one.trans_le hNu1
  have hNueta : 1 ≤ frequencyRowNorm K S u ^ eta := Real.one_le_rpow hNu1 heta.le
  have hheight0 : 0 ≤ NormForm.internalHeight Z T kappa :=
    (Real.rpow_nonneg (zero_le_one.trans hZ1) kappa).trans (le_max_right _ _)
  have hU0 : 0 ≤ 2 + U := by linarith [abs_nonneg z.im]
  let A : ℝ := (u.ideal.val.val.radical.absNorm : ℝ) ^ eps *
    (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) *
    (primeScale g Z) ^ (a - 33 / 50 + 8 * e)
  let B : ℝ := frequencyRowNorm K S u ^ eta *
    (primeScale g Z) ^ (-(4 / 25 : ℝ) + eta)
  let D : ℝ := (primeScale g Z) ^ (-(4 / 25 : ℝ)) *
    ∑ p ∈ repeatedPrimeWindow K S u g ∅ Z i,
      (p.val.asIdeal.absNorm : ℝ) ^ (a - 1 / 2 + 6 * e)
  have hA0 : 0 ≤ A := mul_nonneg (mul_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hU0 _))
      (Real.rpow_nonneg hX0.le _)
  have hB0 : 0 ≤ B := mul_nonneg (Real.rpow_nonneg hNu0.le _) (Real.rpow_nonneg hX0.le _)
  have hD0 : 0 ≤ D := mul_nonneg (Real.rpow_nonneg hX0.le _)
    (Finset.sum_nonneg (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hM : ‖actualCompensationMainSlot K S P g ∅ u Z z i‖ ≤ CM * A := by
    simpa only [A, mul_assoc] using
      hmain Z T hZZM d hd u hu a U z (by linarith) ha1 hz hU hbelow i
  have hR : ‖actualRegularErrorSlot K S P psi g ∅ u Z s w z i‖ ≤ CR * B := by
    apply (hregular Z hZZR P psi hpsi ∅ u a ha ha1 s w z hs hw hz i).trans
    dsimp only [B]
    exact mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left (Real.rpow_nonneg hX0.le _) hNueta) hCR.le
  have hV : ‖actualValuationOneSlot K S P psi g ∅ u Z s w z i‖ ≤ CV * B := by
    apply (hvaluation Z hZZV P psi hcal ∅ u a ha ha1 s w z hs hw hz i).trans
    have hp := Real.rpow_le_rpow_of_exponent_le hX1
      (le_add_of_nonneg_right heta.le : -(4 / 25 : ℝ) ≤ -(4 / 25 : ℝ) + eta)
    simpa only [B, mul_assoc] using
      mul_le_mul_of_nonneg_left hp (mul_nonneg hCV.le (Real.rpow_nonneg hNu0.le _))
  have hQ : ‖actualRepeatedSlot K S P psi g ∅ u Z s w z i‖ ≤ CQ * D := by
    simpa only [D, mul_assoc] using hrepeated Z hZZQ P psi hcal ∅ u a ha ha1 s w z hs hw hz i
  have hsum : ‖actualFullCorrectionSlot K S P psi g ∅ u Z s w z i‖ ≤
      CM * A + (CR + CV) * B + CQ * D := by
    rw [actualFullCorrectionSlot_decomposition]
    calc
      _ ≤ ‖-actualCompensationMainSlot K S P g ∅ u Z z i +
          actualRegularErrorSlot K S P psi g ∅ u Z s w z i +
          actualValuationOneSlot K S P psi g ∅ u Z s w z i‖ +
            ‖actualRepeatedSlot K S P psi g ∅ u Z s w z i‖ := norm_add_le _ _
      _ ≤ (‖-actualCompensationMainSlot K S P g ∅ u Z z i +
          actualRegularErrorSlot K S P psi g ∅ u Z s w z i‖ +
          ‖actualValuationOneSlot K S P psi g ∅ u Z s w z i‖) +
            ‖actualRepeatedSlot K S P psi g ∅ u Z s w z i‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (‖actualCompensationMainSlot K S P g ∅ u Z z i‖ +
          ‖actualRegularErrorSlot K S P psi g ∅ u Z s w z i‖ +
          ‖actualValuationOneSlot K S P psi g ∅ u Z s w z i‖) +
            ‖actualRepeatedSlot K S P psi g ∅ u Z s w z i‖ := by
        apply add_le_add ?_ le_rfl
        apply add_le_add ?_ le_rfl
        simpa only [norm_neg] using
          norm_add_le (-actualCompensationMainSlot K S P g ∅ u Z z i)
            (actualRegularErrorSlot K S P psi g ∅ u Z s w z i)
      _ ≤ (CM * A + CR * B + CV * B) + CQ * D :=
        add_le_add (add_le_add (add_le_add hM hR) hV) hQ
      _ = _ := by ring
  change _ ≤ C * (A + B + D)
  apply hsum.trans
  have hCM' : CM ≤ C := by dsimp only [C]; linarith
  have hCRV : CR + CV ≤ C := by dsimp only [C]; linarith
  have hCQ' : CQ ≤ C := by dsimp only [C]; linarith
  calc
    _ ≤ C * A + C * B + C * D := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_right hCM' hA0)
        (mul_le_mul_of_nonneg_right hCRV hB0)) (mul_le_mul_of_nonneg_right hCQ' hD0)
    _ = _ := by ring

theorem subsetPrimeIdeal_norm_eq_prod (g : PrimeWindowGeometry)
    (p : Fin g.slots → ExteriorPrime K S) (hp : Function.Injective p)
    (J : Finset (Fin g.slots)) :
    exteriorNorm K S (subsetPrimeIdeal K S p J) =
      ∏ i ∈ J, ((p i).val.asIdeal.absNorm : ℝ) := by
  change ((∏ q ∈ (J.image p).image Subtype.val, q.asIdeal).absNorm : ℝ) = _
  rw [map_prod, Nat.cast_prod, Finset.prod_image Subtype.val_injective.injOn,
    Finset.prod_image hp.injOn]

theorem subsetPrimeIdeal_coefficient_eq_prod (g : PrimeWindowGeometry)
    (psi : HeckeCharacter K) (p : Fin g.slots → ExteriorPrime K S)
    (hp : Function.Injective p) (J : Finset (Fin g.slots)) :
    heckeIdealCoefficient K psi (subsetPrimeIdeal K S p J).val =
      ∏ i ∈ J, primeCoefficient K psi (p i).val := by
  change (idealCoefficientHom (primeCoefficient K psi))
    (∏ q ∈ (J.image p).image Subtype.val, q.asIdeal) = _
  rw [map_prod]
  change (∏ q ∈ (J.image p).image Subtype.val,
    idealCoefficient (primeCoefficient K psi) q.asIdeal) = _
  simp only [idealCoefficient_prime]
  rw [Finset.prod_image Subtype.val_injective.injOn, Finset.prod_image hp.injOn]

private theorem ofReal_prod_cpow {ι : Type*} (F : Finset ι) (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (s : ℂ) :
    ((∏ i ∈ F, q i : ℝ) : ℂ) ^ s = ∏ i ∈ F, (q i : ℂ) ^ s := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (hq i) (Finset.prod_nonneg (fun j _ => hq j)), ih]

theorem subsetPrimeIdeal_norm_cpow (g : PrimeWindowGeometry)
    (p : Fin g.slots → ExteriorPrime K S) (hp : Function.Injective p)
    (J : Finset (Fin g.slots)) (s : ℂ) :
    (exteriorNorm K S (subsetPrimeIdeal K S p J) : ℂ) ^ s =
      ∏ i ∈ J, ((p i).val.asIdeal.absNorm : ℂ) ^ s := by
  rw [subsetPrimeIdeal_norm_eq_prod K S g p hp J]
  simpa only [Complex.ofReal_natCast] using ofReal_prod_cpow J
    (fun i => ((p i).val.asIdeal.absNorm : ℝ)) (fun _ => Nat.cast_nonneg _) s

/-- The original powerset of slots is factored for one actual distinct
prime tuple, preserving every ramified and unramified table value. -/
theorem actual_compensation_tuple_factorization (P : ProbeData K S)
    (psi : HeckeCharacter K) (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z : ℝ)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1)
    (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (s w z : ℂ) (hv : (s, w, z) ∈ sweptTube a e)
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
  have hprod : HasProd H total := actual_unmarked_hasProd K S P psi u ha ha1 he he1 s w z hv
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
        actual_rowCorrection_eq_markedProduct K S P psi ((Finset.univ \ J).image p) u
          ha he.le s w z hv]
      simp only [map_prod, A, B, H, M, slotMarkedScalar, slotSelectedScalar,
        Finset.prod_neg, Finset.prod_mul_distrib]
      ring
    _ = _ := NormForm.indexed_compensation_factorization
      (Finset.univ : Finset (Fin g.slots)) p hinj H M A B total hprod
        (fun i _ => hne i)

/-- Exact complete-slot decomposition of the actual finite correction.
Only local nonvanishing on the selected windows occurs in this algebraic
lemma; the next theorem supplies it uniformly from the actual tables. -/
theorem actualFullCorrection_eq_product (P : ProbeData K S) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z : ℝ)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1)
    (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (s w z : ℂ) (hv : (s, w, z) ∈ sweptTube a e)
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
  rw [actual_compensation_tuple_factorization K S P psi g T u Z ha ha1 he he1 s w z hv p hp'
    (fun i => hne i (p i) (hp' i)), Finset.prod_mul_distrib]
  ring

/-- The actual full-correction slots, with every analytic and local
nonvanishing premise derived. The single cutoff precedes all original
probes, characters, row ideals, bins, ray filters and contour points. -/
theorem exists_actualFullCorrection_product_cutoff (g : PrimeWindowGeometry)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (P : ProbeData K S) (psi : HeckeCharacter K) (T : Finset (HeckeCharacter K))
        (u : FrequencyRow K S) (a : ℝ), 51 / 100 ≤ a → a ≤ 1 →
      ∀ s w z : ℂ, (s, w, z) ∈ sweptTube a e →
        compensatedRowFullCorrection K S P psi (arithmeticHighEulerData K S P psi) g T u Z s w z =
          rowCorrection K S P psi (arithmeticHighEulerData K S P psi) ∅ u s w z *
            ∏ i : Fin g.slots, actualFullCorrectionSlot K S P psi g T u Z s w z i := by
  obtain ⟨Z0, hZ0, hnon⟩ := exists_window_unmarked_nonzero K S g he he1
  refine ⟨Z0, hZ0, ?_⟩
  intro Z hZ P psi T u a ha ha1 s w z hv
  exact actualFullCorrection_eq_product K S P psi g T u Z ha ha1 he he1 s w z hv
    (hnon Z hZ P psi T u a ha ha1 s w z hv)

end HighBinVerified.NormFormFullCorrection

#print axioms HighBinVerified.NormFormFullCorrection.exists_window_unmarked_nonzero
#print axioms HighBinVerified.NormFormFullCorrection.actualLocalCompensation_regular_main
#print axioms HighBinVerified.NormFormFullCorrection.actualRegularCompensationError_norm_le
#print axioms HighBinVerified.NormFormFullCorrection.actualLocalCompensation_regular_error_bound
#print axioms HighBinVerified.NormFormFullCorrection.actualLocalCompensation_ramified_bound
#print axioms HighBinVerified.NormFormFullCorrection.actualLocalCompensation_valuation_one_bound
#print axioms HighBinVerified.NormFormFullCorrection.exists_actual_local_compensation_bounds
#print axioms HighBinVerified.NormFormFullCorrection.actualFullCorrectionSlot_decomposition
#print axioms HighBinVerified.NormFormFullCorrection.exists_actualCompensationMainSlot_cap
#print axioms HighBinVerified.NormFormFullCorrection.exists_actualRegularErrorSlot_bound
#print axioms HighBinVerified.NormFormFullCorrection.exists_actualValuationOneSlot_bound
#print axioms HighBinVerified.NormFormFullCorrection.exists_actualRepeatedSlot_bound
#print axioms HighBinVerified.NormFormFullCorrection.exists_actualFullCorrectionSlot_bound
#print axioms HighBinVerified.NormFormFullCorrection.actual_compensation_tuple_factorization
#print axioms HighBinVerified.NormFormFullCorrection.exists_actualFullCorrection_product_cutoff
