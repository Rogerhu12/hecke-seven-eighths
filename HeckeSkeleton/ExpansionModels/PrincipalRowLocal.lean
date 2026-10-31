import HeckeSkeleton.ExpansionModels.SmallRowCorrectionSums
import Expansion.PhysicalEulerRegionFactorization

/-!
# Actual local factors on the principal residue rectangle

The real region is Re(s)>=7/8, Re(w)>=19/20, Re(z)>=33/200.
It includes the original principal residue and shifted rectangle.
The exact local tables supply every bound, without a high-bin tube
restriction.  No ramified row prime is removed from an actual row: the
later principal endpoint explicitly proves its support is empty.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Expansion.PrincipalRows

open NumberField IsDedekindDomain Set Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HighBinVerified.NormFormActual HighBinVerified.NormFormFullCorrection
open HeckeSkeleton.Expansion.SmallRows
open scoped Classical BigOperators Topology ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem principal_rectangle_mem_rowEulerRegion (s w z : ℂ)
    (hs : 7 / 8 ≤ s.re) (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    (s, w, z) ∈ rowEulerRegion := by
  change 1 / 2 < s.re ∧ 0 < w.re ∧ 0 < z.re ∧ 1 < s.re + w.re ∧
    5 / 6 < s.re + z.re ∧ 2 < s.re + w.re + 6 * z.re ∧
    1 < w.re + 6 * z.re ∧ 1 < s.re + 6 * z.re
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith⟩

/-- Literal regular compensation error; the same numerical margin works
over the full principal rectangle, uniformly in all imaginary coordinates. -/
theorem actualRegularCompensationError_principal_rectangle_bound (P : ProbeData K S)
    (psi : HeckeCharacter K) (u : FrequencyRow K S) (s w z : ℂ)
    (hs : 7 / 8 ≤ s.re) (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re)
    (p : ExteriorPrime K S)
    (hclose : ‖actualLocalUnmarked K S P psi u s w z p - 1‖ ≤ 1 / 2) :
    ‖actualRegularCompensationError K S P psi u s w z p‖ ≤
      48 / sweptTubeEulerMargin := by
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
  have hq : 2 ≤ q := exteriorPrime_norm_two_le K S p
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hV : ‖V‖ ≤ q ^ (-6 * z.re) := by
    dsimp only [V]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hq0]
    simp [Complex.mul_re]
  have hW : ‖W‖ ≤ q ^ (-w.re) := by
    dsimp only [W]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq0, Complex.neg_re]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (rowW_norm K S P u p) (Real.rpow_nonneg hq0.le (-w.re))
  have hD : ‖D‖ ≤ q ^ (-s.re) := by
    dsimp only [D]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq0, Complex.neg_re]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (rowD_norm K S P psi u p) (Real.rpow_nonneg hq0.le (-s.re))
  have hE : ‖E‖ ≤ q ^ (4 - 6 * s.re - 6 * z.re) := by
    dsimp only [E]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
    calc
      _ ≤ 1 * q ^ (4 - 6 * s).re * q ^ (-6 * z.re) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_right (rowE_norm K S P psi p) (Real.rpow_nonneg hq0.le _))
          hV (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [one_mul, ← Real.rpow_add hq0]
        congr 1
        norm_num [Complex.mul_re] <;> ring
  have hVone : ‖V‖ ≤ 1 := hV.trans (by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hq1
      (by linarith : -6 * z.re ≤ 0))
  have hWone : ‖W‖ ≤ 1 := hW.trans (by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hq1
      (by linarith : -w.re ≤ 0))
  have hDd : ‖D‖ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (hD.trans (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith))).trans
      (Real.rpow_le_rpow_of_nonpos (by norm_num) hq (by norm_num))
  have hEe : ‖E‖ ≤ 1 / 2 := by
    calc
      _ ≤ q ^ (-1 : ℝ) := hE.trans
        (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith))
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hq (by norm_num)
      _ = 1 / 2 := by norm_num
  have hgap : 0 < 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hDone : ‖D‖ ≤ 1 := hDd.trans (by linarith)
  have h1W : ‖1 - W‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) W
    rw [norm_one] at h
    linarith
  have h1V : ‖1 - V‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) V
    rw [norm_one] at h
    linarith
  have hA : ‖A‖ ≤ 3 := by
    have hterm := (norm_mul W (1 - V)).trans_le
      (mul_le_mul hWone h1V (norm_nonneg _) zero_le_one)
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
  have hdenLower : sweptTubeEulerMargin ≤ ‖den‖ := by
    have hEgap : 1 - (1 / 2 : ℝ) ≤ ‖1 - E‖ := by
      have h := norm_sub_norm_le (1 : ℂ) E
      rw [norm_one] at h
      linarith
    have hDgap : 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ ‖1 - D‖ := by
      have h := norm_sub_norm_le (1 : ℂ) D
      rw [norm_one] at h
      linarith
    dsimp only [den, sweptTubeEulerMargin]
    rw [norm_mul, mul_comm (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))]
    exact mul_le_mul hEgap hDgap hgap.le (norm_nonneg _)
  have hHlower : 1 / 2 ≤ ‖H‖ := HighBin.SelectedCompensation.norm_lower_of_close_one H hclose
  have hHupper : ‖H‖ ≤ 3 / 2 := by
    have h := norm_add_le (H - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at h
    linarith
  have hdenHupper : ‖den * H‖ ≤ 6 := by
    rw [norm_mul]
    exact (mul_le_mul hdenUpper hHupper (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hdenHlower : sweptTubeEulerMargin / 2 ≤ ‖den * H‖ := by
    rw [norm_mul]
    simpa only [div_eq_mul_inv] using
      mul_le_mul hdenLower hHlower (by norm_num : (0 : ℝ) ≤ 1 / 2) (norm_nonneg _)
  have hdenHpos : 0 < ‖den * H‖ :=
    (div_pos sweptTubeEulerMargin_pos (by norm_num)).trans_le hdenHlower
  have hME : ‖M * E‖ ≤ 1 := by
    have hcoeff : ‖conj (primeCoefficient K psi p.val) * rowE K S P psi p‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_conj]
      exact (mul_le_mul (norm_primeCoefficient_le_one K psi p.val)
        (rowE_norm K S P psi p) (norm_nonneg _) zero_le_one).trans_eq (by ring)
    have heq : M * E =
        (conj (primeCoefficient K psi p.val) * rowE K S P psi p) *
          ((q : ℂ) ^ s * (q : ℂ) ^ (4 - 6 * s) * (q : ℂ) ^ (-6 * z)) := by
      dsimp only [M, E, V]
      ring
    have hpower : ‖(q : ℂ) ^ s * (q : ℂ) ^ (4 - 6 * s) * (q : ℂ) ^ (-6 * z)‖ ≤ 1 := by
      simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
      have hexp : s.re + (4 - 6 * s).re + (-6 * z).re ≤ 0 := by
        norm_num [Complex.mul_re]
        linarith
      calc
        _ = q ^ (s.re + (4 - 6 * s).re + (-6 * z).re) := by
          rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
        _ ≤ q ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1 hexp
        _ = 1 := Real.rpow_zero q
    rw [heq, norm_mul]
    exact (mul_le_mul hcoeff hpower (norm_nonneg _) zero_le_one).trans_eq (by ring)
  have hqm : ‖(q : ℂ) - 1‖ ≤ q ^ (1 : ℝ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : 0 ≤ q - 1), Real.rpow_one]
    linarith
  have hWV : ‖((q : ℂ) - 1) * W * V‖ ≤ 1 := by
    rw [norm_mul, norm_mul]
    calc
      _ ≤ q ^ (1 : ℝ) * q ^ (-w.re) * q ^ (-6 * z.re) :=
        mul_le_mul (mul_le_mul hqm hW (norm_nonneg _) (Real.rpow_nonneg hq0.le _))
          hV (norm_nonneg _) (by positivity)
      _ = q ^ ((1 : ℝ) + -w.re + -6 * z.re) := by
        rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
      _ ≤ q ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
      _ = 1 := Real.rpow_zero q
  have hB : ‖B‖ ≤ 3 := (norm_add_le (1 - V) (((q : ℂ) - 1) * W * V)).trans
    (by linarith)
  have hrest : ‖den * H - B‖ ≤ 9 := (norm_sub_le (den * H) B).trans (by linarith)
  have hc : ‖c‖ ≤ 1 := by simpa only [c, Complex.norm_conj] using rowW_norm K S P u p
  have hinner : ‖M * E * A + c * (den * H - B)‖ ≤ 12 := by
    have hmea : ‖M * E * A‖ ≤ 3 := by
      rw [norm_mul]
      exact (mul_le_mul hME hA (norm_nonneg _) zero_le_one).trans_eq (by ring)
    have hcrest : ‖c * (den * H - B)‖ ≤ 9 := by
      rw [norm_mul]
      exact (mul_le_mul hc hrest (norm_nonneg _) zero_le_one).trans_eq (by ring)
    exact (norm_add_le _ _).trans (by linarith)
  have hnum : ‖(1 - W) * (M * E * A + c * (den * H - B))‖ ≤ 24 := by
    rw [norm_mul]
    exact (mul_le_mul h1W hinner (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  change ‖((1 - W) * (M * E * A + c * (den * H - B))) / (den * H)‖ ≤ _
  rw [norm_div]
  apply (div_le_iff₀ hdenHpos).mpr
  calc
    _ ≤ 24 := hnum
    _ = (48 / sweptTubeEulerMargin) * (sweptTubeEulerMargin / 2) := by
      field_simp [sweptTubeEulerMargin_pos.ne']
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdenHlower (by positivity)

/-- The actual leading cancellation gives one q^(Re z-1) factor. -/
theorem actualLocalCompensation_principal_rectangle_bound (P : ProbeData K S)
    (psi : HeckeCharacter K) (u : FrequencyRow K S) (s w z : ℂ)
    (hs : 7 / 8 ≤ s.re) (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re)
    (p : ExteriorPrime K S) (hp : p ∉ exteriorSupport K S u.ideal)
    (hpsi : UnramifiedAt K psi p.val)
    (hclose : ‖actualLocalUnmarked K S P psi u s w z p - 1‖ ≤ 1 / 2) :
    ‖actualLocalCompensation K S P psi u s w z p‖ ≤
      (1 + 48 / sweptTubeEulerMargin) * (p.val.asIdeal.absNorm : ℝ) ^ (z.re - 1) := by
  have hH : actualLocalUnmarked K S P psi u s w z p ≠ 0 := by
    intro heq
    rw [heq, zero_sub, norm_neg, norm_one] at hclose
    norm_num at hclose
  have hv := principal_rectangle_mem_rowEulerRegion s w z hs hw hz
  rw [_root_.Expansion.Project.actualLocalCompensation_regular_main_region
    K S P psi u s w z hv p hp hpsi hH, norm_mul]
  have hq0 : (0 : ℝ) < p.val.asIdeal.absNorm := by
    have := exteriorPrime_norm_two_le K S p
    linarith
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
  simp only [Complex.sub_re, Complex.one_re]
  have herror := actualRegularCompensationError_principal_rectangle_bound K S P psi u s w z hs hw hz p hclose
  have hsum := norm_add_le (-conj (primeCoefficient K (arithmeticRowCharacter K S P u) p.val))
    (actualRegularCompensationError K S P psi u s w z p)
  rw [norm_neg, Complex.norm_conj] at hsum
  exact (mul_le_mul_of_nonneg_left
    (hsum.trans (add_le_add (norm_primeCoefficient_le_one K _ p.val) herror))
    (Real.rpow_nonneg hq0.le _)).trans_eq (by ring)

end HeckeSkeleton.Expansion.PrincipalRows

#print axioms HeckeSkeleton.Expansion.PrincipalRows.principal_rectangle_mem_rowEulerRegion
#print axioms HeckeSkeleton.Expansion.PrincipalRows.actualRegularCompensationError_principal_rectangle_bound
#print axioms HeckeSkeleton.Expansion.PrincipalRows.actualLocalCompensation_principal_rectangle_bound
