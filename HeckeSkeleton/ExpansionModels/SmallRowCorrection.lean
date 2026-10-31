import HeckeSkeleton.ExpansionModels.SmallRowEulerBounds
import HeckeSkeleton.HighBinSupport.ActualNormFormFullCorrection
import HeckeGeneral.Analysis.FrequencyRowCounting

/-!
# The actual full correction on the two outer contours

The regular and ramified estimates below use the literal local factors of
the arithmetic Euler provider.  The scalar region Re(s)>=7/8, Re(w)>=1/2,
Re(z)>=17/50 contains both outer contours.  A single existing prime-window
cutoff supplies nonvanishing only for the selected local unmarked factors;
the unselected product and the full correction may vanish.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Expansion.SmallRows

open NumberField IsDedekindDomain Set Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HighBinVerified.NormFormActual HighBinVerified.NormFormFullCorrection
open scoped Classical BigOperators Topology ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem outer_contour_mem_sweptTube (s w z : ℂ)
    (hs : 7 / 8 ≤ s.re) (hw : 1 / 2 ≤ w.re) (hz : 17 / 50 ≤ z.re) :
    (s, w, z) ∈ sweptTube (3 / 4) (1 / 20000) := by
  change (3 / 4 : ℝ) + 15 * (1 / 20000) < s.re ∧
    1 - 3 / 4 - 7 * (1 / 20000) < w.re ∧ 17 / 50 - 1 / 20000 < z.re
  constructor
  · linarith
  constructor <;> linarith

/-- Only elementary coordinate bounds are needed for the outer regular
error.  The input local margin is supplied by the existing actual cutoff. -/
theorem actualRegularCompensationError_outer_bound (P : ProbeData K S)
    (psi : HeckeCharacter K) (u : FrequencyRow K S) (s w z : ℂ)
    (hs : 7 / 8 ≤ s.re) (hw : 1 / 2 ≤ w.re) (hz : 17 / 50 ≤ z.re)
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
  have hv := outer_contour_mem_sweptTube s w z hs hw hz
  obtain ⟨hV, hW, hD, hE⟩ := phase_coordinate_bounds hq
    (rowW K S P u p) (rowD K S P psi u p) (rowE K S P psi p) s w z
    (rowW_norm K S P u p) (rowD_norm K S P psi u p) (rowE_norm K S P psi p)
    hv.1.le hv.2.1.le hv.2.2.le
  change ‖V‖ ≤ q ^ (-(51 / 25 : ℝ) + 6 * (1 / 20000)) at hV
  change ‖W‖ ≤ q ^ ((3 / 4 : ℝ) - 1 + 7 * (1 / 20000)) at hW
  change ‖D‖ ≤ q ^ (-(3 / 4 : ℝ) - 15 * (1 / 20000)) at hD
  change ‖E‖ ≤ q ^ ((49 / 25 : ℝ) - 6 * (3 / 4) - 84 * (1 / 20000)) at hE
  have hVone : ‖V‖ ≤ 1 := hV.trans (by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hq1
      (by norm_num : -(51 / 25 : ℝ) + 6 * (1 / 20000) ≤ 0))
  have hWone : ‖W‖ ≤ 1 := hW.trans (by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hq1
      (by norm_num : (3 / 4 : ℝ) - 1 + 7 * (1 / 20000) ≤ 0))
  have hDd : ‖D‖ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (hD.trans (Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num))).trans
      (Real.rpow_le_rpow_of_nonpos (by norm_num) hq (by norm_num))
  have hEe : ‖E‖ ≤ 1 / 2 := by
    calc
      _ ≤ q ^ (-1 : ℝ) := hE.trans
        (Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num))
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
      _ ≤ q ^ (1 : ℝ) * q ^ ((3 / 4 : ℝ) - 1 + 7 * (1 / 20000)) *
          q ^ (-(51 / 25 : ℝ) + 6 * (1 / 20000)) :=
        mul_le_mul (mul_le_mul hqm hW (norm_nonneg _) (Real.rpow_nonneg hq0.le _))
          hV (norm_nonneg _) (by positivity)
      _ = q ^ ((1 : ℝ) + (3 / 4 - 1 + 7 * (1 / 20000)) +
          (-(51 / 25) + 6 * (1 / 20000))) := by
        rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
      _ ≤ q ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
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

/-- Quotient-free regular compensation after the genuine leading-term
cancellation, with every local phase supplied by the actual provider. -/
theorem actualLocalCompensation_regular_outer_bound (P : ProbeData K S)
    (psi : HeckeCharacter K) (u : FrequencyRow K S) (s w z : ℂ)
    (hs : 7 / 8 ≤ s.re) (hw : 1 / 2 ≤ w.re) (hz : 17 / 50 ≤ z.re)
    (p : ExteriorPrime K S) (hp : p ∉ exteriorSupport K S u.ideal)
    (hpsi : UnramifiedAt K psi p.val)
    (hclose : ‖actualLocalUnmarked K S P psi u s w z p - 1‖ ≤ 1 / 2) :
    ‖actualLocalCompensation K S P psi u s w z p‖ ≤
      (1 + 48 / sweptTubeEulerMargin) * (p.val.asIdeal.absNorm : ℝ) ^ (z.re - 1) := by
  have hH : actualLocalUnmarked K S P psi u s w z p ≠ 0 := by
    intro heq
    rw [heq, zero_sub, norm_neg, norm_one] at hclose
    norm_num at hclose
  have hv := outer_contour_mem_sweptTube s w z hs hw hz
  rw [actualLocalCompensation_regular_main K S P psi u (by norm_num : (51 / 100 : ℝ) ≤ 3 / 4)
    (by norm_num : (0 : ℝ) ≤ 1 / 20000) s w z hv p hp hpsi hH, norm_mul]
  have hq0 : (0 : ℝ) < p.val.asIdeal.absNorm := by
    have := exteriorPrime_norm_two_le K S p
    linarith
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
  simp only [Complex.sub_re, Complex.one_re]
  have herror := actualRegularCompensationError_outer_bound K S P psi u s w z hs hw hz p hclose
  have hsum := norm_add_le (-conj (primeCoefficient K (arithmeticRowCharacter K S P u) p.val))
    (actualRegularCompensationError K S P psi u s w z p)
  rw [norm_neg, Complex.norm_conj] at hsum
  exact (mul_le_mul_of_nonneg_left
    (hsum.trans (add_le_add (norm_primeCoefficient_le_one K _ p.val) herror))
    (Real.rpow_nonneg hq0.le _)).trans_eq (by ring)

/-- Every ramified selected factor obeys the outer square-root bound,
including valuation one and all repeated-prime valuations. -/
theorem actualLocalCompensation_ramified_outer_bound (P : ProbeData K S)
    (psi : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
    (u : FrequencyRow K S) (s w z : ℂ)
    (hs : 7 / 8 ≤ s.re) (hw : 1 / 2 ≤ w.re) (hz : 17 / 50 ≤ z.re)
    (p : ExteriorPrime K S) (hp : p ∈ exteriorSupport K S u.ideal)
    (hclose : ‖actualLocalUnmarked K S P psi u s w z p - 1‖ ≤ 1 / 2) :
    ‖actualLocalCompensation K S P psi u s w z p‖ ≤
      19 * (p.val.asIdeal.absNorm : ℝ) ^ (z.re - 1 / 2) := by
  let q : ℝ := p.val.asIdeal.absNorm
  let ph := rowPhaseData K S P psi u p
  let H := ramifiedTableValue ph q s w z (rowIndex K S u p)
  have hq : 2 ≤ q := exteriorPrime_norm_two_le K S p
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hv := outer_contour_mem_sweptTube s w z hs hw hz
  have hHeq : actualLocalUnmarked K S P psi u s w z p = H := by
    unfold actualLocalUnmarked
    rw [localFactor_eq_explicit K S P psi ∅ u (by norm_num : (51 / 100 : ℝ) ≤ 3 / 4)
      (by norm_num : (0 : ℝ) ≤ 1 / 20000) p (s, w, z) hv]
    simp only [explicitLocalEuler, if_pos hp, Finset.notMem_empty, if_false, sub_zero]
    rfl
  have hHclose : ‖H - 1‖ ≤ 1 / 2 := by rwa [hHeq] at hclose
  have hH : H ≠ 0 := by
    intro heq
    rw [heq, zero_sub, norm_neg, norm_one] at hHclose
    norm_num at hHclose
  rw [actualLocalCompensation_ramified_eq K S P psi hcal u
    (by norm_num : (51 / 100 : ℝ) ≤ 3 / 4) (by norm_num : (0 : ℝ) ≤ 1 / 20000)
    s w z hv p hp hH, norm_mul]
  have hweighted := ramified_small_weighted_error ph hq s w z hs hw hz (rowIndex K S u p)
  have hW : ‖(q : ℂ) ^ (-w)‖ ≤ q ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hq0, Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hnormalized := HighBin.SelectedCompensation.normalizedCompensation_norm_le_weighted
    ph.eta ((q : ℂ) ^ s) ((q : ℂ) ^ (-w)) H (9 * q ^ (1 / 2 : ℝ))
    ph.eta_bound hHclose hweighted
  have hbound : ‖HighBin.SelectedCompensation.normalizedCompensation
      ph.eta ((q : ℂ) ^ s) ((q : ℂ) ^ (-w)) H‖ ≤ 19 * q ^ (1 / 2 : ℝ) := by linarith
  have hpow : ‖(p.val.asIdeal.absNorm : ℂ) ^ (z - 1)‖ = q ^ (z.re - 1) := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
    simp only [Complex.sub_re, Complex.one_re]
  rw [hpow]
  calc
    _ ≤ q ^ (z.re - 1) * (19 * q ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (by simpa only [q, ph, H, Complex.ofReal_natCast] using hbound)
        (Real.rpow_nonneg hq0.le _)
    _ = 19 * q ^ (z.re - 1 / 2) := by
      rw [mul_left_comm, ← Real.rpow_add hq0]
      congr 1
      congr 1
      ring

/-- All local margins are discharged for the actual finite windows.  The
single cutoff precedes the probe, target, row, height, and prime choice. -/
theorem exists_actual_outer_local_bounds (g : PrimeWindowGeometry) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (P : ProbeData K S) (psi : HeckeCharacter K),
      ThetaCalibrationInput K S P.arithmetic P.Lambda P.G →
      (∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val) →
      ∀ (T : Finset (HeckeCharacter K)) (u : FrequencyRow K S) (s w z : ℂ),
      7 / 8 ≤ s.re → 1 / 2 ≤ w.re → 17 / 50 ≤ z.re →
      ∀ i : Fin g.slots, ∀ p ∈ primeWindow K S g T Z i,
        (p ∉ exteriorSupport K S u.ideal →
          ‖actualLocalCompensation K S P psi u s w z p‖ ≤
            (1 + 48 / sweptTubeEulerMargin) *
              (p.val.asIdeal.absNorm : ℝ) ^ (z.re - 1)) ∧
        (p ∈ exteriorSupport K S u.ideal →
          ‖actualLocalCompensation K S P psi u s w z p‖ ≤
            19 * (p.val.asIdeal.absNorm : ℝ) ^ (z.re - 1 / 2)) := by
  obtain ⟨Z0, hZ0, hcut⟩ := exists_window_local_cutoff K S g
    (e := 1 / 20000) (by norm_num) (by norm_num)
  refine ⟨Z0, hZ0, ?_⟩
  intro Z hZ P psi hcal hpsi T u s w z hs hw hz i p hp
  have hv := outer_contour_mem_sweptTube s w z hs hw hz
  have hclose := (hcut Z hZ P psi T u (3 / 4) (by norm_num) (by norm_num)
    s w z hv i p hp).1
  exact ⟨fun hrow => actualLocalCompensation_regular_outer_bound
    K S P psi u s w z hs hw hz p hrow (hpsi p) hclose,
    fun hrow => actualLocalCompensation_ramified_outer_bound
      K S P psi hcal u s w z hs hw hz p hrow hclose⟩

end HeckeSkeleton.Expansion.SmallRows

#print axioms HeckeSkeleton.Expansion.SmallRows.actualRegularCompensationError_outer_bound
#print axioms HeckeSkeleton.Expansion.SmallRows.actualLocalCompensation_regular_outer_bound
#print axioms HeckeSkeleton.Expansion.SmallRows.actualLocalCompensation_ramified_outer_bound
#print axioms HeckeSkeleton.Expansion.SmallRows.exists_actual_outer_local_bounds
