import HeckeSkeleton.ExpansionModels.LargeRowCorrection

/-!
# Uniform actual full-correction bounds on positive outer strips

The real z coordinate may vary between 17/50 and a fixed upper endpoint.
Monotonicity at each original prime controls its exact exponent by that
endpoint. The actual complete slot, including all ramified valuations and
all subset corrections, therefore has one bound throughout the swept
strip. Constants and the common cutoff precede every point, height and row.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HighBinVerified.NormFormActual HighBinVerified.NormFormFullCorrection
open HeckeSkeleton.Expansion.SmallRows
open scoped Classical BigOperators Topology ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The complete actual slot on the whole fixed outer strip. The lower
endpoint remains 17/50; only the upper endpoint is required to exceed one. -/
theorem exists_actual_outer_fullCorrectionSlot_strip_bound (g : PrimeWindowGeometry)
    {sigma eta : ℝ} (hsigma : 1 ≤ sigma) (heta : 0 < eta) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (P : ProbeData K S) (psi : HeckeCharacter K),
      ThetaCalibrationInput K S P.arithmetic P.Lambda P.G →
      (∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val) →
      ∀ (T : Finset (HeckeCharacter K)) (u : FrequencyRow K S) (s w z : ℂ),
      7 / 8 ≤ s.re → 1 / 2 ≤ w.re → 17 / 50 ≤ z.re → z.re ≤ sigma → ∀ i : Fin g.slots,
        ‖actualFullCorrectionSlot K S P psi g T u Z s w z i‖ ≤
          C * frequencyRowNorm K S u ^ eta * (primeScale g Z) ^ sigma := by
  obtain ⟨Z1, hZ1, hlocal⟩ := exists_actual_outer_local_bounds K S g
  obtain ⟨Z2, hZ2, hscale⟩ := HighBinVerified.NormFormPrimeCap.exists_primeScale_cutoff g
  obtain ⟨M, hM, hprofile⟩ := exists_primeWindow_profile_norm_bound g
  obtain ⟨A, hA, hcount⟩ := exists_primeWindow_linear_count K S
  let Creg : ℝ := (1 + 48 / sweptTubeEulerMargin) * (2 : ℝ) ^ (sigma - 1)
  let Cram : ℝ := 19 * (2 : ℝ) ^ (sigma - 1 / 2)
  let D : ℝ := repeatedTupleConstant 1 eta
  have hCreg : 0 < Creg := by dsimp [Creg]; have := sweptTubeEulerMargin_pos; positivity
  have hCram : 0 < Cram := by dsimp [Cram]; positivity
  have hD : 0 < D := repeatedTupleConstant_pos 1 heta
  let C : ℝ := A * M * Creg + D * M * Cram
  refine ⟨C, max Z1 Z2, by dsimp [C]; positivity,
    hZ1.trans (le_max_left _ _), ?_⟩
  intro Z hZ P psi hcal hpsi T u s w z hs hw hzlo hzhi i
  have hZZ1 : Z1 ≤ Z := (le_max_left _ _).trans hZ
  have hZZ2 : Z2 ≤ Z := (le_max_right _ _).trans hZ
  have hX : 1 ≤ primeScale g Z := (by norm_num : (1 : ℝ) ≤ 2).trans (hscale Z hZZ2)
  have hX0 : 0 < primeScale g Z := zero_lt_one.trans_le hX
  have hN : 1 ≤ frequencyRowNorm K S u := one_le_idealNorm K u.ideal.val
  have hNeta : 1 ≤ frequencyRowNorm K S u ^ eta := Real.one_le_rpow hN heta.le
  let F := primeWindow K S g T Z i
  let R := F.filter (fun p => p ∈ exteriorSupport K S u.ideal)
  let reg : ℝ := M * Creg * (primeScale g Z) ^ (sigma - 1)
  let ram : ℝ := M * Cram * (primeScale g Z) ^ (sigma - 1 / 2)
  have hreg : 0 ≤ reg := by dsimp [reg]; positivity
  have hram : 0 ≤ ram := by dsimp [ram]; positivity
  have hterm (p : ExteriorPrime K S) (hp : p ∈ F) :
      ‖windowWeight K S g Z i p * actualLocalCompensation K S P psi u s w z p‖ ≤
        reg + if p ∈ exteriorSupport K S u.ideal then ram else 0 := by
    have hpX := (actual_primeWindow_norm_range K S g T Z i p hp).2.2.le
    obtain ⟨hregular, hramified⟩ := hlocal Z hZZ1 P psi hcal hpsi T u s w z
      hs hw hzlo i p hp
    rw [norm_mul]
    by_cases hrow : p ∈ exteriorSupport K S u.ideal
    · rw [if_pos hrow]
      have hpow : (p.val.asIdeal.absNorm : ℝ) ^ (sigma - 1 / 2) ≤
          (2 : ℝ) ^ (sigma - 1 / 2) * (primeScale g Z) ^ (sigma - 1 / 2) := by
        calc
          _ ≤ (2 * primeScale g Z) ^ (sigma - 1 / 2) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hpX (by linarith)
          _ = _ := Real.mul_rpow (by norm_num) hX0.le
      have hb : ‖actualLocalCompensation K S P psi u s w z p‖ ≤
          Cram * (primeScale g Z) ^ (sigma - 1 / 2) := by
        apply (hramified hrow).trans
        have hmono : (p.val.asIdeal.absNorm : ℝ) ^ (z.re - 1 / 2) ≤
            (p.val.asIdeal.absNorm : ℝ) ^ (sigma - 1 / 2) :=
          Real.rpow_le_rpow_of_exponent_le
            ((by norm_num : (1 : ℝ) ≤ 2).trans (exteriorPrime_norm_two_le K S p))
            (by linarith)
        exact (mul_le_mul_of_nonneg_left (hmono.trans hpow) (by norm_num)).trans_eq
          (by dsimp [Cram]; ring)
      have hh : ‖windowWeight K S g Z i p‖ *
          ‖actualLocalCompensation K S P psi u s w z p‖ ≤ ram := by
        exact (mul_le_mul (hprofile i _) hb (norm_nonneg _) hM.le).trans_eq (by dsimp [ram]; ring)
      exact hh.trans (le_add_of_nonneg_left hreg)
    · rw [if_neg hrow, add_zero]
      have hpow : (p.val.asIdeal.absNorm : ℝ) ^ (sigma - 1) ≤
          (2 : ℝ) ^ (sigma - 1) * (primeScale g Z) ^ (sigma - 1) := by
        calc
          _ ≤ (2 * primeScale g Z) ^ (sigma - 1) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hpX (by linarith)
          _ = _ := Real.mul_rpow (by norm_num) hX0.le
      have hb : ‖actualLocalCompensation K S P psi u s w z p‖ ≤
          Creg * (primeScale g Z) ^ (sigma - 1) := by
        apply (hregular hrow).trans
        have hmono : (p.val.asIdeal.absNorm : ℝ) ^ (z.re - 1) ≤
            (p.val.asIdeal.absNorm : ℝ) ^ (sigma - 1) :=
          Real.rpow_le_rpow_of_exponent_le
            ((by norm_num : (1 : ℝ) ≤ 2).trans (exteriorPrime_norm_two_le K S p))
            (by linarith)
        have hpos : 0 ≤ 1 + 48 / sweptTubeEulerMargin := by
          have := sweptTubeEulerMargin_pos
          positivity
        exact (mul_le_mul_of_nonneg_left (hmono.trans hpow) hpos).trans_eq (by dsimp [Creg]; ring)
      exact (mul_le_mul (hprofile i _) hb (norm_nonneg _) hM.le).trans_eq (by dsimp [reg]; ring)
  have hcard : (F.card : ℝ) ≤ A * primeScale g Z := hcount g T Z i hX
  have hRcard : (R.card : ℝ) ≤ D * frequencyRowNorm K S u ^ eta :=
    ramified_primeWindow_card_subpower K S g T u Z i heta
  have hsumif : (∑ p ∈ F, if p ∈ exteriorSupport K S u.ideal then ram else 0) =
      (R.card : ℝ) * ram := by
    change _ = ((F.filter (fun p => p ∈ exteriorSupport K S u.ideal)).card : ℝ) * ram
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hmass : primeScale g Z * (primeScale g Z) ^ (sigma - 1) = (primeScale g Z) ^ sigma := by
    calc
      _ = (primeScale g Z) ^ (1 : ℝ) * (primeScale g Z) ^ (sigma - 1) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hX0]; congr 1; ring
  have hsmall : (primeScale g Z) ^ (sigma - 1 / 2) ≤ (primeScale g Z) ^ sigma :=
    Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  change ‖∑ p ∈ F, windowWeight K S g Z i p * actualLocalCompensation K S P psi u s w z p‖ ≤ _
  calc
    _ ≤ ∑ p ∈ F, ‖windowWeight K S g Z i p * actualLocalCompensation K S P psi u s w z p‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ F, (reg + if p ∈ exteriorSupport K S u.ideal then ram else 0) :=
      Finset.sum_le_sum hterm
    _ = (F.card : ℝ) * reg + (R.card : ℝ) * ram := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hsumif]
    _ ≤ (A * primeScale g Z) * reg + (D * frequencyRowNorm K S u ^ eta) * ram :=
      add_le_add (mul_le_mul_of_nonneg_right hcard hreg) (mul_le_mul_of_nonneg_right hRcard hram)
    _ = (A * M * Creg) * (primeScale g Z) ^ sigma +
        (D * M * Cram) * frequencyRowNorm K S u ^ eta * (primeScale g Z) ^ (sigma - 1 / 2) := by
      dsimp only [reg, ram]
      calc
        _ = (A * M * Creg) * (primeScale g Z * (primeScale g Z) ^ (sigma - 1)) +
            (D * M * Cram) * frequencyRowNorm K S u ^ eta *
              (primeScale g Z) ^ (sigma - 1 / 2) := by ring
        _ = _ := by rw [hmass]
    _ ≤ (A * M * Creg) * frequencyRowNorm K S u ^ eta * (primeScale g Z) ^ sigma +
        (D * M * Cram) * frequencyRowNorm K S u ^ eta * (primeScale g Z) ^ sigma := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right (by positivity) hNeta) (Real.rpow_nonneg hX0.le _)
      · exact mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = C * frequencyRowNorm K S u ^ eta * (primeScale g Z) ^ sigma := by dsimp [C]; ring

/-- The full actual correction has the common upper-endpoint power sigma/6
throughout the entire outer strip, uniformly in all arithmetic rows. -/
theorem exists_actual_outer_fullCorrection_strip_bound (g : PrimeWindowGeometry)
    {sigma eta : ℝ} (hsigma : 1 ≤ sigma) (heta : 0 < eta) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (P : ProbeData K S) (psi : HeckeCharacter K),
      ThetaCalibrationInput K S P.arithmetic P.Lambda P.G →
      (∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val) →
      ∀ (T : Finset (HeckeCharacter K)) (u : FrequencyRow K S) (s w z : ℂ),
      7 / 8 ≤ s.re → 1 / 2 ≤ w.re → 17 / 50 ≤ z.re → z.re ≤ sigma →
        ‖compensatedRowFullCorrection K S P psi (arithmeticHighEulerData K S P psi)
          g T u Z s w z‖ ≤ C * frequencyRowNorm K S u ^ eta * Z ^ (sigma / 6) := by
  let delta : ℝ := eta / ((g.slots : ℝ) + 1)
  have hJ : 0 < (g.slots : ℝ) := by exact_mod_cast g.slots_pos
  have hdelta : 0 < delta := div_pos heta (by positivity)
  obtain ⟨Cs, Zs, hCs, hZs, hslot⟩ := exists_actual_outer_fullCorrectionSlot_strip_bound K S g hsigma hdelta
  obtain ⟨Ce, hCe, heuler⟩ := exists_uniform_rowCorrection_subpower K S
    (e := 1 / 20000) (by norm_num) (by norm_num) hdelta
  obtain ⟨Zf, hZf, hfactor⟩ := exists_actualFullCorrection_product_cutoff K S g
    (e := 1 / 20000) (by norm_num) (by norm_num)
  refine ⟨Ce * Cs ^ g.slots, max Zs Zf, by positivity,
    hZs.trans (le_max_left _ _), ?_⟩
  intro Z hZ P psi hcal hpsi T u s w z hs hw hzlo hzhi
  have hZZs : Zs ≤ Z := (le_max_left _ _).trans hZ
  have hZZf : Zf ≤ Z := (le_max_right _ _).trans hZ
  have hZ1 : 1 ≤ Z := hZs.trans hZZs
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ1
  have hX0 : 0 < primeScale g Z := Real.rpow_pos_of_pos hZ0 _
  have hN0 : 0 < frequencyRowNorm K S u := idealNorm_pos K u.ideal.val
  have hv := outer_contour_mem_sweptTube s w z hs hw hzlo
  rw [hfactor Z hZZf P psi T u (3 / 4) (by norm_num) (by norm_num) s w z hv,
    norm_mul, norm_prod]
  have he : ‖rowCorrection K S P psi (arithmeticHighEulerData K S P psi) ∅ u s w z‖ ≤
      Ce * frequencyRowNorm K S u ^ delta := by
    simpa only [Finset.card_empty, pow_zero, mul_one] using
      heuler P psi ∅ u (3 / 4) (by norm_num) (by norm_num) (s, w, z) hv
  have hp : (∏ i : Fin g.slots, ‖actualFullCorrectionSlot K S P psi g T u Z s w z i‖) ≤
      (Cs * frequencyRowNorm K S u ^ delta * (primeScale g Z) ^ sigma) ^ g.slots := by
    calc
      _ ≤ ∏ _i : Fin g.slots, Cs * frequencyRowNorm K S u ^ delta * (primeScale g Z) ^ sigma :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun i _ => hslot Z hZZs P psi hcal hpsi T u s w z hs hw hzlo hzhi i)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hNpow : (frequencyRowNorm K S u ^ delta) ^ g.slots =
      frequencyRowNorm K S u ^ (delta * g.slots) :=
    (Real.rpow_mul_natCast hN0.le delta g.slots).symm
  have hXpow : ((primeScale g Z) ^ sigma) ^ g.slots = Z ^ (sigma / 6) := by
    rw [← Real.rpow_mul_natCast hX0.le]
    unfold primeScale
    rw [← Real.rpow_mul hZ0.le]
    congr 1
    field_simp [hJ.ne']
    <;> ring
  have hdelta_total : delta + delta * (g.slots : ℝ) = eta := by
    dsimp only [delta]
    field_simp [show (g.slots : ℝ) + 1 ≠ 0 by positivity]
    <;> ring
  calc
    _ ≤ (Ce * frequencyRowNorm K S u ^ delta) *
        (Cs * frequencyRowNorm K S u ^ delta * (primeScale g Z) ^ sigma) ^ g.slots :=
      mul_le_mul he hp (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
    _ = (Ce * Cs ^ g.slots) * frequencyRowNorm K S u ^ (delta + delta * g.slots) * Z ^ (sigma / 6) := by
      rw [mul_pow, mul_pow, hNpow, hXpow, Real.rpow_add hN0]
      ring
    _ = _ := by rw [hdelta_total]

end Expansion.Project

#print axioms Expansion.Project.exists_actual_outer_fullCorrectionSlot_strip_bound
#print axioms Expansion.Project.exists_actual_outer_fullCorrection_strip_bound
