import HeckeSkeleton.ExpansionModels.SmallRowCorrection

/-!
# Actual finite-window sums of the small-row correction

The regular primes are counted through genuine nonzero ideals.  Every row
prime, with any of the five valuations, is counted through the support of
the original ideal.  These are proved counts, not fields of an input.
The full correction is the same finite-window/subset expression used by
the physical kernel, identified by the actual Euler provider.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Expansion.SmallRows

open NumberField IsDedekindDomain Set Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HighBinVerified.NormFormActual HighBinVerified.NormFormFullCorrection
open scoped Classical BigOperators Topology ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The constant depends only on the field.  Filtering by ray characters
or by the particular smooth support can only reduce the true prime set. -/
theorem exists_primeWindow_linear_count :
    ∃ A : ℝ, 0 < A ∧ ∀ (g : PrimeWindowGeometry)
      (T : Finset (HeckeCharacter K)) (Z : ℝ) (i : Fin g.slots),
      1 ≤ primeScale g Z →
        ((primeWindow K S g T Z i).card : ℝ) ≤ A * primeScale g Z := by
  obtain ⟨C, hC, hcount⟩ := dyadicIdealSupport_linear_count K
  refine ⟨2 * C, by positivity, ?_⟩
  intro g T Z i hX
  have hX0 : 0 < primeScale g Z := zero_lt_one.trans_le hX
  let f : ExteriorPrime K S → NonzeroIdeal K := fun p => primeNonzeroIdeal K p.val
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.val_injective
    exact primeNonzeroIdeal_injective K hpq
  have hsub : (primeWindow K S g T Z i).image f ⊆ dyadicIdealSupport K (primeScale g Z) := by
    intro I hI
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI
    apply (mem_dyadicIdealSupport_iff K hX0.le (f p)).mpr
    exact (actual_primeWindow_norm_range K S g T Z i p hp).2.2.le
  have hcard : (primeWindow K S g T Z i).card ≤ (dyadicIdealSupport K (primeScale g Z)).card := by
    rw [← Finset.card_image_of_injective (primeWindow K S g T Z i) hf]
    exact Finset.card_le_card hsub
  have hcount' := hcount (2 * primeScale g Z) (by linarith)
  have hhalf : 2 * primeScale g Z / 2 = primeScale g Z := by ring
  exact (Nat.cast_le.mpr hcard).trans (by simpa only [hhalf, mul_assoc, mul_left_comm C 2] using hcount')

/-- The original ideal supplies the count of all ramified primes in a
window; no sector and no repeated valuation is discarded. -/
theorem ramified_primeWindow_card_subpower (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (u : FrequencyRow K S) (Z : ℝ)
    (i : Fin g.slots) {eta : ℝ} (heta : 0 < eta) :
    (((primeWindow K S g T Z i).filter
      (fun p => p ∈ exteriorSupport K S u.ideal)).card : ℝ) ≤
        repeatedTupleConstant 1 eta * frequencyRowNorm K S u ^ eta := by
  let F := (primeWindow K S g T Z i).filter (fun p => p ∈ exteriorSupport K S u.ideal)
  have hsub : F.image Subtype.val ⊆ (primeExponents u.ideal.val).support := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    apply (mem_idealPrimeSupport_iff K u.ideal.val q.val).mpr
    exact (mem_exteriorSupport_iff K S u.ideal q).mp (Finset.mem_filter.mp hq).2
  have hcard : (F.card : ℝ) ≤ ((primeExponents u.ideal.val).support.card : ℝ) := by
    apply Nat.cast_le.mpr
    rw [← Finset.card_image_of_injective F Subtype.val_injective]
    exact Finset.card_le_card hsub
  have hcount := actual_support_tuple_count_subpower K u.ideal.val 1 heta
  simp only [pow_one] at hcount
  exact hcard.trans ((le_add_of_nonneg_right zero_le_one).trans hcount)

/-- The complete literal slot on the small-row contour.  Every local
estimate and both prime counts are derived before this conclusion. -/
theorem exists_actual_small_fullCorrectionSlot_bound (g : PrimeWindowGeometry)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (P : ProbeData K S) (psi : HeckeCharacter K),
      ThetaCalibrationInput K S P.arithmetic P.Lambda P.G →
      (∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val) →
      ∀ (T : Finset (HeckeCharacter K)) (u : FrequencyRow K S) (s w z : ℂ),
      7 / 8 ≤ s.re → 1 / 2 ≤ w.re → z.re = 17 / 50 →
      ∀ i : Fin g.slots,
        ‖actualFullCorrectionSlot K S P psi g T u Z s w z i‖ ≤
          C * frequencyRowNorm K S u ^ eta * (primeScale g Z) ^ (17 / 50 : ℝ) := by
  obtain ⟨Z1, hZ1, hlocal⟩ := exists_actual_outer_local_bounds K S g
  obtain ⟨Z2, hZ2, hscale⟩ := HighBinVerified.NormFormPrimeCap.exists_primeScale_cutoff g
  obtain ⟨M, hM, hprofile⟩ := exists_primeWindow_profile_norm_bound g
  obtain ⟨A, hA, hcount⟩ := exists_primeWindow_linear_count K S
  let Creg : ℝ := 1 + 48 / sweptTubeEulerMargin
  let Cram : ℝ := repeatedTupleConstant 1 eta
  have hCreg : 0 < Creg := by dsimp [Creg]; have := sweptTubeEulerMargin_pos; positivity
  have hCram : 0 < Cram := repeatedTupleConstant_pos 1 heta
  let C : ℝ := A * M * Creg + Cram * M * 19
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, max Z1 Z2, hC, hZ1.trans (le_max_left _ _), ?_⟩
  intro Z hZ P psi hcal hpsi T u s w z hs hw hz i
  have hZZ1 : Z1 ≤ Z := (le_max_left _ _).trans hZ
  have hZZ2 : Z2 ≤ Z := (le_max_right _ _).trans hZ
  have hX : 1 ≤ primeScale g Z := (by norm_num : (1 : ℝ) ≤ 2).trans (hscale Z hZZ2)
  have hX0 : 0 < primeScale g Z := zero_lt_one.trans_le hX
  have hN : 1 ≤ frequencyRowNorm K S u := one_le_idealNorm K u.ideal.val
  have hNeta : 1 ≤ frequencyRowNorm K S u ^ eta := Real.one_le_rpow hN heta.le
  let F := primeWindow K S g T Z i
  let R := F.filter (fun p => p ∈ exteriorSupport K S u.ideal)
  let reg : ℝ := M * Creg * (primeScale g Z) ^ (-(33 / 50 : ℝ))
  let ram : ℝ := M * 19 * (primeScale g Z) ^ (-(4 / 25 : ℝ))
  have hreg : 0 ≤ reg := by dsimp [reg]; positivity
  have hram : 0 ≤ ram := by dsimp [ram]; positivity
  have hterm (p : ExteriorPrime K S) (hp : p ∈ F) :
      ‖windowWeight K S g Z i p * actualLocalCompensation K S P psi u s w z p‖ ≤
        reg + if p ∈ exteriorSupport K S u.ideal then ram else 0 := by
    have hpX := (actual_primeWindow_norm_range K S g T Z i p hp).2.1.le
    obtain ⟨hregular, hramified⟩ := hlocal Z hZZ1 P psi hcal hpsi T u s w z hs hw hz.ge i p hp
    rw [norm_mul]
    by_cases hrow : p ∈ exteriorSupport K S u.ideal
    · rw [if_pos hrow]
      have hb : ‖actualLocalCompensation K S P psi u s w z p‖ ≤
          19 * (p.val.asIdeal.absNorm : ℝ) ^ (-(4 / 25 : ℝ)) := by
        simpa only [hz, show (17 / 50 : ℝ) - 1 / 2 = -(4 / 25) by norm_num] using hramified hrow
      have hpow := Real.rpow_le_rpow_of_nonpos hX0 hpX (by norm_num : -(4 / 25 : ℝ) ≤ 0)
      have hh : ‖windowWeight K S g Z i p‖ *
          ‖actualLocalCompensation K S P psi u s w z p‖ ≤ ram := by
        calc
          _ ≤ M * (19 * (p.val.asIdeal.absNorm : ℝ) ^ (-(4 / 25 : ℝ))) :=
            mul_le_mul (hprofile i _) hb (norm_nonneg _) hM.le
          _ ≤ M * (19 * (primeScale g Z) ^ (-(4 / 25 : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by norm_num)) hM.le
          _ = ram := by dsimp [ram]; ring
      exact hh.trans (le_add_of_nonneg_left hreg)
    · rw [if_neg hrow, add_zero]
      have hb : ‖actualLocalCompensation K S P psi u s w z p‖ ≤
          Creg * (p.val.asIdeal.absNorm : ℝ) ^ (-(33 / 50 : ℝ)) := by
        simpa only [Creg, hz, show (17 / 50 : ℝ) - 1 = -(33 / 50) by norm_num] using hregular hrow
      have hpow := Real.rpow_le_rpow_of_nonpos hX0 hpX (by norm_num : -(33 / 50 : ℝ) ≤ 0)
      calc
        _ ≤ M * (Creg * (p.val.asIdeal.absNorm : ℝ) ^ (-(33 / 50 : ℝ))) :=
          mul_le_mul (hprofile i _) hb (norm_nonneg _) hM.le
        _ ≤ M * (Creg * (primeScale g Z) ^ (-(33 / 50 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hCreg.le) hM.le
        _ = reg := by dsimp [reg]; ring
  have hcard : (F.card : ℝ) ≤ A * primeScale g Z := hcount g T Z i hX
  have hRcard : (R.card : ℝ) ≤ Cram * frequencyRowNorm K S u ^ eta :=
    ramified_primeWindow_card_subpower K S g T u Z i heta
  have hsumif : (∑ p ∈ F, if p ∈ exteriorSupport K S u.ideal then ram else 0) =
      (R.card : ℝ) * ram := by
    change _ = ((F.filter (fun p => p ∈ exteriorSupport K S u.ideal)).card : ℝ) * ram
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hmass : primeScale g Z * (primeScale g Z) ^ (-(33 / 50 : ℝ)) =
      (primeScale g Z) ^ (17 / 50 : ℝ) := by
    calc
      _ = (primeScale g Z) ^ (1 : ℝ) * (primeScale g Z) ^ (-(33 / 50 : ℝ)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hX0]; norm_num
  have hsmall : (primeScale g Z) ^ (-(4 / 25 : ℝ)) ≤ (primeScale g Z) ^ (17 / 50 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
  change ‖∑ p ∈ F, windowWeight K S g Z i p * actualLocalCompensation K S P psi u s w z p‖ ≤ _
  calc
    _ ≤ ∑ p ∈ F, ‖windowWeight K S g Z i p * actualLocalCompensation K S P psi u s w z p‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ F, (reg + if p ∈ exteriorSupport K S u.ideal then ram else 0) :=
      Finset.sum_le_sum hterm
    _ = (F.card : ℝ) * reg + (R.card : ℝ) * ram := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hsumif]
    _ ≤ (A * primeScale g Z) * reg + (Cram * frequencyRowNorm K S u ^ eta) * ram :=
      add_le_add (mul_le_mul_of_nonneg_right hcard hreg) (mul_le_mul_of_nonneg_right hRcard hram)
    _ = (A * M * Creg) * (primeScale g Z) ^ (17 / 50 : ℝ) +
        (Cram * M * 19) * frequencyRowNorm K S u ^ eta * (primeScale g Z) ^ (-(4 / 25 : ℝ)) := by
      dsimp only [reg, ram]
      calc
        _ = (A * M * Creg) * (primeScale g Z * (primeScale g Z) ^ (-(33 / 50 : ℝ))) +
            (Cram * M * 19) * frequencyRowNorm K S u ^ eta * (primeScale g Z) ^ (-(4 / 25 : ℝ)) := by ring
        _ = _ := by rw [hmass]
    _ ≤ (A * M * Creg) * frequencyRowNorm K S u ^ eta * (primeScale g Z) ^ (17 / 50 : ℝ) +
        (Cram * M * 19) * frequencyRowNorm K S u ^ eta * (primeScale g Z) ^ (17 / 50 : ℝ) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right (by positivity) hNeta) (Real.rpow_nonneg hX0.le _)
      · exact mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = C * frequencyRowNorm K S u ^ eta * (primeScale g Z) ^ (17 / 50 : ℝ) := by dsimp [C]; ring

/-- The paper's actual full-correction bound on the small-row contour.
The common unmarked Euler product and every compensated slot come from
the same arithmetic provider.  All constants precede every original row
and scale, and no desired pointwise bound is an input. -/
theorem exists_actual_small_fullCorrection_bound (g : PrimeWindowGeometry)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (P : ProbeData K S) (psi : HeckeCharacter K),
      ThetaCalibrationInput K S P.arithmetic P.Lambda P.G →
      (∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val) →
      ∀ (T : Finset (HeckeCharacter K)) (u : FrequencyRow K S) (s w z : ℂ),
      7 / 8 ≤ s.re → 1 / 2 ≤ w.re → z.re = 17 / 50 →
        ‖compensatedRowFullCorrection K S P psi (arithmeticHighEulerData K S P psi)
          g T u Z s w z‖ ≤
            C * frequencyRowNorm K S u ^ eta * Z ^ (17 / 300 : ℝ) := by
  let delta : ℝ := eta / ((g.slots : ℝ) + 1)
  have hJ : 0 < (g.slots : ℝ) := by exact_mod_cast g.slots_pos
  have hdelta : 0 < delta := div_pos heta (by positivity)
  obtain ⟨Cs, Zs, hCs, hZs, hslot⟩ := exists_actual_small_fullCorrectionSlot_bound K S g hdelta
  obtain ⟨Ce, hCe, heuler⟩ := exists_uniform_rowCorrection_subpower K S
    (e := 1 / 20000) (by norm_num) (by norm_num) hdelta
  obtain ⟨Zf, hZf, hfactor⟩ := exists_actualFullCorrection_product_cutoff K S g
    (e := 1 / 20000) (by norm_num) (by norm_num)
  refine ⟨Ce * Cs ^ g.slots, max Zs Zf, by positivity,
    hZs.trans (le_max_left _ _), ?_⟩
  intro Z hZ P psi hcal hpsi T u s w z hs hw hz
  have hZZs : Zs ≤ Z := (le_max_left _ _).trans hZ
  have hZZf : Zf ≤ Z := (le_max_right _ _).trans hZ
  have hZ1 : 1 ≤ Z := hZs.trans hZZs
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ1
  have hX0 : 0 < primeScale g Z := Real.rpow_pos_of_pos hZ0 _
  have hN0 : 0 < frequencyRowNorm K S u := idealNorm_pos K u.ideal.val
  have hv := outer_contour_mem_sweptTube s w z hs hw hz.ge
  rw [hfactor Z hZZf P psi T u (3 / 4) (by norm_num) (by norm_num) s w z hv,
    norm_mul, norm_prod]
  have he : ‖rowCorrection K S P psi (arithmeticHighEulerData K S P psi) ∅ u s w z‖ ≤
      Ce * frequencyRowNorm K S u ^ delta := by
    simpa only [Finset.card_empty, pow_zero, mul_one] using
      heuler P psi ∅ u (3 / 4) (by norm_num) (by norm_num) (s, w, z) hv
  have hp : (∏ i : Fin g.slots, ‖actualFullCorrectionSlot K S P psi g T u Z s w z i‖) ≤
      (Cs * frequencyRowNorm K S u ^ delta * (primeScale g Z) ^ (17 / 50 : ℝ)) ^ g.slots := by
    calc
      _ ≤ ∏ _i : Fin g.slots,
          Cs * frequencyRowNorm K S u ^ delta * (primeScale g Z) ^ (17 / 50 : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun i _ => hslot Z hZZs P psi hcal hpsi T u s w z hs hw hz i)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hNpow : (frequencyRowNorm K S u ^ delta) ^ g.slots =
      frequencyRowNorm K S u ^ (delta * g.slots) :=
    (Real.rpow_mul_natCast hN0.le delta g.slots).symm
  have hXpow : ((primeScale g Z) ^ (17 / 50 : ℝ)) ^ g.slots =
      Z ^ (17 / 300 : ℝ) := by
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
        (Cs * frequencyRowNorm K S u ^ delta * (primeScale g Z) ^ (17 / 50 : ℝ)) ^ g.slots :=
      mul_le_mul he hp (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
    _ = (Ce * Cs ^ g.slots) * frequencyRowNorm K S u ^ (delta + delta * g.slots) *
        Z ^ (17 / 300 : ℝ) := by
      rw [mul_pow, mul_pow, hNpow, hXpow, Real.rpow_add hN0]
      ring
    _ = _ := by rw [hdelta_total]

end HeckeSkeleton.Expansion.SmallRows

#print axioms HeckeSkeleton.Expansion.SmallRows.exists_primeWindow_linear_count
#print axioms HeckeSkeleton.Expansion.SmallRows.ramified_primeWindow_card_subpower
#print axioms HeckeSkeleton.Expansion.SmallRows.exists_actual_small_fullCorrectionSlot_bound
#print axioms HeckeSkeleton.Expansion.SmallRows.exists_actual_small_fullCorrection_bound
