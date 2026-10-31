import HeckeSkeleton.ExpansionModels.PrincipalRowLocal
import HeckeSkeleton.HighBinSupport.EulerProductBounds

/-!
# Actual full correction on the principal residue rectangle

An empty original row-prime support makes every local factor regular.
The five genuine Euler faces have the uniform margin 163/200.  Actual
prime-norm summability bounds the complete unmarked product, and a single
scale cutoff makes the selected unmarked factors nonzero.  The original
finite subset algebra then gives C Z^(Re(z)/6), including all imaginary
coordinates and every z in [33/200,1].
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

/-- Uniform, summable local error on the principal rectangle. -/
theorem actual_unmarked_principal_rectangle_error_bound
    (P : ProbeData K S) (psi : HeckeCharacter K) (u : FrequencyRow K S)
    (s w z : ℂ) (hs : 7 / 8 ≤ s.re) (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re)
    (p : ExteriorPrime K S) (hp : p ∉ exteriorSupport K S u.ideal) :
    ‖actualLocalUnmarked K S P psi u s w z p - 1‖ ≤
      (11 / sweptTubeEulerMargin) * (p.val.asIdeal.absNorm : ℝ) ^ (-(363 / 200 : ℝ)) := by
  have hv := principal_rectangle_mem_rowEulerRegion s w z hs hw hz
  unfold actualLocalUnmarked
  rw [localFactor_eq_explicit_rowEulerRegion K S P psi ∅ u p (s, w, z) hv]
  simp only [explicitLocalEuler, if_neg hp, Finset.notMem_empty, if_false, sub_zero]
  have hb := phaseRowEuler_region_bound (δ := 163 / 200)
    (exteriorPrime_norm_two_le K S p) (by norm_num)
    (rowW K S P u p) (rowD K S P psi u p) (rowE K S P psi p) s w z
    (rowW_norm K S P u p) (rowD_norm K S P psi u p) (rowE_norm K S P psi p)
    (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  simpa only [show (-1 : ℝ) - 163 / 200 = -(363 / 200) by norm_num] using hb

/-- A fixed actual prime sum, independent of probe, target, row, and heights. -/
def principalEulerConstant : ℝ :=
  Real.exp (∑' p : ExteriorPrime K S,
    (11 / sweptTubeEulerMargin) * (p.val.asIdeal.absNorm : ℝ) ^ (-(363 / 200 : ℝ)))

theorem principalEulerConstant_pos : 0 < principalEulerConstant K S := Real.exp_pos _

/-- Every factor of the original infinite unmarked product is retained;
zeros are allowed and no division by that product is used. -/
theorem actual_principal_unmarked_bound
    (P : ProbeData K S) (psi : HeckeCharacter K) (u : FrequencyRow K S)
    (hrow : exteriorSupport K S u.ideal = ∅)
    (s w z : ℂ) (hs : 7 / 8 ≤ s.re) (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖rowCorrection K S P psi (arithmeticHighEulerData K S P psi) ∅ u s w z‖ ≤
      principalEulerConstant K S := by
  let b : ExteriorPrime K S → ℝ := fun p =>
    (11 / sweptTubeEulerMargin) * (p.val.asIdeal.absNorm : ℝ) ^ (-(363 / 200 : ℝ))
  have hb : ∀ p, 0 ≤ b p := by
    intro p
    dsimp only [b]
    exact mul_nonneg (div_nonneg (by norm_num) sweptTubeEulerMargin_pos.le)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hsum : Summable b :=
    (summable_exteriorPrime_norm_rpow K S (σ := 363 / 200) (by norm_num)).mul_left _
  have hf : ∀ p, ‖actualLocalUnmarked K S P psi u s w z p - 1‖ ≤ b p := by
    intro p
    exact actual_unmarked_principal_rectangle_error_bound K S P psi u s w z hs hw hz p
      (by simp only [hrow, Finset.notMem_empty, not_false_eq_true])
  have hbound := (product_norm_le_exp_tsum
    (actualLocalUnmarked K S P psi u s w z) b hb hsum hf).2
  rw [(_root_.Expansion.Project.actual_unmarked_hasProd_region K S P psi u s w z
    (principal_rectangle_mem_rowEulerRegion s w z hs hw hz)).tprod_eq] at hbound
  exact hbound

/-- One fixed cutoff supplies the selected local margin throughout the
principal rectangle, uniformly in the original target and all heights. -/
theorem exists_principal_window_local_cutoff (g : PrimeWindowGeometry) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (P : ProbeData K S) (psi : HeckeCharacter K) (T : Finset (HeckeCharacter K))
        (u : FrequencyRow K S), exteriorSupport K S u.ideal = ∅ →
      ∀ s w z : ℂ, 7 / 8 ≤ s.re → 19 / 20 ≤ w.re → 33 / 200 ≤ z.re →
      ∀ i : Fin g.slots, ∀ p ∈ primeWindow K S g T Z i,
        ‖actualLocalUnmarked K S P psi u s w z p - 1‖ ≤ 1 / 2 := by
  let B : ℝ := 11 / sweptTubeEulerMargin
  have ht : Tendsto (fun q : ℝ => B * q ^ (-(363 / 200 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 363 / 200)).const_mul B
  have hev : ∀ᶠ q : ℝ in atTop, B * q ^ (-(363 / 200 : ℝ)) ≤ 1 / 2 :=
    (ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono (fun _ h => h.le)
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp hev
  have hJ : (0 : ℝ) < g.slots := by exact_mod_cast g.slots_pos
  have halpha : 0 < (1 / 6 : ℝ) / g.slots := div_pos (by norm_num) hJ
  obtain ⟨Z0, hZ0⟩ := (tendsto_atTop_atTop.mp (tendsto_rpow_atTop halpha)) X0
  refine ⟨max 1 Z0, le_max_left _ _, ?_⟩
  intro Z hZ P psi T u hrow s w z hs hw hz i p hp
  have hX : X0 ≤ primeScale g Z := hZ0 Z ((le_max_right _ _).trans hZ)
  have hq : X0 ≤ (p.val.asIdeal.absNorm : ℝ) :=
    hX.trans (actual_primeWindow_norm_range K S g T Z i p hp).2.1.le
  exact (actual_unmarked_principal_rectangle_error_bound K S P psi u s w z hs hw hz p
    (by simp only [hrow, Finset.notMem_empty, not_false_eq_true])).trans (hX0 _ hq)

/-- The genuine sum over a complete slot has scale X^(Re z). -/
theorem exists_actual_principal_slot_bound (g : PrimeWindowGeometry) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (P : ProbeData K S) (psi : HeckeCharacter K),
      (∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val) →
      ∀ (T : Finset (HeckeCharacter K)) (u : FrequencyRow K S), exteriorSupport K S u.ideal = ∅ →
      ∀ s w z : ℂ, 7 / 8 ≤ s.re → 19 / 20 ≤ w.re → 33 / 200 ≤ z.re → z.re ≤ 1 →
      ∀ i : Fin g.slots,
        ‖actualFullCorrectionSlot K S P psi g T u Z s w z i‖ ≤ C * (primeScale g Z) ^ z.re := by
  obtain ⟨Z0, hZ0, hcut⟩ := exists_principal_window_local_cutoff K S g
  obtain ⟨M, hM, hprofile⟩ := exists_primeWindow_profile_norm_bound g
  obtain ⟨A, hA, hcount⟩ := exists_primeWindow_linear_count K S
  let Creg : ℝ := 1 + 48 / sweptTubeEulerMargin
  have hCreg : 0 < Creg := by dsimp [Creg]; have := sweptTubeEulerMargin_pos; positivity
  refine ⟨A * M * Creg, Z0, by positivity, hZ0, ?_⟩
  intro Z hZ P psi hpsi T u hrow s w z hs hw hz hz1 i
  have hZ1 : 1 ≤ Z := hZ0.trans hZ
  have hJ : (0 : ℝ) < g.slots := by exact_mod_cast g.slots_pos
  have hX : 1 ≤ primeScale g Z := Real.one_le_rpow hZ1 (div_pos (by norm_num) hJ).le
  have hX0 : 0 < primeScale g Z := zero_lt_one.trans_le hX
  have hterm (p : ExteriorPrime K S) (hp : p ∈ primeWindow K S g T Z i) :
      ‖windowWeight K S g Z i p * actualLocalCompensation K S P psi u s w z p‖ ≤
        M * Creg * (primeScale g Z) ^ (z.re - 1) := by
    have hclose := hcut Z hZ P psi T u hrow s w z hs hw hz i p hp
    have hlocal := actualLocalCompensation_principal_rectangle_bound K S P psi u s w z hs hw hz p
      (by simp only [hrow, Finset.notMem_empty, not_false_eq_true]) (hpsi p) hclose
    have hpow := Real.rpow_le_rpow_of_nonpos hX0
      (actual_primeWindow_norm_range K S g T Z i p hp).2.1.le (by linarith : z.re - 1 ≤ 0)
    rw [norm_mul]
    calc
      _ ≤ M * (Creg * (p.val.asIdeal.absNorm : ℝ) ^ (z.re - 1)) :=
        mul_le_mul (hprofile i _) hlocal (norm_nonneg _) hM.le
      _ ≤ M * (Creg * (primeScale g Z) ^ (z.re - 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hCreg.le) hM.le
      _ = _ := by ring
  have hcard := hcount g T Z i hX
  have hscale : primeScale g Z * (primeScale g Z) ^ (z.re - 1) = (primeScale g Z) ^ z.re := by
    calc
      _ = (primeScale g Z) ^ (1 : ℝ) * (primeScale g Z) ^ (z.re - 1) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hX0]; congr 1; ring
  unfold actualFullCorrectionSlot
  calc
    _ ≤ ∑ p ∈ primeWindow K S g T Z i,
        ‖windowWeight K S g Z i p * actualLocalCompensation K S P psi u s w z p‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ primeWindow K S g T Z i, M * Creg * (primeScale g Z) ^ (z.re - 1) :=
      Finset.sum_le_sum hterm
    _ = ((primeWindow K S g T Z i).card : ℝ) * (M * Creg * (primeScale g Z) ^ (z.re - 1)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (A * primeScale g Z) * (M * Creg * (primeScale g Z) ^ (z.re - 1)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (A * M * Creg) * (primeScale g Z * (primeScale g Z) ^ (z.re - 1)) := by ring
    _ = _ := by rw [hscale]

/-- The complete original principal correction, on the whole residue
rectangle and uniformly in every imaginary coordinate.  The original row
support condition is geometric and is discharged for literal principal
rows; no final analytic estimate is an input. -/
theorem exists_actual_principal_fullCorrection_bound (g : PrimeWindowGeometry) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (P : ProbeData K S) (psi : HeckeCharacter K),
      (∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val) →
      ∀ (T : Finset (HeckeCharacter K)) (u : FrequencyRow K S), exteriorSupport K S u.ideal = ∅ →
      ∀ s w z : ℂ, 7 / 8 ≤ s.re → 19 / 20 ≤ w.re → 33 / 200 ≤ z.re → z.re ≤ 1 →
        ‖compensatedRowFullCorrection K S P psi (arithmeticHighEulerData K S P psi)
          g T u Z s w z‖ ≤ C * Z ^ (z.re / 6) := by
  obtain ⟨Cs, Zs, hCs, hZs, hslot⟩ := exists_actual_principal_slot_bound K S g
  obtain ⟨Zf, hZf, hcut⟩ := exists_principal_window_local_cutoff K S g
  have hCe : 0 < principalEulerConstant K S := principalEulerConstant_pos K S
  refine ⟨principalEulerConstant K S * Cs ^ g.slots, max Zs Zf, by positivity,
    hZs.trans (le_max_left _ _), ?_⟩
  intro Z hZ P psi hpsi T u hrow s w z hs hw hz hz1
  have hZZs : Zs ≤ Z := (le_max_left _ _).trans hZ
  have hZZf : Zf ≤ Z := (le_max_right _ _).trans hZ
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZs.trans hZZs)
  have hXpos : 0 < primeScale g Z := Real.rpow_pos_of_pos hZpos _
  have hJ : (0 : ℝ) < g.slots := by exact_mod_cast g.slots_pos
  have hv := principal_rectangle_mem_rowEulerRegion s w z hs hw hz
  have hne : ∀ i : Fin g.slots, ∀ p ∈ primeWindow K S g T Z i,
      actualLocalUnmarked K S P psi u s w z p ≠ 0 := by
    intro i p hp heq
    have hclose := hcut Z hZZf P psi T u hrow s w z hs hw hz i p hp
    rw [heq, zero_sub, norm_neg, norm_one] at hclose
    norm_num at hclose
  rw [_root_.Expansion.Project.actualFullCorrection_eq_product_region K S P psi g T u Z s w z hv hne,
    norm_mul, norm_prod]
  have he := actual_principal_unmarked_bound K S P psi u hrow s w z hs hw hz
  have hp : (∏ i : Fin g.slots, ‖actualFullCorrectionSlot K S P psi g T u Z s w z i‖) ≤
      (Cs * (primeScale g Z) ^ z.re) ^ g.slots := by
    calc
      _ ≤ ∏ _i : Fin g.slots, Cs * (primeScale g Z) ^ z.re :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun i _ => hslot Z hZZs P psi hpsi T u hrow s w z hs hw hz hz1 i)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hscale : ((primeScale g Z) ^ z.re) ^ g.slots = Z ^ (z.re / 6) := by
    rw [← Real.rpow_mul_natCast hXpos.le]
    unfold primeScale
    rw [← Real.rpow_mul hZpos.le]
    congr 1
    field_simp [hJ.ne']
    <;> ring
  calc
    _ ≤ principalEulerConstant K S * (Cs * (primeScale g Z) ^ z.re) ^ g.slots :=
      mul_le_mul he hp (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hCe.le
    _ = (principalEulerConstant K S * Cs ^ g.slots) * Z ^ (z.re / 6) := by
      rw [mul_pow, hscale]
      ring

end HeckeSkeleton.Expansion.PrincipalRows

#print axioms HeckeSkeleton.Expansion.PrincipalRows.actual_unmarked_principal_rectangle_error_bound
#print axioms HeckeSkeleton.Expansion.PrincipalRows.actual_principal_unmarked_bound
#print axioms HeckeSkeleton.Expansion.PrincipalRows.exists_principal_window_local_cutoff
#print axioms HeckeSkeleton.Expansion.PrincipalRows.exists_actual_principal_fullCorrection_bound
