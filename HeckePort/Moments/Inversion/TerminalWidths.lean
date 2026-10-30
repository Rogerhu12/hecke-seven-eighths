import HeckePort.Moments.Descent.Widths
import HeckePort.Moments.Descent.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Terminal widths of the inverse recursion

Port of openai/math `OAI/NumberTheory/DirichletL/Inversion/TerminalWidths.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

Changes:

* openai's row factorisation is `I = rowPowerfulPart I * rowMaskPart I Q * rowResidualPart I Q`
  (`GaussSum/PowerfulParts.lean`).  Here it is an arbitrary factorisation `I = Pw * Mk * Rs`
  with `Mk ≠ ⊥` (`rowPowerfulPart I ↦ Pw`, `rowResidualPart I (B*F*R) ↦ Rs`), as in `Widths.lean`.
  The cost bound `reflectionConductorCost_bound` (CubicSieve/NormalizedMass, which needs the
  pool hypotheses `hpool`, `hres`) enters as a hypothesis `hcost` of the same form.
* `completedLocalExponent I F (P i)` becomes an arbitrary exponent table `j : ι → ℕ`; the
  definition of `reflectionConductorCost` and its pieces are copied (they are elementary).
* `ramifiedWidth` uses an arbitrary real `q ≥ 1` in place of `3` (over `ℤ[ω]`, `3 = N(λ)²`
  is the ramified norm; over a general field `q` is the norm of the relevant `S`-part).
  `fractionalThetaPoint_norm_width` is not ported (it is a statement about the specific
  theta point `fractionalThetaPoint` of `ℤ[ω]`).
* Not ported (they use the cubic-sieve objects `FreeReflection.pool`, `reflectionSixActive`,
  `reflectedBranch`, `reflectedLocalPiece`, `Admissible`/`fixedBadPrimes`):
  `surviving_local_piece`, `canonical_active_pool`, `surviving_inactive_exponent`,
  `surviving_reflected_branch`, `canonical_terminal_common_width`,
  `residual_admissible_of_fixed_bad`, `canonicalDualWidth`, `canonicalExtractedWidth`,
  `canonical_terminal_saving`.  Their abstract content is `actual_terminal_saving` below.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators

variable {K : Type*} [Field K] [NumberField K]
local instance : Infinite (𝓞 K) := Module.Free.infinite ℤ (𝓞 K)

lemma norm_one_le (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : (1 : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem physical_residual_width (I Q Pw Mk Rs : Ideal (𝓞 K)) (hMk : Mk ≠ ⊥)
    (hprod : Pw * Mk * Rs = I)
    (Z M O₀ H Ck CO CH : ℝ) (hZ : 1 < Z) (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm Pw : ℝ))
    (hres : Z ^ H / CH ≤ (Ideal.absNorm Rs : ℝ)) :
    H ≤ M - O₀ + Real.log (CH * Ck * CO) / Real.log Z := by
  have _ := Q
  have hz0 : 0 < Z := by linarith
  have hp := (div_le_iff₀ hCO).mp hpow
  have hr := (div_le_iff₀ hCH).mp hres
  have hs : Z ^ (H + O₀) ≤ (CH * Ck * CO) * Z ^ M := by
    calc
      _ = Z ^ H * Z ^ O₀ := Real.rpow_add hz0 _ _
      _ ≤ ((Ideal.absNorm Rs : ℝ) * CH) * ((Ideal.absNorm Pw : ℝ) * CO) :=
        mul_le_mul hr hp (Real.rpow_nonneg hz0.le _) (by positivity)
      _ = (CH * CO) * ((Ideal.absNorm Pw : ℝ) * (Ideal.absNorm Rs : ℝ)) := by ring
      _ ≤ (CH * CO) * (Ideal.absNorm I : ℝ) :=
        mul_le_mul_of_nonneg_left (by
          simpa only [mul_comm] using actual_residual_norm_width I Pw Mk Rs hMk hprod)
          (by positivity)
      _ ≤ (CH * CO) * (Ck * Z ^ M) := mul_le_mul_of_nonneg_left hk (by positivity)
      _ = _ := by ring
  have hl := Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos hz0 _) hs
  rw [Real.logb_rpow hz0 (ne_of_gt hZ), Real.logb_mul (by positivity) (by positivity),
    Real.logb_rpow hz0 (ne_of_gt hZ)] at hl
  unfold Real.logb at hl
  linarith

theorem constant_log_error (C η : ℝ) (_hC : 0 < C) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → Real.log C / Real.log Z ≤ η := by
  refine ⟨max 2 (Real.exp (Real.log C / η)), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro Z hZ
  have hz : 1 < Z := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hZ)
  have he : Real.exp (Real.log C / η) ≤ Z := (le_max_right _ _).trans hZ
  have hl := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp] at hl
  apply (div_le_iff₀ (Real.log_pos hz)).mpr
  have hh := (div_le_iff₀ hη).mp hl
  nlinarith

def activeCharge (j : ℕ) (e : Fin 3) : ℤ :=
  if j = 4 then (if e = 2 then -2 else 1) else if j = 0 then 1 else 2

theorem activeCharge_le_two (j : ℕ) (e : Fin 3) : activeCharge j e ≤ 2 := by
  unfold activeCharge
  split_ifs <;> norm_num

theorem activeCharge_le_one (j : ℕ) (e : Fin 3) (hj : j = 0 ∨ j = 4) :
    activeCharge j e ≤ 1 := by
  rcases hj with rfl | rfl
  · simp [activeCharge]
  · simp only [activeCharge, ite_true]
    split_ifs <;> norm_num

/-- openai `reflectionLocalCost` (CubicSieve/NormalizedMass). -/
def reflectionLocalCost (q : ℝ) (j : ℕ) (e : Fin 3) : ℝ :=
  if j = 4 then (if e = 2 then 1 / q ^ 2 else q)
  else if j = 0 then q else q ^ 2

theorem reflectionLocalCost_eq_charge (q : ℝ) (_hq : 0 < q) (j : ℕ) (e : Fin 3) :
    reflectionLocalCost q j e = q ^ (activeCharge j e : ℝ) := by
  unfold reflectionLocalCost activeCharge
  split_ifs <;> norm_num [Real.rpow_neg, Real.rpow_two]

/-- openai `reflectionExtractedPrime`. -/
def reflectionExtractedPrime (P : Ideal (𝓞 K)) (j : ℕ) (e v : Fin 3) : Ideal (𝓞 K) :=
  if (j = 4 ∧ e = v) ∨ (j = 0 ∧ v = 0) then P else 1

def reflectionExtractedDivisor {ι : Type*} [Fintype ι]
    (P : ι → Ideal (𝓞 K)) (j : ι → ℕ) (e : ι → Fin 3) (v : Fin 3) : Ideal (𝓞 K) :=
  ∏ i, reflectionExtractedPrime (P i) (j i) (e i) v

def reflectionConductorCost {ι : Type*} [Fintype ι]
    (P : ι → Ideal (𝓞 K)) (j : ι → ℕ) (e : ι → Fin 3) : ℝ :=
  (Ideal.absNorm (∏ i, P i) : ℝ) ^ 2 /
    ((Ideal.absNorm (reflectionExtractedDivisor P j e 1) : ℝ) *
     (Ideal.absNorm (reflectionExtractedDivisor P j e 0) : ℝ) *
     (Ideal.absNorm (reflectionExtractedDivisor P j e 2) : ℝ) ^ 4)

theorem reflectionExtractedDivisor_ne_zero {ι : Type*} [Fintype ι]
    (P : ι → Ideal (𝓞 K)) (hP : ∀ i, P i ≠ ⊥) (j : ι → ℕ) (e : ι → Fin 3) (v : Fin 3) :
    reflectionExtractedDivisor P j e v ≠ ⊥ := by
  unfold reflectionExtractedDivisor
  refine Finset.prod_ne_zero_iff.mpr (fun i _ => ?_)
  unfold reflectionExtractedPrime
  split_ifs
  · exact hP i
  · rw [Ideal.one_eq_top]; exact top_ne_bot

def normWidth (Z : ℝ) (I : Ideal (𝓞 K)) : ℝ := Real.logb Z (Ideal.absNorm I : ℝ)

def reflectionWidth {ι : Type*} [Fintype ι] (Z : ℝ)
    (P : ι → Ideal (𝓞 K)) (j : ι → ℕ) (e : ι → Fin 3) : ℝ :=
  2 * normWidth Z (∏ i, P i) - normWidth Z (reflectionExtractedDivisor P j e 1) -
    normWidth Z (reflectionExtractedDivisor P j e 0) -
      4 * normWidth Z (reflectionExtractedDivisor P j e 2)

theorem reflectionConductorCost_pos {ι : Type*} [Fintype ι]
    (P : ι → Ideal (𝓞 K)) (hP : ∀ i, P i ≠ ⊥) (j : ι → ℕ) (e : ι → Fin 3) :
    0 < reflectionConductorCost P j e := by
  have hp := actual_ideal_norm_pos (∏ i, P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hP i))
  have hd (v : Fin 3) := actual_ideal_norm_pos (reflectionExtractedDivisor P j e v)
    (reflectionExtractedDivisor_ne_zero P hP j e v)
  have h₀ := hd 0
  have h₁ := hd 1
  have h₂ := hd 2
  unfold reflectionConductorCost
  positivity

theorem logb_reflectionConductorCost {ι : Type*} [Fintype ι]
    (Z : ℝ) (P : ι → Ideal (𝓞 K)) (hP : ∀ i, P i ≠ ⊥) (j : ι → ℕ) (e : ι → Fin 3) :
    Real.logb Z (reflectionConductorCost P j e) = reflectionWidth Z P j e := by
  have hp := actual_ideal_norm_pos (∏ i, P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hP i))
  have hd (v : Fin 3) := actual_ideal_norm_pos (reflectionExtractedDivisor P j e v)
    (reflectionExtractedDivisor_ne_zero P hP j e v)
  have h₀ := hd 0
  have h₁ := hd 1
  have h₂ := hd 2
  unfold reflectionConductorCost reflectionWidth normWidth
  rw [Real.logb_div (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (hd 1).ne' (hd 0).ne', Real.logb_pow, Real.logb_pow]
  norm_num
  ring

theorem reflection_charge_width {ι : Type*} [Fintype ι]
    (I F B R Pw Mk Rs : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hF : F ≠ ⊥) (hB : B ≠ ⊥) (hR : R ≠ ⊥)
    (hPw : Pw ≠ ⊥) (hMk : Mk ≠ ⊥) (hRs : Rs ≠ ⊥) (hprod : Pw * Mk * Rs = I)
    (P : ι → Ideal (𝓞 K)) (hP : ∀ i, P i ≠ ⊥) (j : ι → ℕ) (e : ι → Fin 3)
    (hcost : reflectionConductorCost P j e ≤ (Ideal.absNorm Pw : ℝ) *
      (Ideal.absNorm Mk : ℝ) ^ 2 * (Ideal.absNorm (B * F * R) : ℝ))
    (Z : ℝ) (hZ : 1 < Z) :
    2 * normWidth Z Rs + reflectionWidth Z P j e ≤
      normWidth Z B + 2 * normWidth Z I - normWidth Z Pw + normWidth Z F + normWidth Z R := by
  have hi := actual_ideal_norm_pos I hI
  have hf := actual_ideal_norm_pos F hF
  have hb := actual_ideal_norm_pos B hB
  have hr := actual_ideal_norm_pos R hR
  have hp := actual_ideal_norm_pos Pw hPw
  have hx := actual_ideal_norm_pos Rs hRs
  have hc := reflectionConductorCost_pos P hP j e
  have hh := Real.logb_le_logb_of_le hZ (mul_pos (sq_pos_of_pos hx) hc)
    (actual_common_width_charge_label_puncture I F R B Pw Mk Rs hI hF hR hB hPw hMk hprod _ hcost)
  rw [Real.logb_mul (by positivity) hc.ne', Real.logb_pow,
    logb_reflectionConductorCost Z P hP,
    Real.logb_mul (by positivity) hr.ne', Real.logb_mul (by positivity) hf.ne',
    Real.logb_mul hb.ne' (by positivity), Real.logb_div (by positivity) hp.ne',
    Real.logb_pow] at hh
  unfold normWidth
  norm_num at hh ⊢
  linarith

theorem normWidth_upper (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (Z C E : ℝ)
    (hZ : 1 < Z) (hC : 0 < C) (h : (Ideal.absNorm I : ℝ) ≤ C * Z ^ E) :
    normWidth Z I ≤ E + Real.logb Z C := by
  have hz0 : 0 < Z := by linarith
  have hh := Real.logb_le_logb_of_le hZ (actual_ideal_norm_pos I hI) h
  rw [Real.logb_mul hC.ne' (by positivity), Real.logb_rpow hz0 (ne_of_gt hZ)] at hh
  unfold normWidth
  linarith

theorem normWidth_lower (I : Ideal (𝓞 K)) (Z C E : ℝ)
    (hZ : 1 < Z) (hC : 0 < C) (h : Z ^ E / C ≤ (Ideal.absNorm I : ℝ)) :
    E - Real.logb Z C ≤ normWidth Z I := by
  have hz0 : 0 < Z := by linarith
  have hh := Real.logb_le_logb_of_le hZ (div_pos (Real.rpow_pos_of_pos hz0 E) hC) h
  rwa [Real.logb_div (by positivity) hC.ne', Real.logb_rpow hz0 (ne_of_gt hZ)] at hh

def terminalDualWidth {ι : Type*} [Fintype ι] (Z H za Nstar : ℝ)
    (P : ι → Ideal (𝓞 K)) (j : ι → ℕ) (e : ι → Fin 3) : ℝ :=
  2 * H + 2 * normWidth Z (∏ i, P i) + 2 * za - Nstar -
    normWidth Z (reflectionExtractedDivisor P j e 1) -
      3 * normWidth Z (reflectionExtractedDivisor P j e 2)

def widthConstant (B : Ideal (𝓞 K)) (Ck CO CH Cf : ℝ) : ℝ :=
  CH ^ 2 * (Ideal.absNorm B : ℝ) * Ck ^ 2 * CO * Cf

theorem logb_widthConstant (Z : ℝ) (B : Ideal (𝓞 K)) (hB : B ≠ ⊥)
    (Ck CO CH Cf : ℝ) (hk : 0 < Ck) (ho : 0 < CO) (hh : 0 < CH) (hf : 0 < Cf) :
    Real.logb Z (widthConstant B Ck CO CH Cf) =
      2 * Real.logb Z CH + normWidth Z B + 2 * Real.logb Z Ck +
        Real.logb Z CO + Real.logb Z Cf := by
  have hb := actual_ideal_norm_pos B hB
  unfold widthConstant normWidth
  rw [Real.logb_mul (by positivity) hf.ne', Real.logb_mul (by positivity) ho.ne',
    Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) hb.ne',
    Real.logb_pow, Real.logb_pow]
  norm_num

theorem terminal_common_width {ι : Type*} [Fintype ι]
    (I F B R Pw Mk Rs : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hF : F ≠ ⊥) (hB : B ≠ ⊥) (hR : R ≠ ⊥)
    (hPw : Pw ≠ ⊥) (hMk : Mk ≠ ⊥) (hRs : Rs ≠ ⊥) (hprod : Pw * Mk * Rs = I)
    (P : ι → Ideal (𝓞 K)) (hP : ∀ i, P i ≠ ⊥) (j : ι → ℕ) (e : ι → Fin 3)
    (hcost : reflectionConductorCost P j e ≤ (Ideal.absNorm Pw : ℝ) *
      (Ideal.absNorm Mk : ℝ) ^ 2 * (Ideal.absNorm (B * F * R) : ℝ))
    (Z M O₀ H V za Nstar Ck CO CH Cf : ℝ) (hZ : 1 < Z)
    (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH) (hCf : 0 < Cf)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm Pw : ℝ))
    (hrow : Z ^ H / CH ≤ (Ideal.absNorm Rs : ℝ))
    (hf : (Ideal.absNorm F : ℝ) ≤ Cf * Z ^ V) :
    terminalDualWidth Z H za Nstar P j e -
      normWidth Z (reflectionExtractedDivisor P j e 0) -
      normWidth Z (reflectionExtractedDivisor P j e 2) ≤
        2 * M - O₀ + normWidth Z R + V - Nstar + 2 * za +
          Real.log (widthConstant B Ck CO CH Cf) / Real.log Z := by
  have hb := reflection_charge_width I F B R Pw Mk Rs hI hF hB hR hPw hMk hRs hprod P hP j e
    hcost Z hZ
  have h₁ := normWidth_upper I hI Z Ck M hZ hCk hk
  have h₂ := normWidth_lower Pw Z CO O₀ hZ hCO hpow
  have h₃ := normWidth_lower Rs Z CH H hZ hCH hrow
  have h₄ := normWidth_upper F hF Z Cf V hZ hCf hf
  change _ ≤ 2 * M - O₀ + normWidth Z R + V - Nstar + 2 * za +
    Real.logb Z (widthConstant B Ck CO CH Cf)
  rw [logb_widthConstant Z B hB Ck CO CH Cf hCk hCO hCH hCf]
  unfold terminalDualWidth reflectionWidth at *
  linarith

theorem normWidth_nonneg (Z : ℝ) (hZ : 1 < Z) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    0 ≤ normWidth Z I := Real.logb_nonneg hZ (norm_one_le I hI)

theorem rpow_reflectionWidth {ι : Type*} [Fintype ι]
    (Z : ℝ) (hZ : 1 < Z) (P : ι → Ideal (𝓞 K)) (hP : ∀ i, P i ≠ ⊥)
    (j : ι → ℕ) (e : ι → Fin 3) :
    Z ^ reflectionWidth Z P j e = reflectionConductorCost P j e := by
  rw [← logb_reflectionConductorCost Z P hP j e]
  exact Real.rpow_logb (by linarith) (ne_of_gt hZ) (reflectionConductorCost_pos P hP j e)

theorem width_error_threshold (B : Ideal (𝓞 K)) (hB : B ≠ ⊥)
    (Ck CO CH Cf η : ℝ) (hk : 0 < Ck) (ho : 0 < CO) (hh : 0 < CH)
    (hf : 0 < Cf) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      Real.log (CH * Ck * CO) / Real.log Z ≤ η ∧
      Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η := by
  have hb := actual_ideal_norm_pos B hB
  obtain ⟨a, ha, h₁⟩ := constant_log_error (CH * Ck * CO) η (by positivity) hη
  obtain ⟨b, hb', h₂⟩ := constant_log_error (widthConstant B Ck CO CH Cf) η
    (by unfold widthConstant; positivity) hη
  exact ⟨max a b, ha.trans_le (le_max_left _ _), fun Z hZ =>
    ⟨h₁ Z ((le_max_left _ _).trans hZ), h₂ Z ((le_max_right _ _).trans hZ)⟩⟩

def hybridSaving (v za : ℝ) : ℝ := min v (min za ((v + za) / 3))

def reflectedExponent (O₀ H S₀ B₀ za v ell el Td : ℝ) : ℝ :=
  O₀ / 2 + max H (v + ell) - S₀ - B₀ + za - hybridSaving v za - ell -
    2 * el / 3 - max 0 (Td - v - 3 * ell - el) / 2

theorem hybridSaving_nonneg {v za : ℝ} (hv : 0 ≤ v) (hz : 0 ≤ za) :
    0 ≤ hybridSaving v za := by unfold hybridSaving; positivity

theorem hybridSaving_half {v za : ℝ} (hv : 0 ≤ v)
    (hu : hybridSaving v za ≠ za) : v / 2 ≤ hybridSaving v za := by
  unfold hybridSaving at *
  rcases le_total v (min za ((v + za) / 3)) with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h] at *
    rcases le_total za ((v + za) / 3) with hz | hz
    · exact (hu (min_eq_left hz)).elim
    · rw [min_eq_right hz]
      linarith

theorem terminal_width_from_invariant
    {F₀ N V M Q z₀ c O₀ za Nstar hhat d η Td S₀ B₀ : ℝ}
    (hinv : CanonicalMargins F₀ M Q z₀ c) (hF : F₀ = N + V)
    (hscale : Nstar = N - 3 * hhat) (hV : V ≤ d) (hh : hhat ≤ d + η)
    (hwidth : Td - S₀ - B₀ ≤ 2 * M - O₀ + Q + V - Nstar + 2 * za + η) :
    Td - S₀ - B₀ ≤ M - O₀ + 2 * za - z₀ - c + 5 * d + 4 * η := by
  have hi := hinv.1
  linarith

theorem reflected_row_bound {O₀ H S₀ B₀ za v ell el Td M η : ℝ}
    (hO : 0 ≤ O₀) (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hz : 0 ≤ za) (hv : 0 ≤ v) (hl : 0 ≤ ell) (he : -η ≤ el)
    (hrow : v + ell ≤ H) (hH : H ≤ M - O₀ + η) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤ M + za + 5 * η / 3 := by
  have hu := hybridSaving_nonneg hv hz
  have hm := le_max_left 0 (Td - v - 3 * ell - el)
  unfold reflectedExponent
  rw [max_eq_left hrow]
  linarith

theorem reflected_column_full_bound {O₀ H S₀ B₀ za v ell el Td η τ : ℝ}
    (hl : 0 ≤ ell) (he : -η ≤ el) (hcol : H ≤ v + ell)
    (hu : hybridSaving v za = za) (hret : v + 3 * ell + el ≤ Td + τ) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
      O₀ / 2 + (Td - S₀ - B₀) + 5 * η / 3 + τ := by
  have hm := le_max_left 0 (Td - v - 3 * ell - el)
  unfold reflectedExponent
  rw [max_eq_right hcol, hu]
  linarith

theorem reflected_column_partial_bound {O₀ H S₀ B₀ za v ell el Td η τ : ℝ}
    (hS : 0 ≤ S₀) (hB : 0 ≤ B₀) (hv : 0 ≤ v) (hl : 0 ≤ ell)
    (he : -η ≤ el) (hcol : H ≤ v + ell)
    (hu : hybridSaving v za ≠ za) (hret : v + 3 * ell + el ≤ Td + τ) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
      O₀ / 2 + (Td - S₀ - B₀) / 2 + za + 7 * η / 6 + τ / 2 := by
  have hu' := hybridSaving_half hv hu
  have hm := le_max_left 0 (Td - v - 3 * ell - el)
  unfold reflectedExponent
  rw [max_eq_right hcol]
  linarith

theorem reflected_terminal_cases
    {F₀ M Q z₀ c O₀ H S₀ B₀ za v ell el Td d η τ : ℝ}
    (hinv : CanonicalMargins F₀ M Q z₀ c) (hQ : 0 ≤ Q)
    (hO : 0 ≤ O₀) (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hz : 0 ≤ za) (hzcap : za ≤ z₀) (hv : 0 ≤ v) (hl : 0 ≤ ell)
    (he : -η ≤ el) (hret : v + 3 * ell + el ≤ Td + τ)
    (hH : H ≤ M - O₀ + η)
    (hT : Td - S₀ - B₀ ≤ M - O₀ + 2 * za - z₀ - c + 5 * d + 4 * η) :
    (v + ell ≤ H → reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤ F₀ - c + 5 * η / 3) ∧
    (H ≤ v + ell → hybridSaving v za = za →
      reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤ F₀ - 2 * c + 5 * d + 17 * η / 3 + τ) ∧
    (H ≤ v + ell → hybridSaving v za ≠ za →
      reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
        F₀ - M / 4 - 3 * c / 4 + 5 * d / 2 + 19 * η / 6 + τ / 2) := by
  obtain ⟨hi₁, hi₂⟩ := hinv
  refine ⟨?_, ?_, ?_⟩
  · intro hrow
    have hb := reflected_row_bound hO hS hB hz hv hl he hrow hH (Td := Td)
    linarith
  · intro hcol hu
    have hb := reflected_column_full_bound hl he hcol hu hret (O₀ := O₀) (S₀ := S₀) (B₀ := B₀)
    linarith
  · intro hcol hu
    have hb := reflected_column_partial_bound hS hB hv hl he hcol hu hret (O₀ := O₀)
    linarith

theorem reflected_terminal_saving
    {F₀ M Q z₀ c cstar O₀ H S₀ B₀ za v ell el Td d η τ π : ℝ}
    (hinv : CanonicalMargins F₀ M Q z₀ c) (hQ : 0 ≤ Q) (hM : 0 ≤ M)
    (hO : 0 ≤ O₀) (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hz : 0 ≤ za) (hzcap : za ≤ z₀) (hv : 0 ≤ v) (hl : 0 ≤ ell)
    (he : -η ≤ el) (hret : v + 3 * ell + el ≤ Td + τ)
    (hH : H ≤ M - O₀ + η)
    (hT : Td - S₀ - B₀ ≤ M - O₀ + 2 * za - z₀ - c + 5 * d + 4 * η)
    (hc : 0 < cstar) (hmargin : cstar / 2 ≤ c) (hd : d ≤ cstar / 200)
    (hη : η ≤ cstar / 1000) (hτ : τ ≤ cstar / 1000) (hπ : π ≤ cstar / 1000) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td + π ≤ F₀ - cstar / 4 := by
  obtain ⟨hr, hf, hp⟩ := reflected_terminal_cases hinv hQ hO hS hB hz hzcap hv hl he hret hH hT
  rcases le_total (v + ell) H with h | h
  · have := hr h
    linarith
  · by_cases hu : hybridSaving v za = za
    · have := hf h hu
      linarith
    · have := hp h hu
      linarith

/-- openai `ramifiedWidth`, with the ramified norm `3` replaced by an arbitrary real `q`. -/
def ramifiedWidth (q Z : ℝ) (m : ℕ) : ℝ := ((m : ℝ) - 4) * Real.logb Z q

theorem rpow_ramifiedWidth (q Z : ℝ) (hq : 0 < q) (hZ : 1 < Z) (m : ℕ) :
    Z ^ ramifiedWidth q Z m = q ^ ((m : ℝ) - 4) := by
  unfold ramifiedWidth
  rw [mul_comm, Real.rpow_mul (by linarith : 0 ≤ Z),
    Real.rpow_logb (by linarith : 0 < Z) (ne_of_gt hZ) hq]

theorem ramified_width_threshold (q : ℝ) (hq : 1 ≤ q) (η : ℝ) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → ∀ m : ℕ, -η ≤ ramifiedWidth q Z m := by
  obtain ⟨Z₀, hZ₀, hlog⟩ := constant_log_error (q ^ (4 : ℕ)) η (by positivity) hη
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZ m
  have hz := hZ₀.trans_le hZ
  have hl := hlog Z hZ
  change Real.logb Z (q ^ (4 : ℕ)) ≤ η at hl
  rw [Real.logb_pow] at hl
  have hn : 0 ≤ Real.logb Z q := Real.logb_nonneg hz hq
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold ramifiedWidth
  norm_num at hl
  nlinarith

theorem terminal_error_threshold (q : ℝ) (hq : 1 ≤ q) (B : Ideal (𝓞 K)) (hB : B ≠ ⊥)
    (Ck CO CH Cf η : ℝ) (hk : 0 < Ck) (ho : 0 < CO) (hh : 0 < CH)
    (hf : 0 < Cf) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      Real.log (CH * Ck * CO) / Real.log Z ≤ η ∧
      Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η ∧
      ∀ m : ℕ, -η ≤ ramifiedWidth q Z m := by
  obtain ⟨a, ha, h₁⟩ := width_error_threshold B hB Ck CO CH Cf η hk ho hh hf hη
  obtain ⟨b, hb, h₂⟩ := ramified_width_threshold q hq η hη
  refine ⟨max a b, ha.trans_le (le_max_left _ _), fun Z hZ => ?_⟩
  exact ⟨(h₁ Z ((le_max_left _ _).trans hZ)).1,
    (h₁ Z ((le_max_left _ _).trans hZ)).2, h₂ Z ((le_max_right _ _).trans hZ)⟩

theorem actual_terminal_saving {ι : Type*} [Fintype ι]
    (I F B R Pw Mk Rs : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hF : F ≠ ⊥) (hB : B ≠ ⊥) (hR : R ≠ ⊥)
    (hPw : Pw ≠ ⊥) (hMk : Mk ≠ ⊥) (hRs : Rs ≠ ⊥) (hprod : Pw * Mk * Rs = I)
    (P : ι → Ideal (𝓞 K)) (hP : ∀ i, P i ≠ ⊥) (j : ι → ℕ) (e : ι → Fin 3)
    (hcost : reflectionConductorCost P j e ≤ (Ideal.absNorm Pw : ℝ) *
      (Ideal.absNorm Mk : ℝ) ^ 2 * (Ideal.absNorm (B * F * R) : ℝ))
    (Z F₀ N V M z₀ c cstar O₀ H za Nstar hhat v ell el d η τ π Ck CO CH Cf : ℝ)
    (hZ : 1 < Z) (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH) (hCf : 0 < Cf)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm Pw : ℝ))
    (hrow : Z ^ H / CH ≤ (Ideal.absNorm Rs : ℝ))
    (hf : (Ideal.absNorm F : ℝ) ≤ Cf * Z ^ V)
    (hlogH : Real.log (CH * Ck * CO) / Real.log Z ≤ η)
    (hlogT : Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η)
    (hinv : CanonicalMargins F₀ M (normWidth Z R) z₀ c) (hF₀ : F₀ = N + V)
    (hscale : Nstar = N - 3 * hhat) (hV : V ≤ d) (hh : hhat ≤ d + η)
    (hM : 0 ≤ M) (hO : 0 ≤ O₀) (hz : 0 ≤ za) (hzcap : za ≤ z₀)
    (hv : 0 ≤ v) (hl : 0 ≤ ell) (he : -η ≤ el)
    (hret : v + 3 * ell + el ≤ terminalDualWidth Z H za Nstar P j e + τ)
    (hc : 0 < cstar) (hmargin : cstar / 2 ≤ c) (hd : d ≤ cstar / 200)
    (hη : η ≤ cstar / 1000) (hτ : τ ≤ cstar / 1000) (hπ : π ≤ cstar / 1000) :
    reflectedExponent O₀ H
      (normWidth Z (reflectionExtractedDivisor P j e 0))
      (normWidth Z (reflectionExtractedDivisor P j e 2))
      za v ell el (terminalDualWidth Z H za Nstar P j e) + π ≤
        F₀ - cstar / 4 := by
  have hH := physical_residual_width I (B * F * R) Pw Mk Rs hMk hprod Z M O₀ H Ck CO CH hZ hCk
    hCO hCH hk hpow hrow
  have hT := terminal_common_width I F B R Pw Mk Rs hI hF hB hR hPw hMk hRs hprod P hP j e hcost
    Z M O₀ H V za Nstar Ck CO CH Cf hZ hCk hCO hCH hCf hk hpow hrow hf
  have hT' := terminal_width_from_invariant (O₀ := O₀) (za := za) (η := η)
    (Td := terminalDualWidth Z H za Nstar P j e)
    (S₀ := normWidth Z (reflectionExtractedDivisor P j e 0))
    (B₀ := normWidth Z (reflectionExtractedDivisor P j e 2))
    hinv hF₀ hscale hV hh (hT.trans (by linarith))
  exact reflected_terminal_saving hinv (normWidth_nonneg Z hZ R hR) hM hO
    (normWidth_nonneg Z hZ _ (reflectionExtractedDivisor_ne_zero P hP j e 0))
    (normWidth_nonneg Z hZ _ (reflectionExtractedDivisor_ne_zero P hP j e 2))
    hz hzcap hv hl he hret (by linarith) hT' hc hmargin hd hη hτ hπ

end HeckePort.Moments

end
