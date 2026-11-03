import Expansion.NormalizedDyadicExtraction
import ExpansionDetector.IdealFinitePair
import Expansion.TerminalTailBudget

/-! The literal ideal terminal source feeds the dyadic detector.  Its finite
set includes only nonzero ideals and the same multiplicative coefficient
homomorphism carries all deleted Euler factors and ramified zero masks. -/

set_option autoImplicit false
noncomputable section
namespace Expansion.Dyadic

open MeasureTheory UniqueFactorizationMonoid
open scoped NumberField Classical BigOperators ContDiff
open ExpansionDetector.IdealCutoff ExpansionDetector.Fourier

variable {K : Type*} [Field K] [NumberField K]

def idealNorm (I : Ideal (𝓞 K)) : ℝ := Ideal.absNorm I

def inverseRawCoefficient (w : Ideal (𝓞 K) →*₀ ℂ)
    (V : ℝ → ℂ) (D : ℝ) (I : Ideal (𝓞 K)) : ℂ :=
  (moebius I : ℂ) * V (idealNorm I / D) * w I

theorem nonzeroTerminalSet_norm_bounds {H : ℝ} (hH : 1 ≤ H)
    (I : Ideal (𝓞 K)) (hI : I ∈ nonzeroTerminalSet H) :
    1 ≤ idealNorm I ∧ idealNorm I ≤ (2 : ℝ) ^ dyadicCap (3 * H) := by
  obtain ⟨hcap, hne⟩ := (mem_nonzeroTerminalSet H I).mp hI
  have hlower : (1 : ℝ) ≤ idealNorm I := by
    change (1 : ℝ) ≤ (Ideal.absNorm I : ℝ)
    exact_mod_cast Nat.succ_le_iff.mpr
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hne))
  refine ⟨hlower, ?_⟩
  have hceil := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 2 * H)
  have hn : idealNorm I ≤ (⌈2 * H⌉₊ : ℝ) := by
    change (Ideal.absNorm I : ℝ) ≤ (⌈2 * H⌉₊ : ℝ)
    exact_mod_cast hcap
  have hlarge : idealNorm I ≤ 3 * H := by linarith
  exact hlarge.trans (le_two_pow_dyadicCap (by linarith : 0 < 3 * H))

/-- Every nonzero ideal in the full annular norm window of a selected
dyadic scale belongs to the enlarged ambient finite set. This is the
support premise needed to apply the smooth Mellin contour formula to the
actual witness polynomial, without a sharp truncation of its profile. -/
theorem terminal_ambient_covers_annular
    (H : ℝ) (hH : 1 ≤ H) (j : ℕ) (hj : j ≤ dyadicCap (3 * H))
    (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hNI : idealNorm I ≤ 2 * (2 : ℝ) ^ j) :
    I ∈ nonzeroTerminalSet (6 * H) := by
  have hdyad : (2 : ℝ) ^ j ≤ 6 * H :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj).trans
      (two_pow_terminal_dyadicCap_le hH)
  have hNraw : idealNorm I ≤ 2 * (6 * H) := hNI.trans (by linarith)
  have hN : idealNorm I ≤ (⌈2 * (6 * H)⌉₊ : ℝ) :=
    hNraw.trans (Nat.le_ceil (2 * (6 * H)))
  refine (mem_nonzeroTerminalSet (6 * H) I).mpr ⟨?_, hI⟩
  change (Ideal.absNorm I : ℝ) ≤ (⌈2 * (6 * H)⌉₊ : ℝ) at hN
  exact_mod_cast hN

theorem terminalProfile_smooth (V T : ℝ → ℂ)
    (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T) (D H Y : ℝ) :
    ContDiff ℝ ∞ (terminalProfile V T D H Y) := by
  have hexp : ContDiff ℝ ∞ (fun q : ℝ => (Real.exp (-q / Y) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (by fun_prop))
  exact (hexp.mul (contDiff_const.sub (hV.comp (by fun_prop)))).mul
    (hT.comp (by fun_prop))

theorem actual_terminal_eq_finitePairSource
    (w : Ideal (𝓞 K) →*₀ ℂ) (V T : ℝ → ℂ) (D H Y : ℝ) (hH : 0 < H)
    (hTzero : ∀ x : ℝ, 2 ≤ x → T x = 0) (s : ℂ) :
    (∑ I ∈ terminalIdealSet H,
      terminalTerm w V T D H (fun n => (n : ℂ) ^ (-s) * (Real.exp (-(n : ℝ) / Y) : ℂ)) I) =
      finitePairSource (nonzeroTerminalSet H) (nonzeroTerminalSet H)
        (inverseRawCoefficient w V D) w idealNorm idealNorm
        (terminalProfile V T D H Y) s := by
  rw [finite_terminal_as_pair w V T D H Y hH hTzero s]
  unfold finitePairSource weightedCoefficient inverseRawCoefficient idealNorm
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [idealDirichletWeight_apply, Complex.ofReal_natCast]
  ring

/-- The actual finite ideal detector yields one dyadic pair and one common
Fourier frequency, with its explicit tail and exact central normalization.
The source premise is supplied by `actualIdeal_terminal_lower_of_zero`; it
is not a hypothesis about either inverse or plain witness polynomial. -/
theorem actual_terminal_normalized_frequency
    (w : Ideal (𝓞 K) →*₀ ℂ) (V T : ℝ → ℂ)
    (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T)
    (D H Y : ℝ) (hH : 1 ≤ H)
    (hTzero : ∀ x : ℝ, 2 ≤ x → T x = 0) (s : ℂ)
    (R : ℝ) (hR : 0 < R) (order : ℕ) (q : ℝ)
    (hq : q ≤ ‖∑ I ∈ terminalIdealSet H,
      terminalTerm w V T D H (fun n => (n : ℂ) ^ (-s) * (Real.exp (-(n : ℝ) / Y) : ℂ)) I‖) :
    let n := dyadicCap (3 * H)
    ∃ j ≤ n, ∃ k ≤ n, ∃ t : ℝ, ‖t‖ ≤ R ∧
      q ≤ ((n + 1 : ℕ) : ℝ) * (n + 1 : ℕ) *
        normalizedDyadicRHS (nonzeroTerminalSet H) (nonzeroTerminalSet H)
          (inverseRawCoefficient w V D) w idealNorm idealNorm
          (terminalProfile V T D H Y) (terminalProfile_smooth V T hV hT D H Y)
          s j k R order t := by
  rw [actual_terminal_eq_finitePairSource w V T D H Y (by linarith) hTzero s] at hq
  exact exists_normalized_dyadic_frequency (nonzeroTerminalSet H) (nonzeroTerminalSet H)
    (inverseRawCoefficient w V D) w idealNorm idealNorm
    (terminalProfile V T D H Y) (terminalProfile_smooth V T hV hT D H Y) s
    (dyadicCap (3 * H)) (dyadicCap (3 * H))
    (nonzeroTerminalSet_norm_bounds hH) (nonzeroTerminalSet_norm_bounds hH)
    R hR order q hq

/-- The finite terminal set is monotone in its norm cutoff. -/
theorem nonzeroTerminalSet_mono {H H' : ℝ} (h : H ≤ H') :
    nonzeroTerminalSet (K := K) H ⊆ nonzeroTerminalSet H' := by
  intro I hI
  obtain ⟨hN, hI0⟩ := (mem_nonzeroTerminalSet H I).mp hI
  exact (mem_nonzeroTerminalSet H' I).mpr
    ⟨hN.trans (Nat.ceil_mono (by linarith)), hI0⟩

/-- A nonzero literal terminal coefficient has both ideal coordinates
inside the original terminal support, irrespective of the ambient sum. -/
theorem terminal_pair_coefficient_mem
    (w : Ideal (𝓞 K) →*₀ ℂ) (V : ℝ → ℂ)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (D H Y : ℝ) (hH : 0 < H) (s : ℂ)
    (p : Ideal (𝓞 K) × Ideal (𝓞 K))
    (hp : weightedCoefficient (inverseRawCoefficient w V D) idealNorm s p.1 *
      weightedCoefficient w idealNorm s p.2 *
      terminalProfile V V D H Y (idealNorm p.1 * idealNorm p.2) ≠ 0) :
    p.1 ∈ nonzeroTerminalSet H ∧ p.2 ∈ nonzeroTerminalSet H := by
  have hterm := mul_ne_zero_iff.mp hp
  have hweights := mul_ne_zero_iff.mp hterm.1
  have hfirst : p.1 ≠ 0 := by
    intro hz
    apply hweights.1
    simp only [weightedCoefficient, inverseRawCoefficient, hz, map_zero, mul_zero, zero_mul]
  have hsecond : p.2 ≠ 0 := by
    intro hz
    apply hweights.2
    simp only [weightedCoefficient, hz, map_zero, zero_mul]
  have hn₁ : (1 : ℝ) ≤ idealNorm p.1 := by
    change (1 : ℝ) ≤ (Ideal.absNorm p.1 : ℝ)
    exact_mod_cast Nat.succ_le_iff.mpr
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hfirst))
  have hn₂ : (1 : ℝ) ≤ idealNorm p.2 := by
    change (1 : ℝ) ≤ (Ideal.absNorm p.2 : ℝ)
    exact_mod_cast Nat.succ_le_iff.mpr
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hsecond))
  have hprod : idealNorm p.1 * idealNorm p.2 < 2 * H := by
    have hV := (mul_ne_zero_iff.mp hterm.2).2
    have hh : idealNorm p.1 * idealNorm p.2 / H < 2 := by
      apply lt_of_not_ge
      intro hh
      exact hV (hzero _ hh)
    exact (div_lt_iff₀ hH).mp hh
  have hN₁ : idealNorm p.1 ≤ (⌈2 * H⌉₊ : ℝ) :=
    ((le_mul_of_one_le_right (zero_le_one.trans hn₁) hn₂).trans hprod.le).trans
      (Nat.le_ceil (2 * H))
  have hN₂ : idealNorm p.2 ≤ (⌈2 * H⌉₊ : ℝ) :=
    ((le_mul_of_one_le_left (zero_le_one.trans hn₂) hn₁).trans hprod.le).trans
      (Nat.le_ceil (2 * H))
  change (Ideal.absNorm p.1 : ℝ) ≤ (⌈2 * H⌉₊ : ℝ) at hN₁
  change (Ideal.absNorm p.2 : ℝ) ≤ (⌈2 * H⌉₊ : ℝ) at hN₂
  exact ⟨(mem_nonzeroTerminalSet H p.1).mpr ⟨by exact_mod_cast hN₁, hfirst⟩,
    (mem_nonzeroTerminalSet H p.2).mpr ⟨by exact_mod_cast hN₂, hsecond⟩⟩

/-- Enlarging the ambient finite set changes neither the terminal source
nor its original cutoff. The larger set will contain the FULL support of
every subsequently selected smooth annular polynomial. -/
theorem finitePairSource_terminal_enlarge
    (w : Ideal (𝓞 K) →*₀ ℂ) (V : ℝ → ℂ)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (D H H' Y : ℝ) (hH : 0 < H) (hHH' : H ≤ H') (s : ℂ) :
    finitePairSource (nonzeroTerminalSet H) (nonzeroTerminalSet H)
        (inverseRawCoefficient w V D) w idealNorm idealNorm (terminalProfile V V D H Y) s =
      finitePairSource (nonzeroTerminalSet H') (nonzeroTerminalSet H')
        (inverseRawCoefficient w V D) w idealNorm idealNorm (terminalProfile V V D H Y) s := by
  unfold finitePairSource
  rw [← Finset.sum_product', ← Finset.sum_product']
  apply Finset.sum_subset
    (Finset.product_subset_product (nonzeroTerminalSet_mono hHH') (nonzeroTerminalSet_mono hHH'))
  intro p _ hp
  by_contra hnonzero
  exact hp (Finset.mem_product.mpr
    (terminal_pair_coefficient_mem w V hzero D H Y hH s p hnonzero))

/-- Support of a nonzero dyadic block of the literal terminal source. This
uses the actual cutoff values, so it is valid for every cutoff satisfying
the stated plateau and vanishing properties. -/
theorem actual_terminal_pairBlock_scale_bounds
    (w : Ideal (𝓞 K) →*₀ ℂ) (V : ℝ → ℂ)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (D H Y : ℝ) (hD : 0 < D) (hH : 0 < H) (s : ℂ) (j k : ℕ)
    (S : Finset (Ideal (𝓞 K)))
    (hblock : pairBlock (S ×ˢ S)
      (fun p => weightedCoefficient (inverseRawCoefficient w V D) idealNorm s p.1 *
        weightedCoefficient w idealNorm s p.2 *
        terminalProfile V V D H Y (idealNorm p.1 * idealNorm p.2))
      idealNorm idealNorm j k ≠ 0) :
    (2 : ℝ) ^ j < 4 * D ∧
      D / 8 < (2 : ℝ) ^ j * (2 : ℝ) ^ k ∧
      (2 : ℝ) ^ j * (2 : ℝ) ^ k < 8 * H := by
  obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hblock
  have hp₁ := mul_ne_zero_iff.mp hp
  have hp₂ := mul_ne_zero_iff.mp hp₁.1
  have hterm := mul_ne_zero_iff.mp hp₂.1
  have hfirst := (mul_ne_zero_iff.mp hterm.1).1
  have hraw := (mul_ne_zero_iff.mp hfirst).1
  have hV := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hraw).1).2
  have hterminal := mul_ne_zero_iff.mp hterm.2
  have hcomplement := (mul_ne_zero_iff.mp hterminal.1).2
  have hx : idealNorm p.1 < 2 * D := by
    have hquot : idealNorm p.1 / D < 2 := by
      apply lt_of_not_ge
      intro hx
      exact hV (hzero _ hx)
    exact (div_lt_iff₀ hD).mp hquot
  have hxy : D / 2 < idealNorm p.1 * idealNorm p.2 := by
    have hquot : 1 < 2 * (idealNorm p.1 * idealNorm p.2) / D := by
      apply lt_of_not_ge
      intro hxy
      exact hcomplement (by rw [hone _ hxy]; ring)
    have hh := (lt_div_iff₀ hD).mp hquot
    linarith
  have hupper : idealNorm p.1 * idealNorm p.2 < 2 * H := by
    have hquot : idealNorm p.1 * idealNorm p.2 / H < 2 := by
      apply lt_of_not_ge
      intro hxy
      exact hterminal.2 (hzero _ hxy)
    exact (div_lt_iff₀ hH).mp hquot
  have hleft := annular_scaled_support (by positivity : 0 < (2 : ℝ) ^ j) hp₂.2
  have hright := annular_scaled_support (by positivity : 0 < (2 : ℝ) ^ k) hp₁.2
  have hxpos : 0 < idealNorm p.1 := by linarith [pow_pos (by norm_num : (0 : ℝ) < 2) j]
  have hypos : 0 < idealNorm p.2 := by linarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]
  have hprod_upper : idealNorm p.1 * idealNorm p.2 <
      (2 * (2 : ℝ) ^ j) * (2 * (2 : ℝ) ^ k) :=
    (mul_lt_mul_of_pos_right hleft.2 hypos).trans
      (mul_lt_mul_of_pos_left hright.2 (by positivity))
  have hprod_lower : ((2 : ℝ) ^ j / 2) * ((2 : ℝ) ^ k / 2) <
      idealNorm p.1 * idealNorm p.2 :=
    (mul_lt_mul_of_pos_right hleft.1 (by positivity : 0 < (2 : ℝ) ^ k / 2)).trans
      (mul_lt_mul_of_pos_left hright.1 hxpos)
  exact ⟨by linarith, by nlinarith, by nlinarith⟩

/-- The selected frequency retains the support geometry of the SAME large
dyadic block. In particular the total-length lower bound is obtained before
Fourier extraction and cannot be lost by choosing the common frequency. -/
theorem actual_terminal_normalized_frequency_with_support
    (w : Ideal (𝓞 K) →*₀ ℂ) (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (D H Y : ℝ) (hD : 0 < D) (hH : 1 ≤ H) (s : ℂ)
    (R : ℝ) (hR : 0 < R) (order : ℕ) (q : ℝ) (hqpos : 0 < q)
    (hq : q ≤ ‖∑ I ∈ terminalIdealSet H,
      terminalTerm w V V D H
        (fun n => (n : ℂ) ^ (-s) * (Real.exp (-(n : ℝ) / Y) : ℂ)) I‖) :
    let n := dyadicCap (3 * H)
    ∃ j ≤ n, ∃ k ≤ n,
      ((2 : ℝ) ^ j < 4 * D ∧ D / 8 < (2 : ℝ) ^ j * (2 : ℝ) ^ k ∧
        (2 : ℝ) ^ j * (2 : ℝ) ^ k < 8 * H) ∧
      ∃ t : ℝ, ‖t‖ ≤ R ∧
        q ≤ ((n + 1 : ℕ) : ℝ) * (n + 1 : ℕ) *
          normalizedDyadicRHS (nonzeroTerminalSet (6 * H)) (nonzeroTerminalSet (6 * H))
            (inverseRawCoefficient w V D) w idealNorm idealNorm
            (terminalProfile V V D H Y) (terminalProfile_smooth V V hV hV D H Y)
            s j k R order t := by
  let S := nonzeroTerminalSet (K := K) (6 * H)
  let n := dyadicCap (3 * H)
  let a := weightedCoefficient (inverseRawCoefficient w V D) idealNorm s
  let b := weightedCoefficient w idealNorm s
  let coeff : Ideal (𝓞 K) × Ideal (𝓞 K) → ℂ :=
    fun p => a p.1 * b p.2 * terminalProfile V V D H Y (idealNorm p.1 * idealNorm p.2)
  have hq' : q ≤ ‖∑ p ∈ S ×ˢ S, coeff p‖ := by
    rw [actual_terminal_eq_finitePairSource w V V D H Y (by linarith) hzero s] at hq
    rw [finitePairSource_terminal_enlarge w V hzero D H (6 * H) Y
      (by linarith) (by linarith) s] at hq
    simpa only [coeff, a, b, S, Finset.sum_product, finitePairSource] using hq
  have hN := nonzeroTerminalSet_norm_bounds (K := K) hH
  have hNbig := nonzeroTerminalSet_norm_bounds (K := K)
    (show 1 ≤ 6 * H by linarith)
  have hsupport (p : Ideal (𝓞 K) × Ideal (𝓞 K)) (hp : coeff p ≠ 0) :
      p.1 ∈ nonzeroTerminalSet H ∧ p.2 ∈ nonzeroTerminalSet H :=
    terminal_pair_coefficient_mem w V hzero D H Y (by linarith) s p hp
  obtain ⟨j, hj, k, hk, hlarge⟩ := exists_large_pairBlock (S ×ˢ S) coeff
    idealNorm idealNorm n n
    (fun p _ hp => hN p.1 (hsupport p hp).1)
    (fun p _ hp => hN p.2 (hsupport p hp).2) hq'
  have hblock : pairBlock (S ×ˢ S) coeff idealNorm idealNorm j k ≠ 0 := by
    intro hz
    rw [hz, norm_zero, mul_zero] at hlarge
    exact (not_le_of_gt hqpos) hlarge
  have hsupport := actual_terminal_pairBlock_scale_bounds w V hone hzero D H Y hD
    (by linarith) s j k S hblock
  obtain ⟨t, ht, hfreq⟩ := exists_pairBlock_frequency S S a b idealNorm idealNorm
    (terminalProfile V V D H Y) (terminalProfile_smooth V V hV hV D H Y) j k R hR order
  refine ⟨j, hj, k, hk, hsupport, t, ht, hlarge.trans ?_⟩
  have hcoefA : annularCoefficient a idealNorm ((2 : ℝ) ^ j) =
      sourceCoefficient (inverseRawCoefficient w V D) idealNorm annularProfile
        ((2 : ℝ) ^ j) s := rfl
  have hcoefB : annularCoefficient b idealNorm ((2 : ℝ) ^ k) =
      sourceCoefficient w idealNorm annularProfile ((2 : ℝ) ^ k) s := rfl
  rw [hcoefA, hcoefB, pair_phase_norm S S (inverseRawCoefficient w V D) w idealNorm idealNorm
    (fun I hI => zero_lt_one.trans_le (hNbig I hI).1)
    (fun I hI => zero_lt_one.trans_le (hNbig I hI).1)
    annularProfile annularProfile _ _ (by positivity) (by positivity)] at hfreq
  exact mul_le_mul_of_nonneg_left hfreq (by positivity)

end Expansion.Dyadic
