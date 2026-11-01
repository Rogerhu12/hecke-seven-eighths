import Expansion.DyadicSupport
import ExpansionDetector.FourierNormalized

/-! Exact passage from a dyadic pair source to a logarithmic Fourier
profile.  The compact logarithmic window is explicit and equals one on
every nonzero annular summand.  No factorization identity is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Expansion.Dyadic
open MeasureTheory
open scoped Classical BigOperators ContDiff FourierTransform SchwartzMap
open ExpansionDetector.Fourier

def logWindowRadius : ℝ := 2 * Real.log 2

theorem logWindowRadius_pos : 0 < logWindowRadius := by
  exact mul_pos (by norm_num) (Real.log_pos (by norm_num))

def logWindow (y : ℝ) : ℂ :=
  (cutoff (y / logWindowRadius) : ℂ) * (cutoff (-y / logWindowRadius) : ℂ)

theorem logWindow_smooth : ContDiff ℝ ∞ logWindow := by
  unfold logWindow
  have hc := Complex.ofRealCLM.contDiff.comp cutoff_smooth
  exact (hc.comp (by fun_prop)).mul (hc.comp (by fun_prop))

theorem logWindow_one {y : ℝ} (hy : |y| ≤ logWindowRadius) : logWindow y = 1 := by
  have hb := abs_le.mp hy
  have h1 : y / logWindowRadius ≤ 1 := (div_le_one logWindowRadius_pos).mpr hb.2
  have h2 : -y / logWindowRadius ≤ 1 :=
    (div_le_one logWindowRadius_pos).mpr (by linarith)
  simp [logWindow, cutoff_one h1, cutoff_one h2]

theorem logWindow_support :
    Function.support logWindow ⊆ Set.Icc (-2 * logWindowRadius) (2 * logWindowRadius) := by
  intro y hy
  have hp := mul_ne_zero_iff.mp hy
  have h1 : y / logWindowRadius < 2 := by
    apply lt_of_not_ge
    intro h
    exact hp.1 (by rw [cutoff_zero h]; simp)
  have h2 : -y / logWindowRadius < 2 := by
    apply lt_of_not_ge
    intro h
    exact hp.2 (by rw [cutoff_zero h]; simp)
  have h1' := (div_lt_iff₀ logWindowRadius_pos).mp h1
  have h2' := (div_lt_iff₀ logWindowRadius_pos).mp h2
  constructor <;> linarith

theorem logWindow_compact : HasCompactSupport logWindow :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc logWindow_support

theorem logWindow_tsupport :
    tsupport logWindow ⊆ Set.Icc (-(2 * logWindowRadius)) (2 * logWindowRadius) := by
  simpa only [tsupport, neg_mul] using closure_minimal logWindow_support isClosed_Icc

theorem logWindow_on_annular_product {x y : ℝ}
    (hx : annularProfile x ≠ 0) (hy : annularProfile y ≠ 0) :
    logWindow (Real.log x + Real.log y) = 1 := by
  have hx' := annular_scaled_support (D := 1) (by norm_num) (by simpa using hx)
  have hy' := annular_scaled_support (D := 1) (by norm_num) (by simpa using hy)
  simp only [mul_one] at hx' hy'
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hxl := Real.log_lt_log (by norm_num : (0 : ℝ) < 1 / 2) hx'.1
  have hyl := Real.log_lt_log (by norm_num : (0 : ℝ) < 1 / 2) hy'.1
  have hxu := Real.log_lt_log hx0 hx'.2
  have hyu := Real.log_lt_log hy0 hy'.2
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hhalf] at hxl hyl
  apply logWindow_one
  rw [abs_le]
  dsimp [logWindowRadius]
  constructor <;> linarith

def logProductProfile (F : ℝ → ℂ) (D E y : ℝ) : ℂ :=
  logWindow y * F (D * E * Real.exp y)

theorem logProductProfile_smooth (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (D E : ℝ) :
    ContDiff ℝ ∞ (logProductProfile F D E) := by
  unfold logProductProfile
  exact logWindow_smooth.mul (hF.comp (by fun_prop))

def logProductSchwartz (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (D E : ℝ) :
    SchwartzMap ℝ ℂ :=
  (logWindow_compact.mul_right (f' := fun y => F (D * E * Real.exp y))).toSchwartzMap
    (logProductProfile_smooth F hF D E)

/-- Multiplicative ideal norms become additive logarithmic coordinates. -/
theorem logProductProfile_at_pair (F : ℝ → ℂ) {x y D E : ℝ}
    (hD : 0 < D) (hE : 0 < E)
    (hx : annularProfile (x / D) ≠ 0) (hy : annularProfile (y / E) ≠ 0) :
    logProductProfile F D E (Real.log (x / D) + Real.log (y / E)) = F (x * y) := by
  have hxpos : 0 < x := by linarith [(annular_scaled_support hD hx).1]
  have hypos : 0 < y := by linarith [(annular_scaled_support hE hy).1]
  have hx0 : 0 < x / D := div_pos hxpos hD
  have hy0 : 0 < y / E := div_pos hypos hE
  rw [logProductProfile, logWindow_on_annular_product hx hy, one_mul,
    Real.exp_add, Real.exp_log hx0, Real.exp_log hy0]
  congr 1
  field_simp [hD.ne', hE.ne']

variable {ι κ : Type*}

def annularCoefficient (a : ι → ℂ) (N : ι → ℝ) (D : ℝ) (i : ι) : ℂ :=
  a i * annularProfile (N i / D)

theorem pairBlock_eq_logSource (S : Finset ι) (T : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (N : ι → ℝ) (M : κ → ℝ)
    (F : ℝ → ℂ) (j k : ℕ) :
    pairBlock (S ×ˢ T) (fun p => a p.1 * b p.2 * F (N p.1 * M p.2)) N M j k =
      ∑ i ∈ S, ∑ l ∈ T,
        annularCoefficient a N ((2 : ℝ) ^ j) i *
        annularCoefficient b M ((2 : ℝ) ^ k) l *
        logProductProfile F ((2 : ℝ) ^ j) ((2 : ℝ) ^ k)
          (Real.log (N i / (2 : ℝ) ^ j) + Real.log (M l / (2 : ℝ) ^ k)) := by
  unfold pairBlock
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hW : annularProfile (N i / (2 : ℝ) ^ j) = 0
  · simp [annularCoefficient, hW]
  by_cases hV : annularProfile (M l / (2 : ℝ) ^ k) = 0
  · simp [annularCoefficient, hV]
  rw [logProductProfile_at_pair F (by positivity) (by positivity) hW hV]
  unfold annularCoefficient
  ring

/-- A genuine finite dyadic source admits a common bounded frequency.  The
only analytic input is a smooth one-variable product profile F, which is
made Schwartz by the explicit fixed logarithmic window. -/
theorem exists_pairBlock_frequency (S : Finset ι) (T : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (N : ι → ℝ) (M : κ → ℝ)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (j k : ℕ)
    (R : ℝ) (hR : 0 < R) (order : ℕ) :
    let A := annularCoefficient a N ((2 : ℝ) ^ j)
    let B := annularCoefficient b M ((2 : ℝ) ^ k)
    let g := logProductSchwartz F hF ((2 : ℝ) ^ j) ((2 : ℝ) ^ k)
    ∃ t : ℝ, ‖t‖ ≤ R ∧
      ‖pairBlock (S ×ˢ T) (fun p => a p.1 * b p.2 * F (N p.1 * M p.2)) N M j k‖ ≤
        ((∑ i ∈ S, ‖A i‖) * (∑ l ∈ T, ‖B l‖)) / R ^ order *
          (∫ u : ℝ, (1 + ‖u‖) ^ order * ‖(𝓕 g) u‖) +
        (∫ u : ℝ, ‖(𝓕 g) u‖) *
          ‖phasePolynomial S A (fun i => Real.log (N i / (2 : ℝ) ^ j)) t *
            phasePolynomial T B (fun l => Real.log (M l / (2 : ℝ) ^ k)) t‖ := by
  dsimp only
  rw [pairBlock_eq_logSource]
  exact exists_bounded_frequency S T _ _ _ _
    (logProductSchwartz F hF ((2 : ℝ) ^ j) ((2 : ℝ) ^ k)) R hR order

end Expansion.Dyadic
