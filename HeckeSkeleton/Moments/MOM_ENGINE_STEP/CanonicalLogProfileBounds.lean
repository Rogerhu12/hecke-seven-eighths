import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLogProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalProfileNormalizationInput
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedFamilyAtoms
import HeckeGeneral.Analysis.TraceMovingPhaseBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Bounds for the original log-norm profile multipliers

The original scale contributes its real power once.  Its logarithm and
the fixed offset contribute one constant Fourier phase of norm one.
The remaining moving profile is the usual complex norm-power profile.

Finite atom control is constructed directly: the arithmetic rows and
supports are the original fixed finite sets, the profile phase is
continuous, and its modulus is one.  Thus this part has Fourier order
zero, independently of the higher seminorm order needed to normalize
the profiles.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors ContDiff Topology

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

namespace CanonicalLogProfiles

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace Atom

variable (p : Atom V)

def spectralPower (ξ : V) : ℂ :=
  (p.exponent : ℂ) + Complex.I * ((2 * Real.pi * inner ℝ ξ p.direction : ℝ) : ℂ)

def scaleFactor (ξ : V) : ℂ :=
  ((p.scale ^ p.exponent : ℝ) : ℂ) *
    jointPhase ξ (p.offset + Real.log p.scale • p.direction)

theorem norm_scaleFactor (ξ : V) : ‖p.scaleFactor ξ‖ = p.scale ^ p.exponent := by
  rw [scaleFactor, norm_mul, norm_jointPhase, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos p.scale_pos p.exponent)]

/-- The imaginary power is exactly the original Fourier character,
with its genuine `2 * pi` normalization. -/
theorem profilePower_spectralPower (ξ : V) {y : ℝ} (hy : 0 < y) :
    profilePower (p.spectralPower ξ) y =
      ((y ^ p.exponent : ℝ) : ℂ) * jointPhase ξ (Real.log y • p.direction) := by
  rw [profilePower, jointPhase, Real.fourierChar_apply, inner_smul_right,
    Real.rpow_def_of_pos hy, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [spectralPower, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

/-- Scale and offset are separated before any moving derivative bound
is used.  Only positive original profile arguments are asserted here. -/
theorem multiplier_eq_scaleFactor_profilePower (ξ : V) {y : ℝ} (hy : 0 < y) :
    p.multiplier ξ y = p.scaleFactor ξ * profilePower (p.spectralPower ξ) y := by
  have hlocation : p.location y =
      (p.offset + Real.log p.scale • p.direction) + Real.log y • p.direction := by
    simp only [location, Real.log_mul p.scale_pos.ne' hy.ne', add_smul, add_assoc]
  rw [multiplier, hlocation, jointPhase_add,
    Real.mul_rpow p.scale_pos.le hy.le, Complex.ofReal_mul,
    p.profilePower_spectralPower ξ hy, scaleFactor]
  ring

/-- At fixed original norm argument only the unit Fourier phase moves. -/
theorem multiplier_eq_zero_mul_phase (ξ : V) (y : ℝ) :
    p.multiplier ξ y = p.multiplier 0 y * jointPhase ξ (p.location y) := by
  simp only [multiplier, jointPhase, inner_zero_left, AddChar.map_zero_eq_one,
    Circle.coe_one, mul_one]

theorem continuous_multiplier (y : ℝ) : Continuous (fun ξ : V => p.multiplier ξ y) :=
  continuous_const.mul (continuous_jointPhase (p.location y))

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

theorem actualPlainAtom_phase (d : MomentData K ω ψ)
    (W : IdealTest K) (positive : PositivePlainProfile W)
    (u I : NonzeroIdeal K) (N t : ℝ) (ξ : V) :
    actualPlainAtom d (p.idealTest W positive ξ) u N t I =
      actualPlainAtom d (p.idealTest W positive 0) u N t I *
        jointPhase ξ (p.location (idealNorm K I / N)) := by
  by_cases hI : I ∈ W.support u t N
  · simp only [actualPlainAtom, idealTest, if_pos hI,
      p.multiplier_eq_zero_mul_phase ξ]
    ring
  · simp only [actualPlainAtom, idealTest, if_neg hI, zero_mul]

theorem norm_actualPlainAtom (d : MomentData K ω ψ)
    (W : IdealTest K) (positive : PositivePlainProfile W)
    (u I : NonzeroIdeal K) (N t : ℝ) (ξ : V) :
    ‖actualPlainAtom d (p.idealTest W positive ξ) u N t I‖ =
      ‖actualPlainAtom d (p.idealTest W positive 0) u N t I‖ := by
  rw [p.actualPlainAtom_phase d W positive u I N t ξ, norm_mul, norm_jointPhase, mul_one]

theorem continuous_actualPlainAtom (d : MomentData K ω ψ)
    (W : IdealTest K) (positive : PositivePlainProfile W)
    (u I : NonzeroIdeal K) (N t : ℝ) :
    Continuous (fun ξ : V => actualPlainAtom d (p.idealTest W positive ξ) u N t I) := by
  have he : (fun ξ : V => actualPlainAtom d (p.idealTest W positive ξ) u N t I) =
      (fun ξ : V => actualPlainAtom d (p.idealTest W positive 0) u N t I *
        jointPhase ξ (p.location (idealNorm K I / N))) := by
    funext ξ
    exact p.actualPlainAtom_phase d W positive u I N t ξ
  rw [he]
  exact continuous_const.mul (continuous_jointPhase _)

end Atom

section AnnularDerivatives

open Function

private theorem compact_positive_derivative_bound {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (hf : ∀ y : ℝ, 0 < y → ContDiffAt ℝ ∞ f y)
    (window : Set ℝ) (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (J : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ y ∈ window, ∀ n : ℕ, n ≤ J →
      ‖iteratedFDeriv ℝ n f y‖ ≤ C := by
  have hΩ : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
  have hfon : ContDiffOn ℝ ∞ f (Set.Ioi 0) :=
    fun y hy => (hf y hy).contDiffWithinAt
  have hbi (n : ℕ) : ∃ b : ℝ, ∀ y ∈ window,
      ‖iteratedFDerivWithin ℝ n f (Set.Ioi 0) y‖ ≤ b := by
    obtain ⟨b, hb⟩ := hcompact.bddAbove_image
      (((hfon.continuousOn_iteratedFDerivWithin (m := n) (by simp)
        hΩ.uniqueDiffOn).norm).mono hpositive)
    exact ⟨b, fun y hy => hb (Set.mem_image_of_mem _ hy)⟩
  choose b hb using hbi
  let C := 1 + ∑ n ∈ Finset.range (J + 1), max (b n) 0
  have hsum : 0 ≤ ∑ n ∈ Finset.range (J + 1), max (b n) 0 :=
    Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, fun y hy n hn => ?_⟩
  have hsingle := Finset.single_le_sum
    (fun i (_ : i ∈ Finset.range (J + 1)) => le_max_right (b i) 0)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  have hbC : b n ≤ C := by dsimp [C]; linarith [le_max_left (b n) 0]
  have hbound := (hb n y hy).trans hbC
  rwa [iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn
    ((hf y (hpositive hy)).of_le (by simp)) (hpositive hy)] at hbound

private def logPhase (ν y : ℝ) : ℂ := traceRealMovingPhase ν (Real.log y)

private theorem logPhase_smoothAt (ν : ℝ) {y : ℝ} (hy : 0 < y) :
    ContDiffAt ℝ ∞ (logPhase ν) y :=
  (contDiff_traceRealMovingPhase ν).contDiffAt.comp y (Real.contDiffAt_log.mpr hy.ne')

private theorem logPhase_smoothOn (ν : ℝ) :
    ContDiffOn ℝ ∞ (logPhase ν) (Set.Ioi 0) :=
  fun _ hy => (logPhase_smoothAt ν hy).contDiffWithinAt

/-- All derivative constants are selected from the fixed positive
window before the imaginary height. -/
private theorem compact_logPhase_derivative_bound
    (window : Set ℝ) (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : ℝ, ∀ y ∈ window, ∀ n : ℕ, n ≤ J →
      ‖iteratedFDeriv ℝ n (logPhase ν) y‖ ≤ C * (1 + |ν|) ^ J := by
  obtain ⟨D, hD, hlog⟩ := compact_positive_derivative_bound Real.log
    (fun _ hy => Real.contDiffAt_log.mpr hy.ne') window hcompact hpositive J
  have hD0 := zero_le_one.trans hD
  have hΩ : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
  have hlogon : ContDiffOn ℝ ∞ Real.log (Set.Ioi 0) :=
    fun _ hy => (Real.contDiffAt_log.mpr (ne_of_gt hy)).contDiffWithinAt
  refine ⟨(J.factorial : ℝ) * D ^ J, mul_nonneg (by positivity) (pow_nonneg hD0 _),
    fun ν y hy n hn => ?_⟩
  have hy0 := hpositive hy
  have hν : 1 ≤ 1 + |ν| := by linarith [abs_nonneg ν]
  have houter : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i (traceRealMovingPhase ν) Set.univ (Real.log y)‖ ≤
        (1 + |ν|) ^ J := by
    intro i hi
    rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_traceRealMovingPhase]
    exact (pow_le_pow_left₀ (abs_nonneg ν) (by linarith) _).trans
      (pow_le_pow_right₀ hν (hi.trans hn))
  have hinner : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i Real.log (Set.Ioi 0) y‖ ≤ D ^ i := by
    intro i hi hin
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn
      ((Real.contDiffAt_log.mpr hy0.ne').of_le (by simp)) hy0]
    exact (hlog y hy i (hin.trans hn)).trans (le_self_pow₀ hD (by omega))
  have hc := norm_iteratedFDerivWithin_comp_le (contDiff_traceRealMovingPhase ν).contDiffOn
    hlogon (show (n : ℕ∞ω) ≤ ∞ by simp) uniqueDiffOn_univ hΩ.uniqueDiffOn
    (Set.mapsTo_univ _ (Set.Ioi 0)) hy0 houter hinner
  change ‖iteratedFDerivWithin ℝ n (logPhase ν) (Set.Ioi 0) y‖ ≤ _ at hc
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn
    ((logPhase_smoothAt ν hy0).of_le (by simp)) hy0] at hc
  have hfac : (n.factorial : ℝ) ≤ J.factorial := by exact_mod_cast Nat.factorial_le hn
  calc
    _ ≤ (n.factorial : ℝ) * (1 + |ν|) ^ J * D ^ n := hc
    _ ≤ (J.factorial : ℝ) * (1 + |ν|) ^ J * D ^ J :=
      mul_le_mul (mul_le_mul_of_nonneg_right hfac (pow_nonneg (by positivity) _))
        (pow_le_pow_right₀ hD hn) (pow_nonneg hD0 _)
        (mul_nonneg (by positivity) (pow_nonneg (by positivity) _))
    _ = ((J.factorial : ℝ) * D ^ J) * (1 + |ν|) ^ J := by ring

def normalShape (δ ν y : ℝ) : ℂ := ((y ^ δ : ℝ) : ℂ) * logPhase ν y

private theorem realPower_smoothAt (δ : ℝ) {y : ℝ} (hy : 0 < y) :
    ContDiffAt ℝ ∞ (fun x : ℝ => ((x ^ δ : ℝ) : ℂ)) y :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp y
    (Real.contDiffAt_rpow_const_of_ne hy.ne')

theorem normalShape_smoothAt (δ ν : ℝ) {y : ℝ} (hy : 0 < y) :
    ContDiffAt ℝ ∞ (normalShape δ ν) y :=
  (realPower_smoothAt δ hy).mul (logPhase_smoothAt ν hy)

theorem normalShape_smoothOn (δ ν : ℝ) :
    ContDiffOn ℝ ∞ (normalShape δ ν) (Set.Ioi 0) :=
  fun _ hy => (normalShape_smoothAt δ ν hy).contDiffWithinAt

/-- The real part of the power is fixed first.  Leibniz and the actual
exponential derivatives give polynomial growth in its imaginary part. -/
theorem normalShape_derivative_bound
    (window : Set ℝ) (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (δ : ℝ) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : ℝ, ∀ y ∈ window, ∀ n : ℕ, n ≤ J →
      ‖iteratedFDeriv ℝ n (normalShape δ ν) y‖ ≤ C * (1 + |ν|) ^ J := by
  obtain ⟨R, hR, hrpow⟩ := compact_positive_derivative_bound
    (fun y : ℝ => ((y ^ δ : ℝ) : ℂ)) (fun _ hy => realPower_smoothAt δ hy)
    window hcompact hpositive J
  obtain ⟨P, hP, hphase⟩ := compact_logPhase_derivative_bound window hcompact hpositive J
  have hR0 := zero_le_one.trans hR
  have hΩ : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
  refine ⟨(2 : ℝ) ^ J * R * P,
    mul_nonneg (mul_nonneg (by positivity) hR0) hP, fun ν y hy n hn => ?_⟩
  have hy0 := hpositive hy
  have hpon : ContDiffOn ℝ ∞ (fun y : ℝ => ((y ^ δ : ℝ) : ℂ)) (Set.Ioi 0) :=
    fun _ hx => (realPower_smoothAt δ hx).contDiffWithinAt
  have hb := norm_iteratedFDerivWithin_mul_le hpon (logPhase_smoothOn ν)
    hΩ.uniqueDiffOn hy0 (show (n : ℕ∞ω) ≤ ∞ by simp)
  change ‖iteratedFDerivWithin ℝ n (normalShape δ ν) (Set.Ioi 0) y‖ ≤ _ at hb
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn
    ((normalShape_smoothAt δ ν hy0).of_le (by simp)) hy0] at hb
  simp_rw [iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn
      ((realPower_smoothAt δ hy0).of_le (by simp)) hy0,
    iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn
      ((logPhase_smoothAt ν hy0).of_le (by simp)) hy0] at hb
  have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y : ℝ => ((y ^ δ : ℝ) : ℂ)) y‖ *
        ‖iteratedFDeriv ℝ (n - i) (logPhase ν) y‖ := hb
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * R * (P * (1 + |ν|) ^ J) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hrpow y hy i (hin.trans hn)) (Nat.cast_nonneg _))
        (hphase ν y hy (n - i) ((Nat.sub_le n i).trans hn))
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hR0)
    _ = (2 : ℝ) ^ n * R * (P * (1 + |ν|) ^ J) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
    _ ≤ (2 : ℝ) ^ J * R * (P * (1 + |ν|) ^ J) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hR0)
        (mul_nonneg hP (pow_nonneg (by positivity) _))
    _ = ((2 : ℝ) ^ J * R * P) * (1 + |ν|) ^ J := by ring

def shapeProduct (δ ν : ℝ) (φ : 𝓢(ℝ, ℂ)) (y : ℝ) : ℂ :=
  φ y * normalShape δ ν y

theorem tsupport_shapeProduct_subset (δ ν : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    tsupport (shapeProduct δ ν φ) ⊆ tsupport φ := tsupport_mul_subset_left

theorem shapeProduct_smooth (δ ν : ℝ) (φ : 𝓢(ℝ, ℂ))
    (hpositive : tsupport φ ⊆ Set.Ioi 0) : ContDiff ℝ ∞ (shapeProduct δ ν φ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y ∈ tsupport φ
  · exact φ.smooth'.contDiffAt.mul (normalShape_smoothAt δ ν (hpositive hy))
  · have hz : (φ : ℝ → ℂ) =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.mp hy
    have he : shapeProduct δ ν φ =ᶠ[𝓝 y] (fun _ => (0 : ℂ)) := by
      filter_upwards [hz] with x hx
      simp only [shapeProduct, hx, Pi.zero_apply, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

/-- The Schwartz representative is constructed by smooth extension
through the region where the original compact profile vanishes. -/
def shapeSchwartz (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (δ ν : ℝ) (φ : 𝓢(ℝ, ℂ))
    (hsupport : tsupport φ ⊆ window) : 𝓢(ℝ, ℂ) :=
  ((show HasCompactSupport (φ : ℝ → ℂ) from
    hcompact.of_isClosed_subset (isClosed_tsupport _) hsupport).mul_right
      (f' := normalShape δ ν)).toSchwartzMap
        (shapeProduct_smooth δ ν φ (hpositive ∘ hsupport))

@[simp] theorem shapeSchwartz_apply (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (δ ν : ℝ) (φ : 𝓢(ℝ, ℂ))
    (hsupport : tsupport φ ⊆ window) (y : ℝ) :
    shapeSchwartz window hcompact hpositive δ ν φ hsupport y =
      φ y * normalShape δ ν y := rfl

/-- All seminorm constants are fixed before the original Schwartz
profile and the moving imaginary power.  The only input from the
profile is one finite rectangle of its original seminorms. -/
theorem shapeSchwartz_seminorm_bound
    (window : Set ℝ) (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (δ : ℝ) (K J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν : ℝ) (φ : 𝓢(ℝ, ℂ))
      (hsupport : tsupport φ ⊆ window), ∀ k ≤ K, ∀ n ≤ J,
      SchwartzMap.seminorm ℂ k n (shapeSchwartz window hcompact hpositive δ ν φ hsupport) ≤
        C * (1 + |ν|) ^ J *
          (Finset.Iic (K, J)).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
  obtain ⟨D, hD, hshape⟩ := normalShape_derivative_bound window hcompact hpositive δ J
  refine ⟨(2 : ℝ) ^ J * D, mul_nonneg (by positivity) hD,
    fun ν φ hsupport k hk n hn => ?_⟩
  let P := (Finset.Iic (K, J)).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ
  let Q := D * (1 + |ν|) ^ J
  have hP : 0 ≤ P := apply_nonneg _ _
  have hQ : 0 ≤ Q := mul_nonneg hD (pow_nonneg (by positivity) _)
  have hfinal : 0 ≤ ((2 : ℝ) ^ J * D) * (1 + |ν|) ^ J * P := by positivity
  apply SchwartzMap.seminorm_le_bound ℂ k n _ hfinal
  intro y
  change ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (shapeProduct δ ν φ) y‖ ≤ _
  by_cases hy : y ∈ tsupport φ
  · have hywindow := hsupport hy
    have hy0 := hpositive hywindow
    have hΩ : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
    have hb := norm_iteratedFDerivWithin_mul_le φ.smooth'.contDiffOn
      (normalShape_smoothOn δ ν) hΩ.uniqueDiffOn hy0
      (show (n : ℕ∞ω) ≤ ∞ by simp)
    change ‖iteratedFDerivWithin ℝ n (shapeProduct δ ν φ) (Set.Ioi 0) y‖ ≤ _ at hb
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn
      (((shapeProduct_smooth δ ν φ (hpositive ∘ hsupport)).contDiffAt).of_le (by simp))
      hy0] at hb
    simp_rw [iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn
        (φ.smooth'.contDiffAt.of_le (by simp)) hy0,
      iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn
        ((normalShape_smoothAt δ ν hy0).of_le (by simp)) hy0] at hb
    have hweighted : ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (shapeProduct δ ν φ) y‖ ≤
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          (‖y‖ ^ k * ‖iteratedFDeriv ℝ i φ y‖) *
          ‖iteratedFDeriv ℝ (n - i) (normalShape δ ν) y‖ := by
      apply (mul_le_mul_of_nonneg_left hb (pow_nonneg (norm_nonneg _) _)).trans_eq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          (‖y‖ ^ k * ‖iteratedFDeriv ℝ i φ y‖) *
          ‖iteratedFDeriv ℝ (n - i) (normalShape δ ν) y‖ := hweighted
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * P * Q := by
        apply Finset.sum_le_sum
        intro i hi
        have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
        have hφ : ‖y‖ ^ k * ‖iteratedFDeriv ℝ i φ y‖ ≤ P :=
          (SchwartzMap.le_seminorm ℂ k i φ y).trans
            (Seminorm.le_finset_sup_apply
              (Finset.mem_Iic.mpr (show (k, i) ≤ (K, J) from ⟨hk, hin.trans hn⟩)))
        exact mul_le_mul (mul_le_mul_of_nonneg_left hφ (Nat.cast_nonneg _))
          (hshape ν y hywindow (n - i) ((Nat.sub_le n i).trans hn))
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hP)
      _ = (2 : ℝ) ^ n * P * Q := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
      _ ≤ (2 : ℝ) ^ J * P * Q :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hP) hQ
      _ = ((2 : ℝ) ^ J * D) * (1 + |ν|) ^ J * P := by dsimp only [Q]; ring
  · have hz : iteratedFDeriv ℝ n (shapeProduct δ ν φ) y = 0 := by
      apply Function.notMem_support.mp
      intro h
      exact hy ((tsupport_shapeProduct_subset δ ν φ) (support_iteratedFDeriv_subset n h))
    rw [hz, norm_zero, mul_zero]
    exact hfinal

/-- A prescribed finite target set determines the finite original
orders and the frequency degree before any profile is supplied. -/
theorem shapeSchwartz_finset_bound
    (window : Set ℝ) (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (δ : ℝ) (s : Finset (ℕ × ℕ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν : ℝ) (φ : 𝓢(ℝ, ℂ))
      (hsupport : tsupport φ ⊆ window),
      s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
          (shapeSchwartz window hcompact hpositive δ ν φ hsupport) ≤
        C * (1 + |ν|) ^ (s.sup Prod.snd) *
          (Finset.Iic (s.sup Prod.fst, s.sup Prod.snd)).sup
            (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
  obtain ⟨C, hC, hbound⟩ := shapeSchwartz_seminorm_bound window hcompact hpositive
    δ (s.sup Prod.fst) (s.sup Prod.snd)
  refine ⟨C, hC, fun ν φ hs => ?_⟩
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro p hp
  exact hbound ν φ hs p.1 (Finset.le_sup (f := Prod.fst) hp)
    p.2 (Finset.le_sup (f := Prod.snd) hp)

end AnnularDerivatives

/-- The finite original orders needed by a prescribed target family. -/
def sourceOrders (s : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  Finset.Iic (s.sup Prod.fst, s.sup Prod.snd)

theorem subset_sourceOrders (s : Finset (ℕ × ℕ)) : s ⊆ sourceOrders s := by
  intro p hp
  exact Finset.mem_Iic.mpr ⟨Finset.le_sup (f := Prod.fst) hp,
    Finset.le_sup (f := Prod.snd) hp⟩

/-- This coefficient is selected from the proved uniform derivative
estimate.  It has no scale, offset, profile, or Fourier argument. -/
def shapeCoefficient (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (δ : ℝ) (s : Finset (ℕ × ℕ)) : ℝ :=
  Classical.choose (shapeSchwartz_finset_bound window hcompact hpositive δ s)

theorem shapeCoefficient_nonneg (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (δ : ℝ) (s : Finset (ℕ × ℕ)) :
    0 ≤ shapeCoefficient window hcompact hpositive δ s :=
  (Classical.choose_spec (shapeSchwartz_finset_bound window hcompact hpositive δ s)).1

namespace Atom

variable (p : Atom V)

def frequency (ξ : V) : ℝ := 2 * Real.pi * inner ℝ ξ p.direction

theorem phase_log_eq (ξ : V) (y : ℝ) :
    jointPhase ξ (Real.log y • p.direction) = logPhase (p.frequency ξ) y := by
  simp only [jointPhase, Real.fourierChar_apply, inner_smul_right, logPhase,
    traceRealMovingPhase, frequency, Complex.ofReal_mul, Complex.ofReal_ofNat]
  congr 1
  ring

theorem normalShape_frequency (ξ : V) {y : ℝ} (hy : 0 < y) :
    normalShape p.exponent (p.frequency ξ) y = profilePower (p.spectralPower ξ) y := by
  rw [p.profilePower_spectralPower ξ hy, p.phase_log_eq ξ y]
  rfl

theorem one_add_abs_frequency_le (ξ : V) :
    1 + |p.frequency ξ| ≤ (1 + 2 * Real.pi * ‖p.direction‖) * (1 + ‖ξ‖) := by
  have hπ : 0 ≤ 2 * Real.pi := mul_nonneg (by norm_num) Real.pi_pos.le
  have hinner := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm ξ p.direction) hπ
  have hf : |p.frequency ξ| = 2 * Real.pi * |inner ℝ ξ p.direction| := by
    rw [frequency, abs_mul, abs_of_nonneg hπ]
  rw [hf]
  nlinarith [norm_nonneg ξ, norm_nonneg p.direction,
    mul_nonneg hπ (norm_nonneg p.direction)]

/-- A literal Schwartz representative of the original multiplier,
including the original real scale power and its constant unit phase. -/
def schwartz (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (ξ : V) (φ : 𝓢(ℝ, ℂ))
    (hsupport : tsupport φ ⊆ window) : 𝓢(ℝ, ℂ) :=
  p.scaleFactor ξ • shapeSchwartz window hcompact hpositive
    p.exponent (p.frequency ξ) φ hsupport

@[simp] theorem schwartz_apply (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (ξ : V) (φ : 𝓢(ℝ, ℂ))
    (hsupport : tsupport φ ⊆ window) (y : ℝ) :
    p.schwartz window hcompact hpositive ξ φ hsupport y = φ y * p.multiplier ξ y := by
  change p.scaleFactor ξ * (φ y * normalShape p.exponent (p.frequency ξ) y) = _
  by_cases hy : y ∈ tsupport φ
  · rw [p.normalShape_frequency ξ (hpositive (hsupport hy)),
      p.multiplier_eq_scaleFactor_profilePower ξ (hpositive (hsupport hy))]
    ring
  · have hz : φ y = 0 := Function.notMem_support.mp
      (fun h => hy (subset_tsupport φ h))
    rw [hz, zero_mul, mul_zero, zero_mul]

theorem support_schwartz_subset (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (ξ : V) (φ : 𝓢(ℝ, ℂ))
    (hsupport : tsupport φ ⊆ window) :
    Function.support (p.schwartz window hcompact hpositive ξ φ hsupport) ⊆ window := by
  intro y hy
  apply hsupport
  apply subset_tsupport φ
  rw [Function.mem_support, p.schwartz_apply] at hy
  exact left_ne_zero_of_mul hy

/-- The scale power is paid once and the offset is free.  The remaining
coefficient depends on the fixed direction and the requested order. -/
def profileCoefficient (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (s : Finset (ℕ × ℕ)) : ℝ :=
  shapeCoefficient window hcompact hpositive p.exponent s * p.scale ^ p.exponent *
    (1 + 2 * Real.pi * ‖p.direction‖) ^ (s.sup Prod.snd)

theorem profileCoefficient_nonneg (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (s : Finset (ℕ × ℕ)) :
    0 ≤ p.profileCoefficient window hcompact hpositive s :=
  mul_nonneg
    (mul_nonneg (shapeCoefficient_nonneg window hcompact hpositive p.exponent s)
      (Real.rpow_nonneg p.scale_pos.le _))
    (pow_nonneg (by positivity) _)

theorem schwartz_finset_bound (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (s : Finset (ℕ × ℕ))
    (ξ : V) (φ : 𝓢(ℝ, ℂ)) (hsupport : tsupport φ ⊆ window) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (p.schwartz window hcompact hpositive ξ φ hsupport) ≤
      p.profileCoefficient window hcompact hpositive s *
        (1 + ‖ξ‖) ^ (s.sup Prod.snd) *
          (sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
  have hbound :=
    (Classical.choose_spec (shapeSchwartz_finset_bound window hcompact hpositive p.exponent s)).2
      (p.frequency ξ) φ hsupport
  have hfreq := (pow_le_pow_left₀ (by positivity) (p.one_add_abs_frequency_le ξ)
    (s.sup Prod.snd)).trans_eq (mul_pow _ _ _)
  have hC := shapeCoefficient_nonneg window hcompact hpositive p.exponent s
  have hP : 0 ≤ (sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ := apply_nonneg _ _
  rw [schwartz, map_smul_eq_mul, p.norm_scaleFactor]
  apply (mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg p.scale_pos.le _)).trans
  calc
    _ ≤ p.scale ^ p.exponent *
        (shapeCoefficient window hcompact hpositive p.exponent s *
          ((1 + 2 * Real.pi * ‖p.direction‖) ^ (s.sup Prod.snd) *
            (1 + ‖ξ‖) ^ (s.sup Prod.snd)) *
              (sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfreq hC) hP)
        (Real.rpow_nonneg p.scale_pos.le _)
    _ = _ := by unfold profileCoefficient; ring

/-- This is the original-scale budget that the final producer pays.
The exponent must be chosen against the fixed `L` and `ε` before the
moving scale; no scale power is absorbed in a Schwartz seminorm. -/
theorem scaleCost_le (Z L ε : ℝ) (hZ : 1 ≤ Z) (hexponent : 0 ≤ p.exponent)
    (hscale : p.scale ≤ Z ^ L) (hbudget : L * p.exponent ≤ ε) :
    p.scale ^ p.exponent ≤ Z ^ ε := by
  calc
    _ ≤ (Z ^ L) ^ p.exponent := Real.rpow_le_rpow p.scale_pos.le hscale hexponent
    _ = Z ^ (L * p.exponent) := (Real.rpow_mul (zero_le_one.trans hZ) _ _).symm
    _ ≤ Z ^ ε := Real.rpow_le_rpow_of_exponent_le hZ hbudget

theorem profileCoefficient_le_scaleBudget
    (window : Set ℝ) (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (s : Finset (ℕ × ℕ)) (Z L ε : ℝ) (hZ : 1 ≤ Z) (hexponent : 0 ≤ p.exponent)
    (hscale : p.scale ≤ Z ^ L) (hbudget : L * p.exponent ≤ ε) :
    p.profileCoefficient window hcompact hpositive s ≤
      (shapeCoefficient window hcompact hpositive p.exponent s *
        (1 + 2 * Real.pi * ‖p.direction‖) ^ (s.sup Prod.snd)) * Z ^ ε := by
  unfold profileCoefficient
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (p.scaleCost_le Z L ε hZ hexponent hscale hbudget)
      (shapeCoefficient_nonneg window hcompact hpositive p.exponent s))
    (pow_nonneg (by positivity) _)).trans_eq
  ring

/-- Exact adjustment under the already prescribed plain clipping.
It changes only the input scale, before any Fourier parameter. -/
def rescaleArgument (c : ℝ) (hc : 0 < c) : Atom V :=
  { p with scale := p.scale * c, scale_pos := mul_pos p.scale_pos hc }

@[simp] theorem rescaleArgument_multiplier (c : ℝ) (hc : 0 < c) (ξ : V) (y : ℝ) :
    (p.rescaleArgument c hc).multiplier ξ y = p.multiplier ξ (c * y) := by
  simp only [multiplier, location, rescaleArgument, mul_assoc]

end Atom

theorem positive_scaleIdealTest {K : Type} [Field K] [NumberField K]
    (W : IdealTest K) (hW : PositivePlainProfile W) (c : ℝ) (hc : 0 < c) :
    PositivePlainProfile (scaleIdealTest W c hc) := by
  intro u t y hy
  have h : 0 < c * y := hW u t (c * y) (right_ne_zero_of_mul hy)
  rcases mul_pos_iff.mp h with h | h
  · exact h.2
  · exact (lt_asymm hc h.1).elim

namespace Atom

variable (p : Atom V)

theorem scaleIdealTest_idealTest {K : Type} [Field K] [NumberField K]
    (W : IdealTest K) (hW : PositivePlainProfile W) (c : ℝ) (hc : 0 < c) (ξ : V) :
    scaleIdealTest (p.idealTest W hW ξ) c hc =
      (p.rescaleArgument c hc).idealTest (scaleIdealTest W c hc)
        (positive_scaleIdealTest W hW c hc) ξ := by
  unfold scaleIdealTest idealTest
  congr 1
  funext u t y
  rw [p.rescaleArgument_multiplier]
  ring

end Atom

section FixedData

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable (d : MomentData K ω ψ)
variable (left right : Atom V) (slot : Fin d.geometry.slotCount → Atom V)
variable (hleft : PositivePlainProfile d.plainTest₁)
variable (hright : PositivePlainProfile d.plainTest₂)
variable (hslot : ∀ i, PositivePrimeProfile (d.geometry.slots i))

theorem restrict_data (keep : Finset (Fin d.geometry.slotCount)) (ξ : V) :
    (data d left right slot hleft hright hslot ξ).restrictSlots keep =
      data (d.restrictSlots keep) left right
        (fun i => slot (selectedSlotIndex keep i)) hleft hright
        (fun i => hslot (selectedSlotIndex keep i)) ξ := rfl

theorem clip_data (a : RealParameters) (Z : ℝ) (hZ : 0 < Z) (ξ : V) :
    clipPlainData (data d left right slot hleft hright hslot ξ) a Z hZ =
      data (clipPlainData d a Z hZ)
        (left.rescaleArgument (plainClippingFactor Z a.n₁) (plainClippingFactor_pos Z a.n₁ hZ))
        (right.rescaleArgument (plainClippingFactor Z a.n₂) (plainClippingFactor_pos Z a.n₂ hZ))
        slot
        (positive_scaleIdealTest d.plainTest₁ hleft (plainClippingFactor Z a.n₁)
          (plainClippingFactor_pos Z a.n₁ hZ))
        (positive_scaleIdealTest d.plainTest₂ hright (plainClippingFactor Z a.n₂)
          (plainClippingFactor_pos Z a.n₂ hZ)) hslot ξ := by
  simp only [clipPlainData, data]
  rw [left.scaleIdealTest_idealTest d.plainTest₁ hleft _ _ ξ,
    right.scaleIdealTest_idealTest d.plainTest₂ hright _ _ ξ]

/-- One explicit common amplitude pays the original scale powers of
all literal columns once.  It is fixed before the Fourier parameter. -/
def profileAmplitude (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (s : Finset (ℕ × ℕ)) (A : ℝ) : ℝ :=
  A * (1 + left.profileCoefficient window hcompact hpositive s +
    right.profileCoefficient window hcompact hpositive s +
      ∑ i, (slot i).profileCoefficient window hcompact hpositive s)

theorem profileAmplitude_nonneg (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (s : Finset (ℕ × ℕ)) {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ profileAmplitude d left right slot window hcompact hpositive s A := by
  have hL := left.profileCoefficient_nonneg window hcompact hpositive s
  have hR := right.profileCoefficient_nonneg window hcompact hpositive s
  have hS := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
    (slot i).profileCoefficient_nonneg window hcompact hpositive s)
  unfold profileAmplitude
  positivity

/-- The window is constructed from literal original representatives.
The global support clauses are solely about those original profiles;
their bounds are needed only on the prescribed row and height domains. -/
def rawWindow {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (s : Finset (ℕ × ℕ)) {A : ℝ} (hA : 0 ≤ A)
    (w : RawProfileWindow rowDomain heightDomain window (sourceOrders s) d A)
    (hleftSupport : ∀ u t, tsupport (w.leftRep u t) ⊆ window)
    (hrightSupport : ∀ u t, tsupport (w.rightRep u t) ⊆ window)
    (hslotSupport : ∀ i t, tsupport (w.primeRep i t) ⊆ window) (ξ : V) :
    RawProfileWindow rowDomain heightDomain window s
      (data d left right slot hleft hright hslot ξ)
      (profileAmplitude d left right slot window hcompact hpositive s A *
        (1 + ‖ξ‖) ^ (s.sup Prod.snd)) := by
  let C := 1 + left.profileCoefficient window hcompact hpositive s +
    right.profileCoefficient window hcompact hpositive s +
      ∑ i, (slot i).profileCoefficient window hcompact hpositive s
  have hL := left.profileCoefficient_nonneg window hcompact hpositive s
  have hR := right.profileCoefficient_nonneg window hcompact hpositive s
  have hslots : ∀ i, 0 ≤ (slot i).profileCoefficient window hcompact hpositive s :=
    fun i => (slot i).profileCoefficient_nonneg window hcompact hpositive s
  have hS := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hslots i)
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have hLC : left.profileCoefficient window hcompact hpositive s ≤ C := by
    dsimp only [C]; linarith
  have hRC : right.profileCoefficient window hcompact hpositive s ≤ C := by
    dsimp only [C]; linarith
  have hSC (i) : (slot i).profileCoefficient window hcompact hpositive s ≤ C := by
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hslots j)
      (Finset.mem_univ i)
    dsimp only [C]
    linarith
  have hpow : 1 ≤ (1 + ‖ξ‖) ^ (s.sup Prod.snd) :=
    one_le_pow₀ (by linarith [norm_nonneg ξ])
  have hAM : A ≤ profileAmplitude d left right slot window hcompact hpositive s A *
      (1 + ‖ξ‖) ^ (s.sup Prod.snd) := by
    change A ≤ (A * C) * (1 + ‖ξ‖) ^ (s.sup Prod.snd)
    exact (le_mul_of_one_le_right hA hC).trans
      (le_mul_of_one_le_right (mul_nonneg hA (zero_le_one.trans hC)) hpow)
  have hbound (p : Atom V) (hp : p.profileCoefficient window hcompact hpositive s ≤ C)
      (φ : 𝓢(ℝ, ℂ)) (hs : tsupport φ ⊆ window)
      (hb : (sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤ A) :
      s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (p.schwartz window hcompact hpositive ξ φ hs) ≤
        profileAmplitude d left right slot window hcompact hpositive s A *
          (1 + ‖ξ‖) ^ (s.sup Prod.snd) := by
    calc
      _ ≤ p.profileCoefficient window hcompact hpositive s *
          (1 + ‖ξ‖) ^ (s.sup Prod.snd) *
            (sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ :=
        p.schwartz_finset_bound window hcompact hpositive s ξ φ hs
      _ ≤ C * (1 + ‖ξ‖) ^ (s.sup Prod.snd) * A :=
        mul_le_mul (mul_le_mul_of_nonneg_right hp (pow_nonneg (by positivity) _)) hb
          (apply_nonneg _ _) (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (by positivity) _))
      _ = _ := by change C * _ * A = (A * C) * _; ring
  refine
    { inverseRep := w.inverseRep
      leftRep := fun u t => left.schwartz window hcompact hpositive ξ (w.leftRep u t)
        (hleftSupport u t)
      rightRep := fun u t => right.schwartz window hcompact hpositive ξ (w.rightRep u t)
        (hrightSupport u t)
      primeRep := fun i t => (slot i).schwartz window hcompact hpositive ξ (w.primeRep i t)
        (hslotSupport i t)
      inverse_eq := w.inverse_eq
      left_eq := ?_
      right_eq := ?_
      prime_eq := ?_
      inverse_support := w.inverse_support
      left_support := fun u _ t _ => left.support_schwartz_subset
        window hcompact hpositive ξ (w.leftRep u t) (hleftSupport u t)
      right_support := fun u _ t _ => right.support_schwartz_subset
        window hcompact hpositive ξ (w.rightRep u t) (hrightSupport u t)
      prime_support := fun i t _ => (slot i).support_schwartz_subset
        window hcompact hpositive ξ (w.primeRep i t) (hslotSupport i t)
      inverse_bound := ?_
      left_bound := fun u hu t ht => hbound left hLC _ _ (w.left_bound u hu t ht)
      right_bound := fun u hu t ht => hbound right hRC _ _ (w.right_bound u hu t ht)
      prime_bound := fun i t ht => hbound (slot i) (hSC i) _ _ (w.prime_bound i t ht) }
  · intro u t y
    change d.plainTest₁.profile u t y * left.multiplier ξ y = _
    rw [left.schwartz_apply, w.left_eq]
  · intro u t y
    change d.plainTest₂.profile u t y * right.multiplier ξ y = _
    rw [right.schwartz_apply, w.right_eq]
  · intro i t y
    change (d.geometry.slots i).profile t y * (slot i).multiplier ξ y = _
    rw [(slot i).schwartz_apply, w.prime_eq]
  · intro u hu t ht
    have hmono : s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (w.inverseRep u t) ≤
        (sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) (w.inverseRep u t) :=
      Seminorm.finset_sup_apply_le (apply_nonneg _ _)
        (fun p hp => Seminorm.le_finset_sup_apply (subset_sourceOrders s hp))
    exact hmono.trans ((w.inverse_bound u hu t ht).trans hAM)

theorem actualPrimeAtom_phase (u : NonzeroIdeal K) (i : Fin d.geometry.slotCount)
    (q : HeightOneSpectrum (𝓞 K)) (Z t : ℝ) (ξ : V) :
    actualPrimeAtom (data d left right slot hleft hright hslot ξ) i u Z t q =
      actualPrimeAtom (data d left right slot hleft hright hslot 0) i u Z t q *
        jointPhase ξ ((slot i).location
          ((Ideal.absNorm q.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length)) := by
  by_cases hq : q ∈ (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length)
  · simp only [actualPrimeAtom, data, Atom.primeWindow, if_pos hq,
      (slot i).multiplier_eq_zero_mul_phase ξ]
    ring
  · simp only [actualPrimeAtom, data, Atom.primeWindow, if_neg hq, zero_mul]

theorem norm_actualPrimeAtom (u : NonzeroIdeal K) (i : Fin d.geometry.slotCount)
    (q : HeightOneSpectrum (𝓞 K)) (Z t : ℝ) (ξ : V) :
    ‖actualPrimeAtom (data d left right slot hleft hright hslot ξ) i u Z t q‖ =
      ‖actualPrimeAtom (data d left right slot hleft hright hslot 0) i u Z t q‖ := by
  rw [actualPrimeAtom_phase d left right slot hleft hright hslot u i q Z t ξ,
    norm_mul, norm_jointPhase, mul_one]

theorem continuous_actualPrimeAtom (u : NonzeroIdeal K) (i : Fin d.geometry.slotCount)
    (q : HeightOneSpectrum (𝓞 K)) (Z t : ℝ) :
    Continuous (fun ξ : V =>
      actualPrimeAtom (data d left right slot hleft hright hslot ξ) i u Z t q) := by
  have he : (fun ξ : V =>
      actualPrimeAtom (data d left right slot hleft hright hslot ξ) i u Z t q) =
      (fun ξ : V =>
        actualPrimeAtom (data d left right slot hleft hright hslot 0) i u Z t q *
          jointPhase ξ ((slot i).location
            ((Ideal.absNorm q.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length))) := by
    funext ξ
    exact actualPrimeAtom_phase d left right slot hleft hright hslot u i q Z t ξ
  rw [he]
  exact continuous_const.mul (continuous_jointPhase _)

variable {X : Type*} [NormedAddCommGroup X] [MeasureSpace X] [BorelSpace X]

/-- All carriers and all numerical bounds are computed from the
original data at the fixed original time.  No atom estimate, moving
support or measurable-family certificate is supplied as an input. -/
def finiteControl (a : RealParameters) (Z t : ℝ)
    (parameter : X → V) (hparameter : Continuous parameter) :
    ActualFiniteFamilyControl
      (fun x => data d left right slot hleft hright hslot (parameter x))
      d.geometry.slotCount (fun _ => rfl) a Z (fun _ => t) := by
  let rows := pairedRows d a Z
  let S₁ := rows.biUnion (fun u => d.plainTest₁.support u t (Z ^ a.n₁))
  let S₂ := rows.biUnion (fun u => d.plainTest₂.support u t (Z ^ a.n₂))
  let S := fun i : Fin d.geometry.slotCount =>
    (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length)
  let d₀ := data d left right slot hleft hright hslot 0
  let B₁ := ∑ u ∈ rows, ∑ I ∈ S₁, ‖actualPlainAtom d₀ d₀.plainTest₁ u (Z ^ a.n₁) t I‖
  let B₂ := ∑ u ∈ rows, ∑ I ∈ S₂, ‖actualPlainAtom d₀ d₀.plainTest₂ u (Z ^ a.n₂) t I‖
  let B := fun i => ∑ u ∈ rows, ∑ q ∈ S i, ‖actualPrimeAtom d₀ i u Z t q‖
  have hsum {Y T : Type*} (r : Finset Y) (s : Finset T) (f : Y → T → ℂ)
      (u : Y) (hu : u ∈ r) (v : T) (hv : v ∈ s) :
      ‖f u v‖ ≤ ∑ y ∈ r, ∑ z ∈ s, ‖f y z‖ :=
    (Finset.single_le_sum (fun _ _ => norm_nonneg _) hv).trans
      (Finset.single_le_sum (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hu)
  refine
    { rows := rows
      plain₁ := S₁
      plain₂ := S₂
      primes := S
      rows_cover := fun _ _ h => h
      plain₁_cover := ?_
      plain₂_cover := ?_
      primes_cover := fun _ _ _ h => h
      order := 0
      plain₁Bound := B₁
      plain₂Bound := B₂
      primeBound := B
      plain₁_nonneg := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
      plain₂_nonneg := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
      prime_nonneg := fun _ =>
        Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
      row_measurable := ?_
      plain₁_measurable := ?_
      plain₂_measurable := ?_
      prime_measurable := ?_
      plain₁_bound := ?_
      plain₂_bound := ?_
      prime_bound := ?_ }
  · intro x u hu I hI
    exact Finset.mem_biUnion.mpr ⟨u, hu, hI⟩
  · intro x u hu I hI
    exact Finset.mem_biUnion.mpr ⟨u, hu, hI⟩
  · intro u _
    change AEStronglyMeasurable (fun _ : X => actualPairedRowIndicator d a Z u) volume
    exact aestronglyMeasurable_const
  · intro u _ I _
    exact ((left.continuous_actualPlainAtom d d.plainTest₁ hleft u I
      (Z ^ a.n₁) t).comp hparameter).aestronglyMeasurable
  · intro u _ I _
    exact ((right.continuous_actualPlainAtom d d.plainTest₂ hright u I
      (Z ^ a.n₂) t).comp hparameter).aestronglyMeasurable
  · intro u _ i q _
    exact ((continuous_actualPrimeAtom d left right slot hleft hright hslot u i q Z t).comp
      hparameter).aestronglyMeasurable
  · intro x u hu I hI
    change ‖actualPlainAtom d (left.idealTest d.plainTest₁ hleft (parameter x))
      u (Z ^ a.n₁) t I‖ ≤ B₁ * (1 + ‖x‖) ^ 0
    rw [left.norm_actualPlainAtom d d.plainTest₁ hleft u I (Z ^ a.n₁) t (parameter x),
      pow_zero, mul_one]
    exact hsum rows S₁ (fun u I => actualPlainAtom d₀ d₀.plainTest₁ u (Z ^ a.n₁) t I)
      u hu I hI
  · intro x u hu I hI
    change ‖actualPlainAtom d (right.idealTest d.plainTest₂ hright (parameter x))
      u (Z ^ a.n₂) t I‖ ≤ B₂ * (1 + ‖x‖) ^ 0
    rw [right.norm_actualPlainAtom d d.plainTest₂ hright u I (Z ^ a.n₂) t (parameter x),
      pow_zero, mul_one]
    exact hsum rows S₂ (fun u I => actualPlainAtom d₀ d₀.plainTest₂ u (Z ^ a.n₂) t I)
      u hu I hI
  · intro x u hu i q hq
    change ‖actualPrimeAtom (data d left right slot hleft hright hslot (parameter x))
      i u Z t q‖ ≤ B i * (1 + ‖x‖) ^ 0
    rw [norm_actualPrimeAtom d left right slot hleft hright hslot u i q Z t (parameter x),
      pow_zero, mul_one]
    exact hsum rows (S i) (fun u q => actualPrimeAtom d₀ i u Z t q) u hu q hq

/-- The actual clipping is performed first, then the already chosen
retained set is used verbatim.  Its finite-atom control is derived from
the same phase identities; this operation makes no capacity choice. -/
def retainedFiniteControl (a : RealParameters) (Z t : ℝ) (hZ : 0 < Z)
    (keep : Finset (Fin d.geometry.slotCount)) (target : RealParameters)
    (parameter : X → V) (hparameter : Continuous parameter) :
    ActualFiniteFamilyControl
      (fun x => (clipPlainData
        (data d left right slot hleft hright hslot (parameter x)) a Z hZ).restrictSlots keep)
      keep.card (fun _ => rfl) target Z (fun _ => t) := by
  let d' := (clipPlainData d a Z hZ).restrictSlots keep
  let left' := left.rescaleArgument (plainClippingFactor Z a.n₁)
    (plainClippingFactor_pos Z a.n₁ hZ)
  let right' := right.rescaleArgument (plainClippingFactor Z a.n₂)
    (plainClippingFactor_pos Z a.n₂ hZ)
  let slot' := fun i : Fin keep.card => slot (selectedSlotIndex keep i)
  have hl' : PositivePlainProfile d'.plainTest₁ :=
    positive_scaleIdealTest d.plainTest₁ hleft (plainClippingFactor Z a.n₁)
      (plainClippingFactor_pos Z a.n₁ hZ)
  have hr' : PositivePlainProfile d'.plainTest₂ :=
    positive_scaleIdealTest d.plainTest₂ hright (plainClippingFactor Z a.n₂)
      (plainClippingFactor_pos Z a.n₂ hZ)
  have hs' : ∀ i, PositivePrimeProfile (d'.geometry.slots i) :=
    fun i => hslot (selectedSlotIndex keep i)
  have he : (fun x => (clipPlainData
        (data d left right slot hleft hright hslot (parameter x)) a Z hZ).restrictSlots keep) =
      (fun x => data d' left' right' slot' hl' hr' hs' (parameter x)) := by
    funext x
    rw [clip_data d left right slot hleft hright hslot a Z hZ (parameter x), restrict_data]
  rw [he]
  exact finiteControl d' left' right' slot' hl' hr' hs' target Z t parameter hparameter

end FixedData

section ProductWindow

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (d : MomentData K ω ψ)
variable (left right : Atom (WithLp 2 (U × E)))
variable (slot : Fin d.geometry.slotCount → Atom (WithLp 2 (U × E)))
variable (hleft : PositivePlainProfile d.plainTest₁)
variable (hright : PositivePlainProfile d.plainTest₂)
variable (hslot : ∀ i, PositivePrimeProfile (d.geometry.slots i))

/-- The exact two-variable polynomial radius used by the capacity
producer dominates the real constructed profile family. -/
def polynomialWindow {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (s : Finset (ℕ × ℕ)) {A : ℝ} (hA : 0 ≤ A)
    (w : RawProfileWindow rowDomain heightDomain window (sourceOrders s) d A)
    (hleftSupport : ∀ u t, tsupport (w.leftRep u t) ⊆ window)
    (hrightSupport : ∀ u t, tsupport (w.rightRep u t) ⊆ window)
    (hslotSupport : ∀ i t, tsupport (w.primeRep i t) ⊆ window) (z : U × E) :
    RawProfileWindow rowDomain heightDomain window s
      (data d left right slot hleft hright hslot (WithLp.toLp 2 z))
      (polynomialProfileRadius
        (profileAmplitude d left right slot window hcompact hpositive s A)
        (s.sup Prod.snd) (s.sup Prod.snd) z) := by
  let w' := rawWindow d left right slot hleft hright hslot hcompact hpositive s hA w
    hleftSupport hrightSupport hslotSupport (WithLp.toLp 2 z)
  refine w'.mono ?_
  have hB := profileAmplitude_nonneg d left right slot window hcompact hpositive s hA
  have hb := mul_le_mul_of_nonneg_left (hilbert_product_polynomial_le (s.sup Prod.snd) z) hB
  exact hb.trans (by unfold polynomialProfileRadius; linarith)

/-- The canonical normalization therefore places the actual multiplier
profiles in the prescribed fixed unit ball.  All representatives above
are constructed; no transformed-window certificate is an input. -/
theorem normalized_polynomial_window
    {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (s : Finset (ℕ × ℕ)) {A : ℝ} (hA : 0 ≤ A)
    (w : RawProfileWindow rowDomain heightDomain window (sourceOrders s) d A)
    (hleftSupport : ∀ u t, tsupport (w.leftRep u t) ⊆ window)
    (hrightSupport : ∀ u t, tsupport (w.rightRep u t) ⊆ window)
    (hslotSupport : ∀ i t, tsupport (w.primeRep i t) ⊆ window) (z : U × E) :
    InFixedProfileWindow rowDomain heightDomain window s
      (normalizedMomentProfiles
        (data d left right slot hleft hright hslot (WithLp.toLp 2 z))
        (polynomialProfileRadius
          (profileAmplitude d left right slot window hcompact hpositive s A)
          (s.sup Prod.snd) (s.sup Prod.snd) z)
        (polynomialProfileRadius_pos _
          (profileAmplitude_nonneg d left right slot window hcompact hpositive s hA) _ _ z)) :=
  normalizedMomentProfiles_in_fixed_window _
    (polynomialWindow d left right slot hleft hright hslot hcompact hpositive s hA w
      hleftSupport hrightSupport hslotSupport z)

end ProductWindow

section ChosenChild

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {A : SArithmeticData K} {σ : K →+* ℂ} {H : Type*} {k : ℕ}
variable {X : Type*} [NormedAddCommGroup X] [MeasureSpace X] [BorelSpace X]

private theorem restrictSlots_lengthSelection_congr
    {d e : MomentData K ω ψ} (h : d = e) (n : ℕ)
    (hd : d.geometry.slotCount = n) (he : e.geometry.slotCount = n)
    (keep : Finset (Fin n)) :
    d.restrictSlots (lengthSelection d n hd keep) =
      e.restrictSlots (lengthSelection e n he keep) := by
  subst e
  rfl

/-- The selected child is an input already fixed by the capacity
producer.  Only literal identities for its original calibration data
and frozen time are needed to construct all of its finite-atom fields.
The removed set is read from that child and is never chosen anew. -/
def childFiniteControl {source : ActualAllocatedSource A V H k}
    (D : source.Calibration (σ := σ) ω ψ) {G : D.NormalizedCapacityData}
    (out : G.Child) (d : MomentData K ω ψ)
    (left right : Atom V) (slot : Fin d.geometry.slotCount → Atom V)
    (hleft : PositivePlainProfile d.plainTest₁)
    (hright : PositivePlainProfile d.plainTest₂)
    (hslot : ∀ i, PositivePrimeProfile (d.geometry.slots i))
    (hdata : ∀ ξ, D.data ξ = data d left right slot hleft hright hslot ξ)
    (t : ℝ) (ht : ∀ ξ, D.height ξ = t)
    (parameter : X → V) (hparameter : Continuous parameter) :
    ActualFiniteFamilyControl
      (fun x => out.rawData (parameter x)) out.retainedCount
      (fun x => out.raw_count (parameter x)) out.parameters source.base
      (fun x => D.height (parameter x)) := by
  have hcount : d.geometry.slotCount = source.allocation.keep.card := by
    have h := D.count 0
    rw [hdata 0] at h
    exact h
  let keep : Finset (Fin d.geometry.slotCount) :=
    lengthSelection d source.allocation.keep.card hcount (Finset.univ \ out.removed)
  have hcard : keep.card = out.retainedCount :=
    length_restrictSlots_count d source.allocation.keep.card hcount (Finset.univ \ out.removed)
  have hraw (ξ : V) : out.rawData ξ =
      (clipPlainData (data d left right slot hleft hright hslot ξ) D.parameters
        source.base (zero_lt_one.trans source.base_gt_one)).restrictSlots keep := by
    change (D.clippedData ξ).restrictSlots
      (lengthSelection (D.clippedData ξ) source.allocation.keep.card (D.count ξ)
        (Finset.univ \ out.removed)) = _
    exact restrictSlots_lengthSelection_congr
      (congrArg (fun e => clipPlainData e D.parameters source.base
        (zero_lt_one.trans source.base_gt_one)) (hdata ξ))
      source.allocation.keep.card (D.count ξ) hcount (Finset.univ \ out.removed)
  have hfamily : (fun x => out.rawData (parameter x)) =
      (fun x => (clipPlainData (data d left right slot hleft hright hslot (parameter x))
        D.parameters source.base (zero_lt_one.trans source.base_gt_one)).restrictSlots keep) :=
    funext (fun x => hraw (parameter x))
  have htime : (fun x => D.height (parameter x)) = (fun _ : X => t) :=
    funext (fun x => ht (parameter x))
  rw [hfamily, htime, ← hcard]
  exact retainedFiniteControl d left right slot hleft hright hslot
    D.parameters source.base t (zero_lt_one.trans source.base_gt_one) keep out.parameters
    parameter hparameter

end ChosenChild
end CanonicalLogProfiles
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.Atom.multiplier_eq_scaleFactor_profilePower
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.finiteControl
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.shapeSchwartz_finset_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.Atom.schwartz_finset_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.rawWindow
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.normalized_polynomial_window
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.retainedFiniteControl
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.childFiniteControl
