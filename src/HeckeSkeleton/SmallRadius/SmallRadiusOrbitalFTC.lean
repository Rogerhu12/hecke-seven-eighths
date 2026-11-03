import HeckeGeneral.Analysis.SUnitProfileEuler
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
An actual unit-log-interval Sobolev estimate for the S-local Haar orbital
profiles of every Euler iterate of a free Schwartz test (no Fourier transform
is applied).  The proof uses the existing actual FTC identity
`sUnitOrbitalProfile_exp_sub_eq_integral_euler`, not an assumed small-radius
bound.

The positive Mellin weight is also put inside the literal interval integral.
This module does NOT assert that the full weighted log-axis integral is
bounded by finitely many original Schwartz seminorms; that is the local
Tate/Haar step supplied by `ActualOrbitalPositiveMoment`.

This is the free-test (Fourier-free) form of the cached `SmallRadiusOrbitalFTC`
candidate: the profile `sUnitFourierLogEulerProfile K S φ ψ j` of
`traceSchwartzEulerIterCLM K j (traceSchwartzFourier K φ)` is replaced by the
profile `sUnitEulerLogProfile K S φ ψ j` of `traceSchwartzEulerIterCLM K j φ`.
-/

noncomputable section

namespace HeckeGeneral.Analysis.SmallRadiusOrbitalFTCDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic MeasureTheory Set
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- Log-radius profile of the actual `j`-th Euler iterate of the free test `φ`:
the genuine norm-one Haar orbital integral, evaluated at radius `exp v`. -/
def sUnitEulerLogProfile (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ) (j : ℕ) (v : ℝ) : ℂ :=
  sUnitOrbitalProfile K S
    (sLocalTensorTestFunction K S (traceSchwartzEulerIterCLM K j φ) ψ)
    (sUnitExpRadius v)

include Γ in
theorem continuous_logEulerProfile (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ) (j : ℕ) :
    Continuous (sUnitEulerLogProfile K S φ ψ j) :=
  continuous_sUnitOrbitalProfile_exp K S Γ
    (traceSchwartzEulerIterCLM K j φ) ψ hψ hψsupport

include Γ in
/-- The actual increment identity for the Euler profile. -/
theorem logEulerProfile_sub_eq_integral (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (j : ℕ) (t s : ℝ) (hts : t ≤ s) :
    sUnitEulerLogProfile K S φ ψ j s -
      sUnitEulerLogProfile K S φ ψ j t =
      ∫ u in Icc t s, sUnitEulerLogProfile K S φ ψ (j + 1) u := by
  simpa only [sUnitEulerLogProfile, traceSchwartzEulerIterCLM_succ] using
    sUnitOrbitalProfile_exp_sub_eq_integral_euler K S Γ
      (traceSchwartzEulerIterCLM K j φ) ψ hψ hψsupport t s hts

include Γ in
/-- A point of the actual profile is controlled by its own L1 mass and the
next Euler profile on a unit log interval. There is no radial threshold. -/
theorem norm_logEulerProfile_le_unit_interval (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ) (j : ℕ) (t : ℝ) :
    ‖sUnitEulerLogProfile K S φ ψ j t‖ ≤
      (∫ u in Icc t (t + 1), ‖sUnitEulerLogProfile K S φ ψ j u‖) +
        ∫ u in Icc t (t + 1), ‖sUnitEulerLogProfile K S φ ψ (j + 1) u‖ := by
  let P := sUnitEulerLogProfile K S φ ψ j
  let Q := sUnitEulerLogProfile K S φ ψ (j + 1)
  have hP : Continuous P := continuous_logEulerProfile K S Γ φ ψ hψ hψsupport j
  have hQ : Continuous Q := continuous_logEulerProfile K S Γ φ ψ hψ hψsupport (j + 1)
  have hPi : IntegrableOn (fun u => ‖P u‖) (Icc t (t + 1)) :=
    hP.norm.continuousOn.integrableOn_compact isCompact_Icc
  have hQi : IntegrableOn (fun u => ‖Q u‖) (Icc t (t + 1)) :=
    hQ.norm.continuousOn.integrableOn_compact isCompact_Icc
  let C : ℝ := ∫ u in Icc t (t + 1), ‖Q u‖
  have hpoint (s : ℝ) (hs : s ∈ Icc t (t + 1)) : ‖P t‖ ≤ ‖P s‖ + C := by
    have hi : P s - P t = ∫ u in Icc t s, Q u :=
      logEulerProfile_sub_eq_integral K S Γ φ ψ hψ hψsupport j t s hs.1
    have he : P t = P s - ∫ u in Icc t s, Q u := by linear_combination -hi
    have hsub : (∫ u in Icc t s, ‖Q u‖) ≤ C :=
      setIntegral_mono_set hQi
        (Filter.Eventually.of_forall fun u => norm_nonneg (Q u))
        (Filter.Eventually.of_forall fun u hu => ⟨hu.1, hu.2.trans hs.2⟩)
    calc
      ‖P t‖ = ‖P s - ∫ u in Icc t s, Q u‖ := congrArg norm he
      _ ≤ ‖P s‖ + ‖∫ u in Icc t s, Q u‖ := norm_sub_le _ _
      _ ≤ ‖P s‖ + ∫ u in Icc t s, ‖Q u‖ :=
        add_le_add le_rfl (norm_integral_le_integral_norm _)
      _ ≤ ‖P s‖ + C := add_le_add le_rfl hsub
  have hc : IntegrableOn (fun _ : ℝ => C) (Icc t (t + 1)) :=
    continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  have hconst : IntegrableOn (fun _ : ℝ => ‖P t‖) (Icc t (t + 1)) :=
    continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  have hb : (∫ _ in Icc t (t + 1), ‖P t‖) ≤ ∫ u in Icc t (t + 1), (‖P u‖ + C) :=
    setIntegral_mono_on hconst (hPi.add hc) measurableSet_Icc hpoint
  have hvol : volume.real (Icc t (t + 1)) = 1 := by
    rw [Real.volume_real_Icc]
    norm_num
  rw [setIntegral_const, hvol, one_smul,
    integral_add hPi hc, setIntegral_const, hvol, one_smul] at hb
  exact hb

include Γ in
/-- An arbitrary nonnegative Mellin exponent can be inserted without any
small-end or full-axis integrability premise. The remaining integral is
literal and over a compact interval, hence genuinely integrable. -/
theorem weighted_norm_logEulerProfile_le_unit_interval (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (j : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (t : ℝ) :
    Real.exp (ε * t) * ‖sUnitEulerLogProfile K S φ ψ j t‖ ≤
      ∫ u in Icc t (t + 1), Real.exp (ε * u) *
        (‖sUnitEulerLogProfile K S φ ψ j u‖ +
          ‖sUnitEulerLogProfile K S φ ψ (j + 1) u‖) := by
  let P := sUnitEulerLogProfile K S φ ψ j
  let Q := sUnitEulerLogProfile K S φ ψ (j + 1)
  have hP : Continuous P := continuous_logEulerProfile K S Γ φ ψ hψ hψsupport j
  have hQ : Continuous Q := continuous_logEulerProfile K S Γ φ ψ hψ hψsupport (j + 1)
  have hPi : IntegrableOn (fun u => ‖P u‖) (Icc t (t + 1)) :=
    hP.norm.continuousOn.integrableOn_compact isCompact_Icc
  have hQi : IntegrableOn (fun u => ‖Q u‖) (Icc t (t + 1)) :=
    hQ.norm.continuousOn.integrableOn_compact isCompact_Icc
  have hsum := norm_logEulerProfile_le_unit_interval K S Γ φ ψ hψ hψsupport j t
  change ‖P t‖ ≤ (∫ u in Icc t (t + 1), ‖P u‖) +
    ∫ u in Icc t (t + 1), ‖Q u‖ at hsum
  rw [← integral_add hPi hQi] at hsum
  have hweighted := mul_le_mul_of_nonneg_left hsum (Real.exp_pos (ε * t)).le
  rw [← integral_const_mul] at hweighted
  have hright : IntegrableOn
      (fun u => Real.exp (ε * u) * (‖P u‖ + ‖Q u‖)) (Icc t (t + 1)) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (hP.norm.add hQ.norm)).continuousOn.integrableOn_compact isCompact_Icc
  apply hweighted.trans
  apply setIntegral_mono_on ((hPi.add hQi).const_mul _) hright measurableSet_Icc
  intro u hu
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.1 hε))
    (add_nonneg (norm_nonneg _) (norm_nonneg _))

include Γ in
/-- The `n`-th log-radius derivative of the profile of the `j`-th Euler iterate
is the profile of the `(j + n)`-th Euler iterate. -/
theorem iteratedDeriv_sUnitEulerLogProfile (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (j n : ℕ) (t : ℝ) :
    iteratedDeriv n (sUnitEulerLogProfile K S φ ψ j) t =
      sUnitEulerLogProfile K S φ ψ (j + n) t := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ']
      have hd : deriv (sUnitEulerLogProfile K S φ ψ j) =
          sUnitEulerLogProfile K S φ ψ (j + 1) := by
        funext v
        exact (hasDerivAt_sUnitOrbitalProfile_eulerIter_exp K S Γ φ ψ hψ hψsupport j v).deriv
      rw [hd, ih (j + 1), show j + 1 + n = j + (n + 1) by omega]

end HeckeGeneral.Analysis.SmallRadiusOrbitalFTCDraft
