import HeckeGeneral.Analysis.TraceJointSchwartzCutoff
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Trigonometric

/-! The actual moving real frequency in the difference of the two arithmetic
log norms. This phase is separate from a fixed archimedean character. Its
derivative cost is proved from the exact exponential derivatives and the
actual compact-region log-norm derivatives, with constants selected before ν. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic Function
open scoped Classical ContDiff BigOperators nonZeroDivisors Topology

def traceRealMovingPhase (ν t : ℝ) : ℂ := Complex.exp (Complex.I * (ν : ℂ) * (t : ℂ))

theorem norm_traceRealMovingPhase (ν t : ℝ) : ‖traceRealMovingPhase ν t‖ = 1 := by
  simpa only [traceRealMovingPhase, mul_assoc, ← Complex.ofReal_mul] using
    Complex.norm_exp_I_mul_ofReal (ν * t)

theorem contDiff_traceRealMovingPhase (ν : ℝ) : ContDiff ℝ ∞ (traceRealMovingPhase ν) := by
  have h : ContDiff ℝ ∞ (fun t : ℝ => (Complex.I * (ν : ℂ)) * (t : ℂ)) :=
    contDiff_const.mul Complex.ofRealCLM.contDiff
  exact h.cexp

theorem hasDerivAt_traceRealMovingPhase (ν t : ℝ) :
    HasDerivAt (traceRealMovingPhase ν)
      ((Complex.I * (ν : ℂ)) * traceRealMovingPhase ν t) t := by
  have h := (((hasDerivAt_id t).ofReal_comp).const_mul (Complex.I * (ν : ℂ))).cexp
  unfold traceRealMovingPhase
  simpa only [id_eq, Complex.ofReal_one, mul_one, mul_comm] using h

theorem iteratedDeriv_traceRealMovingPhase (ν : ℝ) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (traceRealMovingPhase ν) t =
      (Complex.I * (ν : ℂ)) ^ n * traceRealMovingPhase ν t := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hd : deriv (traceRealMovingPhase ν) =
          fun u => (Complex.I * (ν : ℂ)) * traceRealMovingPhase ν u := by
        funext u
        exact (hasDerivAt_traceRealMovingPhase ν u).deriv
      rw [iteratedDeriv_succ', hd, iteratedDeriv_const_mul_field, ih, pow_succ]
      ring

theorem norm_iteratedFDeriv_traceRealMovingPhase (ν : ℝ) (n : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ n (traceRealMovingPhase ν) t‖ = |ν| ^ n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_traceRealMovingPhase]
  simp only [norm_mul, norm_pow, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, norm_traceRealMovingPhase, mul_one]

def traceLogDifferenceCLM : (ℝ × ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ

variable (K : Type) [Field K] [NumberField K]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Ω" => (Set.prod (traceArchRegular K) (traceArchRegular K))

def traceLogNormDifference : V × V → ℝ := traceLogDifferenceCLM ∘ traceJointLogNormMap K

@[simp] theorem traceLogNormDifference_apply (p : V × V) :
    traceLogNormDifference K p = traceArchLogNorm K p.1 - traceArchLogNorm K p.2 := rfl

def traceMovingPhase (ν : ℝ) : V × V → ℂ := traceRealMovingPhase ν ∘ traceLogNormDifference K

@[simp] theorem traceMovingPhase_apply (ν : ℝ) (p : V × V) :
    traceMovingPhase K ν p = Complex.exp
      (Complex.I * (ν : ℂ) * ((traceArchLogNorm K p.1 - traceArchLogNorm K p.2 : ℝ) : ℂ)) := rfl

theorem norm_traceMovingPhase (ν : ℝ) (p : V × V) : ‖traceMovingPhase K ν p‖ = 1 :=
  norm_traceRealMovingPhase _ _

theorem contDiffAt_traceLogNormDifference {p : V × V} (hp : p ∈ Ω) :
    ContDiffAt ℝ ∞ (traceLogNormDifference K) p :=
  traceLogDifferenceCLM.contDiff.contDiffAt.comp p (contDiffAt_traceJointLogNormMap K hp)

theorem contDiffOn_traceLogNormDifference : ContDiffOn ℝ ∞ (traceLogNormDifference K) Ω :=
  fun _ hp => (contDiffAt_traceLogNormDifference K hp).contDiffWithinAt

theorem contDiffAt_traceMovingPhase (ν : ℝ) {p : V × V} (hp : p ∈ Ω) :
    ContDiffAt ℝ ∞ (traceMovingPhase K ν) p :=
  (contDiff_traceRealMovingPhase ν).contDiffAt.comp p (contDiffAt_traceLogNormDifference K hp)

theorem contDiffOn_traceMovingPhase (ν : ℝ) : ContDiffOn ℝ ∞ (traceMovingPhase K ν) Ω :=
  fun _ hp => (contDiffAt_traceMovingPhase K ν hp).contDiffWithinAt

/-- The inner derivative constant is independent of the moving frequency. -/
theorem exists_traceLogNormDifference_compact_derivative_bound
    (A : Set (V × V)) (hA : IsCompact A) (hAΩ : A ⊆ Ω) (J : ℕ) :
    ∃ E : ℝ, 1 ≤ E ∧ ∀ p ∈ A, ∀ i : ℕ, 1 ≤ i → i ≤ J →
      ‖iteratedFDerivWithin ℝ i (traceLogNormDifference K) Ω p‖ ≤ E ^ i := by
  obtain ⟨D, hD, hb⟩ := exists_traceJointLogNormMap_compact_derivative_bound K A hA hAΩ J
  let L : ℝ := max 1 ‖traceLogDifferenceCLM‖
  have hL : 1 ≤ L := le_max_left _ _
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hLD : 1 ≤ L * D := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ L * D := mul_le_mul hL hD (by norm_num) hL0
  refine ⟨L * D, hLD, fun p hp i hi hiJ => ?_⟩
  have hpΩ := hAΩ hp
  have hΩ : IsOpen Ω := (isOpen_traceArchRegular K).prod (isOpen_traceArchRegular K)
  rw [traceLogNormDifference,
    traceLogDifferenceCLM.iteratedFDerivWithin_comp_left
      (contDiffOn_traceJointLogNormMap K p hpΩ) hΩ.uniqueDiffOn hpΩ (by simp)]
  calc
    _ ≤ ‖traceLogDifferenceCLM‖ *
        ‖iteratedFDerivWithin ℝ i (traceJointLogNormMap K) Ω p‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ L * D ^ i := mul_le_mul (le_max_right _ _) (hb p hp i hi hiJ)
      (norm_nonneg _) hL0
    _ ≤ L ^ i * D ^ i :=
      mul_le_mul_of_nonneg_right (le_self_pow₀ hL (by omega)) (pow_nonneg hD0 _)
    _ = (L * D) ^ i := (mul_pow _ _ _).symm

/-- Actual full derivatives of the moving phase on a fixed compact regular
region. The common constant is selected before ν and all evaluation points. -/
theorem exists_traceMovingPhase_compact_derivative_bound
    (A : Set (V × V)) (hA : IsCompact A) (hAΩ : A ⊆ Ω) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : ℝ, ∀ p ∈ A, ∀ n : ℕ, n ≤ J →
      ‖iteratedFDeriv ℝ n (traceMovingPhase K ν) p‖ ≤ C * (1 + |ν|) ^ J := by
  obtain ⟨D, hD, hinner⟩ :=
    exists_traceLogNormDifference_compact_derivative_bound K A hA hAΩ J
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  refine ⟨(J.factorial : ℝ) * D ^ J, mul_nonneg (by positivity) (pow_nonneg hD0 _),
    fun ν p hp n hn => ?_⟩
  have hpΩ := hAΩ hp
  have hΩ : IsOpen Ω := (isOpen_traceArchRegular K).prod (isOpen_traceArchRegular K)
  have hν : 1 ≤ 1 + |ν| := by linarith [abs_nonneg ν]
  have houter : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i (traceRealMovingPhase ν) Set.univ
        (traceLogNormDifference K p)‖ ≤ (1 + |ν|) ^ J := by
    intro i hi
    rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_traceRealMovingPhase]
    exact (pow_le_pow_left₀ (abs_nonneg ν) (by linarith) _).trans
      (pow_le_pow_right₀ hν (hi.trans hn))
  have hc := norm_iteratedFDerivWithin_comp_le (contDiff_traceRealMovingPhase ν).contDiffOn
    (contDiffOn_traceLogNormDifference K) (show (n : ℕ∞ω) ≤ ∞ by simp)
    uniqueDiffOn_univ hΩ.uniqueDiffOn (Set.mapsTo_univ _ Ω) hpΩ houter
    (fun i hi hin => hinner p hp i hi (hin.trans hn))
  change ‖iteratedFDerivWithin ℝ n (traceMovingPhase K ν) Ω p‖ ≤ _ at hc
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn
    ((contDiffAt_traceMovingPhase K ν hpΩ).of_le (by simp)) hpΩ] at hc
  have hfac : (n.factorial : ℝ) ≤ J.factorial := by exact_mod_cast Nat.factorial_le hn
  calc
    _ ≤ (n.factorial : ℝ) * (1 + |ν|) ^ J * D ^ n := hc
    _ ≤ (J.factorial : ℝ) * (1 + |ν|) ^ J * D ^ J :=
      mul_le_mul (mul_le_mul_of_nonneg_right hfac (pow_nonneg (by positivity) _))
        (pow_le_pow_right₀ hD hn) (pow_nonneg hD0 _)
        (mul_nonneg (by positivity) (pow_nonneg (by positivity) _))
    _ = ((J.factorial : ℝ) * D ^ J) * (1 + |ν|) ^ J := by ring

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

def traceMovingCutoffOrbitalKernel (ν : ℝ) (χ : V × V → ℂ) (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ) (R : {r : ℝ // 0 < r}) (p : V × V) : ℂ :=
  traceMovingPhase K ν p * traceCutoffOrbitalKernel K S χ φ ψ R p

theorem norm_traceMovingCutoffOrbitalKernel
    (ν : ℝ) (χ : V × V → ℂ) (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ) (R : {r : ℝ // 0 < r}) (p : V × V) :
    ‖traceMovingCutoffOrbitalKernel K S ν χ φ ψ R p‖ =
      ‖traceCutoffOrbitalKernel K S χ φ ψ R p‖ := by
  simp only [traceMovingCutoffOrbitalKernel, norm_mul, norm_traceMovingPhase, one_mul]

theorem tsupport_traceMovingCutoffOrbitalKernel_subset
    (ν : ℝ) (χ : V × V → ℂ) (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ) (R : {r : ℝ // 0 < r}) :
    tsupport (traceMovingCutoffOrbitalKernel K S ν χ φ ψ R) ⊆ tsupport χ :=
  tsupport_mul_subset_right.trans (tsupport_traceCutoffOrbitalKernel_subset K S χ φ ψ R)

theorem iteratedFDeriv_traceMovingCutoffOrbitalKernel_zero
    (ν : ℝ) (χ : V × V → ℂ) (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ) (R : {r : ℝ // 0 < r})
    (n : ℕ) {p : V × V} (hp : p ∉ tsupport χ) :
    iteratedFDeriv ℝ n (traceMovingCutoffOrbitalKernel K S ν χ φ ψ R) p = 0 := by
  apply notMem_support.mp
  intro h
  exact hp ((tsupport_traceMovingCutoffOrbitalKernel_subset K S ν χ φ ψ R)
    (support_iteratedFDeriv_subset n h))

include Γ in
theorem contDiff_traceMovingCutoffOrbitalKernel
    (ν : ℝ) (χ : V × V → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχΩ : tsupport χ ⊆ Ω)
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ) (R : {r : ℝ // 0 < r}) :
    ContDiff ℝ ∞ (traceMovingCutoffOrbitalKernel K S ν χ φ ψ R) := by
  have hH := contDiff_traceCutoffOrbitalKernel K S Γ χ hχ hχΩ φ ψ hψ hψsupport R
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p ∈ tsupport χ
  · exact (contDiffAt_traceMovingPhase K ν (hχΩ hp)).mul hH.contDiffAt
  · have hz : χ =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hp
    have hz' : traceMovingCutoffOrbitalKernel K S ν χ φ ψ R =ᶠ[𝓝 p]
        (fun _ => (0 : ℂ)) := by
      filter_upwards [hz] with q hq
      simp only [traceMovingCutoffOrbitalKernel, traceCutoffOrbitalKernel, hq,
        Pi.zero_apply, zero_mul, mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq hz'

/-- The moving phase still gives an actual Schwartz function after the fixed
compact cutoff; no smoothness of the phase on the coordinate hyperplanes is used. -/
def traceMovingCutoffOrbitalSchwartz
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (χ : V × V → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupport : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) : SchwartzMap (V × V) ℂ :=
  ((hasCompactSupport_traceCutoffOrbitalKernel K S χ hχsupport φ ψ R).mul_left
    (f := traceMovingPhase K ν)).toSchwartzMap
      (contDiff_traceMovingCutoffOrbitalKernel K S Γ ν χ hχ hχΩ φ ψ hψ hψsupport R)

@[simp] theorem traceMovingCutoffOrbitalSchwartz_apply
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (χ : V × V → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupport : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) (p : V × V) :
    traceMovingCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport χ hχ hχsupport hχΩ ν φ R p =
      traceMovingPhase K ν p * (χ p * traceJointOrbitalKernel K S φ ψ R p) := rfl

include Γ in
theorem weighted_norm_iteratedFDeriv_traceMovingCutoffOrbitalKernel_le
    (ν : ℝ) (χ : V × V → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχΩ : tsupport χ ⊆ Ω)
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (R : {r : ℝ // 0 < r}) (k n : ℕ) {p : V × V} (hp : p ∈ Ω) :
    ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (traceMovingCutoffOrbitalKernel K S ν χ φ ψ R) p‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (traceMovingPhase K ν) p‖ *
        (‖p‖ ^ k * ‖iteratedFDeriv ℝ (n - i) (traceCutoffOrbitalKernel K S χ φ ψ R) p‖) := by
  have hΩ : IsOpen Ω := (isOpen_traceArchRegular K).prod (isOpen_traceArchRegular K)
  have hphase := contDiffAt_traceMovingPhase K ν hp
  have hH := contDiff_traceCutoffOrbitalKernel K S Γ χ hχ hχΩ φ ψ hψ hψsupport R
  have hb := norm_iteratedFDerivWithin_mul_le (contDiffOn_traceMovingPhase K ν)
    hH.contDiffOn hΩ.uniqueDiffOn hp (show (n : ℕ∞ω) ≤ ∞ by simp)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn
    ((hphase.mul hH.contDiffAt).of_le (by simp)) hp] at hb
  simp_rw [iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn
      (hphase.of_le (by simp)) hp,
    iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn (hH.contDiffAt.of_le (by simp)) hp] at hb
  apply (mul_le_mul_of_nonneg_left hb (pow_nonneg (norm_nonneg _) _)).trans_eq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

local notation "Lattice" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

include Γ in
/-- The same fixed cutoff supports a uniform moving-frequency joint Schwartz
estimate. All choices precede ν, φ, and R. The radius threshold is inherited
from the fixed cutoff support and therefore has no moving-frequency dependence. -/
theorem exists_traceMovingCutoffOrbitalSchwartz_seminorm_power_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (χ : V × V → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupport : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (B : ℝ) (M : ℕ) (hM : Module.finrank ℤ Lattice < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * B ≤ M) (k J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
      ∀ n : ℕ, n ≤ J →
        SchwartzMap.seminorm ℝ k n
          (traceMovingCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport χ hχ hχsupport hχΩ ν φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-B) := by
  obtain ⟨s, C, R0, hC, hR0, hcutoff⟩ := exists_traceCutoffOrbitalSchwartz_seminorm_power_bound
    K S Γ ψ hψ hψsupport χ hχ hχsupport hχΩ B M hM hOrder k J
  obtain ⟨L, hL, hphase⟩ := exists_traceMovingPhase_compact_derivative_bound
    K (tsupport χ) hχsupport hχΩ J
  have hfactor : 0 ≤ (2 : ℝ) ^ J * L * C :=
    mul_nonneg (mul_nonneg (by positivity) hL) hC
  refine ⟨s, (2 : ℝ) ^ J * L * C, R0, hfactor, hR0, fun ν φ R hR n hn => ?_⟩
  let P : ℝ := L * (1 + |ν|) ^ J
  let Q : ℝ := C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B)
  have hP : 0 ≤ P := mul_nonneg hL (pow_nonneg (by positivity) _)
  have hQ : 0 ≤ Q :=
    mul_nonneg (mul_nonneg hC (apply_nonneg _ _)) (Real.rpow_nonneg R.property.le _)
  have hfinal : 0 ≤ ((2 : ℝ) ^ J * L * C) *
      s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-B) :=
    mul_nonneg (mul_nonneg (mul_nonneg hfactor (apply_nonneg _ _))
      (pow_nonneg (by positivity) _)) (Real.rpow_nonneg R.property.le _)
  apply SchwartzMap.seminorm_le_bound ℝ k n _ hfinal
  intro p
  change ‖p‖ ^ k * ‖iteratedFDeriv ℝ n
    (traceMovingCutoffOrbitalKernel K S ν χ φ ψ R) p‖ ≤ _
  by_cases hp : p ∈ tsupport χ
  · have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (traceMovingPhase K ν) p‖ *
          (‖p‖ ^ k * ‖iteratedFDeriv ℝ (n - i) (traceCutoffOrbitalKernel K S χ φ ψ R) p‖) :=
        weighted_norm_iteratedFDeriv_traceMovingCutoffOrbitalKernel_le
          K S Γ ν χ hχ hχΩ φ ψ hψ hψsupport R k n (hχΩ hp)
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * P * Q := by
        apply Finset.sum_le_sum
        intro i hi
        have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
        have hH : ‖p‖ ^ k * ‖iteratedFDeriv ℝ (n - i)
            (traceCutoffOrbitalKernel K S χ φ ψ R) p‖ ≤ Q :=
          (SchwartzMap.le_seminorm ℝ k (n - i)
            (traceCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport χ hχ hχsupport hχΩ φ R) p).trans
              (hcutoff φ R hR (n - i) ((Nat.sub_le n i).trans hn))
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hphase ν p hp i (hin.trans hn))
          (Nat.cast_nonneg _)) hH
          (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))
          (mul_nonneg (Nat.cast_nonneg _) hP)
      _ = (2 : ℝ) ^ n * P * Q := by rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
      _ ≤ (2 : ℝ) ^ J * P * Q :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hP) hQ
      _ = ((2 : ℝ) ^ J * L * C) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          (1 + |ν|) ^ J * R.val ^ (-B) := by dsimp [P, Q]; ring
  · rw [iteratedFDeriv_traceMovingCutoffOrbitalKernel_zero K S ν χ φ ψ R n hp,
      norm_zero, mul_zero]
    exact hfinal

end HeckeGeneral.Analysis
