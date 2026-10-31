import HeckeSkeleton.SmallRadius.SmallRadiusUniformPointBound
import HeckeGeneral.Analysis.TraceJointProfileBounds

/-!
UNCOMPILED / native 0. The actual one-log-axis positive-moment point bound
controls full multilinear derivatives of the genuine joint profile, for every
positive radius. Composition with the actual pair of archimedean log norms
then gives a bound on any fixed compact regular set. No bare two-log-axis L1
estimate, radius threshold, or transformed-test seminorm premise is used.
-/

noncomputable section

namespace HeckeGeneral.Analysis.SmallRadiusJointCompactDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Bridge
open SmallRadiusUniformPointDraft
open scoped Classical ContDiff BigOperators

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
  LanglandsTunnell.TateLocal.borelSpace_localBorel

variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : S, MeasurableSpace (v.val.adicCompletion K)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion K)ˣ]
variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Ω" => (Set.prod (traceArchRegular K) (traceArchRegular K))

include Γ in
/-- Fourier form of the weighted point bound: the Fourier transform is absorbed
into the finite family of original Schwartz seminorms by continuity of the
trace Fourier transform.  (The ported `SmallRadiusUniformPointBound` is stated
for the free test; the profile `sUnitFourierLogEulerProfile` is the free
profile of `traceSchwartzFourier K φ`.) -/
theorem exists_uniform_weighted_fourierLogEuler_point_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ φ : SchwartzMap V ℂ,
      ∀ j : ℕ, j ≤ J → ∀ t : ℝ,
        Real.exp (σ * t) * ‖sUnitFourierLogEulerProfile K S φ ψ j t‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
  obtain ⟨s₀, C₀, hC₀, hb₀⟩ :=
    exists_uniform_weighted_logEuler_point_bound K S Γ ψ hψ hψsupport σ hσ hσ1 J
  let q : Seminorm ℝ (SchwartzMap V ℂ) :=
    (s₀.sup (schwartzSeminormFamily ℝ V ℂ)).comp
      ((traceSchwartzFourierCLM K).restrictScalars ℝ).toLinearMap
  have hp := schwartz_withSeminorms ℝ V ℂ
  have hq : Continuous q :=
    (Seminorm.continuous_finsetSup (fun m _ => hp.continuous_seminorm m)).comp
      ((traceSchwartzFourierCLM K).restrictScalars ℝ).continuous
  obtain ⟨s, D, hD, hbound⟩ := Seminorm.bound_of_continuous hp q hq
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hD
  refine ⟨s, C₀ * (D : ℝ), mul_pos hC₀ hDpos, fun φ j hj t => ?_⟩
  have h1 := hb₀ (traceSchwartzFourier K φ) j hj t
  have h2 : s₀.sup (schwartzSeminormFamily ℝ V ℂ) (traceSchwartzFourier K φ) ≤
      (D : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := Seminorm.le_def.mp hbound φ
  have h3 : Real.exp (σ * t) * ‖sUnitFourierLogEulerProfile K S φ ψ j t‖ ≤
      C₀ * s₀.sup (schwartzSeminormFamily ℝ V ℂ) (traceSchwartzFourier K φ) := h1
  calc
    _ ≤ C₀ * s₀.sup (schwartzSeminormFamily ℝ V ℂ) (traceSchwartzFourier K φ) := h3
    _ ≤ C₀ * ((D : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ) :=
      mul_le_mul_of_nonneg_left h2 hC₀.le
    _ = _ := by ring

include Γ in
/-- Full joint derivatives through any chosen finite order, at every point of
the two-log plane. The loss is in the actual profile radius, not a claim of
integrability along the transverse log direction. -/
theorem exists_sUnitJointRadialProfile_iteratedFDeriv_allRadius_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, ∀ p : ℝ × ℝ,
      ∀ n : ℕ, n ≤ J →
        ‖iteratedFDeriv ℝ n (sUnitJointRadialProfile K S φ ψ R 0) p‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
            (Real.exp (Real.log R.val - p.1 - p.2)) ^ (-σ) := by
  obtain ⟨s, C, hC, hb⟩ := exists_uniform_weighted_fourierLogEuler_point_bound
    K S Γ ψ hψ hψsupport σ hσ hσ1 J
  let A : ℝ := max 1 ‖sUnitJointLogRadiusCLM‖
  have hA : 1 ≤ A := le_max_left _ _
  have hApos : 0 < A := zero_lt_one.trans_le hA
  refine ⟨s, C * A ^ J, mul_pos hC (pow_pos hApos _), fun φ R p n hn => ?_⟩
  let t : ℝ := Real.log R.val - p.1 - p.2
  have he : Real.exp (σ * t) * Real.exp (-(σ * t)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hrpow : Real.exp (-(σ * t)) = (Real.exp t) ^ (-σ) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]
    congr 1
    ring
  have hpoint := hb φ n hn t
  change Real.exp (σ * t) * ‖sUnitJointRadialProfile K S φ ψ R n p‖ ≤
    C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ at hpoint
  have hprof : ‖sUnitJointRadialProfile K S φ ψ R n p‖ ≤
      C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (Real.exp t) ^ (-σ) := by
    calc
      _ = (Real.exp (σ * t) * ‖sUnitJointRadialProfile K S φ ψ R n p‖) *
          Real.exp (-(σ * t)) := by rw [mul_right_comm, he, one_mul]
      _ ≤ (C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ) *
          Real.exp (-(σ * t)) :=
        mul_le_mul_of_nonneg_right hpoint (Real.exp_pos _).le
      _ = _ := by rw [hrpow]
  have hscale : ‖sUnitJointLogRadiusCLM‖ ^ n ≤ A ^ J :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ hA hn)
  calc
    _ ≤ ‖sUnitJointRadialProfile K S φ ψ R n p‖ * ‖sUnitJointLogRadiusCLM‖ ^ n :=
      norm_iteratedFDeriv_sUnitJointRadialProfile_le K S Γ φ ψ hψ hψsupport R n p
    _ ≤ (C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          (Real.exp t) ^ (-σ)) * A ^ J :=
      mul_le_mul hprof hscale (pow_nonneg (norm_nonneg _) _)
        (mul_nonneg (mul_nonneg hC.le (apply_nonneg _ _))
          (Real.rpow_nonneg (Real.exp_pos _).le _))
    _ = (C * A ^ J) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          (Real.exp (Real.log R.val - p.1 - p.2)) ^ (-σ) := by dsimp [t]; ring

include Γ in
/-- On any fixed compact subset of the actual two-column regular locus, every
full derivative through J is bounded by original Schwartz seminorms times
R^(-σ), for all R > 0. The constants precede the test, radius and order.
The inner log-norm derivative bounds come from compactness, with no threshold
on the true profile radius. -/
theorem exists_traceJointOrbitalKernel_compact_allRadius_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (A : Set (V × V)) (hA : IsCompact A) (hAΩ : A ⊆ Ω)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r},
      ∀ p ∈ A, ∀ n : ℕ, n ≤ J →
        ‖iteratedFDeriv ℝ n (traceJointOrbitalKernel K S φ ψ R) p‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-σ) := by
  let F := traceJointLogNormMap K
  let q : V × V → ℝ := fun p => traceArchProductNorm K p.1 * traceArchProductNorm K p.2
  have hq : Continuous q := ((continuous_traceArchProductNorm K).comp continuous_fst).mul
    ((continuous_traceArchProductNorm K).comp continuous_snd)
  have hqpos (p : V × V) (hp : p ∈ A) : 0 < q p :=
    mul_pos (traceArchProductNorm_pos K (hAΩ hp).1)
      (traceArchProductNorm_pos K (hAΩ hp).2)
  have hqσ : ContinuousOn (fun p => q p ^ σ) A :=
    hq.continuousOn.rpow_const (fun p hp => Or.inl (hqpos p hp).ne')
  obtain ⟨Z, hZ⟩ := hA.bddAbove_image hqσ
  let T : ℝ := max Z 1
  have hT : 0 < T := zero_lt_one.trans_le (le_max_right _ _)
  have hqT (p : V × V) (hp : p ∈ A) : q p ^ σ ≤ T :=
    (hZ (Set.mem_image_of_mem _ hp)).trans (le_max_left _ _)
  obtain ⟨D, hD, hinner⟩ :=
    exists_traceJointLogNormMap_compact_derivative_bound K A hA hAΩ J
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  obtain ⟨s, C, hC, houter⟩ :=
    exists_sUnitJointRadialProfile_iteratedFDeriv_allRadius_bound
      K S Γ ψ hψ hψsupport σ hσ hσ1 J
  refine ⟨s, (J.factorial : ℝ) * C * T * D ^ J,
    mul_pos (mul_pos (mul_pos (by positivity) hC) hT) (pow_pos hDpos _),
    fun φ R p hp n hn => ?_⟩
  have hpΩ := hAΩ hp
  have hΩ : IsOpen Ω := (isOpen_traceArchRegular K).prod (isOpen_traceArchRegular K)
  have hqp : 0 < q p := hqpos p hp
  have hρeq : Real.exp (Real.log R.val - (F p).1 - (F p).2) = R.val / q p := by
    change Real.exp (Real.log R.val - Real.log (traceArchProductNorm K p.1) -
      Real.log (traceArchProductNorm K p.2)) = _
    simpa only [q, Real.exp_log (traceArchProductNorm_pos K hpΩ.1),
      Real.exp_log (traceArchProductNorm_pos K hpΩ.2)] using
      sUnitJoint_exp_radius R (Real.log (traceArchProductNorm K p.1))
        (Real.log (traceArchProductNorm K p.2))
  let Q : ℝ := C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-σ) * T
  have hbase : 0 ≤ C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-σ) :=
    mul_nonneg (mul_nonneg hC.le (apply_nonneg _ _)) (Real.rpow_nonneg R.property.le _)
  have hQ : 0 ≤ Q := mul_nonneg hbase hT.le
  let G : ℝ × ℝ → ℂ := sUnitJointRadialProfile K S φ ψ R 0
  have hG : ContDiff ℝ ∞ G :=
    contDiff_sUnitJointRadialProfile K S Γ φ ψ hψ hψsupport R 0
  have hCG : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i G Set.univ (F p)‖ ≤ Q := by
    intro i hi
    rw [iteratedFDerivWithin_univ]
    have hiBound := houter φ R (F p) i (hi.trans hn)
    rw [hρeq, Real.div_rpow R.property.le hqp.le, Real.rpow_neg hqp.le,
      div_inv_eq_mul] at hiBound
    calc
      _ ≤ C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (R.val ^ (-σ) * q p ^ σ) := hiBound
      _ = (C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-σ)) * q p ^ σ := by ring
      _ ≤ Q := mul_le_mul_of_nonneg_left (hqT p hp) hbase
  have hc := norm_iteratedFDerivWithin_comp_le hG.contDiffOn
    (contDiffOn_traceJointLogNormMap K) (show (n : ℕ∞ω) ≤ ∞ by simp)
    uniqueDiffOn_univ hΩ.uniqueDiffOn (Set.mapsTo_univ F Ω) hpΩ hCG
    (fun i hi hin => hinner p hp i hi (hin.trans hn))
  have hcompAt : ContDiffAt ℝ ∞ (G ∘ F) p :=
    hG.contDiffAt.comp p (contDiffAt_traceJointLogNormMap K hpΩ)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn
    (hcompAt.of_le (by simp)) hpΩ] at hc
  change ‖iteratedFDeriv ℝ n (traceJointOrbitalKernel K S φ ψ R) p‖ ≤
    (n.factorial : ℝ) * Q * D ^ n at hc
  have hfac : (n.factorial : ℝ) ≤ J.factorial := by exact_mod_cast Nat.factorial_le hn
  have hDn : D ^ n ≤ D ^ J := pow_le_pow_right₀ hD hn
  calc
    _ ≤ (n.factorial : ℝ) * Q * D ^ n := hc
    _ ≤ (J.factorial : ℝ) * Q * D ^ J :=
      mul_le_mul (mul_le_mul_of_nonneg_right hfac hQ) hDn
        (pow_nonneg hD0 _) (mul_nonneg (by positivity) hQ)
    _ = ((J.factorial : ℝ) * C * T * D ^ J) *
        s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-σ) := by dsimp [Q]; ring

end HeckeGeneral.Analysis.SmallRadiusJointCompactDraft
