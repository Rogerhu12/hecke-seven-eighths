import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceActualArithmetic
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedOrbital

/-!
# Uniform complete-row estimates for every genuine marked annulus

The scale may be below one.  That case is proved directly from the
integer ideal norm and the literal divisor mark; positive scales at
least one use the already proved initial Poisson closure.  The fixed
seminorm, scalar and threshold precede the original source, common
prime product, residual slots, sector, radial profile and frequency.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedComplete

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.Moments.UniformAmplify
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP
open SourceActualArithmetic SourceCompleteRows ProviderNodes
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

local notation "S" => excludedPlaces K c
local notation "Sset" => places K c
local notation "P" => probeData K c
local notation "D" => (probeData K c).arithmetic
local notation "Γ" => sixthPowerSUnitSubgroup K Sset
local notation "Θ" => twists K c
local notation "ψ" => targetCharacter K c

attribute [local instance] Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar
  Expansion.ActualProbeContext.adeleSpace
  Expansion.ActualProbeContext.adeleBorel
  Expansion.ActualProbeContext.adeleMeasure_isAddHaar

local instance normOneSpace : MeasurableSpace (sLocalNormOneGroup K Sset) :=
  (probeMeasures K c).normOneSpace
local instance normOneBorel : BorelSpace (sLocalNormOneGroup K Sset) :=
  (probeMeasures K c).normOneBorel
local instance principal : IsPrincipalIdealRing (Set.integer Sset K) :=
  (axiomChoice K c).C.principal

theorem conjugate_marks {σ : Type*} {slotCap : ℕ} {Z z lo hi : ℝ}
    {slots : Finset σ} {lists : σ → Finset (Ideal (𝓞 K))}
    {a : σ → Ideal (𝓞 K) → ℂ} {lengths : σ → ℝ}
    (h : MarkConditions K S slotCap Z z lo hi slots lists a lengths) :
    MarkConditions K S slotCap Z z lo hi slots lists (fun i p => conj (a i p)) lengths := by
  exact { h with weights_le := fun i hi p hp => by
    simpa only [Complex.norm_conj] using h.weights_le i hi p hp }

/-- Literal residual marked polynomials on all original complete ideal
rows.  The single canonical input is uniform in the surviving total
length; each source keeps its own actual value `z-G`. -/
theorem annular_bound_of_uniform
    (slotCap : ℕ) (gap eps supportC : ℝ) (hgap : 0 < gap) (heps : 0 < eps)
    (hsupport : 1 ≤ supportC) (t : Finset (ℕ × ℕ)) (Cih Zih : ℝ)
    (hCih : 1 ≤ Cih) (hZih : 2 ≤ Zih)
    (hih : ∀ Z : ℝ, Zih ≤ Z → ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D P.Lambda P.G slotCap Z 2
        (3 * gap / 4) z (1 / 2) 2 (eps / 2) 2 Cih t) :
    ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 0 ≤ C ∧ 2 ≤ Z₀ ∧
      ∀ (d : MomentData K c.family.omega ψ) (sector : SixthUnitClasses K Sset),
      d.direction = 1 →
      d.rowCharacter = completeIdealRowCharacter K Sset P (momentRowCharacters K c) sector →
      d.commonMask = completeIdealCommonMask K Sset →
      d.allowedRow = completeIdealIsExterior K Sset →
      BackgroundCycle.Admissible K Θ ψ d.inverseBackground⁻¹ →
      ∀ {σ : Type*} [DecidableEq σ] (slots : Finset σ)
        (lists : σ → Finset (Ideal (𝓞 K))) (a : σ → Ideal (𝓞 K) → ℂ)
        (lengths : σ → ℝ) (j : Ideal (𝓞 K)), j ≠ 0 →
      ∀ (Z X m r z G : ℝ), Z₀ ≤ Z → 0 < X → 0 ≤ m → m ≤ 2 →
      0 ≤ G → G ≤ z → z ≤ 1 →
      r + 2 * z ≤ m - 2 * gap → 2 * r + 8 * z ≤ 3 * m - 2 * gap →
      (j.absNorm : ℝ) ≤ supportC * Z ^ G →
      X ≤ supportC * Z ^ ProviderMarkedScale.columnLength r z G →
      MarkConditions K S slotCap Z (z - G) (1 / 2) 2 slots lists a lengths →
      ∀ W : SchwartzMap ℝ ℂ, tsupport W ⊆ Set.Icc (1 : ℝ) 2 →
      (∑ u ∈ d.rows (Z ^ m),
        ‖SourceMarkedPhysical.polynomial K d (SourceMarkedPhysical.mark slots lists a j) u X W‖ ^ 2) ≤
        C * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 * Z ^ (m + eps) := by
  obtain ⟨qOrb, COrb, ZOrb, hCOrb, hZOrb, horb⟩ :=
    SourceMarkedOrbital.exists_uniform_orbital_bound K S D Γ le_rfl
      (allowedGenerators K c) (Expansion.ActualProbeContext.allLocalMeasures K)
      (Expansion.ActualProbeContext.finiteAdeleMeasure K)
      (Expansion.ActualProbeContext.adeleMeasure K) slotCap gap eps supportC hgap heps hsupport t
  obtain ⟨s, CConj, hCConj, hconj⟩ := conjugateTest_seminorm qOrb
  obtain ⟨CSmall, hCSmall, hsmall⟩ := SourceMarkedPhysical.exists_small_scale_row_bound K slotCap
  let q := insert (0, 0) s
  let CLarge := (InverseRowMajorant.rowCovolume K S)⁻¹ * COrb * Cih * CConj ^ 2
  have hCLarge : 0 ≤ CLarge := by
    dsimp only [CLarge]
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (inv_nonneg.mpr (InverseRowMajorant.rowCovolume_pos K S).le)
      (zero_le_one.trans hCOrb)) (zero_le_one.trans hCih)) (sq_nonneg _)
  refine ⟨q, CSmall + CLarge, max Zih ZOrb, by positivity,
    hZih.trans (le_max_left _ _), ?_⟩
  intro d sector hdir hchar hmask hrows hbackground σ _ slots lists a lengths j hj
    Z X m r z G hZ hX hm0 hm2 hG hGz hz1 hf hg hjbound hXbound hmarks W hW
  have hZi : Zih ≤ Z := (le_max_left _ _).trans hZ
  have hZo : ZOrb ≤ Z := (le_max_right _ _).trans hZ
  have hZ1 : 1 ≤ Z := by linarith
  have hZp : 0 < Z := zero_lt_one.trans_le hZ1
  have hH : 1 ≤ Z ^ m := Real.one_le_rpow hZ1 hm0
  have hHp : 0 < Z ^ m := Real.rpow_pos_of_pos hZp m
  have hq0 : SchwartzMap.seminorm ℝ 0 0 W ≤
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
    Seminorm.le_def.mp (Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ)
      (Finset.mem_insert_self (0, 0) s)) W
  have hqs : s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert (0, 0) s)) W
  by_cases hx : X ≤ 1
  · have hb := hsmall d slots lists a j hmarks.card_le hmarks.weights_le
      (Z ^ m) X W hH hX hx
    calc
      _ ≤ CSmall * Z ^ m * (SchwartzMap.seminorm ℝ 0 0 W) ^ 2 := hb
      _ ≤ CSmall * Z ^ (m + eps) * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 := by
        gcongr
        · exact Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
        · exact hq0
      _ ≤ (CSmall + CLarge) * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
          Z ^ (m + eps) := by
        have hc : CSmall ≤ CSmall + CLarge := le_add_of_nonneg_right hCLarge
        nlinarith [mul_le_mul_of_nonneg_right hc
          (mul_nonneg (sq_nonneg (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W))
            (Real.rpow_nonneg hZp.le (m + eps)))]
  · have hX1 : 1 ≤ X := (lt_of_not_ge hx).le
    have hp := SourceMarkedPhysical.complete_positive_rows_le_orbital
      K S P (momentRowCharacters K c) d (SourceMarkedPhysical.mark slots lists a j)
      sector hdir hchar hmask hrows (Z ^ m) X hHp hX W
    have hcmarks := conjugate_marks K c hmarks
    have ho := horb Θ ψ P.Lambda P.G d.inverseBackground⁻¹ (calibration_mem K c)
      (arithmeticCalibration K c) hbackground
      (SourceActualArithmetic.admissible_unramified K c _ hbackground) j hj
      slots lists (fun i p => conj (a i p)) lengths Z X m r z G (1 / 2) 2
      hZo hX1 hm0 hm2 hG hGz hf hg hjbound hXbound hcmarks (conjugateTest W)
      (by rw [conjugateTest_support]; exact hW) Cih hCih
      (hih Z hZi (z - G) (sub_nonneg.mpr hGz) (by linarith))
    have heq : (fun n : ExteriorIdeal K Sset =>
        conj (SourceMarkedPhysical.mark slots lists a j n.val.val)) =
        fun n => SourceMarkedPhysical.mark slots lists (fun i p => conj (a i p)) j n.val.val := by
      funext n
      exact SourceMarkedPhysical.conjugate_mark slots lists a j _
    rw [heq] at hp
    have hqconj : qOrb.sup (schwartzSeminormFamily ℝ ℝ ℂ) (conjugateTest W) ≤
        CConj * q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
      (hconj W).trans (mul_le_mul_of_nonneg_left hqs hCConj)
    calc
      _ ≤ (InverseRowMajorant.rowCovolume K S)⁻¹ *
          ‖SourceReductionPoisson.orbitalEnergy K S D Γ d.inverseBackground⁻¹
            (fun n => SourceMarkedPhysical.mark slots lists (fun i p => conj (a i p)) j n.val.val)
            (conjugateTest W) X ⟨Z ^ m, hHp⟩‖ := hp
      _ ≤ (InverseRowMajorant.rowCovolume K S)⁻¹ *
          (COrb * Cih * (qOrb.sup (schwartzSeminormFamily ℝ ℝ ℂ)
            (conjugateTest W)) ^ 2 * Z ^ (m + eps)) :=
        mul_le_mul_of_nonneg_left ho (inv_nonneg.mpr (InverseRowMajorant.rowCovolume_pos K S).le)
      _ ≤ (InverseRowMajorant.rowCovolume K S)⁻¹ *
          (COrb * Cih * (CConj * q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
            Z ^ (m + eps)) := by gcongr
      _ = CLarge * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 * Z ^ (m + eps) := by
        dsimp only [CLarge]; ring
      _ ≤ (CSmall + CLarge) * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
          Z ^ (m + eps) := by gcongr; linarith

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedComplete

end
