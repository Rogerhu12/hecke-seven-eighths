module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Genuine two-column Fourier inversion and finite bilinear separation

The Fourier density is the actual Schwartz transform.  The column factors
have norm one, every separated integrand is integrable, and the finite
bilinear expansion uses the same density before Cauchy--Schwarz.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CommonKernel

open MeasureTheory
open scoped Classical BigOperators FourierTransform NNReal

abbrev LogPlane := WithLp 2 (ℝ × ℝ)

def logCoordinates : LogPlane ≃L[ℝ] ℝ × ℝ :=
  WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ

def logPoint (x y : ℝ) : LogPlane := WithLp.toLp 2 (x, y)

/-- A literal unit-circle Fourier multiplier in one column variable. -/
def columnPhase (ξ x : ℝ) : ℂ := (Real.fourierChar (inner ℝ ξ x) : ℂ)

@[simp] theorem norm_columnPhase (ξ x : ℝ) : ‖columnPhase ξ x‖ = 1 :=
  Circle.norm_coe _

theorem phase_product (ξ p : LogPlane) :
    (Real.fourierChar (inner ℝ ξ p) : ℂ) =
      columnPhase ξ.fst p.fst * columnPhase ξ.snd p.snd := by
  rw [WithLp.prod_inner_apply, AddChar.map_add_eq_mul]
  rfl

theorem continuous_columnPhase (x : ℝ) : Continuous (fun ξ : ℝ => columnPhase ξ x) := by
  simp only [columnPhase, Real.fourierChar_apply]
  fun_prop

/-- The separated Fourier integrand is integrable, not merely a
 totalized integral. Its norm is the Fourier density norm. -/
theorem integrable_separated (F : SchwartzMap LogPlane ℂ) (p : LogPlane) :
    Integrable (fun ξ : LogPlane =>
      (𝓕 F) ξ * columnPhase ξ.fst p.fst * columnPhase ξ.snd p.snd) := by
  have hleft : Continuous (fun ξ : LogPlane => columnPhase ξ.fst p.fst) :=
    (continuous_columnPhase p.fst).comp logCoordinates.continuous.fst
  have hright : Continuous (fun ξ : LogPlane => columnPhase ξ.snd p.snd) :=
    (continuous_columnPhase p.snd).comp logCoordinates.continuous.snd
  have hd : Integrable (fun ξ : LogPlane => ‖(𝓕 F) ξ‖) :=
    ((𝓕 F).integrable (μ := (volume : Measure LogPlane))).norm
  apply hd.mono' (((𝓕 F).continuous.mul hleft).mul hright).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ => by
    simp only [norm_mul, norm_columnPhase, mul_one]

theorem norm_separated_integrand (F : SchwartzMap LogPlane ℂ) (ξ p : LogPlane) :
    ‖(𝓕 F) ξ * columnPhase ξ.fst p.fst * columnPhase ξ.snd p.snd‖ = ‖(𝓕 F) ξ‖ := by
  simp only [norm_mul, norm_columnPhase, mul_one]

def spectralMass (F : SchwartzMap LogPlane ℂ) : ℝ :=
  ∫ ξ : LogPlane, ‖(𝓕 F) ξ‖

/-- One fixed integrable frequency envelope for every outer parameter. -/
def fourierEnvelope (ξ : LogPlane) : ℝ :=
  (1 + ‖ξ‖) ^ (-((volume : Measure LogPlane).integrablePower : ℝ))

theorem fourierEnvelope_nonneg (ξ : LogPlane) : 0 ≤ fourierEnvelope ξ :=
  Real.rpow_nonneg (by positivity) _

theorem fourierEnvelope_integrable : Integrable fourierEnvelope :=
  Measure.integrable_pow_neg_integrablePower (volume : Measure LogPlane)

theorem spectralMass_nonneg (F : SchwartzMap LogPlane ℂ) : 0 ≤ spectralMass F :=
  integral_nonneg (fun _ => norm_nonneg _)

/-- The Fourier L¹ cost is controlled by a fixed finite family of actual
Schwartz seminorms.  The indices and constant are selected before F. -/
theorem exists_spectralMass_seminorm_bound :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ F : SchwartzMap LogPlane ℂ,
        spectralMass F ≤ (C : ℝ) * s.sup (schwartzSeminormFamily ℝ LogPlane ℂ) F := by
  let T : SchwartzMap LogPlane ℂ →L[ℝ] Lp ℂ 1 (volume : Measure LogPlane) :=
    (SchwartzMap.toLpCLM ℝ ℂ 1 (volume : Measure LogPlane)).comp
      (SchwartzMap.fourierTransformCLM ℝ)
  let q : Seminorm ℝ (SchwartzMap LogPlane ℂ) :=
    (normSeminorm ℝ (Lp ℂ 1 (volume : Measure LogPlane))).comp T.toLinearMap
  have hq : Continuous q := continuous_norm.comp T.continuous
  obtain ⟨s, C, hC, hb⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ LogPlane ℂ) q hq
  refine ⟨s, C, hC, fun F => ?_⟩
  have hF := Seminorm.le_def.mp hb F
  change ‖(𝓕 F : SchwartzMap LogPlane ℂ).toLp 1 (volume : Measure LogPlane)‖ ≤
    (C : ℝ) * s.sup (schwartzSeminormFamily ℝ LogPlane ℂ) F at hF
  simpa only [SchwartzMap.norm_toLp_one, spectralMass] using hF

private theorem continuous_finite_seminorm (s : Finset (ℕ × ℕ)) :
    Continuous (fun F : SchwartzMap LogPlane ℂ =>
      s.sup (schwartzSeminormFamily ℝ LogPlane ℂ) F) :=
  Seminorm.continuous_finsetSup (fun i _hi =>
    (schwartz_withSeminorms ℝ LogPlane ℂ).continuous_seminorm i)

/-- A common inverse-power Fourier envelope, with finite input
seminorms chosen before the Schwartz function and the frequency. -/
theorem exists_weighted_fourier_bound (q : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ F : SchwartzMap LogPlane ℂ, ∀ ξ : LogPlane,
        (1 + ‖ξ‖) ^ q * ‖(𝓕 F) ξ‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ LogPlane ℂ) F := by
  let T := SchwartzMap.fourierTransformCLM ℝ (V := LogPlane) (E := ℂ)
  let p : Seminorm ℝ (SchwartzMap LogPlane ℂ) :=
    ((Finset.Iic (q, 0)).sup (schwartzSeminormFamily ℝ LogPlane ℂ)).comp T.toLinearMap
  have hp : Continuous p := (continuous_finite_seminorm (Finset.Iic (q, 0))).comp T.continuous
  obtain ⟨s, C, _hC, hb⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ LogPlane ℂ) p hp
  refine ⟨s, (2 : ℝ) ^ q * (C : ℝ), mul_nonneg (by positivity) C.coe_nonneg,
    fun F ξ => ?_⟩
  have hF := Seminorm.le_def.mp hb F
  change (Finset.Iic (q, 0)).sup (schwartzSeminormFamily ℝ LogPlane ℂ) (𝓕 F) ≤
    (C : ℝ) * s.sup (schwartzSeminormFamily ℝ LogPlane ℂ) F at hF
  have hpoint := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℝ) (m := (q, 0)) (k := q) (n := 0) le_rfl le_rfl (𝓕 F) ξ
  simp only [norm_iteratedFDeriv_zero] at hpoint
  exact hpoint.trans ((mul_le_mul_of_nonneg_left hF (by positivity)).trans_eq (by ring))

/-- Two-column Fourier inversion for an actual Schwartz kernel. -/
theorem schwartz_separated (F : SchwartzMap LogPlane ℂ) (p : LogPlane) :
    F p = ∫ ξ : LogPlane,
      (𝓕 F) ξ * columnPhase ξ.fst p.fst * columnPhase ξ.snd p.snd := by
  have hinv := congrArg (fun g : SchwartzMap LogPlane ℂ => g p)
    (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap LogPlane ℂ) F)
  symm
  calc
    _ = ∫ ξ : LogPlane, (Real.fourierChar (inner ℝ ξ p) : ℂ) * (𝓕 F) ξ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ => by rw [phase_product]; ring
    _ = (𝓕⁻ (𝓕 F) : SchwartzMap LogPlane ℂ) p := by
      rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
      simp only [Real.fourierChar_apply, smul_eq_mul]
    _ = F p := hinv

private theorem finite_bilinear_factor {ι κ : Type*} (T : Finset ι) (U : Finset κ)
    (a p : ι → ℂ) (b q : κ → ℂ) (c : ℂ) :
    (∑ i ∈ T, ∑ j ∈ U, a i * b j * (c * p i * q j)) =
      c * (∑ i ∈ T, a i * p i) * (∑ j ∈ U, b j * q j) := by
  calc
    _ = ∑ i ∈ T, (a i * p i) * (∑ j ∈ U, b j * q j) * c := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = (∑ i ∈ T, a i * p i) * (∑ j ∈ U, b j * q j) * c := by
      rw [Finset.sum_mul, Finset.sum_mul]
    _ = _ := by ring

/-- Exact finite bilinear separation.  Both finite sums remain inside
the same Fourier integral, so the kernel is shared before Cauchy--Schwarz. -/
theorem finite_bilinear_separated {ι κ : Type*} (T : Finset ι) (U : Finset κ)
    (F : SchwartzMap LogPlane ℂ) (x : ι → ℝ) (y : κ → ℝ)
    (a : ι → ℂ) (b : κ → ℂ) :
    (∑ i ∈ T, ∑ j ∈ U, a i * b j * F (logPoint (x i) (y j))) =
      ∫ ξ : LogPlane, (𝓕 F) ξ *
        (∑ i ∈ T, a i * columnPhase ξ.fst (x i)) *
        (∑ j ∈ U, b j * columnPhase ξ.snd (y j)) := by
  let g : ι → κ → LogPlane → ℂ := fun i j ξ =>
    a i * b j * ((𝓕 F) ξ * columnPhase ξ.fst (x i) * columnPhase ξ.snd (y j))
  have hg (i : ι) (j : κ) : Integrable (g i j) :=
    (integrable_separated F (logPoint (x i) (y j))).const_mul (a i * b j)
  have hsum (ξ : LogPlane) :
      (∑ i ∈ T, ∑ j ∈ U, g i j ξ) =
        (𝓕 F) ξ * (∑ i ∈ T, a i * columnPhase ξ.fst (x i)) *
          (∑ j ∈ U, b j * columnPhase ξ.snd (y j)) := by
    exact finite_bilinear_factor T U a (fun i => columnPhase ξ.fst (x i))
      b (fun j => columnPhase ξ.snd (y j)) ((𝓕 F) ξ)
  calc
    _ = ∑ i ∈ T, ∑ j ∈ U, ∫ ξ : LogPlane, g i j ξ := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [schwartz_separated F (logPoint (x i) (y j)), ← integral_const_mul]
      rfl
    _ = ∫ ξ : LogPlane, ∑ i ∈ T, ∑ j ∈ U, g i j ξ := by
      rw [integral_finsetSum _ (fun i _hi =>
        integrable_finsetSum U (fun j _hj => hg i j))]
      apply Finset.sum_congr rfl
      intro i _hi
      exact (integral_finsetSum _ (fun j _hj => hg i j)).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hsum)

theorem integrable_finite_bilinear {ι κ : Type*} (T : Finset ι) (U : Finset κ)
    (F : SchwartzMap LogPlane ℂ) (x : ι → ℝ) (y : κ → ℝ)
    (a : ι → ℂ) (b : κ → ℂ) :
    Integrable (fun ξ : LogPlane => (𝓕 F) ξ *
      (∑ i ∈ T, a i * columnPhase ξ.fst (x i)) *
      (∑ j ∈ U, b j * columnPhase ξ.snd (y j))) := by
  have hi := integrable_finsetSum T (fun i _hi =>
    integrable_finsetSum U (fun j _hj =>
      (integrable_separated F (logPoint (x i) (y j))).const_mul (a i * b j)))
  apply hi.congr
  exact Filter.Eventually.of_forall fun ξ => by
    exact finite_bilinear_factor T U a (fun i => columnPhase ξ.fst (x i))
      b (fun j => columnPhase ξ.snd (y j)) ((𝓕 F) ξ)

end HeckeSkeleton.Moments.MOM_INV_STEP.CommonKernel

end
