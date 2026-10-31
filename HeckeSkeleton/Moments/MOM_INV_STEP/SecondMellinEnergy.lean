import HeckeSkeleton.Moments.MOM_INV_STEP.SecondCenteredFamily
import HeckeSkeleton.Moments.MOM_INV_STEP.IntegralEnergy
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Positive Mellin energy of the literal fixed-center second children

All columns here are the actual canonical children supplied by
SecondCenteredFamily. Their complete pool and test are independent of
the reconstructed label and row. A finite sum of the actual coefficient
norms proves continuity and integrability before integral Cauchy is
applied. The original powered test contributes one common Mellin mass.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondMellinEnergy

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools CommonKernel
  SecondCenteredFamily
open scoped Classical BigOperators nonZeroDivisors

private theorem phase_integral_sq_le (ρ : SchwartzMap ℝ ℂ) (p c : ℝ → ℂ)
    (cp : Continuous p) (hp : ∀ t, ‖p t‖ = 1)
    (cc : Continuous c) (B : ℝ) (hc : ∀ t, ‖c t‖ ≤ B) :
    Integrable (fun t => ρ t * p t * c t) ∧
    ‖∫ t, ρ t * p t * c t‖ ^ 2 ≤
      (∫ t, ‖ρ t‖) * ∫ t, ‖ρ t‖ * ‖c t‖ ^ 2 := by
  have hi : Integrable (fun t => ‖ρ t‖ * ‖c t‖ ^ 2) := by
    apply ρ.integrable.norm.mul_bdd (c := B ^ 2) (cc.norm.pow 2).aestronglyMeasurable
    filter_upwards [] with t
    change ‖(‖c t‖ ^ 2)‖ ≤ B ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hc t) 2
  have hiz : Integrable (fun t => ρ t * p t * c t) := by
    apply (ρ.integrable.norm.mul_const B).mono'
      ((ρ.continuous.mul cp).mul cc).aestronglyMeasurable
    filter_upwards [] with t
    change ‖ρ t * p t * c t‖ ≤ ‖ρ t‖ * B
    rw [norm_mul, norm_mul, hp, mul_one]
    exact mul_le_mul_of_nonneg_left (hc t) (norm_nonneg _)
  refine ⟨hiz, ?_⟩
  have hb := IntegralEnergy.weighted_integral_cauchy volume
    (fun t : ℝ => ‖ρ t‖) (fun _ => 1) (fun t => ‖c t‖ ^ 2)
    (fun t => ρ t * p t * c t)
    (fun _ => norm_nonneg _) (fun _ => zero_le_one) (fun _ => sq_nonneg _)
    ρ.continuous.norm continuous_const (cc.norm.pow 2)
    (by simpa only [mul_one] using ρ.integrable.norm) hi (by
      intro t
      simp only [norm_mul, hp, mul_one, Real.sqrt_one,
        Real.sqrt_sq (norm_nonneg _), one_mul, le_refl])
  have hm : 0 ≤ ∫ t : ℝ, ‖ρ t‖ := integral_nonneg (fun _ => norm_nonneg _)
  have he : 0 ≤ ∫ t : ℝ, ‖ρ t‖ * ‖c t‖ ^ 2 :=
    integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  simpa only [mul_one, mul_pow, Real.sq_sqrt hm, Real.sq_sqrt he] using hs

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

variable (C : ColumnFamily K (S : Set (HeightOneSpectrum (𝓞 K))) σ Θ ψ) (γ₀ : OuterTriple K)
variable (G : HeckeCharacter K) (hG : G ∈ Θ) (J : Finset σ) (U : ℝ)
variable (γ : OuterTriple K) (f : Ideal (𝓞 K)) (y : Ideal (𝓞 K) × (CanonicalSectors.UnitClasses K (S : Set (HeightOneSpectrum (𝓞 K))) Γ))

def coefficientMass : ℝ :=
  ∑ n ∈ squarefreePool K Sset (2 * U),
    ‖bareCoefficient K S D Γ C γ₀ G J γ f y n‖

theorem column_continuous (hZ : 1 < C.base) (hU : 0 < U) (τ : ℝ) :
    Continuous (fun t : ℝ =>
      column K Sset D (family K S C γ₀ G hG J U (t + τ))
        (CanonicalSectors.sectorUnit K Sset Γ) γ f y) := by
  simp only [column_eq_complete_sum K S D Γ C γ₀ G hG J U _ hZ hU]
  apply continuous_finsetSum
  intro n hn
  exact continuous_const.mul
    ((FinalMellinTests.continuous_weightedTest 0 _).comp
      (continuous_id.add continuous_const))

theorem column_bound (hZ : 1 < C.base) (hU : 0 < U) (t : ℝ) :
    ‖column K Sset D (family K S C γ₀ G hG J U t)
      (CanonicalSectors.sectorUnit K Sset Γ) γ f y‖ ≤
        coefficientMass K S D Γ C γ₀ G J U γ f y := by
  rw [column_eq_complete_sum K S D Γ C γ₀ G hG J U t hZ hU]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul, FinalMellinTests.norm_weightedTest, Real.rpow_zero, norm_one, mul_one]
  exact (mul_le_mul_of_nonneg_left
    (FinalMellinTests.norm_cutoff_le_one _) (norm_nonneg _)).trans_eq (mul_one _)

def mellinDensity (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8)) : SchwartzMap ℝ ℂ :=
  PositiveIntervalMellin.density (1 / 8) (21 / 8) (by norm_num) (by norm_num) W hW

def mellinMass (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8)) : ℝ :=
  ∫ t : ℝ, ‖mellinDensity W hW t‖

theorem mellinMass_nonneg (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8)) : 0 ≤ mellinMass W hW :=
  integral_nonneg (fun _ => norm_nonneg _)

def columnEnergy (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8)) (τ : ℝ) : ℝ :=
  ∫ t : ℝ, ‖mellinDensity W hW t‖ *
    ‖column K Sset D (family K S C γ₀ G hG J U (t + τ))
      (CanonicalSectors.sectorUnit K Sset Γ) γ f y‖ ^ 2

theorem column_energy_nonneg (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8)) (τ : ℝ) :
    0 ≤ columnEnergy K S D Γ C γ₀ G hG J U γ f y W hW τ :=
  integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))

theorem column_energy_integrable (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8))
    (hZ : 1 < C.base) (hU : 0 < U) (τ : ℝ) :
    Integrable (fun t : ℝ => ‖mellinDensity W hW t‖ *
      ‖column K Sset D (family K S C γ₀ G hG J U (t + τ))
        (CanonicalSectors.sectorUnit K Sset Γ) γ f y‖ ^ 2) := by
  apply (mellinDensity W hW).integrable.norm.mul_bdd
    (c := (coefficientMass K S D Γ C γ₀ G J U γ f y) ^ 2)
    ((column_continuous K S D Γ C γ₀ G hG J U γ f y hZ hU τ).norm.pow 2).aestronglyMeasurable
  filter_upwards [] with t
  change ‖(‖column K Sset D (family K S C γ₀ G hG J U (t + τ))
    (CanonicalSectors.sectorUnit K Sset Γ) γ f y‖ ^ 2)‖ ≤
      (coefficientMass K S D Γ C γ₀ G J U γ f y) ^ 2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (column_bound K S D Γ C γ₀ G hG J U γ f y hZ hU (t + τ)) 2

/-- Cauchy is applied to the genuine Mellin inversion of the original
norm test. The child scale and every child coefficient are constructed,
and the single positive Mellin density appears inside its energy. -/
theorem branch_sq_le (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8))
    (τ vcenter v X A : ℝ) (hZ : 1 < C.base)
    (hc : 0 < vcenter) (hA : 0 < A) (hU : 0 < U)
    (hvlo : vcenter ≤ v) (hvhi : v ≤ 4 * vcenter)
    (hactual : X = v * A) (hcenter : X = vcenter * U) :
    ‖branch K S D Γ C γ₀ G J γ f y W τ v X A‖ ^ 2 ≤
      mellinMass W hW * columnEnergy K S D Γ C γ₀ G hG J U γ f y W hW τ := by
  let p : ℝ → ℂ := fun t => columnPhase t (Real.log v) *
    columnPhase t (-Real.log X) * columnPhase (t + τ) (Real.log U)
  let c : ℝ → ℂ := fun t =>
    column K Sset D (family K S C γ₀ G hG J U (t + τ))
      (CanonicalSectors.sectorUnit K Sset Γ) γ f y
  have cp : Continuous p :=
    ((continuous_columnPhase _).mul (continuous_columnPhase _)).mul
      ((continuous_columnPhase _).comp (continuous_id.add continuous_const))
  have hp (t : ℝ) : ‖p t‖ = 1 := by
    simp only [p, norm_mul, norm_columnPhase, mul_one]
  have hb := (phase_integral_sq_le (mellinDensity W hW) p c cp hp
    (column_continuous K S D Γ C γ₀ G hG J U γ f y hZ hU τ)
    (coefficientMass K S D Γ C γ₀ G J U γ f y)
    (fun t => column_bound K S D Γ C γ₀ G hG J U γ f y hZ hU (t + τ))).2
  rw [second_branch_centered K S D Γ C γ₀ G hG J γ f y W hW
    τ vcenter v X A U hZ hc hA hU hvlo hvhi hactual hcenter]
  change ‖∫ t : ℝ, mellinDensity W hW t * columnPhase t (Real.log v) *
    columnPhase t (-Real.log X) * columnPhase (t + τ) (Real.log U) * c t‖ ^ 2 ≤ _
  have he : (∫ t : ℝ, mellinDensity W hW t * columnPhase t (Real.log v) *
      columnPhase t (-Real.log X) * columnPhase (t + τ) (Real.log U) * c t) =
      ∫ t : ℝ, mellinDensity W hW t * p t * c t := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by dsimp only [p]; ring)
  rw [he]
  exact hb

/-- Absolute joint integrability is derived from the literal finite
column bound. It permits the common Fourier integral and the new Mellin
integral to be interchanged; no spectral convergence is assumed. -/
theorem joint_column_integrable (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8))
    (hZ : 1 < C.base) (hU : 0 < U)
    (d : LogPlane → ℝ) (hd : Integrable d) (cd : Continuous d)
    (coordinate : LogPlane →L[ℝ] ℝ) :
    Integrable (fun p : LogPlane × ℝ =>
      (d p.1 * ‖mellinDensity W hW p.2‖) *
        ‖column K Sset D (family K S C γ₀ G hG J U (p.2 + coordinate p.1))
          (CanonicalSectors.sectorUnit K Sset Γ) γ f y‖ ^ 2)
      ((volume : Measure LogPlane).prod (volume : Measure ℝ)) := by
  have hc : Continuous (fun t : ℝ =>
      column K Sset D (family K S C γ₀ G hG J U t)
        (CanonicalSectors.sectorUnit K Sset Γ) γ f y) := by
    simpa only [add_zero] using
      column_continuous K S D Γ C γ₀ G hG J U γ f y hZ hU 0
  have hj := hc.comp (continuous_snd.add (coordinate.continuous.comp continuous_fst))
  have hρ : Integrable (fun t : ℝ => ‖mellinDensity W hW t‖)
      (volume : Measure ℝ) := (mellinDensity W hW).integrable.norm
  have hbase : Integrable (fun p : LogPlane × ℝ => d p.1 * ‖mellinDensity W hW p.2‖)
      ((volume : Measure LogPlane).prod (volume : Measure ℝ)) := hd.mul_prod hρ
  apply hbase.mul_bdd (c := (coefficientMass K S D Γ C γ₀ G J U γ f y) ^ 2)
    (hj.norm.pow 2).aestronglyMeasurable
  filter_upwards [] with p
  change ‖(‖column K Sset D (family K S C γ₀ G hG J U (p.2 + coordinate p.1))
    (CanonicalSectors.sectorUnit K Sset Γ) γ f y‖ ^ 2)‖ ≤
      (coefficientMass K S D Γ C γ₀ G J U γ f y) ^ 2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (column_bound K S D Γ C γ₀ G hG J U γ f y hZ hU (p.2 + coordinate p.1)) 2

theorem outer_energy_integrable (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8))
    (hZ : 1 < C.base) (hU : 0 < U)
    (d : LogPlane → ℝ) (hd : Integrable d) (cd : Continuous d)
    (coordinate : LogPlane →L[ℝ] ℝ) :
    Integrable (fun τ : LogPlane => d τ *
      columnEnergy K S D Γ C γ₀ G hG J U γ f y W hW (coordinate τ)) := by
  have hi := (joint_column_integrable K S D Γ C γ₀ G hG J U γ f y
    W hW hZ hU d hd cd coordinate).integral_prod_left
  simp only [mul_assoc, integral_const_mul] at hi
  exact hi

/-- The identical positive joint measure may be read with either
frequency outside. This is the form used before summing the actual
reconstruction fibers. -/
theorem energy_fubini (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8))
    (hZ : 1 < C.base) (hU : 0 < U)
    (d : LogPlane → ℝ) (hd : Integrable d) (cd : Continuous d)
    (coordinate : LogPlane →L[ℝ] ℝ) :
    (∫ τ : LogPlane, d τ * columnEnergy K S D Γ C γ₀ G hG J U γ f y W hW
      (coordinate τ)) =
      ∫ t : ℝ, ‖mellinDensity W hW t‖ *
        ∫ τ : LogPlane, d τ *
          ‖column K Sset D (family K S C γ₀ G hG J U (t + coordinate τ))
            (CanonicalSectors.sectorUnit K Sset Γ) γ f y‖ ^ 2 := by
  have hi := joint_column_integrable K S D Γ C γ₀ G hG J U γ f y
    W hW hZ hU d hd cd coordinate
  have he := integral_integral_swap
    (μ := (volume : Measure LogPlane)) (ν := (volume : Measure ℝ))
    (f := fun τ : LogPlane => fun t : ℝ =>
      (d τ * ‖mellinDensity W hW t‖) *
        ‖column K Sset D (family K S C γ₀ G hG J U (t + coordinate τ))
          (CanonicalSectors.sectorUnit K Sset Γ) γ f y‖ ^ 2) hi
  calc
    _ = ∫ τ : LogPlane, ∫ t : ℝ,
        (d τ * ‖mellinDensity W hW t‖) *
          ‖column K Sset D (family K S C γ₀ G hG J U (t + coordinate τ))
            (CanonicalSectors.sectorUnit K Sset Γ) γ f y‖ ^ 2 := by
      simp only [mul_assoc, integral_const_mul, columnEnergy]
    _ = _ := by
      rw [he]
      apply integral_congr_ae
      filter_upwards [] with t
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with τ
      ring

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondMellinEnergy

end
