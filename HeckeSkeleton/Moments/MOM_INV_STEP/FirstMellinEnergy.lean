import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCompleteFamily
import HeckeSkeleton.Moments.MOM_INV_STEP.InverseSpectralEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.IntegralEnergy

/-!
# Genuine Mellin Cauchy for the complete first inverse columns

The frequency-dependent family is the literal family constructed from
the original coefficients. Its finite coefficients have frequency-
independent norms; this proves all integrability needed below.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstMellinEnergy

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalBlock CanonicalNormPools
  FirstCompleteFamily MellinSchwartz MellinWeightedTests MellinSeparation CommonKernel
  InverseRowMajorant
open scoped Classical BigOperators nonZeroDivisors

private theorem phase_cauchy (ρ : SchwartzMap ℝ ℂ) (p c : ℝ → ℂ)
    (cp : Continuous p) (hp : ∀ t, ‖p t‖ = 1)
    (cc : Continuous c) (B : ℝ) (hc : ∀ t, ‖c t‖ ≤ B) :
    Integrable (fun t => ρ t * p t * c t) ∧
    ‖∫ t, ρ t * p t * c t‖ ^ 2 ≤
      (∫ t, ‖ρ t‖) * ∫ t, ‖ρ t‖ * ‖c t‖ ^ 2 := by
  have hi : Integrable (fun t => ‖ρ t‖ * ‖c t‖ ^ 2) := by
    apply ρ.integrable.norm.mul_bdd (c := B ^ 2) (cc.norm.pow 2).aestronglyMeasurable
    filter_upwards [] with t
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hc t) 2
  have hiz : Integrable (fun t => ρ t * p t * c t) := by
    apply (ρ.integrable.norm.mul_const B).mono'
      ((ρ.continuous.mul cp).mul cc).aestronglyMeasurable
    filter_upwards [] with t
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
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

variable {σ : Type*}
variable (C : ColumnData K S σ)
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
variable (J : Finset σ) (U a : ℝ) (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS)

theorem coefficient_continuous (n : Ext) (τ : ℝ) :
    Continuous (fun t => DivisorInverseColumn.coefficient K S D
      (family K S C Θ ψ G hν hG J U a (t + τ)) γ j d n) := by
  unfold DivisorInverseColumn.coefficient FirstCanonicalLabel.inverseCoefficient
  dsimp only [family]
  apply Continuous.mul
  · apply Continuous.mul
    · exact continuous_const
    · exact (continuous_weightedTest a _).comp (continuous_id.add continuous_const)
  · exact continuous_const

theorem coefficient_norm_eq_zero (n : Ext) (t : ℝ) :
    ‖DivisorInverseColumn.coefficient K S D
      (family K S C Θ ψ G hν hG J U a t) γ j d n‖ =
    ‖DivisorInverseColumn.coefficient K S D
      (family K S C Θ ψ G hν hG J U a 0) γ j d n‖ := by
  simp only [DivisorInverseColumn.coefficient, FirstCanonicalLabel.inverseCoefficient,
    family, norm_mul, norm_weightedTest]

def coefficientMass : ℝ :=
  ∑ n ∈ squarefreePool K Sset (2 * U),
    ‖DivisorInverseColumn.coefficient K S D
      (family K S C Θ ψ G hν hG J U a 0) γ j d n‖

theorem coefficient_mass_bound (τ t : ℝ) :
    (∑ n ∈ squarefreePool K Sset (2 * U),
      ‖DivisorInverseColumn.coefficient K S D
        (family K S C Θ ψ G hν hG J U a (t + τ)) γ j d n‖) ≤
      coefficientMass K S D C Θ ψ G hν hG J U a γ j d := by
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro n hn
  exact coefficient_norm_eq_zero K S D C Θ ψ G hν hG J U a γ j d n (t + τ)

theorem column_continuous (y : Ideal (𝓞 K) × Sector) (τ : ℝ) :
    Continuous (fun t => DivisorInverseColumn.column K S Γ D
      (family K S C Θ ψ G hν hG J U a (t + τ)) γ j d y) := by
  apply continuous_finsetSum
  intro n hn
  exact (coefficient_continuous K S D C Θ ψ G hν hG J U a γ j d n τ).mul continuous_const

variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)

include hΓ in
theorem column_eq_amplitude (y : Ext × Sector) (t : ℝ) :
    DivisorInverseColumn.column K S Γ D
      (family K S C Θ ψ G hν hG J U a t) γ j d (y.1.val.val,y.2) =
    amplitude K S Γ D (squarefreePool K Sset (2 * U))
      (DivisorInverseColumn.coefficient K S D
        (family K S C Θ ψ G hν hG J U a t) γ j d)
      (CanonicalSectors.rowOrbit K Sset Γ D y) := by
  exact (DivisorInverseColumn.orbitColumn_rowOrbit K S Γ D hΓ
    (family K S C Θ ψ G hν hG J U a t) γ j d y.1 y.2).symm

include hΓ in
theorem column_bound (y : Ext × Sector) (τ t : ℝ) :
    ‖DivisorInverseColumn.column K S Γ D
      (family K S C Θ ψ G hν hG J U a (t + τ)) γ j d (y.1.val.val,y.2)‖ ≤
      coefficientMass K S D C Θ ψ G hν hG J U a γ j d := by
  rw [column_eq_amplitude K S Γ D C Θ ψ G hν hG J U a γ j d hΓ]
  exact (amplitude_norm_le K S Γ D _ _ _).trans
    (coefficient_mass_bound K S D C Θ ψ G hν hG J U a γ j d τ t)

include hΓ in
theorem column_energy_integrable (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (y : Ext × Sector) (τ : ℝ) :
    Integrable (fun t => ‖density W hW t‖ *
      ‖DivisorInverseColumn.column K S Γ D
        (family K S C Θ ψ G hν hG J U a (t + τ)) γ j d (y.1.val.val,y.2)‖ ^ 2) := by
  apply (density W hW).integrable.norm.mul_bdd
    (c := (coefficientMass K S D C Θ ψ G hν hG J U a γ j d) ^ 2)
    ((column_continuous K S Γ D C Θ ψ G hν hG J U a γ j d
      (y.1.val.val,y.2) τ).norm.pow 2).aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (column_bound K S Γ D C Θ ψ G hν hG J U a γ j d hΓ y τ t) 2

include hΓ in
theorem residual_branch_sq_le (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (y : Ext × Sector) (τ v X : ℝ) (hZ : 1 < C.base)
    (hv : 0 < v) (hU : 0 < U) (hscale : X = v * U) :
    ‖residualBranch K S D Γ C G J γ j d (y.1.val.val,y.2) W a τ v X U‖ ^ 2 ≤
      (U ^ a) ^ 2 * ((∫ t : ℝ, ‖density W hW t‖) *
        ∫ t : ℝ, ‖density W hW t‖ *
          ‖DivisorInverseColumn.column K S Γ D
            (family K S C Θ ψ G hν hG J U a (t + τ)) γ j d (y.1.val.val,y.2)‖ ^ 2) := by
  let p : ℝ → ℂ := fun t => columnPhase t (Real.log v) *
    columnPhase t (-Real.log X) * columnPhase (t + τ) (Real.log U)
  let c : ℝ → ℂ := fun t => DivisorInverseColumn.column K S Γ D
    (family K S C Θ ψ G hν hG J U a (t + τ)) γ j d (y.1.val.val,y.2)
  have cp : Continuous p :=
    ((continuous_columnPhase _).mul (continuous_columnPhase _)).mul
      ((continuous_columnPhase _).comp (continuous_id.add continuous_const))
  have hp (t : ℝ) : ‖p t‖ = 1 := by
    simp only [p, norm_mul, norm_columnPhase, mul_one]
  have hb := (phase_cauchy (density W hW) p c cp hp
    (column_continuous K S Γ D C Θ ψ G hν hG J U a γ j d
      (y.1.val.val,y.2) τ)
    (coefficientMass K S D C Θ ψ G hν hG J U a γ j d)
    (column_bound K S Γ D C Θ ψ G hν hG J U a γ j d hΓ y τ)).2
  rw [first_residual_branch_complete K S D Γ C Θ ψ G hν hG J γ j d
    (y.1.val.val,y.2) W hW a τ v X U hZ hv hU hscale]
  have he : (∫ t : ℝ, density W hW t * columnPhase t (Real.log v) *
      columnPhase t (-Real.log X) *
      (((U ^ a : ℝ) : ℂ) * columnPhase (t + τ) (Real.log U)) * c t) =
      ((U ^ a : ℝ) : ℂ) * ∫ t : ℝ, density W hW t * p t * c t := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by dsimp only [p]; ring)
  change ‖∫ t : ℝ, density W hW t * columnPhase t (Real.log v) *
      columnPhase t (-Real.log X) *
      (((U ^ a : ℝ) : ℂ) * columnPhase (t + τ) (Real.log U)) * c t‖ ^ 2 ≤ _
  rw [he, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg hU.le a)]
  exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)


theorem free_energy_integrable (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (τ : ℝ) (H : {r : ℝ // 0 < r}) :
    Integrable (fun t => ‖density W hW t‖ *
      (DivisorInverseColumn.weightedEnergy K S Γ D
        (family K S C Θ ψ G hν hG J U a (t + τ)) γ j d
        (Physical.ActualGramMajorantDraft.rowBallArchTest K S 1)
        (Physical.ActualGramMajorantDraft.rowBallFiniteFamily K S 1) ∅ (rowRadius H)).re) := by
  simp only [free_weightedEnergy_re]
  exact InverseSpectralEnergy.weighted_energy_integrable K S Γ D
    (squarefreePool K Sset (2 * U))
    (fun t => DivisorInverseColumn.coefficient K S D
      (family K S C Θ ψ G hν hG J U a (t + τ)) γ j d)
    (fun n hn => coefficient_continuous K S D C Θ ψ G hν hG J U a γ j d n τ)
    (coefficientMass K S D C Θ ψ G hν hG J U a γ j d)
    (coefficient_mass_bound K S D C Θ ψ G hν hG J U a γ j d τ)
    H (fun t => ‖density W hW t‖) (density W hW).integrable.norm


include hΓ in
/-- The actual residual branches on all retained original sectors are
bounded by the integral of the free positive inverse energy. -/
theorem residual_rows_le_free_energy (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (T : Finset (Ext × Sector)) (τ v X : ℝ) (hZ : 1 < C.base)
    (hv : 0 < v) (hU : 0 < U) (hscale : X = v * U)
    (H : {r : ℝ // 0 < r}) (hT : ∀ y ∈ T, (y.1.val.val.absNorm : ℝ) ≤ H.val) :
    (∑ y ∈ T,
      ‖residualBranch K S D Γ C G J γ j d (y.1.val.val,y.2) W a τ v X U‖ ^ 2) ≤
      ((U ^ a) ^ 2 * (∫ t : ℝ, ‖density W hW t‖)) *
        ((rowCovolume K S)⁻¹ *
          ∫ t : ℝ, ‖density W hW t‖ *
            (DivisorInverseColumn.weightedEnergy K S Γ D
              (family K S C Θ ψ G hν hG J U a (t + τ)) γ j d
              (Physical.ActualGramMajorantDraft.rowBallArchTest K S 1)
              (Physical.ActualGramMajorantDraft.rowBallFiniteFamily K S 1) ∅ (rowRadius H)).re) := by
  let A : ℝ := (U ^ a) ^ 2 * ∫ t : ℝ, ‖density W hW t‖
  have hA : 0 ≤ A := mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => norm_nonneg _))
  let coeff : ℝ → Ext → ℂ := fun t => DivisorInverseColumn.coefficient K S D
    (family K S C Θ ψ G hν hG J U a (t + τ)) γ j d
  let rows := T.image (CanonicalSectors.rowOrbit K Sset Γ D)
  have hrows (q) (hq : q ∈ rows) : (sIntegerOrbitNorm K Sset Γ q).val ≤ H.val := by
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
    rw [CanonicalSectors.rowOrbit_norm]
    exact hT y hy
  have hi := InverseSpectralEnergy.integral_finite_rows_le_energy K S Γ D
    (squarefreePool K Sset (2 * U)) coeff
    (fun n hn => coefficient_continuous K S D C Θ ψ G hν hG J U a γ j d n τ)
    (coefficientMass K S D C Θ ψ G hν hG J U a γ j d)
    (coefficient_mass_bound K S D C Θ ψ G hν hG J U a γ j d τ)
    H rows hrows (fun t => ‖density W hW t‖) (density W hW).integrable.norm
    (fun _ => norm_nonneg _)
  have hleft (t : ℝ) :
      (∑ q ∈ rows, ‖amplitude K S Γ D (squarefreePool K Sset (2 * U)) (coeff t) q‖ ^ 2) =
      ∑ y ∈ T, ‖DivisorInverseColumn.column K S Γ D
        (family K S C Θ ψ G hν hG J U a (t + τ)) γ j d (y.1.val.val,y.2)‖ ^ 2 := by
    dsimp only [rows]
    rw [Finset.sum_image
      (fun _ _ _ _ h => CanonicalSectors.rowOrbit_injective K Sset Γ D h)]
    apply Finset.sum_congr rfl
    intro y hy
    rw [column_eq_amplitude K S Γ D C Θ ψ G hν hG J U a γ j d hΓ]
  have hright (t : ℝ) :
      energy K S Γ D (squarefreePool K Sset (2 * U)) (coeff t) H =
      (DivisorInverseColumn.weightedEnergy K S Γ D
        (family K S C Θ ψ G hν hG J U a (t + τ)) γ j d
        (Physical.ActualGramMajorantDraft.rowBallArchTest K S 1)
        (Physical.ActualGramMajorantDraft.rowBallFiniteFamily K S 1) ∅ (rowRadius H)).re :=
    (free_weightedEnergy_re K S Γ D
      (family K S C Θ ψ G hν hG J U a (t + τ)) γ j d H).symm
  simp only [hleft, hright] at hi
  calc
    _ ≤ ∑ y ∈ T, A * (∫ t : ℝ, ‖density W hW t‖ *
        ‖DivisorInverseColumn.column K S Γ D
          (family K S C Θ ψ G hν hG J U a (t + τ)) γ j d (y.1.val.val,y.2)‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro y hy
      exact (residual_branch_sq_le K S Γ D C Θ ψ G hν hG J U a γ j d hΓ
        W hW y τ v X hZ hv hU hscale).trans_eq (by dsimp only [A]; ring)
    _ = A * ∫ t : ℝ, ‖density W hW t‖ *
        (∑ y ∈ T, ‖DivisorInverseColumn.column K S Γ D
          (family K S C Θ ψ G hν hG J U a (t + τ)) γ j d (y.1.val.val,y.2)‖ ^ 2) := by
      rw [← Finset.mul_sum, ← integral_finset_sum T
        (fun y hy => column_energy_integrable K S Γ D C Θ ψ G hν hG J U a γ j d hΓ
          W hW y τ)]
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => (Finset.mul_sum _ _ _).symm)
    _ ≤ _ := mul_le_mul_of_nonneg_left hi hA

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstMellinEnergy

end

