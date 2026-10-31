import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInduction
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderLocalStep

/-!
# Backwards finite closure with jointly chosen base thresholds

The child seminorm may influence the threshold of a local analytic
estimate. At each of the finitely many backwards stages this file
therefore selects the parent seminorm, its scalar and its base threshold
together. The maximum with the already selected child threshold is
taken immediately. The final threshold precedes every actual source.

The second theorem specializes the actual long-label and completed-cube
local step to the exact stage schedule. Its explicit short-contribution
argument is the point where the separately proved terminal analytic
theorem is inserted; the induction never assumes an arbitrary leaf
energy or a whole-node terminal estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderFiniteClosure

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOM_INV_STEP
open ProviderNodes CubeCompletionGeometry CubeCompletionMellin
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
variable {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Λ G : HeckeCharacter K) (slotCap : ℕ)

/-- Finite backwards induction chooses the base threshold at the same
time as the seminorm and scalar. No common threshold over infinitely
many possible child seminorms occurs in the hypothesis. -/
theorem exists_uniform_bound_with_thresholds
    (depth : ℕ) (d eta loss Mmax Fmax c z lo hi : ℝ)
    (hdepth : Mmax < (depth : ℝ) * d) (hloss : 0 ≤ loss)
    (hstep : ∀ t : Finset (ℕ × ℕ),
      ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 1 ≤ C ∧ 2 ≤ Z₀ ∧
        ∀ j : ℕ, j < depth → ∀ Z : ℝ, Z₀ ≤ Z →
        ∀ eps B : ℝ, 0 ≤ eps → 1 ≤ B →
        UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
          (stageCapacity Fmax eta (j + 1)) (stageMargin c eta (j + 1))
          z lo hi eps (stageRowBound Mmax d (j + 1)) B t →
        UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
          (stageCapacity Fmax eta j) (stageMargin c eta j)
          z lo hi (eps + loss) (stageRowBound Mmax d j) (3 * C * B) q) :
    ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 1 ≤ C ∧ 2 ≤ Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z →
        UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap
          Z Fmax c z lo hi ((depth : ℝ) * loss) Mmax C q := by
  have stages : ∀ n : ℕ, n ≤ depth →
      ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 1 ≤ C ∧ 2 ≤ Z₀ ∧
        ∀ j : ℕ, j + n = depth → ∀ Z : ℝ, Z₀ ≤ Z →
        UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
          (stageCapacity Fmax eta j) (stageMargin c eta j)
          z lo hi ((n : ℝ) * loss) (stageRowBound Mmax d j) C q := by
    intro n
    induction n with
    | zero =>
      intro hn
      refine ⟨∅, 1, 2, le_rfl, le_rfl, ?_⟩
      intro j hj Z hZ
      have heq : j = depth := by omega
      subst j
      apply ProviderInduction.uniformBound_of_negative_row_cap
      dsimp only [stageRowBound]
      linarith
    | succ n ih =>
      intro hn
      obtain ⟨t, B, ZChild, hB, hZChild, hchild⟩ := ih (by omega)
      obtain ⟨q, C, ZStep, hC, hZStep, hlocal⟩ := hstep t
      have hCB : 1 ≤ 3 * C * B := by
        nlinarith [one_le_mul_of_one_le_of_one_le hC hB]
      refine ⟨q, 3 * C * B, max ZChild ZStep, hCB,
        hZChild.trans (le_max_left _ _), ?_⟩
      intro j hj Z hZ
      have hjlt : j < depth := by omega
      have hprev := hchild (j + 1) (by omega) Z ((le_max_left _ _).trans hZ)
      have hnext := hlocal j hjlt Z ((le_max_right _ _).trans hZ)
        ((n : ℝ) * loss) B (mul_nonneg (Nat.cast_nonneg _) hloss) hB hprev
      have he : (n : ℝ) * loss + loss = ((n + 1 : ℕ) : ℝ) * loss := by
        push_cast
        ring
      simpa only [he] using hnext
  obtain ⟨q, C, Z₀, hC, hZ₀, hq⟩ := stages depth le_rfl
  refine ⟨q, C, Z₀, hC, hZ₀, ?_⟩
  intro Z hZ
  simpa only [stageCapacity, stageMargin, stageRowBound, Nat.cast_zero,
    mul_zero, zero_mul, add_zero, sub_zero] using hq 0 (by omega) Z hZ

theorem exists_uniform_bound_of_budget_with_thresholds
    {Mmax c eps : ℝ} (b : DescentBudget Mmax c eps)
    (Fmax z lo hi : ℝ)
    (hstep : ∀ t : Finset (ℕ × ℕ),
      ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 1 ≤ C ∧ 2 ≤ Z₀ ∧
        ∀ j : ℕ, j < b.depth → ∀ Z : ℝ, Z₀ ≤ Z →
        ∀ e B : ℝ, 0 ≤ e → 1 ≤ B →
        UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
          (stageCapacity Fmax b.eta (j + 1)) (stageMargin c b.eta (j + 1))
          z lo hi e (stageRowBound Mmax b.step (j + 1)) B t →
        UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
          (stageCapacity Fmax b.eta j) (stageMargin c b.eta j)
          z lo hi (e + (40 * b.eta + b.tau + b.pi))
          (stageRowBound Mmax b.step j) (3 * C * B) q) :
    ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 1 ≤ C ∧ 2 ≤ Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z →
        UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap
          Z Fmax c z lo hi (eps / 2) Mmax C q := by
  have hloss : 0 ≤ 40 * b.eta + b.tau + b.pi := by
    have := b.eta_pos
    have := b.tau_pos
    have := b.pi_pos
    positivity
  obtain ⟨q, C, Z₀, hC, hZ₀, hbound⟩ := exists_uniform_bound_with_thresholds D Λ G slotCap
    b.depth b.step b.eta (40 * b.eta + b.tau + b.pi) Mmax Fmax c z lo hi
    b.depth_bound hloss hstep
  refine ⟨q, C, Z₀, hC, hZ₀, ?_⟩
  intro Z hZ
  exact ProviderInduction.uniformBound_mono_loss D Λ G slotCap Z Fmax c z lo hi
    ((b.depth : ℝ) * (40 * b.eta + b.tau + b.pi)) (eps / 2) Mmax C q
    ((by norm_num : (1 : ℝ) ≤ 2).trans (hZ₀.trans hZ))
    (zero_le_one.trans hC) b.loss_budget.le (hbound Z hZ)

variable (K S Γ Θ ψ)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include hΓ hallowed μv ν μ in
/-- Stage specialization for the literal canonical local step. The
fine mesh, every fixed annular dilation and the short-source threshold
share one base threshold before the backwards seminorm construction. -/
theorem exists_stage_steps_of_short_contribution
    (hG : G ∈ Θ) {Mmax c eps : ℝ} (b : DescentBudget Mmax c eps) (hc : 0 < c)
    (Fmax A z lo hi : ℝ) (hA : 1 ≤ A)
    (hcapacity : max 1 (stageCapacity Fmax b.eta b.depth) ≤ A)
    (htau : b.tau ≤ A) (hz : 0 ≤ z)
    (qShort : Finset (ℕ × ℕ)) (CShort ZShort : ℝ) (hCShort : 0 ≤ CShort)
    (hshort : ∀ {σ : Type*} (Z Fcap cStage : ℝ) (x : Node K S Γ Θ ψ σ),
      ZShort ≤ Z → Fcap ≤ A → c / 2 ≤ cStage →
      x.Admissible D Λ G slotCap Z Fcap cStage z lo hi → x.labelLength < b.step →
      TerminalNodes.shortEnergy K S Γ D slotCap x (Z ^ b.step) ≤
        CShort * (qShort.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 * Z ^ x.totalLength) :
    ∀ t : Finset (ℕ × ℕ),
      ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 1 ≤ C ∧ 2 ≤ Z₀ ∧
        ∀ j : ℕ, j < b.depth → ∀ Z : ℝ, Z₀ ≤ Z →
        ∀ e B : ℝ, 0 ≤ e → 1 ≤ B →
        UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
          (stageCapacity Fmax b.eta (j + 1)) (stageMargin c b.eta (j + 1))
          z lo hi e (stageRowBound Mmax b.step (j + 1)) B t →
        UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
          (stageCapacity Fmax b.eta j) (stageMargin c b.eta j)
          z lo hi (e + (40 * b.eta + b.tau + b.pi))
          (stageRowBound Mmax b.step j) (3 * C * B) q := by
  obtain ⟨ZFine, hZFine, hfine⟩ := exists_fine_scale_threshold b partitionScaleCap partitionScaleCap_one_le
  intro t
  obtain ⟨q, C, hC, hlocal⟩ := ProviderLocalStep.exists_uniform_local_step_of_short_contribution
    K S D Γ hΓ hallowed μv ν μ Θ ψ Λ G hG slotCap A b.pi b.tau (c / 2) z lo hi b.step ZShort
    hA b.pi_pos b.tau_pos qShort CShort hCShort hshort t
  refine ⟨q, C, max ZFine ZShort, hC, hZFine.trans (le_max_left _ _), ?_⟩
  intro j hj Z hZ e B he hB hih
  have hjle : j ≤ b.depth := Nat.le_of_lt hj
  have hZF : ZFine ≤ Z := (le_max_left _ _).trans hZ
  have hZS : ZShort ≤ Z := (le_max_right _ _).trans hZ
  obtain ⟨hwidth, hscale, hlogs⟩ := hfine Z hZF
  have hmesh := fineMesh_spec b
  have hshift (i : SchwartzTestPartition.Index) :
      |Real.logb Z (annularScale i)| ≤ b.eta / 8 :=
    hlogs _ (annular_scale_bounds i).1 (annular_scale_bounds i).2
  have hih' : UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
      (stageCapacity Fmax b.eta j + 11 * b.eta) (stageMargin c b.eta j - 7 * b.eta)
      z lo hi e (stageRowBound Mmax b.step j - b.step) B t := by
    simpa only [stageCapacity_succ, stageMargin_succ, stageRowBound_succ] using hih
  exact hlocal Z (stageCapacity Fmax b.eta j) (stageMargin c b.eta j)
    b.eta (fineMesh b) b.tau e B (stageRowBound Mmax b.step j)
    (hZFine.trans hZF) hZS ((stageCapacity_le_common b.eta_pos.le hjle).trans hcapacity)
    (stageMargin_lower b hjle) (stageMargin_half_eta_nonneg b hc hjle) hz
    ⟨hmesh.1.le, hmesh.2.1⟩ ⟨b.tau_pos.le, htau⟩ le_rfl
    hwidth hmesh.2.2 b.eta_step he hB hshift hih'

include hΓ hallowed μv ν μ in
/-- All actual node energies close with the allocated epsilon once
the proved uniform short-completion estimate is inserted. -/
theorem exists_uniform_bound_of_short_contribution
    (hG : G ∈ Θ) {Mmax c eps : ℝ} (b : DescentBudget Mmax c eps) (hc : 0 < c)
    (Fmax A z lo hi : ℝ) (hA : 1 ≤ A)
    (hcapacity : max 1 (stageCapacity Fmax b.eta b.depth) ≤ A)
    (htau : b.tau ≤ A) (hz : 0 ≤ z)
    (qShort : Finset (ℕ × ℕ)) (CShort ZShort : ℝ) (hCShort : 0 ≤ CShort)
    (hshort : ∀ {σ : Type*} (Z Fcap cStage : ℝ) (x : Node K S Γ Θ ψ σ),
      ZShort ≤ Z → Fcap ≤ A → c / 2 ≤ cStage →
      x.Admissible D Λ G slotCap Z Fcap cStage z lo hi → x.labelLength < b.step →
      TerminalNodes.shortEnergy K S Γ D slotCap x (Z ^ b.step) ≤
        CShort * (qShort.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 * Z ^ x.totalLength) :
    ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 1 ≤ C ∧ 2 ≤ Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z →
        UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap
          Z Fmax c z lo hi (eps / 2) Mmax C q := by
  exact exists_uniform_bound_of_budget_with_thresholds D Λ G slotCap b Fmax z lo hi
    (exists_stage_steps_of_short_contribution (K := K) (S := S) (Γ := Γ) (Θ := Θ) (ψ := ψ)
      (D := D) (Λ := Λ) (G := G) (slotCap := slotCap)
      (hΓ := hΓ) (hallowed := hallowed) (μv := μv) (ν := ν) (μ := μ)
      hG b hc Fmax A z lo hi hA hcapacity htau hz qShort CShort ZShort hCShort hshort)

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderFiniteClosure
