import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderFiniteClosure

/-!
# Uniformity in the original total mark length

The total original mark budget remains a universally quantified source
parameter after the finite seminorm, scalar and base threshold have been
selected. Both genuine provider branches already have this uniformity.
The backwards induction selects its constants for the entire interval
of mark budgets together, while preserving each node's actual mark
lengths, coefficients and margins.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderUniformMarks

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOM_INV_STEP
open ProviderNodes CubeCompletionGeometry CubeCompletionMellin
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
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
variable (Θ : Subgroup (HeckeCharacter K)) (ψ Λ G : HeckeCharacter K)

include hΓ hallowed μv ν μ in
/-- The actual local implication is uniform in every mark budget in
the fixed interval. The original mark budget is selected only after the
common seminorm and scalar. -/
theorem exists_uniform_local_step_uniform_marks
    (hG : G ∈ Θ) (slotCap : ℕ) (A pi tauMin cLower zMax lo hi d Z₀ : ℝ)
    (hA : 1 ≤ A) (hpi : 0 < pi) (htauMin : 0 < tauMin)
    (qShort : Finset (ℕ × ℕ)) (CShort : ℝ) (hCShort : 0 ≤ CShort)
    (hshort : ∀ {σ : Type u} (Z Fcap c z : ℝ) (x : Node K S Γ Θ ψ σ),
      Z₀ ≤ Z → Fcap ≤ A → cLower ≤ c → 0 ≤ z → z ≤ zMax →
      x.Admissible D Λ G slotCap Z Fcap c z lo hi → x.labelLength < d →
      TerminalNodes.shortEnergy K S Γ D slotCap x (Z ^ d) ≤
        CShort * (qShort.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 * Z ^ x.totalLength)
    (t : Finset (ℕ × ℕ)) :
    ∃ q : Finset (ℕ × ℕ), ∃ C : ℝ, 1 ≤ C ∧
      ∀ (Z Fcap c z eta h tau eps Cih Rmax : ℝ),
      2 ≤ Z → Z₀ ≤ Z → Fcap ≤ A → cLower ≤ c → 0 ≤ c - eta / 2 → 0 ≤ z → z ≤ zMax →
      h ∈ Set.Icc (0 : ℝ) 1 → tau ∈ Set.Icc (0 : ℝ) A → tauMin ≤ tau →
      2 ≤ Z ^ h → h ≤ eta / 128 → eta ≤ d / 16 →
      0 ≤ eps → 1 ≤ Cih →
      (∀ i : SchwartzTestPartition.Index, |Real.logb Z (annularScale i)| ≤ eta / 8) →
      UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
        (Fcap + 11 * eta) (c - 7 * eta) z lo hi eps (Rmax - d) Cih t →
      UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
        Fcap c z lo hi (eps + (40 * eta + tau + pi)) Rmax (3 * C * Cih) q := by
  obtain ⟨qLabel, CLabel, hCLabel, hlabel⟩ := ProviderNodeStep.exists_uniform_long_label_step
    K S D Γ hΓ hallowed μv ν μ slotCap A pi tauMin hA hpi htauMin t
  obtain ⟨qCube, CCube, hCCube, hcube⟩ := CubeCompletionLong.exists_uniform_long_cube_step
    K S D Γ hΓ hallowed μv ν μ slotCap A pi tauMin hA hpi htauMin t
  let q := qLabel ∪ qCube ∪ qShort
  let C := CLabel + CCube + CShort
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  refine ⟨q, C, hC, ?_⟩
  intro Z Fcap c z eta h tau eps Cih Rmax hZ hZ₀ hFcap hcLower hc hz hzMax
    hh htau htau' hwidth hmesh hstepsize heps hCih hshift hih
  intro σ x hx hrow
  have hz1 : 1 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hz0 := zero_lt_one.trans hz1
  have heta : 0 ≤ eta := by linarith [hh.1]
  have hc0 : 0 ≤ c := by linarith
  have hCih0 : 0 ≤ Cih := zero_le_one.trans hCih
  have hqLabel : qLabel.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test ≤
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left.trans Finset.subset_union_left)) _
  have hqCube : qCube.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test ≤
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_right.trans Finset.subset_union_left)) _
  have hqShort : qShort.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test ≤
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) _
  have hexp : x.totalLength + eps + (40 * eta + tau + pi) =
      x.totalLength + 40 * eta + tau + pi + eps := by ring
  change x.energy D slotCap ≤ (3 * C * Cih) *
    (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 *
      Z ^ (x.totalLength + (eps + (40 * eta + tau + pi)))
  rw [show x.totalLength + (eps + (40 * eta + tau + pi)) =
    x.totalLength + 40 * eta + tau + pi + eps by ring]
  by_cases hlong : d ≤ x.labelLength
  · have hp := hlabel Θ ψ Λ G hG Z Fcap c z lo hi d eta h tau eps Cih Rmax x
      hZ hFcap hc0 hz hx hrow hh htau htau' hwidth (by linarith) hstepsize hlong heps hCih hih
    apply hp.trans
    gcongr
    · dsimp only [C]; linarith
  · have hshort' := hshort Z Fcap c z x hZ₀ hFcap hcLower hz hzMax hx (lt_of_not_ge hlong)
    have hcube' := hcube Θ ψ Λ G hG Z Fcap c z lo hi d eta h tau eps Cih Rmax x
      hZ hFcap hc hz hx hrow hh htau htau' hwidth hmesh hstepsize heps hCih hih hshift
    let E := (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 *
      Z ^ (x.totalLength + 40 * eta + tau + pi + eps)
    have hE : 0 ≤ E := by dsimp only [E]; positivity
    have hs : TerminalNodes.shortEnergy K S Γ D slotCap x (Z ^ d) ≤ CShort * Cih * E := by
      apply hshort'.trans
      calc
        _ ≤ (CShort * Cih) * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 *
            Z ^ (x.totalLength + 40 * eta + tau + pi + eps) := by
          gcongr
          · exact le_mul_of_one_le_right hCShort hCih
          · exact hz1.le
          · linarith [htau.1]
        _ = _ := by dsimp only [E]; ring
    have hl : TerminalNodes.longEnergy K S Γ D slotCap x (Z ^ d) ≤ CCube * Cih * E := by
      apply hcube'.trans
      dsimp only [E]
      rw [← mul_assoc]
      gcongr
    have hsplit := TerminalNodes.energy_le_short_long K S Γ D Λ G slotCap Z Fcap c z lo hi x hx hz0 (Z ^ d)
    apply hsplit.trans
    calc
      _ ≤ 2 * (CShort * Cih * E + CCube * Cih * E) := by gcongr
      _ = (2 * (CShort + CCube)) * Cih * E := by ring
      _ ≤ (3 * C) * Cih * E := by
        apply mul_le_mul_of_nonneg_right _ hE
        apply mul_le_mul_of_nonneg_right _ hCih0
        dsimp only [C]
        linarith
      _ = _ := by dsimp only [E]; ring


variable {K S Γ Θ ψ}
variable (slotCap : ℕ)

/-- Finite backwards induction chooses the base threshold at the same
time as the seminorm and scalar. No common threshold over infinitely
many possible child seminorms occurs in the hypothesis. -/
theorem exists_uniform_bound_with_thresholds_uniform_marks
    (depth : ℕ) (d eta loss Mmax Fmax c zMax lo hi : ℝ)
    (hdepth : Mmax < (depth : ℝ) * d) (hloss : 0 ≤ loss)
    (hstep : ∀ t : Finset (ℕ × ℕ),
      ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 1 ≤ C ∧ 2 ≤ Z₀ ∧
        ∀ j : ℕ, j < depth → ∀ Z : ℝ, Z₀ ≤ Z →
        ∀ z : ℝ, 0 ≤ z → z ≤ zMax →
        ∀ eps B : ℝ, 0 ≤ eps → 1 ≤ B →
        UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
          (stageCapacity Fmax eta (j + 1)) (stageMargin c eta (j + 1))
          z lo hi eps (stageRowBound Mmax d (j + 1)) B t →
        UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
          (stageCapacity Fmax eta j) (stageMargin c eta j)
          z lo hi (eps + loss) (stageRowBound Mmax d j) (3 * C * B) q) :
    ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 1 ≤ C ∧ 2 ≤ Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ∀ z : ℝ, 0 ≤ z → z ≤ zMax →
        UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap
          Z Fmax c z lo hi ((depth : ℝ) * loss) Mmax C q := by
  have stages : ∀ n : ℕ, n ≤ depth →
      ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 1 ≤ C ∧ 2 ≤ Z₀ ∧
        ∀ j : ℕ, j + n = depth → ∀ Z : ℝ, Z₀ ≤ Z → ∀ z : ℝ, 0 ≤ z → z ≤ zMax →
        UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
          (stageCapacity Fmax eta j) (stageMargin c eta j)
          z lo hi ((n : ℝ) * loss) (stageRowBound Mmax d j) C q := by
    intro n
    induction n with
    | zero =>
      intro hn
      refine ⟨∅, 1, 2, le_rfl, le_rfl, ?_⟩
      intro j hj Z hZ z hz hzMax
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
      intro j hj Z hZ z hz hzMax
      have hjlt : j < depth := by omega
      have hprev : UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ)
          D Λ G slotCap Z (stageCapacity Fmax eta (j + 1))
          (stageMargin c eta (j + 1)) z lo hi ((n : ℝ) * loss)
          (stageRowBound Mmax d (j + 1)) B t :=
        hchild (j + 1) (by omega) Z ((le_max_left _ _).trans hZ) z hz hzMax
      have hnext : UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ)
          D Λ G slotCap Z (stageCapacity Fmax eta j) (stageMargin c eta j)
          z lo hi ((n : ℝ) * loss + loss) (stageRowBound Mmax d j)
          (3 * C * B) q := hlocal j hjlt Z ((le_max_right _ _).trans hZ) z hz hzMax
        ((n : ℝ) * loss) B (mul_nonneg (Nat.cast_nonneg _) hloss) hB hprev
      have he : (n : ℝ) * loss + loss = ((n + 1 : ℕ) : ℝ) * loss := by
        push_cast
        ring
      rw [← he]
      intro σ x hx hrow
      exact hnext x hx hrow
  obtain ⟨q, C, Z₀, hC, hZ₀, hq⟩ := stages depth le_rfl
  refine ⟨q, C, Z₀, hC, hZ₀, ?_⟩
  intro Z hZ z hz hzMax
  have hzero : UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ)
      D Λ G slotCap Z (stageCapacity Fmax eta 0) (stageMargin c eta 0)
      z lo hi ((depth : ℝ) * loss) (stageRowBound Mmax d 0) C q :=
    hq 0 (by omega) Z hZ z hz hzMax
  simp only [stageCapacity, stageMargin, stageRowBound, Nat.cast_zero,
    mul_zero, zero_mul, add_zero, sub_zero] at hzero
  intro σ x hx hrow
  exact hzero x hx hrow

theorem exists_uniform_bound_of_budget_with_thresholds_uniform_marks
    {Mmax c eps : ℝ} (b : DescentBudget Mmax c eps)
    (Fmax zMax lo hi : ℝ)
    (hstep : ∀ t : Finset (ℕ × ℕ),
      ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 1 ≤ C ∧ 2 ≤ Z₀ ∧
        ∀ j : ℕ, j < b.depth → ∀ Z : ℝ, Z₀ ≤ Z →
        ∀ z : ℝ, 0 ≤ z → z ≤ zMax →
        ∀ e B : ℝ, 0 ≤ e → 1 ≤ B →
        UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
          (stageCapacity Fmax b.eta (j + 1)) (stageMargin c b.eta (j + 1))
          z lo hi e (stageRowBound Mmax b.step (j + 1)) B t →
        UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
          (stageCapacity Fmax b.eta j) (stageMargin c b.eta j)
          z lo hi (e + (40 * b.eta + b.tau + b.pi))
          (stageRowBound Mmax b.step j) (3 * C * B) q) :
    ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 1 ≤ C ∧ 2 ≤ Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ∀ z : ℝ, 0 ≤ z → z ≤ zMax →
        UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap
          Z Fmax c z lo hi (eps / 2) Mmax C q := by
  have hloss : 0 ≤ 40 * b.eta + b.tau + b.pi := by
    have := b.eta_pos
    have := b.tau_pos
    have := b.pi_pos
    positivity
  obtain ⟨q, C, Z₀, hC, hZ₀, hbound⟩ := exists_uniform_bound_with_thresholds_uniform_marks D Λ G slotCap
    b.depth b.step b.eta (40 * b.eta + b.tau + b.pi) Mmax Fmax c zMax lo hi
    b.depth_bound hloss hstep
  refine ⟨q, C, Z₀, hC, hZ₀, ?_⟩
  intro Z hZ z hz hzMax
  exact ProviderInduction.uniformBound_mono_loss D Λ G slotCap Z Fmax c z lo hi
    ((b.depth : ℝ) * (40 * b.eta + b.tau + b.pi)) (eps / 2) Mmax C q
    ((by norm_num : (1 : ℝ) ≤ 2).trans (hZ₀.trans hZ))
    (zero_le_one.trans hC) b.loss_budget.le (hbound Z hZ z hz hzMax)



include hΓ hallowed μv ν μ in
/-- Stage specialization for the literal canonical local step. The
fine mesh, every fixed annular dilation and the short-source threshold
share one base threshold before the backwards seminorm construction. -/
theorem exists_stage_steps_of_short_contribution_uniform_marks
    (hG : G ∈ Θ) {Mmax c eps : ℝ} (b : DescentBudget Mmax c eps) (hc : 0 < c)
    (Fmax A zMax lo hi : ℝ) (hA : 1 ≤ A)
    (hcapacity : max 1 (stageCapacity Fmax b.eta b.depth) ≤ A)
    (htau : b.tau ≤ A) (hzMax : 0 ≤ zMax)
    (qShort : Finset (ℕ × ℕ)) (CShort ZShort : ℝ) (hCShort : 0 ≤ CShort)
    (hshort : ∀ z : ℝ, 0 ≤ z → z ≤ zMax →
      ∀ {σ : Type u} (Z Fcap cStage : ℝ) (x : Node K S Γ Θ ψ σ),
      ZShort ≤ Z → Fcap ≤ A → c / 2 ≤ cStage →
      x.Admissible D Λ G slotCap Z Fcap cStage z lo hi → x.labelLength < b.step →
      TerminalNodes.shortEnergy K S Γ D slotCap x (Z ^ b.step) ≤
        CShort * (qShort.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 * Z ^ x.totalLength) :
    ∀ t : Finset (ℕ × ℕ),
      ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 1 ≤ C ∧ 2 ≤ Z₀ ∧
        ∀ j : ℕ, j < b.depth → ∀ Z : ℝ, Z₀ ≤ Z →
        ∀ z : ℝ, 0 ≤ z → z ≤ zMax →
        ∀ e B : ℝ, 0 ≤ e → 1 ≤ B →
        UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
          (stageCapacity Fmax b.eta (j + 1)) (stageMargin c b.eta (j + 1))
          z lo hi e (stageRowBound Mmax b.step (j + 1)) B t →
        UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
          (stageCapacity Fmax b.eta j) (stageMargin c b.eta j)
          z lo hi (e + (40 * b.eta + b.tau + b.pi))
          (stageRowBound Mmax b.step j) (3 * C * B) q := by
  obtain ⟨ZFine, hZFine, hfine⟩ := exists_fine_scale_threshold b partitionScaleCap partitionScaleCap_one_le
  intro t
  obtain ⟨q, C, hC, hlocal⟩ := exists_uniform_local_step_uniform_marks
    K S D Γ hΓ hallowed μv ν μ Θ ψ Λ G hG slotCap A b.pi b.tau (c / 2) zMax lo hi b.step ZShort
    hA b.pi_pos b.tau_pos qShort CShort hCShort (by
      intro σ Z Fcap cStage z x hZ hFcap hcStage hz hzMax hx hV
      exact hshort z hz hzMax Z Fcap cStage x hZ hFcap hcStage hx hV) t
  refine ⟨q, C, max ZFine ZShort, hC, hZFine.trans (le_max_left _ _), ?_⟩
  intro j hj Z hZ z hz hzUpper e B he hB hih
  have hjle : j ≤ b.depth := Nat.le_of_lt hj
  have hZF : ZFine ≤ Z := (le_max_left _ _).trans hZ
  have hZS : ZShort ≤ Z := (le_max_right _ _).trans hZ
  obtain ⟨hwidth, hscale, hlogs⟩ := hfine Z hZF
  have hmesh := fineMesh_spec b
  have hshift (i : SchwartzTestPartition.Index) :
      |Real.logb Z (annularScale i)| ≤ b.eta / 8 :=
    hlogs _ (annular_scale_bounds i).1 (annular_scale_bounds i).2
  have hih' : UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
      (stageCapacity Fmax b.eta j + 11 * b.eta) (stageMargin c b.eta j - 7 * b.eta)
      z lo hi e (stageRowBound Mmax b.step j - b.step) B t := by
    simp only [stageCapacity_succ, stageMargin_succ, stageRowBound_succ] at hih
    intro σ x hx hrow
    exact hih x hx hrow
  exact hlocal Z (stageCapacity Fmax b.eta j) (stageMargin c b.eta j) z
    b.eta (fineMesh b) b.tau e B (stageRowBound Mmax b.step j)
    (hZFine.trans hZF) hZS ((stageCapacity_le_common b.eta_pos.le hjle).trans hcapacity)
    (stageMargin_lower b hjle) (stageMargin_half_eta_nonneg b hc hjle) hz hzUpper
    ⟨hmesh.1.le, hmesh.2.1⟩ ⟨b.tau_pos.le, htau⟩ le_rfl
    hwidth hmesh.2.2 b.eta_step he hB hshift hih'

include hΓ hallowed μv ν μ in
/-- All actual node energies close with the allocated epsilon once
the proved uniform short-completion estimate is inserted. -/
theorem exists_uniform_bound_of_short_contribution_uniform_marks
    (hG : G ∈ Θ) {Mmax c eps : ℝ} (b : DescentBudget Mmax c eps) (hc : 0 < c)
    (Fmax A zMax lo hi : ℝ) (hA : 1 ≤ A)
    (hcapacity : max 1 (stageCapacity Fmax b.eta b.depth) ≤ A)
    (htau : b.tau ≤ A) (hzMax : 0 ≤ zMax)
    (qShort : Finset (ℕ × ℕ)) (CShort ZShort : ℝ) (hCShort : 0 ≤ CShort)
    (hshort : ∀ z : ℝ, 0 ≤ z → z ≤ zMax →
      ∀ {σ : Type u} (Z Fcap cStage : ℝ) (x : Node K S Γ Θ ψ σ),
      ZShort ≤ Z → Fcap ≤ A → c / 2 ≤ cStage →
      x.Admissible D Λ G slotCap Z Fcap cStage z lo hi → x.labelLength < b.step →
      TerminalNodes.shortEnergy K S Γ D slotCap x (Z ^ b.step) ≤
        CShort * (qShort.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 * Z ^ x.totalLength) :
    ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 1 ≤ C ∧ 2 ≤ Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ∀ z : ℝ, 0 ≤ z → z ≤ zMax →
        UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap
          Z Fmax c z lo hi (eps / 2) Mmax C q := by
  exact exists_uniform_bound_of_budget_with_thresholds_uniform_marks D Λ G slotCap b Fmax zMax lo hi
    (exists_stage_steps_of_short_contribution_uniform_marks (K := K) (S := S) (Γ := Γ) (Θ := Θ) (ψ := ψ)
      (D := D) (Λ := Λ) (G := G) (slotCap := slotCap)
      (hΓ := hΓ) (hallowed := hallowed) (μv := μv) (ν := ν) (μ := μ)
      hG b hc Fmax A zMax lo hi hA hcapacity htau hzMax qShort CShort ZShort hCShort hshort)


end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderUniformMarks
