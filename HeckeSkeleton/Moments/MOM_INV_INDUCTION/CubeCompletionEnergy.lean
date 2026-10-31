import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionMellin
import HeckeSkeleton.Moments.MOM_INV_STEP.IntegralEnergy
import HeckePort.Moments.Descent.SieveComposition

/-!
# Positive energy of the exact reopened Mellin polynomial

The arithmetic coefficient below is arbitrary so that the original
canonical coefficient, cube divisor weight, label, row, puncture, and
whole-index mark can all remain literal. Every auxiliary column is
defined by its finite sum. Continuity and integrability follow from
that finite sum before integral Cauchy is applied.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionEnergy

open MeasureTheory
open HeckeSkeleton.Moments.MOM_INV_STEP
open HeckeSkeleton.Moments.MOMInvStep
open CommonKernel MellinSeparation CubeCompletionMellin
open scoped Classical BigOperators

variable {β α κ : Type*}

def source (B : Finset β) (N : Finset α) (bNorm : β → ℝ) (nNorm : α → ℝ)
    (a : β → α → ℂ) (W : SchwartzMap ℝ ℂ) (X : ℝ) : ℂ :=
  ∑ b ∈ B, ∑ n ∈ N, a b n * W (bNorm b ^ 3 * nNorm n / X)

def annularColumn (B : Finset β) (N : Finset α)
    (bNorm : β → ℝ) (nNorm : α → ℝ) (a : β → α → ℂ)
    (U t : ℝ) (i : SchwartzTestPartition.Index) : ℂ :=
  ∑ b ∈ B, columnPhase t (Real.log (bNorm b ^ 3)) *
    ∑ n ∈ N, a b n * annularTest t i
      (nNorm n / (SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U))

def windowBound : ℝ := SchwartzMap.seminorm ℝ 0 0 SchwartzTestPartition.window

theorem windowBound_nonneg : 0 ≤ windowBound := apply_nonneg _ _

theorem annularTest_continuous (i : SchwartzTestPartition.Index) (x : ℝ) :
    Continuous (fun t : ℝ => annularTest t i x) := by
  simp only [annularTest, SchwartzTestPartition.piece_apply]
  exact (FinalMellinTests.continuous_weightedTest 0 _).mul continuous_const

theorem annularTest_norm_le (t : ℝ) (i : SchwartzTestPartition.Index) (x : ℝ) :
    ‖annularTest t i x‖ ≤ windowBound := by
  simp only [annularTest, SchwartzTestPartition.piece_apply, norm_mul,
    FinalMellinTests.norm_weightedTest, Real.rpow_zero, norm_one, mul_one]
  exact (mul_le_mul (FinalMellinTests.norm_cutoff_le_one _)
    (SchwartzMap.norm_le_seminorm ℝ SchwartzTestPartition.window x)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

def coefficientMass (B : Finset β) (N : Finset α) (a : β → α → ℂ) : ℝ :=
  ∑ b ∈ B, ∑ n ∈ N, ‖a b n‖ * windowBound

theorem annularColumn_continuous (B : Finset β) (N : Finset α)
    (bNorm : β → ℝ) (nNorm : α → ℝ) (a : β → α → ℂ)
    (U : ℝ) (i : SchwartzTestPartition.Index) :
    Continuous (fun t : ℝ => annularColumn B N bNorm nNorm a U t i) := by
  unfold annularColumn
  apply continuous_finsetSum
  intro b hb
  apply (continuous_columnPhase _).mul
  apply continuous_finsetSum
  intro n hn
  exact continuous_const.mul (annularTest_continuous i _)

theorem annularColumn_norm_le (B : Finset β) (N : Finset α)
    (bNorm : β → ℝ) (nNorm : α → ℝ) (a : β → α → ℂ)
    (U t : ℝ) (i : SchwartzTestPartition.Index) :
    ‖annularColumn B N bNorm nNorm a U t i‖ ≤ coefficientMass B N a := by
  unfold annularColumn coefficientMass
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b hb
  rw [norm_mul, norm_columnPhase, one_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (annularTest_norm_le t i _) (norm_nonneg _)

theorem annularColumn_energy_integrable (B : Finset β) (N : Finset α)
    (bNorm : β → ℝ) (nNorm : α → ℝ) (a : β → α → ℂ) (U : ℝ)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (i : SchwartzTestPartition.Index) :
    Integrable (fun t : ℝ => ‖density W hW t‖ *
      ‖annularColumn B N bNorm nNorm a U t i‖ ^ 2) := by
  apply (density W hW).integrable.norm.mul_bdd
    (c := (coefficientMass B N a) ^ 2)
    ((annularColumn_continuous B N bNorm nNorm a U i).norm.pow 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (annularColumn_norm_le B N bNorm nNorm a U t i) 2

/-- Integral Cauchy with genuine convergence of both the original
integrand and its positive energy. -/
theorem phase_integral_sq_le (ρ : SchwartzMap ℝ ℂ) (p c : ℝ → ℂ)
    (cp : Continuous p) (hp : ∀ t, ‖p t‖ = 1)
    (cc : Continuous c) (A : ℝ) (hc : ∀ t, ‖c t‖ ≤ A) :
    Integrable (fun t => ρ t * p t * c t) ∧
      ‖∫ t, ρ t * p t * c t‖ ^ 2 ≤
        (∫ t, ‖ρ t‖) * ∫ t, ‖ρ t‖ * ‖c t‖ ^ 2 := by
  have hi : Integrable (fun t => ‖ρ t‖ * ‖c t‖ ^ 2) := by
    apply ρ.integrable.norm.mul_bdd (c := A ^ 2) (cc.norm.pow 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hc t) 2
  have hiz : Integrable (fun t => ρ t * p t * c t) := by
    apply (ρ.integrable.norm.mul_const A).mono'
      ((ρ.continuous.mul cp).mul cc).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun t => by
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

/-- The original joint profile is charged once, before the finite
annular Cauchy inequality. The right side contains the actual positive
energies of the defined finite annular polynomials. -/
theorem source_sq_le (B : Finset β) (N : Finset α)
    (bNorm : β → ℝ) (nNorm : α → ℝ) (a : β → α → ℂ)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (H U X : ℝ) (hH : 0 < H) (hU : 0 < U) (hX : X = H ^ 3 * U)
    (hb : ∀ b ∈ B, H ≤ bNorm b ∧ bNorm b ≤ 2 * H)
    (hn : ∀ n ∈ N, 0 < nNorm n) :
    ‖source B N bNorm nNorm a W X‖ ^ 2 ≤
      24 * (∫ t : ℝ, ‖density W hW t‖) *
        ∑ i : SchwartzTestPartition.Index,
          ∫ t : ℝ, ‖density W hW t‖ *
            ‖annularColumn B N bNorm nNorm a U t i‖ ^ 2 := by
  let p : ℝ → ℂ := fun t => columnPhase t (-Real.log X) * columnPhase t (Real.log U)
  let c : ℝ → ℂ := fun t => ∑ i : SchwartzTestPartition.Index,
    annularColumn B N bNorm nNorm a U t i
  have cc : Continuous c := continuous_finsetSum _ (fun i _ =>
    annularColumn_continuous B N bNorm nNorm a U i)
  have hc (t : ℝ) : ‖c t‖ ≤ 24 * coefficientMass B N a := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _i : SchwartzTestPartition.Index, coefficientMass B N a :=
        Finset.sum_le_sum (fun i _ => annularColumn_norm_le B N bNorm nNorm a U t i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_ofNat]
  have hphase := phase_integral_sq_le (density W hW) p c
    ((continuous_columnPhase _).mul (continuous_columnPhase _))
    (fun t => by simp only [p, norm_mul, norm_columnPhase, mul_one]) cc
    (24 * coefficientMass B N a) hc
  have hsource : source B N bNorm nNorm a W X =
      ∫ t : ℝ, density W hW t * p t * c t := by
    rw [source, finite_cube_profile_annular_inverse B N bNorm nNorm a W hW
      H U X hH hU hX hb hn]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      dsimp only [p, c, annularColumn]
      ring
  rw [hsource]
  apply hphase.2.trans
  have hm : 0 ≤ ∫ t : ℝ, ‖density W hW t‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hbnd (t : ℝ) : ‖c t‖ ^ 2 ≤
      24 * ∑ i : SchwartzTestPartition.Index,
        ‖annularColumn B N bNorm nNorm a U t i‖ ^ 2 := by
    have ht := HeckePort.Moments.bounded_coefficient_sum_sq
      (fun _ : SchwartzTestPartition.Index => (1 : ℂ))
      (fun i => annularColumn B N bNorm nNorm a U t i) (by simp)
    simpa only [one_mul, Fintype.card_fin, Nat.cast_ofNat] using ht
  have hi := (integrable_finsetSum Finset.univ (fun i _ =>
    annularColumn_energy_integrable B N bNorm nNorm a U W hW i)).const_mul (24 : ℝ)
  have hbound : (∫ t : ℝ, ‖density W hW t‖ * ‖c t‖ ^ 2) ≤
      24 * ∑ i : SchwartzTestPartition.Index,
        ∫ t : ℝ, ‖density W hW t‖ *
          ‖annularColumn B N bNorm nNorm a U t i‖ ^ 2 := by
    calc
      _ ≤ ∫ t : ℝ, 24 * ∑ i : SchwartzTestPartition.Index,
          ‖density W hW t‖ * ‖annularColumn B N bNorm nNorm a U t i‖ ^ 2 := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun t => mul_nonneg (norm_nonneg _) (sq_nonneg _))) hi
        exact Filter.Eventually.of_forall fun t =>
          (mul_le_mul_of_nonneg_left (hbnd t) (norm_nonneg _)).trans_eq
            (by rw [Finset.mul_sum]; ring)
      _ = _ := by
        rw [integral_const_mul, integral_finsetSum Finset.univ
          (fun i _ => annularColumn_energy_integrable B N bNorm nNorm a U W hW i)]
  exact (mul_le_mul_of_nonneg_left hbound hm).trans_eq (by ring)

def sourceEnergy (R : Finset κ) (w : κ → ℝ)
    (B : Finset β) (N : Finset α) (bNorm : β → ℝ) (nNorm : α → ℝ)
    (a : κ → β → α → ℂ) (W : SchwartzMap ℝ ℂ) (X : ℝ) : ℝ :=
  ∑ k ∈ R, w k * ‖source B N bNorm nNorm (a k) W X‖ ^ 2

def annularEnergy (R : Finset κ) (w : κ → ℝ)
    (B : Finset β) (N : Finset α) (bNorm : β → ℝ) (nNorm : α → ℝ)
    (a : κ → β → α → ℂ) (U t : ℝ) (i : SchwartzTestPartition.Index) : ℝ :=
  ∑ k ∈ R, w k * ‖annularColumn B N bNorm nNorm (a k) U t i‖ ^ 2

theorem source_norm_le_card (B : Finset β) (N : Finset α)
    (bNorm : β → ℝ) (nNorm : α → ℝ) (a : β → α → ℂ)
    (W : SchwartzMap ℝ ℂ) (X D : ℝ)
    (ha : ∀ b ∈ B, ∀ n ∈ N, ‖a b n‖ ≤ D) :
    ‖source B N bNorm nNorm a W X‖ ≤
      (B.card : ℝ) * N.card * D * SchwartzMap.seminorm ℝ 0 0 W := by
  unfold source
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _b ∈ B, ∑ _n ∈ N, D * SchwartzMap.seminorm ℝ 0 0 W := by
      apply Finset.sum_le_sum
      intro b hb
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      exact mul_le_mul (ha b hb n hn) (SchwartzMap.norm_le_seminorm ℝ W _)
        (norm_nonneg _) (le_trans (norm_nonneg _) (ha b hb n hn))
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- The direct finite-column estimate used when the true annular
column scale is below one. Its cube count and all weights are explicit,
so the source normalization can cancel the cube count afterwards. -/
theorem sourceEnergy_le_card (R : Finset κ) (w : κ → ℝ)
    (hw : ∀ k ∈ R, 0 ≤ w k)
    (B : Finset β) (N : Finset α) (bNorm : β → ℝ) (nNorm : α → ℝ)
    (a : κ → β → α → ℂ) (W : SchwartzMap ℝ ℂ) (X D : ℝ)
    (ha : ∀ k ∈ R, ∀ b ∈ B, ∀ n ∈ N, ‖a k b n‖ ≤ D) :
    sourceEnergy R w B N bNorm nNorm a W X ≤
      (∑ k ∈ R, w k) *
        ((B.card : ℝ) * N.card * D * SchwartzMap.seminorm ℝ 0 0 W) ^ 2 := by
  unfold sourceEnergy
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (source_norm_le_card B N bNorm nNorm (a k) W X D
      (ha k hk)) 2) (hw k hk)

theorem annularEnergy_nonneg (R : Finset κ) (w : κ → ℝ)
    (hw : ∀ k ∈ R, 0 ≤ w k)
    (B : Finset β) (N : Finset α) (bNorm : β → ℝ) (nNorm : α → ℝ)
    (a : κ → β → α → ℂ) (U t : ℝ) (i : SchwartzTestPartition.Index) :
    0 ≤ annularEnergy R w B N bNorm nNorm a U t i :=
  Finset.sum_nonneg (fun k hk => mul_nonneg (hw k hk) (sq_nonneg _))

theorem annularEnergy_integrable (R : Finset κ) (w : κ → ℝ)
    (B : Finset β) (N : Finset α) (bNorm : β → ℝ) (nNorm : α → ℝ)
    (a : κ → β → α → ℂ) (U : ℝ)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (i : SchwartzTestPartition.Index) :
    Integrable (fun t : ℝ => ‖density W hW t‖ *
      annularEnergy R w B N bNorm nNorm a U t i) := by
  simp only [annularEnergy, Finset.mul_sum]
  apply integrable_finsetSum R
  intro k hk
  convert (annularColumn_energy_integrable B N bNorm nNorm (a k) U W hW i).const_mul
    (w k) using 1
  ext t
  ring

theorem annularEnergy_integral_eq (R : Finset κ) (w : κ → ℝ)
    (B : Finset β) (N : Finset α) (bNorm : β → ℝ) (nNorm : α → ℝ)
    (a : κ → β → α → ℂ) (U : ℝ)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (i : SchwartzTestPartition.Index) :
    (∫ t : ℝ, ‖density W hW t‖ * annularEnergy R w B N bNorm nNorm a U t i) =
      ∑ k ∈ R, w k * ∫ t : ℝ, ‖density W hW t‖ *
        ‖annularColumn B N bNorm nNorm (a k) U t i‖ ^ 2 := by
  have hp (t : ℝ) : ‖density W hW t‖ * annularEnergy R w B N bNorm nNorm a U t i =
      ∑ k ∈ R, w k * (‖density W hW t‖ *
        ‖annularColumn B N bNorm nNorm (a k) U t i‖ ^ 2) := by
    simp only [annularEnergy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp_rw [hp]
  rw [integral_finsetSum R (fun k _ =>
    (annularColumn_energy_integrable B N bNorm nNorm (a k) U W hW i).const_mul (w k))]
  apply Finset.sum_congr rfl
  intro k hk
  exact integral_const_mul _ _

/-- The actual nonnegative finite row and label weights pass through
the one common Mellin integral. No independent row-dependent profile is
introduced. -/
theorem sourceEnergy_le (R : Finset κ) (w : κ → ℝ)
    (hw : ∀ k ∈ R, 0 ≤ w k)
    (B : Finset β) (N : Finset α) (bNorm : β → ℝ) (nNorm : α → ℝ)
    (a : κ → β → α → ℂ)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (H U X : ℝ) (hH : 0 < H) (hU : 0 < U) (hX : X = H ^ 3 * U)
    (hb : ∀ b ∈ B, H ≤ bNorm b ∧ bNorm b ≤ 2 * H)
    (hn : ∀ n ∈ N, 0 < nNorm n) :
    sourceEnergy R w B N bNorm nNorm a W X ≤
      24 * (∫ t : ℝ, ‖density W hW t‖) *
        ∑ i : SchwartzTestPartition.Index,
          ∫ t : ℝ, ‖density W hW t‖ * annularEnergy R w B N bNorm nNorm a U t i := by
  calc
    _ ≤ ∑ k ∈ R, w k * (24 * (∫ t : ℝ, ‖density W hW t‖) *
        ∑ i : SchwartzTestPartition.Index,
          ∫ t : ℝ, ‖density W hW t‖ *
            ‖annularColumn B N bNorm nNorm (a k) U t i‖ ^ 2) :=
      Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left
        (source_sq_le B N bNorm nNorm (a k) W hW H U X hH hU hX hb hn) (hw k hk))
    _ = 24 * (∫ t : ℝ, ‖density W hW t‖) *
        ∑ k ∈ R, ∑ i : SchwartzTestPartition.Index,
          w k * ∫ t : ℝ, ‖density W hW t‖ *
            ‖annularColumn B N bNorm nNorm (a k) U t i‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.mul_sum]
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact (annularEnergy_integral_eq R w B N bNorm nNorm a U W hW i).symm

theorem density_cauchy_moment_bound (m : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2),
      (∫ t : ℝ, ‖density W hW t‖) *
          (∫ t : ℝ, (1 + |t|) ^ m * ‖density W hW t‖) ≤
        C * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 := by
  obtain ⟨s₀, C₀, hC₀, hb₀⟩ := density_moment_bound 0
  obtain ⟨s₁, C₁, hC₁, hb₁⟩ := density_moment_bound m
  refine ⟨s₀ ∪ s₁, C₀ * C₁, mul_nonneg hC₀ hC₁, ?_⟩
  intro W hW
  have h₀ : (∫ t : ℝ, ‖density W hW t‖) ≤
      C₀ * (s₀ ∪ s₁).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    have hh : (∫ t : ℝ, ‖density W hW t‖) ≤
        C₀ * s₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
      simpa only [pow_zero, one_mul] using hb₀ W hW
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) W) hC₀)
  have h₁ : (∫ t : ℝ, (1 + |t|) ^ m * ‖density W hW t‖) ≤
      C₁ * (s₀ ∪ s₁).sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
    (hb₁ W hW).trans (mul_le_mul_of_nonneg_left
      (Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) W) hC₁)
  have hn : 0 ≤ ∫ t : ℝ, (1 + |t|) ^ m * ‖density W hW t‖ :=
    integral_nonneg (fun t => mul_nonneg (pow_nonneg (by positivity) _) (norm_nonneg _))
  exact (mul_le_mul h₀ h₁ hn (by positivity)).trans_eq (by ring)

/-- Uniformly bounded actual annular energies imply a bound for the
original joint-profile energy. The finite original-profile seminorm is
selected before the source, arithmetic weights, scales, and rows. -/
theorem exists_uniform_sourceEnergy_bound (q : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (R : Finset κ) (w : κ → ℝ), (∀ k ∈ R, 0 ≤ w k) →
      ∀ (B : Finset β) (N : Finset α) (bNorm : β → ℝ) (nNorm : α → ℝ)
        (a : κ → β → α → ℂ)
        (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
        (H U X E : ℝ), 0 < H → 0 < U → X = H ^ 3 * U → 0 ≤ E →
      (∀ b ∈ B, H ≤ bNorm b ∧ bNorm b ≤ 2 * H) →
      (∀ n ∈ N, 0 < nNorm n) →
      (∀ (t : ℝ) (i : SchwartzTestPartition.Index),
        annularEnergy R w B N bNorm nNorm a U t i ≤
          E * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) (annularTest t i)) ^ 2) →
      sourceEnergy R w B N bNorm nNorm a W X ≤
        C * E * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 := by
  obtain ⟨m, A, hA, htest⟩ := annularTest_seminorm_bound q
  obtain ⟨s, C, hC, hbudget⟩ := density_cauchy_moment_bound (2 * m)
  refine ⟨s, 576 * A ^ 2 * C, by positivity, ?_⟩
  intro R w hw B N bNorm nNorm a W hW H U X E hH hU hX hE hb hn henergy
  have hm : 0 ≤ ∫ t : ℝ, ‖density W hW t‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hp (t : ℝ) (i : SchwartzTestPartition.Index) :
      annularEnergy R w B N bNorm nNorm a U t i ≤ E * A ^ 2 * (1 + |t|) ^ (2 * m) := by
    have ht := pow_le_pow_left₀
      (apply_nonneg (q.sup (schwartzSeminormFamily ℝ ℝ ℂ)) _) (htest t i) 2
    exact (henergy t i).trans
      ((mul_le_mul_of_nonneg_left ht hE).trans_eq (by
        rw [mul_pow, ← pow_mul, Nat.mul_comm m 2]
        ring))
  have hi (i : SchwartzTestPartition.Index) :
      (∫ t : ℝ, ‖density W hW t‖ * annularEnergy R w B N bNorm nNorm a U t i) ≤
        E * A ^ 2 * (∫ t : ℝ, (1 + |t|) ^ (2 * m) * ‖density W hW t‖) := by
    calc
      _ ≤ ∫ t : ℝ, (E * A ^ 2) * ((1 + |t|) ^ (2 * m) * ‖density W hW t‖) := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun t => mul_nonneg (norm_nonneg _)
            (annularEnergy_nonneg R w hw B N bNorm nNorm a U t i)))
          ((density_moment_integrable W hW (2 * m)).const_mul (E * A ^ 2))
        exact Filter.Eventually.of_forall fun t =>
          (mul_le_mul_of_nonneg_left (hp t i) (norm_nonneg _)).trans_eq (by ring)
      _ = _ := integral_const_mul _ _
  calc
    _ ≤ 24 * (∫ t : ℝ, ‖density W hW t‖) *
        ∑ i : SchwartzTestPartition.Index,
          ∫ t : ℝ, ‖density W hW t‖ * annularEnergy R w B N bNorm nNorm a U t i :=
      sourceEnergy_le R w hw B N bNorm nNorm a W hW H U X hH hU hX hb hn
    _ ≤ 24 * (∫ t : ℝ, ‖density W hW t‖) *
        ∑ _i : SchwartzTestPartition.Index,
          E * A ^ 2 * (∫ t : ℝ, (1 + |t|) ^ (2 * m) * ‖density W hW t‖) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hi i)) (by positivity)
    _ = (576 * E * A ^ 2) * ((∫ t : ℝ, ‖density W hW t‖) *
        (∫ t : ℝ, (1 + |t|) ^ (2 * m) * ‖density W hW t‖)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_ofNat]
      ring
    _ ≤ (576 * E * A ^ 2) * (C * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2) :=
      mul_le_mul_of_nonneg_left (hbudget W hW) (by positivity)
    _ = _ := by ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionEnergy
