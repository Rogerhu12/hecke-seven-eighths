import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialClosure
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceScaleBudget

/-!
# The actual zero-slot orbital source from the canonical bound

The column datum here has the unit puncture, no prime slots and the
original background character and radial test. Its source mark is
identically one. All initial source conditions are proved from the
literal scale `X`, row scale `H` and the strict logarithmic gap.

The only energy premise in the internal adapter is the actual canonical
`UniformBound`, which the finite induction supplies. Initial Poisson,
positive production, principal terms and tails are already discharged
by `ProviderInitialClosure`. The finite seminorm, scalar and threshold
are selected before the original scale or test is chosen.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceUnmarkedOrbital

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP
open ProviderNodes ProviderInitialEstimate
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset

/-- This is an actual original column datum, with no auxiliary
coefficient or energy attached to it. -/
def columns (Λ ν₀ : HeckeCharacter K) (H X : ℝ) (W : SchwartzMap ℝ ℂ) :
    CanonicalBlock.ColumnData K S Unit where
  lambda := Λ
  background := ν₀
  puncture := 1
  slots := ∅
  primeLists := fun _ => ∅
  primeWeights := fun _ _ => 0
  labelWeight := fun _ _ => 1
  cutoff := W
  base := H
  length := Real.logb H X

theorem sourceMark_eq_one (Λ ν₀ : HeckeCharacter K) (H X : ℝ) (W : SchwartzMap ℝ ℂ) :
    ProviderInitialInverse.sourceMark K S (columns K S Λ ν₀ H X W) = fun _ => 1 := by
  funext n
  simp only [ProviderInitialInverse.sourceMark, columns, isCoprime_one_right,
    if_true, divisorMark, Finset.prod_empty, mul_one]

theorem empty_marks (slotCap : ℕ) (H lo hi : ℝ) :
    MarkConditions K S slotCap H 0 lo hi (∅ : Finset Unit)
      (fun _ => ∅) (fun _ _ => 0) (fun _ => 0) where
  card_le := by simp
  length_nonneg := by simp
  total_length := by simp
  prime := by simp
  exterior := by simp
  norm_window := by simp
  weights_le := by simp
  disjoint := by simp

def mesh (gap eps : ℝ) : ℝ := min 1 (min (gap / 3200) (eps / 384))
def truncation (gap : ℝ) : ℝ := gap / 96
def auxiliaryLoss (eps : ℝ) : ℝ := eps / 40

theorem mesh_pos {gap eps : ℝ} (hgap : 0 < gap) (heps : 0 < eps) :
    0 < mesh gap eps := by
  exact lt_min zero_lt_one (lt_min (by positivity) (by positivity))

theorem mesh_le_one (gap eps : ℝ) : mesh gap eps ≤ 1 := min_le_left _ _

theorem mesh_le_gap (gap eps : ℝ) : mesh gap eps ≤ gap / 3200 :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem mesh_le_loss (gap eps : ℝ) : mesh gap eps ≤ eps / 384 :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem source_loss_budget (gap eps : ℝ) :
    100 * mesh gap eps + 3 * truncation gap ≤ (gap / 4) / 4 := by
  have hh := mesh_le_gap gap eps
  dsimp only [truncation]
  linarith

theorem final_loss_budget {gap eps : ℝ} (heps : 0 ≤ eps) :
    48 * mesh gap eps + 5 * auxiliaryLoss eps + eps / 2 ≤ eps := by
  have hh := mesh_le_loss gap eps
  dsimp only [auxiliaryLoss]
  linarith

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

/-- Every field of the initial source condition is verified for the
zero-slot source. The strict source gap is kept in both inequalities. -/
theorem source_conditions (slotCap : ℕ) (Λ G ν₀ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset D Λ G)
    (hν₀ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K ν₀ p)
    (gap eps H X lo hi : ℝ) (W : SchwartzMap ℝ ℂ)
    (hgap0 : 0 < gap) (hgap1 : gap < 1) (heps : 0 < eps)
    (hH : 4 ≤ H) (hX : 1 ≤ X)
    (hlength : Real.logb H X ≤ 1 - gap / 2)
    (hwidth : 2 ≤ H ^ mesh gap eps) :
    SourceConditions K S D (columns K S Λ ν₀ H X W) Λ G slotCap
      2 1 0 0 (gap / 4) (mesh gap eps) (truncation gap) lo hi (fun _ => 0) := by
  have hH1 : 1 < H := by linarith
  have hn : 0 ≤ Real.logb H X := Real.logb_nonneg hH1 hX
  have hm := SourceScaleBudget.initial_margins hgap0.le hgap1.le hlength
  exact {
    base_gt_one := hH1
    row_nonneg := by norm_num
    column_nonneg := hn
    column_le := by dsimp only [columns]; linarith
    puncture_nonneg := le_rfl
    mark_nonneg := le_rfl
    mesh := ⟨(mesh_pos hgap0 heps).le, mesh_le_one gap eps⟩
    truncation_nonneg := by dsimp only [truncation]; positivity
    mesh_width := hwidth
    pool_cap := SourceScaleBudget.initial_pool_cap hH (by dsimp only [columns]; linarith)
    source_margin_one := hm.1
    source_margin_two := hm.2
    loss_budget := source_loss_budget gap eps
    lambda_eq := rfl
    calibration := hcal
    background_unramified := hν₀
    puncture_nonzero := one_ne_zero
    puncture_bound := by simp only [columns, Ideal.one_eq_top, Ideal.radical_top,
      Ideal.absNorm_top, Nat.cast_one, Real.rpow_zero, le_refl]
    marks := empty_marks K S slotCap H lo hi }

theorem column_scale {Λ ν₀ : HeckeCharacter K} {H X : ℝ}
    (W : SchwartzMap ℝ ℂ) (hH : 1 < H) (hX : 0 < X) :
    (columns K S Λ ν₀ H X W).base ^ (columns K S Λ ν₀ H X W).length = X :=
  Real.rpow_logb (zero_lt_one.trans hH) (ne_of_gt hH) hX

theorem rowCap_eq (Λ ν₀ : HeckeCharacter K) (H X : ℝ) (W : SchwartzMap ℝ ℂ)
    (hH : 1 < H) (hHp : 0 < H) :
    ProviderInitialProduction.rowCap K S (columns K S Λ ν₀ H X W) hH 1 = ⟨H, hHp⟩ := by
  apply Subtype.ext
  simp only [ProviderInitialProduction.rowCap, columns, Real.rpow_one]

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [Γ.FiniteIndex]
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
/-- The common zero-slot orbital estimate. The constants are even
uniform over the fixed admissible background class: selecting `ν₀ = 1`
or `ν₀ = ψ` does not change the seminorm or base threshold. -/
theorem exists_uniform_orbital_bound_of_uniform
    (slotCap : ℕ) (gap eps : ℝ) (hgap0 : 0 < gap) (hgap1 : gap < 1) (heps : 0 < eps)
    (qchild : Finset (ℕ × ℕ)) :
    ∃ q : Finset (ℕ × ℕ), ∃ C H₀ : ℝ, 1 ≤ C ∧ 4 ≤ H₀ ∧
      ∀ (Θ : Subgroup (HeckeCharacter K)) (ψ Λ G ν₀ : HeckeCharacter K), G ∈ Θ →
      ThetaCalibrationInput K Sset D Λ G → BackgroundCycle.Admissible K Θ ψ ν₀ →
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K ν₀ p) →
      ∀ (lo hi H X : ℝ) (hH : 0 < H) (W : SchwartzMap ℝ ℂ),
      tsupport W ⊆ Set.Icc (1 : ℝ) 2 → H₀ ≤ H → 1 ≤ X →
      Real.logb H X ≤ 1 - gap / 2 → ∀ Cih : ℝ, 1 ≤ Cih →
      UniformBound.{0} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap H 1 (3 * gap / 16)
        0 lo hi (eps / 2) 1 Cih qchild →
      ‖SourceReductionPoisson.orbitalEnergy K S D Γ ν₀ (fun _ => 1) W X ⟨H, hH⟩‖ ≤
        C * Cih * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 * H ^ (1 + eps) := by
  obtain ⟨q, C, hC, horbital⟩ := ProviderInitialClosure.exists_uniform_orbital_bound
    K S D Γ hΓ hallowed μv ν μ slotCap 2 1 (auxiliaryLoss eps) (truncation gap)
      (by norm_num) (by norm_num) (by dsimp only [auxiliaryLoss]; positivity)
      (by dsimp only [truncation]; positivity) qchild
  obtain ⟨H₁, hH₁, hwidth⟩ := exists_uniform_power_threshold (mesh gap eps) 2
    (mesh_pos hgap0 heps) (by norm_num)
  refine ⟨q, C, max 4 H₁, hC, le_max_left _ _, ?_⟩
  intro Θ ψ Λ G ν₀ hG hcal hadmissible hunram lo hi H X hHp W hW hH hX hlength Cih hCih hih
  have hH4 : 4 ≤ H := (le_max_left _ _).trans hH
  have hH1 : 1 < H := by linarith
  have hHwidth : 2 ≤ H ^ mesh gap eps := hwidth H ((le_max_right _ _).trans hH)
  let C₀ := columns K S Λ ν₀ H X W
  have hb := source_conditions K S D slotCap Λ G ν₀ hcal hunram
    gap eps H X lo hi W hgap0 hgap1 heps hH4 hX hlength hHwidth
  have hih' : UniformBound.{0} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap H 1
      (3 * (gap / 4) / 4) 0 lo hi (eps / 2) 1 Cih qchild := by
    intro σ x hx hr
    rw [show 3 * (gap / 4) / 4 = 3 * gap / 16 by ring] at hx
    exact hih x hx hr
  have hbnd := horbital C₀ Θ ψ hadmissible W hW Λ G hG 1 0 0 (gap / 4)
    (mesh gap eps) (truncation gap) lo hi (fun _ => 0) hb (eps / 2) Cih
    le_rfl le_rfl (by positivity) hCih hih'
  have hscale := column_scale K S (Λ := Λ) (ν₀ := ν₀) W hH1 (zero_lt_one.trans_le hX)
  have hrow := rowCap_eq K S Λ ν₀ H X W hb.base_gt_one hHp
  change ‖SourceReductionPoisson.orbitalEnergy K S D Γ ν₀
    (ProviderInitialInverse.sourceMark K S (columns K S Λ ν₀ H X W)) W
    ((columns K S Λ ν₀ H X W).base ^ (columns K S Λ ν₀ H X W).length)
    (ProviderInitialProduction.rowCap K S (columns K S Λ ν₀ H X W) hb.base_gt_one 1)‖ ≤
      C * Cih * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
        H ^ (1 + 48 * mesh gap eps + 5 * auxiliaryLoss eps + eps / 2) at hbnd
  rw [sourceMark_eq_one K S Λ ν₀ H X W, hscale, hrow] at hbnd
  apply hbnd.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hH1.le
  linarith [final_loss_budget (gap := gap) heps.le]

include hΓ hallowed μv ν μ in
/-- The same uniform estimate stated in terms of the original positive
column scale, as used by the common scale-sup prefix. -/
theorem exists_uniform_orbital_bound_of_scale
    (slotCap : ℕ) (gap eps : ℝ) (hgap0 : 0 < gap) (hgap1 : gap < 1) (heps : 0 < eps)
    (qchild : Finset (ℕ × ℕ)) :
    ∃ q : Finset (ℕ × ℕ), ∃ C H₀ : ℝ, 1 ≤ C ∧ 4 ≤ H₀ ∧
      ∀ (Θ : Subgroup (HeckeCharacter K)) (ψ Λ G ν₀ : HeckeCharacter K), G ∈ Θ →
      ThetaCalibrationInput K Sset D Λ G → BackgroundCycle.Admissible K Θ ψ ν₀ →
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K ν₀ p) →
      ∀ (lo hi H X : ℝ) (hH : 0 < H) (W : SchwartzMap ℝ ℂ),
      tsupport W ⊆ Set.Icc (1 : ℝ) 2 → H₀ ≤ H → 1 ≤ X →
      X ≤ H ^ (1 - gap / 2) → ∀ Cih : ℝ, 1 ≤ Cih →
      UniformBound.{0} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap H 1 (3 * gap / 16)
        0 lo hi (eps / 2) 1 Cih qchild →
      ‖SourceReductionPoisson.orbitalEnergy K S D Γ ν₀ (fun _ => 1) W X ⟨H, hH⟩‖ ≤
        C * Cih * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 * H ^ (1 + eps) := by
  obtain ⟨q, C, H₀, hC, hH₀, hb⟩ := exists_uniform_orbital_bound_of_uniform
    K S D Γ hΓ hallowed μv ν μ slotCap gap eps hgap0 hgap1 heps qchild
  refine ⟨q, C, H₀, hC, hH₀, ?_⟩
  intro Θ ψ Λ G ν₀ hG hcal hadmissible hunram lo hi H X hHp W hW hH hX hscale Cih hCih hih
  have hH1 : 1 < H := by linarith
  have hlength : Real.logb H X ≤ 1 - gap / 2 := by
    have hb := Real.logb_le_logb_of_le hH1 (zero_lt_one.trans_le hX) hscale
    simpa only [Real.logb_rpow hHp (ne_of_gt hH1)] using hb
  exact hb Θ ψ Λ G ν₀ hG hcal hadmissible hunram lo hi H X hHp W hW hH hX
    hlength Cih hCih hih

theorem admissible_one (Θ : Subgroup (HeckeCharacter K)) (ψ : HeckeCharacter K) :
    BackgroundCycle.Admissible K Θ ψ 1 := Or.inl Θ.one_mem

theorem admissible_target (Θ : Subgroup (HeckeCharacter K)) (ψ : HeckeCharacter K) :
    BackgroundCycle.Admissible K Θ ψ ψ := Or.inr ⟨1, Θ.one_mem, by simp⟩

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceUnmarkedOrbital
