import HeckeGeneral.Arithmetic.SIntegerOrbitCounting
import HeckeGeneral.Analysis.CountingPowerTail
import HeckeGeneral.Analysis.SUnitSchwartzDecay

/-!
# Quantitative tails of the actual S-integer orbital profiles

The norm cutoff is on every actual subgroup orbit. Its proved linear count
and the proved Schwartz seminorm decay give the dyadic truncation error,
uniform in the radius, truncation threshold, and archimedean test function.
The finite-place test function is fixed here; varying coefficient families
and their Fourier identification are separate steps.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic MeasureTheory
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "Q" => SIntegerOrbits K S Γ
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

omit [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)] in
theorem finite_setOf_sIntegerOrbitNorm_le (H : ℝ) :
    Set.Finite {q : Q | (sIntegerOrbitNorm K S Γ q).val ≤ H} := by
  change Finite (BoundedSIntegerOrbits K S Γ H)
  infer_instance

/-- Actual profile tails are summable and their absolute sums satisfy the power bound.
The constant is chosen before all moving radii, thresholds, and Schwartz maps. -/
theorem exists_sIntegerSchwartzProfile_tail_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (A : ℝ) (hA : 1 < A) (M : ℕ) (hM : Module.finrank ℤ L < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * A ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : SchwartzMap V ℂ,
      ∀ ρ : {r : ℝ // 0 < r}, ∀ X : ℝ, 1 ≤ X →
        let f := fun q : {q : Q // X < ρ.val * (sIntegerOrbitNorm K S Γ q).val} =>
          sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
            ⟨ρ.val * (sIntegerOrbitNorm K S Γ q.val).val,
              mul_pos ρ.property (sIntegerOrbitNorm K S Γ q.val).property⟩
        Summable f ∧ (∑' q, ‖f q‖) ≤
          C * SchwartzMap.seminorm ℂ M 0 φ * (1 + ρ.val⁻¹) * X ^ (1 - A) := by
  obtain ⟨D, hD, hcount⟩ := exists_card_boundedSIntegerOrbits_le K S Γ
  obtain ⟨B, hB, hdecay⟩ :=
    exists_sLocalSchwartzProfile_power_decay K S Γ ψ hψ hψsupport A M hM hOrder
  let C := countingPowerTailConstant A * D * B
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (countingPowerTailConstant_pos hA).le hD.le) hB
  refine ⟨C, hC, fun φ ρ X hX => ?_⟩
  dsimp only
  let qnorm : Q → ℝ := fun q => (sIntegerOrbitNorm K S Γ q).val
  let T := {q : Q // X < ρ.val * qnorm q}
  let f : T → ℂ := fun q =>
    sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
      ⟨ρ.val * qnorm q.val, mul_pos ρ.property (sIntegerOrbitNorm K S Γ q.val).property⟩
  let w : T → ℝ := fun q => (ρ.val * qnorm q.val) ^ (-A)
  let P : ℝ := B * SchwartzMap.seminorm ℂ M 0 φ
  have hP : 0 ≤ P := mul_nonneg hB (apply_nonneg (SchwartzMap.seminorm ℂ M 0) φ)
  have hw : Summable w :=
    summable_neg_rpow_tail_of_linear_count qnorm
      (finite_setOf_sIntegerOrbitNorm_le K S Γ) D hcount A ρ.val X hA ρ.property hX
  have hf (q : T) : ‖f q‖ ≤ P * w q :=
    hdecay φ _ (hX.trans q.property.le)
  have hfnorm : Summable (fun q => ‖f q‖) :=
    (hw.mul_left P).of_nonneg_of_le (fun q => norm_nonneg _) hf
  have hsum : Summable f := hfnorm.of_norm
  refine ⟨hsum, ?_⟩
  have htail := tsum_neg_rpow_tail_le_of_linear_count qnorm
    (finite_setOf_sIntegerOrbitNorm_le K S Γ) D hcount A ρ.val X hA ρ.property hX
  change (∑' q, ‖f q‖) ≤ _
  calc
    _ ≤ ∑' q, P * w q := hfnorm.tsum_le_tsum hf (hw.mul_left P)
    _ = P * ∑' q, w q := tsum_mul_left
    _ ≤ P * (countingPowerTailConstant A * D * (1 + ρ.val⁻¹) * X ^ (1 - A)) :=
      mul_le_mul_of_nonneg_left htail hP
    _ = _ := by dsimp only [P, C]; ring

/-- Arbitrary bounded orbit coefficients preserve the quantitative truncation
bound. Periodic Fourier coefficients may be inserted once their actual
orbit invariance and finite supremum bound have been proved. -/
theorem exists_sIntegerSchwartzProfile_weighted_tail_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (A : ℝ) (hA : 1 < A) (M : ℕ) (hM : Module.finrank ℤ L < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * A ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : SchwartzMap V ℂ,
      ∀ ρ : {r : ℝ // 0 < r}, ∀ X : ℝ, 1 ≤ X →
      ∀ w : Q → ℂ, ∀ B : ℝ, 0 ≤ B → (∀ q, ‖w q‖ ≤ B) →
        let f := fun q : {q : Q // X < ρ.val * (sIntegerOrbitNorm K S Γ q).val} =>
          w q.val * sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
            ⟨ρ.val * (sIntegerOrbitNorm K S Γ q.val).val,
              mul_pos ρ.property (sIntegerOrbitNorm K S Γ q.val).property⟩
        Summable f ∧ ‖∑' q, f q‖ ≤
          B * C * SchwartzMap.seminorm ℂ M 0 φ * (1 + ρ.val⁻¹) * X ^ (1 - A) := by
  obtain ⟨C, hC, htail⟩ :=
    exists_sIntegerSchwartzProfile_tail_bound K S Γ ψ hψ hψsupport A hA M hM hOrder
  refine ⟨C, hC, fun φ ρ X hX w B hB hw => ?_⟩
  obtain ⟨hf, hsum⟩ := htail φ ρ X hX
  let T := {q : Q // X < ρ.val * (sIntegerOrbitNorm K S Γ q).val}
  let f : T → ℂ := fun q => sUnitOrbitalProfile K S
    (sLocalTensorTestFunction K S φ ψ)
    ⟨ρ.val * (sIntegerOrbitNorm K S Γ q.val).val,
      mul_pos ρ.property (sIntegerOrbitNorm K S Γ q.val).property⟩
  have hfnorm : Summable (fun q => ‖f q‖) := hf.norm
  have hpoint (q : T) : ‖w q.val * f q‖ ≤ B * ‖f q‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hw q.val) (norm_nonneg _)
  have hwnorm : Summable (fun q : T => ‖w q.val * f q‖) :=
    (hfnorm.mul_left B).of_nonneg_of_le (fun q => norm_nonneg _) hpoint
  refine ⟨hwnorm.of_norm, ?_⟩
  change ‖∑' q : T, w q.val * f q‖ ≤ _
  calc
    _ ≤ ∑' q : T, ‖w q.val * f q‖ := norm_tsum_le_tsum_norm hwnorm
    _ ≤ ∑' q : T, B * ‖f q‖ := hwnorm.tsum_le_tsum hpoint (hfnorm.mul_left B)
    _ = B * ∑' q : T, ‖f q‖ := tsum_mul_left
    _ ≤ B * (C * SchwartzMap.seminorm ℂ M 0 φ * (1 + ρ.val⁻¹) * X ^ (1 - A)) :=
      mul_le_mul_of_nonneg_left hsum hB
    _ = _ := by ring

end HeckeGeneral.Analysis
