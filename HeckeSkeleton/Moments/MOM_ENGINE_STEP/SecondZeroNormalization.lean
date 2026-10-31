import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstZeroMaskSubpower
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondSourceNormalization

/-!
# The actual central normalization in the second zero term

The complete second zero coefficient carries the norm of its original
ideal. Two original column normalizations cancel this norm exactly on
the diagonal. For the existing terminal interface, which requests a
profile window on every original pair, the same calculation uses only
the original common upper and lower norm windows.

No diagonal sum or zero-frequency estimate is an input. The final
per-profile normalization is obtained from the actual scalar identity
and the proved small-power bound for the original mask divisors.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis

variable {K : Type} [Field K] [NumberField K]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- The norm payment in the literal second-zero profile, before any
sum or estimate. The raw column factors stay visible. -/
theorem second_zero_gram_norm_identity
    (seminorms : Finset (ℕ × ℕ)) (φ : SchwartzMap V ℂ)
    (c d rawLeft rawRight : ℂ) (NL NR NI : ℝ)
    (hleft : c = rawLeft / (Real.sqrt NL : ℂ))
    (hright : d = rawRight / (Real.sqrt NR : ℂ)) :
    seminorms.sup (schwartzSeminormFamily ℂ V ℂ) ((c * star d) • φ) * NI =
      (‖rawLeft‖ * ‖rawRight‖ *
        seminorms.sup (schwartzSeminormFamily ℂ V ℂ) φ) *
          (NI / (Real.sqrt NL * Real.sqrt NR)) := by
  rw [hleft, hright, map_smul_eq_mul]
  simp only [norm_mul, norm_star, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

/-- On the true diagonal the complete original ideal norm cancels
without any norm-window loss. -/
theorem second_zero_gram_norm_diagonal
    (seminorms : Finset (ℕ × ℕ)) (φ : SchwartzMap V ℂ)
    (rawLeft rawRight : ℂ) (N : ℝ) (hN : 0 < N) :
    seminorms.sup (schwartzSeminormFamily ℂ V ℂ)
        (((rawLeft / (Real.sqrt N : ℂ)) * star (rawRight / (Real.sqrt N : ℂ))) • φ) * N =
      ‖rawLeft‖ * ‖rawRight‖ * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) φ := by
  rw [second_zero_gram_norm_identity seminorms φ _ _ rawLeft rawRight N N N rfl rfl,
    ← pow_two, Real.sq_sqrt hN.le, div_self hN.ne', mul_one]

/-- The pairwise window required by the existing source calibration is
derived from original individual norm windows. Negative column
exponents are allowed; positivity comes from the positive base. -/
theorem second_zero_gram_norm_le_original_windows
    (seminorms : Finset (ℕ × ℕ)) (φ : SchwartzMap V ℂ)
    (Z columnExponent ratio NL NR NI : ℝ) (hZ : 0 < Z) (hratio : 0 ≤ ratio)
    (hNL : Z ^ columnExponent ≤ NL) (hNR : Z ^ columnExponent ≤ NR)
    (hNI : NI ≤ ratio * Z ^ columnExponent)
    (c d rawLeft rawRight : ℂ)
    (hleft : c = rawLeft / (Real.sqrt NL : ℂ))
    (hright : d = rawRight / (Real.sqrt NR : ℂ)) :
    seminorms.sup (schwartzSeminormFamily ℂ V ℂ) ((c * star d) • φ) * NI ≤
      ratio * (‖rawLeft‖ * ‖rawRight‖ *
        seminorms.sup (schwartzSeminormFamily ℂ V ℂ) φ) := by
  have hcentral := second_source_central_scale_lower Z hZ columnExponent NL NR hNL hNR
  have hden : 0 < Real.sqrt NL * Real.sqrt NR :=
    (Real.rpow_pos_of_pos hZ columnExponent).trans_le hcentral
  have hnorm : NI / (Real.sqrt NL * Real.sqrt NR) ≤ ratio :=
    (div_le_iff₀ hden).2 (hNI.trans (mul_le_mul_of_nonneg_left hcentral hratio))
  have hs : 0 ≤ seminorms.sup (schwartzSeminormFamily ℂ V ℂ) φ := apply_nonneg _ _
  rw [second_zero_gram_norm_identity seminorms φ c d rawLeft rawRight NL NR NI hleft hright]
  exact (mul_le_mul_of_nonneg_left hnorm
    (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hs)).trans_eq (by ring)

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

/-- This supplies the exact individual profile inequality demanded by
`ActualGaussStage.TerminalCalibration.zero_normalization`. The constant
is fixed before the source profile, its column norms and all scales. -/
theorem second_zero_profile_normalization_uniform
    (B loss : ℝ) (hB : 0 ≤ B) (hloss : 0 < loss) :
    ∃ Cmask : ℝ, 0 < Cmask ∧ ∀ (Z : ℝ), 1 ≤ Z →
    ∀ (radius : {r : ℝ // 0 < r})
      (M : Finset (HeightOneSpectrum
        (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
      (R : Ideal (𝓞 K)), R ≠ 0 → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      OriginalMaskPrimeData M R →
    ∀ (seminorms : Finset (ℕ × ℕ)) (φ : SchwartzMap V ℂ)
      (c d rawLeft rawRight : ℂ)
      (NL NR NI columnExponent ratio profileBound profileExponent
        inverseRadiusExponent productExponent : ℝ),
      0 ≤ NI → 0 ≤ ratio → 0 ≤ profileBound →
      Z ^ columnExponent ≤ NL → Z ^ columnExponent ≤ NR →
      NI ≤ ratio * Z ^ columnExponent →
      c = rawLeft / (Real.sqrt NL : ℂ) → d = rawRight / (Real.sqrt NR : ℂ) →
      (‖rawLeft‖ * ‖rawRight‖ * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) φ) ≤
        profileBound * Z ^ profileExponent →
      radius.val⁻¹ ≤ Z ^ inverseRadiusExponent →
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) ((c * star d) • φ) * NI *
          (∑ D ∈ M.powerset, firstZeroDivisorWeight radius D) ≤
        (Cmask * ratio * profileBound *
          Z ^ (profileExponent + inverseRadiusExponent + loss + productExponent / 2)) /
            Real.sqrt (Z ^ productExponent) := by
  obtain ⟨Cmask, hCmask, hmask⟩ :=
    first_zero_profile_normalization_uniform (S := S) B loss hB hloss
  refine ⟨Cmask, hCmask, ?_⟩
  intro Z hZ radius M R hR hRN W seminorms φ c d rawLeft rawRight NL NR NI
    columnExponent ratio profileBound profileExponent inverseRadiusExponent productExponent
    hNI0 hratio hprofile hNL hNR hNI hleft hright hraw hradius
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hseminorm : 0 ≤ seminorms.sup (schwartzSeminormFamily ℂ V ℂ) ((c * star d) • φ) :=
    apply_nonneg _ _
  have hcoefficient := second_zero_gram_norm_le_original_windows seminorms φ
    Z columnExponent ratio NL NR NI hz hratio hNL hNR hNI c d rawLeft rawRight hleft hright
  have hpoint :
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) ((c * star d) • φ) * NI ≤
        (ratio * profileBound) * Z ^ profileExponent := by
    exact (hcoefficient.trans (mul_le_mul_of_nonneg_left hraw hratio)).trans_eq (by ring)
  have h := hmask Z hZ radius M R hR hRN W
    (seminorms.sup (schwartzSeminormFamily ℂ V ℂ) ((c * star d) • φ) * NI)
    (ratio * profileBound) profileExponent inverseRadiusExponent productExponent
    (mul_nonneg hseminorm hNI0) (mul_nonneg hratio hprofile) hpoint hradius
  exact h.trans_eq (by ring)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.second_zero_gram_norm_diagonal
#print axioms HeckeSkeleton.Moments.EngineStep.second_zero_gram_norm_le_original_windows
#print axioms HeckeSkeleton.Moments.EngineStep.second_zero_profile_normalization_uniform
