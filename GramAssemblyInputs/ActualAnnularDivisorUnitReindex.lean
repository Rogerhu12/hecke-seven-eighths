import ActualWholeAnnularAllScalePoisson
import HeckeGeneral.Arithmetic.SIntegerTripleReindex

/-!
UNCOMPILED / native 0. The true inverse-unit change of both column indices
transports the selected divisor back to the original divisor. The actual
products d*m_i are unchanged, including their finite coordinates, every
zero mask, the raw/R factors and the artificial residual extension.

This is the literal originalChartCoefficient route (the actual c=1 ideal
coefficient route); c below is the common-factor frequency element, not an
arbitrary ideal-coefficient family. No invariance of extra coefficients is
assumed or claimed. The original Gamma and the single joint profile remain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeGeneral.Analysis.ActualAnnularDivisorUnitReindexDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open AlgebraicNumberTheory.PowerResidueSymbols
open HeckeGeneral.Arithmetic.PeriodicFourier
open ActualGramJointMeanDraft ActualGramJointChartDraft ActualGramJointChartCoverDraft
open ActualGramFamilyDraft ActualGramFixedDenominatorDraft
open ActualClearedJointPeriodicDraft ActualWholeAnnularAllScaleDraft
open scoped Classical BigOperators ContDiff nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "NZ" => NonzeroRingElements (S.integer K)
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- Both literal product columns survive the same original-subgroup
divisor translation and inverse translation of the quotient index. -/
theorem divisorColumn_translate_inverse (u : Γ) (d m : NZ) :
    divisorColumn K S (sIntegerOrbitTranslate K S Γ u d)
      (sIntegerOrbitTranslate K S Γ u⁻¹ m) = divisorColumn K S d m := by
  apply Subtype.ext
  apply Subtype.ext
  change ((sIntegerOrbitTranslate K S Γ u d).val : K) *
    ((sIntegerOrbitTranslate K S Γ u⁻¹ m).val : K) = (d.val : K) * (m.val : K)
  simp only [sIntegerOrbitTranslate_val, Subgroup.coe_inv, Units.val_inv_eq_inv_val]
  have hu : ((u.val : Kˣ) : K) ≠ 0 := (u.val : Kˣ).ne_zero
  field_simp [hu]
  <;> ring

variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)

private theorem residualExtension_eq_of_product_columns
    (c k d e m₁ m₂ n₁ n₂ : NZ)
    (h₁ : divisorColumn K S e n₁ = divisorColumn K S d m₁)
    (h₂ : divisorColumn K S e n₂ = divisorColumn K S d m₂) :
    actualResidualExtension K S ζ hζ σ
        (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
        (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)
        (actualFrequencyIdeal_exterior K S c) (actualFrequencyIdeal_exterior K S k)
        hS6 e.val k.val n₁.val n₂.val =
      actualResidualExtension K S ζ hζ σ
        (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
        (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)
        (actualFrequencyIdeal_exterior K S c) (actualFrequencyIdeal_exterior K S k)
        hS6 d.val k.val m₁.val m₂.val := by
  have he₁ : e.val * n₁.val = d.val * m₁.val := congrArg Subtype.val h₁
  have he₂ : e.val * n₂.val = d.val * m₂.val := congrArg Subtype.val h₂
  unfold actualResidualExtension
  apply Finset.prod_congr rfl
  intro p _
  let red := sIntegerSexticResidueMap K S p.val
    (jointExterior K S (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
      (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)
      (actualFrequencyIdeal_exterior K S c) (actualFrequencyIdeal_exterior K S k) p)
  have hr₁ : red e.val * red n₁.val = red d.val * red m₁.val := by
    simpa only [map_mul] using congrArg red he₁
  have hr₂ : red e.val * red n₂.val = red d.val * red m₂.val := by
    simpa only [map_mul] using congrArg red he₂
  simp only [residualColumnFactor, jointReduction]
  rw [hr₁, hr₂]

/-- The actual coefficient is unchanged because its two product columns
are unchanged. This retains every artificial residual-extension zero. -/
theorem originalChartCoefficient_translate_inverse (c k : NZ) (u : Γ)
    (d m₁ m₂ : NZ) :
    originalChartCoefficient K S ζ hζ σ hS6 c k (sIntegerOrbitTranslate K S Γ u d)
      (sIntegerOrbitTranslate K S Γ u⁻¹ m₁) (sIntegerOrbitTranslate K S Γ u⁻¹ m₂) =
      originalChartCoefficient K S ζ hζ σ hS6 c k d m₁ m₂ := by
  have h₁ := divisorColumn_translate_inverse K S Γ u d m₁
  have h₂ := divisorColumn_translate_inverse K S Γ u d m₂
  unfold originalChartCoefficient
  rw [h₁, h₂, residualExtension_eq_of_product_columns K S ζ hζ σ hS6
    c k d (sIntegerOrbitTranslate K S Γ u d) m₁ m₂
      (sIntegerOrbitTranslate K S Γ u⁻¹ m₁) (sIntegerOrbitTranslate K S Γ u⁻¹ m₂) h₁ h₂]

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (a : ℝ → ℝ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)

/-- A pointwise actual identity, with the original finite coordinates and
the unsplit joint factor. No profile change or unit-invariance input occurs. -/
theorem actualAnnularJointSummand_translate_inverse (c k : NZ) (u : Γ) (d : NZ)
    (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) (N : ℝ) (m : NZ × NZ) :
    actualAnnularJointSummand K S Γ a ψ ζ hζ σ hS6 c k
      (sIntegerOrbitTranslate K S Γ u d) ν φ R N
      (((sIntegerTranslateEquiv K S Γ u⁻¹).prodCongr
        (sIntegerTranslateEquiv K S Γ u⁻¹)) m) =
      actualAnnularJointSummand K S Γ a ψ ζ hζ σ hS6 c k d ν φ R N m := by
  rcases m with ⟨m₁, m₂⟩
  change actualAnnularJointSummand K S Γ a ψ ζ hζ σ hS6 c k
    (sIntegerOrbitTranslate K S Γ u d) ν φ R N
    (sIntegerOrbitTranslate K S Γ u⁻¹ m₁, sIntegerOrbitTranslate K S Γ u⁻¹ m₂) = _
  unfold actualAnnularJointSummand annularOriginalSummand
  rw [originalChartCoefficient_translate_inverse K S Γ ζ hζ σ hS6 c k u d m₁ m₂]
  simp only [originalJointFactor, divisorColumn_translate_inverse K S Γ u d m₁,
    divisorColumn_translate_inverse K S Γ u d m₂]

/-- One complete product-index reindexing, requiring no extra convergence
input. All original subgroup elements and nonzero S-integers remain. -/
theorem tsum_actualAnnularJointSummand_translate (c k : NZ) (u : Γ) (d : NZ)
    (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) (N : ℝ) :
    (∑' m, actualAnnularJointSummand K S Γ a ψ ζ hζ σ hS6 c k d ν φ R N m) =
      ∑' m, actualAnnularJointSummand K S Γ a ψ ζ hζ σ hS6 c k
        (sIntegerOrbitTranslate K S Γ u d) ν φ R N m := by
  calc
    _ = ∑' m, actualAnnularJointSummand K S Γ a ψ ζ hζ σ hS6 c k
        (sIntegerOrbitTranslate K S Γ u d) ν φ R N
        (((sIntegerTranslateEquiv K S Γ u⁻¹).prodCongr
          (sIntegerTranslateEquiv K S Γ u⁻¹)) m) := by
      apply tsum_congr
      intro m
      exact (actualAnnularJointSummand_translate_inverse K S Γ ζ hζ σ hS6
        a ψ c k u d ν φ R N m).symm
    _ = _ := ((sIntegerTranslateEquiv K S Γ u⁻¹).prodCongr
      (sIntegerTranslateEquiv K S Γ u⁻¹)).tsum_eq _

variable (ha : ContDiff ℝ ∞ a) (a0 b0 : ℝ) (ha0 : 0 < a0)
  (haSupport : tsupport a ⊆ Set.Icc a0 b0)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)

/-- The previous balanced whole-sum estimate now applies to the fixed
ORIGINAL divisor. The real norm q_d is preserved by the genuine S-unit
translation; no missing divisor transport remains in this endpoint. -/
theorem exists_original_whole_annular_fixedDepth_allScale_min_bound
    (A : ℕ) (hA : 2 < A) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ (d c k : NZ)
      (p : jointPlaces K (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
        (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)),
      (¬ p.val.asIdeal ∣ actualFrequencyIdeal K S c) →
      (¬ 6 ∣ idealPrimeMultiplicity K p.val (actualFrequencyIdeal K S k)) →
      ∀ (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) (N : ℝ), 0 < N →
      ‖∑' m, actualAnnularJointSummand K S Γ a ψ ζ hζ σ hS6 c k d ν φ R N m‖ ≤
        C * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
          fixedBoxJointSeminormSum K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport s ν φ R *
          (N / (sIntegerElementNorm K S d).val) ^ 2 *
          min 1 ((((Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
            (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) /
              (N / (sIntegerElementNorm K S d).val)) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := exists_whole_annular_fixedDepth_allScale_min_bound
    K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport ζ hζ σ hS6 A hA
  refine ⟨s, C, hC, ?_⟩
  intro d c k p hpC hpJ ν φ R N hN
  obtain ⟨u, _, _, hu⟩ := hb d
  have h := hu c k p hpC hpJ ν φ R N hN
  rw [← tsum_actualAnnularJointSummand_translate K S Γ ζ hζ σ hS6
    a ψ c k u d ν φ R N] at h
  simpa only [elementNorm_subgroup_translate K S Γ u d] using h

end HeckeGeneral.Analysis.ActualAnnularDivisorUnitReindexDraft
