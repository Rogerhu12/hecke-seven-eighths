import ActualChoiceMaskedWholeAnnular
import ActualAnnularDivisorUnitReindex

/-!
UNCOMPILED / native 0. Remove the compact and active divisor restrictions
by the SAME original sixth-power unit subgroup. Both literal products d*m
are unchanged by inverse column translation, so their actual choice masks
are unchanged as well. No uniform estimate under arbitrary unit changes
of a Schwartz test is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualChoiceMaskedOriginalDivisorDraft

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open AlgebraicNumberTheory.PowerResidueSymbols
open ActualGeneratorChoiceDraft ActualChoiceMaskedAnnularDraft
open ActualGramJointChartDraft ActualGramJointMeanDraft
open ActualGramFixedDenominatorDraft ActualWholeAnnularAllScaleDraft
open ActualAnnularDivisorUnitReindexDraft
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]
variable (w : GeneratorMaskWitness K)
local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Γ" => sixthPowerUnits K S
local notation "NZ" => NonzeroRingElements (Set.integer S K)
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

local instance originalMask_sixthUnits_finiteIndex : Subgroup.FiniteIndex Γ :=
  sUnit_power_range_finiteIndex K S 6 (by decide)

theorem choiceColumnMask_translate_inverse (u : Γ) (d m : NZ) :
    choiceColumnMask K w (sIntegerOrbitTranslate K S Γ u d)
      (sIntegerOrbitTranslate K S Γ u⁻¹ m) = choiceColumnMask K w d m := by
  unfold choiceColumnMask
  rw [divisorColumn_translate_inverse K S Γ u d m]

variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ (w.S : Set (HeightOneSpectrum (𝓞 K))))
variable [MeasurableSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))] [BorelSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
variable (a : ℝ → ℝ) (ψ : ((v : (w.S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)

theorem choiceMaskedActualAnnularJointSummand_translate_inverse
    (c k : NZ) (u : Γ) (d : NZ) (ν : ℝ) (φ : SchwartzMap V ℂ)
    (R : {r : ℝ // 0 < r}) (N : ℝ) (m : NZ × NZ) :
    choiceMaskedActualAnnularJointSummand K w ζ hζ σ hS6 a ψ c k
      (sIntegerOrbitTranslate K S Γ u d) ν φ R N
      (((sIntegerTranslateEquiv K S Γ u⁻¹).prodCongr
        (sIntegerTranslateEquiv K S Γ u⁻¹)) m) =
      choiceMaskedActualAnnularJointSummand K w ζ hζ σ hS6 a ψ c k d ν φ R N m := by
  rcases m with ⟨m₁, m₂⟩
  change choiceColumnMask K w (sIntegerOrbitTranslate K S Γ u d)
      (sIntegerOrbitTranslate K S Γ u⁻¹ m₁) *
      choiceColumnMask K w (sIntegerOrbitTranslate K S Γ u d)
        (sIntegerOrbitTranslate K S Γ u⁻¹ m₂) *
      actualAnnularJointSummand K S Γ a ψ ζ hζ σ hS6 c k
        (sIntegerOrbitTranslate K S Γ u d) ν φ R N
        (sIntegerOrbitTranslate K S Γ u⁻¹ m₁, sIntegerOrbitTranslate K S Γ u⁻¹ m₂) =
    choiceColumnMask K w d m₁ * choiceColumnMask K w d m₂ *
      actualAnnularJointSummand K S Γ a ψ ζ hζ σ hS6 c k d ν φ R N (m₁, m₂)
  rw [choiceColumnMask_translate_inverse K w u d m₁,
    choiceColumnMask_translate_inverse K w u d m₂]
  congr 1
  exact actualAnnularJointSummand_translate_inverse K S Γ ζ hζ σ hS6
    a ψ c k u d ν φ R N (m₁, m₂)

/-- A bijection of the complete product index, with no Fubini exchange. -/
theorem tsum_choiceMaskedActualAnnularJointSummand_translate
    (c k : NZ) (u : Γ) (d : NZ) (ν : ℝ) (φ : SchwartzMap V ℂ)
    (R : {r : ℝ // 0 < r}) (N : ℝ) :
    (∑' m, choiceMaskedActualAnnularJointSummand K w ζ hζ σ hS6 a ψ c k d ν φ R N m) =
      ∑' m, choiceMaskedActualAnnularJointSummand K w ζ hζ σ hS6 a ψ c k
        (sIntegerOrbitTranslate K S Γ u d) ν φ R N m := by
  calc
    _ = ∑' m, choiceMaskedActualAnnularJointSummand K w ζ hζ σ hS6 a ψ c k
        (sIntegerOrbitTranslate K S Γ u d) ν φ R N
        (((sIntegerTranslateEquiv K S Γ u⁻¹).prodCongr
          (sIntegerTranslateEquiv K S Γ u⁻¹)) m) := by
      exact tsum_congr (fun m =>
        (choiceMaskedActualAnnularJointSummand_translate_inverse
          K w ζ hζ σ hS6 a ψ c k u d ν φ R N m).symm)
    _ = _ := ((sIntegerTranslateEquiv K S Γ u⁻¹).prodCongr
      (sIntegerTranslateEquiv K S Γ u⁻¹)).tsum_eq _

variable (ha : ContDiff ℝ ∞ a) (a0 b0 : ℝ) (ha0 : 0 < a0)
  (haSupport : tsupport a ⊆ Set.Icc a0 b0)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)

/-- The actual masked bound for every original divisor. The same compact
representative supplies both required conditions and preserves q_d. -/
theorem exists_choiceMasked_originalDivisor_allScale_min_bound
    (A : ℕ) (hA : 2 < A) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ (d c k : NZ)
      (p : jointPlaces K (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
        (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)),
      (¬ p.val.asIdeal ∣ actualFrequencyIdeal K S c) →
      (¬ 6 ∣ idealPrimeMultiplicity K p.val (actualFrequencyIdeal K S k)) →
      ∀ (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) (N : ℝ), 0 < N →
      ‖∑' m, choiceMaskedActualAnnularJointSummand K w ζ hζ σ hS6 a ψ c k d ν φ R N m‖ ≤
        C * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
          fixedBoxJointSeminormSum K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport s ν φ R *
          (N / (sIntegerElementNorm K S d).val) ^ 2 *
          min 1 ((((Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
            (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) /
              (N / (sIntegerElementNorm K S d).val)) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := exists_choiceMasked_whole_annular_allScale_min_bound
    (K := K) (w := w) (ζ := ζ) (hζ := hζ) (σ := σ) (hS6 := hS6)
    (a := a) (ha := ha) (a0 := a0) (b0 := b0) (ha0 := ha0) (haSupport := haSupport)
    (ψ := ψ) (hψ := hψ) (hψsupport := hψsupport) A hA
  refine ⟨s, C, hC, ?_⟩
  intro d c k p hpC hpJ ν φ R N hN
  obtain ⟨u, hcompact, hactive, _, _⟩ :=
    exists_compact_divisor_with_fixed_denominator K S Γ d
  have h := hb (sIntegerOrbitTranslate K S Γ u d) hcompact hactive
    c k p hpC hpJ ν φ R N hN
  rw [← tsum_choiceMaskedActualAnnularJointSummand_translate
    K w ζ hζ σ hS6 a ψ c k u d ν φ R N] at h
  simpa only [elementNorm_subgroup_translate K S Γ u d] using h

end HeckeGeneral.ThetaSkeleton.Physical.ActualChoiceMaskedOriginalDivisorDraft
