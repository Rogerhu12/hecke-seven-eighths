import ActualSexticPeriodicLatticeWeight
import ActualFixedSBoxDenominator

/-!
UNCOMPILED candidate. The quotient weight agrees with the original
coefficient on every cleared column in a fixed S fiber, not only on the
chosen quotient representatives. At the actual valuation-box depth the
clearing coordinates are constructed from the active divisor and columns.
No coprimality restriction or discarded zero residue is introduced.
-/

noncomputable section

namespace HeckeGeneral.Characters.ActualGramClearedColumnDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open ActualGramJointMeanDraft ActualGramJointChartDraft ActualGramJointChartCoverDraft
open ActualGramCoefficientBoundDraft ActualGramFixedDenominatorDraft
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "OS" => S.integer K
local notation "NZ" => NonzeroRingElements OS
local notation "D" => finiteSIntegerDenominator K S
local notation "H" => finiteIndexSUnitBoxWidth K S Γ
local notation:max "active" m:max =>
  Prod.snd (sLocalNonzeroIntegerDiagonal K S m) ∈ finiteLocalValuationBox K S H
local notation:max "clear" M:max m:max z:max =>
  algebraMap (𝓞 K) OS (D ^ M) * Subtype.val m = algebraMap (𝓞 K) OS z

/-- Agreement on all actual columns with the stated ordinary residue,
including exterior collision zeros. The columns are not replaced by a
selected representative of their period class. -/
theorem fixedChartPeriodWeight_eq_original_of_cleared_columns
    (c k d m₀₁ m₀₂ m₁ m₂ : NZ) (M L : ℕ) (a z₀₁ z₀₂ z₁ z₂ : 𝓞 K)
    (hd : clear L d a) (h₀₁ : clear M m₀₁ z₀₁) (h₀₂ : clear M m₀₂ z₀₂)
    (h₁ : clear M m₁ z₁) (h₂ : clear M m₂ z₂)
    (hb₁ : active (divisorColumn K S d m₀₁))
    (hb₂ : active (divisorColumn K S d m₀₂))
    (hz₁ : z₁ - z₀₁ ∈ clearedSModulus K S ζ hζ (M + L))
    (hz₂ : z₂ - z₀₂ ∈ clearedSModulus K S ζ hζ (M + L)) :
    fixedChartPeriodWeight K S ζ hζ σ hS6 c k (M + L) M
      (Ideal.Quotient.mk _ z₀₁) (Ideal.Quotient.mk _ z₀₂) d
      (divisorColumn K S d m₀₁) (divisorColumn K S d m₀₂)
      (Ideal.Quotient.mk _ z₁, Ideal.Quotient.mk _ z₂) =
    originalChartCoefficient K S ζ hζ σ hS6 c k d m₁ m₂ := by
  have hchart₁ := divisorColumn_chart_of_cleared_congruence K S ζ hζ
    M L d m₁ m₀₁ a z₁ z₀₁ hd h₁ h₀₁ hz₁
  have hchart₂ := divisorColumn_chart_of_cleared_congruence K S ζ hζ
    M L d m₂ m₀₂ a z₂ z₀₂ hd h₂ h₀₂ hz₂
  have hres₁ : Ideal.Quotient.mk (clearedSModulus K S ζ hζ (M + L)) z₁ =
      Ideal.Quotient.mk _ z₀₁ := Ideal.Quotient.eq.mpr hz₁
  have hres₂ : Ideal.Quotient.mk (clearedSModulus K S ζ hζ (M + L)) z₂ =
      Ideal.Quotient.mk _ z₀₂ := Ideal.Quotient.eq.mpr hz₂
  unfold fixedChartPeriodWeight
  simp only [chartCRT_mk, hres₁, hres₂, if_pos rfl]
  rw [denominatorScale_eq_jointReduction K S _ _ _ _ _ _ M z₁ m₁.val h₁,
    denominatorScale_eq_jointReduction K S _ _ _ _ _ _ M z₂ m₂.val h₂]
  exact (raw_mul_RCorrection_mul_residual_eq_chart_jointCoefficient
    K S ζ hζ σ hS6 c k Γ d m₁ (divisorColumn K S d m₀₁)
      m₂ (divisorColumn K S d m₀₂) hchart₁ hchart₂ hb₁ hb₂).symm

/-- The divisor and reference columns in the actual fixed box determine
ordinary coordinates using D^H. Every other active column then has the
same fixed denominator, and the agreement uses the fixed period depth 2H.
The residue-fiber condition is retained; no analytic estimate is assumed. -/
theorem exists_fixedDepth_original_coefficient_coordinates
    (c k d m₀₁ m₀₂ : NZ) (hd : active d)
    (h₀₁ : active (divisorColumn K S d m₀₁))
    (h₀₂ : active (divisorColumn K S d m₀₂)) :
    ∃ a z₀₁ z₀₂ : 𝓞 K, clear H d a ∧ clear H m₀₁ z₀₁ ∧ clear H m₀₂ z₀₂ ∧
      ∀ m₁ m₂ : NZ,
        active (divisorColumn K S d m₁) → active (divisorColumn K S d m₂) →
        ∃ z₁ z₂ : 𝓞 K, clear H m₁ z₁ ∧ clear H m₂ z₂ ∧
          (z₁ - z₀₁ ∈ clearedSModulus K S ζ hζ (H + H) →
           z₂ - z₀₂ ∈ clearedSModulus K S ζ hζ (H + H) →
            fixedChartPeriodWeight K S ζ hζ σ hS6 c k (H + H) H
              (Ideal.Quotient.mk _ z₀₁) (Ideal.Quotient.mk _ z₀₂) d
              (divisorColumn K S d m₀₁) (divisorColumn K S d m₀₂)
              (Ideal.Quotient.mk _ z₁, Ideal.Quotient.mk _ z₂) =
            originalChartCoefficient K S ζ hζ σ hS6 c k d m₁ m₂) := by
  obtain ⟨a, z₀₁, z₀₂, ha, hz₀₁, hz₀₂⟩ :=
    fixed_clearing_triple K S H d m₀₁ m₀₂ hd h₀₁ h₀₂
  refine ⟨a, z₀₁, z₀₂, ha, hz₀₁, hz₀₂, ?_⟩
  intro m₁ m₂ hm₁ hm₂
  obtain ⟨z₁, hz₁⟩ :=
    exactSDenominator_pow_clears_divisor_quotient K S H d m₁ hd hm₁
  obtain ⟨z₂, hz₂⟩ :=
    exactSDenominator_pow_clears_divisor_quotient K S H d m₂ hd hm₂
  refine ⟨z₁, z₂, hz₁, hz₂, fun hres₁ hres₂ => ?_⟩
  exact fixedChartPeriodWeight_eq_original_of_cleared_columns K S ζ hζ σ hS6 Γ
    c k d m₀₁ m₀₂ m₁ m₂ H H a z₀₁ z₀₂ z₁ z₂
    ha hz₀₁ hz₀₂ hz₁ hz₂ h₀₁ h₀₂ hres₁ hres₂

end HeckeGeneral.Characters.ActualGramClearedColumnDraft
