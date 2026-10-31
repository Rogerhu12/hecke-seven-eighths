import HeckeGeneral.Analysis.PhysicalProbeData
import ActualSexticAnnularChartFamily
import ActualOriginalChartSixthUnit
import ActualScaledColumnUnitReconstruction

/-!
UNCOMPILED / native 0. Original raw/R/residual coefficients are retained
inside the actual annular column sum. Fixed-frequency sixth-unit
invariance and the proved analytic partition reconstruct each ideal pair.
The whole column family has finite support from its original cutoffs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualOriginalAnnularUnitDraft

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open ActualGramJointChartDraft ActualGramJointChartCoverDraft ActualGramFamilyDraft
open ActualOriginalChartSixthUnitDraft ActualScaledColumnUnitDraft
open ActualTraceProductFourierDilationDraft
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "NZ" => NonzeroRingElements (S.integer K)
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Γ" => sixthPowerUnits K S
local instance : Subgroup.FiniteIndex Γ := sUnit_power_range_finiteIndex K S 6 (by decide)

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)

/-- The literal original coefficient and two annular columns, with each
term's own finite-norm compensation in the joint orbital factor. -/
def originalTotalNormAnnularSummand
    (a : ℝ → ℝ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (c k d : NZ) (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r})
    (N : ℝ) : NZ × NZ → ℂ :=
  annularOriginalSummand K S ζ hζ Γ σ hS6 c k d a a
    (traceNormScale K N) (traceNormScale K N)
    (scaledColumnCompensatedJointFactor K S ψ d ν φ R N)

theorem originalTotalNormAnnularSummand_eq_coefficient
    (a : ℝ → ℝ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (c k d : NZ) (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r})
    (N : ℝ) (m : NZ × NZ) :
    originalTotalNormAnnularSummand K S ζ hζ σ hS6 a ψ c k d ν φ R N m =
      originalChartCoefficient K S ζ hζ σ hS6 c k d m.1 m.2 *
        scaledColumnAnnularJointTerm K S Γ a ψ d ν φ R N m := by
  dsimp only [originalTotalNormAnnularSummand, annularOriginalSummand,
    scaledColumnAnnularJointTerm]
  ring

/-- Actual global finite support, independent of coefficient cancellation
or any already established Gram estimate. -/
theorem originalTotalNormAnnularSummand_hasFiniteSupport
    (a : ℝ → ℝ) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (haSupport : tsupport a ⊆ Set.Icc a0 b0)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (c k d : NZ) (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r})
    (N : ℝ) (hN : 0 < N) :
    Function.HasFiniteSupport
      (originalTotalNormAnnularSummand K S ζ hζ σ hS6 a ψ c k d ν φ R N) := by
  have hs := finite_support_divisor_annularColumn K S Γ d a a0 b0 ha0 haSupport
    (traceNormScale K N) (traceNormScale_pos K N hN).ne'
  apply (hs.prod hs).subset
  rintro ⟨m₁, m₂⟩ hm
  constructor
  · intro hz
    exact hm (by simp only [originalTotalNormAnnularSummand, annularOriginalSummand,
      hz, Complex.ofReal_zero, mul_zero, zero_mul])
  · intro hz
    exact hm (by simp only [originalTotalNormAnnularSummand, annularOriginalSummand,
      hz, Complex.ofReal_zero, mul_zero, zero_mul])

/-- The original arithmetic factor is invariant at the same frequency;
thus the genuine double-unit family is summable for each pair. -/
theorem originalTotalNormAnnularSummand_units_summable
    (a : ℝ → ℝ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (c k d m₁ m₂ : NZ) (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r})
    (N : ℝ) (hN : 0 < N) :
    Summable (fun uv : Γ × Γ =>
      originalTotalNormAnnularSummand K S ζ hζ σ hS6 a ψ c k d ν φ R N
        (sIntegerOrbitTranslate K S Γ uv.1 m₁, sIntegerOrbitTranslate K S Γ uv.2 m₂)) := by
  have h := (scaledColumnAnnularJointTerm_summable K S Γ a ψ d m₁ m₂ ν φ R N hN).mul_left
    (originalChartCoefficient K S ζ hζ σ hS6 c k d m₁ m₂)
  apply h.congr
  intro uv
  have hcol (c k d m₁ m₂ : NZ) (u v : Γ) :
      originalChartCoefficient K S ζ hζ σ hS6 c k d
        (sIntegerOrbitTranslate K S Γ u m₁) (sIntegerOrbitTranslate K S Γ v m₂) =
      originalChartCoefficient K S ζ hζ σ hS6 c k d m₁ m₂ :=
    originalChartCoefficient_sixthPower_columns K S ζ hζ σ hS6 c k d m₁ m₂ u v
  rw [originalTotalNormAnnularSummand_eq_coefficient]
  dsimp only
  rw [hcol]

/-- Product-indexed unit reconstruction. No conditional Fubini step is
used; its summability was established from the actual partition. -/
theorem originalTotalNormAnnularSummand_units_tsum
    (a : ℝ → ℝ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (c k d m₁ m₂ : NZ) (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r})
    (N : ℝ) (hN : 0 < N) :
    (∑' uv : Γ × Γ,
      originalTotalNormAnnularSummand K S ζ hζ σ hS6 a ψ c k d ν φ R N
        (sIntegerOrbitTranslate K S Γ uv.1 m₁, sIntegerOrbitTranslate K S Γ uv.2 m₂)) =
      originalChartCoefficient K S ζ hζ σ hS6 c k d m₁ m₂ *
        (scaledColumnCompensatedJointFactor K S ψ d ν φ R N (m₁, m₂) *
          ((a ((Ideal.absNorm (sIntegerModulusContraction K S
                (divisorColumn K S d m₁).val) : ℝ) / N) *
            a ((Ideal.absNorm (sIntegerModulusContraction K S
                (divisorColumn K S d m₂).val) : ℝ) / N) : ℝ) : ℂ)) := by
  rw [(originalTotalNormAnnularSummand_units_summable
    K S ζ hζ σ hS6 a ψ c k d m₁ m₂ ν φ R N hN).tsum_prod]
  have hcol (c k d m₁ m₂ : NZ) (u v : Γ) :
      originalChartCoefficient K S ζ hζ σ hS6 c k d
        (sIntegerOrbitTranslate K S Γ u m₁) (sIntegerOrbitTranslate K S Γ v m₂) =
      originalChartCoefficient K S ζ hζ σ hS6 c k d m₁ m₂ :=
    originalChartCoefficient_sixthPower_columns K S ζ hζ σ hS6 c k d m₁ m₂ u v
  simp_rw [originalTotalNormAnnularSummand_eq_coefficient]
  simp_rw [hcol, tsum_mul_left]
  rw [scaledColumnAnnularJointTerm_two_column K S Γ a ψ d m₁ m₂ ν φ R N hN]

end HeckeGeneral.ThetaSkeleton.Physical.ActualOriginalAnnularUnitDraft
