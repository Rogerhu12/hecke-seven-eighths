import ActualSexticClearedColumnWeight
import ActualSexticAnnularChartFamily

/-!
UNCOMPILED candidate. On a genuine cleared S fiber the entire finite-place
annular cutoff is fixed. Combining this fact with the original coefficient
identity retains one unsplit joint profile and the literal two column
arguments. It does not assert a Schwartz bound for that profile.
-/

noncomputable section

namespace HeckeGeneral.Characters.ActualGramClearedColumnDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open ActualGramJointMeanDraft ActualGramJointChartDraft ActualGramJointChartCoverDraft
open ActualGramCoefficientBoundDraft ActualGramFamilyDraft
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6)
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "OS" => S.integer K
local notation "NZ" => NonzeroRingElements OS
local notation "D" => finiteSIntegerDenominator K S
local notation:max "active" m:max => Prod.snd (sLocalNonzeroIntegerDiagonal K S m) ∈
  finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)

/-- Every original S prime occurs to positive depth in the genuine
correction modulus. No extra S-prime refinement is needed for this lemma. -/
theorem correctionModulus_le_prime (v : S) :
    sIntegerSexticSPlaceModulus K S ζ hζ ≤ v.val.asIdeal := by
  have hn := sPlaceSexticCorrectionDepth_pos K S ζ hζ v
  exact (sIntegerPrincipalUnitModulus_le_prime_pow K S _ v).trans
    (Ideal.pow_le_self (by omega))

/-- The whole archimedean cutoff function, not merely its value at one
point, is fixed by membership in the actual S chart of an active center. -/
theorem annularCutoff_eq_of_fixedSChart (a : ℝ → ℝ) (n base : NZ)
    (hn : n ∈ fixedSChart K S ζ hζ base) (hb : active base) :
    sUnitAnnularPartitionCutoff K S Γ a (sLocalNonzeroIntegerDiagonal K S n).2 =
      sUnitAnnularPartitionCutoff K S Γ a (sLocalNonzeroIntegerDiagonal K S base).2 := by
  obtain ⟨t, ht, he⟩ := hn
  have hreverse : base.val - n.val = algebraMap (𝓞 K) OS (-t) := by
    rw [map_neg, ← he, neg_sub]
  have horders := sIntegerAnnular_active_orders_eq K S Γ base n (-t) hreverse
    (fun v => (v.val.asIdeal).neg_mem (correctionModulus_le_prime K S ζ hζ v ht)) hb
  exact (sUnitAnnularPartitionCutoff_eq_of_orders_eq K S Γ a _ _ horders).symm

/-- Actual annular factor after clearing the divisor and column separately.
The finite coordinate is frozen, while the full moving archimedean argument
is retained. This is not unit-invariance of an arbitrary joint profile. -/
theorem annularColumn_eq_fixedFibre_of_cleared_congruence
    (d m m₀ : NZ) (M L : ℕ) (b z z₀ : 𝓞 K)
    (hd : algebraMap (𝓞 K) OS (D ^ L) * d.val = algebraMap (𝓞 K) OS b)
    (hm : algebraMap (𝓞 K) OS (D ^ M) * m.val = algebraMap (𝓞 K) OS z)
    (h₀ : algebraMap (𝓞 K) OS (D ^ M) * m₀.val = algebraMap (𝓞 K) OS z₀)
    (hb : active (divisorColumn K S d m₀))
    (hz : z - z₀ ∈ clearedSModulus K S ζ hζ (M + L))
    (a : ℝ → ℝ) (r : ℝ) :
    sIntegerAnnularColumn K S Γ a r (divisorColumn K S d m) =
      sUnitAnnularPartitionCutoff K S Γ a
        (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀)).2
        (r⁻¹ • traceEmbedding K ((divisorColumn K S d m).val : K)) := by
  have hchart := divisorColumn_chart_of_cleared_congruence K S ζ hζ
    M L d m m₀ b z z₀ hd hm h₀ hz
  exact congrFun (annularCutoff_eq_of_fixedSChart K S ζ hζ Γ a _ _ hchart hb) _

variable (σ : K →+* ℂ) (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)

/-- Pointwise identity for the complete literal annular summand on one
cleared S fiber. The same joint H is kept, with neither factorization nor
coprimality imposed. Every zero coefficient remains a zero summand. -/
theorem annularOriginalSummand_eq_cleared_weight_fixedFibre
    (c k d m₀₁ m₀₂ m₁ m₂ : NZ) (M L : ℕ) (b z₀₁ z₀₂ z₁ z₂ : 𝓞 K)
    (hd : algebraMap (𝓞 K) OS (D ^ L) * d.val = algebraMap (𝓞 K) OS b)
    (h₀₁ : algebraMap (𝓞 K) OS (D ^ M) * m₀₁.val = algebraMap (𝓞 K) OS z₀₁)
    (h₀₂ : algebraMap (𝓞 K) OS (D ^ M) * m₀₂.val = algebraMap (𝓞 K) OS z₀₂)
    (h₁ : algebraMap (𝓞 K) OS (D ^ M) * m₁.val = algebraMap (𝓞 K) OS z₁)
    (h₂ : algebraMap (𝓞 K) OS (D ^ M) * m₂.val = algebraMap (𝓞 K) OS z₂)
    (hb₁ : active (divisorColumn K S d m₀₁))
    (hb₂ : active (divisorColumn K S d m₀₂))
    (hz₁ : z₁ - z₀₁ ∈ clearedSModulus K S ζ hζ (M + L))
    (hz₂ : z₂ - z₀₂ ∈ clearedSModulus K S ζ hζ (M + L))
    (a₁ a₂ : ℝ → ℝ) (r₁ r₂ : ℝ) (H : NZ × NZ → ℂ) :
    annularOriginalSummand K S ζ hζ Γ σ hS6 c k d a₁ a₂ r₁ r₂ H (m₁, m₂) =
      fixedChartPeriodWeight K S ζ hζ σ hS6 c k (M + L) M
        (Ideal.Quotient.mk _ z₀₁) (Ideal.Quotient.mk _ z₀₂) d
        (divisorColumn K S d m₀₁) (divisorColumn K S d m₀₂)
        (Ideal.Quotient.mk _ z₁, Ideal.Quotient.mk _ z₂) *
      (sUnitAnnularPartitionCutoff K S Γ a₁
        (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀₁)).2
        (r₁⁻¹ • traceEmbedding K ((divisorColumn K S d m₁).val : K)) : ℂ) *
      (sUnitAnnularPartitionCutoff K S Γ a₂
        (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀₂)).2
        (r₂⁻¹ • traceEmbedding K ((divisorColumn K S d m₂).val : K)) : ℂ) * H (m₁, m₂) := by
  rw [fixedChartPeriodWeight_eq_original_of_cleared_columns K S ζ hζ σ hS6 Γ
    c k d m₀₁ m₀₂ m₁ m₂ M L b z₀₁ z₀₂ z₁ z₂ hd h₀₁ h₀₂ h₁ h₂ hb₁ hb₂ hz₁ hz₂]
  unfold annularOriginalSummand
  rw [annularColumn_eq_fixedFibre_of_cleared_congruence K S ζ hζ Γ
      d m₁ m₀₁ M L b z₁ z₀₁ hd h₁ h₀₁ hb₁ hz₁ a₁ r₁,
    annularColumn_eq_fixedFibre_of_cleared_congruence K S ζ hζ Γ
      d m₂ m₀₂ M L b z₂ z₀₂ hd h₂ h₀₂ hb₂ hz₂ a₂ r₂]

end HeckeGeneral.Characters.ActualGramClearedColumnDraft
