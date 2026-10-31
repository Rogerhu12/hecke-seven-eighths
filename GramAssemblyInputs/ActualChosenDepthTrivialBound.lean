import ActualChosenDepthPoissonBound
import HeckeGeneral.Analysis.SUnitTotalNormFourierBounds

/-!
UNCOMPILED / native 0. The actual chart coefficient has a uniform norm
bound without a good prime. The existing all-scale lattice count therefore
bounds the literal chosen-depth periodic sum by its zeroth seminorm.
The balanced and total-norm versions retain the unsplit joint kernel and
both finite coordinates. No all-radius bound for the input profile is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.Analysis.ActualChosenDepthTrivialDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open AlgebraicNumberTheory.PowerResidueSymbols
open ActualGramJointMeanDraft ActualGramJointChartDraft ActualGramJointChartCoverDraft
open ActualGramCoefficientBoundDraft ActualGramPeriodNormDraft
open ActualMeanZeroProductPoissonDraft ActualFixedDepthAllScaleDraft
open ActualBalancedClearedJointDraft ActualBalancedJointSeminormDraft
open ActualBalancedJointSupportFourierDraft
open scoped Classical BigOperators ContDiff nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "NZ" => NonzeroRingElements (S.integer K)
local notation "W" => traceProductSpace K

/-- This branch uses neither mean zero nor a prime at the frequency. -/
theorem exists_uniform_chosenDepth_weight_allScale_trivial_bound
    (depth clearing : ℕ) (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c k : NZ)
      (a₁ a₂ : 𝓞 K ⧸ clearedSModulus K S ζ hζ depth) (d b₁ b₂ : NZ)
      (F : SchwartzMap W ℂ) (N : ℝ), 0 < N → F 0 = 0 →
      (∀ x, F x ≠ 0 → ‖x‖ ≤ B) →
      ‖productPeriodicSum K (fixedChartPeriodIdeal K S ζ hζ c k depth)
        (fixedChartLatticeWeight K S ζ hζ σ hS6 c k depth clearing a₁ a₂ d b₁ b₂) F N 0‖ ≤
      C * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
        SchwartzMap.seminorm ℂ 0 0 F * N ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_productPeriodicSum_allScale_trivial_bound K B hB
  refine ⟨C, hC, ?_⟩
  intro c k a₁ a₂ d b₁ b₂ F N hN hF0 hFB
  exact hb (fixedChartPeriodIdeal K S ζ hζ c k depth)
    (fixedChartLatticeWeight K S ζ hζ σ hS6 c k depth clearing a₁ a₂ d b₁ b₂)
    F N (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) hN (Nat.cast_nonneg _)
    (norm_fixedChartLatticeWeight_le_absNorm K S ζ hζ σ hS6
      c k depth clearing a₁ a₂ d b₁ b₂) hF0 hFB

variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Z" => SFiniteLocalGroup K S
variable (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
  (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
  (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)

/-- The fixed support and compact divisor set make the constant uniform in
all moving data. The original joint profile needs only its zeroth seminorm. -/
theorem exists_balancedJoint_chosenDepth_allScale_trivial_bound (depth clearing : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ (c k : NZ)
      (a₁ a₂ : 𝓞 K ⧸ clearedSModulus K S ζ hζ depth) (d b₁ b₂ : NZ),
      ∀ y ∈ sUnitCompactRepresentativeSet K S Γ,
      ∀ (ν : ℝ) (z₁ z₂ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r})
        (N : ℝ), 0 < N →
      ‖productPeriodicSum K (fixedChartPeriodIdeal K S ζ hζ c k depth)
        (fixedChartLatticeWeight K S ζ hζ σ hS6 c k depth clearing a₁ a₂ d b₁ b₂)
        (balancedClearedJointTraceSchwartz K S Γ a ha a0 b0 ha0 haSupport
          ψ hψ hψsupport clearing y ν z₁ z₂ φ R) N 0‖ ≤
      C * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
        s.sup (schwartzSeminormFamily ℝ (V × V) ℂ)
          (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
            ψ hψ hψsupport ν z₁ z₂ φ R) * N ^ 2 := by
  obtain ⟨B, hB, hsupp⟩ := exists_balancedJoint_support_radius K S Γ
    a ha a0 b0 ha0 haSupport ψ hψ hψsupport clearing
  obtain ⟨C₀, hC₀, hb⟩ := exists_uniform_chosenDepth_weight_allScale_trivial_bound
    K S ζ hζ σ hS6 depth clearing B hB
  obtain ⟨D, hD, hd⟩ := exists_balancedJoint_profile_seminorm_bound K S Γ
    a ha a0 b0 ha0 haSupport ψ hψ hψsupport clearing 0 0
  refine ⟨{(0, 0)}, C₀ * D, mul_pos hC₀ hD, ?_⟩
  intro c k a₁ a₂ d b₁ b₂ y hy ν z₁ z₂ φ R N hN
  have hfirst := hb c k a₁ a₂ d b₁ b₂ _ N hN
    (balancedJoint_zero K S Γ a ha a0 b0 ha0 haSupport
      ψ hψ hψsupport clearing y ν z₁ z₂ φ R)
    (hsupp y hy ν z₁ z₂ φ R)
  have h0 : SchwartzMap.seminorm ℂ 0 0
      (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ν z₁ z₂ φ R) ≤
      ({(0, 0)} : Finset (ℕ × ℕ)).sup (schwartzSeminormFamily ℝ (V × V) ℂ)
        (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
          ψ hψ hψsupport ν z₁ z₂ φ R) :=
    HeckeGeneral.Analysis.ActualBalancedJointSupportFourierDraft.schwartzSeminorm_le_finset_sup K
      {(0, 0)} (0, 0) (Finset.mem_singleton_self (0, 0)) _
  have hsemi := (hd y hy ν z₁ z₂ φ R).trans (mul_le_mul_of_nonneg_left h0 hD.le)
  have hqC : 0 ≤ (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ _ := hfirst
    _ ≤ C₀ * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
        (D * ({(0, 0)} : Finset (ℕ × ℕ)).sup (schwartzSeminormFamily ℝ (V × V) ℂ)
          (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
            ψ hψ hψsupport ν z₁ z₂ φ R)) * N ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsemi (mul_nonneg hC₀.le hqC)) (sq_nonneg N)
    _ = _ := by ring

/-- The same bound after inserting both finite norm factors into the radius.
It controls the original total-norm Schwartz map, before any Fourier map. -/
theorem exists_balancedTotalNorm_chosenDepth_allScale_trivial_bound (depth clearing : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ (c k : NZ)
      (a₁ a₂ : 𝓞 K ⧸ clearedSModulus K S ζ hζ depth) (d b₁ b₂ : NZ),
      ∀ y ∈ sUnitCompactRepresentativeSet K S Γ,
      ∀ (ν : ℝ) (z₁ z₂ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r})
        (N : ℝ), 0 < N →
      ‖productPeriodicSum K (fixedChartPeriodIdeal K S ζ hζ c k depth)
        (fixedChartLatticeWeight K S ζ hζ σ hS6 c k depth clearing a₁ a₂ d b₁ b₂)
        (balancedClearedJointTraceSchwartz K S Γ a ha a0 b0 ha0 haSupport
          ψ hψ hψsupport clearing y ν z₁ z₂ φ (sUnitTotalNormRadius K S z₁ z₂ R)) N 0‖ ≤
      C * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
        s.sup (schwartzSeminormFamily ℝ (V × V) ℂ)
          (sUnitTotalNormAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
            ψ hψ hψsupport ν z₁ z₂ φ R) * N ^ 2 := by
  obtain ⟨s, C, hC, hb⟩ := exists_balancedJoint_chosenDepth_allScale_trivial_bound
    K S ζ hζ σ hS6 Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport depth clearing
  refine ⟨s, C, hC, ?_⟩
  intro c k a₁ a₂ d b₁ b₂ y hy ν z₁ z₂ φ R N hN
  exact hb c k a₁ a₂ d b₁ b₂ y hy ν z₁ z₂ φ (sUnitTotalNormRadius K S z₁ z₂ R) N hN

end HeckeGeneral.Analysis.ActualChosenDepthTrivialDraft
