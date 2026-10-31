import ActualClearedJointPeriodicTransport
import ActualCompactDivisorReduction
import HeckeGeneral.Analysis.TraceRadialScaling

/-!
UNCOMPILED / native 0. Exact radial separation of the actual d/D^M
multiplier, retaining the original S-local normalization and finite fibers.
The scale becomes N/q_d. The residual multiplier belongs to a fixed compact
set after the actual Gamma representative is chosen. No uniform Schwartz
seminorm estimate, whole-chart identity or Gram estimate is an input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeGeneral.Analysis.ActualBalancedClearedJointDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open ActualGramJointChartCoverDraft ActualClearedJointPeriodicDraft
open ActualGramFixedDenominatorDraft ActualTraceProductFourierDilationDraft
open ActualMeanZeroProductPoissonDraft ActualTraceProductResidueQuotientDraft
open scoped Classical BigOperators ContDiff nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "OS" => S.integer K
local notation "NZ" => NonzeroRingElements OS
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => traceProductSpace K
local notation "U" => (mixedEmbedding.mixedSpace K)ˣ
local notation "G" => sLocalMultiplicativeGroup K S
local notation "Z" => SFiniteLocalGroup K S

/-- The fixed denominator contribution, independent of the divisor. -/
def clearedDenominatorMixedUnit (M : ℕ) : U :=
  Units.map (mixedEmbedding K).toMonoidHom
    (Units.map (algebraMap OS K).toMonoidHom (commonDenominatorUnit K S M)⁻¹)

/-- The archimedean part of the actual normalized local point, with the
same fixed clearing denominator as the arithmetic reindexing. -/
def balancedClearedMixedUnit (M : ℕ) (y : G) : U :=
  y.1 * clearedDenominatorMixedUnit K S M

theorem diagonal_arch_eq_section_mul_normalized (d : NZ) :
    (sLocalNonzeroIntegerDiagonal K S d).1 =
      (sLocalNormSection K S (sIntegerElementNorm K S d)).1 *
        (normalizedDivisorLocalPoint K S d).1 := by
  change (sLocalNonzeroIntegerDiagonal K S d).1 =
    (sLocalNormSection K S (sIntegerElementNorm K S d)).1 *
      ((sLocalNormSection K S (sIntegerElementNorm K S d)).1⁻¹ *
        (sLocalNonzeroIntegerDiagonal K S d).1)
  exact (mul_inv_cancel_left _ _).symm

/-- Genuine mixed-space equality for d/D^M; q_d is the full S-local norm,
and its positive section has finite coordinates exactly one. -/
theorem clearedDivisor_mixed_radial_factor (M : ℕ) (d : NZ) :
    Units.map (mixedEmbedding K).toMonoidHom (clearedDivisorFieldUnit K S M d) =
      (sLocalNormSection K S (sIntegerElementNorm K S d)).1 *
        balancedClearedMixedUnit K S M (normalizedDivisorLocalPoint K S d) := by
  unfold clearedDivisorFieldUnit
  rw [map_mul]
  change (sLocalNonzeroIntegerDiagonal K S d).1 * clearedDenominatorMixedUnit K S M =
    (sLocalNormSection K S (sIntegerElementNorm K S d)).1 *
      ((normalizedDivisorLocalPoint K S d).1 * clearedDenominatorMixedUnit K S M)
  rw [diagonal_arch_eq_section_mul_normalized K S d]
  exact mul_assoc _ _ _

def balancedClearedTraceEquiv (M : ℕ) (y : G) : V ≃L[ℝ] V :=
  traceUnitMulEquiv K (balancedClearedMixedUnit K S M y)

theorem clearedDivisorTraceEquiv_radial_apply (M : ℕ) (d : NZ) (x : V) :
    clearedDivisorTraceEquiv K S M d x =
      traceNormScale K (sIntegerElementNorm K S d).val •
        balancedClearedTraceEquiv K S M (normalizedDivisorLocalPoint K S d) x := by
  rw [clearedDivisorTraceEquiv, clearedDivisor_mixed_radial_factor]
  exact traceUnitMulEquiv_normSection_apply K S (sIntegerElementNorm K S d)
    (balancedClearedMixedUnit K S M (normalizedDivisorLocalPoint K S d)) x

theorem traceNormScale_div {N q : ℝ} (hN : 0 < N) (hq : 0 < q) :
    traceNormScale K (N / q) = traceNormScale K N / traceNormScale K q :=
  Real.div_rpow hN.le hq.le _

/-- Exact rescaling in trace coordinates; the direction is N/q_d. -/
theorem clearedDivisorTraceEquiv_scaled_apply (M : ℕ) (d : NZ)
    (N : ℝ) (hN : 0 < N) (x : V) :
    clearedDivisorTraceEquiv K S M d ((traceNormScale K N)⁻¹ • x) =
      balancedClearedTraceEquiv K S M (normalizedDivisorLocalPoint K S d)
        ((traceNormScale K (N / (sIntegerElementNorm K S d).val))⁻¹ • x) := by
  have hs : (traceNormScale K N)⁻¹ * traceNormScale K (sIntegerElementNorm K S d).val =
      (traceNormScale K (N / (sIntegerElementNorm K S d).val))⁻¹ := by
    rw [traceNormScale_div K hN (sIntegerElementNorm K S d).property]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [map_smul, clearedDivisorTraceEquiv_radial_apply, smul_smul, hs, map_smul]

variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

/-- One fixed compact unit set for the residual multiplier. -/
def balancedClearedMixedSet (M : ℕ) : Set U :=
  balancedClearedMixedUnit K S M '' sUnitCompactRepresentativeSet K S Γ

theorem isCompact_balancedClearedMixedSet (M : ℕ) :
    IsCompact (balancedClearedMixedSet K S Γ M) :=
  (isCompact_sUnitCompactRepresentativeSet K S Γ).image
    (continuous_fst.mul continuous_const)

theorem exists_uniform_balancedCleared_inverse_bound (M : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ y ∈ sUnitCompactRepresentativeSet K S Γ,
      ‖(balancedClearedTraceEquiv K S M y).symm.toContinuousLinearMap‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := exists_uniform_traceUnit_inverse_bound K
    (balancedClearedMixedSet K S Γ M) (isCompact_balancedClearedMixedSet K S Γ M)
  exact ⟨B, hB, fun y hy => hb _ (Set.mem_image_of_mem _ hy)⟩

variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
  (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
  (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)

/-- Original unsplit joint profile with only a compact parameter action.
The original Gamma, finite S coordinates and orbital radius are unchanged. -/
def balancedClearedJointTraceSchwartz (M : ℕ) (y : G) (ν : ℝ) (z₁ z₂ : Z)
    (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) : SchwartzMap W ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((traceProductEquiv K).trans
      ((balancedClearedTraceEquiv K S M y).prodCongr
        (balancedClearedTraceEquiv K S M y)))
    (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
      ψ hψ hψsupport ν z₁ z₂ φ R)

theorem clearedJointTraceSchwartz_scaled_apply (M : ℕ) (d : NZ)
    (ν : ℝ) (z₁ z₂ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r})
    (N : ℝ) (hN : 0 < N) (x : W) :
    clearedJointTraceSchwartz K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport
      M d ν z₁ z₂ φ R ((traceNormScale K N)⁻¹ • x) =
    balancedClearedJointTraceSchwartz K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport
      M (normalizedDivisorLocalPoint K S d) ν z₁ z₂ φ R
        ((traceNormScale K (N / (sIntegerElementNorm K S d).val))⁻¹ • x) := by
  change sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
    ψ hψ hψsupport ν z₁ z₂ φ R
    (((clearedDivisorTraceEquiv K S M d).prodCongr
      (clearedDivisorTraceEquiv K S M d))
      (traceProductEquiv K ((traceNormScale K N)⁻¹ • x))) =
    sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
      ψ hψ hψsupport ν z₁ z₂ φ R
      (((balancedClearedTraceEquiv K S M (normalizedDivisorLocalPoint K S d)).prodCongr
        (balancedClearedTraceEquiv K S M (normalizedDivisorLocalPoint K S d)))
        (traceProductEquiv K
          ((traceNormScale K (N / (sIntegerElementNorm K S d).val))⁻¹ • x)))
  rw [(traceProductEquiv K).map_smul, (traceProductEquiv K).map_smul]
  apply congrArg (sUnitMellinAnnularPartitionJointSchwartz K S Γ
    a ha a0 b0 ha0 haSupport ψ hψ hψsupport ν z₁ z₂ φ R)
  apply Prod.ext
  · exact clearedDivisorTraceEquiv_scaled_apply K S M d N hN (traceProductEquiv K x).1
  · exact clearedDivisorTraceEquiv_scaled_apply K S M d N hN (traceProductEquiv K x).2

/-- Termwise identity for the same true periodic weight and lattice. No
summability premise is needed for this pointwise coordinate transport. -/
theorem productPeriodicSum_cleared_eq_balanced (I : (Ideal (𝓞 K))⁰)
    (w : LatticeQuotient (ordinaryProductLattice K) (integralProductLattice K I) → ℂ)
    (M : ℕ) (d : NZ) (ν : ℝ) (z₁ z₂ : Z) (φ : SchwartzMap V ℂ)
    (R : {r : ℝ // 0 < r}) (N : ℝ) (hN : 0 < N) :
    productPeriodicSum K I w
      (clearedJointTraceSchwartz K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport
        M d ν z₁ z₂ φ R) N 0 =
    productPeriodicSum K I w
      (balancedClearedJointTraceSchwartz K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport
        M (normalizedDivisorLocalPoint K S d) ν z₁ z₂ φ R)
      (N / (sIntegerElementNorm K S d).val) 0 := by
  unfold productPeriodicSum
  apply tsum_congr
  intro l
  congr 1
  simpa only [zero_add] using clearedJointTraceSchwartz_scaled_apply K S Γ
    a ha a0 b0 ha0 haSupport ψ hψ hψsupport M d ν z₁ z₂ φ R N hN (l : W)

end HeckeGeneral.Analysis.ActualBalancedClearedJointDraft
