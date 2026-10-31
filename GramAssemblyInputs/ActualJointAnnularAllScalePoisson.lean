import ActualFixedDepthAllScalePoisson
import HeckeGeneral.Analysis.SUnitMellinFourierBounds
import HeckeGeneral.Analysis.SIntegerAnnularSexticCosets

/-!
UNCOMPILED / native 0. A direct actual-profile consumer of the all-scale
fixed-depth periodic-sum estimate. The input is the original joint orbital
Schwartz kernel with its original total Mellin phase and both finite S
coordinates. Fixed bounded support and origin vanishing are proved from the
constructed unit partition; they are not additional mathematical inputs.

The only coordinate transport is the actual Hilbert-product equivalence.
This does not yet identify an entire S-integer divisor sum with the periodic
sum or bound the remaining Schwartz seminorms uniformly in moving inputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Analysis.ActualJointAnnularAllScaleDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open AlgebraicNumberTheory.PowerResidueSymbols
open ActualGramJointMeanDraft ActualGramJointChartDraft ActualGramJointChartCoverDraft
open ActualGramCoefficientBoundDraft ActualGramPeriodNormDraft
open ActualMeanZeroProductPoissonDraft ActualFixedDepthAllScaleDraft
open scoped Classical BigOperators ContDiff FourierTransform nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => traceProductSpace K
local notation "Z" => SFiniteLocalGroup K S

variable (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
  (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
  (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)

/-- Literal pullback of the original unsplit joint profile to the actual
Hilbert product used by the product-lattice Poisson theorem. -/
def actualJointAnnularTraceSchwartz
    (ν : ℝ) (z₁ z₂ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) :
    SchwartzMap W ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (traceProductEquiv K)
    (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
      ψ hψ hψsupport ν z₁ z₂ φ R)

@[simp] theorem actualJointAnnularTraceSchwartz_apply
    (ν : ℝ) (z₁ z₂ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) (x : W) :
    actualJointAnnularTraceSchwartz K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ν z₁ z₂ φ R x =
      sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ν z₁ z₂ φ R (traceProductEquiv K x) := rfl

/-- The real annular factors kill the origin even if S is empty. -/
theorem actualJointAnnularTraceSchwartz_zero
    (ν : ℝ) (z₁ z₂ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) :
    actualJointAnnularTraceSchwartz K S Γ a ha a0 b0 ha0 haSupport
      ψ hψ hψsupport ν z₁ z₂ φ R 0 = 0 := by
  rw [actualJointAnnularTraceSchwartz_apply, map_zero,
    sUnitMellinAnnularPartitionJointSchwartz_apply]
  simp only [sUnitAnnularPartitionJointCutoff, Prod.fst_zero, Prod.snd_zero,
    sUnitAnnularPartitionCutoff_origin, zero_mul, Complex.ofReal_zero, mul_zero]

/-- A single radius is chosen before frequency, both finite S fibers,
the Schwartz input and the orbital radius. -/
theorem exists_actualJointAnnularTraceSchwartz_support_radius :
    ∃ B : ℝ, 0 < B ∧ ∀ (ν : ℝ) (z₁ z₂ : Z) (φ : SchwartzMap V ℂ)
      (R : {r : ℝ // 0 < r}) (x : W),
      actualJointAnnularTraceSchwartz K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ν z₁ z₂ φ R x ≠ 0 → ‖x‖ ≤ B := by
  let E := sUnitAnnularPartitionEnclosure K S Γ a0 b0
  have hE : IsCompact E := isCompact_sUnitAnnularPartitionEnclosure K S Γ a0 b0 ha0
  have hcompact : IsCompact ((traceProductEquiv K).symm '' (E ×ˢ E)) :=
    (hE.prod hE).image (traceProductEquiv K).symm.continuous
  obtain ⟨B, hB⟩ := hcompact.isBounded.subset_closedBall (0 : W)
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro ν z₁ z₂ φ R x hx
  rw [actualJointAnnularTraceSchwartz_apply,
    sUnitMellinAnnularPartitionJointSchwartz_apply] at hx
  have hcut := (mul_ne_zero_iff.mp ((mul_ne_zero_iff.mp hx).2)).1
  have hreal : sUnitAnnularPartitionCutoff K S Γ a z₁ (traceProductEquiv K x).1 *
      sUnitAnnularPartitionCutoff K S Γ a z₂ (traceProductEquiv K x).2 ≠ 0 := by
    intro hzero
    exact hcut (by simp only [sUnitAnnularPartitionJointCutoff, hzero, Complex.ofReal_zero])
  have h1 := support_sUnitAnnularPartitionCutoff_subset_enclosure K S Γ a z₁
    a0 b0 ha0 haSupport (mul_ne_zero_iff.mp hreal).1
  have h2 := support_sUnitAnnularPartitionCutoff_subset_enclosure K S Γ a z₂
    a0 b0 ha0 haSupport (mul_ne_zero_iff.mp hreal).2
  have hximage : x ∈ (traceProductEquiv K).symm '' (E ×ˢ E) :=
    ⟨traceProductEquiv K x, ⟨h1, h2⟩, (traceProductEquiv K).symm_apply_apply x⟩
  have hxB : ‖x‖ ≤ B := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hB hximage
  exact hxB.trans (le_max_right _ _)

variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "NZ" => NonzeroRingElements (S.integer K)
local notation "H" => finiteIndexSUnitBoxWidth K S Γ
local notation "N₀" => H + H
local notation:max "F" ν:max z₁:max z₂:max φ:max R:max =>
  actualJointAnnularTraceSchwartz K S Γ a ha a0 b0 ha0 haSupport
    ψ hψ hψsupport ν z₁ z₂ φ R

/-- Direct consumer for the original actual joint profile. Constants precede
the moving ideals, centers, finite S coordinates, frequency and both scales.
Nonexceptionality supplies the actual proved mean zero, not an estimate input. -/
theorem exists_actualJointAnnular_fixedDepth_allScale_min_bound
    (A : ℕ) (hA : 2 < A) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (c k : NZ)
      (a₁ a₂ : 𝓞 K ⧸ clearedSModulus K S ζ hζ N₀) (d b₁ b₂ : NZ)
      (p : jointPlaces K (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
        (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)),
      (¬ p.val.asIdeal ∣ actualFrequencyIdeal K S c) →
      (¬ 6 ∣ idealPrimeMultiplicity K p.val (actualFrequencyIdeal K S k)) →
      ∀ (ν : ℝ) (z₁ z₂ : Z) (φ : SchwartzMap V ℂ)
        (R : {r : ℝ // 0 < r}) (N : ℝ), 0 < N →
      ‖productPeriodicSum K (fixedChartPeriodIdeal K S ζ hζ c k N₀)
        (fixedChartLatticeWeight K S ζ hζ σ hS6 c k N₀ H a₁ a₂ d b₁ b₂)
        (F ν z₁ z₂ φ R) N 0‖ ≤
      C₀ * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
        (SchwartzMap.seminorm ℂ 0 0 (F ν z₁ z₂ φ R) +
          SchwartzMap.seminorm ℂ (Module.finrank ℚ K * A) 0 (𝓕 (F ν z₁ z₂ φ R))) *
        N ^ 2 * min 1 ((((Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
          (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) / N) ^ A) := by
  obtain ⟨B, hB, hsupp⟩ := exists_actualJointAnnularTraceSchwartz_support_radius K S Γ
    a ha a0 b0 ha0 haSupport ψ hψ hψsupport
  obtain ⟨C₀, hC₀, hbound⟩ := exists_uniform_fixedDepth_weight_allScale_min_bound
    K S Γ ζ hζ σ hS6 B hB A hA
  refine ⟨C₀, hC₀, ?_⟩
  intro c k a₁ a₂ d b₁ b₂ p hpC hpJ ν z₁ z₂ φ R N hN
  exact hbound c k a₁ a₂ d b₁ b₂ p hpC hpJ (F ν z₁ z₂ φ R) N hN
    (actualJointAnnularTraceSchwartz_zero K S Γ a ha a0 b0 ha0 haSupport
      ψ hψ hψsupport ν z₁ z₂ φ R)
    (hsupp ν z₁ z₂ φ R)

end HeckeGeneral.Analysis.ActualJointAnnularAllScaleDraft
