import SchwartzLinearCompositionSeminorm
import ActualBalancedClearedJointTransport
import Mathlib.Analysis.Normed.Operator.Prod

/-!
UNCOMPILED / native 0. Uniform linear-composition constants for the actual
balanced divisor family, with fixed D^M. The original joint profile,
Gamma, finite S coordinates, nu and orbital radius remain literal.
No moving-profile frequency or small/large-radius estimate is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeGeneral.Analysis.ActualBalancedJointSeminormDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open ActualGramFixedDenominatorDraft ActualBalancedClearedJointDraft
open SchwartzLinearCompositionDraft
open scoped Classical BigOperators ContDiff nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "NZ" => NonzeroRingElements (S.integer K)
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => traceProductSpace K
local notation "U" => (mixedEmbedding.mixedSpace K)ˣ
local notation "G" => sLocalMultiplicativeGroup K S
local notation "Z" => SFiniteLocalGroup K S

/-- The forward family is the actual multiplication CLM conjugated by the
trace model, so its operator-norm continuity is proved directly. -/
theorem traceUnitMulEquiv_forwardCLM (u : U) :
    (traceUnitMulEquiv K u).toContinuousLinearMap =
      (traceToMixed K).symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.mul ℝ (mixedEmbedding.mixedSpace K) (u : mixedEmbedding.mixedSpace K)).comp
          (traceToMixed K).toContinuousLinearMap) := by
  ext x
  rfl

theorem continuous_traceUnitMulEquiv_forwardCLM :
    Continuous (fun u : U => (traceUnitMulEquiv K u).toContinuousLinearMap) := by
  simp_rw [traceUnitMulEquiv_forwardCLM]
  exact continuous_const.clm_comp
    (((ContinuousLinearMap.mul ℝ (mixedEmbedding.mixedSpace K)).continuous.comp
      Units.continuous_val).clm_comp continuous_const)

def balancedJointCoordinateEquiv (M : ℕ) (y : G) : W ≃L[ℝ] (V × V) :=
  (traceProductEquiv K).trans
    ((balancedClearedTraceEquiv K S M y).prodCongr (balancedClearedTraceEquiv K S M y))

theorem continuous_balancedJointCoordinate_forwardCLM (M : ℕ) :
    Continuous (fun y : G => (balancedJointCoordinateEquiv K S M y).toContinuousLinearMap) := by
  have hp : Continuous (balancedClearedMixedUnit K S M) :=
    continuous_fst.mul continuous_const
  have he : Continuous (fun y : G => (balancedClearedTraceEquiv K S M y).toContinuousLinearMap) :=
    (continuous_traceUnitMulEquiv_forwardCLM K).comp hp
  change Continuous (fun y : G =>
    ((balancedClearedTraceEquiv K S M y).prodCongr
      (balancedClearedTraceEquiv K S M y)).toContinuousLinearMap.comp
        (traceProductEquiv K).toContinuousLinearMap)
  exact (Continuous.prod_map_equivL ℝ he he).clm_comp continuous_const

theorem continuous_balancedJointCoordinate_inverseCLM (M : ℕ) :
    Continuous (fun y : G => (balancedJointCoordinateEquiv K S M y).symm.toContinuousLinearMap) := by
  have hp : Continuous (balancedClearedMixedUnit K S M) :=
    continuous_fst.mul continuous_const
  have hi : Continuous (fun y : G =>
      (balancedClearedTraceEquiv K S M y).symm.toContinuousLinearMap) :=
    (continuous_traceUnitMulEquiv_inverseCLM K).comp hp
  change Continuous (fun y : G => (traceProductEquiv K).symm.toContinuousLinearMap.comp
    ((balancedClearedTraceEquiv K S M y).symm.prodCongr
      (balancedClearedTraceEquiv K S M y).symm).toContinuousLinearMap)
  exact continuous_const.clm_comp (Continuous.prod_map_equivL ℝ hi hi)

variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

/-- The constants precede the normalized divisor and the Schwartz function.
Both operator continuities and actual compactness are discharged here. -/
theorem exists_balancedJoint_comp_seminorm_bound (M k n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ y ∈ sUnitCompactRepresentativeSet K S Γ,
      ∀ f : SchwartzMap (V × V) ℂ,
        SchwartzMap.seminorm ℂ k n
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (balancedJointCoordinateEquiv K S M y) f) ≤
          B * SchwartzMap.seminorm ℂ k n f :=
  exists_compact_family_seminorm_bound
    (sUnitCompactRepresentativeSet K S Γ) (isCompact_sUnitCompactRepresentativeSet K S Γ)
    (balancedJointCoordinateEquiv K S M)
    (continuous_balancedJointCoordinate_forwardCLM K S M)
    (continuous_balancedJointCoordinate_inverseCLM K S M) k n

variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
  (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
  (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)

/-- Specialization to the original unsplit actual profile, with no estimate
of that profile substituted for its genuine input seminorm. -/
theorem exists_balancedJoint_profile_seminorm_bound (M k n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ y ∈ sUnitCompactRepresentativeSet K S Γ,
      ∀ ν : ℝ, ∀ z₁ z₂ : Z, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r},
        SchwartzMap.seminorm ℂ k n
          (balancedClearedJointTraceSchwartz K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport
            M y ν z₁ z₂ φ R) ≤
          B * SchwartzMap.seminorm ℂ k n
            (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
              ψ hψ hψsupport ν z₁ z₂ φ R) := by
  obtain ⟨B, hB, hb⟩ := exists_balancedJoint_comp_seminorm_bound K S Γ M k n
  exact ⟨B, hB, fun y hy ν z₁ z₂ φ R => hb y hy _⟩

/-- The same original-Gamma representative gives the compact parameter,
the actual H-box and fixed D^H clearing, followed by the uniform estimate.
The constant is chosen before d, nu, both finite fibers, phi and R. -/
theorem exists_originalSubgroup_fixedDenominator_profile_seminorm_bound (k n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ d : NZ, ∃ u : Γ,
      let d' := sIntegerOrbitTranslate K S Γ u d
      normalizedDivisorLocalPoint K S d' ∈ sUnitCompactRepresentativeSet K S Γ ∧
      (sLocalNonzeroIntegerDiagonal K S d').2 ∈
        finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ) ∧
      (∃ z : 𝓞 K, algebraMap (𝓞 K) (S.integer K)
          (finiteSIntegerDenominator K S ^ finiteIndexSUnitBoxWidth K S Γ) * d'.val =
        algebraMap (𝓞 K) (S.integer K) z) ∧
      (∀ m : NZ, (sLocalNonzeroIntegerDiagonal K S (sIntegerNonzeroMul K S d' m)).2 ∈
          finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ) →
        ∃ z : 𝓞 K, algebraMap (𝓞 K) (S.integer K)
            (finiteSIntegerDenominator K S ^ finiteIndexSUnitBoxWidth K S Γ) * m.val =
          algebraMap (𝓞 K) (S.integer K) z) ∧
      ∀ ν : ℝ, ∀ z₁ z₂ : Z, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r},
        SchwartzMap.seminorm ℂ k n
          (balancedClearedJointTraceSchwartz K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport
            (finiteIndexSUnitBoxWidth K S Γ) (normalizedDivisorLocalPoint K S d') ν z₁ z₂ φ R) ≤
          B * SchwartzMap.seminorm ℂ k n
            (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
              ψ hψ hψsupport ν z₁ z₂ φ R) := by
  obtain ⟨B, hB, hb⟩ := exists_balancedJoint_profile_seminorm_bound K S Γ
    a ha a0 b0 ha0 haSupport ψ hψ hψsupport (finiteIndexSUnitBoxWidth K S Γ) k n
  refine ⟨B, hB, fun d => ?_⟩
  obtain ⟨u, hc, hbox, hclear, hcolumns⟩ := exists_compact_divisor_with_fixed_denominator K S Γ d
  exact ⟨u, hc, hbox, hclear, hcolumns, fun ν z₁ z₂ φ R => hb _ hc ν z₁ z₂ φ R⟩

end HeckeGeneral.Analysis.ActualBalancedJointSeminormDraft
