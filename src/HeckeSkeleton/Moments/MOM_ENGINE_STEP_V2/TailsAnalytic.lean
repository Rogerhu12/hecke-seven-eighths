module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsPhase
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GaussPhaseTerminal

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Uniform analytic bounds for the two exact truncation differences

The only estimate selected here is the base uniform physical-source
Poisson bound. Its seminorms and constant precede every source, mask,
radius, cutoff, and moving Fourier phase. The actual finite tail masses
are left explicit for the separate original-source counting argument.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open EngineStep NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton.Global HeckePort.Moments
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar
  Expansion.ActualProbeContext.adeleSpace
  Expansion.ActualProbeContext.adeleBorel
  Expansion.ActualProbeContext.adeleMeasure_isAddHaar

/-- The actual uniform masked Poisson theorem, with the fixed arithmetic
data and row-ball test of the blueprint. -/
structure UniformEstimate (c : TargetContext K) (decay : ℝ) where
  orders : Finset (ℕ × ℕ)
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  bound : ∀ {ι κ : Type}
    (source : FirstFiniteSource K (Arithmetic.data c).Sf (Arithmetic.unitSubgroup c) ι κ),
    ‖(∑ i ∈ source.leftColumns, ∑ j ∈ source.rightColumns,
        (source.pairs i j).maskedSeries
          (sIntegerFiniteTestFunction K (Arithmetic.data c).Sf
            (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)) source.radius source.mask) -
      source.transform (Arithmetic.localMeasures (K := K)) (Arithmetic.different c)
        (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)‖ ≤
      coefficient * source.cutoff ^ (1 - decay) *
        ∑ i ∈ source.leftColumns, ∑ j ∈ source.rightColumns,
          orders.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
              (source.pairs i j).profile *
            (source.pairs i j).truncationMass source.mask source.radius

theorem exists_uniformEstimate (c : TargetContext K) (decay : ℝ) (hdecay : 1 < decay) :
    Nonempty (UniformEstimate c decay) := by
  let rank := Module.finrank ℤ (traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ))
  obtain ⟨order, horder⟩ :=
    exists_nat_gt (max (rank : ℝ) ((Module.finrank ℚ K : ℝ) * decay))
  have hrank : rank < order := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) horder)
  have hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ (order : ℝ) :=
    (lt_of_le_of_lt (le_max_right _ _) horder).le
  obtain ⟨orders, Ctail, hCtail, htail⟩ := finite_source_uniform_bound
    (K := K) (S := (Arithmetic.data c).Sf) (Γ := Arithmetic.unitSubgroup c)
    (Arithmetic.finiteMeasure (K := K)) (Arithmetic.localMeasures (K := K))
    (Arithmetic.fullMeasure (K := K)) (Arithmetic.different c)
    (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)
    (rowBallFiniteFamily_locallyConstant K (Arithmetic.data c).Sf 1)
    (rowBallFiniteFamily_compactSupport K (Arithmetic.data c).Sf 1)
    decay hdecay order hrank hdegree
  exact ⟨{
    orders := orders
    coefficient := Ctail
    coefficient_nonneg := hCtail
    bound := fun source => htail source }⟩

/-- The same uniform Poisson theorem for the first source's literal
divisor-dependent row cutoffs. -/
structure DivisorUniformEstimate (c : TargetContext K) (decay : ℝ) where
  orders : Finset (ℕ × ℕ)
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  bound : ∀ {ι κ : Type}
    (source : FirstFiniteSource K (Arithmetic.data c).Sf (Arithmetic.unitSubgroup c) ι κ),
    ‖(∑ i ∈ source.leftColumns, ∑ j ∈ source.rightColumns,
        (source.pairs i j).maskedSeries
          (sIntegerFiniteTestFunction K (Arithmetic.data c).Sf
            (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)) source.radius source.mask) -
      source.divisorTransform (Arithmetic.localMeasures (K := K)) (Arithmetic.different c)
        (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)‖ ≤
      coefficient * source.cutoff ^ (1 - decay) *
        ∑ i ∈ source.leftColumns, ∑ j ∈ source.rightColumns,
          orders.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
              (source.pairs i j).profile *
            (source.pairs i j).truncationMass source.mask source.radius

theorem exists_divisorUniformEstimate (c : TargetContext K)
    (decay : ℝ) (hdecay : 1 < decay) :
    Nonempty (DivisorUniformEstimate c decay) := by
  let rank := Module.finrank ℤ (traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ))
  obtain ⟨order, horder⟩ :=
    exists_nat_gt (max (rank : ℝ) ((Module.finrank ℚ K : ℝ) * decay))
  have hrank : rank < order := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) horder)
  have hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ (order : ℝ) :=
    (lt_of_le_of_lt (le_max_right _ _) horder).le
  obtain ⟨orders, Ctail, hCtail, htail⟩ := finite_source_divisor_uniform_bound
    (K := K) (S := (Arithmetic.data c).Sf) (Γ := Arithmetic.unitSubgroup c)
    (Arithmetic.finiteMeasure (K := K)) (Arithmetic.localMeasures (K := K))
    (Arithmetic.fullMeasure (K := K)) (Arithmetic.different c)
    (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)
    (rowBallFiniteFamily_locallyConstant K (Arithmetic.data c).Sf 1)
    (rowBallFiniteFamily_compactSupport K (Arithmetic.data c).Sf 1)
    decay hdecay order hrank hdegree
  exact ⟨{
    orders := orders
    coefficient := Ctail
    coefficient_nonneg := hCtail
    bound := fun source => htail source }⟩

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c} {decay : ℝ}

/-- The common-block mask in this formula is the actual finite-source
mask, including its principal common-prime factors. -/
theorem first_masked_tail_le (estimate : DivisorUniformEstimate c decay)
    (F : FirstPresentation call p) :
    F.tail ≤
      (F.source.fiber : ℝ) *
        (estimate.coefficient * (p.firstCutoff call) ^ (1 - decay) *
          F.source.tailCost estimate.orders) := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ v : F.source.CommonLabel,
        estimate.coefficient * (p.firstCutoff call) ^ (1 - decay) *
          ∑ i ∈ (F.source.source v).leftColumns,
            ∑ j ∈ (F.source.source v).rightColumns,
              estimate.orders.sup
                  (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
                  ((F.source.source v).pairs i j).profile *
                ((F.source.source v).pairs i j).truncationMass
                  (F.source.source v).mask F.source.radius :=
      Finset.sum_le_sum (fun v _ => estimate.bound (F.source.source v))
    _ = _ := by simp only [ActualDirectFirstSource.tailCost, Finset.mul_sum]

/-- The Gram phase has norm one and changes neither residue weights nor
moduli. Its actual tail mass is exactly the original one. -/
theorem phase_rawTailMass_eq (source : SecondSource call p) (x : ℝ)
    (orders : Finset (ℕ × ℕ)) :
    (source.phaseStage x).rawTailMass orders = source.stage.rawTailMass orders := by
  unfold ActualGaussStage.rawTailMass
  apply Finset.sum_congr rfl
  intro DE _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg₂ (fun a b : ℝ => a * b)
  · change orders.sup
      (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
        (((jointPhase x (source.physical.firstPoint i) * source.physical.source.coefficient i) *
          star (jointPhase x (source.physical.firstPoint j) *
            source.physical.source.coefficient j)) • source.stage.profile) =
      orders.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
        ((source.physical.source.coefficient i * star (source.physical.source.coefficient j)) •
          source.stage.profile)
    exact original_gram_seminorm_unit_multipliers orders _ _ _ _
      (norm_jointPhase x (source.physical.firstPoint i))
      (norm_jointPhase x (source.physical.firstPoint j)) source.stage.profile
  · rfl

theorem phase_tail_le (estimate : UniformEstimate c decay)
    (source : SecondSource call p) (x : ℝ) :
    source.phaseTail x ≤ estimate.coefficient * source.stage.cutoff ^ (1 - decay) *
      source.stage.rawTailMass estimate.orders := by
  calc
    _ ≤ ∑ DE : source.CommonLabel,
        estimate.coefficient * source.stage.cutoff ^ (1 - decay) *
          ∑ i ∈ ((source.phaseStage x).sources DE).leftColumns,
            ∑ j ∈ ((source.phaseStage x).sources DE).rightColumns,
              estimate.orders.sup
                  (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
                  (((source.phaseStage x).sources DE).pairs i j).profile *
                (((source.phaseStage x).sources DE).pairs i j).truncationMass
                  source.stage.mask source.stage.radius :=
      Finset.sum_le_sum (fun DE _ => estimate.bound ((source.phaseStage x).sources DE))
    _ = estimate.coefficient * source.stage.cutoff ^ (1 - decay) *
        (source.phaseStage x).rawTailMass estimate.orders := by
      simp only [ActualGaussStage.rawTailMass, Finset.mul_sum]
      rfl
    _ = _ := by rw [phase_rawTailMass_eq]

/-- Integrating the phase-bound pays the same first Fourier mass once. -/
theorem second_tail_le (estimate : UniformEstimate c decay)
    (source : SecondSource call p) :
    source.tail ≤ source.physical.outerWeight * (source.stage.fiber : ℝ) *
      ((actualFourierMeasure source.physical.firstKernel).real Set.univ *
        (estimate.coefficient * source.stage.cutoff ^ (1 - decay) *
          source.stage.rawTailMass estimate.orders)) := by
  letI := actualFourierMeasure_finite source.physical.firstKernel
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg source.physical.outerWeight_nonneg (Nat.cast_nonneg _))
  have h := integral_mono (phaseTail_integrable source)
    (integrable_const (estimate.coefficient * source.stage.cutoff ^ (1 - decay) *
      source.stage.rawTailMass estimate.orders))
    (fun x => phase_tail_le estimate source x)
  simpa only [integral_const, smul_eq_mul] using h

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.exists_uniformEstimate
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.exists_divisorUniformEstimate
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.first_masked_tail_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.phase_rawTailMass_eq
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.second_tail_le
