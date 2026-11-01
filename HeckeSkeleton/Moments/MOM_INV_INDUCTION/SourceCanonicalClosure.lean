import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderShortBound
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderUniformMarks
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceUnmarkedComplete

/-!
# Canonical induction for the literal arithmetic source

The two primitive sieve inputs construct the reflected input for the
fixed actual period inventory. The proved short-completion estimate and
the two proved provider steps then close the finite backwards induction.
All constants precede the base, the residual total mark length, and every
original node. The unmarked all-smaller-scale estimate uses this bound
with the actual zero-slot data and the complete original ideal rows.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

universe u

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceCanonicalClosure

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.UniformAmplify
open HeckeSkeleton.Moments.MOM_INV_STEP
open HeckeSkeleton.LowEnergy.ActualSieveDictionary
open SourceActualArithmetic ProviderNodes
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

local notation "S" => excludedPlaces K c
local notation "Sset" => places K c
local notation "P" => probeData K c
local notation "D" => (probeData K c).arithmetic
local notation "Γ" => sixthPowerSUnitSubgroup K Sset
local notation "Θ" => twists K c
local notation "ψ" => targetCharacter K c

attribute [local instance] Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar
  Expansion.ActualProbeContext.adeleSpace
  Expansion.ActualProbeContext.adeleBorel
  Expansion.ActualProbeContext.adeleMeasure_isAddHaar

local instance normOneSpace : MeasurableSpace (sLocalNormOneGroup K Sset) :=
  (probeMeasures K c).normOneSpace

local instance normOneBorel : BorelSpace (sLocalNormOneGroup K Sset) :=
  (probeMeasures K c).normOneBorel

local instance principal : IsPrincipalIdealRing (Set.integer Sset K) :=
  (axiomChoice K c).C.principal

/-- One actual canonical estimate for every residual mark length in a
fixed bounded interval. The seminorm, scalar and threshold are selected
before that length, as required by the original marked Fourier source. -/
theorem exists_uniform_canonical_bound
    (hquadratic : ExteriorQuadraticBound K Sset D)
    (hcubic : ExteriorCubicBound K Sset D)
    (slotCap : ℕ) (Fmax Mmax margin zMax lo hi loss : ℝ)
    (hmargin : 0 < margin) (hzMax : 0 ≤ zMax)
    (hlo : 0 < lo) (hhi : lo ≤ hi) (hloss : 0 < loss) :
    ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 1 ≤ C ∧ 2 ≤ Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ∀ z : ℝ, 0 ≤ z → z ≤ zMax →
        UniformBound.{u} («Γ» := Γ) («Θ» := Θ) («ψ» := ψ) D (P).Lambda (P).G slotCap
          Z Fmax margin z lo hi loss Mmax C q := by
  obtain ⟨b, hstep⟩ := exists_terminal_descentBudget Mmax margin (2 * loss) hmargin (by positivity)
  let A := max (max 1 (stageCapacity Fmax b.eta b.depth)) (max b.tau zMax)
  have hA : 1 ≤ A := (le_max_left _ _).trans (le_max_left _ _)
  have hcapacity : max 1 (stageCapacity Fmax b.eta b.depth) ≤ A := le_max_left _ _
  have htau : b.tau ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hzA : zMax ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hE := reflected_input K c hquadratic hcubic
  obtain ⟨qShort, CShort, ZShort, hCShort, hZShort, hshort⟩ :=
    TerminalShort.exists_uniform_short_contribution K S D Γ Θ ψ (allowedGenerators K c)
      (P).Lambda (P).G (reflectionFamily K c) hE slotCap A (margin / 2) lo hi hA
      (by positivity) hlo hhi
  have hs : ∀ z : ℝ, 0 ≤ z → z ≤ zMax →
      ∀ {σ : Type u} (Z Fcap cStage : ℝ) (x : Node K S Γ Θ ψ σ),
      ZShort ≤ Z → Fcap ≤ A → margin / 2 ≤ cStage →
      x.Admissible D (P).Lambda (P).G slotCap Z Fcap cStage z lo hi → x.labelLength < b.step →
      TerminalNodes.shortEnergy K S Γ D slotCap x (Z ^ b.step) ≤
        CShort * (qShort.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 * Z ^ x.totalLength := by
    intro z hz hzz σ Z Fcap cStage x hZ hF hc hx hsmall
    exact hshort b.step z b.step_pos hstep hz (hzz.trans hzA)
      Z Fcap cStage x hZ hF hc hx hsmall
  obtain ⟨q, C, Z₀, hC, hZ₀, hb⟩ :=
    ProviderUniformMarks.exists_uniform_bound_of_short_contribution_uniform_marks
      (K := K) («S» := S) («Γ» := Γ) («Θ» := Θ) («ψ» := ψ)
      («D» := D) (Λ := (P).Lambda) (G := (P).G) (slotCap := slotCap)
      (hΓ := le_rfl) (hallowed := allowedGenerators K c)
      (μv := Expansion.ActualProbeContext.allLocalMeasures K)
      (ν := Expansion.ActualProbeContext.finiteAdeleMeasure K)
      (μ := Expansion.ActualProbeContext.adeleMeasure K)
      (calibration_mem K c) b hmargin Fmax A zMax lo hi hA hcapacity htau hzMax
      qShort CShort ZShort (zero_le_one.trans hCShort) hs
  refine ⟨q, C, Z₀, hC, hZ₀, ?_⟩
  intro Z hZ z hz hzz σ x hx hr
  simpa only [show (2 * loss) / 2 = loss by ring] using hb Z hZ z hz hzz x hx hr

/-- The strict seed is now discharged from the original two sieve
inputs. Its rowwise majorant controls every smaller source scale with
the original complete ideal rows and original recipe profiles. -/
theorem actual_complete_unmarked_scale_sup
    (hquadratic : ExteriorQuadraticBound K Sset D)
    (hcubic : ExteriorCubicBound K Sset D) :
    CompleteUnmarkedScaleSupBound
      (recipeMomentModels K c (expansionRecipeRaw K c)).unmarked := by
  apply SourceUnmarkedComplete.strict_seed_of_canonical_uniform K c
  intro margin loss hmargin hloss
  obtain ⟨q, C, Z₀, hC, hZ₀, hb⟩ := exists_uniform_canonical_bound.{0} K c hquadratic hcubic
    0 1 1 margin 0 1 2 loss hmargin le_rfl (by norm_num) (by norm_num) hloss
  exact ⟨q, C, Z₀, hC, hZ₀, fun Z hZ => hb Z hZ 0 le_rfl le_rfl⟩

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceCanonicalClosure

end
