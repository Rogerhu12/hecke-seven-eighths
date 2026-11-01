import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.UniversalReflectionBranches
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ScheduleCompatibility

/-!
# Ordinary-reflection parameters in the original recipe schedule

The amplification and reserve are the preselected values of the original
moment mesh. We spend r/8 each on the fixed-conductor absorption, terminal
gap and dyadic rounding, r/4 on the Euler-product loss, and r/2 on the
finite-branch count. The actual reflection mass exponent is exactly r,
already inside the original edge loss r + mesh + r.

The original reserve definition gives the stronger inequality r≤sigma/100.
Consequently the outer core error 5r/8 fits sigma/16, and the comparison
error 3r/8 fits the existing boundary reserve r. No mesh, source geometry,
constant-selection order or final loss budget is changed.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open scoped Classical

/-- This is the literal first term in the existing minimum defining the
reserve, rather than a new choice of a smaller source mesh. -/
theorem sourceReserve_sharp_bound (ε : ℝ) :
    sourceReserve ε ≤ HeckePort.Schedule.amplification ε / 100 := by
  unfold sourceReserve HeckePort.Schedule.reserve
  exact min_le_left _ _

/-- The one positive Euler-product exponent is selected from the fixed
width-two and conductor-loss caps before any original row or scale. -/
def recipeReflectionEulerParameter (ε : ℝ) : ℝ :=
  (sourceReserve ε / 4) / (2 + sourceReserve ε / 8 + 1)

theorem recipeReflectionEulerParameter_pos {ε : ℝ} (hε : 0 < ε) :
    0 < recipeReflectionEulerParameter ε := by
  have hr := (moment_mesh_engine_bounds hε).2.1
  unfold recipeReflectionEulerParameter
  positivity

theorem recipeReflectionEulerParameter_budget {ε : ℝ} (hε : 0 < ε) :
    recipeReflectionEulerParameter ε * (2 + sourceReserve ε / 8) ≤ sourceReserve ε / 4 := by
  have hr := (moment_mesh_engine_bounds hε).2.1
  have hp := recipeReflectionEulerParameter_pos hε
  have hd : 0 < 2 + sourceReserve ε / 8 + 1 := by positivity
  calc
    _ ≤ recipeReflectionEulerParameter ε * (2 + sourceReserve ε / 8 + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hp.le
    _ = sourceReserve ε / 4 := div_mul_cancel₀ _ hd.ne'

/-- All supported child geometry uses these already available margins.
The variable overhead may be any genuine absorption exponent up to r/8. -/
theorem recipe_reflection_geometry_bounds {ε overhead : ℝ} (hε : 0 < ε)
    (hoverhead : overhead ≤ sourceReserve ε / 8) :
    overhead + sourceReserve ε / 8 + sourceReserve ε / 8 ≤ sourceReserve ε ∧
      (overhead + sourceReserve ε / 8) +
        (overhead + sourceReserve ε / 8 + sourceReserve ε / 8) ≤
          HeckePort.Schedule.amplification ε / 16 := by
  obtain ⟨hσ, hr, _⟩ := moment_mesh_engine_bounds hε
  have hsharp := sourceReserve_sharp_bound ε
  constructor <;> linarith

/-- The original width floor pays the positive-slot comparison margin
and the padded-core hypothesis in the genuine quarter reflection. -/
theorem recipe_reflection_comparison_floor {ε M : ℝ} (hε : 0 < ε)
    (hfloor : 16 * HeckePort.Schedule.amplification ε ≤ M) :
    sourceReserve ε ≤ M / 15 ∧ HeckePort.Schedule.amplification ε / 16 ≤ M / 4 := by
  have hσ := (moment_mesh_engine_bounds hε).1
  exact ⟨(moment_mesh_comparison_margins hε hfloor).2, by linarith⟩

/-- The complete reflected mass has exponent r. A whole-series or tail
terminal uses exponent zero, which also fits the original terminal loss. -/
theorem recipe_reflection_loss_bounds {ε : ℝ} (hε : 0 < ε) :
    sourceReserve ε / 2 + 2 * (sourceReserve ε / 4) = sourceReserve ε ∧
      sourceReserve ε ≤ sourceReserve ε + HeckePort.Schedule.momentMeshValue ε + sourceReserve ε ∧
      0 ≤ terminalBudget (16 * HeckePort.Schedule.amplification ε)
        (HeckePort.Schedule.amplification ε / 16) (HeckePort.Schedule.amplification ε)
        (sourceReserve ε) := by
  obtain ⟨hσ, hr, hm, _⟩ := moment_mesh_engine_bounds hε
  refine ⟨by ring, by linarith, ?_⟩
  unfold terminalBudget
  positivity

variable {K : Type} [Field K] [NumberField K]
variable [MeasurableSpace (ℕ × Bool)] [MeasurableSingletonClass (ℕ × Bool)]

/-- A single fixed scale threshold absorbs the actual conductor
constant and pays the same dyadic rounding exponent r/8. -/
theorem recipe_reflection_conductor_threshold {ε : ℝ} (hε : 0 < ε)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (ψ : HeckeCharacter K) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
      uniformReflectionConductorConstant S ψ ≤ U ^ (sourceReserve ε / 8) ∧
        2 ≤ U ^ (sourceReserve ε / 8) := by
  have hr := (moment_mesh_engine_bounds hε).2.1
  exact reflection_constant_threshold (uniformReflectionConductorConstant_pos S ψ)
    (by positivity) (by positivity)

/-- The actual uniform production theorem with every numerical input
instantiated from the unchanged recipe schedule. Its inferred proposition
retains the producer's full order: decay, finite child order, normalization
and required source order, profile constants, then the moving height,
primitive family, original node and scale. -/
def recipe_reflection_production
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (ω ψ : HeckeCharacter K) (cap : ℕ) {ε upper : ℝ}
    (hε : 0 < ε) (hupper : 2 ≤ upper) :=
  uniform_universalReflection_branches hcomplex ω ψ cap
    (HeckePort.Schedule.amplification ε) 2 (HeckePort.Schedule.amplification ε / 16)
    (sourceReserve ε / 8) 2 (sourceReserve ε / 4) 0
    (sourceReserve ε / 8) (sourceReserve ε / 8) (sourceReserve ε / 2)
    (1 / 8) (recipeReflectionEulerParameter ε) upper
    (moment_mesh_engine_bounds hε).1 (by norm_num)
    (by have h := (moment_mesh_engine_bounds hε).1; positivity)
    (by have h := (moment_mesh_engine_bounds hε).2.1; positivity) (by norm_num)
    (by have h := (moment_mesh_engine_bounds hε).2.1; positivity) (by norm_num)
    (by have h := (moment_mesh_engine_bounds hε).2.1; positivity)
    (by have h := (moment_mesh_engine_bounds hε).2.1; positivity)
    (by have h := (moment_mesh_engine_bounds hε).2.1; positivity)
    (by norm_num) (by norm_num) (recipeReflectionEulerParameter_pos hε)
    (recipeReflectionEulerParameter_budget hε) hupper

variable {ω ψ : HeckeCharacter K} {σ W : ℝ}
variable {PSystem : PolynomialSystem.{0} K ω ψ σ W} {parent : PSystem.Label}
variable {ε U C originalControl : ℝ}

/-- Insert the actually produced short reflection into the original
edge and terminal budgets. Only its already proved numerical exponents
are enlarged; the real kernel, children and remainder remain identical. -/
def ShortReflectionBranchAt.toRecipeBudget
    (out : ShortReflectionBranchAt (Ω := (ℕ × Bool) × ℝ) PSystem parent U (sourceReserve ε)
      (sourceReserve ε / 2 + 2 * (sourceReserve ε / 4)) (-2 * 0) C originalControl)
    (hε : 0 < ε) (hU : 1 ≤ U) (hC : 0 ≤ C) (hcontrol : 0 ≤ originalControl) :
    ShortReflectionBranchAt (Ω := (ℕ × Bool) × ℝ) PSystem parent U (sourceReserve ε)
      (sourceReserve ε + HeckePort.Schedule.momentMeshValue ε + sourceReserve ε)
      (terminalBudget (16 * HeckePort.Schedule.amplification ε)
        (HeckePort.Schedule.amplification ε / 16) (HeckePort.Schedule.amplification ε)
        (sourceReserve ε)) C originalControl where
  output := out.output
  terminal := out.terminal.trans <| mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hU
      (by simpa using (recipe_reflection_loss_bounds hε).2.2)) (mul_nonneg hC hcontrol)
  mass := out.mass.trans <| mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hU
      (by rw [(recipe_reflection_loss_bounds hε).1]
          exact (recipe_reflection_loss_bounds hε).2.1)) (mul_nonneg hC hcontrol)

/-- The same exact budget insertion covers both the genuine retained
outer reflection and its zero-kernel whole-series terminal branch. -/
def OuterReflectionBranchAt.toRecipeBudget
    (out : OuterReflectionBranchAt (Ω := (ℕ × Bool) × ℝ) PSystem parent U
      (HeckePort.Schedule.amplification ε / 16)
      (sourceReserve ε / 2 + 2 * (sourceReserve ε / 4)) (-2 * 0) C originalControl)
    (hε : 0 < ε) (hU : 1 ≤ U) (hC : 0 ≤ C) (hcontrol : 0 ≤ originalControl) :
    OuterReflectionBranchAt (Ω := (ℕ × Bool) × ℝ) PSystem parent U
      (HeckePort.Schedule.amplification ε / 16)
      (sourceReserve ε + HeckePort.Schedule.momentMeshValue ε + sourceReserve ε)
      (terminalBudget (16 * HeckePort.Schedule.amplification ε)
        (HeckePort.Schedule.amplification ε / 16) (HeckePort.Schedule.amplification ε)
        (sourceReserve ε)) C originalControl where
  output := out.output
  terminal := out.terminal.trans <| mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hU
      (by simpa using (recipe_reflection_loss_bounds hε).2.2)) (mul_nonneg hC hcontrol)
  mass := out.mass.trans <| mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hU
      (by rw [(recipe_reflection_loss_bounds hε).1]
          exact (recipe_reflection_loss_bounds hε).2.1)) (mul_nonneg hC hcontrol)

end HeckeSkeleton.Moments.EngineInduction
