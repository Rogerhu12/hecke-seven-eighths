module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondZeroFactors
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondZeroNormalization

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The signed zero bound for every actual second source

The original residual divisor, Fourier measure, outer weight and orbital
fibre remain explicit. The actual coefficient, tuple and column-window
bounds pay both contributions of the signed zero. Empty rows, vanishing
original coefficients and nonsquarefree first divisors are treated before
using a positive norm window.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

theorem first_family_outer_eq_zero_of_not_squarefree
    (hfamily : family.Realizes) (i : Fin family.count)
    (hS : ¬Squarefree (family.source i).first.residualDivisor.val) :
    (family.source i).outerWeight = 0 := by
  rw [hfamily.residual i] at hS
  rw [hfamily.outer i]
  simp only [FirstCauchyKey.outer, UniqueFactorizationMonoid.moebius_of_not_squarefree hS,
    Int.cast_zero, norm_zero, mul_zero, zero_mul, zero_div]

theorem origin_outer_eq_zero_of_not_squarefree
    (hfamily : family.Realizes) (P : PoolPresentation family)
    (index : P.Index) (source : PhysicalSource call p)
    (hsource : P.Origin index source)
    (hS : ¬Squarefree source.first.residualDivisor.val) : source.outerWeight = 0 := by
  rcases index with ⟨i, tag⟩
  cases tag with
  | inl unit =>
    rcases hsource with ⟨htype, hsource, hancestor, hmultiplier, hkernel, hpoint, houter, hfirst⟩
    have hresidual : source.first.residualDivisor = (family.source i).first.residualDivisor :=
      congrArg (fun first => first.residualDivisor) hfirst
    rw [hresidual] at hS
    rw [houter, first_family_outer_eq_zero_of_not_squarefree hfamily i hS,
      zero_mul, zero_mul]
  | inr qe =>
    rcases hsource with ⟨htype, hsource, hancestor, hmultiplier, hkernel, hpoint, houter,
      hselected, hopposite, hcomplementary, hresidual, hfirstElement, hright, hpower,
      hretained, htag, hdeletion, hpaid⟩
    rw [hresidual] at hS
    rw [houter, first_family_outer_eq_zero_of_not_squarefree hfamily i hS,
      zero_mul, zero_mul]

theorem expansion_outer_eq_zero_of_not_squarefree
    (hfamily : family.Realizes) (expansion : PoolExpansion family)
    (hexpansion : expansion.Realizes) :
    ∀ i, ¬Squarefree (expansion.source i).first.residualDivisor.val →
      (expansion.source i).outerWeight = 0 := by
  cases expansion with
  | direct => exact first_family_outer_eq_zero_of_not_squarefree hfamily
  | pooled P count index source =>
    intro i hS
    exact origin_outer_eq_zero_of_not_squarefree hfamily P (index i) (source i)
      (hexpansion.2.2 i) hS

theorem source_zero_eq_zero_of_rows_empty (source : SecondSource call p)
    (hsource : source.Realizes) (hrows : ¬source.physical.source.rows.Nonempty) :
    source.zero = 0 := by
  have hempty : source.physical.source.rows = ∅ := Finset.not_nonempty_iff_eq_empty.mp hrows
  simp only [SecondSource.zero, hsource.fiber, PhysicalSource.orbitMultiplicity,
    hempty, Finset.image_empty, Finset.sup_empty, show (⊥ : ℕ) = 0 from rfl,
    Nat.cast_zero, mul_zero, zero_mul]

/-- The norm window applies only to genuinely active columns. Its two
upper endpoints control the actual ideal product used by square counting. -/
theorem source_product_norm_le (source : PhysicalSource call p)
    (windows : source.Windows)
    (ij : source.Column × source.Column)
    (hij : ij ∈ source.source.columns ×ˢ source.source.columns)
    (hi : source.source.coefficient ij.1 ≠ 0)
    (hj : source.source.coefficient ij.2 ≠ 0) :
    (Ideal.absNorm ((source.source.ideal ij.1).val *
      (source.source.ideal ij.2).val) : ℝ) ≤
        call.base ^ (2 * (sourceColumnExponent source + 4 * p.loss)) := by
  have hmem := Finset.mem_product.mp hij
  calc
    _ = (Arithmetic.data c).exteriorNorm (source.source.ideal ij.1) *
        (Arithmetic.data c).exteriorNorm (source.source.ideal ij.2) := by
      simp only [map_mul, Nat.cast_mul, SArithmeticData.exteriorNorm,
        DedekindZetaZeroFree.idealNorm]
    _ ≤ call.base ^ (sourceColumnExponent source + 4 * p.loss) *
        call.base ^ (sourceColumnExponent source + 4 * p.loss) :=
      mul_le_mul (windows.column_upper ij.1 hmem.1 hi)
        (windows.column_upper ij.2 hmem.2 hj)
        ((Arithmetic.data c).exteriorNorm_pos _).le
        (Real.rpow_nonneg (zero_lt_one.trans call.domain.scale).le _)
    _ = _ := by
      rw [← Real.rpow_add (zero_lt_one.trans call.domain.scale)]
      congr 1
      ring

/-- This is the remaining original mass of a second source. The first
Fourier measure and orbital fibre are both literal; the divisor saving
comes from the actual square-root ideal count. -/
def sourceZeroMass (source : PhysicalSource call p) : ℝ :=
  source.outerWeight * (source.orbitMultiplicity : ℝ) *
    (actualFourierMeasure source.firstKernel).real Set.univ *
      sourceSideAllowance source / (Ideal.absNorm source.first.residualDivisor.val : ℝ)

theorem sourceZeroMass_nonneg (source : PhysicalSource call p) :
    0 ≤ sourceZeroMass source := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact mul_nonneg
    (mul_nonneg (mul_nonneg source.outerWeight_nonneg (Nat.cast_nonneg _)) measureReal_nonneg)
    (Real.rpow_nonneg (zero_lt_one.trans call.domain.scale).le _)

/-- Constants are selected before the moving call and its actual source
trace. Only the fixed annulus threshold and original `(0,0)` seminorm
are needed from the profile input. The pool padding is retained exactly
until the single pool mass is summed. -/
theorem second_zero_local_estimate_uniform (c : TargetContext K) (p : SourceParameters c) :
    ∃ Cbound : ℝ, 0 < Cbound ∧
    ∀ (frame : SourceFrame) (call : Call c) (input : ProfileInput call),
    {(0, 0)} ⊆ input.orders → call.frame = frame →
    FirstZeroProof.uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤ call.base ^ p.loss →
    ∀ (trace : SourceTrace call p), trace.Realizes → ∀ i,
    (trace.second.source i).zero ≤
      Cbound * input.amplitude ^ (2 * (c.geometry.slots + 2)) *
        sourceZeroMass (trace.expansion.source i) *
        call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z) +
          (trace.expansion.source i).first.tag.padding (recipeInductionSigma c) +
          recipeInductionSigma c / 16 + 20 * p.loss) := by
  obtain ⟨Cstage, hCstage, hstage⟩ := second_source_zero_bound_uniform c p
    (2 * (c.geometry.slots + 2)) (secondCountingExponent p) (secondCountingExponent_pos p)
  obtain ⟨Cfactor, hCfactor, hfactorBound⟩ :=
    second_factor_multiplicity_uniform c p p.loss p.loss_pos
  refine ⟨8 * Cstage * Cfactor, by positivity, ?_⟩
  intro frame call input horders hframe hannulus trace htrace i
  let source := trace.second.source i
  let G := source.physical
  have hphysical : G = trace.expansion.source i := htrace.second.physical i
  have hsource : source.Realizes := htrace.second.stage i
  have windows : G.Windows := by
    rw [hphysical]
    exact htrace.poolWindows i
  have hZ : 0 < call.base := zero_lt_one.trans call.domain.scale
  have hresult_nonneg : 0 ≤ (8 * Cstage * Cfactor) *
      input.amplitude ^ (2 * (c.geometry.slots + 2)) * sourceZeroMass G *
      call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
        call.workingParameters.z) + G.first.tag.padding (recipeInductionSigma c) +
        recipeInductionSigma c / 16 + 20 * p.loss) := by
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (by positivity) (pow_nonneg (zero_le_one.trans input.amplitude_one_le) _))
      (sourceZeroMass_nonneg G)) (Real.rpow_nonneg hZ.le _)
  rw [← hphysical]
  change source.zero ≤ _
  by_cases hrows : G.source.rows.Nonempty
  swap
  · rw [source_zero_eq_zero_of_rows_empty source hsource hrows]
    exact hresult_nonneg
  by_cases hS : Squarefree G.first.residualDivisor.val
  swap
  · have houter : G.outerWeight = 0 := by
      rw [hphysical]
      exact expansion_outer_eq_zero_of_not_squarefree htrace.cauchy trace.expansion
        htrace.expansion i (by simpa only [hphysical] using hS)
    have hz : source.zero = 0 := by
      change G.outerWeight * _ * _ = 0
      rw [houter, zero_mul, zero_mul]
    rw [hz]
    exact hresult_nonneg
  have hactualFactors := expansion_actual_factors htrace.first htrace.cauchy
    trace.expansion htrace.expansion i
  rw [← hphysical] at hactualFactors
  obtain ⟨factors, hproduct, hfiber⟩ := hactualFactors
  have hdiv : ∀ j ∈ G.source.columns, G.source.coefficient j ≠ 0 →
      G.first.residualDivisor.val ∣ (G.source.ideal j).val := by
    have h := expansion_coefficient_divisor htrace.cauchy trace.expansion htrace.expansion i
    rw [← hphysical] at h
    exact h hrows
  by_cases hactive : ∃ j ∈ G.source.columns, G.source.coefficient j ≠ 0
  swap
  · have hcoeffzero (j) (hj : j ∈ G.source.columns) : G.source.coefficient j = 0 := by
      by_contra hnz
      exact hactive ⟨j, hj, hnz⟩
    have hz := hstage source hsource factors (secondFactorMultiplicity G) hfiber hproduct
      hS hdiv 1 1 0 (by norm_num) (by norm_num) (by norm_num)
      (fun ij hij hnz _ => False.elim (hnz (hcoeffzero ij.1 (Finset.mem_product.mp hij).1)))
      (fun j hj hnz => False.elim (hnz (hcoeffzero j hj)))
      (fun j hj => by rw [hcoeffzero j hj, norm_zero, zero_mul])
    have hz' : source.zero ≤ 0 := by
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul, zero_div] using hz
    exact hz'.trans hresult_nonneg
  let Camp := 2 * input.amplitude ^ (c.geometry.slots + 2)
  let A := call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z
  let a := sourceColumnExponent G
  let N := call.base ^ (2 * (a + 4 * p.loss))
  let L := call.base ^ (a - 4 * p.loss)
  let B := Camp * call.base ^ (-A / 2) * call.base ^ (3 * p.tilt)
  let R := G.first.retainedScale * call.base ^ G.enlargement / L + 1
  let mass := G.outerWeight * (G.orbitMultiplicity : ℝ) *
    (actualFourierMeasure G.firstKernel).real Set.univ
  let S := (Ideal.absNorm G.first.residualDivisor.val : ℝ)
  let E := -A + G.first.tag.padding (recipeInductionSigma c) +
    recipeInductionSigma c / 16 + 18 * p.loss
  have hmass : 0 ≤ mass :=
    mul_nonneg (mul_nonneg G.outerWeight_nonneg (Nat.cast_nonneg _)) measureReal_nonneg
  have hSpos : 0 < S := by
    change (0 : ℝ) < (Ideal.absNorm G.first.residualDivisor.val : ℝ)
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors G.first.residualDivisor
  have hallowance : 0 ≤ sourceSideAllowance G := Real.rpow_nonneg hZ.le _
  have hN : 1 ≤ N := source_product_window_one_le G windows hactive
  have hL : 0 < L := Real.rpow_pos_of_pos hZ _
  have hB : 0 ≤ B := by
    dsimp only [B, Camp]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (pow_nonneg (zero_le_one.trans input.amplitude_one_le) _)) (Real.rpow_nonneg hZ.le _))
      (Real.rpow_nonneg hZ.le _)
  have hR : 0 ≤ R := add_nonneg
    (div_nonneg (mul_nonneg G.first.retainedScale_pos.le (Real.rpow_nonneg hZ.le _)) hL.le)
    zero_le_one
  have hT : A + p.loss ≤ (3 : ℝ) := by
    have ht := second_total_window_le_three p call
    dsimp only [A]
    linarith [p.loss_pos]
  have hcoefficient : ∀ j ∈ G.source.columns,
      ‖G.source.coefficient j‖ * (Arithmetic.data c).exteriorNorm (G.source.ideal j) ≤ B := by
    have hfirst : ∀ j, ∀ k ∈ (trace.cauchy.source j).source.columns,
        ‖(trace.cauchy.source j).source.coefficient k‖ *
          (Arithmetic.data c).exteriorNorm ((trace.cauchy.source j).source.ideal k) ≤ B :=
      fun j => first_family_weighted_coefficient_bound htrace.first htrace.cauchy
        frame input horders hframe hannulus 3 hT j
    have h := expansion_weighted_coefficient_bound trace.expansion htrace.expansion B hfirst i
    rw [← hphysical] at h
    exact h
  have hlocal := hstage source hsource factors (secondFactorMultiplicity G) hfiber hproduct
    hS hdiv N L B hN hL hB (source_product_norm_le G windows)
    (fun j hj hnz => windows.column_lower j hj hnz) hcoefficient
  have hmult : (secondFactorMultiplicity G : ℝ) ≤ Cfactor * call.base ^ p.loss :=
    hfactorBound G (source_selected_norm_le_cube G windows hactive)
  have hscalar : B ^ 2 * R * Real.sqrt N ≤
      2 * Camp ^ 2 * sourceSideAllowance G * call.base ^ E :=
    source_signed_scalar_le_allowance G windows hrows Camp
  have hcount : N ^ secondCountingExponent p ≤ call.base ^ p.loss :=
    second_counting_power_le p call.base a call.domain.scale.le
      (source_column_exponent_le_three G)
  have hscalar_nonneg : 0 ≤ B ^ 2 * R * Real.sqrt N :=
    mul_nonneg (mul_nonneg (sq_nonneg B) hR) (Real.sqrt_nonneg N)
  have hscalar_bound_nonneg : 0 ≤ 2 * Camp ^ 2 * sourceSideAllowance G * call.base ^ E :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Camp)) hallowance)
      (Real.rpow_nonneg hZ.le _)
  have hmult_bound_nonneg : 0 ≤ Cfactor * call.base ^ p.loss :=
    mul_nonneg hCfactor.le (Real.rpow_nonneg hZ.le _)
  have hcount_nonneg : 0 ≤ N ^ secondCountingExponent p :=
    Real.rpow_nonneg (zero_le_one.trans hN) _
  have hpay : (secondFactorMultiplicity G : ℝ) * (B ^ 2 * R * Real.sqrt N) *
      N ^ secondCountingExponent p ≤
      (Cfactor * call.base ^ p.loss) *
        (2 * Camp ^ 2 * sourceSideAllowance G * call.base ^ E) * call.base ^ p.loss := by
    calc
      _ ≤ (Cfactor * call.base ^ p.loss) * (B ^ 2 * R * Real.sqrt N) *
          N ^ secondCountingExponent p :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hmult hscalar_nonneg) hcount_nonneg
      _ ≤ (Cfactor * call.base ^ p.loss) *
          (2 * Camp ^ 2 * sourceSideAllowance G * call.base ^ E) *
            N ^ secondCountingExponent p :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hscalar hmult_bound_nonneg) hcount_nonneg
      _ ≤ _ := mul_le_mul_of_nonneg_left hcount
        (mul_nonneg hmult_bound_nonneg hscalar_bound_nonneg)
  have hcamp : Camp ^ 2 = 4 * input.amplitude ^ (2 * (c.geometry.slots + 2)) := by
    dsimp only [Camp]
    rw [mul_pow, ← pow_mul, Nat.mul_comm (c.geometry.slots + 2) 2]
    norm_num
  have hpowers : call.base ^ p.loss * call.base ^ E * call.base ^ p.loss =
      call.base ^ (-A + G.first.tag.padding (recipeInductionSigma c) +
        recipeInductionSigma c / 16 + 20 * p.loss) := by
    rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
    congr 1
    dsimp only [E]
    ring
  calc
    source.zero ≤ mass * (Cstage *
        ((secondFactorMultiplicity G : ℝ) * (B ^ 2 * R * Real.sqrt N) *
          N ^ secondCountingExponent p) / S) := by
      convert hlocal using 1 <;> dsimp only [mass, R, S] <;> ring
    _ ≤ mass * (Cstage * ((Cfactor * call.base ^ p.loss) *
        (2 * Camp ^ 2 * sourceSideAllowance G * call.base ^ E) * call.base ^ p.loss) / S) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpay hCstage.le) hSpos.le) hmass
    _ = (8 * Cstage * Cfactor) * input.amplitude ^ (2 * (c.geometry.slots + 2)) *
        sourceZeroMass G * (call.base ^ p.loss * call.base ^ E * call.base ^ p.loss) := by
      rw [hcamp]
      dsimp only [sourceZeroMass, mass, S]
      ring
    _ = _ := by rw [hpowers]

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof
