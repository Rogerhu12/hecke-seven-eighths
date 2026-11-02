import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsSecondGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsCauchyCoefficients

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Literal size transport through the single pool

Main columns are the original columns. Every error column is an actual
valuation subtype, with its original coefficient multiplied by the
explicit prime power and a unit complex phase. The finite row and column
counts below therefore follow from images and subtypes of the original
carriers.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton.Global HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

section OriginalPool

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type}

theorem pool_residual_coefficient_norm (d : FirstGaussPoolData C P ι)
    (q : ExteriorPrime A) (n : ℕ) (coeff : ι → ℂ) (i : d.valuationColumns q n) :
    ‖d.residualCoefficient q n coeff i‖ = ‖coeff i.val‖ * Q q ^ n := by
  rw [d.residualCoefficient_eq, norm_mul, norm_mul,
    (d.residualPresentation q n i).columnPhase_norm, mul_one,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (primeNorm_pos q)]

theorem pool_residual_active_card (d : FirstGaussPoolData C P ι)
    (q : ExteriorPrime A) (n : ℕ) (coeff : ι → ℂ) :
    ((Finset.univ.filter (fun i : d.valuationColumns q n =>
      d.residualCoefficient q n coeff i ≠ 0)).card : ℝ) ≤
      ((d.columns.filter (fun i => coeff i ≠ 0)).card : ℝ) := by
  let S := Finset.univ.filter (fun i : d.valuationColumns q n =>
    d.residualCoefficient q n coeff i ≠ 0)
  have hsub : S.image Subtype.val ⊆ d.columns.filter (fun i => coeff i ≠ 0) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have hjm := (Finset.mem_filter.mp hj).2
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp j.property).1, ?_⟩
    intro hz
    apply hjm
    rw [d.residualCoefficient_eq, hz, zero_mul, zero_mul]
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hcount
  exact_mod_cast hcount

theorem pool_main_rows_card (d : FirstGaussPoolData C P ι) :
    d.mainRows.card ≤ d.rows.card * P.primes.card := by
  apply (Finset.card_image_le).trans
  change (eligiblePairs d.rows P.primes
    (fun h q => actualPrimeEligible d.frozen (d.rowIdeal h) q)).card ≤ _
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_product _ _)

theorem pool_error_rows_card (d : FirstGaussPoolData C P ι) (q : ExteriorPrime A) :
    (d.errorRows q).card ≤ d.rows.card := Finset.card_filter_le _ _

theorem pool_prime_power_le (q : P.primes) (e : AmplifierValuation) :
    Q q.val ^ e.multiplicity ≤ Z ^ (7 * ell) := by
  have hZ := zero_lt_one.trans P.base_gt_one
  have hn : (e.multiplicity : ℝ) ≤ 7 := by cases e <;> norm_num [AmplifierValuation.multiplicity]
  calc
    _ ≤ (Z ^ ell) ^ e.multiplicity :=
      pow_le_pow_left₀ (primeNorm_pos q.val).le (P.norm_upper q.val q.property) _
    _ = Z ^ (ell * (e.multiplicity : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hZ.le]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le P.base_gt_one.le (by
      nlinarith [P.exponent_pos])

end OriginalPool

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

theorem pool_original_columns (P : PoolPresentation family) (hP : P.Realizes)
    (i : Fin family.count) :
    (P.data i).columns = (family.source i).source.columns :=
  congrArg (fun G => G.columns) (hP.original i)

theorem pool_original_rows (P : PoolPresentation family) (hP : P.Realizes)
    (i : Fin family.count) :
    (P.data i).rows = (family.source i).source.rows :=
  congrArg (fun G => G.rows) (hP.original i)

theorem pool_main_active_card (P : PoolPresentation family) (hP : P.Realizes)
    (i : Fin family.count) (source : PhysicalSource call p) (ho : P.MainOrigin i source) :
    (physicalActiveColumns source).card = (physicalActiveColumns (family.source i)).card := by
  have he := dependent_projection_eq
    (fun (Column : Type) (G : ActualGaussSource (Arithmetic.context c) Column) =>
      (G.columns.filter (fun j => G.coefficient j ≠ 0)).card) ho.1 ho.2.1
  change _ = _ at he
  rw [he]
  change ((P.data i).columns.filter (fun j => (family.source i).source.coefficient j ≠ 0)).card = _
  rw [pool_original_columns P hP i]
  rfl

theorem pool_error_active_card (P : PoolPresentation family) (hP : P.Realizes)
    (i : Fin family.count) (q : P.pool.primes) (e : AmplifierValuation)
    (source : PhysicalSource call p) (ho : P.ErrorOrigin i q e source) :
    ((physicalActiveColumns source).card : ℝ) ≤
      ((physicalActiveColumns (family.source i)).card : ℝ) := by
  have he := dependent_projection_eq
    (fun (Column : Type) (G : ActualGaussSource (Arithmetic.context c) Column) =>
      ((G.columns.filter (fun j => G.coefficient j ≠ 0)).card : ℝ)) ho.1 ho.2.1
  rw [show ((physicalActiveColumns source).card : ℝ) = _ from he]
  exact (pool_residual_active_card (P.data i) q.val e.multiplicity
    (family.source i).source.coefficient).trans_eq (by rw [pool_original_columns P hP i]; rfl)

theorem pool_origin_active_card (P : PoolPresentation family) (hP : P.Realizes)
    (index : P.Index) (source : PhysicalSource call p) (ho : P.Origin index source) :
    ((physicalActiveColumns source).card : ℝ) ≤
      ((physicalActiveColumns (family.source index.1)).card : ℝ) := by
  rcases index with ⟨i, u | ⟨q, e⟩⟩
  · exact le_of_eq (congrArg (fun n : ℕ => (n : ℝ)) (pool_main_active_card P hP i source ho))
  · exact pool_error_active_card P hP i q e source ho

theorem pool_main_coefficient_bound (P : PoolPresentation family) (hP : P.Realizes)
    (i : Fin family.count) (source : PhysicalSource call p) (ho : P.MainOrigin i source)
    (amplitude : ℝ)
    (hcoeff : ∀ j ∈ (family.source i).source.columns,
      ‖(family.source i).source.coefficient j‖ ≤ amplitude) :
    ∀ j ∈ source.source.columns, ‖source.source.coefficient j‖ ≤ amplitude := by
  have he := dependent_projection_eq
    (fun (Column : Type) (G : ActualGaussSource (Arithmetic.context c) Column) =>
      ∀ j ∈ G.columns, ‖G.coefficient j‖ ≤ amplitude) ho.1 ho.2.1
  rw [he]
  change ∀ j ∈ (P.data i).columns, ‖(family.source i).source.coefficient j‖ ≤ amplitude
  rw [pool_original_columns P hP i]
  exact hcoeff

theorem pool_error_coefficient_bound (P : PoolPresentation family) (hP : P.Realizes)
    (i : Fin family.count) (q : P.pool.primes) (e : AmplifierValuation)
    (source : PhysicalSource call p) (ho : P.ErrorOrigin i q e source)
    (amplitude : ℝ) (hamp : 0 ≤ amplitude)
    (hcoeff : ∀ j ∈ (family.source i).source.columns,
      ‖(family.source i).source.coefficient j‖ ≤ amplitude) :
    ∀ j ∈ source.source.columns, ‖source.source.coefficient j‖ ≤
      amplitude * call.base ^ (7 * (recipeInductionSigma c / 3)) := by
  have he := dependent_projection_eq
    (fun (Column : Type) (G : ActualGaussSource (Arithmetic.context c) Column) =>
      ∀ j ∈ G.columns, ‖G.coefficient j‖ ≤
        amplitude * call.base ^ (7 * (recipeInductionSigma c / 3))) ho.1 ho.2.1
  rw [he]
  intro j hj
  change ‖(P.data i).residualCoefficient q.val e.multiplicity
    (family.source i).source.coefficient j‖ ≤ _
  rw [pool_residual_coefficient_norm]
  have hjc : j.val ∈ (family.source i).source.columns := by
    rw [← pool_original_columns P hP i]
    exact (Finset.mem_filter.mp j.property).1
  exact mul_le_mul (hcoeff j.val hjc) (pool_prime_power_le q e)
    (pow_nonneg (primeNorm_pos q.val).le _) hamp

theorem pool_origin_coefficient_bound (P : PoolPresentation family) (hP : P.Realizes)
    (index : P.Index) (source : PhysicalSource call p) (ho : P.Origin index source)
    (amplitude : ℝ) (hamp : 0 ≤ amplitude)
    (hcoeff : ∀ j ∈ (family.source index.1).source.columns,
      ‖(family.source index.1).source.coefficient j‖ ≤ amplitude) :
    ∀ j ∈ source.source.columns, ‖source.source.coefficient j‖ ≤
      amplitude * call.base ^ (7 * (recipeInductionSigma c / 3)) := by
  rcases index with ⟨i, u | ⟨q, e⟩⟩
  · intro j hj
    apply (pool_main_coefficient_bound P hP i source ho amplitude hcoeff j hj).trans
    exact le_mul_of_one_le_right hamp
      (Real.one_le_rpow call.domain.scale.le (by
        have hs := (recipeInduction_budget (c := c)).1
        linarith))
  · exact pool_error_coefficient_bound P hP i q e source ho amplitude hamp hcoeff

theorem pool_main_row_card (P : PoolPresentation family) (hP : P.Realizes)
    (i : Fin family.count) (source : PhysicalSource call p) (ho : P.MainOrigin i source) :
    source.source.rows.card ≤ (family.source i).source.rows.card * P.pool.primes.card := by
  have he := dependent_projection_eq
    (fun (Column : Type) (G : ActualGaussSource (Arithmetic.context c) Column) =>
      G.rows.card) ho.1 ho.2.1
  rw [he]
  exact (pool_main_rows_card (P.data i)).trans_eq (by rw [pool_original_rows P hP i])

theorem pool_error_row_card (P : PoolPresentation family) (hP : P.Realizes)
    (i : Fin family.count) (q : P.pool.primes) (e : AmplifierValuation)
    (source : PhysicalSource call p) (ho : P.ErrorOrigin i q e source) :
    source.source.rows.card ≤ (family.source i).source.rows.card := by
  have he := dependent_projection_eq
    (fun (Column : Type) (G : ActualGaussSource (Arithmetic.context c) Column) =>
      G.rows.card) ho.1 ho.2.1
  rw [he]
  exact (pool_error_rows_card (P.data i) q.val).trans_eq (by rw [pool_original_rows P hP i])

theorem pool_origin_row_card (P : PoolPresentation family) (hP : P.Realizes)
    (index : P.Index) (source : PhysicalSource call p) (ho : P.Origin index source) :
    source.source.rows.card ≤ (family.source index.1).source.rows.card *
      max 1 P.pool.primes.card := by
  rcases index with ⟨i, u | ⟨q, e⟩⟩
  · exact (pool_main_row_card P hP i source ho).trans
      (Nat.mul_le_mul_left _ (le_max_right _ _))
  · exact (pool_error_row_card P hP i q e source ho).trans
      (by simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left (family.source i).source.rows.card (le_max_left 1 P.pool.primes.card))

/-- The pool changes the valuation tag, with the inherited original
first common coordinates, kernel and retained scale kept literally. -/
theorem pool_origin_coordinates (P : PoolPresentation family)
    (index : P.Index) (source : PhysicalSource call p) (ho : P.Origin index source) :
    source.firstKernel = (family.source index.1).firstKernel ∧
    source.first.retainedScale = (family.source index.1).first.retainedScale ∧
    source.first.selected = (family.source index.1).first.selected ∧
    source.first.opposite = (family.source index.1).first.opposite ∧
    source.first.complementary = (family.source index.1).first.complementary := by
  rcases index with ⟨i, u | ⟨q, e⟩⟩
  · rcases ho with ⟨_, _, _, _, hk, _, _, hf⟩
    exact ⟨hk, by rw [hf], by rw [hf], by rw [hf], by rw [hf]⟩
  · rcases ho with ⟨_, _, _, _, hk, _, _, hs, ho, hc, _, _, _, _, hr, _, _, _⟩
    exact ⟨hk, hr, hs, ho, hc⟩

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.pool_origin_active_card
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.pool_origin_coefficient_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.pool_origin_row_card
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.pool_origin_coordinates
