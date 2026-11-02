import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S3RowTransport

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Physical windows for the literal main and valuation sources

Only the main rows grow, by the actual sixth prime power.  Each error
keeps an original row and divides the original column norm by its exact
prime power.  No density estimate is used a second time in this transport.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

theorem residual_norm_lower {q : ExteriorPrime (Arithmetic.data c)} {n : ℕ}
    {I : (Arithmetic.data c).Exterior}
    (R : AmplifierResidualPresentation (Arithmetic.context c) q n I)
    (x : ℝ) (hx : call.base ^ x ≤ (Arithmetic.data c).exteriorNorm I) :
    call.base ^ (x - (n : ℝ) * idealLogLength call.base q.val.asIdeal) ≤
      (Arithmetic.data c).exteriorNorm R.residual := by
  rw [rpow_sub_prime_multiple, R.norm_residual]
  exact div_le_div_of_nonneg_right hx (pow_nonneg (primeNorm_pos q).le n)

theorem residual_norm_upper {q : ExteriorPrime (Arithmetic.data c)} {n : ℕ}
    {I : (Arithmetic.data c).Exterior}
    (R : AmplifierResidualPresentation (Arithmetic.context c) q n I)
    (x : ℝ) (hx : (Arithmetic.data c).exteriorNorm I ≤ call.base ^ x) :
    (Arithmetic.data c).exteriorNorm R.residual ≤
      call.base ^ (x - (n : ℝ) * idealLogLength call.base q.val.asIdeal) := by
  rw [rpow_sub_prime_multiple, R.norm_residual]
  exact div_le_div_of_nonneg_right hx (pow_nonneg (primeNorm_pos q).le n)

theorem main_windows (P : PoolPresentation family) (hP : P.Realizes)
    (hF : F.Realizes) (hfamily : family.Realizes)
    (i : Fin family.count) (hW : (family.source i).Windows) :
    (main P i).Windows := by
  have hrows : (P.data i).rows = (family.source i).source.rows :=
    congrArg ActualGaussSource.rows (hP.original i)
  have hcolumns : (P.data i).columns = (family.source i).source.columns :=
    congrArg ActualGaussSource.columns (hP.original i)
  have hideal : (P.data i).ideal = (family.source i).source.ideal :=
    congrArg ActualGaussSource.ideal (hP.original i)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hne
    change (P.data i).mainRows.Nonempty at hne
    obtain ⟨h, hh⟩ := hne
    obtain ⟨rq, hmem, _⟩ := Finset.mem_image.mp hh
    have hr := (Finset.mem_product.mp (Finset.mem_filter.mp hmem).1).1
    rw [hrows] at hr
    exact hW.retained_upper ⟨rq.1, hr⟩
  · intro j hj hjnz
    change j ∈ (P.data i).columns at hj
    rw [hcolumns] at hj
    simpa only [main, FirstGaussPoolData.mainSource, hideal,
      hfamily.tag i, OriginalNominalTag.removedLength] using hW.column_lower j hj hjnz
  · intro j hj hjnz
    change j ∈ (P.data i).columns at hj
    rw [hcolumns] at hj
    simpa only [main, FirstGaussPoolData.mainSource, hideal,
      hfamily.tag i, OriginalNominalTag.removedLength] using hW.column_upper j hj hjnz
  · intro h hh
    change h ∈ (P.data i).mainRows at hh
    obtain ⟨⟨r, q⟩, hmem, rfl⟩ := Finset.mem_image.mp hh
    have hrq := Finset.mem_product.mp (Finset.mem_filter.mp hmem).1
    have hr := hrq.1
    rw [hrows] at hr
    change (Arithmetic.data c).exteriorNorm
        (originalFrequencyIdeal (actualFrequencyAmplify (Arithmetic.context c) (r, q))) ≤
      (family.source i).first.retainedScale * call.base ^ (2 * recipeInductionSigma c)
    rw [amplified_row_norm r ((family.source i).source.row_nonzero r hr) q]
    exact mul_le_mul (original_row_sharp hF hfamily i r hr)
      (pool_prime_sixth P q hrq.2) (pow_nonneg (primeNorm_pos q).le 6)
      (family.source i).first.retainedScale_pos.le

theorem error_windows (P : PoolPresentation family) (hP : P.Realizes)
    (hfamily : family.Realizes) (i : Fin family.count)
    (q : P.pool.primes) (e : AmplifierValuation)
    (hW : (family.source i).Windows) : (error P i q e).Windows := by
  have hrows : (P.data i).rows = (family.source i).source.rows :=
    congrArg ActualGaussSource.rows (hP.original i)
  have hcolumns : (P.data i).columns = (family.source i).source.columns :=
    congrArg ActualGaussSource.columns (hP.original i)
  have hideal : (P.data i).ideal = (family.source i).source.ideal :=
    congrArg ActualGaussSource.ideal (hP.original i)
  have hcoeff (j : (P.data i).valuationColumns q.val e.multiplicity)
      (hj : (error P i q e).source.coefficient j ≠ 0) :
      (family.source i).source.coefficient j.val ≠ 0 := by
    intro hz
    apply hj
    change (P.data i).residualCoefficient q.val e.multiplicity
      (family.source i).source.coefficient j = 0
    rw [FirstGaussPoolData.residualCoefficient_eq, hz, zero_mul, zero_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hne
    change ((P.data i).errorRows q.val).Nonempty at hne
    obtain ⟨h, hh⟩ := hne
    have hr := (Finset.mem_filter.mp hh).1
    rw [hrows] at hr
    exact hW.retained_upper ⟨h, hr⟩
  · intro j _ hjnz
    have hj := (Finset.mem_filter.mp j.property).1
    rw [hcolumns] at hj
    have hbound := hW.column_lower j.val hj (hcoeff j hjnz)
    have hbound' : call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
        call.workingParameters.z - idealLogLength call.base (family.source i).first.selected.val -
        4 * p.loss) ≤ (Arithmetic.data c).exteriorNorm ((P.data i).ideal j.val) := by
      simpa only [hideal, hfamily.tag i, OriginalNominalTag.removedLength,
        sub_zero] using hbound
    have hres := residual_norm_lower (call := call)
      ((P.data i).residualPresentation q.val e.multiplicity j) _ hbound'
    change call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
        call.workingParameters.z - idealLogLength call.base (family.source i).first.selected.val -
        (e.multiplicity : ℝ) * idealLogLength call.base q.val.val.asIdeal - 4 * p.loss) ≤
      (Arithmetic.data c).exteriorNorm
        ((P.data i).residualPresentation q.val e.multiplicity j).residual
    convert hres using 1 <;> congr 1 <;> ring
  · intro j _ hjnz
    have hj := (Finset.mem_filter.mp j.property).1
    rw [hcolumns] at hj
    have hbound := hW.column_upper j.val hj (hcoeff j hjnz)
    have hbound' : (Arithmetic.data c).exteriorNorm ((P.data i).ideal j.val) ≤
        call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z - idealLogLength call.base (family.source i).first.selected.val +
          4 * p.loss) := by
      simpa only [hideal, hfamily.tag i, OriginalNominalTag.removedLength,
        sub_zero] using hbound
    have hres := residual_norm_upper (call := call)
      ((P.data i).residualPresentation q.val e.multiplicity j) _ hbound'
    change (Arithmetic.data c).exteriorNorm
        ((P.data i).residualPresentation q.val e.multiplicity j).residual ≤
      call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
        call.workingParameters.z - idealLogLength call.base (family.source i).first.selected.val -
        (e.multiplicity : ℝ) * idealLogLength call.base q.val.val.asIdeal + 4 * p.loss)
    convert hres using 1 <;> congr 1 <;> ring
  · intro h hh
    change h ∈ (P.data i).errorRows q.val at hh
    have hr := (Finset.mem_filter.mp hh).1
    rw [hrows] at hr
    simpa only [error, hfamily.tag i, OriginalNominalTag.padding] using hW.row_upper h hr

theorem physical_windows (P : PoolPresentation family) (hP : P.Realizes)
    (hF : F.Realizes) (hfamily : family.Realizes)
    (hW : ∀ i, (family.source i).Windows) (key : P.Index) :
    (physical P key).Windows := by
  rcases key with ⟨i, key⟩
  cases key with
  | inl u => exact main_windows P hP hF hfamily i (hW i)
  | inr qe => exact error_windows P hP hfamily i qe.1 qe.2 (hW i)

theorem expansion_windows (P : PoolPresentation family) (hP : P.Realizes)
    (hF : F.Realizes) (hfamily : family.Realizes)
    (hW : ∀ i, (family.source i).Windows) :
    ∀ i, ((expansion P).source i).Windows := by
  intro i
  exact physical_windows P hP hF hfamily hW _

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3
