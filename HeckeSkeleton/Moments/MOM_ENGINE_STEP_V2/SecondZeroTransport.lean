import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondZeroCoefficients
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceEqualityTransport

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Original coefficient and divisor transport through the one pool

The exact column-type and source equalities in the public realization
records transfer the original bounds. The error source's divisor is
retained precisely when its actual row set is nonempty: the actual
prime eligibility condition then says that the prime avoids the frozen
first divisor. No new assumption on a second transformed source enters
the transport.
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

theorem first_family_weighted_coefficient_bound
    (hF : F.Realizes) (hfamily : family.Realizes)
    (frame : SourceFrame) (input : ProfileInput call)
    (horders : {(0, 0)} ⊆ input.orders) (hframe : call.frame = frame)
    (hannulus : FirstZeroProof.uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤
      call.base ^ p.loss)
    (T : ℝ) (hT : call.workingParameters.n₁ + call.workingParameters.n₂ +
      call.workingParameters.z + p.loss ≤ T) (i : Fin family.count) :
    ∀ j ∈ (family.source i).source.columns,
      ‖(family.source i).source.coefficient j‖ *
        (Arithmetic.data c).exteriorNorm ((family.source i).source.ideal j) ≤
      ((2 * input.amplitude ^ (c.geometry.slots + 2)) *
        call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z) / 2)) * call.base ^ (T * p.tilt) := by
  apply weighted_coefficient_bound_of_heq (family.source i).source
    ((FirstCauchyKey.data (family.index i)).directSource
      (FirstCauchyKey.coefficient (family.index i)))
    (hfamily.column i) (hfamily.source i)
  intro j hj
  exact first_key_weighted_coefficient_bound F hF frame input horders hframe
    hannulus T hT (family.index i) j hj

theorem first_family_coefficient_divisor (hfamily : family.Realizes)
    (i : Fin family.count) :
    ∀ j ∈ (family.source i).source.columns, (family.source i).source.coefficient j ≠ 0 →
      (family.source i).first.residualDivisor.val ∣ ((family.source i).source.ideal j).val := by
  apply coefficient_divisor_of_heq (family.source i).source
    ((FirstCauchyKey.data (family.index i)).directSource
      (FirstCauchyKey.coefficient (family.index i)))
    (hfamily.column i) (hfamily.source i)
  intro j _ hnz
  rw [hfamily.residual i]
  exact first_key_divisor_dvd F (family.index i) j hnz

section PoolTransport

variable (P : PoolPresentation family) (hP : P.Realizes)

theorem main_weighted_coefficient_bound (i : Fin family.count)
    (source : PhysicalSource call p) (hsource : P.MainOrigin i source)
    (B : ℝ) (hbound : ∀ j ∈ (family.source i).source.columns,
      ‖(family.source i).source.coefficient j‖ *
        (Arithmetic.data c).exteriorNorm ((family.source i).source.ideal j) ≤ B) :
    ∀ j ∈ source.source.columns, ‖source.source.coefficient j‖ *
      (Arithmetic.data c).exteriorNorm (source.source.ideal j) ≤ B := by
  apply weighted_coefficient_bound_of_heq source.source
    ((P.data i).mainSource (family.source i).source.coefficient) hsource.1 hsource.2.1
  have hcols : (P.data i).columns = (family.source i).source.columns :=
    congrArg ActualGaussSource.columns (hP.original i)
  have hideal : (P.data i).ideal = (family.source i).source.ideal :=
    congrArg ActualGaussSource.ideal (hP.original i)
  intro j hj
  change ‖(family.source i).source.coefficient j‖ *
    (Arithmetic.data c).exteriorNorm ((P.data i).ideal j) ≤ B
  rw [hideal]
  exact hbound j (hcols ▸ hj)

theorem error_weighted_coefficient_bound (i : Fin family.count)
    (q : P.pool.primes) (e : AmplifierValuation)
    (source : PhysicalSource call p) (hsource : P.ErrorOrigin i q e source)
    (B : ℝ) (hbound : ∀ j ∈ (family.source i).source.columns,
      ‖(family.source i).source.coefficient j‖ *
        (Arithmetic.data c).exteriorNorm ((family.source i).source.ideal j) ≤ B) :
    ∀ j ∈ source.source.columns, ‖source.source.coefficient j‖ *
      (Arithmetic.data c).exteriorNorm (source.source.ideal j) ≤ B := by
  apply weighted_coefficient_bound_of_heq source.source
    ((P.data i).residualSource q.val e.multiplicity (family.source i).source.coefficient)
    hsource.1 hsource.2.1
  have hcols : (P.data i).columns = (family.source i).source.columns :=
    congrArg ActualGaussSource.columns (hP.original i)
  have hideal : (P.data i).ideal = (family.source i).source.ideal :=
    congrArg ActualGaussSource.ideal (hP.original i)
  intro j _
  change ‖(P.data i).residualCoefficient q.val e.multiplicity
      (family.source i).source.coefficient j‖ *
    (Arithmetic.data c).exteriorNorm ((P.data i).residualPresentation q.val e.multiplicity j).residual ≤ B
  rw [residual_coefficient_norm_mul_norm, hideal]
  exact hbound j.val (hcols ▸ (Finset.mem_filter.mp j.property).1)

theorem origin_weighted_coefficient_bound (index : P.Index)
    (source : PhysicalSource call p) (hsource : P.Origin index source)
    (B : ℝ) (hbound : ∀ j ∈ (family.source index.1).source.columns,
      ‖(family.source index.1).source.coefficient j‖ *
        (Arithmetic.data c).exteriorNorm ((family.source index.1).source.ideal j) ≤ B) :
    ∀ j ∈ source.source.columns, ‖source.source.coefficient j‖ *
      (Arithmetic.data c).exteriorNorm (source.source.ideal j) ≤ B := by
  rcases index with ⟨i, tag⟩
  cases tag with
  | inl unit => exact main_weighted_coefficient_bound P hP i source hsource B hbound
  | inr qe => exact error_weighted_coefficient_bound P hP i qe.1 qe.2 source hsource B hbound

theorem main_coefficient_divisor (hfamily : family.Realizes)
    (i : Fin family.count) (source : PhysicalSource call p)
    (hsource : P.MainOrigin i source) :
    ∀ j ∈ source.source.columns, source.source.coefficient j ≠ 0 →
      source.first.residualDivisor.val ∣ (source.source.ideal j).val := by
  rcases hsource with ⟨htype, hsource, hancestor, hmultiplier, hkernel, hpoint, houter, hfirst⟩
  have hS : source.first.residualDivisor = (family.source i).first.residualDivisor :=
    congrArg (fun first => first.residualDivisor) hfirst
  rw [hS]
  apply coefficient_divisor_of_heq source.source
    ((P.data i).mainSource (family.source i).source.coefficient) htype hsource
  have hcols : (P.data i).columns = (family.source i).source.columns :=
    congrArg ActualGaussSource.columns (hP.original i)
  have hideal : (P.data i).ideal = (family.source i).source.ideal :=
    congrArg ActualGaussSource.ideal (hP.original i)
  intro j hj hnz
  change (family.source i).first.residualDivisor.val ∣ ((P.data i).ideal j).val
  rw [hideal]
  exact first_family_coefficient_divisor hfamily i j (hcols ▸ hj) hnz

theorem error_coefficient_divisor (hfamily : family.Realizes)
    (i : Fin family.count) (q : P.pool.primes) (e : AmplifierValuation)
    (source : PhysicalSource call p) (hsource : P.ErrorOrigin i q e source)
    (hrows : source.source.rows.Nonempty) :
    ∀ j ∈ source.source.columns, source.source.coefficient j ≠ 0 →
      source.first.residualDivisor.val ∣ (source.source.ideal j).val := by
  rcases hsource with ⟨htype, hsource, hancestor, hmultiplier, hkernel, hpoint, houter,
    hselected, hopposite, hcomplementary, hresidual, hfirstElement, hright, hpower,
    hretained, htag, hdeletion, hpaid⟩
  have hrows' : ((P.data i).errorRows q.val).Nonempty := by
    rw [source_rows_of_heq source.source
      ((P.data i).residualSource q.val e.multiplicity (family.source i).source.coefficient)
      htype hsource] at hrows
    exact hrows
  obtain ⟨h, hh⟩ := hrows'
  have havoid : ¬q.val.val.asIdeal ∣ (family.source i).first.residualDivisor.val := by
    have he := (Finset.mem_filter.mp hh).2
    change ¬q.val.val.asIdeal ∣ ((P.data i).rowIdeal h).val ∧
      ¬q.val.val.asIdeal ∣ (P.data i).frozen at he
    simpa only [hP.frozen i] using he.2
  rw [hresidual]
  apply coefficient_divisor_of_heq source.source
    ((P.data i).residualSource q.val e.multiplicity (family.source i).source.coefficient)
    htype hsource
  have hcols : (P.data i).columns = (family.source i).source.columns :=
    congrArg ActualGaussSource.columns (hP.original i)
  have hideal : (P.data i).ideal = (family.source i).source.ideal :=
    congrArg ActualGaussSource.ideal (hP.original i)
  intro j _ hnz
  change (family.source i).first.residualDivisor.val ∣
    ((P.data i).residualPresentation q.val e.multiplicity j).residual.val
  apply ((P.data i).residualPresentation q.val e.multiplicity j).dvd_residual_of_dvd_original
    _ _ havoid
  rw [hideal]
  exact first_family_coefficient_divisor hfamily i j.val
    (hcols ▸ (Finset.mem_filter.mp j.property).1)
    (residual_coefficient_nonzero_original (P.data i) q.val e.multiplicity
      (family.source i).source.coefficient j hnz)

theorem origin_coefficient_divisor (hfamily : family.Realizes) (index : P.Index)
    (source : PhysicalSource call p) (hsource : P.Origin index source)
    (hrows : source.source.rows.Nonempty) :
    ∀ j ∈ source.source.columns, source.source.coefficient j ≠ 0 →
      source.first.residualDivisor.val ∣ (source.source.ideal j).val := by
  rcases index with ⟨i, tag⟩
  cases tag with
  | inl unit => exact main_coefficient_divisor P hP hfamily i source hsource
  | inr qe => exact error_coefficient_divisor P hP hfamily i qe.1 qe.2 source hsource hrows

end PoolTransport

theorem expansion_weighted_coefficient_bound
    (expansion : PoolExpansion family) (hexpansion : expansion.Realizes)
    (B : ℝ) (hbound : ∀ i, ∀ j ∈ (family.source i).source.columns,
      ‖(family.source i).source.coefficient j‖ *
        (Arithmetic.data c).exteriorNorm ((family.source i).source.ideal j) ≤ B) :
    ∀ i, ∀ j ∈ (expansion.source i).source.columns,
      ‖(expansion.source i).source.coefficient j‖ *
        (Arithmetic.data c).exteriorNorm ((expansion.source i).source.ideal j) ≤ B := by
  cases expansion with
  | direct => exact hbound
  | pooled P count index source =>
    intro i
    exact origin_weighted_coefficient_bound P hexpansion.2.1 (index i) (source i)
      (hexpansion.2.2 i) B (hbound (index i).1)

theorem expansion_coefficient_divisor (hfamily : family.Realizes)
    (expansion : PoolExpansion family) (hexpansion : expansion.Realizes) :
    ∀ i, (expansion.source i).source.rows.Nonempty →
    ∀ j ∈ (expansion.source i).source.columns, (expansion.source i).source.coefficient j ≠ 0 →
      (expansion.source i).first.residualDivisor.val ∣
        ((expansion.source i).source.ideal j).val := by
  cases expansion with
  | direct =>
    intro i _
    exact first_family_coefficient_divisor hfamily i
  | pooled P count index source =>
    intro i hrows
    exact origin_coefficient_divisor P hexpansion.2.1 hfamily (index i) (source i)
      (hexpansion.2.2 i) hrows

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof
