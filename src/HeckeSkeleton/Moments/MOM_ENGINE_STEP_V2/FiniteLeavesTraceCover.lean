module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FiniteLeavesOriginalSupport

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Original occurrence covers along one coherent source trace

The first, main and valuation sources use the same constructor. Column
type identities make the heterogeneous source equalities coherent.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.FiniteLeaves

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.Support
open HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem fibreInput_first_heq
    (F : FirstPresentation call p) (hF : F.Realizes)
    (key : Blueprint.FirstCauchyKey F) (source : PhysicalSource call p)
    (column : source.Column = F.source.Column)
    (hsource : HEq source.source
      ((Blueprint.FirstCauchyKey.data key).directSource
        (Blueprint.FirstCauchyKey.coefficient key)))
    (hancestor : HEq source.ancestor (fun j : F.source.Column => F.index j))
    (hdeletion : source.first.fullDeletion = primeSupport key.1.val.1) :
    OriginalFibreInput source := by
  rcases source with ⟨Column, G, ancestor, multiplier, kernel, point, outer, houter, first⟩
  dsimp only at column hsource hancestor hdeletion ⊢
  subst Column
  have hG := eq_of_heq hsource
  have ha := eq_of_heq hancestor
  subst G
  subst ancestor
  apply fibreInput_of_first F hF key _ (Equiv.refl _)
    (fun _ => rfl) (fun _ => Iff.rfl) (fun _ => rfl) hdeletion

theorem fibreInput_firstCauchy
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (i : Fin family.count) : OriginalFibreInput (family.source i) := by
  apply fibreInput_first_heq F hF (family.index i) (family.source i)
    (hfamily.column i) (hfamily.source i) (hfamily.ancestor i)
  rw [hfamily.deletion i, hfamily.selected i]
  exact FirstCauchyKey.selected_support (family.index i)

section Pool

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool (Arithmetic.data c) bad Z ell eps}

theorem fibreInput_main_heq
    (source target : PhysicalSource call p) (h : OriginalFibreInput source)
    (d : FirstGaussPoolData (Arithmetic.context c) P source.Column)
    (original : d.directSource source.source.coefficient = source.source)
    (column : target.Column = source.Column)
    (hsource : HEq target.source (d.mainSource source.source.coefficient))
    (hancestor : HEq target.ancestor source.ancestor)
    (hdeletion : target.first.fullDeletion = source.first.fullDeletion) :
    OriginalFibreInput target := by
  rcases target with ⟨Column, G, ancestor, multiplier, kernel, point, outer, houter, first⟩
  dsimp only at column hsource hancestor hdeletion ⊢
  subst Column
  have hG := eq_of_heq hsource
  have ha := eq_of_heq hancestor
  subst G
  subst ancestor
  have hcolumns : d.columns = source.source.columns :=
    congrArg ActualGaussSource.columns original
  have hideal : d.ideal = source.source.ideal := congrArg ActualGaussSource.ideal original
  apply fibreInput_congr source
    { Column := source.Column
      source := d.mainSource source.source.coefficient
      ancestor := source.ancestor
      multiplier := multiplier
      firstKernel := kernel
      firstPoint := point
      outerWeight := outer
      outerWeight_nonneg := houter
      first := first } h (Equiv.refl _) (fun _ => rfl) ?_ ?_ hdeletion
  · intro i
    change i ∈ d.columns ↔ i ∈ source.source.columns
    rw [hcolumns]
  · intro i
    exact congrFun hideal i

theorem fibreInput_residual_heq
    (source target : PhysicalSource call p) (h : OriginalFibreInput source)
    (d : FirstGaussPoolData (Arithmetic.context c) P source.Column)
    (original : d.directSource source.source.coefficient = source.source)
    (q : ExteriorPrime (Arithmetic.data c)) (n : ℕ)
    (column : target.Column = d.valuationColumns q n)
    (hsource : HEq target.source (d.residualSource q n source.source.coefficient))
    (hancestor : HEq target.ancestor
      (fun j : d.valuationColumns q n => source.ancestor j.val))
    (hdeletion : target.first.fullDeletion = source.first.fullDeletion ∪ {q.val.asIdeal}) :
    OriginalFibreInput target := by
  rcases target with ⟨Column, G, ancestor, multiplier, kernel, point, outer, houter, first⟩
  dsimp only at column hsource hancestor hdeletion ⊢
  subst Column
  have hG := eq_of_heq hsource
  have ha := eq_of_heq hancestor
  subst G
  subst ancestor
  have hcolumns : d.columns = source.source.columns :=
    congrArg ActualGaussSource.columns original
  have hideal : d.ideal = source.source.ideal := congrArg ActualGaussSource.ideal original
  apply fibreInput_of_residual source _ h d hcolumns hideal q n (Equiv.refl _)
    (fun _ => Finset.mem_univ _) (fun _ => rfl) ?_ hdeletion
  intro i
  change (d.residualPresentation q n i).residual.val = _
  rw [(d.residualPresentation q n i).residual_eq_supportResidual, hideal]
  rfl

end Pool

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

theorem fibreInput_expansion
    (expansion : PoolExpansion family) (hexpansion : expansion.Realizes)
    (hfirst : ∀ i, OriginalFibreInput (family.source i))
    (i : Fin expansion.count) : OriginalFibreInput (expansion.source i) := by
  cases expansion with
  | direct => exact hfirst i
  | pooled P count index source =>
    rcases hexpansion with ⟨hslots, hP, horigin⟩
    have ho := horigin i
    cases he : (index i).2 with
    | inl u =>
      rw [PoolPresentation.Origin, he] at ho
      rcases ho with ⟨hcol, hs, ha, hm, hk, hp, hw, hf⟩
      apply fibreInput_main_heq (family.source (index i).1) (source i)
        (hfirst _) (P.data _) (hP.original _) hcol hs ha
      rw [hf]
    | inr qe =>
      rw [PoolPresentation.Origin, he] at ho
      rcases ho with ⟨hcol, hs, ha, hm, hk, hp, hw, hselected, hopposite, hcomplementary,
        hresidual, helement, hright, hpower, hscale, htag, hdeletion, hpaid⟩
      exact fibreInput_residual_heq (family.source (index i).1) (source i)
        (hfirst _) (P.data _) (hP.original _) qe.1.val qe.2.multiplicity
        hcol hs ha hdeletion

theorem covers_of_trace
    (trace : SourceTrace call p) (htrace : trace.Realizes) :
    ∃ covers : RawCovers trace.second,
      ∀ i, (covers.left i).Realizes ∧ (covers.right i).Realizes := by
  have hfirst := fibreInput_firstCauchy trace.first htrace.first
    trace.cauchy htrace.cauchy
  have hsource (i : Fin trace.expansion.count) :
      OriginalFibreInput (trace.second.source i).physical := by
    rw [htrace.second.physical i]
    exact fibreInput_expansion trace.expansion htrace.expansion hfirst i
  refine ⟨{
    left := fun i => (hsource i).cover
    right := fun i => (hsource i).cover }, ?_⟩
  intro i
  exact ⟨(hsource i).cover_realizes, (hsource i).cover_realizes⟩

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.FiniteLeaves

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FiniteLeaves.covers_of_trace
