import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bOrbitFibres
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bIndexWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bRowBounds

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! # The original source chain supplies its own physical orbit fibres -/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

namespace PhysicalSource

theorem t3b_orbitMultiplicity_le (source : PhysicalSource call p)
    (B : ℝ) (hB : 0 ≤ B)
    (hfibres : ∀ q,
      ((source.source.rows.filter (fun h =>
        engineElementOrbit (Γ := Arithmetic.unitSubgroup c) h = q)).card : ℝ) ≤ B) :
    (source.orbitMultiplicity : ℝ) ≤ B := by
  let image := source.source.rows.image
    (engineElementOrbit (Γ := Arithmetic.unitSubgroup c))
  by_cases hi : image.Nonempty
  · obtain ⟨q, hq, he⟩ := Finset.exists_mem_eq_sup image hi (fun q =>
      (source.source.rows.filter (fun h =>
        engineElementOrbit (Γ := Arithmetic.unitSubgroup c) h = q)).card)
    change ((image.sup (fun q => (source.source.rows.filter (fun h =>
      engineElementOrbit (Γ := Arithmetic.unitSubgroup c) h = q)).card) : ℕ) : ℝ) ≤ B
    rw [he]
    exact hfibres q
  · change ((image.sup (fun q => (source.source.rows.filter (fun h =>
      engineElementOrbit (Γ := Arithmetic.unitSubgroup c) h = q)).card) : ℕ) : ℝ) ≤ B
    rw [Finset.not_nonempty_iff_eq_empty.mp hi, Finset.sup_empty]
    simpa only [bot_eq_zero, Nat.cast_zero] using hB

end PhysicalSource

namespace FirstCauchyFamily

/-- The original first carriers have exactly one representative for
each subgroup orbit; the right carrier retains its original sign. -/
theorem t3b_source_orbit_injective (family : FirstCauchyFamily F)
    (hF : F.Realizes) (hfamily : family.Realizes) (i : Fin family.count) :
    Set.InjOn (engineElementOrbit (Γ := Arithmetic.unitSubgroup c))
      ((family.source i).source.rows : Set (Arithmetic.data c).R) := by
  rw [(family.source i).rows_eq_of_transport
    ((FirstCauchyKey.data (family.index i)).directSource
      (FirstCauchyKey.coefficient (family.index i)))
    (hfamily.column i) (hfamily.source i)]
  change Set.InjOn _ ((FirstCauchyKey.data (family.index i)).rows : Set (Arithmetic.data c).R)
  unfold FirstCauchyKey.data
  split_ifs
  · have hrows : (FirstCauchyKey.piece (family.index i)).rightData.rows =
        ((F.source.source (FirstCauchyKey.common (family.index i))).divisorRows
          (FirstCauchyKey.divisor (family.index i)).val).image (fun q => -q.out.val) :=
      hF.rightRows _ _
    rw [hrows]
    exact T3b.negative_representative_image_orbit_injective _
  · have hrows : (FirstCauchyKey.piece (family.index i)).leftData.rows =
        ((F.source.source (FirstCauchyKey.common (family.index i))).divisorRows
          (FirstCauchyKey.divisor (family.index i)).val).image (fun q => q.out.val) :=
      hF.leftRows _ _
    rw [hrows]
    exact T3b.representative_image_orbit_injective _

theorem t3b_orbitMultiplicity_le_one (family : FirstCauchyFamily F)
    (hF : F.Realizes) (hfamily : family.Realizes) (i : Fin family.count) :
    ((family.source i).orbitMultiplicity : ℝ) ≤ 1 := by
  apply (family.source i).t3b_orbitMultiplicity_le 1 zero_le_one
  intro q
  have hcard : ((family.source i).source.rows.filter (fun h =>
      engineElementOrbit (Γ := Arithmetic.unitSubgroup c) h = q)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact (family.t3b_source_orbit_injective hF hfamily i)
      (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
      ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  exact_mod_cast hcard

end FirstCauchyFamily

namespace PoolExpansion

/-- This factor counts the actual second-input orbit fibre only.
The original amplifier's outer multiplicity remains in its outer weight. -/
def t3bOrbitFibreAllowance (expansion : PoolExpansion family) : Fin expansion.count → ℝ :=
  match expansion with
  | .direct => fun _ => 1
  | .pooled P _ index _ => fun i =>
    match (index i).2 with
    | .inl _ => (P.data (index i).1).multiplicity
    | .inr _ => 1

theorem t3bOrbitFibreAllowance_nonneg (expansion : PoolExpansion family)
    (i : Fin expansion.count) : 0 ≤ expansion.t3bOrbitFibreAllowance i := by
  cases expansion with
  | direct => exact zero_le_one
  | pooled P count index source =>
    dsimp only [t3bOrbitFibreAllowance]
    cases (index i).2 with
    | inl u => exact (P.data (index i).1).multiplicity_nonneg
    | inr qe => exact zero_le_one

/-- Every fibre comes from the exact direct/main/1/6/7 constructor.
No new orbit-fibre assumption is requested of the caller. -/
theorem t3b_orbitMultiplicity_le (expansion : PoolExpansion family)
    (hF : F.Realizes) (hfamily : family.Realizes) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count) :
    ((expansion.source i).orbitMultiplicity : ℝ) ≤ expansion.t3bOrbitFibreAllowance i := by
  cases expansion with
  | direct => exact family.t3b_orbitMultiplicity_le_one hF hfamily i
  | pooled P count index source =>
    have horiginal : (P.data (index i).1).rows = (family.source (index i).1).source.rows :=
      congrArg ActualGaussSource.rows (hexpansion.2.1.original (index i).1)
    have hinj : Set.InjOn (engineElementOrbit (Γ := Arithmetic.unitSubgroup c))
        ((P.data (index i).1).rows : Set (Arithmetic.data c).R) := by
      rw [horiginal]
      exact family.t3b_source_orbit_injective hF hfamily (index i).1
    cases htag : (index i).2 with
    | inl u =>
      have ho : P.MainOrigin (index i).1 (source i) := by
        simpa only [PoolPresentation.Origin, htag] using hexpansion.2.2 i
      change ((source i).orbitMultiplicity : ℝ) ≤ _
      simp only [t3bOrbitFibreAllowance, htag]
      apply (source i).t3b_orbitMultiplicity_le _ (P.data (index i).1).multiplicity_nonneg
      intro q
      rw [(source i).rows_eq_of_transport _ ho.1 ho.2.1]
      exact T3b.mainRows_orbit_fibre_le (P.data (index i).1) hinj q
    | inr qe =>
      have ho : P.ErrorOrigin (index i).1 qe.1 qe.2 (source i) := by
        simpa only [PoolPresentation.Origin, htag] using hexpansion.2.2 i
      change ((source i).orbitMultiplicity : ℝ) ≤ _
      simp only [t3bOrbitFibreAllowance, htag]
      apply (source i).t3b_orbitMultiplicity_le 1 zero_le_one
      intro q
      rw [(source i).rows_eq_of_transport _ ho.1 ho.2.1]
      have hinjerror : Set.InjOn (engineElementOrbit (Γ := Arithmetic.unitSubgroup c))
          ((P.data (index i).1).errorRows qe.1.val : Set (Arithmetic.data c).R) := by
        intro a ha b hb he
        exact hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 he
      have hcard : (((P.data (index i).1).residualSource qe.1.val qe.2.multiplicity
          (family.source (index i).1).source.coefficient).rows.filter (fun h =>
          engineElementOrbit (Γ := Arithmetic.unitSubgroup c) h = q)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        exact hinjerror (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
          ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
      exact_mod_cast hcard

end PoolExpansion

namespace RawFamily

theorem t3b_secondFiber_le (trace : SourceTrace call p) (htrace : trace.Realizes)
    {geometry : GeometryFamily trace.second} (raw : RawFamily geometry) (j : Fin raw.count) :
    ((raw.packet j).second.stage.fiber : ℝ) ≤
      trace.expansion.t3bOrbitFibreAllowance (raw.sourceIndex j) := by
  change ((trace.second.source (raw.sourceIndex j)).stage.fiber : ℝ) ≤ _
  rw [(htrace.second.stage (raw.sourceIndex j)).fiber,
    htrace.second.physical (raw.sourceIndex j)]
  exact trace.expansion.t3b_orbitMultiplicity_le htrace.first htrace.cauchy
    htrace.expansion (raw.sourceIndex j)

end RawFamily

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawFamily.t3b_secondFiber_le
