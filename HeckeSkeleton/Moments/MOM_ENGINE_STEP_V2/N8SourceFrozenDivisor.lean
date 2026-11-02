import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceRawCarrier
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AmplifierResidualSupport

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The first divisor survives into the actual second common pair

The first coefficient gate forces its divisor into every nonzero
column.  On an error source, a physical row witnesses the original
pool eligibility, which excludes that prime from the frozen divisor.
The genuine residual presentation therefore retains the same divisor.
These facts supply the old-mask density of the second harmonic sum.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open CommonSupportMass HeckePort.IdealMobiusDivisorSum
open HeckePort.Moments HeckePort.Moments.Support UniqueFactorizationMonoid
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  coveredClassKeyFintype

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

namespace N8Source

theorem transport_coefficient_ideal {I J : Type}
    (G : ActualGaussSource (Arithmetic.context c) I)
    (H : ActualGaussSource (Arithmetic.context c) J)
    (hI : I = J) (hG : HEq G H)
    (P : (Arithmetic.data c).Exterior → Prop)
    (hP : ∀ j, H.coefficient j ≠ 0 → P (H.ideal j)) :
    ∀ i, G.coefficient i ≠ 0 → P (G.ideal i) := by
  subst J
  have hG' : G = H := eq_of_heq hG
  subst H
  exact hP

theorem transport_rows_nonempty {I J : Type}
    (G : ActualGaussSource (Arithmetic.context c) I)
    (H : ActualGaussSource (Arithmetic.context c) J)
    (hI : I = J) (hG : HEq G H) (hrows : G.rows.Nonempty) :
    H.rows.Nonempty := by
  subst J
  have hG' : G = H := eq_of_heq hG
  simpa only [hG'] using hrows

theorem positive_left_factor {a b d : ℝ} (ha : 0 ≤ a) (h : 0 < a * b * d) :
    0 < a := by
  by_contra hn
  have hz : a = 0 := le_antisymm (le_of_not_gt hn) ha
  simp only [hz, zero_mul, lt_self_iff_false] at h

theorem squarefree_dvd_commonSupportLabel (S I J : Ideal (𝓞 K))
    (hS : Squarefree S) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hSI : S ∣ I) (hSJ : S ∣ J) :
    S ∣ (commonSupportLabel I J).1 ∧ S ∣ (commonSupportLabel I J).2 := by
  have hsupport : primeSupport S ⊆ primeSupport I ∩ primeSupport J := by
    intro P hP
    exact Finset.mem_inter.mpr
      ⟨squarefree_divisor_support hI hS hSI hP,
        squarefree_divisor_support hJ hS hSJ hP⟩
  constructor
  · rw [← squarefree_support_product_self hS]
    apply support_product_dvd (supportExtract_ne_zero I _)
    intro P hP
    rw [supportExtract_support]
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (hsupport hP)).1, hsupport hP⟩
  · rw [← squarefree_support_product_self hS]
    apply support_product_dvd (supportExtract_ne_zero J _)
    intro P hP
    rw [supportExtract_support]
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (hsupport hP)).2, hsupport hP⟩

end N8Source

namespace FirstCauchyKey

variable (key : FirstCauchyKey F)

theorem residual_dvd_of_coefficient_ne_zero (j : F.source.Column)
    (hj : FirstCauchyKey.coefficient key j ≠ 0) :
    (FirstCauchyKey.residual key).val ∣ ((FirstCauchyKey.data key).ideal j).val := by
  by_contra h
  exact hj (by simp only [FirstCauchyKey.coefficient, if_neg h])

theorem residual_squarefree_of_outer_pos (N : F.source.Normalization)
    (h : 0 < FirstCauchyKey.outer key N) :
    Squarefree (FirstCauchyKey.residual key).val := by
  by_contra hS
  have hmu : (UniqueFactorizationMonoid.moebius (FirstCauchyKey.residual key).val : ℂ) = 0 := by
    simp [UniqueFactorizationMonoid.moebius, hS]
  simp only [FirstCauchyKey.outer, hmu, norm_zero, mul_zero, zero_mul,
    zero_div, lt_self_iff_false] at h

end FirstCauchyKey

namespace FirstCauchyFamily

variable (family : FirstCauchyFamily F)

theorem residual_dvd_of_coefficient_ne_zero (hf : family.Realizes)
    (i : Fin family.count) (j : (family.source i).Column)
    (hj : (family.source i).source.coefficient j ≠ 0) :
    (family.source i).first.residualDivisor.val ∣
      ((family.source i).source.ideal j).val := by
  rw [hf.residual i]
  exact N8Source.transport_coefficient_ideal (family.source i).source
    ((FirstCauchyKey.data (family.index i)).directSource
      (FirstCauchyKey.coefficient (family.index i)))
    (hf.column i) (hf.source i)
    (fun I => (FirstCauchyKey.residual (family.index i)).val ∣ I.val)
    (fun j hj => (family.index i).residual_dvd_of_coefficient_ne_zero j hj) j hj

theorem residual_squarefree_of_outer_pos (hf : family.Realizes)
    (i : Fin family.count) (h : 0 < (family.source i).outerWeight) :
    Squarefree (family.source i).first.residualDivisor.val := by
  rw [hf.residual i]
  apply (family.index i).residual_squarefree_of_outer_pos family.normalization
  rwa [← hf.outer i]

end FirstCauchyFamily

namespace PoolPresentation

variable (pool : PoolPresentation family)

theorem main_residual_dvd (hf : family.Realizes) (hpool : pool.Realizes)
    (i : Fin family.count) (source : PhysicalSource call p)
    (horigin : pool.MainOrigin i source)
    (j : source.Column) (hj : source.source.coefficient j ≠ 0) :
    source.first.residualDivisor.val ∣ (source.source.ideal j).val := by
  rcases horigin with ⟨hcol, hsource, _, _, _, _, _, hfirst⟩
  rw [hfirst]
  apply N8Source.transport_coefficient_ideal source.source
    ((pool.data i).mainSource (family.source i).source.coefficient)
    hcol hsource (fun I => (family.source i).first.residualDivisor.val ∣ I.val) _ j hj
  intro x hx
  change (family.source i).first.residualDivisor.val ∣ ((pool.data i).ideal x).val
  rw [pool.data_ideal_eq hpool i x]
  exact family.residual_dvd_of_coefficient_ne_zero hf i x hx

theorem error_residual_dvd (hf : family.Realizes) (hpool : pool.Realizes)
    (i : Fin family.count) (q : pool.pool.primes) (e : AmplifierValuation)
    (source : PhysicalSource call p) (horigin : pool.ErrorOrigin i q e source)
    (hrows : source.source.rows.Nonempty)
    (j : source.Column) (hj : source.source.coefficient j ≠ 0) :
    source.first.residualDivisor.val ∣ (source.source.ideal j).val := by
  rcases horigin with
    ⟨hcol, hsource, _, _, _, _, _, _, _, _, hdivisor, _, _, _, _, _, _, _⟩
  have hr := N8Source.transport_rows_nonempty source.source
    ((pool.data i).residualSource q.val e.multiplicity (family.source i).source.coefficient)
    hcol hsource hrows
  obtain ⟨h, hh⟩ := hr
  have hq : ¬q.val.val.asIdeal ∣ (family.source i).first.residualDivisor.val := by
    rw [← hpool.frozen i]
    exact (Finset.mem_filter.mp hh).2.2
  rw [hdivisor]
  apply N8Source.transport_coefficient_ideal source.source
    ((pool.data i).residualSource q.val e.multiplicity (family.source i).source.coefficient)
    hcol hsource (fun I => (family.source i).first.residualDivisor.val ∣ I.val) _ j hj
  intro x hx
  have hx' : (family.source i).source.coefficient x.val ≠ 0 := by
    intro hz
    apply hx
    change (pool.data i).residualCoefficient q.val e.multiplicity
      (family.source i).source.coefficient x = 0
    rw [(pool.data i).residualCoefficient_eq, hz, zero_mul, zero_mul]
  apply ((pool.data i).residualPresentation q.val e.multiplicity x).dvd_residual_of_dvd_original
    (family.source i).first.residualDivisor.val _ hq
  rw [pool.data_ideal_eq hpool i x.val]
  exact family.residual_dvd_of_coefficient_ne_zero hf i x.val hx'

theorem residual_dvd (hf : family.Realizes) (hpool : pool.Realizes)
    (index : pool.Index) (source : PhysicalSource call p)
    (horigin : pool.Origin index source) (hrows : source.source.rows.Nonempty)
    (j : source.Column) (hj : source.source.coefficient j ≠ 0) :
    source.first.residualDivisor.val ∣ (source.source.ideal j).val := by
  rcases index with ⟨i, branch⟩
  cases branch with
  | inl u => exact pool.main_residual_dvd hf hpool i source horigin j hj
  | inr qe => exact pool.error_residual_dvd hf hpool i qe.1 qe.2 source horigin hrows j hj

theorem residual_squarefree (hf : family.Realizes)
    (index : pool.Index) (source : PhysicalSource call p)
    (horigin : pool.Origin index source) (hpos : 0 < source.outerWeight) :
    Squarefree source.first.residualDivisor.val := by
  rcases index with ⟨i, branch⟩
  cases branch with
  | inl u =>
    rcases horigin with ⟨_, _, _, _, _, _, houter, hfirst⟩
    rw [hfirst]
    apply family.residual_squarefree_of_outer_pos hf i
    apply N8Source.positive_left_factor (family.source i).outerWeight_nonneg
    rwa [← houter]
  | inr qe =>
    rcases horigin with
      ⟨_, _, _, _, _, _, houter, _, _, _, hdivisor, _, _, _, _, _, _, _⟩
    rw [hdivisor]
    apply family.residual_squarefree_of_outer_pos hf i
    apply N8Source.positive_left_factor (family.source i).outerWeight_nonneg
    rwa [← houter]

end PoolPresentation

namespace PoolExpansion

variable (expansion : PoolExpansion family)

theorem residual_dvd (hf : family.Realizes) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count) (hrows : (expansion.source i).source.rows.Nonempty)
    (j : (expansion.source i).Column) (hj : (expansion.source i).source.coefficient j ≠ 0) :
    (expansion.source i).first.residualDivisor.val ∣
      ((expansion.source i).source.ideal j).val := by
  cases expansion with
  | direct => exact family.residual_dvd_of_coefficient_ne_zero hf i j hj
  | pooled pool count index source =>
    exact pool.residual_dvd hf hexpansion.2.1 (index i) (source i)
      (hexpansion.2.2 i) hrows j hj

theorem residual_squarefree (hf : family.Realizes) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count) (hpos : 0 < (expansion.source i).outerWeight) :
    Squarefree (expansion.source i).first.residualDivisor.val := by
  cases expansion with
  | direct => exact family.residual_squarefree_of_outer_pos hf i hpos
  | pooled pool count index source =>
    exact pool.residual_squarefree hf (index i) (source i) (hexpansion.2.2 i) hpos

end PoolExpansion

namespace PhysicalSource

variable (source : PhysicalSource call p)

theorem activeCommon_valid (hS : Squarefree source.first.residualDivisor.val)
    (hdiv : ∀ j, source.source.coefficient j ≠ 0 →
      source.first.residualDivisor.val ∣ (source.source.ideal j).val)
    (DE : Ideal (𝓞 K) × Ideal (𝓞 K)) (hDE : DE ∈ source.activeCommon) :
    Valid source.first.residualDivisor.val (DE, ∅) := by
  obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hDE
  have hi := Finset.mem_filter.mp (Finset.mem_product.mp hij).1
  have hj := Finset.mem_filter.mp (Finset.mem_product.mp hij).2
  have hd := N8Source.squarefree_dvd_commonSupportLabel source.first.residualDivisor.val
    (source.source.ideal ij.1).val (source.source.ideal ij.2).val hS
    (source.source.ideal ij.1).property.1 (source.source.ideal ij.2).property.1
    (hdiv ij.1 hi.2) (hdiv ij.2 hj.2)
  exact ⟨supportExtract_ne_zero _ _, supportExtract_ne_zero _ _,
    commonSupportLabel_support_eq _ _, hd.1, hd.2, Finset.empty_subset _⟩

end PhysicalSource
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PoolExpansion.residual_dvd
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PoolExpansion.residual_squarefree
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PhysicalSource.activeCommon_valid
