module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondZeroTransport
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstZeroFactorization
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonTupleFibers

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Actual ordered factor tuples through the first support and the pool

The original two plain ideals and every original prime occurrence are
kept. Common-support extraction and prime-power removal operate on
each of these factors. The information lost in those actual quotients
is counted by the existing divisor and valuation allocation theorems.
The source's original column carrier is never replaced by ideal values.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

section Arithmetic

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS} {ι : Type}

/-- Internal arithmetic data constructed from the original dictionary.
Every field concerns a literal finite tuple or support extraction. -/
structure OriginalSupportFactors (G : ActualGaussSource C ι)
    (D : Ideal (𝓞 K)) (k : ℕ) where
  support : Finset (Ideal (𝓞 K))
  fullIdeal : ι → A.Exterior
  factors : ι × ι → Fin k → A.Exterior
  injective : Set.InjOn (fun ij t => (factors ij t).val)
    ((G.columns ×ˢ G.columns) : Set (ι × ι))
  product : ∀ ij ∈ G.columns ×ˢ G.columns,
    PowerfulDiagonal.tupleIdeal (fun t => (factors ij t).val) =
      (fullIdeal ij.1).val * (fullIdeal ij.2).val
  common : ∀ i ∈ G.columns, supportExtract (fullIdeal i).val support = D
  residual : ∀ i, G.ideal i = residualExterior (fullIdeal i) support

def OriginalSupportFactors.ofHEq {κ : Type}
    (G : ActualGaussSource C ι) (H : ActualGaussSource C κ)
    (htype : ι = κ) (hsource : HEq G H) (D : Ideal (𝓞 K)) (k : ℕ)
    (W : OriginalSupportFactors H D k) : OriginalSupportFactors G D k := by
  cases htype
  have he : G = H := eq_of_heq hsource
  rw [he]
  exact W

theorem OriginalSupportFactors.actualFactors
    {G : ActualGaussSource C ι} {D : Ideal (𝓞 K)} {k : ℕ}
    (W : OriginalSupportFactors G D k) (hD : D ≠ 0) :
    ∃ f : ι × ι → Fin k → Ideal (𝓞 K),
      (∀ ij ∈ G.columns ×ˢ G.columns, PowerfulDiagonal.tupleIdeal (f ij) =
        (G.ideal ij.1).val * (G.ideal ij.2).val) ∧
      ∀ v, ((G.columns ×ˢ G.columns).filter (fun ij => f ij = v)).card ≤
        idealDivisorCount (D ^ 2) ^ k := by
  have h := actual_support_residual_pair_data G.columns W.fullIdeal W.factors
    W.injective W.product W.support D hD W.common
  refine ⟨fun ij t => (actualSupportResidualFactors W.support (W.factors ij) t).val, ?_, h.2⟩
  intro ij hij
  simpa only [W.residual] using h.1 ij hij

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

def OriginalSupportFactors.main
    (d : FirstGaussPoolData C P ι) (a : ι → ℂ)
    {D : Ideal (𝓞 K)} {k : ℕ}
    (W : OriginalSupportFactors (d.directSource a) D k) :
    OriginalSupportFactors (d.mainSource a) D k where
  support := W.support
  fullIdeal := W.fullIdeal
  factors := W.factors
  injective := W.injective
  product := W.product
  common := W.common
  residual := W.residual

theorem OriginalSupportFactors.errorActualFactors
    (d : FirstGaussPoolData C P ι) (a : ι → ℂ)
    {D : Ideal (𝓞 K)} {k : ℕ}
    (W : OriginalSupportFactors (d.directSource a) D k) (hD : D ≠ 0)
    (q : ExteriorPrime A) (n : ℕ) :
    ∃ f : (d.valuationColumns q n) × (d.valuationColumns q n) → Fin k → Ideal (𝓞 K),
      (∀ ij ∈ (d.residualSource q n a).columns ×ˢ (d.residualSource q n a).columns,
        PowerfulDiagonal.tupleIdeal (f ij) =
          ((d.residualSource q n a).ideal ij.1).val * ((d.residualSource q n a).ideal ij.2).val) ∧
      ∀ v, (((d.residualSource q n a).columns ×ˢ (d.residualSource q n a).columns).filter
        (fun ij => f ij = v)).card ≤ idealDivisorCount (D ^ 2) ^ k * (n + n + 1) ^ k := by
  let cols : Finset (d.valuationColumns q n) := Finset.univ
  let full := fun i : d.valuationColumns q n => W.fullIdeal i.val
  let factors := fun ij : (d.valuationColumns q n) × (d.valuationColumns q n) =>
    W.factors (ij.1.val, ij.2.val)
  have hmem (i : d.valuationColumns q n) : i.val ∈ d.columns :=
    (Finset.mem_filter.mp i.property).1
  have hinj : Set.InjOn (fun ij t => (factors ij t).val)
      ((cols ×ˢ cols) : Set ((d.valuationColumns q n) × (d.valuationColumns q n))) := by
    intro ij _ uv _ he
    have hp : (ij.1.val, ij.2.val) = (uv.1.val, uv.2.val) := by
      apply W.injective
      · exact ⟨hmem ij.1, hmem ij.2⟩
      · exact ⟨hmem uv.1, hmem uv.2⟩
      · exact he
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hp)) (Subtype.ext (congrArg Prod.snd hp))
  have hproduct : ∀ ij ∈ cols ×ˢ cols,
      PowerfulDiagonal.tupleIdeal (fun t => (factors ij t).val) =
        (full ij.1).val * (full ij.2).val := by
    intro ij _
    exact W.product (ij.1.val, ij.2.val) (Finset.mem_product.mpr ⟨hmem ij.1, hmem ij.2⟩)
  have hcommon : ∀ i ∈ cols, supportExtract (full i).val W.support = D :=
    fun i _ => W.common i.val (hmem i)
  let Q : ∀ i : d.valuationColumns q n,
      AmplifierResidualPresentation C q n (residualExterior (full i) W.support) := fun i =>
    { residual := (d.residualPresentation q n i).residual
      generator := (d.residualPresentation q n i).generator
      generates := (d.residualPresentation q n i).generates
      reconstructed := by
        rw [← W.residual i.val]
        exact (d.residualPresentation q n i).reconstructed
      primitive := (d.residualPresentation q n i).primitive
      coprime := (d.residualPresentation q n i).coprime
      allowed := (d.residualPresentation q n i).allowed }
  have h := actual_support_amplifier_pair_data C q cols full factors hinj hproduct
    W.support D hD hcommon Q
  exact ⟨fun ij => actualResidualFactorTuple C q
    (actualSupportResidualFactors W.support (factors ij)), h.1, h.2⟩

theorem actual_factors_of_heq {κ : Type}
    (G : ActualGaussSource C ι) (H : ActualGaussSource C κ)
    (htype : ι = κ) (hsource : HEq G H) (k multiplicity : ℕ)
    (hfactor : ∃ f : κ × κ → Fin k → Ideal (𝓞 K),
      (∀ ij ∈ H.columns ×ˢ H.columns, PowerfulDiagonal.tupleIdeal (f ij) =
        (H.ideal ij.1).val * (H.ideal ij.2).val) ∧
      ∀ v, ((H.columns ×ˢ H.columns).filter (fun ij => f ij = v)).card ≤ multiplicity) :
    ∃ f : ι × ι → Fin k → Ideal (𝓞 K),
      (∀ ij ∈ G.columns ×ˢ G.columns, PowerfulDiagonal.tupleIdeal (f ij) =
        (G.ideal ij.1).val * (G.ideal ij.2).val) ∧
      ∀ v, ((G.columns ×ˢ G.columns).filter (fun ij => f ij = v)).card ≤ multiplicity := by
  cases htype
  have he : G = H := eq_of_heq hsource
  simpa only [he] using hfactor

end Arithmetic

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable (F : FirstPresentation call p)

def firstExteriorPairFactors (ij : F.source.Column × F.source.Column) :
    Fin (2 * (c.geometry.slots + 2)) → (Arithmetic.data c).Exterior :=
  call.workingRaw.originalPairExteriorFactors
    (A := Arithmetic.data c) (Γ := Arithmetic.unitSubgroup c)
    c.geometry.slots call.slots_le (F.index ij.1, F.index ij.2)

theorem firstExteriorPairFactors_val (hF : F.Realizes)
    (ij : F.source.Column × F.source.Column) (hi : ij.1 ∈ F.source.columns)
    (hj : ij.2 ∈ F.source.columns) :
    (fun t => (firstExteriorPairFactors F ij t).val) = FirstZeroProof.firstPairFactors F ij := by
  exact call.workingRaw.originalPairExteriorFactors_val
    (A := Arithmetic.data c) (Γ := Arithmetic.unitSubgroup c)
    c.geometry.slots call.slots_le (F.index ij.1, F.index ij.2)
    (FirstZeroProof.first_index_mem F hF ij.1 hi)
    (FirstZeroProof.first_index_mem F hF ij.2 hj)

def firstKeySelected (key : FirstCauchyKey F) : Ideal (𝓞 K) :=
  if FirstCauchyKey.side key then key.1.val.2 else key.1.val.1

theorem firstKeySelected_ne_zero (key : FirstCauchyKey F) : firstKeySelected F key ≠ 0 := by
  unfold firstKeySelected
  split_ifs
  · rw [← (FirstCauchyKey.block key).common_right]
    exact (primePowerProduct (FirstCauchyKey.block key).primes
      (FirstCauchyKey.block key).rightMultiplicity).property.1
  · rw [← (FirstCauchyKey.block key).common_left]
    exact (primePowerProduct (FirstCauchyKey.block key).primes
      (FirstCauchyKey.block key).leftMultiplicity).property.1

def first_key_support_factors (hF : F.Realizes) (key : FirstCauchyKey F) :
    OriginalSupportFactors
      ((FirstCauchyKey.data key).directSource (FirstCauchyKey.coefficient key))
      (firstKeySelected F key) (2 * (c.geometry.slots + 2)) where
  support := primeSupport key.1.val.1
  fullIdeal := F.source.ideal
  factors := firstExteriorPairFactors F
  injective := by
    intro ij hij uv huv he
    have hij' : ij ∈ (FirstCauchyKey.data key).columns ×ˢ (FirstCauchyKey.data key).columns :=
      Finset.mem_product.mpr hij
    have huv' : uv ∈ (FirstCauchyKey.data key).columns ×ˢ (FirstCauchyKey.data key).columns :=
      Finset.mem_product.mpr huv
    have hijval := firstExteriorPairFactors_val F hF ij
      (first_key_column_mem F key ij.1 (Finset.mem_product.mp hij').1)
      (first_key_column_mem F key ij.2 (Finset.mem_product.mp hij').2)
    have huvval := firstExteriorPairFactors_val F hF uv
      (first_key_column_mem F key uv.1 (Finset.mem_product.mp huv').1)
      (first_key_column_mem F key uv.2 (Finset.mem_product.mp huv').2)
    exact FirstZeroProof.firstPairFactors_injective F
      (hijval.symm.trans (he.trans huvval))
  product := by
    intro ij hij
    have hi := first_key_column_mem F key ij.1 (Finset.mem_product.mp hij).1
    have hj := first_key_column_mem F key ij.2 (Finset.mem_product.mp hij).2
    rw [firstExteriorPairFactors_val F hF ij hi hj]
    exact FirstZeroProof.firstPairFactors_product F hF ij (Finset.mem_product.mpr ⟨hi, hj⟩)
  common := by
    intro i hi
    cases hs : FirstCauchyKey.side key
    · simp only [FirstCauchyKey.data, hs, Bool.false_eq_true, if_false,
        DirectGaussData.directSource] at hi
      rw [(FirstCauchyKey.piece key).left_columns] at hi
      simpa only [firstKeySelected, hs, Bool.false_eq_true, if_false] using
        (Finset.mem_filter.mp hi).2
    · simp only [FirstCauchyKey.data, hs, if_true, DirectGaussData.directSource] at hi
      rw [(FirstCauchyKey.piece key).right_columns] at hi
      simpa only [firstKeySelected, hs, if_true] using (Finset.mem_filter.mp hi).2
  residual := by
    intro i
    apply Subtype.ext
    cases hs : FirstCauchyKey.side key
    · simp only [FirstCauchyKey.data, hs, Bool.false_eq_true, if_false,
        DirectGaussData.directSource]
      have hideal : ((FirstCauchyKey.piece key).leftData.ideal i).val =
          supportResidual (F.source.ideal i).val (primeSupport key.1.val.1) :=
        (congrArg (fun f : F.source.Column → (Arithmetic.data c).Exterior => (f i).val)
          (FirstCauchyKey.piece key).left_ideal).trans
            ((FirstCauchyKey.block key).left_residual i)
      exact hideal
    · simp only [FirstCauchyKey.data, hs, if_true, DirectGaussData.directSource]
      have hideal : ((FirstCauchyKey.piece key).rightData.ideal i).val =
          supportResidual (F.source.ideal i).val (primeSupport key.1.val.1) :=
        (congrArg (fun f : F.source.Column → (Arithmetic.data c).Exterior => (f i).val)
          (FirstCauchyKey.piece key).right_ideal).trans
            ((FirstCauchyKey.block key).right_residual i)
      exact hideal

variable {F} {family : FirstCauchyFamily F}

def first_family_support_factors (hF : F.Realizes) (hfamily : family.Realizes)
    (i : Fin family.count) :
    OriginalSupportFactors (family.source i).source (family.source i).first.selected.val
      (2 * (c.geometry.slots + 2)) := by
  rw [hfamily.selected i]
  exact OriginalSupportFactors.ofHEq (family.source i).source
    ((FirstCauchyKey.data (family.index i)).directSource
      (FirstCauchyKey.coefficient (family.index i)))
    (hfamily.column i) (hfamily.source i) _ _ (first_key_support_factors F hF (family.index i))

theorem first_family_actual_factors (hF : F.Realizes) (hfamily : family.Realizes)
    (i : Fin family.count) :
    ∃ f : (family.source i).Column × (family.source i).Column →
        Fin (2 * (c.geometry.slots + 2)) → Ideal (𝓞 K),
      (∀ ij ∈ (family.source i).source.columns ×ˢ (family.source i).source.columns,
        PowerfulDiagonal.tupleIdeal (f ij) =
          ((family.source i).source.ideal ij.1).val * ((family.source i).source.ideal ij.2).val) ∧
      ∀ v, (((family.source i).source.columns ×ˢ (family.source i).source.columns).filter
        (fun ij => f ij = v)).card ≤
          idealDivisorCount ((family.source i).first.selected.val ^ 2) ^
            (2 * (c.geometry.slots + 2)) :=
  (first_family_support_factors hF hfamily i).actualFactors
    (nonZeroDivisors.coe_ne_zero (family.source i).first.selected)

/-- A single finite multiplicity bound covers the direct and all
three actual amplifier valuations. It depends on the original selected
common ideal, whose norm is controlled before the second zero count. -/
def secondFactorMultiplicity (source : PhysicalSource call p) : ℕ :=
  idealDivisorCount (source.first.selected.val ^ 2) ^ (2 * (c.geometry.slots + 2)) *
    15 ^ (2 * (c.geometry.slots + 2))

private theorem firstMultiplicity_le_second (source : PhysicalSource call p) :
    idealDivisorCount (source.first.selected.val ^ 2) ^ (2 * (c.geometry.slots + 2)) ≤
      secondFactorMultiplicity source := by
  simpa only [Nat.mul_one, secondFactorMultiplicity] using
    Nat.mul_le_mul_left
      (idealDivisorCount (source.first.selected.val ^ 2) ^ (2 * (c.geometry.slots + 2)))
      (one_le_pow₀ (by norm_num : 1 ≤ (15 : ℕ)) : 1 ≤ 15 ^ (2 * (c.geometry.slots + 2)))

theorem main_actual_factors (hF : F.Realizes) (hfamily : family.Realizes)
    (P : PoolPresentation family) (hP : P.Realizes)
    (i : Fin family.count) (source : PhysicalSource call p)
    (hsource : P.MainOrigin i source) :
    ∃ f : source.Column × source.Column → Fin (2 * (c.geometry.slots + 2)) → Ideal (𝓞 K),
      (∀ ij ∈ source.source.columns ×ˢ source.source.columns,
        PowerfulDiagonal.tupleIdeal (f ij) =
          (source.source.ideal ij.1).val * (source.source.ideal ij.2).val) ∧
      ∀ v, ((source.source.columns ×ˢ source.source.columns).filter
        (fun ij => f ij = v)).card ≤ secondFactorMultiplicity source := by
  rcases hsource with ⟨htype, hsource, hancestor, hmultiplier, hkernel, hpoint, houter, hfirst⟩
  have hselected : source.first.selected = (family.source i).first.selected :=
    congrArg (fun first => first.selected) hfirst
  have W : OriginalSupportFactors ((P.data i).directSource (family.source i).source.coefficient)
      (family.source i).first.selected.val (2 * (c.geometry.slots + 2)) := by
    rw [hP.original i]
    exact first_family_support_factors hF hfamily i
  obtain ⟨f, hproduct, hfiber⟩ := (W.main (P.data i) (family.source i).source.coefficient).actualFactors
    (nonZeroDivisors.coe_ne_zero (family.source i).first.selected)
  apply actual_factors_of_heq source.source
    ((P.data i).mainSource (family.source i).source.coefficient) htype hsource _ _
  refine ⟨f, hproduct, fun v => (hfiber v).trans ?_⟩
  simpa only [secondFactorMultiplicity, hselected] using firstMultiplicity_le_second (family.source i)

theorem error_actual_factors (hF : F.Realizes) (hfamily : family.Realizes)
    (P : PoolPresentation family) (hP : P.Realizes)
    (i : Fin family.count) (q : P.pool.primes) (e : AmplifierValuation)
    (source : PhysicalSource call p) (hsource : P.ErrorOrigin i q e source) :
    ∃ f : source.Column × source.Column → Fin (2 * (c.geometry.slots + 2)) → Ideal (𝓞 K),
      (∀ ij ∈ source.source.columns ×ˢ source.source.columns,
        PowerfulDiagonal.tupleIdeal (f ij) =
          (source.source.ideal ij.1).val * (source.source.ideal ij.2).val) ∧
      ∀ v, ((source.source.columns ×ˢ source.source.columns).filter
        (fun ij => f ij = v)).card ≤ secondFactorMultiplicity source := by
  rcases hsource with ⟨htype, hsource, hancestor, hmultiplier, hkernel, hpoint, houter,
    hselected, hopposite, hcomplementary, hresidual, hfirstElement, hright, hpower,
    hretained, htag, hdeletion, hpaid⟩
  have W : OriginalSupportFactors ((P.data i).directSource (family.source i).source.coefficient)
      (family.source i).first.selected.val (2 * (c.geometry.slots + 2)) := by
    rw [hP.original i]
    exact first_family_support_factors hF hfamily i
  obtain ⟨f, hproduct, hfiber⟩ := W.errorActualFactors (P.data i)
    (family.source i).source.coefficient
    (nonZeroDivisors.coe_ne_zero (family.source i).first.selected) q.val e.multiplicity
  apply actual_factors_of_heq source.source
    ((P.data i).residualSource q.val e.multiplicity (family.source i).source.coefficient)
    htype hsource _ _
  refine ⟨f, hproduct, fun v => (hfiber v).trans ?_⟩
  have hn : e.multiplicity + e.multiplicity + 1 ≤ 15 := by
    cases e <;> norm_num [AmplifierValuation.multiplicity]
  simpa only [secondFactorMultiplicity, hselected] using
    Nat.mul_le_mul_left
      (idealDivisorCount ((family.source i).first.selected.val ^ 2) ^
        (2 * (c.geometry.slots + 2)))
      (Nat.pow_le_pow_left hn (2 * (c.geometry.slots + 2)))

theorem origin_actual_factors (hF : F.Realizes) (hfamily : family.Realizes)
    (P : PoolPresentation family) (hP : P.Realizes)
    (index : P.Index) (source : PhysicalSource call p) (hsource : P.Origin index source) :
    ∃ f : source.Column × source.Column → Fin (2 * (c.geometry.slots + 2)) → Ideal (𝓞 K),
      (∀ ij ∈ source.source.columns ×ˢ source.source.columns,
        PowerfulDiagonal.tupleIdeal (f ij) =
          (source.source.ideal ij.1).val * (source.source.ideal ij.2).val) ∧
      ∀ v, ((source.source.columns ×ˢ source.source.columns).filter
        (fun ij => f ij = v)).card ≤ secondFactorMultiplicity source := by
  rcases index with ⟨i, tag⟩
  cases tag with
  | inl unit => exact main_actual_factors hF hfamily P hP i source hsource
  | inr qe => exact error_actual_factors hF hfamily P hP i qe.1 qe.2 source hsource

theorem expansion_actual_factors (hF : F.Realizes) (hfamily : family.Realizes)
    (expansion : PoolExpansion family) (hexpansion : expansion.Realizes) :
    ∀ i, ∃ f : (expansion.source i).Column × (expansion.source i).Column →
        Fin (2 * (c.geometry.slots + 2)) → Ideal (𝓞 K),
      (∀ ij ∈ (expansion.source i).source.columns ×ˢ (expansion.source i).source.columns,
        PowerfulDiagonal.tupleIdeal (f ij) =
          ((expansion.source i).source.ideal ij.1).val * ((expansion.source i).source.ideal ij.2).val) ∧
      ∀ v, (((expansion.source i).source.columns ×ˢ (expansion.source i).source.columns).filter
        (fun ij => f ij = v)).card ≤ secondFactorMultiplicity (expansion.source i) := by
  cases expansion with
  | direct =>
    intro i
    obtain ⟨f, hproduct, hfiber⟩ := first_family_actual_factors hF hfamily i
    exact ⟨f, hproduct, fun v => (hfiber v).trans (firstMultiplicity_le_second (family.source i))⟩
  | pooled P count index source =>
    intro i
    exact origin_actual_factors hF hfamily P hexpansion.2.1 (index i) (source i)
      (hexpansion.2.2 i)

theorem second_factor_multiplicity_uniform (c : TargetContext K)
    (p : SourceParameters c) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ {call : Call c} (source : PhysicalSource call p),
      (Ideal.absNorm source.first.selected.val : ℝ) ≤ call.base ^ (3 : ℝ) →
      (secondFactorMultiplicity source : ℝ) ≤ Cbound * call.base ^ ε := by
  obtain ⟨Cbound, hCbound, hcount⟩ := common_amplifier_fiber_subpower
    (K := K) (2 * (c.geometry.slots + 2)) 3 ε (by norm_num) hε
  refine ⟨Cbound, hCbound, ?_⟩
  intro call source hnorm
  have h := hcount call.base call.domain.scale.le source.first.selected.val 7 (by norm_num) hnorm
  simpa only [secondFactorMultiplicity, show 7 + 7 + 1 = (15 : ℕ) by omega] using h

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof
