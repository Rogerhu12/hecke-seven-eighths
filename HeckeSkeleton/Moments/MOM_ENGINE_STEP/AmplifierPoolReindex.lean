import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AmplifierSupportDictionary
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SupportKernelPartition
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolSecondStage

/-! Actual pool-error source dictionaries on retained occurrence branches. -/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckePort.Moments HeckePort.Moments.Support UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K] {A : SArithmeticData K}
variable {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior} {k : ℕ}

namespace CartesianSourceReindex

variable (R : CartesianSourceReindex columns ideal k)

def subtypeIndex (T : Finset ι) (hT : columns ⊆ T) (hne : columns.Nonempty)
    (x : AllocationColumn K k) : T :=
  if hx : R.index x ∈ T then ⟨R.index x, hx⟩
  else ⟨hne.choose, hT hne.choose_spec⟩

theorem subtypeIndex_val (T : Finset ι) (hT : columns ⊆ T) (hne : columns.Nonempty)
    (x : AllocationColumn K k) (hx : x ∈ R.cartesian) :
    (R.subtypeIndex T hT hne x).val = R.index x := by
  rw [subtypeIndex, dif_pos (hT (R.maps x hx))]

/-- Only the original indices are lifted.  The source support is the
actual finite subtype support, with no multiplicity loss. -/
def subtypeSource (T : Finset ι) (hT : columns ⊆ T) (hne : columns.Nonempty) :
    CartesianSourceReindex (columns.subtype (fun i => i ∈ T))
      (fun i : T => ideal i.val) k where
  plain₁ := R.plain₁
  plain₂ := R.plain₂
  slots := R.slots
  index := R.subtypeIndex T hT hne
  maps x hx := Finset.mem_subtype.mpr (by
    rw [R.subtypeIndex_val T hT hne x hx]
    exact R.maps x hx)
  injective := by
    intro x hx y hy he
    apply R.injective hx hy
    have hv := congrArg Subtype.val he
    simpa only [R.subtypeIndex_val T hT hne x hx,
      R.subtypeIndex_val T hT hne y hy] using hv
  surjective := by
    intro i hi
    obtain ⟨x, hx, hxi⟩ := R.surjective i.val (Finset.mem_subtype.mp hi)
    exact ⟨x, hx, Subtype.ext ((R.subtypeIndex_val T hT hne x hx).trans hxi)⟩
  ideal_product := by
    intro x hx
    rw [R.subtypeIndex_val T hT hne x hx]
    exact R.ideal_product x hx

end CartesianSourceReindex

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces} {C : A.GeneralArithmeticContext σ η hS}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

namespace FirstGaussPoolData

variable (d : FirstGaussPoolData C P ι)
variable (R : CartesianSourceReindex d.columns d.ideal k)
variable (p : ExteriorPrime A) (n : ℕ)
variable (b : SupportCartesianBranch R.plain₁ R.plain₂ R.slots {p.val.asIdeal})

/-- Fixing the extracted occurrence tuple fixes the whole valuation.
Only the actual witness needs to carry the original error label. -/
theorem supportBranch_subset_valuation
    (hν : primeExponent p (d.ideal (R.index b.witness)) = n) :
    b.originalColumns.image R.index ⊆ d.valuationColumns p n := by
  intro i hi
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
  apply Finset.mem_filter.mpr
  refine ⟨R.maps x (b.original_subset hx), ?_⟩
  have he : supportExtract (d.ideal (R.index x)).val {p.val.asIdeal} =
      supportExtract (d.ideal (R.index b.witness)).val {p.val.asIdeal} := by
    rw [R.ideal_product x (b.original_subset hx),
      R.ideal_product b.witness (b.original_subset b.witness_mem),
      b.extract_ideal x hx, b.extract_ideal b.witness b.witness_mem]
  have hc := congrArg (fun I : Ideal (𝓞 K) => (normalizedFactors I).count p.val.asIdeal) he
  simp only [supportExtract_count, Finset.mem_singleton_self, if_true] at hc
  exact hc.trans hν

theorem supportBranch_nonempty :
    (b.originalColumns.image R.index).Nonempty :=
  ⟨R.index b.witness, Finset.mem_image.mpr ⟨b.witness, b.witness_mem, rfl⟩⟩

/-- The source has exactly PoolSecondStage's valuation-subtype index,
actual residual ideal, and fixed whole coefficient index. -/
def residualSource_cartesianBranch
    (c : ι → ℂ) (hν : primeExponent p (d.ideal (R.index b.witness)) = n) :
    CartesianSourceReindex
      ((b.originalColumns.image R.index).subtype (fun i => i ∈ d.valuationColumns p n))
      (d.residualSource p n c).ideal b.keep.card := by
  let B := (R.supportResidualBranch {p.val.asIdeal} b).subtypeSource
    (d.valuationColumns p n) (d.supportBranch_subset_valuation R p n b hν)
    (d.supportBranch_nonempty R p b)
  exact B.congrIdeal (d.residualSource p n c).ideal (by
    intro i hi
    exact (d.residualPresentation p n i).residual_eq_supportResidual)

/-- The actual finite subtype branch is precisely the label filter
used by the measured kernel partition. -/
theorem residualSource_branch_filter :
    (b.originalColumns.image R.index).subtype (fun i => i ∈ d.valuationColumns p n) =
      Finset.univ.filter (fun i : d.valuationColumns p n =>
        R.supportExtractionLabel {p.val.asIdeal} i.val = b.key) := by
  rw [← R.supportExtractionLabel_fibre {p.val.asIdeal} b]
  ext i
  have hi : i.val ∈ d.columns := (Finset.mem_filter.mp i.property).1
  simp only [Finset.mem_subtype, Finset.mem_filter, Finset.mem_univ, true_and, hi]

end FirstGaussPoolData

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CartesianSourceReindex.subtypeSource
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.residualSource_cartesianBranch
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.residualSource_branch_filter

