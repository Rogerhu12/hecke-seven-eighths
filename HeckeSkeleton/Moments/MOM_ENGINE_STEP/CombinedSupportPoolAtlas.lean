import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AmplifierPoolReindex
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SourceCartesianAtlas

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums UniqueFactorizationMonoid
open DedekindZetaZeroFree.LargeSieve
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

theorem supportResidual_twice (I : Ideal (𝓞 K))
    (S T : Finset (Ideal (𝓞 K))) :
    supportResidual (supportResidual I S) T = supportResidual I (S ∪ T) := by
  change ((normalizedFactors (supportResidual I S)).filter (fun Q => Q ∉ T)).prod =
    ((normalizedFactors I).filter (fun Q => Q ∉ S ∪ T)).prod
  rw [supportResidual_factors]
  congr 1
  apply Multiset.ext.mpr
  intro Q
  by_cases hS : Q ∈ S <;> by_cases hT : Q ∈ T <;>
    simp [Multiset.count_filter, hS, hT]

theorem supportExtract_union_left (I : Ideal (𝓞 K))
    (S T : Finset (Ideal (𝓞 K))) :
    supportExtract (supportExtract I (S ∪ T)) S = supportExtract I S := by
  change ((normalizedFactors (supportExtract I (S ∪ T))).filter (fun Q => Q ∈ S)).prod =
    ((normalizedFactors I).filter (fun Q => Q ∈ S)).prod
  rw [supportExtract_factors]
  congr 1
  apply Multiset.ext.mpr
  intro Q
  by_cases hS : Q ∈ S <;> by_cases hT : Q ∈ T <;>
    simp [Multiset.count_filter, hS, hT]

theorem supportExtract_union_factor (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (S T : Finset (Ideal (𝓞 K))) :
    supportExtract I (S ∪ T) =
      supportExtract I S * supportExtract (supportResidual I S) T := by
  apply mul_right_cancel₀ (supportResidual_ne_zero I (S ∪ T))
  calc
    supportExtract I (S ∪ T) * supportResidual I (S ∪ T) = I :=
      support_reconstruct I hI (S ∪ T)
    _ = (supportExtract I S * supportExtract (supportResidual I S) T) *
        supportResidual I (S ∪ T) := by
      rw [mul_assoc, ← supportResidual_twice I S T,
        support_reconstruct (supportResidual I S) (supportResidual_ne_zero I S) T,
        support_reconstruct I hI S]

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {ι : Type*} {originalColumns : Finset ι} {originalIdeal : ι → A.Exterior}

namespace FirstGaussPoolData

variable (d : FirstGaussPoolData C P ι)
variable (T : SourceCartesianAtlas originalColumns originalIdeal)

def mainAtlasForLabel
    (S : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (hcolumns : d.columns =
      originalColumns.filter (fun i => supportExtract (originalIdeal i).val S = D))
    (hideal : ∀ i, (d.ideal i).val = supportResidual (originalIdeal i).val S)
    (c : ι → ℂ) (a : T.labels S D) :
    SourceCartesianAtlas
      ((d.mainSource c).columns.filter
        (fun i => T.reindex.supportExtractionLabel S i = a.val))
      (d.mainSource c).ideal := by
  change SourceCartesianAtlas
    (d.columns.filter (fun i => T.reindex.supportExtractionLabel S i = a.val)) d.ideal
  rw [hcolumns]
  apply SourceCartesianAtlas.ofReindex
    (T.residualReindex S D d.ideal (fun i _ => hideal i) a)
  obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp a.property
  exact ⟨i, Finset.mem_filter.mpr ⟨hi, hia⟩⟩

theorem sum_mainSource_labels {M : Type*} [AddCommMonoid M]
    (S : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (hcolumns : d.columns =
      originalColumns.filter (fun i => supportExtract (originalIdeal i).val S = D))
    (c : ι → ℂ) (f : ι → M) :
    (∑ i ∈ (d.mainSource c).columns, f i) =
      ∑ a : T.labels S D, ∑ i ∈ (d.mainSource c).columns.filter
        (fun i => T.reindex.supportExtractionLabel S i = a.val), f i := by
  change (∑ i ∈ d.columns, f i) =
    ∑ a : T.labels S D, ∑ i ∈ d.columns.filter
      (fun i => T.reindex.supportExtractionLabel S i = a.val), f i
  rw [hcolumns]
  exact T.sum_common S D f

def combinedLabels (S : Finset (Ideal (𝓞 K))) (p : ExteriorPrime A) (n : ℕ) :
    Finset (SupportCartesian.ExtractionKey K T.slotCount) :=
  (d.valuationColumns p n).image
    (T.reindex.supportExtractionLabel (S ∪ {p.val.asIdeal}))

theorem combinedBranch_subset_valuation
    (S : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (hcolumns : d.columns =
      originalColumns.filter (fun i => supportExtract (originalIdeal i).val S = D))
    (hideal : ∀ i, (d.ideal i).val = supportResidual (originalIdeal i).val S)
    (p : ExteriorPrime A) (n : ℕ)
    (b : SupportCartesianBranch T.reindex.plain₁ T.reindex.plain₂ T.reindex.slots
      (S ∪ {p.val.asIdeal}))
    (hw : T.reindex.index b.witness ∈ d.valuationColumns p n) :
    b.originalColumns.image T.reindex.index ⊆ d.valuationColumns p n := by
  intro i hi
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
  have he : supportExtract (originalIdeal (T.reindex.index x)).val (S ∪ {p.val.asIdeal}) =
      supportExtract (originalIdeal (T.reindex.index b.witness)).val (S ∪ {p.val.asIdeal}) := by
    rw [T.reindex.ideal_product x (b.original_subset hx),
      T.reindex.ideal_product b.witness (b.original_subset b.witness_mem),
      b.extract_ideal x hx, b.extract_ideal b.witness b.witness_mem]
  apply Finset.mem_filter.mpr
  constructor
  · rw [hcolumns]
    apply Finset.mem_filter.mpr
    refine ⟨T.reindex.maps x (b.original_subset hx), ?_⟩
    have hbase := congrArg (fun I : Ideal (𝓞 K) => supportExtract I S) he
    simp only [supportExtract_union_left] at hbase
    have hw₀ := (Finset.mem_filter.mp hw).1
    rw [hcolumns] at hw₀
    exact hbase.trans (Finset.mem_filter.mp hw₀).2
  · have hc := congrArg (fun I : Ideal (𝓞 K) =>
        (normalizedFactors I).count p.val.asIdeal) he
    simp only [supportExtract_count, Finset.mem_union,
      Finset.mem_singleton_self, or_true, if_true] at hc
    have hwν := (Finset.mem_filter.mp hw).2
    change (normalizedFactors (d.ideal (T.reindex.index x)).val).count p.val.asIdeal = n
    change (normalizedFactors (d.ideal (T.reindex.index b.witness)).val).count
      p.val.asIdeal = n at hwν
    rw [hideal (T.reindex.index x), supportResidual_count]
    rw [hideal (T.reindex.index b.witness), supportResidual_count] at hwν
    by_cases hp : p.val.asIdeal ∈ S
    · simpa only [hp, if_true] using hwν
    · simp only [hp, if_false] at hwν ⊢
      exact hc.trans hwν

def residualSource_cartesianBranch_of_original_support
    (S : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (hcolumns : d.columns =
      originalColumns.filter (fun i => supportExtract (originalIdeal i).val S = D))
    (hideal : ∀ i, (d.ideal i).val = supportResidual (originalIdeal i).val S)
    (p : ExteriorPrime A) (n : ℕ) (c : ι → ℂ)
    (b : SupportCartesianBranch T.reindex.plain₁ T.reindex.plain₂ T.reindex.slots
      (S ∪ {p.val.asIdeal}))
    (hw : T.reindex.index b.witness ∈ d.valuationColumns p n) :
    CartesianSourceReindex
      ((b.originalColumns.image T.reindex.index).subtype
        (fun i => i ∈ d.valuationColumns p n))
      (d.residualSource p n c).ideal b.keep.card := by
  let B := (T.reindex.supportResidualBranch (S ∪ {p.val.asIdeal}) b).subtypeSource
    (d.valuationColumns p n)
    (d.combinedBranch_subset_valuation T S D hcolumns hideal p n b hw)
    ⟨T.reindex.index b.witness,
      Finset.mem_image.mpr ⟨b.witness, b.witness_mem, rfl⟩⟩
  exact B.congrIdeal (d.residualSource p n c).ideal (by
    intro i _
    calc
      ((d.residualSource p n c).ideal i).val =
          supportResidual (d.ideal i.val).val {p.val.asIdeal} :=
        (d.residualPresentation p n i).residual_eq_supportResidual
      _ = supportResidual (supportResidual (originalIdeal i.val).val S) {p.val.asIdeal} := by
        rw [hideal i.val]
      _ = supportResidual (originalIdeal i.val).val (S ∪ {p.val.asIdeal}) :=
        supportResidual_twice _ _ _)

theorem residualSource_branch_filter_of_original_support
    (S : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (hcolumns : d.columns =
      originalColumns.filter (fun i => supportExtract (originalIdeal i).val S = D))
    (p : ExteriorPrime A) (n : ℕ)
    (b : SupportCartesianBranch T.reindex.plain₁ T.reindex.plain₂ T.reindex.slots
      (S ∪ {p.val.asIdeal})) :
    (b.originalColumns.image T.reindex.index).subtype
        (fun i => i ∈ d.valuationColumns p n) =
      Finset.univ.filter (fun i : d.valuationColumns p n =>
        T.reindex.supportExtractionLabel (S ∪ {p.val.asIdeal}) i.val = b.key) := by
  rw [← T.reindex.supportExtractionLabel_fibre (S ∪ {p.val.asIdeal}) b]
  ext i
  have hi := (Finset.mem_filter.mp i.property).1
  rw [hcolumns] at hi
  have hi₀ : i.val ∈ originalColumns := (Finset.mem_filter.mp hi).1
  simp only [Finset.mem_subtype, Finset.mem_filter, Finset.mem_univ, true_and, hi₀]

theorem exists_combinedBranch_for_label
    (S : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (hcolumns : d.columns =
      originalColumns.filter (fun i => supportExtract (originalIdeal i).val S = D))
    (p : ExteriorPrime A) (n : ℕ) (a : d.combinedLabels T S p n) :
    ∃ b : SupportCartesianBranch T.reindex.plain₁ T.reindex.plain₂ T.reindex.slots
        (S ∪ {p.val.asIdeal}),
      b.key = a.val ∧ T.reindex.index b.witness ∈ d.valuationColumns p n := by
  obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp a.property
  have hi₀ := (Finset.mem_filter.mp hi).1
  rw [hcolumns] at hi₀
  obtain ⟨x, hx, hxi⟩ := T.reindex.surjective i (Finset.mem_filter.mp hi₀).1
  let b := SupportCartesianBranch.ofColumn (P := S ∪ {p.val.asIdeal})
    T.plain₁_nonzero T.plain₂_nonzero x hx
  refine ⟨b, ?_, ?_⟩
  · change SupportCartesian.extractionKey (S ∪ {p.val.asIdeal}) x = a.val
    rw [← T.reindex.supportExtractionLabel_index (S ∪ {p.val.asIdeal}) x hx, hxi]
    exact hia
  · change T.reindex.index x ∈ d.valuationColumns p n
    rwa [hxi]

def combinedBranchForLabel
    (S : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (hcolumns : d.columns =
      originalColumns.filter (fun i => supportExtract (originalIdeal i).val S = D))
    (p : ExteriorPrime A) (n : ℕ) (a : d.combinedLabels T S p n) :
    SupportCartesianBranch T.reindex.plain₁ T.reindex.plain₂ T.reindex.slots
      (S ∪ {p.val.asIdeal}) :=
  Classical.choose (d.exists_combinedBranch_for_label T S D hcolumns p n a)

theorem combinedBranchForLabel_spec
    (S : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (hcolumns : d.columns =
      originalColumns.filter (fun i => supportExtract (originalIdeal i).val S = D))
    (p : ExteriorPrime A) (n : ℕ) (a : d.combinedLabels T S p n) :
    (d.combinedBranchForLabel T S D hcolumns p n a).key = a.val ∧
      T.reindex.index (d.combinedBranchForLabel T S D hcolumns p n a).witness ∈
        d.valuationColumns p n :=
  Classical.choose_spec (d.exists_combinedBranch_for_label T S D hcolumns p n a)

def combinedAtlasForLabel
    (S : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (hcolumns : d.columns =
      originalColumns.filter (fun i => supportExtract (originalIdeal i).val S = D))
    (hideal : ∀ i, (d.ideal i).val = supportResidual (originalIdeal i).val S)
    (p : ExteriorPrime A) (n : ℕ) (c : ι → ℂ)
    (a : d.combinedLabels T S p n) :
    SourceCartesianAtlas
      (Finset.univ.filter (fun i : d.valuationColumns p n =>
        T.reindex.supportExtractionLabel (S ∪ {p.val.asIdeal}) i.val = a.val))
      (d.residualSource p n c).ideal := by
  let b := d.combinedBranchForLabel T S D hcolumns p n a
  have hb := d.combinedBranchForLabel_spec T S D hcolumns p n a
  have he := d.residualSource_branch_filter_of_original_support T S D hcolumns p n b
  rw [hb.1] at he
  rw [← he]
  apply SourceCartesianAtlas.ofReindex
    (d.residualSource_cartesianBranch_of_original_support T S D hcolumns hideal p n c b hb.2)
  refine ⟨⟨T.reindex.index b.witness, hb.2⟩, ?_⟩
  exact Finset.mem_subtype.mpr
    (Finset.mem_image.mpr ⟨b.witness, b.witness_mem, rfl⟩)

theorem sum_residualSource_combinedLabels {M : Type*} [AddCommMonoid M]
    (S : Finset (Ideal (𝓞 K))) (p : ExteriorPrime A) (n : ℕ)
    (f : d.valuationColumns p n → M) :
    (∑ i : d.valuationColumns p n, f i) =
      ∑ a : d.combinedLabels T S p n,
        ∑ i ∈ Finset.univ.filter (fun i : d.valuationColumns p n =>
          T.reindex.supportExtractionLabel (S ∪ {p.val.asIdeal}) i.val = a.val), f i := by
  calc
    _ = ∑ a ∈ d.combinedLabels T S p n,
        ∑ i ∈ Finset.univ.filter (fun i : d.valuationColumns p n =>
          T.reindex.supportExtractionLabel (S ∪ {p.val.asIdeal}) i.val = a), f i :=
      (Finset.sum_fiberwise_of_maps_to
        (fun i _ => Finset.mem_image_of_mem
          (T.reindex.supportExtractionLabel (S ∪ {p.val.asIdeal})) i.property) f).symm
    _ = _ := (Finset.sum_coe_sort _ _).symm

theorem combined_extract_of_mem
    (S : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (hcolumns : d.columns =
      originalColumns.filter (fun i => supportExtract (originalIdeal i).val S = D))
    (hideal : ∀ i, (d.ideal i).val = supportResidual (originalIdeal i).val S)
    (p : ExteriorPrime A) (n : ℕ) (i : ι) (hi : i ∈ d.valuationColumns p n) :
    supportExtract (originalIdeal i).val (S ∪ {p.val.asIdeal}) = D * p.val.asIdeal ^ n := by
  have hi₀ := (Finset.mem_filter.mp hi).1
  rw [hcolumns] at hi₀
  have hcommon := (Finset.mem_filter.mp hi₀).2
  have hν := (Finset.mem_filter.mp hi).2
  rw [supportExtract_union_factor _ (originalIdeal i).property.1, hcommon,
    ← hideal i, supportExtract_singleton_power]
  change D * p.val.asIdeal ^ MaskedQuotientCRT.primeExponent p (d.ideal i) = _
  rw [hν]

theorem combinedLabels_card_le
    (S : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) (hD : D ≠ 0)
    (hcolumns : d.columns =
      originalColumns.filter (fun i => supportExtract (originalIdeal i).val S = D))
    (hideal : ∀ i, (d.ideal i).val = supportResidual (originalIdeal i).val S)
    (p : ExteriorPrime A) (n : ℕ) :
    (d.combinedLabels T S p n).card ≤
      (idealDivisors (D * p.val.asIdeal ^ n)).card ^ (T.slotCount + 2) := by
  have hsub : d.combinedLabels T S p n ⊆
      T.labels (S ∪ {p.val.asIdeal}) (D * p.val.asIdeal ^ n) := by
    intro a ha
    obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp ha
    have hi₀ := (Finset.mem_filter.mp hi).1
    rw [hcolumns] at hi₀
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hi₀).1,
        d.combined_extract_of_mem S D hcolumns hideal p n i hi⟩, hia⟩
  exact (Finset.card_le_card hsub).trans
    (T.labels_card_le (S ∪ {p.val.asIdeal}) (D * p.val.asIdeal ^ n)
      (mul_ne_zero hD (pow_ne_zero n p.val.ne_bot)))

end FirstGaussPoolData

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.supportResidual_twice
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.combinedAtlasForLabel
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.sum_residualSource_combinedLabels
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.combinedLabels_card_le
