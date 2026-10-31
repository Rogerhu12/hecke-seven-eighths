import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SupportKernelPartition

/-!
# Canonical occurrence partitions of a common-support source

A source atlas is the primitive finite EXPANSION dictionary for the
original two plain factors and all original prime slots.  Its only
additional facts say that the original plain ideals are nonzero.
Every common-support label, residual support, retained slot set and
residual bijection below is computed from that original dictionary.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K] {A : SArithmeticData K}
variable {ι κ : Type*}

/-- Primitive original-column data, before common-support extraction.
There is no polynomial identity, energy estimate or residual injection
among the inputs. -/
structure SourceCartesianAtlas (columns : Finset ι) (ideal : ι → A.Exterior) where
  slotCount : ℕ
  reindex : CartesianSourceReindex columns ideal slotCount
  plain₁_nonzero : ∀ I ∈ reindex.plain₁, I ≠ 0
  plain₂_nonzero : ∀ I ∈ reindex.plain₂, I ≠ 0

namespace SourceCartesianAtlas

variable {columns : Finset ι} {ideal : ι → A.Exterior}
variable (T : SourceCartesianAtlas columns ideal)

/-- Nonempty original source columns force both entire plain supports
of their Cartesian dictionary to consist of nonzero ideals. -/
private theorem reindex_plain_nonzero {n : ℕ}
    (R : CartesianSourceReindex columns ideal n) (hne : columns.Nonempty) :
    (∀ I ∈ R.plain₁, I ≠ 0) ∧ (∀ J ∈ R.plain₂, J ≠ 0) := by
  obtain ⟨i, hi⟩ := hne
  obtain ⟨x, hx, _⟩ := R.surjective i hi
  have hp := Finset.mem_product.mp hx
  have hplain := Finset.mem_product.mp hp.1
  constructor
  · intro I hI hzero
    have hy : ((I, x.1.2), x.2) ∈ R.cartesian :=
      Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hI, hplain.2⟩, hp.2⟩
    apply (ideal (R.index ((I, x.1.2), x.2))).property.1
    rw [R.ideal_product _ hy]
    simp only [allocationColumnIdeal, hzero, zero_mul]
  · intro J hJ hzero
    have hy : ((x.1.1, J), x.2) ∈ R.cartesian :=
      Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hplain.1, hJ⟩, hp.2⟩
    apply (ideal (R.index ((x.1.1, J), x.2))).property.1
    rw [R.ideal_product _ hy]
    simp only [allocationColumnIdeal, hzero, mul_zero, zero_mul]

/-- An already constructed true residual Cartesian branch supplies its
atlas without any new nonzero-support or source-identity assumption. -/
def ofReindex {n : ℕ}
    (R : CartesianSourceReindex columns ideal n) (hne : columns.Nonempty) :
    SourceCartesianAtlas columns ideal where
  slotCount := n
  reindex := R
  plain₁_nonzero := (reindex_plain_nonzero R hne).1
  plain₂_nonzero := (reindex_plain_nonzero R hne).2

def commonColumns (_T : SourceCartesianAtlas columns ideal)
    (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) : Finset ι :=
  columns.filter (fun i => supportExtract (ideal i).val P = D)

def labels (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) :
    Finset (SupportCartesian.ExtractionKey K T.slotCount) :=
  (T.commonColumns P D).image (T.reindex.supportExtractionLabel P)

def commonFibre (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (d : T.labels P D) : Finset ι :=
  (T.commonColumns P D).filter (fun i => T.reindex.supportExtractionLabel P i = d.val)

/-- The finite source label itself supplies the original witness. -/
def branch (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (d : T.labels P D) :
    SupportCartesianBranch T.reindex.plain₁ T.reindex.plain₂ T.reindex.slots P :=
  SupportCartesianBranch.ofKey T.plain₁_nonzero T.plain₂_nonzero d.val (by
    rw [← T.reindex.supportExtractionLabel_image P]
    obtain ⟨i, hi, hid⟩ := Finset.mem_image.mp d.property
    exact Finset.mem_image.mpr ⟨i, (Finset.mem_filter.mp hi).1, hid⟩)

theorem branch_key (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (d : T.labels P D) : (T.branch P D d).key = d.val := by
  apply SupportCartesianBranch.ofKey_key

/-- The individual extracted occurrence labels multiply to the
original fixed whole common ideal. -/
theorem branch_product (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (d : T.labels P D) :
    (T.branch P D d).plainExtract₁ * (T.branch P D d).plainExtract₂ *
      (∏ i, (T.branch P D d).slotExtract i) = D := by
  obtain ⟨i, hi, hid⟩ := Finset.mem_image.mp d.property
  obtain ⟨x, hx, rfl⟩ := T.reindex.surjective i (Finset.mem_filter.mp hi).1
  have hbranch : x ∈ (T.branch P D d).originalColumns := by
    rw [(T.branch P D d).originalColumns_eq_filter]
    apply Finset.mem_filter.mpr
    refine ⟨hx, ?_⟩
    rw [← T.reindex.supportExtractionLabel_index P x hx, T.branch_key P D d]
    exact hid
  have hwhole := (Finset.mem_filter.mp hi).2
  rw [T.reindex.ideal_product x hx, (T.branch P D d).extract_ideal x hbranch] at hwhole
  exact hwhole

theorem commonFibre_subset (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (d : T.labels P D) :
    T.commonFibre P D d ⊆ T.commonColumns P D := by
  intro i hi
  exact (Finset.mem_filter.mp hi).1

/-- The common-ideal restriction removes no member of a fixed actual
occurrence label whose product is that common ideal. -/
theorem commonFibre_eq_full (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (d : T.labels P D) :
    T.commonFibre P D d =
      columns.filter (fun i => T.reindex.supportExtractionLabel P i = d.val) := by
  ext i
  simp only [commonFibre, commonColumns, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hi, _⟩, hid⟩
    exact ⟨hi, hid⟩
  · rintro ⟨hi, hid⟩
    refine ⟨⟨hi, ?_⟩, hid⟩
    have hb : i ∈ (T.branch P D d).originalColumns.image T.reindex.index := by
      rw [← T.reindex.supportExtractionLabel_fibre P (T.branch P D d),
        T.branch_key P D d]
      exact Finset.mem_filter.mpr ⟨hi, hid⟩
    have hc := T.reindex.supportResidualBranch_subset_common P (T.branch P D d)
      D (T.branch_product P D d) hb
    exact (Finset.mem_filter.mp hc).2

/-- This residual dictionary has the literal common-source label fibre
as its source support.  Both its inverse maps are already proved by the
actual supportResidual construction. -/
def residualReindex (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (J : ι → A.Exterior)
    (hJ : ∀ i ∈ columns, (J i).val = supportResidual (ideal i).val P)
    (d : T.labels P D) :
    CartesianSourceReindex (T.commonFibre P D d) J (T.branch P D d).keep.card := by
  rw [T.commonFibre_eq_full P D d]
  simpa only [T.branch_key P D d] using
    T.reindex.supportResidualLabelBranch P (T.branch P D d) J hJ

/-- Exact linear partition of the complete coefficient.  In particular
a centered difference is kept as one summand throughout. -/
theorem sum_common {M : Type*} [AddCommMonoid M]
    (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) (f : ι → M) :
    (∑ i ∈ T.commonColumns P D, f i) =
      ∑ d : T.labels P D, ∑ i ∈ T.commonFibre P D d, f i := by
  change (∑ i ∈ T.commonColumns P D, f i) =
    ∑ d : (T.commonColumns P D).image (T.reindex.supportExtractionLabel P),
      ∑ i ∈ (T.commonColumns P D).filter
        (fun i => T.reindex.supportExtractionLabel P i = d.val), f i
  calc
    _ = ∑ d ∈ (T.commonColumns P D).image (T.reindex.supportExtractionLabel P),
        ∑ i ∈ (T.commonColumns P D).filter
          (fun i => T.reindex.supportExtractionLabel P i = d), f i :=
      (Finset.sum_fiberwise_of_maps_to
        (fun i hi => Finset.mem_image_of_mem (T.reindex.supportExtractionLabel P) hi) f).symm
    _ = _ := (Finset.sum_coe_sort _ _).symm

variable {otherColumns : Finset κ} {otherIdeal : κ → A.Exterior}
variable (U : SourceCartesianAtlas otherColumns otherIdeal)

/-- Exact partition of the coupled complex source, before a norm or
either row Cauchy inequality is applied. -/
theorem sum_pair_rows {H M : Type*} [AddCommMonoid M]
    (rows : Finset H) (P : Finset (Ideal (𝓞 K))) (D E : Ideal (𝓞 K))
    (f : H → ι → κ → M) :
    (∑ h ∈ rows, ∑ i ∈ T.commonColumns P D, ∑ j ∈ U.commonColumns P E, f h i j) =
      ∑ d : T.labels P D, ∑ e : U.labels P E,
        ∑ h ∈ rows, ∑ i ∈ T.commonFibre P D d, ∑ j ∈ U.commonFibre P E e, f h i j := by
  calc
    _ = ∑ h ∈ rows, ∑ d : T.labels P D, ∑ i ∈ T.commonFibre P D d,
        ∑ e : U.labels P E, ∑ j ∈ U.commonFibre P E e, f h i j := by
      apply Finset.sum_congr rfl
      intro h _
      rw [T.sum_common P D]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro i _
      exact U.sum_common P E (fun j => f h i j)
    _ = _ := by
      rw [Finset.sum_comm (s := rows) (t := (Finset.univ : Finset (T.labels P D)))]
      apply Finset.sum_congr rfl
      intro d _
      simp_rw [Finset.sum_comm (s := T.commonFibre P D d)
        (t := (Finset.univ : Finset (U.labels P E)))]
      rw [Finset.sum_comm (s := rows) (t := (Finset.univ : Finset (U.labels P E)))]

/-- Every actual support key consists of divisors of the fixed common
ideal.  Its finite branch count is therefore paid by the genuine ideal
divisor count, including the two plain occurrences. -/
theorem labels_card_le
    (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) (hD : D ≠ 0) :
    (T.labels P D).card ≤ (idealDivisors D).card ^ (T.slotCount + 2) := by
  let V := idealDivisors D
  have hsub : T.labels P D ⊆
      (V ×ˢ V) ×ˢ Fintype.piFinset (fun _ : Fin T.slotCount => V) := by
    intro d hd
    let q := T.branch P D ⟨d, hd⟩
    have hkey : q.key = d := T.branch_key P D ⟨d, hd⟩
    have hprod : q.plainExtract₁ * q.plainExtract₂ * (∏ i, q.slotExtract i) = D :=
      T.branch_product P D ⟨d, hd⟩
    rw [← hkey]
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · apply (mem_idealDivisors hD).mpr
      refine ⟨q.plainExtract₂ * ∏ i, q.slotExtract i, ?_⟩
      simpa only [mul_assoc] using hprod.symm
    · apply (mem_idealDivisors hD).mpr
      refine ⟨q.plainExtract₁ * ∏ i, q.slotExtract i, ?_⟩
      calc
        D = q.plainExtract₁ * q.plainExtract₂ * (∏ i, q.slotExtract i) := hprod.symm
        _ = q.plainExtract₂ * (q.plainExtract₁ * ∏ i, q.slotExtract i) := by ac_rfl
    · apply Fintype.mem_piFinset.mpr
      intro i
      apply (mem_idealDivisors hD).mpr
      have hs : q.slotExtract i ∣ ∏ j, q.slotExtract j :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      have ht := dvd_mul_of_dvd_right hs (q.plainExtract₁ * q.plainExtract₂)
      simpa only [hprod] using ht
  calc
    (T.labels P D).card ≤ V.card * V.card * V.card ^ T.slotCount := by
      simpa only [Finset.card_product, Fintype.card_piFinset_const] using
        Finset.card_le_card hsub
    _ = (idealDivisors D).card ^ (T.slotCount + 2) := by
      dsimp only [V]
      rw [pow_add, pow_two]
      ac_rfl

end SourceCartesianAtlas

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SourceCartesianAtlas.branch_product
#print axioms HeckeSkeleton.Moments.EngineStep.SourceCartesianAtlas.residualReindex
#print axioms HeckeSkeleton.Moments.EngineStep.SourceCartesianAtlas.sum_pair_rows
#print axioms HeckeSkeleton.Moments.EngineStep.SourceCartesianAtlas.labels_card_le

