import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondChartAllocation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SlotRestriction

/-!
# Actual rectangular branches of the common-support quotient

A common-support filter alone does not preserve a Cartesian support:
different occurrences may carry the same removed prime.  This module
first fixes every actual extracted occurrence.  On that finite branch,
each plain residual map is inverted by multiplication by its extracted
ideal.  A prime occurrence is either outside the common support, or is
a singleton which is removed.  The resulting Cartesian reindex keeps
the original whole coefficient and its original index.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree HeckeGeneral.Arithmetic
open HeckePort.Moments
open HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {k : ℕ}

namespace SupportCartesian

def plainFibre (S P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) :
    Finset (Ideal (𝓞 K)) :=
  S.filter (fun I => supportExtract I P = D)

def plainResidual (S P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) :
    Finset (Ideal (𝓞 K)) :=
  (plainFibre S P D).image (fun I => supportResidual I P)

def primeFibre (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  S.filter (fun p => supportExtract p.asIdeal P = D)

def primeLive (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : Finset (Ideal (𝓞 K))) : Finset (HeightOneSpectrum (𝓞 K)) :=
  S.filter (fun p => p.asIdeal ∉ P)

theorem prime_extract_eq_one (p : HeightOneSpectrum (𝓞 K))
    (P : Finset (Ideal (𝓞 K))) :
    supportExtract p.asIdeal P = 1 ↔ p.asIdeal ∉ P := by
  have hp : p.asIdeal ≠ 1 := by
    intro he
    apply p.prime.not_unit
    rw [he]
    exact isUnit_one
  rw [supportExtract_prime p.asIdeal p.prime P]
  by_cases h : p.asIdeal ∈ P <;> simp [h, hp]

theorem prime_fibre_one (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : Finset (Ideal (𝓞 K))) :
    primeFibre S P 1 = primeLive S P := by
  ext p
  simp only [primeFibre, primeLive, Finset.mem_filter, prime_extract_eq_one]

theorem prime_fibre_frozen (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) (hD : D ≠ 1)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ primeFibre S P D) :
    primeFibre S P D = {p} := by
  have heq (q : HeightOneSpectrum (𝓞 K)) (hq : q ∈ primeFibre S P D) :
      q.asIdeal = D := by
    have he := (Finset.mem_filter.mp hq).2
    rw [supportExtract_prime q.asIdeal q.prime P] at he
    split_ifs at he with hqP
    · exact he
    · exact False.elim (hD he.symm)
  ext q
  constructor
  · intro hq
    apply Finset.mem_singleton.mpr
    exact HeightOneSpectrum.asIdeal_injective ((heq q hq).trans (heq p hp).symm)
  · intro hq
    rw [Finset.mem_singleton.mp hq]
    exact hp

theorem prime_fibre_frozen_mem (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) (hD : D ≠ 1)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ primeFibre S P D) :
    p.asIdeal ∈ P := by
  by_contra hn
  have he := (Finset.mem_filter.mp hp).2
  rw [supportExtract_prime p.asIdeal p.prime P, if_neg hn] at he
  exact hD he.symm

theorem plain_reconstruct (S P : Finset (Ideal (𝓞 K))) (D I : Ideal (𝓞 K))
    (hS : ∀ J ∈ S, J ≠ 0) (hI : I ∈ plainFibre S P D) :
    D * supportResidual I P = I := by
  have hx := Finset.mem_filter.mp hI
  rw [← hx.2]
  exact support_reconstruct I (hS I hx.1) P

theorem plain_reconstruct_mem (S P : Finset (Ideal (𝓞 K))) (D J : Ideal (𝓞 K))
    (hS : ∀ I ∈ S, I ≠ 0) (hJ : J ∈ plainResidual S P D) :
    D * J ∈ plainFibre S P D := by
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
  rwa [plain_reconstruct S P D I hS hI]

theorem plain_residual_reconstruct (S P : Finset (Ideal (𝓞 K))) (D J : Ideal (𝓞 K))
    (hS : ∀ I ∈ S, I ≠ 0) (hJ : J ∈ plainResidual S P D) :
    supportResidual (D * J) P = J := by
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
  rw [plain_reconstruct S P D I hS hI]

abbrev ExtractionKey (K : Type) [Field K] [NumberField K] (k : ℕ) :=
  (Ideal (𝓞 K) × Ideal (𝓞 K)) × (Fin k → Ideal (𝓞 K))

def extractionKey (P : Finset (Ideal (𝓞 K))) (x : AllocationColumn K k) :
    ExtractionKey K k :=
  ((supportExtract x.1.1 P, supportExtract x.1.2 P),
    fun i => supportExtract (x.2 i).asIdeal P)

theorem extraction_fibre_eq
    (S₁ S₂ : Finset (Ideal (𝓞 K)))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (P : Finset (Ideal (𝓞 K))) (d : ExtractionKey K k) :
    childCartesianColumns (plainFibre S₁ P d.1.1) (plainFibre S₂ P d.1.2)
        (fun i => primeFibre (S i) P (d.2 i)) =
      (childCartesianColumns S₁ S₂ S).filter (fun x => extractionKey P x = d) := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_product.mp hx with ⟨hx₀, hxs⟩
    rcases Finset.mem_product.mp hx₀ with ⟨hx₁, hx₂⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr
          ⟨(Finset.mem_filter.mp hx₁).1, (Finset.mem_filter.mp hx₂).1⟩,
          Fintype.mem_piFinset.mpr fun i =>
            (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hxs i)).1⟩
    · apply Prod.ext
      · exact Prod.ext (Finset.mem_filter.mp hx₁).2 (Finset.mem_filter.mp hx₂).2
      · funext i
        exact (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hxs i)).2
  · intro hx
    rcases Finset.mem_filter.mp hx with ⟨hx, he⟩
    rcases Finset.mem_product.mp hx with ⟨hx₀, hxs⟩
    rcases Finset.mem_product.mp hx₀ with ⟨hx₁, hx₂⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨hx₁, congrArg (fun z => z.1.1) he⟩,
        Finset.mem_filter.mpr ⟨hx₂, congrArg (fun z => z.1.2) he⟩⟩, ?_⟩
    exact Fintype.mem_piFinset.mpr fun i =>
      Finset.mem_filter.mpr
        ⟨Fintype.mem_piFinset.mp hxs i, congrArg (fun z => z.2 i) he⟩

/-- The occurrence labels form an exact partition of the original
whole sum.  No triangle or separate-factor absolute value is used. -/
theorem whole_sum_partition {M : Type*} [AddCommMonoid M]
    (S₁ S₂ : Finset (Ideal (𝓞 K)))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (P : Finset (Ideal (𝓞 K))) (c : AllocationColumn K k → M) :
    (∑ x ∈ childCartesianColumns S₁ S₂ S, c x) =
      ∑ d ∈ (childCartesianColumns S₁ S₂ S).image (extractionKey P),
        ∑ x ∈ childCartesianColumns
          (plainFibre S₁ P d.1.1) (plainFibre S₂ P d.1.2)
          (fun i => primeFibre (S i) P (d.2 i)), c x := by
  simp_rw [extraction_fibre_eq]
  exact (Finset.sum_fiberwise_of_maps_to
    (fun x hx => Finset.mem_image_of_mem (extractionKey P) hx) c).symm

end SupportCartesian

/-- The data of a nonempty branch consists of the actual extracted
ideals and one original support witness.  Its support and all residual
maps below are computed; no residual bijection is assumed. -/
structure SupportCartesianBranch
    (S₁ S₂ : Finset (Ideal (𝓞 K)))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (P : Finset (Ideal (𝓞 K))) where
  plainExtract₁ : Ideal (𝓞 K)
  plainExtract₂ : Ideal (𝓞 K)
  slotExtract : Fin k → Ideal (𝓞 K)
  plain₁_nonzero : ∀ I ∈ S₁, I ≠ 0
  plain₂_nonzero : ∀ I ∈ S₂, I ≠ 0
  witness : AllocationColumn K k
  witness_mem : witness ∈ childCartesianColumns
    (SupportCartesian.plainFibre S₁ P plainExtract₁)
    (SupportCartesian.plainFibre S₂ P plainExtract₂)
    (fun i => SupportCartesian.primeFibre (S i) P (slotExtract i))

namespace SupportCartesianBranch

open SupportCartesian

variable {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {P : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch S₁ S₂ S P)

def originalColumns : Finset (AllocationColumn K k) :=
  childCartesianColumns
    (plainFibre S₁ P b.plainExtract₁) (plainFibre S₂ P b.plainExtract₂)
    (fun i => primeFibre (S i) P (b.slotExtract i))

def keep : Finset (Fin k) := Finset.univ.filter (fun i => b.slotExtract i = 1)

def residualColumns : Finset (AllocationColumn K b.keep.card) :=
  childCartesianColumns
    (plainResidual S₁ P b.plainExtract₁) (plainResidual S₂ P b.plainExtract₂)
    (fun j => primeLive (S (SlotRestriction.index b.keep j)) P)

def reconstruct (y : AllocationColumn K b.keep.card) : AllocationColumn K k :=
  ((b.plainExtract₁ * y.1.1, b.plainExtract₂ * y.1.2),
    SlotRestriction.extend b.keep b.witness.2 y.2)

def residual (x : AllocationColumn K k) : AllocationColumn K b.keep.card :=
  ((supportResidual x.1.1 P, supportResidual x.1.2 P),
    SlotRestriction.restrict b.keep x.2)

def key : SupportCartesian.ExtractionKey K k :=
  ((b.plainExtract₁, b.plainExtract₂), b.slotExtract)

theorem originalColumns_eq_filter :
    b.originalColumns =
      (childCartesianColumns S₁ S₂ S).filter
        (fun x => SupportCartesian.extractionKey P x = b.key) :=
  SupportCartesian.extraction_fibre_eq S₁ S₂ S P b.key

/-- Each original column supplies the nonempty branch of its own
actual extracted occurrence tuple. -/
def ofColumn
    (h₁ : ∀ I ∈ S₁, I ≠ 0) (h₂ : ∀ I ∈ S₂, I ≠ 0)
    (x : AllocationColumn K k) (hx : x ∈ childCartesianColumns S₁ S₂ S) :
    SupportCartesianBranch S₁ S₂ S P where
  plainExtract₁ := supportExtract x.1.1 P
  plainExtract₂ := supportExtract x.1.2 P
  slotExtract i := supportExtract (x.2 i).asIdeal P
  plain₁_nonzero := h₁
  plain₂_nonzero := h₂
  witness := x
  witness_mem := by
    have hp := Finset.mem_product.mp (Finset.mem_product.mp hx).1
    refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨hp.1, rfl⟩, Finset.mem_filter.mpr ⟨hp.2, rfl⟩⟩, ?_⟩
    exact Fintype.mem_piFinset.mpr fun i =>
      Finset.mem_filter.mpr
        ⟨Fintype.mem_piFinset.mp (Finset.mem_product.mp hx).2 i, rfl⟩

/-- The finite label image itself supplies a witness. -/
def ofKey
    (h₁ : ∀ I ∈ S₁, I ≠ 0) (h₂ : ∀ I ∈ S₂, I ≠ 0)
    (d : SupportCartesian.ExtractionKey K k)
    (hd : d ∈ (childCartesianColumns S₁ S₂ S).image
      (SupportCartesian.extractionKey P)) :
    SupportCartesianBranch S₁ S₂ S P :=
  ofColumn h₁ h₂ (Classical.choose (Finset.mem_image.mp hd))
    (Classical.choose_spec (Finset.mem_image.mp hd)).1

theorem ofKey_key
    (h₁ : ∀ I ∈ S₁, I ≠ 0) (h₂ : ∀ I ∈ S₂, I ≠ 0)
    (d : SupportCartesian.ExtractionKey K k)
    (hd : d ∈ (childCartesianColumns S₁ S₂ S).image
      (SupportCartesian.extractionKey P)) :
    (ofKey h₁ h₂ d hd).key = d :=
  (Classical.choose_spec (Finset.mem_image.mp hd)).2

theorem witness_slots (i : Fin k) :
    b.witness.2 i ∈ primeFibre (S i) P (b.slotExtract i) :=
  Fintype.mem_piFinset.mp (Finset.mem_product.mp b.witness_mem).2 i

theorem slots_eq :
    (fun i => primeFibre (S i) P (b.slotExtract i)) =
      fun i => if i ∈ b.keep then primeLive (S i) P else {b.witness.2 i} := by
  funext i
  by_cases hi : b.slotExtract i = 1
  · simp only [keep, Finset.mem_filter, Finset.mem_univ, true_and, hi, if_true]
    exact prime_fibre_one (S i) P
  · simp only [keep, Finset.mem_filter, Finset.mem_univ, true_and, hi, if_false]
    exact prime_fibre_frozen (S i) P (b.slotExtract i) hi
      (b.witness.2 i) (b.witness_slots i)

theorem original_subset :
    b.originalColumns ⊆ childCartesianColumns S₁ S₂ S := by
  intro x hx
  rcases Finset.mem_product.mp hx with ⟨hx₀, hxs⟩
  rcases Finset.mem_product.mp hx₀ with ⟨hx₁, hx₂⟩
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_product.mpr
    ⟨(Finset.mem_filter.mp hx₁).1, (Finset.mem_filter.mp hx₂).1⟩, ?_⟩
  exact Fintype.mem_piFinset.mpr fun i =>
    (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hxs i)).1

theorem original_slots (x : AllocationColumn K k) (hx : x ∈ b.originalColumns) :
    x.2 ∈ SlotRestriction.fullSupport b.keep (fun i => primeLive (S i) P) b.witness.2 := by
  have hs := (Finset.mem_product.mp hx).2
  change x.2 ∈ Fintype.piFinset (fun i => primeFibre (S i) P (b.slotExtract i)) at hs
  rw [b.slots_eq] at hs
  exact hs

theorem residual_mem (x : AllocationColumn K k) (hx : x ∈ b.originalColumns) :
    b.residual x ∈ b.residualColumns := by
  rcases Finset.mem_product.mp hx with ⟨hx₀, hxs⟩
  rcases Finset.mem_product.mp hx₀ with ⟨hx₁, hx₂⟩
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_product.mpr
    ⟨Finset.mem_image.mpr ⟨x.1.1, hx₁, rfl⟩,
      Finset.mem_image.mpr ⟨x.1.2, hx₂, rfl⟩⟩, ?_⟩
  exact SlotRestriction.restrict_mem b.keep (fun i => primeLive (S i) P)
    b.witness.2 x.2 (b.original_slots x hx)

theorem reconstruct_mem (y : AllocationColumn K b.keep.card)
    (hy : y ∈ b.residualColumns) : b.reconstruct y ∈ b.originalColumns := by
  rcases Finset.mem_product.mp hy with ⟨hy₀, hys⟩
  rcases Finset.mem_product.mp hy₀ with ⟨hy₁, hy₂⟩
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_product.mpr
    ⟨plain_reconstruct_mem S₁ P b.plainExtract₁ y.1.1 b.plain₁_nonzero hy₁,
      plain_reconstruct_mem S₂ P b.plainExtract₂ y.1.2 b.plain₂_nonzero hy₂⟩, ?_⟩
  change SlotRestriction.extend b.keep b.witness.2 y.2 ∈
    Fintype.piFinset (fun i => primeFibre (S i) P (b.slotExtract i))
  rw [b.slots_eq]
  exact SlotRestriction.extend_mem b.keep (fun i => primeLive (S i) P) b.witness.2 y.2 hys

theorem reconstruct_residual (x : AllocationColumn K k)
    (hx : x ∈ b.originalColumns) : b.reconstruct (b.residual x) = x := by
  have hp := Finset.mem_product.mp (Finset.mem_product.mp hx).1
  apply Prod.ext
  · apply Prod.ext
    · exact plain_reconstruct S₁ P b.plainExtract₁ x.1.1 b.plain₁_nonzero hp.1
    · exact plain_reconstruct S₂ P b.plainExtract₂ x.1.2 b.plain₂_nonzero hp.2
  · exact SlotRestriction.extend_restrict b.keep (fun i => primeLive (S i) P)
      b.witness.2 x.2 (b.original_slots x hx)

theorem residual_reconstruct (y : AllocationColumn K b.keep.card)
    (hy : y ∈ b.residualColumns) : b.residual (b.reconstruct y) = y := by
  have hp := Finset.mem_product.mp (Finset.mem_product.mp hy).1
  apply Prod.ext
  · apply Prod.ext
    · exact plain_residual_reconstruct S₁ P b.plainExtract₁ y.1.1 b.plain₁_nonzero hp.1
    · exact plain_residual_reconstruct S₂ P b.plainExtract₂ y.1.2 b.plain₂_nonzero hp.2
  · exact SlotRestriction.restrict_extend b.keep b.witness.2 y.2

theorem sum_reindex {M : Type*} [AddCommMonoid M] (c : AllocationColumn K k → M) :
    (∑ x ∈ b.originalColumns, c x) = ∑ y ∈ b.residualColumns, c (b.reconstruct y) := by
  refine Finset.sum_bij (fun x _ => b.residual x) ?_ ?_ ?_ ?_
  · exact fun x hx => b.residual_mem x hx
  · intro x hx z hz he
    rw [← b.reconstruct_residual x hx, ← b.reconstruct_residual z hz, he]
  · intro y hy
    exact ⟨b.reconstruct y, b.reconstruct_mem y hy, b.residual_reconstruct y hy⟩
  · intro x hx
    rw [b.reconstruct_residual x hx]

theorem residual_slots_product (x : AllocationColumn K k)
    (hx : x ∈ b.originalColumns) :
    (∏ i, supportResidual (x.2 i).asIdeal P) =
      ∏ j, (x.2 (SlotRestriction.index b.keep j)).asIdeal := by
  have he := SlotRestriction.extend_restrict b.keep (fun i => primeLive (S i) P)
    b.witness.2 x.2 (b.original_slots x hx)
  have hprod := SlotRestriction.product_extend b.keep b.witness.2
    (SlotRestriction.restrict b.keep x.2)
    (fun _ p => supportResidual p.asIdeal P)
  rw [he] at hprod
  rw [hprod]
  have hf : (∏ i ∈ Finset.univ.filter (fun i => i ∉ b.keep),
      supportResidual (b.witness.2 i).asIdeal P) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have hni : b.slotExtract i ≠ 1 := by
      simpa only [keep, Finset.mem_filter, Finset.mem_univ, true_and] using
        (Finset.mem_filter.mp hi).2
    rw [supportResidual_prime _ (b.witness.2 i).prime P,
      if_pos (prime_fibre_frozen_mem (S i) P (b.slotExtract i) hni
        (b.witness.2 i) (b.witness_slots i))]
  rw [hf, one_mul]
  apply Finset.prod_congr rfl
  intro j _
  have hi := SlotRestriction.index_mem b.keep j
  have hd : b.slotExtract (SlotRestriction.index b.keep j) = 1 :=
    (Finset.mem_filter.mp hi).2
  have hp := Fintype.mem_piFinset.mp (Finset.mem_product.mp hx).2
    (SlotRestriction.index b.keep j)
  have hnot : (x.2 (SlotRestriction.index b.keep j)).asIdeal ∉ P := by
    apply (prime_extract_eq_one _ P).mp
    exact (Finset.mem_filter.mp hp).2.trans hd
  exact (supportResidual_prime _ (x.2 (SlotRestriction.index b.keep j)).prime P).trans
    (if_neg hnot)

theorem residual_ideal (x : AllocationColumn K k) (hx : x ∈ b.originalColumns) :
    supportResidual (allocationColumnIdeal x) P = allocationColumnIdeal (b.residual x) := by
  have hp := Finset.mem_product.mp (Finset.mem_product.mp hx).1
  have h₁ := b.plain₁_nonzero x.1.1 (Finset.mem_filter.mp hp.1).1
  have h₂ := b.plain₂_nonzero x.1.2 (Finset.mem_filter.mp hp.2).1
  have hs : (∏ i, (x.2 i).asIdeal) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact (x.2 i).prime.ne_zero
  unfold allocationColumnIdeal
  rw [supportResidual_mul _ _ (mul_ne_zero h₁ h₂) hs P,
    supportResidual_mul _ _ h₁ h₂ P,
    supportResidual_prod Finset.univ (fun i => (x.2 i).asIdeal)
      (fun i _ => (x.2 i).prime.ne_zero) P,
    b.residual_slots_product x hx]
  rfl

theorem extract_ideal (x : AllocationColumn K k) (hx : x ∈ b.originalColumns) :
    supportExtract (allocationColumnIdeal x) P =
      b.plainExtract₁ * b.plainExtract₂ * ∏ i, b.slotExtract i := by
  have hp := Finset.mem_product.mp (Finset.mem_product.mp hx).1
  have h₁ := b.plain₁_nonzero x.1.1 (Finset.mem_filter.mp hp.1).1
  have h₂ := b.plain₂_nonzero x.1.2 (Finset.mem_filter.mp hp.2).1
  have hs : (∏ i, (x.2 i).asIdeal) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact (x.2 i).prime.ne_zero
  unfold allocationColumnIdeal
  rw [supportExtract_mul _ _ (mul_ne_zero h₁ h₂) hs P,
    supportExtract_mul _ _ h₁ h₂ P,
    supportExtract_prod Finset.univ (fun i => (x.2 i).asIdeal)
      (fun i _ => (x.2 i).prime.ne_zero) P,
    (Finset.mem_filter.mp hp.1).2, (Finset.mem_filter.mp hp.2).2]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact (Finset.mem_filter.mp
    (Fintype.mem_piFinset.mp (Finset.mem_product.mp hx).2 i)).2

end SupportCartesianBranch

namespace CartesianSourceReindex

variable {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
variable (R : CartesianSourceReindex columns ideal k)
/-- Ideal recipes may be replaced by their actual value equality on
the retained original indices.  No equality of generators is needed. -/
def congrIdeal (J : ι → A.Exterior)
    (hJ : ∀ i ∈ columns, (J i).val = (ideal i).val) :
    CartesianSourceReindex columns J k where
  plain₁ := R.plain₁
  plain₂ := R.plain₂
  slots := R.slots
  index := R.index
  maps := R.maps
  injective := R.injective
  surjective := R.surjective
  ideal_product x hx := (hJ (R.index x) (R.maps x hx)).trans (R.ideal_product x hx)

variable (P : Finset (Ideal (𝓞 K)))
variable (b : SupportCartesianBranch R.plain₁ R.plain₂ R.slots P)

/-- The actual common-support quotient on a fixed occurrence branch.
The original source index is recovered inside the construction. -/
def supportResidualBranch :
    CartesianSourceReindex (b.originalColumns.image R.index)
      (fun i => residualExterior (ideal i) P) b.keep.card where
  plain₁ := SupportCartesian.plainResidual R.plain₁ P b.plainExtract₁
  plain₂ := SupportCartesian.plainResidual R.plain₂ P b.plainExtract₂
  slots j := SupportCartesian.primeLive (R.slots (SlotRestriction.index b.keep j)) P
  index y := R.index (b.reconstruct y)
  maps y hy := Finset.mem_image.mpr
    ⟨b.reconstruct y, b.reconstruct_mem y hy, rfl⟩
  injective := by
    intro y hy z hz he
    have h := R.injective
      (b.original_subset (b.reconstruct_mem y hy))
      (b.original_subset (b.reconstruct_mem z hz)) he
    calc
      y = b.residual (b.reconstruct y) := (b.residual_reconstruct y hy).symm
      _ = b.residual (b.reconstruct z) := congrArg b.residual h
      _ = z := b.residual_reconstruct z hz
  surjective := by
    intro i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨b.residual x, b.residual_mem x hx,
      congrArg R.index (b.reconstruct_residual x hx)⟩
  ideal_product := by
    intro y hy
    change supportResidual (ideal (R.index (b.reconstruct y))).val P =
      allocationColumnIdeal y
    rw [R.ideal_product (b.reconstruct y) (b.original_subset (b.reconstruct_mem y hy)),
      b.residual_ideal (b.reconstruct y) (b.reconstruct_mem y hy),
      b.residual_reconstruct y hy]

/-- This variant uses the residual ideals of an actual source chart.
The pointwise recipe is exactly the defining supportResidual formula. -/
def supportResidualBranchOf (J : ι → A.Exterior)
    (hJ : ∀ i ∈ columns, (J i).val = supportResidual (ideal i).val P) :
    CartesianSourceReindex (b.originalColumns.image R.index) J b.keep.card :=
  (R.supportResidualBranch P b).congrIdeal J (by
    intro i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    exact hJ (R.index x) (R.maps x (b.original_subset hx)))

theorem supportResidualBranch_subset_common
    (D : Ideal (𝓞 K))
    (hD : b.plainExtract₁ * b.plainExtract₂ * (∏ i, b.slotExtract i) = D) :
    b.originalColumns.image R.index ⊆
      columns.filter (fun i => supportExtract (ideal i).val P = D) := by
  intro i hi
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
  apply Finset.mem_filter.mpr
  refine ⟨R.maps x (b.original_subset hx), ?_⟩
  rw [R.ideal_product x (b.original_subset hx), b.extract_ideal x hx, hD]

end CartesianSourceReindex

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesian.whole_sum_partition
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.sum_reindex
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.residual_ideal
#print axioms HeckeSkeleton.Moments.EngineStep.CartesianSourceReindex.supportResidualBranch
