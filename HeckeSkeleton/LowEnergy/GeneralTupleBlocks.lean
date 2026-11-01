import HeckeSkeleton.LowEnergy.GeneralProductReconstruction
import HeckeSkeleton.LowEnergy.GeneralCanonicalBlock

/-!
# From prime choices to literal finite canonical blocks

An active prime selects every slot in which that prime occurs.  Thus the
slot patterns which represent a prime choice are exactly the patterns
whose active and inactive supports are disjoint.  The finite identities
below preserve that condition while moving the inactive tuple outside
the active ideal fibre sum.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GeneralTupleBlocks

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.GeneralInactiveMass
open HeckeSkeleton.LowEnergy.TupleCore
open scoped Classical BigOperators NumberField nonZeroDivisors

section FiniteReindex

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]

theorem join_active_image (I : Finset ι) (a : I → α) (b : {i // i ∉ I} → α) :
    I.image (join (fun i => i ∈ I) a b) = tupleSupport a := by
  ext q
  constructor
  · intro hq
    obtain ⟨i, hi, hq⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, by
      simpa only [join_of_true (fun i => i ∈ I) a b i hi] using hq⟩
  · intro hq
    obtain ⟨i, _, hq⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨i, i.property, by
      simpa only [join_of_true (fun i => i ∈ I) a b i i.property] using hq⟩

theorem join_inactive_image (I : Finset ι) (a : I → α) (b : {i // i ∉ I} → α) :
    (Finset.univ \ I).image (join (fun i => i ∈ I) a b) = tupleSupport b := by
  ext q
  constructor
  · intro hq
    obtain ⟨i, hi, hq⟩ := Finset.mem_image.mp hq
    have hi' := (Finset.mem_sdiff.mp hi).2
    exact Finset.mem_image.mpr ⟨⟨i, hi'⟩, Finset.mem_univ _, by
      simpa only [join_of_false (fun i => i ∈ I) a b i hi'] using hq⟩
  · intro hq
    obtain ⟨i, _, hq⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, i.property⟩, by
      simpa only [join_of_false (fun i => i ∈ I) a b i i.property] using hq⟩

theorem join_support (I : Finset ι) (a : I → α) (b : {i // i ∉ I} → α) :
    tupleSupport (join (fun i => i ∈ I) a b) = tupleSupport a ∪ tupleSupport b := by
  have hu : I ∪ (Finset.univ \ I) = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ I)
  calc
    _ = (I ∪ (Finset.univ \ I)).image (join (fun i => i ∈ I) a b) := by rw [hu]; rfl
    _ = _ := by rw [Finset.image_union, join_active_image, join_inactive_image]

theorem join_support_sdiff_active (I : Finset ι)
    (a : I → α) (b : {i // i ∉ I} → α)
    (h : Disjoint (tupleSupport a) (tupleSupport b)) :
    tupleSupport (join (fun i => i ∈ I) a b) \ tupleSupport a = tupleSupport b := by
  rw [join_support, Finset.union_sdiff_distrib, Finset.sdiff_self, Finset.empty_union]
  exact h.symm.sdiff_eq_left

/-- A prime choice is bijective with a saturated activity pattern. -/
theorem sum_primeChoices_eq_saturated_patterns (p : ι → α) (f : Finset α → ℂ) :
    (∑ A ∈ (tupleSupport p).powerset, f A) =
      ∑ I ∈ (Finset.univ : Finset ι).powerset,
        if Disjoint (I.image p) ((Finset.univ \ I).image p) then f (I.image p) else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun A _ => activeSlots p A)
  · intro A hA
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
      active_inactive_support_disjoint p A (Finset.mem_powerset.mp hA)⟩
  · intro A hA B hB h
    have hi := congrArg (fun I : Finset ι => I.image p) h
    rw [activeSlots_image p A (Finset.mem_powerset.mp hA),
      activeSlots_image p B (Finset.mem_powerset.mp hB)] at hi
    exact hi
  · intro I hI
    refine ⟨I.image p, Finset.mem_powerset.mpr ?_, ?_⟩
    · exact Finset.image_subset_image (Finset.subset_univ I)
    · exact activeSlots_unique p I (Finset.mem_filter.mp hI).2
  · intro A hA
    rw [activeSlots_image p A (Finset.mem_powerset.mp hA)]

/-- Exact product-weighted regrouping of every original tuple and every
prime MarkChoice.  Duplicate coordinates stay on the same side. -/
theorem weighted_primeChoices_reindex (W : ι → Finset α) (w : ι → α → ℂ)
    (H : Finset ι → Finset α → Finset α → ℂ) :
    (∑ p ∈ Fintype.piFinset W, slotProduct w p *
      ∑ A ∈ (tupleSupport p).powerset, H (activeSlots p A) (tupleSupport p \ A) A) =
      ∑ I ∈ (Finset.univ : Finset ι).powerset,
        ∑ b ∈ Fintype.piFinset (fun i : {i // i ∉ I} => W i),
          slotProduct (fun i : {i // i ∉ I} => w i) b *
            ∑ a ∈ Fintype.piFinset (fun i : I => W i),
              if Disjoint (tupleSupport a) (tupleSupport b) then
                slotProduct (fun i : I => w i) a * H I (tupleSupport b) (tupleSupport a)
              else 0 := by
  simp_rw [sum_primeChoices_eq_saturated_patterns]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  rw [sum_piFinset_split W (fun i => i ∈ I), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  refine Finset.sum_congr ?_ ?_
  · ext a
    simp only [Fintype.mem_piFinset]
  intro a _
  have hactive := join_active_image I a b
  have hinactive := join_inactive_image I a b
  simp only [hactive, hinactive]
  by_cases h : Disjoint (tupleSupport a) (tupleSupport b)
  · simp only [if_pos h]
    rw [join_support_sdiff_active I a b h]
    have hI := activeSlots_unique (join (fun i => i ∈ I) a b) I (by
      rw [hactive, hinactive]
      exact h)
    rw [hactive] at hI
    rw [hI]
    have hw : slotProduct w (join (fun i => i ∈ I) a b) =
        slotProduct (fun i : I => w i) a *
          slotProduct (fun i : {i // i ∉ I} => w i) b := by
      unfold slotProduct
      rw [InactiveCore.prod_join]
      apply congrArg₂ (· * ·)
      · refine Finset.prod_congr ?_ ?_
        · ext i
          simp only [Finset.mem_univ]
        · intro i _
          rfl
      · rfl
    rw [hw]
    ring
  · simp only [if_neg h, mul_zero]

theorem sum_piFinset_equiv {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (W : ι → Finset α) (f : (ι → α) → ℂ) :
    (∑ p ∈ Fintype.piFinset W, f p) =
      ∑ p ∈ Fintype.piFinset (fun i => W (e i)), f (fun i => p (e.symm i)) := by
  apply Finset.sum_bij (fun p _ i => p (e i))
  · intro p hp
    exact Fintype.mem_piFinset.mpr (fun i => Fintype.mem_piFinset.mp hp (e i))
  · intro p _ q _ hpq
    funext i
    simpa using congrFun hpq (e.symm i)
  · intro p hp
    refine ⟨(fun i => p (e.symm i)), Fintype.mem_piFinset.mpr ?_, ?_⟩
    · intro i
      simpa using Fintype.mem_piFinset.mp hp (e.symm i)
    · funext i
      simp
  · intro p _
    congr 1
    funext i
    simp

theorem tupleSupport_equiv {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (p : ι → α) : tupleSupport (fun i => p (e i)) = tupleSupport p := by
  ext q
  simp only [tupleSupport, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨e i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨e.symm i, by simpa using hi⟩

theorem slotProduct_unindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (w : ι → α → ℂ) (p : κ → α) :
    slotProduct w (fun i => p (e.symm i)) = slotProduct (fun i => w (e i)) p := by
  simpa only [slotProduct, e.symm_apply_apply] using
    (e.prod_comp (fun i => w i (p (e.symm i)))).symm

end FiniteReindex

open HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualSourceReindex
open HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open HeckeSkeleton.LowEnergy.GeneralReconstruction
open HeckeSkeleton.LowEnergy.GeneralAggregation
open HeckeSkeleton.LowEnergy.GeneralInactiveEnergy
open HeckeSkeleton.LowEnergy.GeneralCanonicalBlock

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- A single active ideal in the literal finite source rectangle. -/
def markKernel (b : FrozenBlock K S) (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (V : SmoothAnnularTest)
    (P k : Ideal (𝓞 K)) : ℂ :=
  if k ∈ b.rows then
    ∑ s ∈ b.states, ∑ c ∈ b.squarefreeColumns, ∑ n ∈ b.cubeColumns,
      sourceTerm K S D { b with markWeight := fun _ => 1 } s F θ V.toFun k P c n
  else 0

theorem sourceTerm_reweight (b : FrozenBlock K S) (marks : Finset (Ideal (𝓞 K)))
    (weight : Ideal (𝓞 K) → ℂ) (s : FrozenState K S b.fixed.frozen b.fixed.puncture)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : ℝ → ℂ)
    (k P c n : Ideal (𝓞 K)) :
    sourceTerm K S D { b with marks := marks, markWeight := weight } s F θ V k P c n =
      weight P * sourceTerm K S D { b with markWeight := fun _ => 1 } s F θ V k P c n := by
  have hterm (k' P' c' n' : ExteriorIdeal K S)
      (hk' : RowAdmissible K S b.fixed k') (hP' : MarkAdmissible K S b.fixed P') :
      literalTerm K S D b.fixed s F θ weight V b.X k' P' c' n' hk' hP' =
        weight P'.val.val *
          literalTerm K S D b.fixed s F θ (fun _ => 1) V b.X k' P' c' n' hk' hP' := by
    by_cases hkP : IsCoprime k'.val.val P'.val.val
    · by_cases hcn : ColumnCondition K S s c' n'
      · by_cases hPn : IsCoprime P'.val.val n'.val.val
        · simp only [literalTerm, dif_pos hkP, dif_pos hcn, dif_pos hPn, one_mul]
        · simp only [literalTerm, dif_pos hkP, dif_pos hcn, dif_neg hPn, mul_zero]
      · simp only [literalTerm, dif_pos hkP, dif_neg hcn, mul_zero]
    · simp only [literalTerm, dif_neg hkP, mul_zero]
  unfold sourceTerm
  by_cases hk : IsExterior K S k
  · by_cases hP : IsExterior K S P
    · by_cases hc : IsExterior K S c
      · by_cases hn : IsExterior K S n
        · by_cases hrow : RowAdmissible K S b.fixed (toExterior K S k hk)
          · by_cases hmark : MarkAdmissible K S b.fixed (toExterior K S P hP)
            · simp only [dif_pos hk, dif_pos hP, dif_pos hc, dif_pos hn,
                dif_pos hrow, dif_pos hmark]
              simpa only [toExterior] using
                hterm (toExterior K S k hk) (toExterior K S P hP)
                  (toExterior K S c hc) (toExterior K S n hn) hrow hmark
            · simp only [dif_pos hk, dif_pos hP, dif_pos hc, dif_pos hn,
                dif_pos hrow, dif_neg hmark, mul_zero]
          · simp only [dif_pos hk, dif_pos hP, dif_pos hc, dif_pos hn,
              dif_neg hrow, mul_zero]
        · simp only [dif_pos hk, dif_pos hP, dif_pos hc, dif_neg hn, mul_zero]
      · simp only [dif_pos hk, dif_pos hP, dif_neg hc, mul_zero]
    · simp only [dif_pos hk, dif_neg hP, mul_zero]
  · simp only [dif_neg hk, mul_zero]

theorem sourceRow_reweight (b : FrozenBlock K S) (marks : Finset (Ideal (𝓞 K)))
    (weight : Ideal (𝓞 K) → ℂ) (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (V : SmoothAnnularTest) (k : Ideal (𝓞 K)) :
    sourceRow K S D { b with marks := marks, markWeight := weight } F θ V k =
      ∑ P ∈ marks, weight P * markKernel K S D b F θ V P k := by
  by_cases hk : k ∈ b.rows
  · rw [sourceRow, if_pos hk]
    simp_rw [sourceTerm_reweight K S D b marks weight]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro P _
    rw [markKernel, if_pos hk]
    simp only [Finset.mul_sum]
  · simp only [sourceRow, markKernel, hk, if_false, mul_zero, Finset.sum_const_zero]

/-- The original row--active-mark collision remains a literal zero after
every finite state and column restriction. -/
theorem markKernel_eq_zero_of_not_coprime (b : FrozenBlock K S)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : SmoothAnnularTest)
    (P k : Ideal (𝓞 K)) (hkP : ¬IsCoprime k P) :
    markKernel K S D b F θ V P k = 0 := by
  unfold markKernel
  split_ifs
  · apply Finset.sum_eq_zero
    intro state _
    apply Finset.sum_eq_zero
    intro c _
    apply Finset.sum_eq_zero
    intro n _
    unfold sourceTerm
    split_ifs <;> try rfl
    unfold literalTerm
    apply dif_neg
    change ¬IsCoprime k P
    exact hkP
  · rfl

/-- Ordinary finite cut data; there is no estimate or reconstruction
assertion among these fields. -/
structure BlockRanges (frozen puncture : ExteriorIdeal K S) where
  states : Finset (FrozenState K S frozen puncture)
  rowScale : ℝ
  markScale : ℝ
  squarefreeScale : ℝ
  cubeScale : ℝ
  rows : Finset (Ideal (𝓞 K))
  squarefreeColumns : Finset (Ideal (𝓞 K))
  cubeColumns : Finset (Ideal (𝓞 K))

structure ProductData (r : ℕ) where
  frozen : ExteriorIdeal K S
  puncture : ExteriorIdeal K S
  puncture_squarefree : Squarefree puncture.val.val
  rowUnit : S.unit K
  X : ℝ
  windows : Fin r → Finset (ExteriorPrime K S)
  scales : Fin r → ℝ
  coefficient : Fin r → ExteriorPrime K S → ℂ
  rows : Finset (Ideal (𝓞 K))
  ranges : Finset (Fin r) → Finset (ExteriorPrime K S) →
    BlockRanges K S frozen puncture

namespace ProductData

variable {K S} {r : ℕ}

/-- The common arithmetic data of an original marked row.  Moving rows
and the tuple's marks are not inserted into the coefficient factory. -/
def ofMarkedDatum (d₀ : MarkedDatum K S) (X : ℝ)
    (windows : Fin r → Finset (ExteriorPrime K S)) (scales : Fin r → ℝ)
    (coefficient : Fin r → ExteriorPrime K S → ℂ) (rows : Finset (Ideal (𝓞 K)))
    (ranges : Finset (Fin r) → Finset (ExteriorPrime K S) →
      BlockRanges K S d₀.frozen d₀.puncture) : ProductData K S r where
  frozen := d₀.frozen
  puncture := d₀.puncture
  puncture_squarefree := d₀.puncture_squarefree
  rowUnit := d₀.rowUnit
  X := X
  windows := windows
  scales := scales
  coefficient := coefficient
  rows := rows
  ranges := ranges

def Away (d : ProductData K S r) (q : ExteriorPrime K S) : Prop :=
  ¬q.val.asIdeal ∣ d.frozen.val.val ∧ ¬q.val.asIdeal ∣ d.puncture.val.val

def LegalInactive (d : ProductData K S r) (B : Finset (ExteriorPrime K S)) : Prop :=
  ∀ q ∈ B, d.Away q

/-- Filtering only supplies total data at tuples outside the outer sum.
For every retained inactive tuple, this is its complete actual support. -/
def fixed (d : ProductData K S r) (B : Finset (ExteriorPrime K S)) : FixedData K S where
  frozen := d.frozen
  puncture := d.puncture
  puncture_squarefree := d.puncture_squarefree
  rowUnit := d.rowUnit
  inactive := B.filter d.Away
  inactive_away := by
    intro q hq
    exact (Finset.mem_filter.mp hq).2

theorem fixed_inactive (d : ProductData K S r) (B : Finset (ExteriorPrime K S))
    (hB : d.LegalInactive B) : (d.fixed B).inactive = B := by
  exact Finset.filter_eq_self.mpr hB

def baseBlock (d : ProductData K S r) (I : Finset (Fin r))
    (B : Finset (ExteriorPrime K S)) : FrozenBlock K S where
  fixed := d.fixed B
  states := (d.ranges I B).states
  X := d.X
  rowScale := (d.ranges I B).rowScale
  markScale := (d.ranges I B).markScale
  squarefreeScale := (d.ranges I B).squarefreeScale
  cubeScale := (d.ranges I B).cubeScale
  rows := d.rows.filter (fun k => k ∈ (d.ranges I B).rows ∧
    ∃ hk : IsExterior K S k, RowAdmissible K S (d.fixed B) (toExterior K S k hk))
  marks := ∅
  squarefreeColumns := (d.ranges I B).squarefreeColumns.filter (IsExterior K S)
  cubeColumns := (d.ranges I B).cubeColumns.filter (IsExterior K S)
  markWeight := fun _ => 1

theorem baseBlock_rows_subset (d : ProductData K S r) (I : Finset (Fin r))
    (B : Finset (ExteriorPrime K S)) : (d.baseBlock I B).rows ⊆ d.rows :=
  Finset.filter_subset _ _

def ActiveAllowed (d : ProductData K S r) (I : Finset (Fin r))
    (B A : Finset (ExteriorPrime K S)) : Prop :=
  MarkAdmissible K S (d.fixed B) (primeSetIdeal K S A) ∧
    (d.ranges I B).markScale ≤ exteriorNorm K S (primeSetIdeal K S A) ∧
    exteriorNorm K S (primeSetIdeal K S A) ≤ 2 * (d.ranges I B).markScale

/-- Every restriction in the active coefficient is independent of the
moving row and both dual columns.  The norm annulus is the actual ideal
annulus, not a product over possibly repeated slots. -/
def activeTuples (d : ProductData K S r) (I : Finset (Fin r))
    (B : Finset (ExteriorPrime K S)) : Finset (I → ExteriorPrime K S) :=
  (Fintype.piFinset (fun i : I => d.windows i)).filter (fun a =>
    Disjoint (tupleSupport a) B ∧ d.ActiveAllowed I B (tupleSupport a))

def activeWeight (d : ProductData K S r) (I : Finset (Fin r))
    (B : Finset (ExteriorPrime K S)) (P : Ideal (𝓞 K)) : ℂ :=
  ∑ a ∈ (d.activeTuples I B).filter (fun a =>
      (GeneralInactiveMass.activeIdeal K S a).val.val = P),
    slotProduct (fun i : I => d.coefficient i) a

def block (d : ProductData K S r) (I : Finset (Fin r))
    (B : Finset (ExteriorPrime K S)) : FrozenBlock K S :=
  { d.baseBlock I B with
    marks := (d.activeTuples I B).image (fun a => (GeneralInactiveMass.activeIdeal K S a).val.val)
    markWeight := d.activeWeight I B }

def inactiveEquiv (I : Finset (Fin r)) :
    Fin (Fintype.card {i : Fin r // i ∉ I}) ≃ {i : Fin r // i ∉ I} :=
  (Fintype.equivFin _).symm

def component (d : ProductData K S r) (I : Finset (Fin r)) : InactiveFamily K S where
  slots := Fintype.card {i : Fin r // i ∉ I}
  windows := fun j => d.windows (inactiveEquiv I j)
  scales := fun j => d.scales (inactiveEquiv I j)
  slotCoefficient := fun j => d.coefficient (inactiveEquiv I j)
  tuples := (Fintype.piFinset (fun j => d.windows (inactiveEquiv I j))).filter
    (fun b => d.LegalInactive (tupleSupport b))
  phase := fun _ => 1
  blocks := fun b => d.block I (tupleSupport b)
  rows := d.rows

def family (d : ProductData K S r) : MarkedFamily K S r where
  patterns := (Finset.univ : Finset (Fin r)).powerset
  components := d.component
  rows := d.rows

theorem activeWeight_exterior (d : ProductData K S r) (I : Finset (Fin r))
    (B : Finset (ExteriorPrime K S)) (P : ExteriorIdeal K S) :
    d.activeWeight I B P.val.val =
      GeneralInactiveMass.activeCoefficient K S (d.activeTuples I B)
        (fun i : I => d.coefficient i) P := by
  simp only [activeWeight, GeneralInactiveMass.activeCoefficient,
    (exterior_val_injective K S).eq_iff]

theorem activeWeight_norm_le (d : ProductData K S r) (I : Finset (Fin r))
    (B : Finset (ExteriorPrime K S)) {A : ℝ} (hA : 1 ≤ A)
    (ha : ∀ i p, p ∈ d.windows i → ‖d.coefficient i p‖ ≤ A)
    (P : Ideal (𝓞 K)) : ‖d.activeWeight I B P‖ ≤ fibreBound r * A ^ r := by
  have hslots : Fintype.card I ≤ r := by
    simpa only [Fintype.card_coe, Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ I)
  by_cases hne : ((d.activeTuples I B).filter (fun a =>
      (GeneralInactiveMass.activeIdeal K S a).val.val = P)).Nonempty
  · obtain ⟨a, ha'⟩ := hne
    rw [← (Finset.mem_filter.mp ha').2, activeWeight_exterior]
    apply GeneralInactiveMass.activeCoefficient_norm_le K S r hslots _ _ hA
    intro p hp i
    exact ha i (p i) (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hp).1 i)
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [activeWeight, hz, Finset.sum_empty, norm_zero]
    exact mul_nonneg (zero_le_one.trans (fibreBound_one_le r))
      (pow_nonneg (zero_le_one.trans hA) _)

theorem block_sourceSupported (d : ProductData K S r) (I : Finset (Fin r))
    (B : Finset (ExteriorPrime K S)) : SourceSupported K S (d.block I B) where
  rows_exterior := by
    intro k hk
    exact ((Finset.mem_filter.mp hk).2.2).choose
  marks_exterior := by
    intro P hP
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hP
    exact exterior_isExterior K S (GeneralInactiveMass.activeIdeal K S a)
  squarefree_exterior := by
    intro c hc
    exact (Finset.mem_filter.mp hc).2
  cube_exterior := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  rows_admissible := by
    intro k hk
    exact ((Finset.mem_filter.mp hk).2.2).choose_spec
  marks_admissible := by
    intro P hP
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hP
    exact (Finset.mem_filter.mp ha).2.2.1

theorem family_sourceSupported (d : ProductData K S r) :
    FamilySourceSupported K S d.family := by
  intro I _ b _
  exact d.block_sourceSupported I (tupleSupport b)

theorem component_inactive_eq (d : ProductData K S r) (I : Finset (Fin r))
    (b : Fin (Fintype.card {i : Fin r // i ∉ I}) → ExteriorPrime K S)
    (hb : b ∈ (d.component I).tuples) :
    ((d.component I).blocks b).fixed.inactive = tupleSupport b := by
  exact d.fixed_inactive _ (Finset.mem_filter.mp hb).2

theorem component_rows_subset (d : ProductData K S r) (I : Finset (Fin r))
    (b : Fin (Fintype.card {i : Fin r // i ∉ I}) → ExteriorPrime K S) :
    ((d.component I).blocks b).rows ⊆ (d.component I).rows :=
  d.baseBlock_rows_subset I (tupleSupport b)

/-- Actual ideal-fibre aggregation is identified with the literal source
row, before any norm or energy estimate is used. -/
theorem sourceRow_block_eq_active (d : ProductData K S r)
    (I : Finset (Fin r)) (B : Finset (ExteriorPrime K S))
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (V : SmoothAnnularTest) (k : Ideal (𝓞 K)) :
    sourceRow K S D (d.block I B) F θ V k =
      ∑ a ∈ d.activeTuples I B, slotProduct (fun i : I => d.coefficient i) a *
        markKernel K S D (d.baseBlock I B) F θ V
          (GeneralInactiveMass.activeIdeal K S a).val.val k := by
  rw [block, sourceRow_reweight]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := d.activeTuples I B)
    (t := (d.activeTuples I B).image (fun a => (GeneralInactiveMass.activeIdeal K S a).val.val))
    (g := fun a => (GeneralInactiveMass.activeIdeal K S a).val.val)
    (fun a ha => Finset.mem_image_of_mem _ ha)
    (fun a => slotProduct (fun i : I => d.coefficient i) a *
      markKernel K S D (d.baseBlock I B) F θ V
        (GeneralInactiveMass.activeIdeal K S a).val.val k)]
  apply Finset.sum_congr rfl
  intro P _
  rw [activeWeight, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [(Finset.mem_filter.mp ha).2]

/-- The kernel of the original prime-choice projection.  Both fixed
collision tests and the actual marked-ideal annulus are retained. -/
def projectionKernel (d : ProductData K S r) (I : Finset (Fin r))
    (B A : Finset (ExteriorPrime K S)) (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (V : SmoothAnnularTest) (k : Ideal (𝓞 K)) : ℂ :=
  if d.LegalInactive B then
    if d.ActiveAllowed I B A then
      markKernel K S D (d.baseBlock I B) F θ V (primeSetIdeal K S A).val.val k
    else 0
  else 0

/-- A nonzero projected term already satisfies every original mark
collision test.  No disjointness or coprimality is imposed afterwards. -/
theorem projectionKernel_marks_away_of_ne_zero (d : ProductData K S r)
    (I : Finset (Fin r)) (B A : Finset (ExteriorPrime K S))
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : SmoothAnnularTest)
    (k : ExteriorIdeal K S)
    (hne : d.projectionKernel D I B A F θ V k.val.val ≠ 0) :
    ∀ q ∈ A ∪ B, ¬q.val.asIdeal ∣ k.val.val ∧ d.Away q := by
  have hB : d.LegalInactive B := by
    by_contra hB
    exact hne (by simp only [projectionKernel, if_neg hB])
  have hA : d.ActiveAllowed I B A := by
    by_contra hA
    exact hne (by simp only [projectionKernel, if_pos hB, if_neg hA])
  have hkernel :
      markKernel K S D (d.baseBlock I B) F θ V (primeSetIdeal K S A).val.val k.val.val ≠ 0 := by
    simpa only [projectionKernel, if_pos hB, if_pos hA] using hne
  have hk : k.val.val ∈ (d.baseBlock I B).rows := by
    by_contra hk
    exact hkernel (by simp only [markKernel, if_neg hk])
  have hrow : RowAdmissible K S (d.fixed B) k :=
    ((Finset.mem_filter.mp hk).2.2).choose_spec
  have hkP : IsCoprime k.val.val (primeSetIdeal K S A).val.val := by
    by_contra hkP
    exact hkernel (markKernel_eq_zero_of_not_coprime K S D (d.baseBlock I B)
      F θ V (primeSetIdeal K S A).val.val k.val.val hkP)
  intro q hq
  rcases Finset.mem_union.mp hq with hqA | hqB
  · have hqs : q ∈ exteriorSupport K S (primeSetIdeal K S A) := by
      rw [exteriorSupport_primeSetIdeal]
      exact hqA
    refine ⟨?_, hA.1.prime_away q hqs⟩
    intro hqk
    exact q.val.prime.not_unit (hkP.isUnit_of_dvd' hqk
      ((prime_dvd_primeSetIdeal_iff K S A q).mpr hqA))
  · have hqf : q ∈ (d.fixed B).inactive := by
      rw [d.fixed_inactive B hB]
      exact hqB
    exact ⟨hrow.inactive_away q hqf, hB q hqB⟩

/-- Finite projection of the original tuple and prime-MarkChoice sum.
Its summands are literal `reflectedTerm` values through `sourceTerm` and
its genuine source index, with the original masks left in place. -/
def projectedSourceRow (d : ProductData K S r) (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (V : SmoothAnnularTest) (k : Ideal (𝓞 K)) : ℂ :=
  if k ∈ d.rows then
    ∑ p ∈ Fintype.piFinset d.windows, slotProduct d.coefficient p *
      ∑ A ∈ (tupleSupport p).powerset,
        d.projectionKernel D (activeSlots p A) (tupleSupport p \ A) A F θ V k
  else 0

theorem saturated_active_sum (d : ProductData K S r) (I : Finset (Fin r))
    (B : Finset (ExteriorPrime K S)) (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (V : SmoothAnnularTest) (k : Ideal (𝓞 K)) :
    (∑ a ∈ Fintype.piFinset (fun i : I => d.windows i),
      if Disjoint (tupleSupport a) B then
        slotProduct (fun i : I => d.coefficient i) a *
          d.projectionKernel D I B (tupleSupport a) F θ V k else 0) =
      if d.LegalInactive B then sourceRow K S D (d.block I B) F θ V k else 0 := by
  by_cases hB : d.LegalInactive B
  · rw [if_pos hB, d.sourceRow_block_eq_active D I B F θ V k]
    rw [activeTuples, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hd : Disjoint (tupleSupport a) B <;>
      by_cases ha : d.ActiveAllowed I B (tupleSupport a) <;>
        simp only [projectionKernel, hB, hd, ha, if_true, if_false, and_true,
          and_false, false_and, true_and, mul_zero, GeneralInactiveMass.activeIdeal]
  · simp only [projectionKernel, hB, if_false, mul_zero, ite_self, Finset.sum_const_zero]

theorem sourceInactiveRow_component (d : ProductData K S r) (I : Finset (Fin r))
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (V : SmoothAnnularTest) (k : Ideal (𝓞 K)) :
    sourceInactiveRow K S D (d.component I) F θ V k =
      ∑ b ∈ Fintype.piFinset (fun i : {i : Fin r // i ∉ I} => d.windows i),
        slotProduct (fun i : {i : Fin r // i ∉ I} => d.coefficient i) b *
          (if d.LegalInactive (tupleSupport b) then
            sourceRow K S D (d.block I (tupleSupport b)) F θ V k else 0) := by
  symm
  rw [sum_piFinset_equiv (inactiveEquiv I)]
  simp only [slotProduct_unindex, tupleSupport_equiv]
  simp only [sourceInactiveRow, component, InactiveFamily.coefficient, mul_one,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : d.LegalInactive (tupleSupport b)
  · simp only [if_pos hb]
    rfl
  · simp only [if_neg hb, mul_zero]

/-- The actual original finite projection is exactly the concrete source
family.  This is a proved identity, not a field or input of the family. -/
theorem projectedSourceRow_eq_sourceMarkedRow (d : ProductData K S r)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (V : SmoothAnnularTest) (k : Ideal (𝓞 K)) :
    d.projectedSourceRow D F θ V k = sourceMarkedRow K S D d.family F θ V k := by
  by_cases hk : k ∈ d.rows
  · rw [projectedSourceRow, if_pos hk,
      weighted_primeChoices_reindex d.windows d.coefficient
        (fun I B A => d.projectionKernel D I B A F θ V k)]
    change _ = ∑ I ∈ (Finset.univ : Finset (Fin r)).powerset,
      if k ∈ d.rows then sourceInactiveRow K S D (d.component I) F θ V k else 0
    simp only [if_pos hk]
    apply Finset.sum_congr rfl
    intro I _
    rw [d.sourceInactiveRow_component D I F θ V k]
    apply Finset.sum_congr rfl
    intro b _
    rw [d.saturated_active_sum D I (tupleSupport b) F θ V k]
  · simp only [projectedSourceRow, sourceMarkedRow, family, component, hk, if_false,
      Finset.sum_const_zero]

def projectedSourceEnergy (d : ProductData K S r) (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (V : SmoothAnnularTest) : ℝ :=
  ∑ k ∈ d.rows, ‖d.projectedSourceRow D F θ V k‖ ^ 2

theorem projectedSourceEnergy_eq_sourceMarkedEnergy (d : ProductData K S r)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : SmoothAnnularTest) :
    d.projectedSourceEnergy D F θ V = sourceMarkedEnergy K S D d.family F θ V := by
  simp only [projectedSourceEnergy, projectedSourceRow_eq_sourceMarkedRow,
    sourceMarkedEnergy, family]

section OriginalIndices

variable (d₀ : MarkedDatum K S) (X : ℝ)
variable (windows : Fin r → Finset (ExteriorPrime K S)) (scales : Fin r → ℝ)
variable (coefficient : Fin r → ExteriorPrime K S → ℂ) (rows : Finset (Ideal (𝓞 K)))
variable (ranges : Finset (Fin r) → Finset (ExteriorPrime K S) →
  BlockRanges K S d₀.frozen d₀.puncture)

local notation "pd" => ofMarkedDatum d₀ X windows scales coefficient rows ranges

theorem ofMarkedDatum_legal (A : MarkChoice K S d₀) :
    (pd).LegalInactive (d₀.marks \ A.val) := by
  intro q hq
  exact ⟨(d₀.marks_coprime q (Finset.mem_sdiff.mp hq).1).2.1,
    (d₀.marks_coprime q (Finset.mem_sdiff.mp hq).1).2.2⟩

theorem ofMarkedDatum_fixed (A : MarkChoice K S d₀) :
    (pd).fixed (d₀.marks \ A.val) = splitFixed K S d₀ A := by
  have hf : (d₀.marks \ A.val).filter (pd).Away = d₀.marks \ A.val :=
    Finset.filter_eq_self.mpr (ofMarkedDatum_legal d₀ X windows scales coefficient rows ranges A)
  let supportType := {B : Finset (ExteriorPrime K S) // (pd).LegalInactive B}
  let pack : supportType → FixedData K S := fun B =>
    { frozen := d₀.frozen
      puncture := d₀.puncture
      puncture_squarefree := d₀.puncture_squarefree
      rowUnit := d₀.rowUnit
      inactive := B.val
      inactive_away := B.property }
  have hs :
      (⟨(d₀.marks \ A.val).filter (pd).Away,
        fun q hq => (Finset.mem_filter.mp hq).2⟩ : supportType) =
        ⟨d₀.marks \ A.val, ofMarkedDatum_legal d₀ X windows scales coefficient rows ranges A⟩ :=
    Subtype.ext hf
  exact congrArg pack hs

/-- Each source summand of the concrete factory is exactly the original
reflection index with its canonical column and mark--cube zero extension. -/
theorem sourceTerm_ofMarkedDatum (hD : AllowedGeneratorInput K S D)
    (A : MarkChoice K S d₀) (I : Finset (Fin r))
    (state : FrozenState K S d₀.frozen d₀.puncture)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : ℝ → ℂ)
    (c b : ExteriorIdeal K S) :
    sourceTerm K S D ((pd).baseBlock I (d₀.marks \ A.val)) state F θ V
      d₀.moving.val.val (primeSetIdeal K S A.val).val.val c.val.val b.val.val =
      extendColumn K S state (extendMarkedColumn K S state A.val
        (fun cb => reflectedTerm K S D d₀
          ((reflectionSigmaEquiv K S d₀).symm ⟨state, A, cb⟩) F θ V X)) c b := by
  unfold sourceTerm
  rw [dif_pos (exterior_isExterior K S d₀.moving),
    dif_pos (exterior_isExterior K S (primeSetIdeal K S A.val)),
    dif_pos (exterior_isExterior K S c), dif_pos (exterior_isExterior K S b)]
  change (if hr : RowAdmissible K S ((pd).fixed (d₀.marks \ A.val)) d₀.moving then
    if hm : MarkAdmissible K S ((pd).fixed (d₀.marks \ A.val)) (primeSetIdeal K S A.val) then
      literalTerm K S D ((pd).fixed (d₀.marks \ A.val)) state F θ (fun _ => 1) V X
        d₀.moving (primeSetIdeal K S A.val) c b hr hm else 0 else 0) = _
  have hf : (d₀.marks \ A.val).filter (pd).Away = d₀.marks \ A.val :=
    Finset.filter_eq_self.mpr (ofMarkedDatum_legal d₀ X windows scales coefficient rows ranges A)
  let supportType := {B : Finset (ExteriorPrime K S) // (pd).LegalInactive B}
  let pack : supportType → FixedData K S := fun B =>
    { frozen := d₀.frozen
      puncture := d₀.puncture
      puncture_squarefree := d₀.puncture_squarefree
      rowUnit := d₀.rowUnit
      inactive := B.val
      inactive_away := B.property }
  let filtered : supportType := ⟨(d₀.marks \ A.val).filter (pd).Away,
    fun q hq => (Finset.mem_filter.mp hq).2⟩
  let original : supportType :=
    ⟨d₀.marks \ A.val, ofMarkedDatum_legal d₀ X windows scales coefficient rows ranges A⟩
  have hs : filtered = original := Subtype.ext hf
  change (if hr : RowAdmissible K S (pack filtered) d₀.moving then
    if hm : MarkAdmissible K S (pack filtered) (primeSetIdeal K S A.val) then
      literalTerm K S D (pack filtered) state F θ (fun _ => 1) V X
        d₀.moving (primeSetIdeal K S A.val) c b hr hm else 0 else 0) = _
  rw [hs]
  change (if hr : RowAdmissible K S (splitFixed K S d₀ A) d₀.moving then
    if hm : MarkAdmissible K S (splitFixed K S d₀ A) (primeSetIdeal K S A.val) then
      literalTerm K S D (splitFixed K S d₀ A) state F θ (fun _ => 1) V X
        d₀.moving (primeSetIdeal K S A.val) c b hr hm else 0 else 0) = _
  rw [dif_pos (splitRow_admissible K S d₀ A), dif_pos (splitMark_admissible K S d₀ A),
    literalTerm_eq_generalAtom K S D (splitFixed K S d₀ A) state hD]
  exact (extended_reflectionSummand_eq_generalAtom K S D hD F θ d₀ state A V X (c, b)).symm

/-- A genuine finite projection of the original `reflectedTuple` series:
the indices are the original reflection sigma indices, not new formal
coefficients.  The common row and column restrictions are explicit. -/
def originalIndexProjection (A : MarkChoice K S d₀) (I : Finset (Fin r))
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : SmoothAnnularTest) : ℂ :=
  let base := (pd).baseBlock I (d₀.marks \ A.val)
  if d₀.moving.val.val ∈ base.rows then
    ∑ state ∈ (ranges I (d₀.marks \ A.val)).states,
      ∑ c ∈ base.squarefreeColumns.attach, ∑ b ∈ base.cubeColumns.attach,
        extendColumn K S state (extendMarkedColumn K S state A.val
          (fun cb => reflectedTerm K S D d₀
            ((reflectionSigmaEquiv K S d₀).symm ⟨state, A, cb⟩) F θ V.toFun X))
          (toExterior K S c.val (Finset.mem_filter.mp c.property).2)
          (toExterior K S b.val (Finset.mem_filter.mp b.property).2)
  else 0

theorem markKernel_ofMarkedDatum (hD : AllowedGeneratorInput K S D)
    (A : MarkChoice K S d₀) (I : Finset (Fin r))
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : SmoothAnnularTest) :
    markKernel K S D ((pd).baseBlock I (d₀.marks \ A.val)) F θ V
      (primeSetIdeal K S A.val).val.val d₀.moving.val.val =
      originalIndexProjection D d₀ X windows scales coefficient rows ranges A I F θ V := by
  unfold markKernel originalIndexProjection
  by_cases hk : d₀.moving.val.val ∈ ((pd).baseBlock I (d₀.marks \ A.val)).rows
  · simp only [if_pos hk]
    apply Finset.sum_congr rfl
    intro state _
    rw [← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro c _
    rw [← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro b _
    exact sourceTerm_ofMarkedDatum D d₀ X windows scales coefficient rows ranges hD A I state
      F θ V.toFun (toExterior K S c.val (Finset.mem_filter.mp c.property).2)
      (toExterior K S b.val (Finset.mem_filter.mp b.property).2)
  · simp only [if_neg hk]

/-- The concrete product factory projects precisely the original marked
reflection, on the actual active ideal norm annulus. -/
theorem projectionKernel_ofMarkedDatum (hD : AllowedGeneratorInput K S D)
    (A : MarkChoice K S d₀) (I : Finset (Fin r))
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : SmoothAnnularTest) :
    (pd).projectionKernel D I (d₀.marks \ A.val) A.val F θ V d₀.moving.val.val =
      if (ranges I (d₀.marks \ A.val)).markScale ≤ exteriorNorm K S (primeSetIdeal K S A.val) ∧
          exteriorNorm K S (primeSetIdeal K S A.val) ≤
            2 * (ranges I (d₀.marks \ A.val)).markScale then
        originalIndexProjection D d₀ X windows scales coefficient rows ranges A I F θ V
      else 0 := by
  have hm : MarkAdmissible K S ((pd).fixed (d₀.marks \ A.val)) (primeSetIdeal K S A.val) := by
    rw [ofMarkedDatum_fixed d₀ X windows scales coefficient rows ranges A]
    exact splitMark_admissible K S d₀ A
  rw [projectionKernel,
    if_pos (ofMarkedDatum_legal d₀ X windows scales coefficient rows ranges A)]
  simp only [ActiveAllowed, hm, true_and]
  rw [markKernel_ofMarkedDatum D d₀ X windows scales coefficient rows ranges hD A I F θ V]
  rfl

end OriginalIndices

section OriginalTuples

open HeckeSkeleton.LowEnergy.GeneralRows
open HeckeSkeleton.LowEnergy.GeneralProductReconstruction

variable (k label puncture : ExteriorIdeal K S)
variable (hpuncture : Squarefree puncture.val.val) (u : S.unit K) (X : ℝ)
variable (windows : Fin r → Finset (ExteriorPrime K S)) (scales : Fin r → ℝ)
variable (coefficient : Fin r → ExteriorPrime K S → ℂ) (rows : Finset (Ideal (𝓞 K)))
variable (ranges : Finset (Fin r) → Finset (ExteriorPrime K S) →
  BlockRanges K S (reflectedFrozen K S k label puncture) puncture)

/-- The common block data of the original row and fourth-power label.
It is defined before selecting a tuple or making a collision test. -/
def ofOriginalRow : ProductData K S r where
  frozen := reflectedFrozen K S k label puncture
  puncture := puncture
  puncture_squarefree := hpuncture
  rowUnit := u
  X := X
  windows := windows
  scales := scales
  coefficient := coefficient
  rows := rows
  ranges := ranges

local notation "od" => ofOriginalRow k label puncture hpuncture u X
  windows scales coefficient rows ranges

theorem ofOriginalRow_eq_ofMarkedDatum (p : Fin r → ExteriorPrime K S)
    (hp : TupleAdmissible K S k label puncture p) :
    od = ofMarkedDatum
      (markedDatum K S k label puncture hpuncture u (tupleSupport p) hp)
      X windows scales coefficient rows ranges := rfl

/-- The same row, label and puncture collision which vanishes in the
primal canonical sum also vanishes in each finite reflected projection. -/
theorem projectionKernel_eq_zero_of_not_admissible
    (p : Fin r → ExteriorPrime K S) (hp : ¬TupleAdmissible K S k label puncture p)
    (I : Finset (Fin r)) (A : Finset (ExteriorPrime K S)) (hA : A ⊆ tupleSupport p)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : SmoothAnnularTest) :
    (od).projectionKernel D I (tupleSupport p \ A) A F θ V
      (movingRow K S k label puncture).val.val = 0 := by
  by_contra hne
  apply hp
  intro q hq
  have hqAB : q ∈ A ∪ (tupleSupport p \ A) := by
    by_cases hqA : q ∈ A
    · exact Finset.mem_union_left _ hqA
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hq, hqA⟩)
  have haway := (od).projectionKernel_marks_away_of_ne_zero D I (tupleSupport p \ A)
    A F θ V (movingRow K S k label puncture) hne q hqAB
  change (¬q.val.asIdeal ∣ (movingRow K S k label puncture).val.val) ∧
    (¬q.val.asIdeal ∣ (reflectedFrozen K S k label puncture).val.val) ∧
    ¬q.val.asIdeal ∣ puncture.val.val at haway
  refine ⟨?_, ?_, haway.2.2⟩
  · intro hqk
    have hsplit := congrArg (fun J : ExteriorIdeal K S => J.val.val)
      (moving_frozenRow_eq K S k label puncture)
    change (movingRow K S k label puncture).val.val *
      (frozenRow K S k label puncture).val.val = k.val.val at hsplit
    rw [← hsplit] at hqk
    rcases q.val.prime.dvd_mul.mp hqk with hmove | hfrozen
    · exact haway.1 hmove
    · apply haway.2.1
      change q.val.asIdeal ∣ (frozenRow K S k label puncture).val.val * label.val.val ^ 4
      exact dvd_mul_of_dvd_left hfrozen _
  · intro hqlabel
    apply haway.2.1
    change q.val.asIdeal ∣ (frozenRow K S k label puncture).val.val * label.val.val ^ 4
    exact dvd_mul_of_dvd_right
      (dvd_trans hqlabel (dvd_pow_self _ (by decide : 4 ≠ 0))) _

/-- The finite projection of one original surviving tuple, summed over
all of its genuine prime choices.  Every summand uses the original
reflection sigma index through `originalIndexProjection`. -/
def originalTupleProjection (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (p : Fin r → ExteriorPrime K S) (hp : TupleAdmissible K S k label puncture p)
    (V : SmoothAnnularTest) : ℂ :=
  let d₀ := markedDatum K S k label puncture hpuncture u (tupleSupport p) hp
  ∑ A ∈ (tupleSupport p).powerset.attach,
    if (ranges (activeSlots p A.val) (tupleSupport p \ A.val)).markScale ≤
          exteriorNorm K S (primeSetIdeal K S A.val) ∧
        exteriorNorm K S (primeSetIdeal K S A.val) ≤
          2 * (ranges (activeSlots p A.val) (tupleSupport p \ A.val)).markScale then
      originalIndexProjection D d₀ X windows scales coefficient rows ranges
        ⟨A.val, Finset.mem_powerset.mp A.property⟩ (activeSlots p A.val) F θ V
    else 0

theorem primeChoiceProjection_eq_originalTupleProjection
    (hD : AllowedGeneratorInput K S D) (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (p : Fin r → ExteriorPrime K S) (hp : TupleAdmissible K S k label puncture p)
    (V : SmoothAnnularTest) :
    (∑ A ∈ (tupleSupport p).powerset,
      (od).projectionKernel D (activeSlots p A) (tupleSupport p \ A) A F θ V
        (movingRow K S k label puncture).val.val) =
      originalTupleProjection D k label puncture hpuncture u X windows scales coefficient
        rows ranges F θ p hp V := by
  unfold originalTupleProjection
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro A _
  exact projectionKernel_ofMarkedDatum D
    (markedDatum K S k label puncture hpuncture u (tupleSupport p) hp)
    X windows scales coefficient rows ranges hD
    ⟨A.val, Finset.mem_powerset.mp A.property⟩ (activeSlots p A.val) F θ V

/-- The factory's original full tuple sum is exactly the finite original
reflection projection over the primal noncolliding tuples.  The tuple
filter is proved by the original zero masks, not supplied as an identity. -/
theorem projectedSourceRow_eq_originalTuples
    (hD : AllowedGeneratorInput K S D) (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (V : SmoothAnnularTest) :
    (od).projectedSourceRow D F θ V (movingRow K S k label puncture).val.val =
      if (movingRow K S k label puncture).val.val ∈ rows then
        ∑ p ∈ ((Fintype.piFinset windows).filter
          (TupleAdmissible K S k label puncture)).attach,
          slotProduct coefficient p.val *
            originalTupleProjection D k label puncture hpuncture u X windows scales coefficient
              rows ranges F θ p.val (Finset.mem_filter.mp p.property).2 V
      else 0 := by
  let H := fun p : Fin r → ExteriorPrime K S =>
    ∑ A ∈ (tupleSupport p).powerset,
      (od).projectionKernel D (activeSlots p A) (tupleSupport p \ A) A F θ V
        (movingRow K S k label puncture).val.val
  have hfilter : (∑ p ∈ Fintype.piFinset windows, slotProduct coefficient p * H p) =
      ∑ p ∈ (Fintype.piFinset windows).filter (TupleAdmissible K S k label puncture),
        slotProduct coefficient p * H p := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : TupleAdmissible K S k label puncture p
    · rw [if_pos hp]
    · rw [if_neg hp]
      have hz : H p = 0 := by
        apply Finset.sum_eq_zero
        intro A hA
        exact projectionKernel_eq_zero_of_not_admissible D k label puncture hpuncture u X
          windows scales coefficient rows ranges p hp (activeSlots p A) A
          (Finset.mem_powerset.mp hA) F θ V
      rw [hz, mul_zero]
  change (if (movingRow K S k label puncture).val.val ∈ rows then
    ∑ p ∈ Fintype.piFinset windows, slotProduct coefficient p * H p else 0) = _
  by_cases hk : (movingRow K S k label puncture).val.val ∈ rows
  · simp only [if_pos hk]
    rw [hfilter, ← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    exact primeChoiceProjection_eq_originalTupleProjection D k label puncture hpuncture u X
      windows scales coefficient rows ranges hD F θ p.val (Finset.mem_filter.mp p.property).2 V
  · simp only [if_neg hk]

/-- The same identity ends directly at the concrete family used by the
uniform energy theorem. -/
theorem sourceMarkedRow_eq_originalTuples
    (hD : AllowedGeneratorInput K S D) (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (V : SmoothAnnularTest) :
    sourceMarkedRow K S D (od).family F θ V (movingRow K S k label puncture).val.val =
      if (movingRow K S k label puncture).val.val ∈ rows then
        ∑ p ∈ ((Fintype.piFinset windows).filter
          (TupleAdmissible K S k label puncture)).attach,
          slotProduct coefficient p.val *
            originalTupleProjection D k label puncture hpuncture u X windows scales coefficient
              rows ranges F θ p.val (Finset.mem_filter.mp p.property).2 V
      else 0 := by
  rw [← (od).projectedSourceRow_eq_sourceMarkedRow D F θ V]
  exact projectedSourceRow_eq_originalTuples D k label puncture hpuncture u X windows scales
    coefficient rows ranges hD F θ V

end OriginalTuples

end ProductData

#print axioms sum_primeChoices_eq_saturated_patterns
#print axioms weighted_primeChoices_reindex
#print axioms ProductData.activeWeight_norm_le
#print axioms ProductData.family_sourceSupported
#print axioms ProductData.sourceRow_block_eq_active
#print axioms ProductData.projectedSourceRow_eq_sourceMarkedRow
#print axioms ProductData.projectedSourceEnergy_eq_sourceMarkedEnergy
#print axioms ProductData.sourceTerm_ofMarkedDatum
#print axioms ProductData.projectionKernel_ofMarkedDatum
#print axioms ProductData.projectionKernel_eq_zero_of_not_admissible
#print axioms ProductData.projectedSourceRow_eq_originalTuples
#print axioms ProductData.sourceMarkedRow_eq_originalTuples

end HeckeSkeleton.LowEnergy.GeneralTupleBlocks
