import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentOriginalAtlas
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocationPadding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonTupleFibers
import Mathlib.Algebra.BigOperators.Fin

/-!
# The actual original parent has an injective whole-factor tuple

The coordinates are the two original plain ideals followed by every
original prime occurrence. Equality of these ordered tuples recovers
the entire original column. No uniqueness of the product ideal is
asserted or needed. Unit padding fixes the length before the moving
parent is chosen, and appending the two columns gives the genuine pair
tuple used in the first terminal count.

Every factor of a column in the original exterior support is exterior:
it divides the complete original ideal. The exterior-valued tuple is
therefore constructed from the same actual carrier, including zero
prime slots and repeated prime occurrences. Existing support and
amplifier tuple counts can consume it without a new injectivity input.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis

namespace OriginalParentTuple

/-- Append only unit factors, preserving the literal occurrence map
already used by the allocation padding. -/
def padUnit {α : Type*} [One α] {n cap : ℕ} (h : n ≤ cap)
    (f : Fin n → α) : Fin cap → α :=
  fun i => Fin.append f (fun _ : Fin (cap - n) => 1)
    (Fin.cast (by omega : cap = n + (cap - n)) i)

@[simp] theorem padUnit_original {α : Type*} [One α] {n cap : ℕ}
    (h : n ≤ cap) (f : Fin n → α) (i : Fin n) :
    padUnit h f (AllocationMass.finInclusion h i) = f i := by
  unfold padUnit
  have hi : Fin.cast (by omega : cap = n + (cap - n))
      (AllocationMass.finInclusion h i) = Fin.castAdd (cap - n) i := Fin.ext rfl
  rw [hi, Fin.append_left]

theorem padUnit_injective {α : Type*} [One α] {n cap : ℕ} (h : n ≤ cap) :
    Function.Injective (padUnit (α := α) h) := by
  intro f g he
  funext i
  simpa only [padUnit_original] using
    congrFun he (AllocationMass.finInclusion h i)

@[simp] theorem prod_padUnit {α : Type*} [CommMonoid α] {n cap : ℕ}
    (h : n ≤ cap) (f : Fin n → α) :
    (∏ i, padUnit h f i) = ∏ i, f i := by
  calc
    _ = ∏ i : Fin (n + (cap - n)), Fin.append f (fun _ : Fin (cap - n) => 1) i :=
      Fin.prod_congr' _ (by omega : cap = n + (cap - n))
    _ = _ := by
      rw [Fin.prod_univ_add]
      simp only [Fin.append_left, Fin.append_right, Finset.prod_const_one, mul_one]

/-- The two complete ordered tuples use the fixed arithmetic length
`2*n`; the cast changes only the presentation of that natural number. -/
def pairAppend {α : Type*} {n : ℕ} (f g : Fin n → α) : Fin (2 * n) → α :=
  fun i => Fin.append f g (Fin.cast (two_mul n) i)

@[simp] theorem pairAppend_left {α : Type*} {n : ℕ} (f g : Fin n → α) (i : Fin n) :
    pairAppend f g (Fin.cast (two_mul n).symm (Fin.castAdd n i)) = f i := by
  unfold pairAppend
  have he : Fin.cast (two_mul n) (Fin.cast (two_mul n).symm (Fin.castAdd n i)) =
      Fin.castAdd n i := Fin.ext rfl
  rw [he, Fin.append_left]

@[simp] theorem pairAppend_right {α : Type*} {n : ℕ} (f g : Fin n → α) (i : Fin n) :
    pairAppend f g (Fin.cast (two_mul n).symm (Fin.natAdd n i)) = g i := by
  unfold pairAppend
  have he : Fin.cast (two_mul n) (Fin.cast (two_mul n).symm (Fin.natAdd n i)) =
      Fin.natAdd n i := Fin.ext rfl
  rw [he, Fin.append_right]

theorem pairAppend_injective {α : Type*} {n : ℕ} :
    Function.Injective (fun fg : (Fin n → α) × (Fin n → α) => pairAppend fg.1 fg.2) := by
  intro fg uv he
  apply Prod.ext
  · funext i
    have hi := congrFun he (Fin.cast (two_mul n).symm (Fin.castAdd n i))
    simpa only [pairAppend_left] using hi
  · funext i
    have hi := congrFun he (Fin.cast (two_mul n).symm (Fin.natAdd n i))
    simpa only [pairAppend_right] using hi

@[simp] theorem prod_pairAppend {α : Type*} [CommMonoid α] {n : ℕ}
    (f g : Fin n → α) : (∏ i, pairAppend f g i) = (∏ i, f i) * ∏ i, g i := by
  calc
    _ = ∏ i : Fin (n + n), Fin.append f g i := Fin.prod_congr' _ (two_mul n)
    _ = _ := by
      rw [Fin.prod_univ_add]
      simp only [Fin.append_left, Fin.append_right]

theorem pairAppend_map {α β : Type*} {n : ℕ} (f g : Fin n → α) (u : α → β) :
    (fun i => u (pairAppend f g i)) = pairAppend (fun i => u (f i)) (fun i => u (g i)) := by
  funext i
  unfold pairAppend
  generalize Fin.cast (two_mul n) i = j
  cases j using Fin.addCases <;> simp only [Fin.append_left, Fin.append_right]

end OriginalParentTuple

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {Γ : Subgroup A.U}
variable {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}

namespace ParentRawAtoms

variable (raw : ParentRawAtoms
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t Y₁ Y₂)

/-- Both plain factors and all original prime occurrences, in their
original order. For zero prime slots the two plain factors remain. -/
def originalIdealFactors (v : raw.Column) :
    Fin (d.geometry.slotCount + 2) → Ideal (𝓞 K) :=
  Fin.cons v.1.1.val (Fin.cons v.1.2.val (fun i => (v.2 i).asIdeal))

@[simp] theorem originalIdealFactors_plain₁ (v : raw.Column) :
    raw.originalIdealFactors v 0 = v.1.1.val := by
  simp only [originalIdealFactors, Fin.cons_zero]

@[simp] theorem originalIdealFactors_plain₂ (v : raw.Column) :
    raw.originalIdealFactors v 1 = v.1.2.val := by
  simp only [originalIdealFactors, Fin.cons_one, Fin.cons_zero]

@[simp] theorem originalIdealFactors_slot (v : raw.Column) (i : Fin d.geometry.slotCount) :
    raw.originalIdealFactors v i.succ.succ = (v.2 i).asIdeal := by
  simp only [originalIdealFactors, Fin.cons_succ]

/-- Injectivity follows from every ordered coordinate, before any
exterior filter or common-support quotient is applied. -/
theorem originalIdealFactors_injective : Function.Injective raw.originalIdealFactors := by
  intro v w he
  change Fin.cons v.1.1.val (Fin.cons v.1.2.val (fun i => (v.2 i).asIdeal)) =
    Fin.cons w.1.1.val (Fin.cons w.1.2.val (fun i => (w.2 i).asIdeal)) at he
  obtain ⟨h₁, hrest⟩ := Fin.cons_inj.mp he
  obtain ⟨h₂, hslots⟩ := Fin.cons_inj.mp hrest
  apply Prod.ext
  · exact Prod.ext (Subtype.ext h₁) (Subtype.ext h₂)
  · funext i
    exact HeightOneSpectrum.asIdeal_injective (congrFun hslots i)

theorem originalIdealFactors_product (v : raw.Column) :
    PowerfulDiagonal.tupleIdeal (raw.originalIdealFactors v) = raw.columnIdeal v := by
  simp only [PowerfulDiagonal.tupleIdeal, originalIdealFactors, Fin.prod_cons,
    columnIdeal, mul_assoc]

/-- The fixed occurrence cap changes only the number of appended
unit factors. It never removes an original occurrence. -/
def paddedOriginalIdealFactors (cap : ℕ) (hcap : d.geometry.slotCount ≤ cap)
    (v : raw.Column) : Fin (cap + 2) → Ideal (𝓞 K) :=
  OriginalParentTuple.padUnit (Nat.add_le_add_right hcap 2) (raw.originalIdealFactors v)

@[simp] theorem paddedOriginalIdealFactors_original (cap : ℕ)
    (hcap : d.geometry.slotCount ≤ cap) (v : raw.Column)
    (i : Fin (d.geometry.slotCount + 2)) :
    raw.paddedOriginalIdealFactors cap hcap v
        (AllocationMass.finInclusion (Nat.add_le_add_right hcap 2) i) =
      raw.originalIdealFactors v i :=
  OriginalParentTuple.padUnit_original _ _ i

theorem paddedOriginalIdealFactors_injective (cap : ℕ)
    (hcap : d.geometry.slotCount ≤ cap) :
    Function.Injective (raw.paddedOriginalIdealFactors cap hcap) :=
  (OriginalParentTuple.padUnit_injective _).comp raw.originalIdealFactors_injective

theorem paddedOriginalIdealFactors_product (cap : ℕ)
    (hcap : d.geometry.slotCount ≤ cap) (v : raw.Column) :
    PowerfulDiagonal.tupleIdeal (raw.paddedOriginalIdealFactors cap hcap v) =
      raw.columnIdeal v := by
  unfold PowerfulDiagonal.tupleIdeal paddedOriginalIdealFactors
  rw [OriginalParentTuple.prod_padUnit]
  exact raw.originalIdealFactors_product v

theorem paddedOriginalIdealFactors_ne_zero (cap : ℕ)
    (hcap : d.geometry.slotCount ≤ cap) (v : raw.Column) (i : Fin (cap + 2)) :
    raw.paddedOriginalIdealFactors cap hcap v i ≠ 0 := by
  have h : (∏ i, raw.paddedOriginalIdealFactors cap hcap v i) ≠ 0 := by
    change PowerfulDiagonal.tupleIdeal _ ≠ 0
    rw [raw.paddedOriginalIdealFactors_product]
    exact raw.columnIdeal_ne_zero v
  exact Finset.prod_ne_zero_iff.mp h i (Finset.mem_univ i)

theorem paddedOriginalIdealFactors_dvd (cap : ℕ)
    (hcap : d.geometry.slotCount ≤ cap) (v : raw.Column) (i : Fin (cap + 2)) :
    raw.paddedOriginalIdealFactors cap hcap v i ∣ raw.columnIdeal v := by
  rw [← raw.paddedOriginalIdealFactors_product cap hcap v]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem paddedOriginalIdealFactors_coprime (cap : ℕ)
    (hcap : d.geometry.slotCount ≤ cap) (v : raw.Column) (hv : v ∈ raw.exteriorColumns)
    (i : Fin (cap + 2)) :
    IsCoprime (raw.paddedOriginalIdealFactors cap hcap v i) A.cS :=
  (Finset.mem_filter.mp hv).2.2.of_isCoprime_of_dvd_left
    (raw.paddedOriginalIdealFactors_dvd cap hcap v i)

/-- The actual ordered pair tuple for the fixed first-tail factor
count `2*(cap+2)`. -/
def originalPairIdealFactors (cap : ℕ) (hcap : d.geometry.slotCount ≤ cap)
    (v : raw.Column × raw.Column) : Fin (2 * (cap + 2)) → Ideal (𝓞 K) :=
  OriginalParentTuple.pairAppend
    (raw.paddedOriginalIdealFactors cap hcap v.1)
    (raw.paddedOriginalIdealFactors cap hcap v.2)

theorem originalPairIdealFactors_injective (cap : ℕ)
    (hcap : d.geometry.slotCount ≤ cap) :
    Function.Injective (raw.originalPairIdealFactors cap hcap) := by
  intro v w he
  have h := OriginalParentTuple.pairAppend_injective he
  exact Prod.ext
    (raw.paddedOriginalIdealFactors_injective cap hcap (congrArg Prod.fst h))
    (raw.paddedOriginalIdealFactors_injective cap hcap (congrArg Prod.snd h))

theorem originalPairIdealFactors_product (cap : ℕ)
    (hcap : d.geometry.slotCount ≤ cap) (v : raw.Column × raw.Column) :
    PowerfulDiagonal.tupleIdeal (raw.originalPairIdealFactors cap hcap v) =
      raw.columnIdeal v.1 * raw.columnIdeal v.2 := by
  unfold PowerfulDiagonal.tupleIdeal originalPairIdealFactors
  rw [OriginalParentTuple.prod_pairAppend]
  exact congrArg₂ (fun I J : Ideal (𝓞 K) => I * J)
    (raw.paddedOriginalIdealFactors_product cap hcap v.1)
    (raw.paddedOriginalIdealFactors_product cap hcap v.2)

/-- The same actual factors acquire their exterior proofs internally.
The unit fallback only makes the dictionary total off the actual
exterior source; it has no effect on any term or fibre being counted. -/
def paddedOriginalExteriorFactors (cap : ℕ) (hcap : d.geometry.slotCount ≤ cap)
    (v : raw.Column) (i : Fin (cap + 2)) : A.Exterior :=
  if hv : v ∈ raw.exteriorColumns then
    ⟨raw.paddedOriginalIdealFactors cap hcap v i,
      raw.paddedOriginalIdealFactors_ne_zero cap hcap v i,
      Ideal.isCoprime_iff_sup_eq.mp (raw.paddedOriginalIdealFactors_coprime cap hcap v hv i)⟩
  else unitExterior A

theorem paddedOriginalExteriorFactors_val (cap : ℕ)
    (hcap : d.geometry.slotCount ≤ cap) (v : raw.Column) (hv : v ∈ raw.exteriorColumns) :
    (fun i => (raw.paddedOriginalExteriorFactors cap hcap v i).val) =
      raw.paddedOriginalIdealFactors cap hcap v := by
  funext i
  simp only [paddedOriginalExteriorFactors, dif_pos hv]

def originalPairExteriorFactors (cap : ℕ) (hcap : d.geometry.slotCount ≤ cap)
    (v : raw.Column × raw.Column) : Fin (2 * (cap + 2)) → A.Exterior :=
  OriginalParentTuple.pairAppend
    (raw.paddedOriginalExteriorFactors cap hcap v.1)
    (raw.paddedOriginalExteriorFactors cap hcap v.2)

theorem originalPairExteriorFactors_val (cap : ℕ)
    (hcap : d.geometry.slotCount ≤ cap) (v : raw.Column × raw.Column)
    (hv₁ : v.1 ∈ raw.exteriorColumns) (hv₂ : v.2 ∈ raw.exteriorColumns) :
    (fun i => (raw.originalPairExteriorFactors cap hcap v i).val) =
      raw.originalPairIdealFactors cap hcap v := by
  unfold originalPairExteriorFactors originalPairIdealFactors
  rw [OriginalParentTuple.pairAppend_map,
    raw.paddedOriginalExteriorFactors_val cap hcap v.1 hv₁,
    raw.paddedOriginalExteriorFactors_val cap hcap v.2 hv₂]

/-- Direct inputs for `FirstTailWindows`: genuine subsets of the
original exterior carrier retain the original pair injection and full
ideal-product identity. No pair-injectivity premise is introduced. -/
theorem original_first_tail_pair_data
    (cap : ℕ) (hcap : d.geometry.slotCount ≤ cap)
    (left right : Finset raw.Column)
    (hleft : left ⊆ raw.exteriorColumns) (hright : right ⊆ raw.exteriorColumns) :
    Set.InjOn (raw.originalPairIdealFactors cap hcap)
        (left ×ˢ right : Set (raw.Column × raw.Column)) ∧
      ∀ v ∈ left ×ˢ right,
        PowerfulDiagonal.tupleIdeal (raw.originalPairIdealFactors cap hcap v) =
          (raw.columnExterior v.1).val * (raw.columnExterior v.2).val := by
  constructor
  · intro v _ w _ he
    exact raw.originalPairIdealFactors_injective cap hcap he
  · intro v hv
    have hm := Finset.mem_product.mp hv
    rw [raw.originalPairIdealFactors_product,
      raw.columnExterior_val_of_mem v.1 (hleft hm.1),
      raw.columnExterior_val_of_mem v.2 (hright hm.2)]

/-- Direct inputs for the common-support and amplifier tuple
constructors. Their actual divisor and valuation multiplicities now
follow from this original parent dictionary. -/
theorem original_exterior_pair_data
    (cap : ℕ) (hcap : d.geometry.slotCount ≤ cap)
    (left right : Finset raw.Column)
    (hleft : left ⊆ raw.exteriorColumns) (hright : right ⊆ raw.exteriorColumns) :
    Set.InjOn (fun v i => (raw.originalPairExteriorFactors cap hcap v i).val)
        (left ×ˢ right : Set (raw.Column × raw.Column)) ∧
      ∀ v ∈ left ×ˢ right,
        PowerfulDiagonal.tupleIdeal (fun i => (raw.originalPairExteriorFactors cap hcap v i).val) =
          (raw.columnExterior v.1).val * (raw.columnExterior v.2).val := by
  have hdata := raw.original_first_tail_pair_data cap hcap left right hleft hright
  have he (v : raw.Column × raw.Column) (hv : v ∈ left ×ˢ right) :=
    raw.originalPairExteriorFactors_val cap hcap v
      (hleft (Finset.mem_product.mp hv).1) (hright (Finset.mem_product.mp hv).2)
  constructor
  · intro v hv w hw hvw
    have hv' : v ∈ (left ×ˢ right : Finset (raw.Column × raw.Column)) := by
      simpa only [Finset.mem_product, Set.mem_prod, Finset.mem_coe] using hv
    have hw' : w ∈ (left ×ˢ right : Finset (raw.Column × raw.Column)) := by
      simpa only [Finset.mem_product, Set.mem_prod, Finset.mem_coe] using hw
    apply hdata.1 hv hw
    exact (he v hv').symm.trans (hvw.trans (he w hw'))
  · intro v hv
    rw [he v hv]
    exact hdata.2 v hv

end ParentRawAtoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalParentTuple.prod_padUnit
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.originalIdealFactors_injective
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.original_first_tail_pair_data
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.original_exterior_pair_data
