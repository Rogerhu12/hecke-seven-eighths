import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentColumnPhaseBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SourceCartesianAtlas
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCoefficientBinding

/-!
# The original parent has its own actual Cartesian atlas

Filtering the original complete column by the exterior condition is
exactly the same as filtering its two plain occurrences and every prime
occurrence separately.  This follows from nonvanishing and the product
criterion for coprimality.  It is not a source-support assumption.

The resulting ideal-valued Cartesian carrier is reindexed to the same
original columns by the standard nonzero-ideal coercion.  The inverse,
the complete ideal product and both nonzero plain supports are proved
here.  No new prime, slot, coefficient or source label is selected.
The construction works for empty supports and for every number of slots.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {Γ : Subgroup A.U}
variable {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}

local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

namespace ParentRawAtoms

variable (raw : ParentRawAtoms (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t Y₁ Y₂)

/-- The original tuple is nonzero before any exterior filtering. -/
theorem columnIdeal_ne_zero (v : raw.Column) : raw.columnIdeal v ≠ 0 := by
  apply mul_ne_zero
  · exact mul_ne_zero (nonZeroDivisors.coe_ne_zero v.1.1)
      (nonZeroDivisors.coe_ne_zero v.1.2)
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => (v.2 i).ne_bot)

/-- Every occurrence is exterior exactly when the complete original
ideal is exterior.  In particular repeated primes are not removed. -/
theorem columnIdeal_coprime_iff (v : raw.Column) :
    IsCoprime (raw.columnIdeal v) A.cS ↔
      (IsCoprime v.1.1.val A.cS ∧ IsCoprime v.1.2.val A.cS) ∧
        ∀ i, IsCoprime (v.2 i).asIdeal A.cS := by
  simp only [columnIdeal, IsCoprime.mul_left_iff, IsCoprime.prod_left_iff,
    Finset.mem_univ, forall_const]

def exteriorPlain₁ : Finset (NonzeroIdeal K) :=
  raw.leftColumns.filter (fun I => IsCoprime I.val A.cS)

def exteriorPlain₂ : Finset (NonzeroIdeal K) :=
  raw.rightColumns.filter (fun I => IsCoprime I.val A.cS)

def exteriorSlots (i : Fin d.geometry.slotCount) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (raw.slotColumns i).filter (fun p => IsCoprime p.asIdeal A.cS)

/-- The whole-ideal exterior filter is proved to be the actual full
Cartesian product of the individually filtered original supports. -/
theorem exteriorColumns_eq_cartesian :
    raw.exteriorColumns =
      childCartesianColumns raw.exteriorPlain₁ raw.exteriorPlain₂ raw.exteriorSlots := by
  ext v
  simp only [exteriorColumns, exteriorPlain₁, exteriorPlain₂, exteriorSlots,
    columns, childCartesianColumns, Finset.mem_filter, Finset.mem_product,
    Fintype.mem_piFinset, raw.columnIdeal_ne_zero v, true_and,
    raw.columnIdeal_coprime_iff v, forall_and]
  tauto

/-- The atlas uses ordinary ideals only for its two plain coordinates.
Their source identities are retained by the injective subtype coercion. -/
def originalPlain₁ : Finset (Ideal (𝓞 K)) := raw.exteriorPlain₁.image Subtype.val

def originalPlain₂ : Finset (Ideal (𝓞 K)) := raw.exteriorPlain₂.image Subtype.val

theorem originalPlain₁_nonzero (I : Ideal (𝓞 K)) (hI : I ∈ raw.originalPlain₁) : I ≠ 0 := by
  obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hI
  exact nonZeroDivisors.coe_ne_zero J

theorem originalPlain₂_nonzero (I : Ideal (𝓞 K)) (hI : I ∈ raw.originalPlain₂) : I ≠ 0 := by
  obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hI
  exact nonZeroDivisors.coe_ne_zero J

private theorem sourceMomentIdeal_mem_image
    (S : Finset (NonzeroIdeal K)) (I : Ideal (𝓞 K))
    (hI : I ∈ S.image Subtype.val) : sourceMomentIdeal I ∈ S := by
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
  simpa only [sourceMomentIdeal_coe] using hJ

/-- The index restores just the original nonzero-ideal subtype.  Its
prime tuple is unchanged, including every occurrence index. -/
def originalIndex (x : AllocationColumn K d.geometry.slotCount) : raw.Column :=
  ((sourceMomentIdeal x.1.1, sourceMomentIdeal x.1.2), x.2)

/-- The inverse forgets only the two nonzero proofs. -/
def originalCoordinates (v : raw.Column) : AllocationColumn K d.geometry.slotCount :=
  ((v.1.1.val, v.1.2.val), v.2)

theorem originalIndex_coordinates (v : raw.Column) :
    raw.originalIndex (raw.originalCoordinates v) = v := by
  simp only [originalIndex, originalCoordinates, sourceMomentIdeal_coe]

theorem originalCoordinates_index
    (x : AllocationColumn K d.geometry.slotCount)
    (hx : x ∈ childCartesianColumns raw.originalPlain₁ raw.originalPlain₂ raw.exteriorSlots) :
    raw.originalCoordinates (raw.originalIndex x) = x := by
  have hp := Finset.mem_product.mp (Finset.mem_product.mp hx).1
  simp only [originalCoordinates, originalIndex,
    sourceMomentIdeal_val_of_ne_zero _ (raw.originalPlain₁_nonzero _ hp.1),
    sourceMomentIdeal_val_of_ne_zero _ (raw.originalPlain₂_nonzero _ hp.2)]

theorem originalIndex_mem
    (x : AllocationColumn K d.geometry.slotCount)
    (hx : x ∈ childCartesianColumns raw.originalPlain₁ raw.originalPlain₂ raw.exteriorSlots) :
    raw.originalIndex x ∈ raw.exteriorColumns := by
  rw [raw.exteriorColumns_eq_cartesian]
  have hm := Finset.mem_product.mp hx
  have hp := Finset.mem_product.mp hm.1
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hm.2⟩
  · exact sourceMomentIdeal_mem_image raw.exteriorPlain₁ x.1.1 hp.1
  · exact sourceMomentIdeal_mem_image raw.exteriorPlain₂ x.1.2 hp.2

theorem originalCoordinates_mem (v : raw.Column) (hv : v ∈ raw.exteriorColumns) :
    raw.originalCoordinates v ∈
      childCartesianColumns raw.originalPlain₁ raw.originalPlain₂ raw.exteriorSlots := by
  rw [raw.exteriorColumns_eq_cartesian] at hv
  have hm := Finset.mem_product.mp hv
  have hp := Finset.mem_product.mp hm.1
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hm.2⟩
  · exact Finset.mem_image.mpr ⟨v.1.1, hp.1, rfl⟩
  · exact Finset.mem_image.mpr ⟨v.1.2, hp.2, rfl⟩

/-- The complete generated ideal is exactly the original Cartesian
ideal product.  No ideal-product dictionary is assumed. -/
theorem originalIndex_ideal_product
    (x : AllocationColumn K d.geometry.slotCount)
    (hx : x ∈ childCartesianColumns raw.originalPlain₁ raw.originalPlain₂ raw.exteriorSlots) :
    (raw.columnExterior (raw.originalIndex x)).val = allocationColumnIdeal x := by
  rw [raw.columnExterior_val_of_mem (raw.originalIndex x) (raw.originalIndex_mem x hx)]
  change allocationColumnIdeal (raw.originalCoordinates (raw.originalIndex x)) = _
  rw [raw.originalCoordinates_index x hx]

/-- The actual finite bijection required by all subsequent common,
support and valuation partitions.  Both inverse identities and the
whole ideal product are conclusions of the original atom coordinates. -/
def originalReindex :
    CartesianSourceReindex raw.exteriorColumns raw.columnExterior d.geometry.slotCount where
  plain₁ := raw.originalPlain₁
  plain₂ := raw.originalPlain₂
  slots := raw.exteriorSlots
  index := raw.originalIndex
  maps := raw.originalIndex_mem
  injective x hx y hy h := by
    have hc := congrArg raw.originalCoordinates h
    rw [raw.originalCoordinates_index x hx, raw.originalCoordinates_index y hy] at hc
    exact hc
  surjective v hv :=
    ⟨raw.originalCoordinates v, raw.originalCoordinates_mem v hv, raw.originalIndex_coordinates v⟩
  ideal_product := raw.originalIndex_ideal_product

/-- A source atlas computed from the same filtered actual parent
columns.  No witness of a nonempty source is needed. -/
def originalAtlas : SourceCartesianAtlas raw.exteriorColumns raw.columnExterior where
  slotCount := d.geometry.slotCount
  reindex := raw.originalReindex
  plain₁_nonzero := raw.originalPlain₁_nonzero
  plain₂_nonzero := raw.originalPlain₂_nonzero

@[simp] theorem originalAtlas_slotCount : raw.originalAtlas.slotCount = d.geometry.slotCount := rfl

@[simp] theorem originalAtlas_index_slot
    (x : AllocationColumn K d.geometry.slotCount) (i : Fin d.geometry.slotCount) :
    (raw.originalAtlas.reindex.index x).2 i = x.2 i := rfl

/-- Reindexing preserves each original complete coefficient as a
single summand, for any additive target. -/
theorem sum_exteriorColumns_originalCartesian {M : Type*} [AddCommMonoid M]
    (f : raw.Column → M) :
    (∑ v ∈ raw.exteriorColumns, f v) =
      ∑ x ∈ childCartesianColumns raw.originalPlain₁ raw.originalPlain₂ raw.exteriorSlots,
        f (raw.originalIndex x) :=
  raw.originalReindex.sum_reindex f

section Polynomial

variable {σ : K →+* ℂ}

/-- The same literal parent polynomial, including its entire centered
difference, now uses the atlas computed from its own atom supports. -/
theorem polynomial_originalCartesian
    (left : ∀ I ∈ raw.leftColumns, ∀ q : Q,
      raw.leftPhase q I = actualIdealResidue (A := A) (σ := σ) I.val q.out.val)
    (right : ∀ I ∈ raw.rightColumns, ∀ q : Q,
      raw.rightPhase q I = actualIdealResidue (A := A) (σ := σ) I.val q.out.val)
    (prime : ∀ i, ∀ p ∈ raw.slotColumns i, ∀ q : Q,
      raw.primePhase q i p = actualIdealResidue (A := A) (σ := σ) p.asIdeal q.out.val)
    (centered : Bool) (u : NonzeroIdeal K) (hu : u ∈ pairedRows d a Z) :
    pairedStagePolynomial centered d u (Z ^ a.n₁) (Z ^ a.n₂) Y₁ Y₂ Z t =
      ∑ x ∈ childCartesianColumns raw.originalPlain₁ raw.originalPlain₂ raw.exteriorSlots,
        raw.coefficient centered (raw.rowMap u) (raw.originalIndex x) *
          raw.phase (raw.rowMap u) (raw.originalIndex x) :=
  (raw.polynomial centered u hu).trans
    ((raw.coefficient_phase_sum_filter_exterior left right prime centered (raw.rowMap u)).trans
      (raw.sum_exteriorColumns_originalCartesian
        (fun v => raw.coefficient centered (raw.rowMap u) v * raw.phase (raw.rowMap u) v)))

end Polynomial
end ParentRawAtoms

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.exteriorColumns_eq_cartesian
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.originalReindex
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.originalAtlas
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.polynomial_originalCartesian
