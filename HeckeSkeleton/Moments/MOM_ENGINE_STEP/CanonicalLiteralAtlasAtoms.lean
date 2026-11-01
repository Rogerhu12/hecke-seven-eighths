import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolAtlas
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralProfileData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSupport

/-!
# The original atom table on the existing covered source dictionary

An existing source atlas transports its proof of finite support without
changing its original occurrence dictionary.  Here the literal atom
table is transported through that already proved dictionary equality.
Its support fields are then the actual atlas fields by definition.

No column coefficient or polynomial identity is an input.  The same
two plain tests, every original prime test, the centered difference and
all normalization factors are retained.  The index and membership
lemmas permit the actual original coefficient calculation to be applied
directly to the stored covered leaf.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralAtlasAtoms

/-- Transport only the occurrence index. The two actual plain ideals
and every prime value are unchanged. -/
def castColumn {k l : ℕ} (h : k = l) (i : AllocationColumn K k) :
    AllocationColumn K l :=
  (i.1, fun j => i.2 (Fin.cast h.symm j))

@[simp] theorem castColumn_rfl {k : ℕ} (i : AllocationColumn K k) :
    castColumn rfl i = i := rfl

@[simp] theorem castColumn_symm {k l : ℕ} (h : k = l)
    (i : AllocationColumn K k) :
    castColumn h.symm (castColumn h i) = i := by
  cases h
  rfl

@[simp] theorem castColumn_ideal {k l : ℕ} (h : k = l)
    (i : AllocationColumn K k) :
    allocationColumnIdeal (castColumn h i) = allocationColumnIdeal i := by
  cases h
  rfl

abbrev Dictionary (ι : Type*) :=
  Σ n : ℕ, (Finset (Ideal (𝓞 K)) × Finset (Ideal (𝓞 K))) ×
    (Fin n → Finset (HeightOneSpectrum (𝓞 K))) ×
      (AllocationColumn K n → ι)

theorem dictionary_index {ι : Type*} {L M : Dictionary (K := K) ι}
    (h : L = M) (i : AllocationColumn K L.1) :
    L.2.2.2 i = M.2.2.2 (castColumn (congrArg Sigma.fst h) i) := by
  cases h
  rfl

theorem dictionary_membership {ι : Type*} {L M : Dictionary (K := K) ι}
    (h : L = M) (i : AllocationColumn K L.1) :
    i ∈ childCartesianColumns L.2.1.1 L.2.1.2 L.2.2.1 ↔
      castColumn (congrArg Sigma.fst h) i ∈
        childCartesianColumns M.2.1.1 M.2.1.2 M.2.2.1 := by
  cases h
  rfl

end CanonicalLiteralAtlasAtoms

namespace CanonicalLiteralRectangles.Atoms

open CanonicalLiteralAtlasAtoms

variable {k : ℕ} (d : Atoms (K := K) k)

private def onDictionary {ι : Type*} (D : Dictionary (K := K) ι)
    (h : k = D.1)
    (h₁ : ∀ I ∈ D.2.1.1, I ≠ 0) (h₂ : ∀ I ∈ D.2.1.2, I ≠ 0) :
    Atoms (K := K) D.1 :=
  { cast (congrArg (Atoms (K := K)) h) d with
    plain₁ := D.2.1.1
    plain₂ := D.2.1.2
    slots := D.2.2.1
    plain₁_nonzero := h₁
    plain₂_nonzero := h₂ }

private theorem onDictionary_eq_cast {ι : Type*}
    (D : Dictionary (K := K) ι) (index : AllocationColumn K k → ι)
    (e : D = ⟨k, (d.plain₁, d.plain₂), d.slots, index⟩)
    (h₁ : ∀ I ∈ D.2.1.1, I ≠ 0) (h₂ : ∀ I ∈ D.2.1.2, I ≠ 0) :
    d.onDictionary D (congrArg Sigma.fst e).symm h₁ h₂ =
      cast (congrArg (Atoms (K := K)) (congrArg Sigma.fst e).symm) d := by
  cases e
  rfl

variable {A : SArithmeticData K} {ι : Type*}
variable {columns : Finset ι} {ideal : ι → A.Exterior}
variable (T : SourceCartesianAtlas columns ideal)

/-- The supports are the already constructed atlas supports, while
all coefficient and profile data come from the original literal table. -/
def onAtlas (h : k = T.slotCount) : Atoms (K := K) T.slotCount :=
  d.onDictionary T.literalDictionary h T.plain₁_nonzero T.plain₂_nonzero

@[simp] theorem onAtlas_plain₁ (h : k = T.slotCount) :
    (d.onAtlas T h).plain₁ = T.reindex.plain₁ := rfl

@[simp] theorem onAtlas_plain₂ (h : k = T.slotCount) :
    (d.onAtlas T h).plain₂ = T.reindex.plain₂ := rfl

@[simp] theorem onAtlas_slots (h : k = T.slotCount) :
    (d.onAtlas T h).slots = T.reindex.slots := rfl

theorem onAtlas_term (h : k = T.slotCount) (r : Bool)
    (i : AllocationColumn K T.slotCount) :
    (d.onAtlas T h).term r i = d.term r (castColumn h.symm i) := by
  cases h
  rfl

theorem onAtlas_whole (h : k = T.slotCount)
    (i : AllocationColumn K T.slotCount) :
    (d.onAtlas T h).whole i = d.whole (castColumn h.symm i) := by
  cases h
  rfl

/-- The original occurrence equality, rather than a completed column
identity, proves that support retargeting leaves this atom table intact. -/
theorem onAtlas_eq_cast (index : AllocationColumn K k → ι)
    (e : T.literalDictionary = ⟨k, (d.plain₁, d.plain₂), d.slots, index⟩) :
    d.onAtlas T (congrArg Sigma.fst e).symm =
      cast (congrArg (Atoms (K := K)) (congrArg Sigma.fst e).symm) d :=
  d.onDictionary_eq_cast T.literalDictionary index e T.plain₁_nonzero T.plain₂_nonzero

theorem onAtlas_index (index : AllocationColumn K k → ι)
    (e : T.literalDictionary = ⟨k, (d.plain₁, d.plain₂), d.slots, index⟩)
    (i : AllocationColumn K T.slotCount) :
    T.reindex.index i = index (castColumn (congrArg Sigma.fst e) i) :=
  dictionary_index e i

theorem onAtlas_membership (index : AllocationColumn K k → ι)
    (e : T.literalDictionary = ⟨k, (d.plain₁, d.plain₂), d.slots, index⟩)
    (i : AllocationColumn K T.slotCount) :
    i ∈ T.reindex.cartesian ↔
      castColumn (congrArg Sigma.fst e) i ∈
        childCartesianColumns d.plain₁ d.plain₂ d.slots :=
  dictionary_membership e i

namespace ProfileData

variable {d} (W : d.ProfileData)

/-- The profiles do not depend on the finite support proofs. No new
test, scale, frequency direction or Fourier parameter is selected. -/
def onAtlas (h : k = T.slotCount) : (d.onAtlas T h).ProfileData := by
  cases h
  exact
    { left := W.left
      right := W.right
      slot := W.slot
      slot_length := W.slot_length
      left_positive := W.left_positive
      right_positive := W.right_positive
      slot_positive := W.slot_positive
      left_frozen := W.left_frozen
      right_frozen := W.right_frozen
      slot_frozen := W.slot_frozen
      left_eval := W.left_eval
      right_eval := W.right_eval
      slot_eval := W.slot_eval }

end ProfileData

namespace SupportData

variable {d} {excluded : Finset (Ideal (𝓞 K))} (W : d.SupportData excluded)

private def castTable {l : ℕ} (h : k = l) :
    (cast (congrArg (Atoms (K := K)) h) d).SupportData excluded := by
  cases h
  exact W

/-- The true individual support dictionary follows through the
original finite occurrence equality. -/
def onAtlas (index : AllocationColumn K k → ι)
    (e : T.literalDictionary = ⟨k, (d.plain₁, d.plain₂), d.slots, index⟩) :
    (d.onAtlas T (congrArg Sigma.fst e).symm).SupportData excluded := by
  rw [d.onAtlas_eq_cast T index e]
  exact W.castTable (congrArg Sigma.fst e).symm

end SupportData
end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAtlasAtoms.dictionary_index
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.onAtlas_whole
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.onAtlas_eq_cast
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.onAtlas
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.SupportData.onAtlas
