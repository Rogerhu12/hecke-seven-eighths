import HeckeSkeleton.ExpansionModels.RowLocalWitnessRecipe
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Fixed-sector parameter assembly without increasing the dimension

Refining a physical amplitude label by its unit sector makes the ideal
projection injective.  Consequently every rowwise detector parameter map can
be extended to the ideal-indexed map required by SourceMomentModels, in the
same dimension n.  This respects the choice order "dimension, mesh, target".
-/

set_option autoImplicit false
noncomputable section

namespace ExpansionRecipe

open scoped Classical

variable {Row Ideal Sector Parameter : Type*}

def sectorFiber (e : Row ↪ Ideal × Sector) (s : Sector) : Type _ :=
  {u : Row // (e u).2 = s}

def sectorIdealEmbedding (e : Row ↪ Ideal × Sector) (s : Sector) :
    sectorFiber e s ↪ Ideal where
  toFun u := (e u.val).1
  inj' := by
    intro u v h
    apply Subtype.ext
    apply e.injective
    apply Prod.ext h
    exact u.property.trans v.property.symm

def extendAlongEmbedding {A B : Type*} (e : A ↪ B)
    (p : A → Parameter) (default : Parameter) (x : B) : Parameter :=
  if h : ∃ u, e u = x then p (Classical.choose h) else default

theorem extendAlongEmbedding_at {A B : Type*} (e : A ↪ B)
    (p : A → Parameter) (default : Parameter) (u : A) :
    extendAlongEmbedding e p default (e u) = p u := by
  have h : ∃ v, e v = e u := ⟨u, rfl⟩
  rw [extendAlongEmbedding, dite_eq_left h]
  exact congrArg p (e.injective (Classical.choose_spec h))

theorem extendAlongEmbedding_preserves_predicate {A B : Type*} (e : A ↪ B)
    (p : A → Parameter) (default : Parameter) (Q : Parameter → Prop)
    (hp : ∀ u, Q (p u)) (hd : Q default) (x : B) :
    Q (extendAlongEmbedding e p default x) := by
  unfold extendAlongEmbedding
  split
  · exact hp _
  · exact hd

/-- The constructor required for either σ or τ of a fixed-sector label. -/
def fixedSectorParameterMap (e : Row ↪ Ideal × Sector) (s : Sector)
    (p : sectorFiber e s → Parameter) (default : Parameter) : Ideal → Parameter :=
  extendAlongEmbedding (sectorIdealEmbedding e s) p default

theorem fixedSectorParameterMap_exact (e : Row ↪ Ideal × Sector) (s : Sector)
    (p : sectorFiber e s → Parameter) (default : Parameter) (u : sectorFiber e s) :
    fixedSectorParameterMap e s p default (e u.val).1 = p u :=
  extendAlongEmbedding_at (sectorIdealEmbedding e s) p default u

/-- Applying this once with Q=||σ||≤8 and once with Q=||τ||≤1+||ξ||
preserves the source's bounds exactly; no coordinate is added. -/
theorem fixedSectorParameterMap_bound {n : ℕ}
    (e : Row ↪ Ideal × Sector) (s : Sector)
    (p : sectorFiber e s → Fin n → ℝ) (default : Fin n → ℝ) (B : ℝ)
    (hp : ∀ u, ‖p u‖ ≤ B) (hd : ‖default‖ ≤ B) (I : Ideal) :
    ‖fixedSectorParameterMap e s p default I‖ ≤ B :=
  extendAlongEmbedding_preserves_predicate (sectorIdealEmbedding e s) p default
    (fun v => ‖v‖ ≤ B) hp hd I

/-- Local choices on a finite physical label assemble to ONE ideal-indexed
map in the original parameter space.  Fixed-sector refinement is the only
extra finite label, and its cardinality is independent of the scale. -/
theorem assemble_fixed_sector_parameters (e : Row ↪ Ideal × Sector) (s : Sector)
    (rows : Finset Row) (hsector : ∀ u ∈ rows, (e u).2 = s)
    (default : Parameter) (admissible : Parameter → Prop)
    (hdefault : admissible default) (P : Row → Parameter → Prop)
    (hlocal : ∀ u ∈ rows, ∃ p, admissible p ∧ P u p) :
    ∃ p : Ideal → Parameter,
      (∀ I, admissible (p I)) ∧ (∀ u ∈ rows, P u (p (e u).1)) := by
  classical
  obtain ⟨q, hq, hqout⟩ := assemble_row_parameters rows default
    (fun u p => admissible p ∧ P u p) hlocal
  have hqa : ∀ u, admissible (q u) := by
    intro u
    by_cases hu : u ∈ rows
    · exact (hq u hu).1
    · rw [hqout u hu]
      exact hdefault
  let p : Ideal → Parameter := fixedSectorParameterMap e s (fun u => q u.val) default
  refine ⟨p, ?_, ?_⟩
  · intro I
    exact extendAlongEmbedding_preserves_predicate (sectorIdealEmbedding e s)
      (fun u => q u.val) default admissible (fun u => hqa u.val) hdefault I
  · intro u hu
    have heq := fixedSectorParameterMap_exact e s (fun v => q v.val) default
      (⟨u, hsector u hu⟩ : sectorFiber e s)
    change P u (fixedSectorParameterMap e s (fun v => q v.val) default (e u).1)
    rw [heq]
    exact (hq u hu).2

/-- Specialization to the simultaneous inverse/plain spike selected by the
detector.  Both factors use the SAME extended parameter map. -/
theorem assemble_fixed_sector_witnesses {Column Slot : Type*}
    (e : Row ↪ Ideal × Sector) (s : Sector)
    (rows : Finset Row) (hsector : ∀ u ∈ rows, (e u).2 = s)
    (r : SharedRecipe Row Column Parameter Slot)
    (default : Parameter) (admissible : Parameter → Prop)
    (hdefault : admissible default) (inverseTarget plainTarget : Row → ℝ)
    (hlocal : ∀ u ∈ rows, ∃ p, admissible p ∧
      inverseTarget u ≤ ‖(r.inverse u p).value‖ ^ 2 ∧
      plainTarget u ≤ ‖(r.plain u p).value‖ ^ 2) :
    ∃ p : Ideal → Parameter,
      (∀ I, admissible (p I)) ∧
      (∀ u ∈ rows, inverseTarget u ≤
        ‖(r.witness (fun v => p (e v).1)).inverse u‖ ^ 2) ∧
      (∀ u ∈ rows, plainTarget u ≤
        ‖(r.witness (fun v => p (e v).1)).plain u‖ ^ 2) := by
  obtain ⟨p, hp, hspikes⟩ := assemble_fixed_sector_parameters e s rows hsector
    default admissible hdefault
    (fun u p => inverseTarget u ≤ ‖(r.inverse u p).value‖ ^ 2 ∧
      plainTarget u ≤ ‖(r.plain u p).value‖ ^ 2) hlocal
  exact ⟨p, hp, fun u hu => (hspikes u hu).1, fun u hu => (hspikes u hu).2⟩

end ExpansionRecipe

#print axioms ExpansionRecipe.sectorIdealEmbedding
#print axioms ExpansionRecipe.fixedSectorParameterMap_exact
#print axioms ExpansionRecipe.fixedSectorParameterMap_bound
#print axioms ExpansionRecipe.assemble_fixed_sector_parameters
#print axioms ExpansionRecipe.assemble_fixed_sector_witnesses
