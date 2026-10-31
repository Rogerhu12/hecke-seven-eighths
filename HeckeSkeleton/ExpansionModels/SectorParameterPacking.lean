import HeckeSkeleton.ExpansionModels.RowLocalWitnessRecipe
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Sector-dependent witnesses in one fixed finite parameter dimension

`SourceMomentModels.realShifts` and `.imagShifts` are indexed by ideals,
not by (ideal, sixth-unit sector).  The detector may choose different
parameters for two sectors of the same ideal.  This file gives an exact
solution: pack every sector's coordinates into one fixed `Fin D` vector.
The Pi norm is preserved, so the bounds 8 and 1+||xi|| do not deteriorate.
No extra scale-dependent label or discretization is introduced.
-/

set_option autoImplicit false
noncomputable section

namespace ExpansionRecipe

open scoped Classical

variable {Row Ideal Sector : Type*} [Fintype Sector] {n : ℕ}

def sectorDimension (Sector : Type*) [Fintype Sector] (n : ℕ) : ℕ :=
  Fintype.card (Sector × Fin n)

theorem sectorDimension_eq (Sector : Type*) [Fintype Sector] (n : ℕ) :
    sectorDimension Sector n = Fintype.card Sector * n := by
  simp [sectorDimension]

def packSectors (x : Sector → Fin n → ℝ) : Fin (sectorDimension Sector n) → ℝ :=
  fun k => let ij := (Fintype.equivFin (Sector × Fin n)).symm k
    x ij.1 ij.2

def unpackSector (x : Fin (sectorDimension Sector n) → ℝ)
    (s : Sector) : Fin n → ℝ :=
  fun j => x (Fintype.equivFin (Sector × Fin n) (s, j))

@[simp] theorem unpack_packSectors (x : Sector → Fin n → ℝ) (s : Sector) :
    unpackSector (packSectors x) s = x s := by
  funext j
  simp [packSectors, unpackSector]

@[simp] theorem pack_unpackSectors (x : Fin (sectorDimension Sector n) → ℝ) :
    packSectors (unpackSector x) = x := by
  funext k
  change x ((Fintype.equivFin (Sector × Fin n))
    ((Fintype.equivFin (Sector × Fin n)).symm k)) = x k
  exact congrArg x ((Fintype.equivFin (Sector × Fin n)).apply_symm_apply k)

theorem norm_packSectors_le_iff (x : Sector → Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B) :
    ‖packSectors x‖ ≤ B ↔ ∀ s, ‖x s‖ ≤ B := by
  rw [pi_norm_le_iff_of_nonneg hB]
  constructor
  · intro h s
    apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro j
    simpa [packSectors] using h (Fintype.equivFin (Sector × Fin n) (s, j))
  · intro h k
    exact (pi_norm_le_iff_of_nonneg hB).mp
      (h ((Fintype.equivFin (Sector × Fin n)).symm k).1)
      ((Fintype.equivFin (Sector × Fin n)).symm k).2

theorem norm_packSectors (x : Sector → Fin n → ℝ) : ‖packSectors x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (norm_packSectors_le_iff x (norm_nonneg x)).mpr
    intro s
    exact norm_le_pi_norm x s
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (packSectors x))).mpr
    exact (norm_packSectors_le_iff x (norm_nonneg (packSectors x))).mp le_rfl

/-- Extend chosen physical-row parameters to all ideal/sector pairs, using
the actual injection of a physical row into its ideal and sector. -/
def extendRowParameters (e : Row ↪ Ideal × Sector)
    (p : Row → Fin n → ℝ) (default : Fin n → ℝ) (x : Ideal × Sector) : Fin n → ℝ :=
  if h : ∃ u, e u = x then p (Classical.choose h) else default

theorem extendRowParameters_at_row (e : Row ↪ Ideal × Sector)
    (p : Row → Fin n → ℝ) (default : Fin n → ℝ) (u : Row) :
    extendRowParameters e p default (e u) = p u := by
  have h : ∃ v, e v = e u := ⟨u, rfl⟩
  rw [extendRowParameters, dite_eq_left h]
  exact congrArg p (e.injective (Classical.choose_spec h))

theorem extendRowParameters_bound (e : Row ↪ Ideal × Sector)
    (p : Row → Fin n → ℝ) (default : Fin n → ℝ) {B : ℝ}
    (hp : ∀ u, ‖p u‖ ≤ B) (hd : ‖default‖ ≤ B) (x : Ideal × Sector) :
    ‖extendRowParameters e p default x‖ ≤ B := by
  unfold extendRowParameters
  split
  · exact hp _
  · exact hd

/-- One ideal-indexed map with dimension |Sector|*n, matching the shape of
the existing SourceMomentModels parameter fields. -/
def packedRowParameters (e : Row ↪ Ideal × Sector)
    (p : Row → Fin n → ℝ) (default : Fin n → ℝ) (I : Ideal) :
    Fin (sectorDimension Sector n) → ℝ :=
  packSectors fun s => extendRowParameters e p default (I, s)

theorem packedRowParameters_exact (e : Row ↪ Ideal × Sector)
    (p : Row → Fin n → ℝ) (default : Fin n → ℝ) (u : Row) :
    unpackSector (packedRowParameters e p default (e u).1) (e u).2 = p u := by
  rw [packedRowParameters, unpack_packSectors]
  exact extendRowParameters_at_row e p default u

theorem packedRowParameters_bound (e : Row ↪ Ideal × Sector)
    (p : Row → Fin n → ℝ) (default : Fin n → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hp : ∀ u, ‖p u‖ ≤ B) (hd : ‖default‖ ≤ B) (I : Ideal) :
    ‖packedRowParameters e p default I‖ ≤ B := by
  apply (norm_packSectors_le_iff _ hB).mpr
  intro s
  exact extendRowParameters_bound e p default hp hd (I, s)

end ExpansionRecipe

#print axioms ExpansionRecipe.norm_packSectors
#print axioms ExpansionRecipe.packedRowParameters_exact
#print axioms ExpansionRecipe.packedRowParameters_bound
