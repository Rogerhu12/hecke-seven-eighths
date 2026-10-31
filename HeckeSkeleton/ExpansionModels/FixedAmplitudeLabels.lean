import HeckeSkeleton.ExpansionModels.SourceGeometry
import ExpansionInterfaces.AmplitudePartition
import Mathlib.Data.Fin.Embedding

/-!
# Fixed finite label spaces for all physical bins

The actual amplitude alphabet varies with the bin cap.  Its fixed upper
alphabet uses cap `1/2`, since every physical bin has `a ≤ 1`.
Padding copies existing legal amplitude data into unused labels, and the
retained-label set contains exactly the original labels.  Original block
values, physical points, rows, polynomial values and witness data remain
unchanged.  Transported pieces vanish off the retained-label set.
-/

set_option autoImplicit false
noncomputable section

namespace ExpansionInterfaces

def fixedAmplitudeLabelCount (J : ℕ) (width : ℝ) : ℕ :=
  (Nat.floor ((1 / 2 : ℝ) / width) + 2) ^ J

theorem amplitudeLabels_card_pos (J : ℕ) (width cap : ℝ) :
    0 < Fintype.card (AmplitudeLabels J width cap) :=
  Fintype.card_pos_iff.mpr ⟨fun _ => ⟨0, by omega⟩⟩

theorem amplitudeLabels_card_le_fixed (J : ℕ) {width cap : ℝ}
    (hw : 0 < width) (hc : cap ≤ 1 / 2) :
    Fintype.card (AmplitudeLabels J width cap) ≤ fixedAmplitudeLabelCount J width :=
  card_amplitudeLabels_le J hw hc

end ExpansionInterfaces

namespace HeckeGeneral.Analysis.ExpansionRecipe

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]
variable {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
variable {P : ProbeData K S} {R : RowCharacterInput K S P}
variable {ω ψ : HeckeCharacter K} {g : PrimeWindowGeometry}
variable {F : RecipeFamily K ψ g} {n N : ℕ}

def fixedLabelProjection (hn : 0 < n) (j : Fin N) : Fin n :=
  if h : j.val < n then ⟨j.val, h⟩ else ⟨0, hn⟩

theorem fixedLabelProjection_embed (hn : 0 < n) (h : n ≤ N) (j : Fin n) :
    fixedLabelProjection hn (Fin.castLEEmb h j) = j := by
  simp only [fixedLabelProjection, Fin.coe_castLEEmb, Fin.coe_castLE, dif_pos j.isLt]

def retainedFixedLabels (h : n ≤ N) : Finset (Fin N) :=
  Finset.univ.map (Fin.castLEEmb h)

theorem mem_retainedFixedLabels (h : n ≤ N) (j : Fin N) :
    j ∈ retainedFixedLabels h ↔ j.val < n := by
  constructor
  · intro hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hj
    exact i.isLt
  · intro hj
    exact Finset.mem_map.mpr ⟨⟨j.val, hj⟩, Finset.mem_univ _, by apply Fin.ext; rfl⟩

theorem card_retainedFixedLabels (h : n ≤ N) : (retainedFixedLabels h).card = n := by
  simp only [retainedFixedLabels, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- Extra labels reuse legal data; the physical sum selects exactly the
embedded original labels through `retainedFixedLabels`. -/
def RecipeBlockData.pad (b : RecipeBlockData K S ψ g F n) (hn : 0 < n)
    (_h : n ≤ N) : RecipeBlockData K S ψ g F N where
  bin := b.bin
  value := b.value
  amplitude j := b.amplitude (fixedLabelProjection hn j)

theorem RecipeBlockData.pad_amplitude_embed (b : RecipeBlockData K S ψ g F n)
    (hn : 0 < n) (h : n ≤ N) (j : Fin n) :
    (b.pad hn h).amplitude (Fin.castLEEmb h j) = b.amplitude j := by
  simp only [RecipeBlockData.pad, fixedLabelProjection_embed]

theorem RecipeBlockData.pad_source (b : RecipeBlockData K S ψ g F n)
    (hn : 0 < n) (hN : n ≤ N) (d Z T B lam k : ℝ)
    (h : BlockSource g (b.toBlock (P := P) (R := R) (ω := ω) d Z T) B lam k Z) :
    BlockSource g ((b.pad hn hN).toBlock (P := P) (R := R) (ω := ω) d Z T)
      B lam k Z := by
  obtain ⟨hd, hd', ha, ha', hlabels⟩ := h
  exact ⟨hd, hd', ha, ha', fun j => hlabels (fixedLabelProjection hn j)⟩

theorem RecipeBlockData.pad_geometry (b : RecipeBlockData K S ψ g F n)
    (hn : 0 < n) (hN : n ≤ N) (T L : ℝ)
    (h : ∀ j, (b.amplitude j).MomentGeometry T L) :
    ∀ j, ((b.pad hn hN).amplitude j).MomentGeometry T L :=
  fun j => h (fixedLabelProjection hn j)

/-- The original physical piece is extended by zero outside its retained
finite label set. -/
def fixedLabelPiece {Row : Type*} (f : Fin n → Row → ℂ) (j : Fin N) (u : Row) : ℂ :=
  if h : j.val < n then f ⟨j.val, h⟩ u else 0

theorem fixedLabelPiece_embed {Row : Type*} (f : Fin n → Row → ℂ)
    (h : n ≤ N) (j : Fin n) (u : Row) :
    fixedLabelPiece f (Fin.castLEEmb h j) u = f j u := by
  simp only [fixedLabelPiece, Fin.coe_castLEEmb, Fin.coe_castLE, dif_pos j.isLt]

theorem fixedLabelPiece_zero_of_not_retained {Row : Type*} (f : Fin n → Row → ℂ)
    (h : n ≤ N) (j : Fin N) (hj : j ∉ retainedFixedLabels h) (u : Row) :
    fixedLabelPiece f j u = 0 := by
  have hn : ¬j.val < n := fun hn => hj ((mem_retainedFixedLabels h j).mpr hn)
  simp only [fixedLabelPiece, dif_neg hn]

theorem sum_fixedLabelPiece {Row : Type*} (f : Fin n → Row → ℂ)
    (h : n ≤ N) (u : Row) :
    (∑ j ∈ retainedFixedLabels h, fixedLabelPiece f j u) = ∑ j, f j u := by
  simp only [retainedFixedLabels, Finset.sum_map, fixedLabelPiece_embed]

end HeckeGeneral.Analysis.ExpansionRecipe

#print axioms ExpansionInterfaces.amplitudeLabels_card_le_fixed
#print axioms HeckeGeneral.Analysis.ExpansionRecipe.RecipeBlockData.pad_source
#print axioms HeckeGeneral.Analysis.ExpansionRecipe.sum_fixedLabelPiece
