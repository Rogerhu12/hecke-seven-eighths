import Expansion.PhysicalAmplitudeProvenance
import Expansion.PhysicalShellPartition

/-!
# The actual shell, buffered-bin and sector schedule

This schedule and its family are fixed before the scale and height. Each
scheduled value is the original shifted contour integral summed over the
selected, globally clipped rows in one sector. In particular a default
witness at a small scale never changes the physical block value.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open ExpansionInterfaces
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local instance physicalRecipe_sectorFintype : Fintype (SixthUnitClasses K S) :=
  Fintype.ofFinite _

abbrev PhysicalRecipeChoice (B e : ℝ) := RowBufferIndex B e × SixthUnitClasses K S

def physicalRecipeMultiplicity (B e : ℝ) : ℕ :=
  Fintype.card (PhysicalRecipeChoice K S B e)

theorem physicalRecipeMultiplicity_pos (B e : ℝ) :
    0 < physicalRecipeMultiplicity K S B e :=
  Fintype.card_pos_iff.mpr ⟨((0, 0), 1)⟩

def physicalRecipeHeightBound (B e : ℝ) : ℕ :=
  Nat.ceil ((B - 51 / 100) / e) + 1

theorem physicalRecipeChoice_height_le (B e : ℝ) (c : PhysicalRecipeChoice K S B e) :
    c.1.1.val + 1 ≤ physicalRecipeHeightBound B e := by
  have h := c.1.1.isLt
  dsimp only [RowBufferIndex, BufferedIndex, physicalRecipeHeightBound] at h ⊢
  omega

theorem rowBufferIndex_center_range {B e : ℝ} (hB : 51 / 100 ≤ B) (he : 0 < e)
    (b : RowBufferIndex B e) : 51 / 100 ≤ b.center ∧ b.center ≤ B := by
  have hk : b.2.val ≤ Nat.floor ((B - 51 / 100) / e) := Nat.le_of_lt_succ b.2.isLt
  have hcast : (b.2.val : ℝ) ≤ (Nat.floor ((B - 51 / 100) / e) : ℝ) := by
    exact_mod_cast hk
  have hfloor := Nat.floor_le (div_nonneg (sub_nonneg.mpr hB) he.le)
  have hmul := (le_div_iff₀ he).mp (hcast.trans hfloor)
  have hn : (0 : ℝ) ≤ b.2.val := Nat.cast_nonneg _
  dsimp only [BufferedIndex.center]
  constructor <;> nlinarith

def physicalRecipeSlotTime (g : PrimeWindowGeometry) :
    Fin g.slots → (Fin 3 → ℝ) → ℝ := fun _ _ => 0

/-- This is the literal power in the shared forward polynomial for the
main compensation slot on the fixed line `Re z = 17/50`. -/
def physicalRecipeSlotPower (g : PrimeWindowGeometry) :
    Fin g.slots → (Fin 3 → ℝ) → ℂ :=
  fun _ p => conj ((17 / 50 : ℂ) + (p 2 : ℂ) * Complex.I) - 1

def physicalRecipeSlotCoefficient (K : Type) [Field K] [NumberField K]
    (g : PrimeWindowGeometry) : Fin g.slots → HeckeCharacter K := fun _ => 1

def physicalRecipeFamily (ψ : HeckeCharacter K) (g : PrimeWindowGeometry) (B e : ℝ) :
    RecipeFamily K ψ g :=
  scaledCanonicalRecipeFamily K ψ g cutoffProfile (physicalRecipeSlotTime g)
    (physicalRecipeSlotPower g) (physicalRecipeSlotCoefficient K g)
    (3 * ((physicalRecipeHeightBound B e : ℝ) + 1))

def physicalRecipeShellIndex (B e ζ Z : ℝ)
    (b : Fin (shellCount Z (1 / 16) (13 / 16 + ζ) * physicalRecipeMultiplicity K S B e)) :
    Fin (shellCount Z (1 / 16) (13 / 16 + ζ)) :=
  ⟨b.val / physicalRecipeMultiplicity K S B e,
    (Nat.div_lt_iff_lt_mul (physicalRecipeMultiplicity_pos K S B e)).mpr b.isLt⟩

def physicalRecipeChoice (B e ζ Z : ℝ)
    (b : Fin (shellCount Z (1 / 16) (13 / 16 + ζ) * physicalRecipeMultiplicity K S B e)) :
    PhysicalRecipeChoice K S B e :=
  (Fintype.equivFin (PhysicalRecipeChoice K S B e)).symm
    ⟨b.val % physicalRecipeMultiplicity K S B e,
      Nat.mod_lt _ (physicalRecipeMultiplicity_pos K S B e)⟩

theorem physicalRecipe_trivial_twists :
    ∀ θ ∈ ({1} : Finset (HeckeCharacter K)), FiniteOrder θ := by
  intro θ hθ
  obtain rfl := Finset.mem_singleton.mp hθ
  exact IsOfFinOrder.one

variable (P : ProbeData K S) (E : RowEulerData K S P) (ω ψ : HeckeCharacter K)
variable {B e : ℝ} (hψ : ψ ∈ HeckePacket K ω)
variable (hB0 : 51 / 100 ≤ B) (hB : B ≤ 1) (he : 0 < e)
variable (hbound : ∀ χ r, r ∈ heckePacketZeros K ω χ →
  1 / 2 ≤ r → r ≤ 1 → r ≤ B)

def physicalRecipeRows (ζ Z T : ℝ) (j : Fin (shellCount Z (1 / 16) (13 / 16 + ζ)))
    (c : PhysicalRecipeChoice K S B e) : Finset (FrequencyRow K S) :=
  (clippedSelectedPhysicalRows K S ω ψ {1} P E hψ (physicalRecipe_trivial_twists K)
    hB0 hB he hbound (Z ^ shellExponent Z (1 / 16) j.val) (Z ^ (13 / 16 + ζ)) T c.1).
      filter fun u => u.sector = c.2

/-- The selector supplies the original zero predicates on exactly these
rows; the height index is the first buffer coordinate plus one. -/
theorem physicalRecipeRows_spec (ζ Z T : ℝ) (hZ : 1 < Z)
    (j : Fin (shellCount Z (1 / 16) (13 / 16 + ζ)))
    (c : PhysicalRecipeChoice K S B e) (u : FrequencyRow K S)
    (hu : u ∈ physicalRecipeRows K S P E ω ψ hψ hB0 hB he hbound ζ Z T j c) :
    Z ^ shellExponent Z (1 / 16) j.val < frequencyRowNorm K S u ∧
      frequencyRowNorm K S u ≤ 2 * Z ^ shellExponent Z (1 / 16) j.val ∧
      u.sector = c.2 ∧
      (51 / 100 < c.1.center → rowZeroAbove K S ψ {1} P E u
        (selectedHeight (c.1.1.val + 1) T) c.1.center) ∧
      rowZeroBelow K S ψ {1} P E u
        (upperHeight (c.1.1.val + 1) T) (c.1.center + 2 * e) := by
  obtain ⟨hu, hsector⟩ := Finset.mem_filter.mp hu
  have hselected := clippedSelectedPhysicalRows_subset K S ω ψ {1} P E hψ
    (physicalRecipe_trivial_twists K) hB0 hB he hbound _ _ T c.1 hu
  have hmem := (mem_selectedRows _ _ c.1 u).mp hselected
  have hshell := Finset.mem_filter.mp hmem.1
  have hnorm := (mem_frequencyRows_iff K S _ (by positivity) u).mp hshell.1
  have hgood := rowBufferIndex_good K S ω ψ {1} P E hψ
    (physicalRecipe_trivial_twists K) hB0 hB he hbound T u
  rw [hmem.2] at hgood
  refine ⟨hshell.2.1, hnorm, hsector, ?_, ?_⟩
  · exact hgood.2.2.1
  · simpa only [upperHeight, Nat.add_assoc, show (1 + 1 : ℕ) = 2 by norm_num]
      using hgood.2.2.2

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S) → Measure (p.val.adicCompletion K))
variable [∀ p : S, (μ p).IsAddHaarMeasure]
variable (g : PrimeWindowGeometry) (windowCharacters : Finset (HeckeCharacter K))

/-- The value of every scheduled block is its actual shifted row-contour
sum, at every scale including scales before detection is available. -/
def physicalRecipeBlockValue (ζ Z T : ℝ)
    (j : Fin (shellCount Z (1 / 16) (13 / 16 + ζ)))
    (c : PhysicalRecipeChoice K S B e) : ℂ :=
  ∑ u ∈ physicalRecipeRows K S P E ω ψ hψ hB0 hB he hbound ζ Z T j c,
    rowContourBox K S μ P ψ E g windowCharacters u Z T
      (c.1.center + 16 * e) (1 - c.1.center - 6 * e) (17 / 50)

end Expansion.Project

#print axioms Expansion.Project.physicalRecipeRows_spec
#print axioms Expansion.Project.physicalRecipeBlockValue
