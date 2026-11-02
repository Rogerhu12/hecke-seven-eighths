import HeckeSkeleton.ExpansionModels.SourceData
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.SourceAdapter
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CoreGeometry

/-!
# Primitive root geometry of the one explicit source recipe

The recipe is fixed before every later height degree, loss budget and scale.
Its actual selected model supplies the slot-count cap, the individual slot
lengths and the original mesh. None of these facts is inferred just from an
equality of total lengths. The canonical source geometry supplies the actual
plain-length and parameter bounds, and the canonical profile control is
evaluated at those same parameters.

These are geometric and profile statements, not moment estimates. The named
unfinished actual recipe is never selected in this module.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open scoped BigOperators Classical

variable {K : Type} [Field K] [NumberField K] {c : TargetContext K}

/-- The complete actual root, with its original sector and selected slots. -/
def recipeRoot
    (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
      c.geometry (expansionShellAllowance K c))
    {Z T : ℝ} (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
    (s : SixthUnitClasses K (places K c)) :
    Node K c.family.omega (targetCharacter K c) :=
  Node.ordinary (pairedModelFor (recipeMomentModels K c R) i s) (pairedParametersFor i)

variable (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
  c.geometry (expansionShellAllowance K c))
variable {Z T : ℝ} (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
variable (s : SixthUnitClasses K (places K c))

@[simp] theorem recipeRoot_slotCount :
    (recipeRoot R i s).data.geometry.slotCount = i.selected.card := rfl

/-- The original physical number of slots bounds every selected root. -/
theorem recipeRoot_slotCount_le :
    (recipeRoot R i s).data.geometry.slotCount ≤ c.geometry.slots := by
  rw [recipeRoot_slotCount]
  simpa only [Fintype.card_fin] using Finset.card_le_univ i.selected

/-- Freeze and selection retain the actual shell-rescaled slot length. -/
theorem recipeRoot_slot_length (j : Fin (recipeRoot R i s).data.geometry.slotCount) :
    ((recipeRoot R i s).data.geometry.slots j).length =
      HeckeGeneral.ThetaSkeleton.TIP.slotLength c.geometry.slots (momentBlockFor i).shell := by
  change ((1 / 6 : ℝ) / c.geometry.slots) / (momentBlockFor i).shell =
    (1 / 6 : ℝ) / (c.geometry.slots * (momentBlockFor i).shell)
  rw [div_div]

theorem recipeRoot_totalLength :
    (recipeRoot R i s).data.geometry.totalLength = selectedLengthFor i := by
  calc
    _ = ∑ _j : Fin i.selected.card,
        HeckeGeneral.ThetaSkeleton.TIP.slotLength c.geometry.slots (momentBlockFor i).shell := by
      unfold SlotGeometry.totalLength
      apply Finset.sum_congr rfl
      intro j _
      exact recipeRoot_slot_length R i s j
    _ = ∑ _j ∈ i.selected,
        HeckeGeneral.ThetaSkeleton.TIP.slotLength c.geometry.slots (momentBlockFor i).shell :=
      selectedSlots_sum i.selected (fun _ =>
        HeckeGeneral.ThetaSkeleton.TIP.slotLength c.geometry.slots (momentBlockFor i).shell)
    _ = _ := rfl

/-- The engine's actual-length identity follows from the recipe itself. -/
theorem recipeRoot_length :
    (recipeRoot R i s).parameters.z = (recipeRoot R i s).data.geometry.totalLength :=
  (recipeRoot_totalLength R i s).symm

/-- The capacity's selected-slot mesh is the actual root geometry mesh. -/
theorem recipeRoot_fitsMesh (hcap : pairedCapacityFor i) :
    (recipeRoot R i s).data.geometry.fitsMesh (momentMesh K c.family).val := by
  intro j
  rw [recipeRoot_slot_length]
  exact hcap.1 _ (selectedSlotIndex_mem i.selected j)

/-- Width is the original dyadic row exponent, without changing the
physical plain or prime scales. -/
theorem recipeRoot_width :
    (recipeRoot R i s).width = rowWidthFor i := by
  change rowWidthFor i + 0 = rowWidthFor i
  exact add_zero _

theorem recipeRoot_width_range :
    1 < (recipeRoot R i s).width ∧ (recipeRoot R i s).width ≤ 2 := by
  rw [recipeRoot_width]
  exact ⟨(recipeMoment_rowWidth_spec i).1, (recipeMoment_rowWidth_spec i).2.1⟩

/-- The full family includes the endpoint and has a strict lower margin. -/
theorem recipeRoot_kappa :
    3 / 4 < (recipeRoot R i s).parameters.κ ∧ (recipeRoot R i s).parameters.κ ≤ 1 := by
  change 3 / 4 < 2 * c.family.B - 1 ∧ 2 * c.family.B - 1 ≤ 1
  constructor <;> linarith [c.family.B_lower, c.family.B_upper]

theorem recipeRoot_capacity (hcap : pairedCapacityFor i) :
    (recipeRoot R i s).parameters.n₁ + (recipeRoot R i s).parameters.n₂ +
      6 * (recipeRoot R i s).parameters.κ * (recipeRoot R i s).parameters.z ≤
        (recipeRoot R i s).width := by
  rw [recipeRoot_width]
  change (momentWitnessFor i).plainLength + (momentWitnessFor i).plainLength +
    6 * (2 * c.family.B - 1) * selectedLengthFor i ≤ rowWidthFor i
  have hc := hcap.2
  have hw := (recipeMoment_rowWidth_spec i).1
  linarith

theorem recipeRoot_positive_core (hcap : pairedCapacityFor i) :
    (recipeRoot R i s).totalLength ≤ (recipeRoot R i s).width :=
  (recipeRoot R i s).totalLength_le_width_of_capacity
    (recipeRoot_length R i s) (recipeRoot_kappa R i s).1.le
    (recipeRoot_capacity R i s hcap)

/-- The same recipe geometry supplies both actual plain-length bounds. -/
theorem recipeRoot_plain_lengths {L : ℝ} (hgeom : R.MomentGeometry L) :
    0 ≤ (recipeRoot R i s).parameters.n₁ ∧ (recipeRoot R i s).parameters.n₁ ≤ L ∧
      0 ≤ (recipeRoot R i s).parameters.n₂ ∧ (recipeRoot R i s).parameters.n₂ ≤ L := by
  have h := (recipeMomentModels_geometry K c R hgeom).1 Z T i
  exact ⟨h.2.1, h.2.2, h.2.1, h.2.2⟩

/-- Original profile constants apply at the selected parameters of every
actual root. The constants and common annulus precede all moving indices. -/
theorem recipeRoot_uniform_profiles {L : ℝ} (hgeom : R.MomentGeometry L)
    (hprofiles : WholeMomentProfileControlFor (recipeMomentModels K c R)) :
    ∀ J : ℕ, ∀ A : ℝ, 0 ≤ A →
      ∃ C H a b : ℝ, 0 < C ∧ 0 ≤ H ∧ 0 < a ∧ a < b ∧
        ∀ Z T (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
          (s : SixthUnitClasses K (places K c)),
          UniformAmplify.ModelProfileControl (recipeRoot R i s).data J A C H a b T := by
  have hp := (recipeMomentModels_geometry K c R hgeom).2
  intro J A hA
  obtain ⟨C, H, a, b, hC, hH, ha, hab, hb⟩ := hprofiles.evaluated hp J A hA
  refine ⟨C, H, a, b, hC, hH, ha, hab, ?_⟩
  intro Z T i s
  have hscale := recipeMoment_scale_of_index i
  have hZ : 1 ≤ Z := (by norm_num : (1 : ℝ) ≤ 2 ^ (16 : ℕ)).trans hscale.1
  exact hb Z T i hZ hscale.2 s (pairedModelFor (recipeMomentModels K c R) i s) (by simp)

end HeckeSkeleton.Moments.EngineInduction.Source
