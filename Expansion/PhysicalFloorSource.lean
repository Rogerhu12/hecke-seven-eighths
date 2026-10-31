import Expansion.PhysicalAmplitudeSource

/-!
# The actual amplitude source in the floor bin

The floor bin is controlled by the total row count, so its `BlockSource`
has no zero-detection requirement.  Its amplitudes are nevertheless the
same actual prime-slot fibers as in a live bin, sampled at one common
physical point.  A singleton witness subdivision stores legal lengths and
parameters for the shared moment interface; no spike is asserted there.
The output uses the same fixed amplitude alphabet as every live bin.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.TIP ExpansionInterfaces
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)
variable (ω ψ : HeckeCharacter K) (g : PrimeWindowGeometry)

def floorRecipeAmplitude (F : RecipeFamily K ψ g)
    (rows : Finset (FrequencyRow K S)) (sector : SixthUnitClasses K S)
    (p : Fin 3 → ℝ) (amplitude : Fin g.slots → ℝ) :
    RecipeAmplitudeData K S ψ g F where
  candidates := rows
  sector := sector
  physical := p
  amplitude := amplitude
  witnessCount _ := 1
  witnessChoice _ _ := 0
  witness t _ :=
    { inverseLength := t
      plainLength := 0
      presentation := ⟨0, F.presentationCount_pos⟩
      realShifts := fun _ => 0
      imagShifts := fun _ => 0 }

theorem floorRecipeAmplitude_rows (F : RecipeFamily K ψ g)
    (rows : Finset (FrequencyRow K S)) (sector : SixthUnitClasses K S)
    (p : Fin 3 → ℝ) (amplitude : Fin g.slots → ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hnorm : ∀ u ∈ rows, frequencyRowNorm K S u ≤ 2 * U)
    (hsector : ∀ u ∈ rows, u.sector = sector) :
    (floorRecipeAmplitude K S ψ g F rows sector p amplitude).rows U = rows := by
  ext u
  simp only [RecipeAmplitudeData.rows, floorRecipeAmplitude, Finset.mem_filter]
  constructor
  · exact fun h => h.2.1
  · intro hu
    exact ⟨(mem_frequencyRows_iff K S (2 * U) (by positivity) u).mpr (hnorm u hu),
      hu, hsector u hu⟩

theorem floorRecipeAmplitude_geometry (F : RecipeFamily K ψ g)
    (rows : Finset (FrequencyRow K S)) (sector : SixthUnitClasses K S)
    (p : Fin 3 → ℝ) (amplitude : Fin g.slots → ℝ)
    (T : ℝ) (hT : 1 ≤ T) (hp : ‖p‖ ≤ T) :
    (floorRecipeAmplitude K S ψ g F rows sector p amplitude).MomentGeometry T 22 := by
  let A := floorRecipeAmplitude K S ψ g F rows sector p amplitude
  intro t ht ht' j
  refine ⟨show 0 ≤ t from zero_le_one.trans ht, le_rfl, by norm_num, ?_, ?_, ?_⟩
  · exact ((A.witness t j).heights_norm_eq p t T hT hp ⟨ht, ht'⟩).le
  · intro I
    change ‖(0 : RecipeVector)‖ ≤ 8
    norm_num
  · intro I
    change ‖(0 : RecipeVector)‖ ≤ 1 + ‖(A.witness t j).heights p t T‖
    simp only [norm_zero]
    positivity

/-- Every floor-bin block has the actual slot lower bounds and the common
fixed label count.  Its original supplied physical value is unchanged. -/
theorem exists_physical_floor_block_source
    (F : RecipeFamily K ψ g) (Z T d B lam k width : ℝ) (value : ℂ)
    (hZ : 1 < Z) (hT : 1 ≤ T) (hd : 1 / 16 ≤ d) (hd' : d ≤ 13 / 16 + lam)
    (hB : 51 / 100 ≤ B) (hw : 0 < width)
    (sector : SixthUnitClasses K S) (rows : Finset (FrequencyRow K S))
    (hnorm : ∀ u ∈ rows, frequencyRowNorm K S u ≤ 2 * Z ^ d)
    (hsector : ∀ u ∈ rows, u.sector = sector) :
    ∃ b : RecipeBlockData K S ψ g F (fixedAmplitudeLabelCount g.slots width),
      b.bin = 51 / 100 ∧ b.value = value ∧
      BlockSource g (b.toBlock (P := P) (R := R) (ω := ω) d Z T) B lam k Z ∧
      (∀ l, (b.amplitude l).MomentGeometry T 22) ∧
      (∀ l, (b.amplitude l).rows (Z ^ d) ⊆ rows) ∧
      (∀ l, ‖(b.amplitude l).physical‖ ≤ T) := by
  let Labels := AmplitudeLabels g.slots width (1 / 100)
  have hsamples (label : Labels) := exists_recipeAmplitude_sample K S P R ω ψ g F
    width (1 / 100) Z T (zero_le_one.trans hT) rows label
  choose p hp hmax using hsamples
  let sampled := fun label : Labels =>
    recipeAmplitudeRows K S P R ω ψ g F width (1 / 100) Z rows (p label) label
  have hsub (label : Labels) : sampled label ⊆ rows :=
    recipeAmplitudeRows_subset K S P R ω ψ g F width (1 / 100) Z rows (p label) label
  let A := fun label : Labels => floorRecipeAmplitude K S ψ g F
    (sampled label) sector (p label) (fun j => decodeAmplitude width (1 / 100) (label j))
  have hrows (label : Labels) : (A label).rows (Z ^ d) = sampled label :=
    floorRecipeAmplitude_rows K S ψ g F (sampled label) sector (p label)
      (fun j => decodeAmplitude width (1 / 100) (label j)) (Z ^ d)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      (fun u hu => hnorm u (hsub label hu)) (fun u hu => hsector u (hsub label hu))
  have hgeometry (label : Labels) : (A label).MomentGeometry T 22 :=
    floorRecipeAmplitude_geometry K S ψ g F (sampled label) sector (p label)
      (fun j => decodeAmplitude width (1 / 100) (label j)) T hT (hp label)
  have hamp (label : Labels) := recipeAmplitudeRows_amplitude_spec K S P R ω ψ g F
    width (1 / 100) Z rows (p label) hw (by norm_num) hZ label
  let decode := (Fintype.equivFin Labels).symm
  let b : RecipeBlockData K S ψ g F (Fintype.card Labels) :=
    { bin := 51 / 100
      value := value
      amplitude := fun l => A (decode l) }
  have hblock : BlockSource g
      (b.toBlock (P := P) (R := R) (ω := ω) d Z T) B lam k Z := by
    refine ⟨by dsimp [b, RecipeBlockData.toBlock]; linarith, hd', le_rfl, hB, ?_⟩
    intro l
    refine ⟨?_, ?_, ?_⟩
    · simpa only [RecipeBlockData.toBlock, b, A, floorRecipeAmplitude,
        RecipeAmplitudeData.toAmplitude,
        show (2 * (51 / 100 : ℝ) - 1) / 2 = 1 / 100 by norm_num] using (hamp (decode l)).1
    · intro j hj u hu
      have hu' : u ∈ sampled (decode l) := (hrows (decode l)) ▸ hu
      exact (hamp (decode l)).2 j hj u hu'
    · intro hbin
      exact (lt_irrefl (51 / 100 : ℝ) hbin).elim
  have hn := amplitudeLabels_card_pos g.slots width (1 / 100)
  have hN := amplitudeLabels_card_le_fixed g.slots hw
    (show (1 / 100 : ℝ) ≤ 1 / 2 by norm_num)
  refine ⟨b.pad hn hN, rfl, rfl, b.pad_source hn hN d Z T B lam k hblock, ?_, ?_, ?_⟩
  · intro l
    exact hgeometry (decode (fixedLabelProjection hn l))
  · intro l
    change (A (decode (fixedLabelProjection hn l))).rows (Z ^ d) ⊆ rows
    rw [hrows]
    exact hsub _
  · intro l
    exact hp (decode (fixedLabelProjection hn l))

end Expansion.Project

#print axioms Expansion.Project.floorRecipeAmplitude_geometry
#print axioms Expansion.Project.exists_physical_floor_block_source
