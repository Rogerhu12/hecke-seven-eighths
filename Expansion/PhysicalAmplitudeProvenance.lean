import Expansion.PhysicalFloorSource

/-!
# Retained physical labels and the provenance of every sampled source

The fixed alphabet contains a canonical embedded copy of the actual
bin-dependent amplitude labels. Its retained-label sum is exactly the
original amplitude-label sum. Every retained label keeps its decoded
amplitude, literal prime-slot fiber, and common sample maximizing the
fiber cardinality in the original height box. Padding only repeats such
actual sources. These facts are separate from the raw recipe data and
assert no integral or kernel estimate.
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

/-- The canonical embedding of the actual bin alphabet into a fixed one. -/
def physicalAmplitudeLabelEmbedding (J : ℕ) (width cap : ℝ) {N : ℕ}
    (hcard : Fintype.card (AmplitudeLabels J width cap) ≤ N) :
    AmplitudeLabels J width cap ↪ Fin N :=
  (Fintype.equivFin (AmplitudeLabels J width cap)).toEmbedding.trans
    (Fin.castLEEmb hcard)

theorem physicalAmplitudeLabelEmbedding_mem (J : ℕ) (width cap : ℝ) {N : ℕ}
    (hcard : Fintype.card (AmplitudeLabels J width cap) ≤ N)
    (label : AmplitudeLabels J width cap) :
    physicalAmplitudeLabelEmbedding J width cap hcard label ∈
      retainedFixedLabels hcard := by
  apply (mem_retainedFixedLabels hcard _).mpr
  exact ((Fintype.equivFin (AmplitudeLabels J width cap)) label).isLt

theorem retainedFixedLabels_eq_physicalAmplitudeLabels (J : ℕ) (width cap : ℝ)
    {N : ℕ} (hcard : Fintype.card (AmplitudeLabels J width cap) ≤ N) :
    retainedFixedLabels hcard =
      Finset.univ.map (physicalAmplitudeLabelEmbedding J width cap hcard) := by
  let e := Fintype.equivFin (AmplitudeLabels J width cap)
  ext j
  constructor
  · intro hj
    let i : Fin (Fintype.card (AmplitudeLabels J width cap)) :=
      ⟨j.val, (mem_retainedFixedLabels hcard j).mp hj⟩
    refine Finset.mem_map.mpr ⟨e.symm i, Finset.mem_univ _, ?_⟩
    change Fin.castLEEmb hcard (e (e.symm i)) = j
    rw [e.apply_symm_apply]
    apply Fin.ext
    rfl
  · intro hj
    obtain ⟨label, _, rfl⟩ := Finset.mem_map.mp hj
    exact physicalAmplitudeLabelEmbedding_mem J width cap hcard label

/-- Retaining exactly the original labels introduces no multiplicity. -/
theorem sum_retained_physicalAmplitudeLabels (J : ℕ) (width cap : ℝ) {N : ℕ}
    (hcard : Fintype.card (AmplitudeLabels J width cap) ≤ N) (f : Fin N → ℂ) :
    (∑ j ∈ retainedFixedLabels hcard, f j) =
      ∑ label, f (physicalAmplitudeLabelEmbedding J width cap hcard label) := by
  rw [retainedFixedLabels_eq_physicalAmplitudeLabels J width cap hcard]
  simp only [Finset.sum_map]

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)
variable (ω ψ : HeckeCharacter K) (g : PrimeWindowGeometry)

/-- The exact sampled fiber of an actual numerical amplitude label. -/
def PhysicalAmplitudeOrigin (F : RecipeFamily K ψ g) (width cap Z T U : ℝ)
    (rows : Finset (FrequencyRow K S)) (sector : SixthUnitClasses K S)
    (label : AmplitudeLabels g.slots width cap)
    (A : RecipeAmplitudeData K S ψ g F) : Prop :=
  A.sector = sector ∧ ‖A.physical‖ ≤ T ∧
    A.amplitude = (fun j => decodeAmplitude width cap (label j)) ∧
    A.rows U = recipeAmplitudeRows K S P R ω ψ g F width cap Z rows A.physical label ∧
    ∀ q : Fin 3 → ℝ, ‖q‖ ≤ T →
      (recipeAmplitudeRows K S P R ω ψ g F width cap Z rows q label).card ≤
        (A.rows U).card

variable (E : RowEulerData K S P)
variable (slotTime : Fin g.slots → (Fin 3 → ℝ) → ℝ)
variable (slotPower : Fin g.slots → (Fin 3 → ℝ) → ℂ)
variable (slotCoefficient : Fin g.slots → HeckeCharacter K)

/-- The live-bin source with the original finite labels still visible.
The first label assertion covers every actual amplitude code through the
canonical embedding; the second also identifies every padded label. -/
theorem exists_physical_live_block_source_with_provenance
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) (lam : ℝ) (hlam : 0 < lam) :
    ∃ e ε ceiling k : ℝ,
      0 < e ∧ e < 1 / 1000 ∧ e ≤ lam / 1000 ∧ 0 < ε ∧ 0 < ceiling ∧ 0 < k ∧
      ∀ N : ℕ, ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
        let F := scaledCanonicalRecipeFamily K ψ g cutoffProfile slotTime slotPower
          slotCoefficient (3 * ((N : ℝ) + 1))
        ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
          ∀ d a B : ℝ, 1 / 16 ≤ d → d ≤ 13 / 16 + lam → d ≤ 1 →
          51 / 100 ≤ a → a ≤ B → B ≤ 1 → ∀ h : ℕ, h ≤ N →
          ∀ sector : SixthUnitClasses K S, ∀ rows : Finset (FrequencyRow K S),
            (∀ u ∈ rows, Z ^ d < frequencyRowNorm K S u) →
            (∀ u ∈ rows, frequencyRowNorm K S u ≤ 2 * Z ^ d) →
            (∀ u ∈ rows, u.sector = sector) →
            (∀ u ∈ rows, rowZeroAbove K S ψ {1} P E u
              (selectedHeight h (Z ^ τ)) a) →
            (∀ u ∈ rows, rowZeroBelow K S ψ {1} P E u
              (upperHeight h (Z ^ τ)) (a + 2 * e)) →
            ∀ width : ℝ, 0 < width → ∀ value : ℂ,
            ∃ hcard : Fintype.card (AmplitudeLabels g.slots width ((2 * a - 1) / 2)) ≤
              fixedAmplitudeLabelCount g.slots width,
            ∃ b : RecipeBlockData K S ψ g F (fixedAmplitudeLabelCount g.slots width),
              b.bin = a ∧ b.value = value ∧
              BlockSource g (b.toBlock (P := P) (R := E.rows) (ω := ω)
                d Z (Z ^ τ)) B lam k Z ∧
              (∀ l, (b.amplitude l).MomentGeometry (Z ^ τ) 22) ∧
              (∀ label : AmplitudeLabels g.slots width ((2 * a - 1) / 2),
                PhysicalAmplitudeOrigin K S P E.rows ω ψ g F width ((2 * a - 1) / 2)
                  Z (Z ^ τ) (Z ^ d) rows sector label
                    (b.amplitude (physicalAmplitudeLabelEmbedding g.slots width
                      ((2 * a - 1) / 2) hcard label))) ∧
              (∀ l, ∃ label : AmplitudeLabels g.slots width ((2 * a - 1) / 2),
                PhysicalAmplitudeOrigin K S P E.rows ω ψ g F width ((2 * a - 1) / 2)
                  Z (Z ^ τ) (Z ^ d) rows sector label (b.amplitude l)) := by
  obtain ⟨e, ε, ceiling, k, he, heSmall, heLam, hε, hceiling, hk, hsource⟩ :=
    exists_physical_amplitude_source K S P ω ψ g E slotTime slotPower
      slotCoefficient hcomplex lam hlam
  refine ⟨e, ε, ceiling, k, he, heSmall, heLam, hε, hceiling, hk, ?_⟩
  intro N τ hτ hτc
  dsimp only
  let F := scaledCanonicalRecipeFamily K ψ g cutoffProfile slotTime slotPower
    slotCoefficient (3 * ((N : ℝ) + 1))
  obtain ⟨Z₀, hZ₀, hdata⟩ := hsource N τ hτ hτc
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZ d a B hd hdUpper hdOne ha haB hB h hh sector rows hlower hnorm
    hsector habove hbelow width hw value
  let Labels := AmplitudeLabels g.slots width ((2 * a - 1) / 2)
  have hlabels := hdata Z hZ d a hd hdOne ha h hh sector rows
    hlower hnorm hsector habove hbelow width hw
  choose p A hp hphysical hsectorA hamplitude_eq hrows hmax hgeometry hamplitude hslots hwitness
    using hlabels
  have horigin (label : Labels) :
      PhysicalAmplitudeOrigin K S P E.rows ω ψ g F width ((2 * a - 1) / 2)
        Z (Z ^ τ) (Z ^ d) rows sector label (A label) := by
    refine ⟨hsectorA label, ?_, hamplitude_eq label, ?_, hmax label⟩
    · rw [hphysical label]
      exact hp label
    · rw [hphysical label]
      exact hrows label
  let decode := (Fintype.equivFin Labels).symm
  let b : RecipeBlockData K S ψ g F (Fintype.card Labels) :=
    { bin := a
      value := value
      amplitude := fun l => A (decode l) }
  have hblock : BlockSource g
      (b.toBlock (P := P) (R := E.rows) (ω := ω) d Z (Z ^ τ)) B lam k Z := by
    refine ⟨by dsimp [b, RecipeBlockData.toBlock]; linarith,
      hdUpper, ha, haB, ?_⟩
    intro l
    exact ⟨hamplitude (decode l), hslots (decode l),
      fun _ t ht ht' => hwitness (decode l) t ht ht'⟩
  have hn := amplitudeLabels_card_pos g.slots width ((2 * a - 1) / 2)
  have hcard := amplitudeLabels_card_le_fixed g.slots hw
    (show (2 * a - 1) / 2 ≤ 1 / 2 by linarith)
  refine ⟨hcard, b.pad hn hcard, rfl, rfl,
    b.pad_source hn hcard d Z (Z ^ τ) B lam k hblock, ?_, ?_, ?_⟩
  · intro l
    exact hgeometry (decode (fixedLabelProjection hn l))
  · intro label
    have heq : (b.pad hn hcard).amplitude
        (physicalAmplitudeLabelEmbedding g.slots width ((2 * a - 1) / 2) hcard label) =
          A label := by
      change A (decode (fixedLabelProjection hn
        (Fin.castLEEmb hcard ((Fintype.equivFin Labels) label)))) = A label
      rw [fixedLabelProjection_embed]
      simp only [decode, Equiv.symm_apply_apply]
    rw [heq]
    exact horigin label
  · intro l
    exact ⟨decode (fixedLabelProjection hn l), horigin _⟩

/-- The floor bin preserves the same physical provenance and fixed label
embedding. Its source needs no live-bin zero-detection hypothesis. -/
theorem exists_physical_floor_block_source_with_provenance
    (F : RecipeFamily K ψ g) (Z T d B lam k width : ℝ) (value : ℂ)
    (hZ : 1 < Z) (hT : 1 ≤ T) (hd : 1 / 16 ≤ d) (hd' : d ≤ 13 / 16 + lam)
    (hB : 51 / 100 ≤ B) (hw : 0 < width)
    (sector : SixthUnitClasses K S) (rows : Finset (FrequencyRow K S))
    (hnorm : ∀ u ∈ rows, frequencyRowNorm K S u ≤ 2 * Z ^ d)
    (hsector : ∀ u ∈ rows, u.sector = sector) :
    ∃ hcard : Fintype.card (AmplitudeLabels g.slots width (1 / 100)) ≤
      fixedAmplitudeLabelCount g.slots width,
    ∃ b : RecipeBlockData K S ψ g F (fixedAmplitudeLabelCount g.slots width),
      b.bin = 51 / 100 ∧ b.value = value ∧
      BlockSource g (b.toBlock (P := P) (R := R) (ω := ω) d Z T) B lam k Z ∧
      (∀ l, (b.amplitude l).MomentGeometry T 22) ∧
      (∀ label : AmplitudeLabels g.slots width (1 / 100),
        PhysicalAmplitudeOrigin K S P R ω ψ g F width (1 / 100) Z T (Z ^ d)
          rows sector label (b.amplitude
            (physicalAmplitudeLabelEmbedding g.slots width (1 / 100) hcard label))) ∧
      (∀ l, ∃ label : AmplitudeLabels g.slots width (1 / 100),
        PhysicalAmplitudeOrigin K S P R ω ψ g F width (1 / 100) Z T (Z ^ d)
          rows sector label (b.amplitude l)) := by
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
  have horigin (label : Labels) :
      PhysicalAmplitudeOrigin K S P R ω ψ g F width (1 / 100) Z T (Z ^ d)
        rows sector label (A label) := by
    refine ⟨rfl, hp label, rfl, hrows label, ?_⟩
    intro q hq
    rw [hrows label]
    exact hmax label q hq
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
  have hcard := amplitudeLabels_card_le_fixed g.slots hw
    (show (1 / 100 : ℝ) ≤ 1 / 2 by norm_num)
  refine ⟨hcard, b.pad hn hcard, rfl, rfl,
    b.pad_source hn hcard d Z T B lam k hblock, ?_, ?_, ?_⟩
  · intro l
    exact hgeometry (decode (fixedLabelProjection hn l))
  · intro label
    have heq : (b.pad hn hcard).amplitude
        (physicalAmplitudeLabelEmbedding g.slots width (1 / 100) hcard label) = A label := by
      change A (decode (fixedLabelProjection hn
        (Fin.castLEEmb hcard ((Fintype.equivFin Labels) label)))) = A label
      rw [fixedLabelProjection_embed]
      simp only [decode, Equiv.symm_apply_apply]
    rw [heq]
    exact horigin label
  · intro l
    exact ⟨decode (fixedLabelProjection hn l), horigin _⟩

end Expansion.Project

#print axioms Expansion.Project.sum_retained_physicalAmplitudeLabels
#print axioms Expansion.Project.exists_physical_live_block_source_with_provenance
#print axioms Expansion.Project.exists_physical_floor_block_source_with_provenance
