import Expansion.PhysicalRecipeOrigins
import Expansion.PhysicalAmplitudeIntegral
import Expansion.PhysicalContourMeasure

/-!
# The actual labels and transported pieces of the physical recipe

Every receiving row belongs to the genuine maximal-cardinality amplitude
fiber at the physical sample stored in the same recipe block.  At each
physical parameter its contribution is the existing finite-pattern
transport of an original row kernel.  The retained label sum is exactly
the unchanged original row contour sum.  No analytic estimate is part of
the construction.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open ExpansionInterfaces Expansion.CommonSampleTransport
open scoped Classical BigOperators ComplexConjugate

section LabelTransport

variable {K : Type} [Field K] [NumberField K]
variable {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
variable {P : ProbeData K S} {R : RowCharacterInput K S P}
variable {ω ψ : HeckeCharacter K} {g : PrimeWindowGeometry}
variable {F : RecipeFamily K ψ g} {N : ℕ}

def physicalBlockLabelSample (width cap : ℝ) (b : RecipeBlockData K S ψ g F N)
    (hcard : Fintype.card (AmplitudeLabels g.slots width cap) ≤ N)
    (label : AmplitudeLabels g.slots width cap) : Fin 3 → ℝ :=
  (b.amplitude (physicalAmplitudeLabelEmbedding g.slots width cap hcard label)).physical

def physicalBlockLabelRows (width cap Z : ℝ) (rows : Finset (FrequencyRow K S))
    (b : RecipeBlockData K S ψ g F N)
    (hcard : Fintype.card (AmplitudeLabels g.slots width cap) ≤ N)
    (label : AmplitudeLabels g.slots width cap) : Finset (FrequencyRow K S) :=
  recipeAmplitudeRows K S P R ω ψ g F width cap Z rows
    (physicalBlockLabelSample width cap b hcard label) label

/-- A receiving row carries at most one original moving-row kernel at
each parameter, using the existing cardinality-preserving injection. -/
def physicalBlockLabelIntegrand (width cap Z : ℝ) (rows : Finset (FrequencyRow K S))
    (b : RecipeBlockData K S ψ g F N)
    (hcard : Fintype.card (AmplitudeLabels g.slots width cap) ≤ N)
    (kernel : FrequencyRow K S → (Fin 3 → ℝ) → ℂ)
    (label : AmplitudeLabels g.slots width cap) (u : FrequencyRow K S) (p : Fin 3 → ℝ) : ℂ :=
  let target := physicalBlockLabelRows (P := P) (R := R) (ω := ω) width cap Z rows b hcard label
  if hu : u ∈ target then
    movingPiece rows target
      (fun q => recipeAmplitudeRows K S P R ω ψ g F width cap Z rows q label)
      kernel ⟨u, hu⟩ p
  else 0

/-- The retained labels alone contribute; extra fixed-alphabet labels
retain legal source data but their transported pieces are zero. -/
def physicalBlockShiftedPiece (width cap Z T : ℝ) (rows : Finset (FrequencyRow K S))
    (b : RecipeBlockData K S ψ g F N)
    (hcard : Fintype.card (AmplitudeLabels g.slots width cap) ≤ N)
    (measure : Measure (Fin 3 → ℝ))
    (kernel : FrequencyRow K S → (Fin 3 → ℝ) → ℂ) (l : Fin N) (u : FrequencyRow K S) : ℂ :=
  fixedLabelPiece
    (fun i u => ∫ p in {p : Fin 3 → ℝ | ‖p‖ ≤ T},
      physicalBlockLabelIntegrand (P := P) (R := R) (ω := ω) width cap Z rows b hcard kernel
        ((Fintype.equivFin (AmplitudeLabels g.slots width cap)).symm i) u p ∂measure) l u

theorem physicalBlockShiftedPiece_embed (width cap Z T : ℝ)
    (rows : Finset (FrequencyRow K S)) (b : RecipeBlockData K S ψ g F N)
    (hcard : Fintype.card (AmplitudeLabels g.slots width cap) ≤ N)
    (measure : Measure (Fin 3 → ℝ)) (kernel : FrequencyRow K S → (Fin 3 → ℝ) → ℂ)
    (label : AmplitudeLabels g.slots width cap) (u : FrequencyRow K S) :
    physicalBlockShiftedPiece (P := P) (R := R) (ω := ω) width cap Z T rows b hcard measure kernel
      (physicalAmplitudeLabelEmbedding g.slots width cap hcard label) u =
      ∫ p in {p : Fin 3 → ℝ | ‖p‖ ≤ T},
        physicalBlockLabelIntegrand (P := P) (R := R) (ω := ω)
          width cap Z rows b hcard kernel label u p ∂measure := by
  unfold physicalBlockShiftedPiece physicalAmplitudeLabelEmbedding
  change fixedLabelPiece _
    (Fin.castLEEmb hcard ((Fintype.equivFin (AmplitudeLabels g.slots width cap)) label)) u = _
  rw [fixedLabelPiece_embed, Equiv.symm_apply_apply]

theorem physicalBlockShiftedPiece_zero (width cap Z T : ℝ)
    (rows : Finset (FrequencyRow K S)) (b : RecipeBlockData K S ψ g F N)
    (hcard : Fintype.card (AmplitudeLabels g.slots width cap) ≤ N)
    (measure : Measure (Fin 3 → ℝ)) (kernel : FrequencyRow K S → (Fin 3 → ℝ) → ℂ)
    (l : Fin N) (hl : l ∉ retainedFixedLabels hcard) (u : FrequencyRow K S) :
    physicalBlockShiftedPiece (P := P) (R := R) (ω := ω)
      width cap Z T rows b hcard measure kernel l u = 0 :=
  fixedLabelPiece_zero_of_not_retained _ hcard l hl u

theorem physicalBlockLabelIntegrand_integrable
    (hF : ∀ j, Measurable (F.slotPower j)) (width cap Z T : ℝ)
    (rows : Finset (FrequencyRow K S)) (b : RecipeBlockData K S ψ g F N)
    (hcard : Fintype.card (AmplitudeLabels g.slots width cap) ≤ N)
    (measure : Measure (Fin 3 → ℝ)) (kernel : FrequencyRow K S → (Fin 3 → ℝ) → ℂ)
    (hkernel : ∀ u ∈ rows, IntegrableOn (kernel u) {p : Fin 3 → ℝ | ‖p‖ ≤ T} measure)
    (label : AmplitudeLabels g.slots width cap) (u : FrequencyRow K S) :
    IntegrableOn (physicalBlockLabelIntegrand (P := P) (R := R) (ω := ω)
      width cap Z rows b hcard kernel label u) {p : Fin 3 → ℝ | ‖p‖ ≤ T} measure := by
  let target := physicalBlockLabelRows (P := P) (R := R) (ω := ω) width cap Z rows b hcard label
  by_cases hu : u ∈ target
  · have hfun : physicalBlockLabelIntegrand (P := P) (R := R) (ω := ω)
        width cap Z rows b hcard kernel label u =
        movingPiece rows target
          (fun q => recipeAmplitudeRows K S P R ω ψ g F width cap Z rows q label)
          kernel ⟨u, hu⟩ := by
      funext p
      simp only [physicalBlockLabelIntegrand, show u ∈ physicalBlockLabelRows
        (P := P) (R := R) (ω := ω) width cap Z rows b hcard label from hu, dif_pos]
    rw [hfun]
    apply movingPiece_integrable measure {p : Fin 3 → ℝ | ‖p‖ ≤ T} rows target _ kernel hkernel
    intro A hA
    exact measurableSet_recipeAmplitudeRows_eq K S P R ω ψ g F hF width cap Z rows label A
      (mem_patterns.mp hA).1
  · have hfun : physicalBlockLabelIntegrand (P := P) (R := R) (ω := ω)
        width cap Z rows b hcard kernel label u = (fun _ : Fin 3 → ℝ => (0 : ℂ)) := by
      funext p
      simp only [physicalBlockLabelIntegrand, show u ∉ physicalBlockLabelRows
        (P := P) (R := R) (ω := ω) width cap Z rows b hcard label from hu, dif_neg]
    rw [hfun]
    exact integrable_zero _ _ _

private theorem physicalBlockLabel_sum_subtype (width cap Z T U : ℝ)
    (rows : Finset (FrequencyRow K S)) (sector : SixthUnitClasses K S)
    (b : RecipeBlockData K S ψ g F N)
    (hcard : Fintype.card (AmplitudeLabels g.slots width cap) ≤ N)
    (measure : Measure (Fin 3 → ℝ)) (kernel : FrequencyRow K S → (Fin 3 → ℝ) → ℂ)
    (label : AmplitudeLabels g.slots width cap)
    (horigin : PhysicalAmplitudeOrigin K S P R ω ψ g F width cap Z T U rows sector label
      (b.amplitude (physicalAmplitudeLabelEmbedding g.slots width cap hcard label))) :
    (∑ u ∈ (b.amplitude (physicalAmplitudeLabelEmbedding g.slots width cap hcard label)).rows U,
      ∫ p in {p : Fin 3 → ℝ | ‖p‖ ≤ T},
        physicalBlockLabelIntegrand (P := P) (R := R) (ω := ω)
          width cap Z rows b hcard kernel label u p ∂measure) =
      ∑ v : physicalBlockLabelRows (P := P) (R := R) (ω := ω) width cap Z rows b hcard label,
        ∫ p in {p : Fin 3 → ℝ | ‖p‖ ≤ T},
          movingPiece rows
            (physicalBlockLabelRows (P := P) (R := R) (ω := ω) width cap Z rows b hcard label)
            (fun q => recipeAmplitudeRows K S P R ω ψ g F width cap Z rows q label)
            kernel v p ∂measure := by
  have heq : (b.amplitude (physicalAmplitudeLabelEmbedding g.slots width cap hcard label)).rows U =
      physicalBlockLabelRows (P := P) (R := R) (ω := ω) width cap Z rows b hcard label :=
    horigin.2.2.2.1
  rw [heq, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro v _
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => by
    simp only [physicalBlockLabelIntegrand, dif_pos v.property])

/-- Exact finite-label integral identity, with every sample read from the
same original recipe block.  Only ordinary kernel integrability is needed
for this generic transport theorem; the actual specialization proves it. -/
theorem physicalBlockShiftedPiece_sum
    (hF : ∀ j, Measurable (F.slotPower j)) (width cap Z T U : ℝ)
    (rows : Finset (FrequencyRow K S)) (sector : SixthUnitClasses K S)
    (b : RecipeBlockData K S ψ g F N)
    (hcard : Fintype.card (AmplitudeLabels g.slots width cap) ≤ N)
    (measure : Measure (Fin 3 → ℝ)) (kernel : FrequencyRow K S → (Fin 3 → ℝ) → ℂ)
    (hkernel : ∀ u ∈ rows, IntegrableOn (kernel u) {p : Fin 3 → ℝ | ‖p‖ ≤ T} measure)
    (horigin : ∀ label : AmplitudeLabels g.slots width cap,
      PhysicalAmplitudeOrigin K S P R ω ψ g F width cap Z T U rows sector label
        (b.amplitude (physicalAmplitudeLabelEmbedding g.slots width cap hcard label))) :
    (∑ l ∈ retainedFixedLabels hcard, ∑ u ∈ (b.amplitude l).rows U,
      physicalBlockShiftedPiece (P := P) (R := R) (ω := ω)
        width cap Z T rows b hcard measure kernel l u) =
      ∫ p in {p : Fin 3 → ℝ | ‖p‖ ≤ T}, ∑ u ∈ rows, kernel u p ∂measure := by
  rw [sum_retained_physicalAmplitudeLabels g.slots width cap hcard]
  simp_rw [physicalBlockShiftedPiece_embed]
  calc
    _ = ∑ label : AmplitudeLabels g.slots width cap,
        ∑ v : physicalBlockLabelRows (P := P) (R := R) (ω := ω) width cap Z rows b hcard label,
          ∫ p in {p : Fin 3 → ℝ | ‖p‖ ≤ T},
            movingPiece rows
              (physicalBlockLabelRows (P := P) (R := R) (ω := ω) width cap Z rows b hcard label)
              (fun q => recipeAmplitudeRows K S P R ω ψ g F width cap Z rows q label)
              kernel v p ∂measure := by
      apply Finset.sum_congr rfl
      intro label _
      exact physicalBlockLabel_sum_subtype width cap Z T U rows sector b hcard measure kernel
        label (horigin label)
    _ = _ := by
      apply recipeAmplitude_full_integral K S P R ω ψ g F hF width cap Z T rows
        (physicalBlockLabelSample width cap b hcard) _ measure kernel hkernel
      intro label p hp
      have hm := (horigin label).2.2.2.2 p hp
      rw [(horigin label).2.2.2.1] at hm
      exact hm

end LabelTransport

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The original floor/live buffered bin, with the floor's literal lack
of a selected-zero condition.  This is independent of any target context. -/
def physicalRecipeWideRowBin (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (P : ProbeData K S) (E : RowEulerData K S P)
    (selected upper lowerNorm upperNorm a e : ℝ) : Finset (FrequencyRow K S) :=
  if a = 51 / 100 then
    (frequencyRows K S upperNorm).filter fun u =>
      lowerNorm < frequencyRowNorm K S u ∧ ¬principalFrequencyRow K S u ∧
        rowZeroBelow K S psi companions P E u upper (a + 2 * e)
  else bufferedPhysicalRowBin K S psi companions P E selected upper lowerNorm upperNorm a e

def physicalRecipePresentationHeightIndex (B e : ℝ) (c : PhysicalRecipeChoice K S B e) :
    Fin (physicalRecipeHeightBound B e + 1) :=
  ⟨c.1.1.val, by
    have hc := physicalRecipeChoice_height_le K S B e c
    omega⟩

@[simp] theorem physicalRecipePresentationHeightIndex_val (B e : ℝ)
    (c : PhysicalRecipeChoice K S B e) :
    (physicalRecipePresentationHeightIndex K S B e c).val = c.1.1.val := rfl

variable (P : ProbeData K S) (E : RowEulerData K S P) (ω ψ : HeckeCharacter K)
variable {B e : ℝ} (hψ : ψ ∈ HeckePacket K ω)
variable (hB0 : 51 / 100 ≤ B) (hB : B ≤ 1) (he : 0 < e)
variable (hbound : ∀ χ r, r ∈ heckePacketZeros K ω χ →
  1 / 2 ≤ r → r ≤ 1 → r ≤ B)

theorem physicalRecipeRows_nonprincipal (ζ Z T : ℝ)
    (j : Fin (shellCount Z (1 / 16) (13 / 16 + ζ))) (c : PhysicalRecipeChoice K S B e)
    (u : FrequencyRow K S)
    (hu : u ∈ physicalRecipeRows K S P E ω ψ hψ hB0 hB he hbound ζ Z T j c) :
    ¬principalFrequencyRow K S u := by
  have hc := (Finset.mem_filter.mp hu).1
  have hs := clippedSelectedPhysicalRows_subset K S ω ψ {1} P E hψ
    (physicalRecipe_trivial_twists K) hB0 hB he hbound _ _ T c.1 hc
  exact (Finset.mem_filter.mp ((mem_selectedRows _ _ c.1 u).mp hs).1).2.2

theorem physicalRecipeRows_in_bin (ζ Z T : ℝ) (hZ : 1 < Z)
    (j : Fin (shellCount Z (1 / 16) (13 / 16 + ζ))) (c : PhysicalRecipeChoice K S B e) :
    physicalRecipeRows K S P E ω ψ hψ hB0 hB he hbound ζ Z T j c ⊆
      physicalRecipeWideRowBin K S ψ {1} P E
        (3 * ((physicalRecipePresentationHeightIndex K S B e c).val + 1 : ℝ) * T)
        (3 * ((physicalRecipePresentationHeightIndex K S B e c).val + 2 : ℝ) * T)
        (Z ^ shellExponent Z (1 / 16) j.val) (2 * Z ^ shellExponent Z (1 / 16) j.val)
        c.1.center e := by
  intro u hu
  have hr := physicalRecipeRows_spec K S P E ω ψ hψ hB0 hB he hbound ζ Z T hZ j c u hu
  have hc := (Finset.mem_filter.mp hu).1
  have hs := clippedSelectedPhysicalRows_subset K S ω ψ {1} P E hψ
    (physicalRecipe_trivial_twists K) hB0 hB he hbound _ _ T c.1 hc
  unfold physicalRecipeWideRowBin
  split_ifs with hfloor
  · apply Finset.mem_filter.mpr
    refine ⟨(mem_frequencyRows_iff K S _ (by positivity) u).mpr hr.2.1,
      hr.1, physicalRecipeRows_nonprincipal K S P E ω ψ hψ hB0 hB he hbound ζ Z T j c u hu, ?_⟩
    have hheight : upperHeight (c.1.1.val + 1) T =
        3 * ((physicalRecipePresentationHeightIndex K S B e c).val + 2 : ℝ) * T := by
      simp only [physicalRecipePresentationHeightIndex_val, upperHeight,
        Nat.cast_add, Nat.cast_one]
      ring
    exact hheight ▸ hr.2.2.2.2
  · have hlive : 51 / 100 < c.1.center :=
      lt_of_le_of_ne (rowBufferIndex_center_range hB0 he c.1).1 (Ne.symm hfloor)
    have hb := selectedPhysicalRows_subset_buffered K S ω ψ {1} P E hψ
      (physicalRecipe_trivial_twists K) hB0 hB he hbound _ T c.1 hlive hs
    simpa only [physicalRecipePresentationHeightIndex_val, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat] using hb

variable (g : PrimeWindowGeometry)

def physicalRecipeRetainedLabels (width : ℝ) (hw : 0 < width)
    (c : PhysicalRecipeChoice K S B e) : Finset (Fin (fixedAmplitudeLabelCount g.slots width)) :=
  retainedFixedLabels (amplitudeLabels_card_le_fixed g.slots hw
    (show (2 * c.1.center - 1) / 2 ≤ (1 / 2 : ℝ) from by
      have ha := (rowBufferIndex_center_range hB0 he c.1).2.trans hB
      linarith))

theorem measurable_physicalRecipeSlotPower (j : Fin g.slots) :
    Measurable ((physicalRecipeFamily K ψ g B e).slotPower j) := by
  change Measurable (fun p : Fin 3 → ℝ =>
    conj ((17 / 50 : ℂ) + (p 2 : ℂ) * Complex.I) - 1)
  fun_prop

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S) → Measure (p.val.adicCompletion K))
variable [∀ p : S, (μ p).IsAddHaarMeasure]
variable (windowCharacters : Finset (HeckeCharacter K))

/-- The concrete shifted piece of the same all-scale scheduled block. -/
def physicalRecipeShiftedPiece (lam ζ width k : ℝ) (hw : 0 < width) (Z T : ℝ)
    (j : Fin (shellCount Z (1 / 16) (13 / 16 + ζ))) (c : PhysicalRecipeChoice K S B e)
    (l : Fin (fixedAmplitudeLabelCount g.slots width)) (u : FrequencyRow K S) : ℂ :=
  physicalBlockShiftedPiece (P := P) (R := E.rows) (ω := ω)
    width ((2 * c.1.center - 1) / 2) Z T
    (physicalRecipeRows K S P E ω ψ hψ hB0 hB he hbound ζ Z T j c)
    (physicalRecipeScheduledBlock K S P ω ψ g E hψ hB0 hB he hbound
      μ windowCharacters lam ζ width k hw Z T j c)
    (amplitudeLabels_card_le_fixed g.slots hw (physicalRecipeChoice_cap K S hB0 hB he c))
    physicalHeightVolume
    (physicalContourKernel K S μ P ψ E g windowCharacters Z
      (c.1.center + 16 * e) (1 - c.1.center - 6 * e) (17 / 50)) l u

theorem physicalRecipeScheduledBlock_bin (lam ζ width k : ℝ) (hw : 0 < width) (Z T : ℝ)
    (j : Fin (shellCount Z (1 / 16) (13 / 16 + ζ))) (c : PhysicalRecipeChoice K S B e) :
    (physicalRecipeScheduledBlock K S P ω ψ g E hψ hB0 hB he hbound
      μ windowCharacters lam ζ width k hw Z T j c).bin = c.1.center :=
  physicalSourceOrDefault_bin K S P E.rows ω ψ g _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem physicalRecipeScheduledBlock_bin_range (lam ζ width k : ℝ) (hw : 0 < width) (Z T : ℝ)
    (j : Fin (shellCount Z (1 / 16) (13 / 16 + ζ))) (c : PhysicalRecipeChoice K S B e) :
    51 / 100 ≤ (physicalRecipeScheduledBlock K S P ω ψ g E hψ hB0 hB he hbound
      μ windowCharacters lam ζ width k hw Z T j c).bin ∧
    (physicalRecipeScheduledBlock K S P ω ψ g E hψ hB0 hB he hbound
      μ windowCharacters lam ζ width k hw Z T j c).bin ≤ B := by
  rw [physicalRecipeScheduledBlock_bin]
  exact rowBufferIndex_center_range hB0 he c.1

/-- The full retained-label sum is the original contour sum, with no
contribution from copied padding labels and no change of arithmetic rows. -/
theorem physicalRecipeShiftedPiece_sum (lam ζ width k : ℝ) (hw : 0 < width)
    (Z T : ℝ) (hZ : 1 < Z) (hT : 0 ≤ T)
    (j : Fin (shellCount Z (1 / 16) (13 / 16 + ζ))) (c : PhysicalRecipeChoice K S B e)
    (hkernel : ∀ u ∈ physicalRecipeRows K S P E ω ψ hψ hB0 hB he hbound ζ Z T j c,
      IntegrableOn (rowVerticalKernel K S μ P ψ E g windowCharacters u Z
        (c.1.center + 16 * e) (1 - c.1.center - 6 * e) (17 / 50))
        (rowRetainedHeightBox T) rowHeightVolume) :
    (∑ l ∈ physicalRecipeRetainedLabels K S (hB0 := hB0) (hB := hB) (he := he)
      (g := g) width hw c,
      ∑ u ∈ ((physicalRecipeScheduledBlock K S P ω ψ g E hψ hB0 hB he hbound
        μ windowCharacters lam ζ width k hw Z T j c).amplitude l).rows
          (Z ^ shellExponent Z (1 / 16) j.val),
        physicalRecipeShiftedPiece K S P E ω ψ hψ hB0 hB he hbound g
          μ windowCharacters lam ζ width k hw Z T j c l u) =
      physicalRecipeBlockValue K S P E ω ψ hψ hB0 hB he hbound
        μ g windowCharacters ζ Z T j c := by
  have ho := (physicalRecipeScheduledBlock_origins K S P ω ψ g E hψ hB0 hB he hbound
    μ windowCharacters lam ζ width k hw Z T hZ hT j c).1
  have hi (u : FrequencyRow K S)
      (hu : u ∈ physicalRecipeRows K S P E ω ψ hψ hB0 hB he hbound ζ Z T j c) :=
    physicalContourKernel_integrable K S μ P ψ E g windowCharacters Z T
      (c.1.center + 16 * e) (1 - c.1.center - 6 * e) (17 / 50) hT u (hkernel u hu)
  calc
    _ = ∫ p in {p : Fin 3 → ℝ | ‖p‖ ≤ T},
        ∑ u ∈ physicalRecipeRows K S P E ω ψ hψ hB0 hB he hbound ζ Z T j c,
          physicalContourKernel K S μ P ψ E g windowCharacters Z
            (c.1.center + 16 * e) (1 - c.1.center - 6 * e) (17 / 50) u p
          ∂physicalHeightVolume :=
      physicalBlockShiftedPiece_sum (measurable_physicalRecipeSlotPower K ψ g)
        width ((2 * c.1.center - 1) / 2) Z T (Z ^ shellExponent Z (1 / 16) j.val)
        _ c.2 _ _ physicalHeightVolume _ hi ho
    _ = _ := (sum_rowContourBox_eq_physicalHeight_integral K S μ P ψ E g windowCharacters
      Z T (c.1.center + 16 * e) (1 - c.1.center - 6 * e) (17 / 50) hT _ hkernel).symm

/-- The literal data field of the same block is its transported label sum. -/
theorem physicalRecipeScheduledBlock_identification (lam ζ width k : ℝ) (hw : 0 < width)
    (Z T : ℝ) (hZ : 1 < Z) (hT : 0 ≤ T)
    (j : Fin (shellCount Z (1 / 16) (13 / 16 + ζ))) (c : PhysicalRecipeChoice K S B e)
    (hkernel : ∀ u ∈ physicalRecipeRows K S P E ω ψ hψ hB0 hB he hbound ζ Z T j c,
      IntegrableOn (rowVerticalKernel K S μ P ψ E g windowCharacters u Z
        (c.1.center + 16 * e) (1 - c.1.center - 6 * e) (17 / 50))
        (rowRetainedHeightBox T) rowHeightVolume) :
    (physicalRecipeScheduledBlock K S P ω ψ g E hψ hB0 hB he hbound
      μ windowCharacters lam ζ width k hw Z T j c).value =
      ∑ l ∈ physicalRecipeRetainedLabels K S (hB0 := hB0) (hB := hB) (he := he)
        (g := g) width hw c,
        ∑ u ∈ ((physicalRecipeScheduledBlock K S P ω ψ g E hψ hB0 hB he hbound
          μ windowCharacters lam ζ width k hw Z T j c).amplitude l).rows
            (Z ^ shellExponent Z (1 / 16) j.val),
          physicalRecipeShiftedPiece K S P E ω ψ hψ hB0 hB he hbound g
            μ windowCharacters lam ζ width k hw Z T j c l u := by
  rw [physicalRecipeShiftedPiece_sum K S P E ω ψ hψ hB0 hB he hbound g
    μ windowCharacters lam ζ width k hw Z T hZ hT j c hkernel]
  exact physicalSourceOrDefault_value K S P E.rows ω ψ g _ _ _ _ _ _ _ _ _ _ _ _ _ _

end Expansion.Project

#print axioms Expansion.Project.physicalBlockLabelIntegrand_integrable
#print axioms Expansion.Project.physicalBlockShiftedPiece_sum
#print axioms Expansion.Project.physicalRecipeRows_in_bin
#print axioms Expansion.Project.physicalRecipeShiftedPiece_sum
#print axioms Expansion.Project.physicalRecipeScheduledBlock_identification
