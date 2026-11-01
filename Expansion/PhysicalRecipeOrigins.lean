import Expansion.PhysicalRecipeAssembly

/-!
# Numerical provenance at every active physical recipe scale

The default branch uses the same actual prime-slot fibers and a genuine
maximum-cardinality physical sample.  Its witnesses need no detection
assertion.  Both branches therefore preserve the origin of every retained
label and every copied padding label, including scales before detection.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open ExpansionInterfaces
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)
variable (ω ψ : HeckeCharacter K) (g : PrimeWindowGeometry)

theorem physicalDefaultSample_card_max (F : RecipeFamily K ψ g)
    (width cap Z T : ℝ) (rows : Finset (FrequencyRow K S))
    (label : AmplitudeLabels g.slots width cap) :
    ∀ q : Fin 3 → ℝ, ‖q‖ ≤ max T 0 →
      (recipeAmplitudeRows K S P R ω ψ g F width cap Z rows q label).card ≤
        (recipeAmplitudeRows K S P R ω ψ g F width cap Z rows
          (physicalDefaultSample K S P R ω ψ g F width cap Z T rows label) label).card :=
  (Classical.choose_spec (exists_recipeAmplitude_sample K S P R ω ψ g F
    width cap Z (max T 0) (le_max_right _ _) rows label)).2

theorem physicalDefaultAmplitude_origin (F : RecipeFamily K ψ g)
    (width cap Z T U : ℝ) (hT : 0 ≤ T) (hU : 0 ≤ U)
    (rows : Finset (FrequencyRow K S)) (sector : SixthUnitClasses K S)
    (hnorm : ∀ u ∈ rows, frequencyRowNorm K S u ≤ 2 * U)
    (hsector : ∀ u ∈ rows, u.sector = sector)
    (label : AmplitudeLabels g.slots width cap) :
    PhysicalAmplitudeOrigin K S P R ω ψ g F width cap Z T U rows sector label
      (physicalDefaultAmplitude K S P R ω ψ g F width cap Z T rows sector label) := by
  let p := physicalDefaultSample K S P R ω ψ g F width cap Z T rows label
  let sampled := recipeAmplitudeRows K S P R ω ψ g F width cap Z rows p label
  have hsub : sampled ⊆ rows := recipeAmplitudeRows_subset K S P R ω ψ g F
    width cap Z rows p label
  have hrows : (physicalDefaultAmplitude K S P R ω ψ g F width cap Z T rows sector label).rows U =
      sampled := floorRecipeAmplitude_rows K S ψ g F sampled sector p
        (fun j => decodeAmplitude width cap (label j)) U hU
        (fun u hu => hnorm u (hsub hu)) (fun u hu => hsector u (hsub hu))
  refine ⟨rfl, ?_, rfl, hrows, ?_⟩
  · exact (physicalDefaultSample_norm K S P R ω ψ g F width cap Z T rows label).trans_eq
      (max_eq_left hT)
  · intro q hq
    rw [hrows]
    exact physicalDefaultSample_card_max K S P R ω ψ g F width cap Z T rows label q
      (hq.trans (le_max_left _ _))

theorem physicalDefaultBlock_origins (F : RecipeFamily K ψ g)
    (width Z T d a : ℝ) (hw : 0 < width) (hcap : (2 * a - 1) / 2 ≤ 1 / 2)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (rows : Finset (FrequencyRow K S))
    (sector : SixthUnitClasses K S) (value : ℂ)
    (hnorm : ∀ u ∈ rows, frequencyRowNorm K S u ≤ 2 * Z ^ d)
    (hsector : ∀ u ∈ rows, u.sector = sector) :
    (∀ label : AmplitudeLabels g.slots width ((2 * a - 1) / 2),
      PhysicalAmplitudeOrigin K S P R ω ψ g F width ((2 * a - 1) / 2) Z T (Z ^ d)
        rows sector label
        ((physicalDefaultBlock K S P R ω ψ g F width Z T a hw hcap rows sector value).amplitude
          (physicalAmplitudeLabelEmbedding g.slots width ((2 * a - 1) / 2)
            (amplitudeLabels_card_le_fixed g.slots hw hcap) label))) ∧
    (∀ l, ∃ label : AmplitudeLabels g.slots width ((2 * a - 1) / 2),
      PhysicalAmplitudeOrigin K S P R ω ψ g F width ((2 * a - 1) / 2) Z T (Z ^ d)
        rows sector label
        ((physicalDefaultBlock K S P R ω ψ g F width Z T a hw hcap rows sector value).amplitude l)) := by
  let Labels := AmplitudeLabels g.slots width ((2 * a - 1) / 2)
  let hn := amplitudeLabels_card_pos g.slots width ((2 * a - 1) / 2)
  let hcard := amplitudeLabels_card_le_fixed g.slots hw hcap
  have ho (label : Labels) := physicalDefaultAmplitude_origin K S P R ω ψ g F
    width ((2 * a - 1) / 2) Z T (Z ^ d) hT (Real.rpow_nonneg hZ _) rows sector hnorm hsector label
  constructor
  · intro label
    change PhysicalAmplitudeOrigin K S P R ω ψ g F width ((2 * a - 1) / 2) Z T (Z ^ d)
      rows sector label (physicalDefaultAmplitude K S P R ω ψ g F
        width ((2 * a - 1) / 2) Z T rows sector
          ((Fintype.equivFin Labels).symm (fixedLabelProjection hn
            (Fin.castLEEmb hcard ((Fintype.equivFin Labels) label)))))
    rw [fixedLabelProjection_embed, Equiv.symm_apply_apply]
    exact ho label
  · intro l
    exact ⟨(Fintype.equivFin Labels).symm (fixedLabelProjection hn l), ho _⟩

/-- No detection threshold is used in either provenance conclusion. -/
theorem physicalSourceOrDefault_origins (F : RecipeFamily K ψ g)
    (width Z T d a B lam k : ℝ) (hw : 0 < width) (hcap : (2 * a - 1) / 2 ≤ 1 / 2)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (rows : Finset (FrequencyRow K S))
    (sector : SixthUnitClasses K S) (value : ℂ)
    (hnorm : ∀ u ∈ rows, frequencyRowNorm K S u ≤ 2 * Z ^ d)
    (hsector : ∀ u ∈ rows, u.sector = sector) :
    (∀ label : AmplitudeLabels g.slots width ((2 * a - 1) / 2),
      PhysicalAmplitudeOrigin K S P R ω ψ g F width ((2 * a - 1) / 2) Z T (Z ^ d)
        rows sector label
        ((physicalSourceOrDefault K S P R ω ψ g F width Z T d a B lam k hw hcap rows sector value).amplitude
          (physicalAmplitudeLabelEmbedding g.slots width ((2 * a - 1) / 2)
            (amplitudeLabels_card_le_fixed g.slots hw hcap) label))) ∧
    (∀ l, ∃ label : AmplitudeLabels g.slots width ((2 * a - 1) / 2),
      PhysicalAmplitudeOrigin K S P R ω ψ g F width ((2 * a - 1) / 2) Z T (Z ^ d)
        rows sector label
        ((physicalSourceOrDefault K S P R ω ψ g F width Z T d a B lam k hw hcap rows sector value).amplitude
          l)) := by
  unfold physicalSourceOrDefault
  split_ifs with h
  · exact (Classical.choose_spec h).2.2.2.2
  · exact physicalDefaultBlock_origins K S P R ω ψ g F width Z T d a hw hcap hZ hT
      rows sector value hnorm hsector

theorem PhysicalAmplitudeOrigin.rows_subset {F : RecipeFamily K ψ g}
    {width cap Z T U : ℝ} {rows : Finset (FrequencyRow K S)}
    {sector : SixthUnitClasses K S} {label : AmplitudeLabels g.slots width cap}
    {A : RecipeAmplitudeData K S ψ g F}
    (h : PhysicalAmplitudeOrigin K S P R ω ψ g F width cap Z T U rows sector label A) :
    A.rows U ⊆ rows := by
  rw [h.2.2.2.1]
  exact recipeAmplitudeRows_subset K S P R ω ψ g F width cap Z rows A.physical label

variable (E : RowEulerData K S P)
variable {B e : ℝ} (hψ : ψ ∈ HeckePacket K ω)
variable (hB0 : 51 / 100 ≤ B) (hB : B ≤ 1) (he : 0 < e)
variable (hbound : ∀ χ r, r ∈ heckePacketZeros K ω χ →
  1 / 2 ≤ r → r ≤ 1 → r ≤ B)
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S) → Measure (p.val.adicCompletion K))
variable [∀ p : S, (μ p).IsAddHaarMeasure]
variable (windowCharacters : Finset (HeckeCharacter K))

theorem physicalRecipeScheduledBlock_origins (lam ζ width k : ℝ) (hw : 0 < width)
    (Z T : ℝ) (hZ : 1 < Z) (hT : 0 ≤ T)
    (j : Fin (shellCount Z (1 / 16) (13 / 16 + ζ))) (c : PhysicalRecipeChoice K S B e) :
    let rows := physicalRecipeRows K S P E ω ψ hψ hB0 hB he hbound ζ Z T j c
    let b := physicalRecipeScheduledBlock K S P ω ψ g E hψ hB0 hB he hbound
      μ windowCharacters lam ζ width k hw Z T j c
    (∀ label : AmplitudeLabels g.slots width ((2 * c.1.center - 1) / 2),
      PhysicalAmplitudeOrigin K S P E.rows ω ψ g (physicalRecipeFamily K ψ g B e)
        width ((2 * c.1.center - 1) / 2) Z T (Z ^ shellExponent Z (1 / 16) j.val)
        rows c.2 label (b.amplitude (physicalAmplitudeLabelEmbedding g.slots width
          ((2 * c.1.center - 1) / 2)
          (amplitudeLabels_card_le_fixed g.slots hw (physicalRecipeChoice_cap K S hB0 hB he c)) label))) ∧
    (∀ l, ∃ label : AmplitudeLabels g.slots width ((2 * c.1.center - 1) / 2),
      PhysicalAmplitudeOrigin K S P E.rows ω ψ g (physicalRecipeFamily K ψ g B e)
        width ((2 * c.1.center - 1) / 2) Z T (Z ^ shellExponent Z (1 / 16) j.val)
        rows c.2 label (b.amplitude l)) := by
  dsimp only
  apply physicalSourceOrDefault_origins K S P E.rows ω ψ g
    (physicalRecipeFamily K ψ g B e) width Z T (shellExponent Z (1 / 16) j.val)
    c.1.center B lam k hw (physicalRecipeChoice_cap K S hB0 hB he c)
    (zero_lt_one.trans hZ).le hT
  · intro u hu
    exact (physicalRecipeRows_spec K S P E ω ψ hψ hB0 hB he hbound ζ Z T hZ j c u hu).2.1
  · intro u hu
    exact (physicalRecipeRows_spec K S P E ω ψ hψ hB0 hB he hbound ζ Z T hZ j c u hu).2.2.1

theorem physicalRecipeScheduledBlock_rows_subset (lam ζ width k : ℝ) (hw : 0 < width)
    (Z T : ℝ) (hZ : 1 < Z) (hT : 0 ≤ T)
    (j : Fin (shellCount Z (1 / 16) (13 / 16 + ζ))) (c : PhysicalRecipeChoice K S B e)
    (l : Fin (fixedAmplitudeLabelCount g.slots width)) :
    ((physicalRecipeScheduledBlock K S P ω ψ g E hψ hB0 hB he hbound
      μ windowCharacters lam ζ width k hw Z T j c).amplitude l).rows
        (Z ^ shellExponent Z (1 / 16) j.val) ⊆
      physicalRecipeRows K S P E ω ψ hψ hB0 hB he hbound ζ Z T j c := by
  obtain ⟨label, ho⟩ := (physicalRecipeScheduledBlock_origins K S P ω ψ g E hψ hB0 hB he hbound
    μ windowCharacters lam ζ width k hw Z T hZ hT j c).2 l
  exact PhysicalAmplitudeOrigin.rows_subset K S P E.rows ω ψ g ho

end Expansion.Project

#print axioms Expansion.Project.physicalDefaultAmplitude_origin
#print axioms Expansion.Project.physicalRecipeScheduledBlock_origins
#print axioms Expansion.Project.physicalRecipeScheduledBlock_rows_subset
