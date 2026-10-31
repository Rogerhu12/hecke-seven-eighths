import Expansion.PhysicalRecipeSchedule

/-!
# One all-scale recipe with actual physical block values

The family, amplitude alphabet, and buffered-sector multiplicity are fixed
before the scale and height. Actual detector sources are selected whenever
they exist. Elsewhere the same numerical amplitude fibers have legal
default witnesses and retain the actual contour value. The eventual-source
theorem below proves existence from the physical detector and the original
packet boundary; no source or integral estimate is an input field.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.TIP ExpansionInterfaces
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)
variable (ω ψ : HeckeCharacter K) (g : PrimeWindowGeometry)

def physicalDefaultSample (F : RecipeFamily K ψ g) (width cap Z T : ℝ)
    (rows : Finset (FrequencyRow K S)) (label : AmplitudeLabels g.slots width cap) :
    Fin 3 → ℝ :=
  Classical.choose (exists_recipeAmplitude_sample K S P R ω ψ g F
    width cap Z (max T 0) (le_max_right _ _) rows label)

theorem physicalDefaultSample_norm (F : RecipeFamily K ψ g) (width cap Z T : ℝ)
    (rows : Finset (FrequencyRow K S)) (label : AmplitudeLabels g.slots width cap) :
    ‖physicalDefaultSample K S P R ω ψ g F width cap Z T rows label‖ ≤ max T 0 :=
  (Classical.choose_spec (exists_recipeAmplitude_sample K S P R ω ψ g F
    width cap Z (max T 0) (le_max_right _ _) rows label)).1

def physicalDefaultAmplitude (F : RecipeFamily K ψ g) (width cap Z T : ℝ)
    (rows : Finset (FrequencyRow K S)) (sector : SixthUnitClasses K S)
    (label : AmplitudeLabels g.slots width cap) : RecipeAmplitudeData K S ψ g F :=
  let p := physicalDefaultSample K S P R ω ψ g F width cap Z T rows label
  floorRecipeAmplitude K S ψ g F
    (recipeAmplitudeRows K S P R ω ψ g F width cap Z rows p label) sector p
      (fun j => decodeAmplitude width cap (label j))

theorem physicalDefaultAmplitude_geometry (F : RecipeFamily K ψ g)
    (width cap Z T : ℝ) (hT : 1 ≤ T) (rows : Finset (FrequencyRow K S))
    (sector : SixthUnitClasses K S) (label : AmplitudeLabels g.slots width cap) :
    (physicalDefaultAmplitude K S P R ω ψ g F width cap Z T rows sector label).MomentGeometry
      T 22 := by
  apply floorRecipeAmplitude_geometry K S ψ g F _ sector _ _ T hT
  exact (physicalDefaultSample_norm K S P R ω ψ g F width cap Z T rows label).trans_eq
    (max_eq_left (zero_le_one.trans hT))

def physicalDefaultBlock (F : RecipeFamily K ψ g) (width Z T a : ℝ)
    (hw : 0 < width) (hcap : (2 * a - 1) / 2 ≤ 1 / 2)
    (rows : Finset (FrequencyRow K S)) (sector : SixthUnitClasses K S) (value : ℂ) :
    RecipeBlockData K S ψ g F (fixedAmplitudeLabelCount g.slots width) :=
  let Labels := AmplitudeLabels g.slots width ((2 * a - 1) / 2)
  let b : RecipeBlockData K S ψ g F (Fintype.card Labels) :=
    { bin := a
      value := value
      amplitude := fun l => physicalDefaultAmplitude K S P R ω ψ g F
        width ((2 * a - 1) / 2) Z T rows sector ((Fintype.equivFin Labels).symm l) }
  b.pad (amplitudeLabels_card_pos g.slots width ((2 * a - 1) / 2))
    (amplitudeLabels_card_le_fixed g.slots hw hcap)

theorem physicalDefaultBlock_geometry (F : RecipeFamily K ψ g) (width Z T a : ℝ)
    (hw : 0 < width) (hcap : (2 * a - 1) / 2 ≤ 1 / 2) (hT : 1 ≤ T)
    (rows : Finset (FrequencyRow K S)) (sector : SixthUnitClasses K S) (value : ℂ) :
    ∀ l, ((physicalDefaultBlock K S P R ω ψ g F width Z T a hw hcap rows sector value).amplitude
      l).MomentGeometry T 22 := by
  intro l
  exact physicalDefaultAmplitude_geometry K S P R ω ψ g F width ((2 * a - 1) / 2)
    Z T hT rows sector _

/-- The source property used to select data has literal numerical
provenance. Its eventual existence is proved, rather than assumed. -/
def PhysicalRecipeBlockSource (F : RecipeFamily K ψ g) (width Z T d a B lam k : ℝ)
    (hw : 0 < width) (hcap : (2 * a - 1) / 2 ≤ 1 / 2)
    (rows : Finset (FrequencyRow K S)) (sector : SixthUnitClasses K S) (value : ℂ)
    (b : RecipeBlockData K S ψ g F (fixedAmplitudeLabelCount g.slots width)) : Prop :=
  b.bin = a ∧ b.value = value ∧
    BlockSource g (b.toBlock (P := P) (R := R) (ω := ω) d Z T) B lam k Z ∧
    (∀ l, (b.amplitude l).MomentGeometry T 22) ∧
    (∀ label : AmplitudeLabels g.slots width ((2 * a - 1) / 2),
      PhysicalAmplitudeOrigin K S P R ω ψ g F width ((2 * a - 1) / 2) Z T (Z ^ d)
        rows sector label (b.amplitude (physicalAmplitudeLabelEmbedding g.slots width
          ((2 * a - 1) / 2) (amplitudeLabels_card_le_fixed g.slots hw hcap) label))) ∧
    (∀ l, ∃ label : AmplitudeLabels g.slots width ((2 * a - 1) / 2),
      PhysicalAmplitudeOrigin K S P R ω ψ g F width ((2 * a - 1) / 2) Z T (Z ^ d)
        rows sector label (b.amplitude l))

def physicalSourceOrDefault (F : RecipeFamily K ψ g) (width Z T d a B lam k : ℝ)
    (hw : 0 < width) (hcap : (2 * a - 1) / 2 ≤ 1 / 2)
    (rows : Finset (FrequencyRow K S)) (sector : SixthUnitClasses K S) (value : ℂ) :
    RecipeBlockData K S ψ g F (fixedAmplitudeLabelCount g.slots width) :=
  if h : ∃ b, PhysicalRecipeBlockSource K S P R ω ψ g F width Z T d a B lam k
      hw hcap rows sector value b then Classical.choose h
  else physicalDefaultBlock K S P R ω ψ g F width Z T a hw hcap rows sector value

theorem physicalSourceOrDefault_bin (F : RecipeFamily K ψ g) (width Z T d a B lam k : ℝ)
    (hw : 0 < width) (hcap : (2 * a - 1) / 2 ≤ 1 / 2)
    (rows : Finset (FrequencyRow K S)) (sector : SixthUnitClasses K S) (value : ℂ) :
    (physicalSourceOrDefault K S P R ω ψ g F width Z T d a B lam k
      hw hcap rows sector value).bin = a := by
  unfold physicalSourceOrDefault
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · rfl

theorem physicalSourceOrDefault_value (F : RecipeFamily K ψ g) (width Z T d a B lam k : ℝ)
    (hw : 0 < width) (hcap : (2 * a - 1) / 2 ≤ 1 / 2)
    (rows : Finset (FrequencyRow K S)) (sector : SixthUnitClasses K S) (value : ℂ) :
    (physicalSourceOrDefault K S P R ω ψ g F width Z T d a B lam k
      hw hcap rows sector value).value = value := by
  unfold physicalSourceOrDefault
  split_ifs with h
  · exact (Classical.choose_spec h).2.1
  · rfl

theorem physicalSourceOrDefault_geometry (F : RecipeFamily K ψ g)
    (width Z T d a B lam k : ℝ) (hw : 0 < width) (hcap : (2 * a - 1) / 2 ≤ 1 / 2)
    (hT : 1 ≤ T) (rows : Finset (FrequencyRow K S))
    (sector : SixthUnitClasses K S) (value : ℂ) :
    ∀ l, ((physicalSourceOrDefault K S P R ω ψ g F width Z T d a B lam k
      hw hcap rows sector value).amplitude l).MomentGeometry T 22 := by
  unfold physicalSourceOrDefault
  split_ifs with h
  · exact (Classical.choose_spec h).2.2.2.1
  · exact physicalDefaultBlock_geometry K S P R ω ψ g F width Z T a
      hw hcap hT rows sector value

theorem physicalSourceOrDefault_source (F : RecipeFamily K ψ g)
    (width Z T d a B lam k : ℝ) (hw : 0 < width) (hcap : (2 * a - 1) / 2 ≤ 1 / 2)
    (rows : Finset (FrequencyRow K S)) (sector : SixthUnitClasses K S) (value : ℂ)
    (h : ∃ b, PhysicalRecipeBlockSource K S P R ω ψ g F width Z T d a B lam k
      hw hcap rows sector value b) :
    PhysicalRecipeBlockSource K S P R ω ψ g F width Z T d a B lam k hw hcap rows sector value
      (physicalSourceOrDefault K S P R ω ψ g F width Z T d a B lam k
        hw hcap rows sector value) := by
  rw [physicalSourceOrDefault, dif_pos h]
  exact Classical.choose_spec h

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

include hB0 hB he in
theorem physicalRecipeChoice_cap (c : PhysicalRecipeChoice K S B e) :
    (2 * c.1.center - 1) / 2 ≤ 1 / 2 := by
  have ha := (rowBufferIndex_center_range hB0 he c.1).2.trans hB
  linarith

def physicalRecipeScheduledBlock (lam ζ width k : ℝ) (hw : 0 < width) (Z T : ℝ)
    (j : Fin (shellCount Z (1 / 16) (13 / 16 + ζ))) (c : PhysicalRecipeChoice K S B e) :
    RecipeBlockData K S ψ g (physicalRecipeFamily K ψ g B e)
      (fixedAmplitudeLabelCount g.slots width) :=
  physicalSourceOrDefault K S P E.rows ω ψ g (physicalRecipeFamily K ψ g B e)
    width Z T (shellExponent Z (1 / 16) j.val) c.1.center B lam k hw
    (physicalRecipeChoice_cap K S hB0 hB he c)
    (physicalRecipeRows K S P E ω ψ hψ hB0 hB he hbound ζ Z T j c) c.2
    (physicalRecipeBlockValue K S P E ω ψ hψ hB0 hB he hbound μ g windowCharacters ζ Z T j c)

/-- The actual recipe, including an unchanged contour value at every
scheduled scale. All four remaining components are explicit data. -/
def physicalRecipeExpansion (lam ζ width k : ℝ) (hw : 0 < width)
    (principal small large tail : ℝ → ℝ → ℂ) : RecipeExpansion K S ψ g ζ where
  family := physicalRecipeFamily K ψ g B e
  labelCount := fixedAmplitudeLabelCount g.slots width
  bufferMultiplicity := physicalRecipeMultiplicity K S B e
  principal := principal
  small := small
  large := large
  tail := tail
  blocks Z T b := physicalRecipeScheduledBlock K S P ω ψ g E hψ hB0 hB he hbound
    μ windowCharacters lam ζ width k hw Z T
    (physicalRecipeShellIndex K S B e ζ Z b) (physicalRecipeChoice K S B e ζ Z b)

theorem physicalRecipeExpansion_block_value (lam ζ width k : ℝ) (hw : 0 < width)
    (principal small large tail : ℝ → ℝ → ℂ) (Z T : ℝ)
    (b : Fin (shellCount Z (1 / 16) (13 / 16 + ζ) * physicalRecipeMultiplicity K S B e)) :
    ((physicalRecipeExpansion K S P ω ψ g E hψ hB0 hB he hbound μ windowCharacters
      lam ζ width k hw principal small large tail).blocks Z T b).value =
      physicalRecipeBlockValue K S P E ω ψ hψ hB0 hB he hbound μ g windowCharacters ζ Z T
        (physicalRecipeShellIndex K S B e ζ Z b) (physicalRecipeChoice K S B e ζ Z b) :=
  physicalSourceOrDefault_value K S P E.rows ω ψ g _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Even before the detection threshold, every active source has the
same length and parameter bounds. -/
theorem physicalRecipeExpansion_geometry (lam ζ width k : ℝ) (hw : 0 < width)
    (principal small large tail : ℝ → ℝ → ℂ) :
    (physicalRecipeExpansion K S P ω ψ g E hψ hB0 hB he hbound μ windowCharacters
      lam ζ width k hw principal small large tail).MomentGeometry 22 := by
  intro Z T b l
  have hT := ((physicalRecipeExpansion K S P ω ψ g E hψ hB0 hB he hbound μ windowCharacters
    lam ζ width k hw principal small large tail).active_of_index Z T b).2
  exact physicalSourceOrDefault_geometry K S P E.rows ω ψ g _ _ _ _ _ _ _ _ _ _ _
    hT _ _ _ l

/-- Source and numerical provenance for every concrete scheduled block. -/
def PhysicalRecipeSourceAtScale (lam ζ width k : ℝ) (hw : 0 < width) (Z T : ℝ) : Prop :=
  ∀ j : Fin (shellCount Z (1 / 16) (13 / 16 + ζ)), ∀ c : PhysicalRecipeChoice K S B e,
    PhysicalRecipeBlockSource K S P E.rows ω ψ g (physicalRecipeFamily K ψ g B e)
      width Z T (shellExponent Z (1 / 16) j.val) c.1.center B lam k hw
      (physicalRecipeChoice_cap K S hB0 hB he c)
      (physicalRecipeRows K S P E ω ψ hψ hB0 hB he hbound ζ Z T j c) c.2
      (physicalRecipeBlockValue K S P E ω ψ hψ hB0 hB he hbound
        μ g windowCharacters ζ Z T j c)
      (physicalRecipeScheduledBlock K S P ω ψ g E hψ hB0 hB he hbound
        μ windowCharacters lam ζ width k hw Z T j c)

/-- The raw schedule uses the same quotient to recover its shell as the
public `RecipeExpansion.toHigh`, so the source is literally that block. -/
theorem physicalRecipeSourceAtScale_block (lam ζ width k : ℝ) (hw : 0 < width)
    (principal small large tail : ℝ → ℝ → ℂ) (Z T : ℝ)
    (h : PhysicalRecipeSourceAtScale K S P ω ψ g E hψ hB0 hB he hbound
      μ windowCharacters lam ζ width k hw Z T)
    (b : Fin ((physicalRecipeExpansion K S P ω ψ g E hψ hB0 hB he hbound
      μ windowCharacters lam ζ width k hw principal small large tail).activeCount Z T)) :
    BlockSource g (((physicalRecipeExpansion K S P ω ψ g E hψ hB0 hB he hbound
      μ windowCharacters lam ζ width k hw principal small large tail).toHigh
        (P := P) (R := E.rows) (ω := ω) Z T).block b) B lam k Z := by
  let X := physicalRecipeExpansion K S P ω ψ g E hψ hB0 hB he hbound
    μ windowCharacters lam ζ width k hw principal small large tail
  have hs := h (physicalRecipeShellIndex K S B e ζ Z (X.rawBlockIndex Z T b))
    (physicalRecipeChoice K S B e ζ Z (X.rawBlockIndex Z T b))
  exact hs.2.2.1

/-- One fixed all-scale physical recipe is an actual source at all
sufficiently large scales of every admissible small height exponent. The
choice of recipe, family, labels and multiplicity precedes that exponent. -/
theorem exists_physical_recipe_parameters
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (lam ζ : ℝ) (hlam : 0 < lam) (hlamSmall : lam < 1 / 48) (hζ : ζ ≤ lam)
    (eCap : ℝ) (heCap : 0 < eCap) :
    ∃ e₁ width ceiling k : ℝ, ∃ he₁ : 0 < e₁, ∃ hw : 0 < width,
      e₁ < 1 / 1000 ∧ e₁ ≤ lam / 1000 ∧ e₁ ≤ eCap ∧ 0 < ceiling ∧ 0 < k ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
        ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
          PhysicalRecipeSourceAtScale K S P ω ψ g E hψ hB0 hB he₁ hbound
            μ windowCharacters lam ζ width k hw Z (Z ^ τ) := by
  obtain ⟨e₁, width, ceiling, k, he₁, heSmall, heLam, heCap', hw, hceiling, hk, hsource⟩ :=
    exists_physical_live_block_source_with_provenance K S P ω ψ g E
      (physicalRecipeSlotTime g) (physicalRecipeSlotPower g)
      (physicalRecipeSlotCoefficient K g) hcomplex lam hlam eCap heCap
  refine ⟨e₁, width, ceiling, k, he₁, hw, heSmall, heLam, heCap', hceiling, hk, ?_⟩
  intro τ hτ hτc
  obtain ⟨Z₀, hZ₀, hdata⟩ := hsource (physicalRecipeHeightBound B e₁) τ hτ hτc
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZ j c
  have hZone : 1 < Z := by linarith [hZ₀.trans hZ]
  have hT : 1 ≤ Z ^ τ := Real.one_le_rpow hZone.le hτ.le
  let F := physicalRecipeFamily K ψ g B e₁
  let d := shellExponent Z (1 / 16) j.val
  let rows := physicalRecipeRows K S P E ω ψ hψ hB0 hB he₁ hbound ζ Z (Z ^ τ) j c
  let value := physicalRecipeBlockValue K S P E ω ψ hψ hB0 hB he₁ hbound
    μ g windowCharacters ζ Z (Z ^ τ) j c
  have hd := actualShell_range hZone j
  have hdUpper : d ≤ 13 / 16 + lam := hd.2.le.trans (by linarith)
  have hdOne : d ≤ 1 := by linarith
  have ha := rowBufferIndex_center_range hB0 he₁ c.1
  have hrows (u : FrequencyRow K S) (hu : u ∈ rows) :=
    physicalRecipeRows_spec K S P E ω ψ hψ hB0 hB he₁ hbound
      ζ Z (Z ^ τ) hZone j c u hu
  apply physicalSourceOrDefault_source K S P E.rows ω ψ g F
    width Z (Z ^ τ) d c.1.center B lam k hw
    (physicalRecipeChoice_cap K S hB0 hB he₁ c) rows c.2 value
  by_cases hlive : 51 / 100 < c.1.center
  · obtain ⟨hcard, b, hbin, hvalue, hblock, hgeometry, horigin, horiginAll⟩ :=
      hdata Z hZ d c.1.center B hd.1 hdUpper hdOne ha.1 ha.2 hB
        (c.1.1.val + 1) (physicalRecipeChoice_height_le K S B e₁ c) c.2 rows
        (fun u hu => (hrows u hu).1) (fun u hu => (hrows u hu).2.1)
        (fun u hu => (hrows u hu).2.2.1)
        (fun u hu => (hrows u hu).2.2.2.1 hlive)
        (fun u hu => (hrows u hu).2.2.2.2) width hw value
    exact ⟨b, hbin, hvalue, hblock, hgeometry, horigin, horiginAll⟩
  · have hfloor : c.1.center = 51 / 100 := le_antisymm (le_of_not_gt hlive) ha.1
    have hdelta : (2 * c.1.center - 1) / 2 = (1 / 100 : ℝ) := by
      rw [hfloor]
      norm_num
    obtain ⟨hcard, b, hbin, hvalue, hblock, hgeometry, horigin, horiginAll⟩ :=
      exists_physical_floor_block_source_with_provenance K S P E.rows ω ψ g F
        Z (Z ^ τ) d B lam k width value hZone hT hd.1 hdUpper hB0 hw c.2 rows
        (fun u hu => (hrows u hu).2.1) (fun u hu => (hrows u hu).2.2.1)
    refine ⟨b, hbin.trans hfloor.symm, hvalue, hblock, hgeometry, ?_, ?_⟩
    · simpa only [hdelta] using horigin
    · simpa only [hdelta] using horiginAll

/-- The same parameter choice supplies the geometry for every choice of
the four literal analytic components; it does not depend on those values. -/
theorem exists_physical_recipe_expansion
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (lam ζ : ℝ) (hlam : 0 < lam) (hlamSmall : lam < 1 / 48) (hζ : ζ ≤ lam)
    (eCap : ℝ) (heCap : 0 < eCap)
    (principal small large tail : ℝ → ℝ → ℂ) :
    ∃ e₁ width ceiling k : ℝ, ∃ he₁ : 0 < e₁, ∃ hw : 0 < width,
      e₁ < 1 / 1000 ∧ e₁ ≤ lam / 1000 ∧ e₁ ≤ eCap ∧ 0 < ceiling ∧ 0 < k ∧
      (physicalRecipeExpansion K S P ω ψ g E hψ hB0 hB he₁ hbound
        μ windowCharacters lam ζ width k hw principal small large tail).MomentGeometry 22 ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
        ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
          PhysicalRecipeSourceAtScale K S P ω ψ g E hψ hB0 hB he₁ hbound
            μ windowCharacters lam ζ width k hw Z (Z ^ τ) := by
  obtain ⟨e₁, width, ceiling, k, he₁, hw, heSmall, heLam, heCap', hceiling, hk, hsource⟩ :=
    exists_physical_recipe_parameters K S P ω ψ g E hψ hB0 hB hbound
      μ windowCharacters hcomplex lam ζ hlam hlamSmall hζ eCap heCap
  exact ⟨e₁, width, ceiling, k, he₁, hw, heSmall, heLam, heCap', hceiling, hk,
    physicalRecipeExpansion_geometry K S P ω ψ g E hψ hB0 hB he₁ hbound
      μ windowCharacters lam ζ width k hw principal small large tail, hsource⟩

end Expansion.Project

#print axioms Expansion.Project.physicalRecipeExpansion_block_value
#print axioms Expansion.Project.physicalRecipeExpansion_geometry
#print axioms Expansion.Project.physicalRecipeSourceAtScale_block
#print axioms Expansion.Project.exists_physical_recipe_parameters
#print axioms Expansion.Project.exists_physical_recipe_expansion
