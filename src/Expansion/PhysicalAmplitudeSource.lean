import Expansion.PhysicalWitnessCover
import HeckeSkeleton.ExpansionModels.FixedAmplitudeLabels
import ExpansionInterfaces.AmplitudePartition
import HeckeSkeleton.ExpansionModels.CommonPhysicalSample
import Expansion.WitnessLoss

/-!
# Actual prime amplitudes and the physical witness source

The amplitude rows are the literal finite fibers of the actual normalized
prime polynomials.  One common physical point is chosen for every label,
with maximal row cardinality on the original height box.  The detector is
then applied to those same rows and that same physical point.

The resulting source has the required amplitude cap, every positive-slot
lower bound, the actual witness covers, and the uniform moment geometry.
The prime base here is the original external scale `Z`; moment models use
the already proved change-of-base identity when their row base is `U=Z^d`.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.TIP
open ExpansionInterfaces
open Expansion.Dyadic
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)
variable (ω ψ : HeckeCharacter K) (g : PrimeWindowGeometry)

/-- The shared physical slot at its original external scale, with the
unchanged complete-ideal mask and square-root normalization. -/
def recipePhysicalSlots (F : RecipeFamily K ψ g) (Z : ℝ) (p : Fin 3 → ℝ)
    (j : Fin g.slots) (u : FrequencyRow K S) : ℂ :=
  primePolynomial (F.slotModel K S P R ω ψ g p u.sector) j u.ideal.val Z 0

/-- A finite amplitude label is determined by those actual slot values. -/
def recipeAmplitudeRows (F : RecipeFamily K ψ g) (width cap Z : ℝ)
    (rows : Finset (FrequencyRow K S)) (p : Fin 3 → ℝ)
    (label : AmplitudeLabels g.slots width cap) : Finset (FrequencyRow K S) :=
  rowPiece rows (fun u j => slotCode width cap (physicalSlotBase g.slots Z)
    (recipePhysicalSlots K S P R ω ψ g F Z p j u)) label

theorem recipeAmplitudeRows_subset (F : RecipeFamily K ψ g) (width cap Z : ℝ)
    (rows : Finset (FrequencyRow K S)) (p : Fin 3 → ℝ)
    (label : AmplitudeLabels g.slots width cap) :
    recipeAmplitudeRows K S P R ω ψ g F width cap Z rows p label ⊆ rows :=
  rowPiece_subset _ _ _

/-- The sample lies in the original height box and dominates the row count
at every other physical point of that same box. -/
theorem exists_recipeAmplitude_sample (F : RecipeFamily K ψ g)
    (width cap Z T : ℝ) (hT : 0 ≤ T) (rows : Finset (FrequencyRow K S))
    (label : AmplitudeLabels g.slots width cap) :
    ∃ p : Fin 3 → ℝ, ‖p‖ ≤ T ∧ ∀ q : Fin 3 → ℝ, ‖q‖ ≤ T →
      (recipeAmplitudeRows K S P R ω ψ g F width cap Z rows q label).card ≤
        (recipeAmplitudeRows K S P R ω ψ g F width cap Z rows p label).card := by
  exact _root_.ExpansionRecipe.CommonPhysicalSample.exists_card_max_point rows
    {p : Fin 3 → ℝ | ‖p‖ ≤ T}
      ⟨0, by simpa only [Set.mem_setOf_eq, norm_zero] using hT⟩
    (fun p => recipeAmplitudeRows K S P R ω ψ g F width cap Z rows p label)
    (fun p _ => recipeAmplitudeRows_subset K S P R ω ψ g F width cap Z rows p label)

/-- Both numerical amplitude fields follow from the actual slot values;
no prime-polynomial lower estimate is assumed. -/
theorem recipeAmplitudeRows_amplitude_spec (F : RecipeFamily K ψ g)
    (width cap Z : ℝ) (rows : Finset (FrequencyRow K S)) (p : Fin 3 → ℝ)
    (hw : 0 < width) (hc : 0 ≤ cap) (hZ : 1 < Z)
    (label : AmplitudeLabels g.slots width cap) :
    (∀ j, 0 ≤ decodeAmplitude width cap (label j) ∧
      decodeAmplitude width cap (label j) ≤ cap) ∧
    (∀ j, 0 < decodeAmplitude width cap (label j) →
      ∀ u ∈ recipeAmplitudeRows K S P R ω ψ g F width cap Z rows p label,
        Z ^ ((1 / 6 : ℝ) / g.slots * decodeAmplitude width cap (label j)) ≤
          ‖recipePhysicalSlots K S P R ω ψ g F Z p j u‖) :=
  physical_amplitudePiece_spec g.slots g.slots_pos rows width cap Z
    (recipePhysicalSlots K S P R ω ψ g F Z p) hw hc hZ label

/-- Once finite-height prime cancellation supplies the uniform cap, every
row in the literal amplitude fiber also has its rounded upper bound. -/
theorem recipeAmplitudeRows_slot_upper (F : RecipeFamily K ψ g)
    (width cap Z : ℝ) (rows : Finset (FrequencyRow K S)) (p : Fin 3 → ℝ)
    (hw : 0 < width) (hc : 0 ≤ cap) (hZ : 1 < Z)
    (hprime : ∀ j, ∀ u ∈ rows, ‖recipePhysicalSlots K S P R ω ψ g F Z p j u‖ ≤
      physicalSlotBase g.slots Z ^ (cap + width))
    (label : AmplitudeLabels g.slots width cap) (j : Fin g.slots)
    (u : FrequencyRow K S)
    (hu : u ∈ recipeAmplitudeRows K S P R ω ψ g F width cap Z rows p label) :
    ‖recipePhysicalSlots K S P R ω ψ g F Z p j u‖ ≤
      Z ^ ((1 / 6 : ℝ) / g.slots * (decodeAmplitude width cap (label j) + width)) := by
  have hr := recipeAmplitudeRows_subset K S P R ω ψ g F width cap Z rows p label hu
  have heq := slotAmplitude_eq_on_piece g.slots rows width cap
    (fun _ => physicalSlotBase g.slots Z) (recipePhysicalSlots K S P R ω ψ g F Z p)
    hw hc label u hu j
  have hh := slotAmplitude_upper (recipePhysicalSlots K S P R ω ψ g F Z p j u)
    hw (physicalSlotBase_gt_one g.slots g.slots_pos hZ) (hprime j u hr)
  rw [heq] at hh
  simpa only [physicalSlotBase, ← Real.rpow_mul (zero_lt_one.trans hZ).le] using hh

variable (E : RowEulerData K S P)
variable (slotTime : Fin g.slots → (Fin 3 → ℝ) → ℝ)
variable (slotPower : Fin g.slots → (Fin 3 → ℝ) → ℂ)
variable (slotCoefficient : Fin g.slots → HeckeCharacter K)

/-- A real physical zero bin produces its amplitude source at one common
physical sample.  Constants and detector losses precede the height
multiplicity, scale, bin, amplitude label, and every witness choice. -/
theorem exists_physical_amplitude_source
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) (lam : ℝ) (hlam : 0 < lam)
    (eCap : ℝ) (heCap : 0 < eCap) :
    ∃ e ε ceiling k : ℝ,
      0 < e ∧ e < 1 / 1000 ∧ e ≤ lam / 1000 ∧ e ≤ eCap ∧
      0 < ε ∧ 0 < ceiling ∧ 0 < k ∧
      ∀ N : ℕ, ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
        let F := scaledCanonicalRecipeFamily K ψ g cutoffProfile slotTime slotPower
          slotCoefficient (3 * ((N : ℝ) + 1))
        ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
          ∀ d a : ℝ, 1 / 16 ≤ d → d ≤ 1 → 51 / 100 ≤ a →
          ∀ h : ℕ, h ≤ N → ∀ sector : SixthUnitClasses K S,
          ∀ rows : Finset (FrequencyRow K S),
            (∀ u ∈ rows, Z ^ d < frequencyRowNorm K S u) →
            (∀ u ∈ rows, frequencyRowNorm K S u ≤ 2 * Z ^ d) →
            (∀ u ∈ rows, u.sector = sector) →
            (∀ u ∈ rows, rowZeroAbove K S ψ {1} P E u
              (selectedHeight h (Z ^ τ)) a) →
            (∀ u ∈ rows, rowZeroBelow K S ψ {1} P E u
              (upperHeight h (Z ^ τ)) (a + 2 * e)) →
            ∀ width : ℝ, 0 < width →
            ∀ label : AmplitudeLabels g.slots width ((2 * a - 1) / 2),
            ∃ p : Fin 3 → ℝ, ∃ A : RecipeAmplitudeData K S ψ g F,
              ‖p‖ ≤ Z ^ τ ∧ A.physical = p ∧ A.sector = sector ∧
              A.amplitude = (fun j => decodeAmplitude width ((2 * a - 1) / 2) (label j)) ∧
              A.rows (Z ^ d) =
                recipeAmplitudeRows K S P E.rows ω ψ g F width ((2 * a - 1) / 2)
                  Z rows p label ∧
              (∀ q : Fin 3 → ℝ, ‖q‖ ≤ Z ^ τ →
                (recipeAmplitudeRows K S P E.rows ω ψ g F width ((2 * a - 1) / 2)
                  Z rows q label).card ≤ (A.rows (Z ^ d)).card) ∧
              A.MomentGeometry (Z ^ τ) 22 ∧
              (∀ j, 0 ≤ A.amplitude j ∧ A.amplitude j ≤ (2 * a - 1) / 2) ∧
              (∀ j, 0 < A.amplitude j → ∀ u ∈ A.rows (Z ^ d),
                Z ^ ((1 / 6 : ℝ) / g.slots * A.amplitude j) ≤
                  ‖(A.toAmplitude (P := P) (R := E.rows) (ω := ω)
                    Z (Z ^ τ) (Z ^ d)).slotValue j u‖) ∧
              (∀ t : ℝ, 1 ≤ t → t ≤ 3 / 2 →
                WitnessCover (A.toAmplitude (P := P) (R := E.rows) (ω := ω)
                  Z (Z ^ τ) (Z ^ d)) t (2 * a - 1) (Z ^ d) lam k) := by
  let innerLoss := min lam (1000 * eCap)
  have hinner : 0 < innerLoss := lt_min hlam (mul_pos (by norm_num) heCap)
  have hinnerLam : innerLoss ≤ lam := min_le_left _ _
  have hinnerCap : innerLoss ≤ 1000 * eCap := min_le_right _ _
  obtain ⟨e, ε, ceiling, k, he, heSmall, heInner, hε, hceiling, hk, hcover⟩ :=
    exists_physical_witness_cover_with_geometry K S P E ω ψ g slotTime slotPower
      slotCoefficient hcomplex innerLoss hinner
  refine ⟨e, ε, ceiling, k, he, heSmall, by linarith, by linarith,
    hε, hceiling, hk, ?_⟩
  intro N τ hτ hτc
  dsimp only
  let F := scaledCanonicalRecipeFamily K ψ g cutoffProfile slotTime slotPower
    slotCoefficient (3 * ((N : ℝ) + 1))
  obtain ⟨Z₀, hZ₀, hdata⟩ := hcover N τ hτ hτc
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZ d a hd hd' ha h hh sector rows hlower hnorm hsector habove hbelow
    width hw label
  have hZtwo : 2 ≤ Z := hZ₀.trans hZ
  have hZone : 1 ≤ Z := by linarith
  have hT : 0 ≤ Z ^ τ := Real.rpow_nonneg (by linarith) _
  have hcap : 0 ≤ (2 * a - 1) / 2 := by linarith
  obtain ⟨p, hp, hmax⟩ := exists_recipeAmplitude_sample K S P E.rows ω ψ g F
    width ((2 * a - 1) / 2) Z (Z ^ τ) hT rows label
  let sampled := recipeAmplitudeRows K S P E.rows ω ψ g F width ((2 * a - 1) / 2)
    Z rows p label
  have hsub : sampled ⊆ rows := recipeAmplitudeRows_subset K S P E.rows ω ψ g F
    width ((2 * a - 1) / 2) Z rows p label
  obtain ⟨A, _, hsectorA, hphysical, hamplitude, hrows, hgeometry, hwitness⟩ :=
    hdata Z hZ d a hd hd' ha h hh sector sampled
      (fun u hu => hlower u (hsub hu)) (fun u hu => hnorm u (hsub hu))
      (fun u hu => hsector u (hsub hu)) (fun u hu => habove u (hsub hu))
      (fun u hu => hbelow u (hsub hu)) p hp
      (fun j => decodeAmplitude width ((2 * a - 1) / 2) (label j))
  have hamp := recipeAmplitudeRows_amplitude_spec K S P E.rows ω ψ g F
    width ((2 * a - 1) / 2) Z rows p hw hcap (by linarith) label
  refine ⟨p, A, hp, hphysical, hsectorA, hamplitude, hrows, ?_, hgeometry, ?_, ?_, ?_⟩
  · intro q hq
    rw [hrows]
    exact hmax q hq
  · simpa only [hamplitude] using hamp.1
  · intro j hj u hu
    rw [hamplitude] at hj ⊢
    rw [hrows] at hu
    change _ ≤ ‖primePolynomial (F.slotModel K S P E.rows ω ψ g A.physical u.sector)
      j u.ideal.val Z 0‖
    rw [hphysical]
    exact hamp.2 j hj u hu
  · intro t ht ht'
    exact ((hwitness t ht ht').1).mono_loss
      (Real.one_le_rpow hZone (by linarith)) hk.le hinnerLam


/-- Assemble every actual amplitude label into one live-bin block.  The
block value is retained literally, so the physical integral identity can
be established separately without changing the constructed source data. -/
theorem exists_physical_live_block_source
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) (lam : ℝ) (hlam : 0 < lam) :
    ∃ e ε ceiling k : ℝ,
      0 < e ∧ e < 1 / 1000 ∧ e ≤ lam / 1000 ∧ 0 < ε ∧ 0 < ceiling ∧ 0 < k ∧
      ∀ N : ℕ, ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
        let F := scaledCanonicalRecipeFamily K ψ g cutoffProfile slotTime slotPower
          slotCoefficient (3 * ((N : ℝ) + 1))
        ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
          ∀ d a B : ℝ, 1 / 16 ≤ d → d ≤ 13 / 16 + lam → d ≤ 1 →
          51 / 100 ≤ a → a ≤ B → ∀ h : ℕ, h ≤ N →
          ∀ sector : SixthUnitClasses K S, ∀ rows : Finset (FrequencyRow K S),
            (∀ u ∈ rows, Z ^ d < frequencyRowNorm K S u) →
            (∀ u ∈ rows, frequencyRowNorm K S u ≤ 2 * Z ^ d) →
            (∀ u ∈ rows, u.sector = sector) →
            (∀ u ∈ rows, rowZeroAbove K S ψ {1} P E u
              (selectedHeight h (Z ^ τ)) a) →
            (∀ u ∈ rows, rowZeroBelow K S ψ {1} P E u
              (upperHeight h (Z ^ τ)) (a + 2 * e)) →
            ∀ width : ℝ, 0 < width → ∀ value : ℂ,
            ∃ b : RecipeBlockData K S ψ g F
              (Fintype.card (AmplitudeLabels g.slots width ((2 * a - 1) / 2))),
              b.bin = a ∧ b.value = value ∧
              BlockSource g (b.toBlock (P := P) (R := E.rows) (ω := ω)
                d Z (Z ^ τ)) B lam k Z ∧
              (∀ l, (b.amplitude l).MomentGeometry (Z ^ τ) 22) ∧
              (∀ l, (b.amplitude l).rows (Z ^ d) ⊆ rows) := by
  obtain ⟨e, ε, ceiling, k, he, heSmall, heLam, _, hε, hceiling, hk, hsource⟩ :=
    exists_physical_amplitude_source K S P ω ψ g E slotTime slotPower
      slotCoefficient hcomplex lam hlam lam hlam
  refine ⟨e, ε, ceiling, k, he, heSmall, heLam, hε, hceiling, hk, ?_⟩
  intro N τ hτ hτc
  dsimp only
  let F := scaledCanonicalRecipeFamily K ψ g cutoffProfile slotTime slotPower
    slotCoefficient (3 * ((N : ℝ) + 1))
  obtain ⟨Z₀, hZ₀, hdata⟩ := hsource N τ hτ hτc
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZ d a B hd hdUpper hdOne ha haB h hh sector rows hlower hnorm
    hsector habove hbelow width hw value
  let Labels := AmplitudeLabels g.slots width ((2 * a - 1) / 2)
  have hlabels := hdata Z hZ d a hd hdOne ha h hh sector rows
    hlower hnorm hsector habove hbelow width hw
  choose p A hp hphysical hsectorA hamplitude_eq hrows hmax hgeometry hamplitude hslots hwitness
    using hlabels
  let decode := (Fintype.equivFin Labels).symm
  let b : RecipeBlockData K S ψ g F (Fintype.card Labels) :=
    { bin := a
      value := value
      amplitude := fun l => A (decode l) }
  refine ⟨b, rfl, rfl, ?_, ?_, ?_⟩
  · refine ⟨by dsimp [b, RecipeBlockData.toBlock]; linarith,
      hdUpper, ha, haB, ?_⟩
    intro l
    exact ⟨hamplitude (decode l), hslots (decode l),
      fun _ t ht ht' => hwitness (decode l) t ht ht'⟩
  · intro l
    exact hgeometry (decode l)
  · intro l
    change (A (decode l)).rows (Z ^ d) ⊆ rows
    rw [hrows (decode l)]
    exact recipeAmplitudeRows_subset K S P E.rows ω ψ g F width ((2 * a - 1) / 2)
      Z rows (p (decode l)) (decode l)

/-- The common label bound is independent of the bin, scale, and height. -/
theorem exists_physical_live_block_source_uniform_labels
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
            ∃ b : RecipeBlockData K S ψ g F
              (fixedAmplitudeLabelCount g.slots width),
              b.bin = a ∧ b.value = value ∧
              BlockSource g (b.toBlock (P := P) (R := E.rows) (ω := ω)
                d Z (Z ^ τ)) B lam k Z ∧
              (∀ l, (b.amplitude l).MomentGeometry (Z ^ τ) 22) ∧
              (∀ l, (b.amplitude l).rows (Z ^ d) ⊆ rows) := by
  obtain ⟨e, ε, ceiling, k, he, heSmall, heLam, hε, hceiling, hk, hsource⟩ :=
    exists_physical_live_block_source K S P ω ψ g E slotTime slotPower
      slotCoefficient hcomplex lam hlam
  refine ⟨e, ε, ceiling, k, he, heSmall, heLam, hε, hceiling, hk, ?_⟩
  intro N τ hτ hτc
  dsimp only
  obtain ⟨Z₀, hZ₀, hdata⟩ := hsource N τ hτ hτc
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZ d a B hd hdUpper hdOne ha haB hB h hh sector rows hlower hnorm
    hsector habove hbelow width hw value
  obtain ⟨b, hbin, hvalue, hblock, hgeometry, hrows⟩ :=
    hdata Z hZ d a B hd hdUpper hdOne ha haB h hh sector rows hlower hnorm
      hsector habove hbelow width hw value
  have hn := amplitudeLabels_card_pos g.slots width ((2 * a - 1) / 2)
  have hN := amplitudeLabels_card_le_fixed g.slots hw
    (show (2 * a - 1) / 2 ≤ 1 / 2 by linarith)
  refine ⟨b.pad hn hN, hbin, hvalue, ?_, ?_, ?_⟩
  · exact b.pad_source hn hN d Z (Z ^ τ) B lam k hblock
  · exact b.pad_geometry hn hN (Z ^ τ) 22 hgeometry
  · intro l
    exact hrows (fixedLabelProjection hn l)

end Expansion.Project

#print axioms Expansion.Project.exists_recipeAmplitude_sample
#print axioms Expansion.Project.recipeAmplitudeRows_amplitude_spec
#print axioms Expansion.Project.exists_physical_amplitude_source

#print axioms Expansion.Project.exists_physical_live_block_source

#print axioms Expansion.Project.exists_physical_live_block_source_uniform_labels
