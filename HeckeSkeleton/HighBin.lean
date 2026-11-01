import HeckeSkeleton.Base
import HeckeSkeleton.Theta
import HeckeSkeleton.HighArithmeticInputs
import HeckeGeneral.Analysis.BufferedPhysicalRowBin
import HeckeGeneral.Analysis.RowEulerNegativeStrip
import HeckeGeneral.Characters.LocalConductor
import ExpansionInterfaces.BufferedHeights
import Expansion.ActualPhysicalRecipePresentation

/-!
Top-down obligations for revised Proposition 6.3(ii), printed pp.41–42,
and its single-bin consequence. This is an admitted skeleton, not a verified
transfer of Q's estimates. In particular no Part II restriction B ≤ 11/12
or δ ≤ 5/6 is inserted here.

`ActualHighPresentation` contains choices, exact identifications and support
properties only. All analytic bounds occur in separately named obligations.
Its named construction refines Base's named data constructors (especially
D-EXPANSION, D-ARITHMETIC, D-TESTS, D-MEASURES and D-RAY): one must identify the actual
full-correction amplitude, including selected slots, unselected slots and
zero masks. Choosing arbitrary row pieces satisfying only their sum identity
does NOT prove the later norm-form estimates.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]

abbrev HighRow (c : TargetContext K) :=
  FrequencyRow K ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))

abbrev HighBlockIndex (c : TargetContext K) (Z T : ℝ) :=
  Fin ((targetData K c).expansion Z T).blockCount

abbrev HighLabel (c : TargetContext K) (Z T : ℝ) (b : HighBlockIndex K c Z T) :=
  (((targetData K c).expansion Z T).block b).Label

local instance highNormOneMeasurable (c : TargetContext K) :
    MeasurableSpace (sLocalNormOneGroup K
      ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :=
  (targetData K c).measures.normOneSpace

local instance highNormOneBorel (c : TargetContext K) :
    BorelSpace (sLocalNormOneGroup K
      ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :=
  (targetData K c).measures.normOneBorel

local instance highLocalMeasurable (c : TargetContext K)
    (p : ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :
    MeasurableSpace (p.val.adicCompletion K) :=
  (targetData K c).measures.localSpace p

local instance highLocalBorel (c : TargetContext K)
    (p : ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :
    BorelSpace (p.val.adicCompletion K) :=
  (targetData K c).measures.localBorel p

local instance highLocalHaar (c : TargetContext K)
    (p : ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :
    ((targetData K c).measures.haar p).IsAddHaarMeasure :=
  (targetData K c).measures.haar_isAddHaar p

/-- The floor bin does not demand a selected zero. Live bins use the two
independent buffered detector heights, including the endpoint a=1. -/
def highFixedRowBin (c : TargetContext K)
    (P : ProbeData K ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K))))
    (E : RowEulerData K _ P) (Θ : Finset (HeckeCharacter K))
    (selectedHeight upperHeight normLower normUpper a e : ℝ) : Finset (HighRow K c) :=
  if a = 51 / 100 then
    (frequencyRows K _ normUpper).filter fun u =>
      normLower < frequencyRowNorm K _ u ∧ ¬ principalFrequencyRow K _ u ∧
        rowZeroBelow K _ (targetCharacter K c) Θ P E u upperHeight (a + 2 * e)
  else bufferedPhysicalRowBin K _ (targetCharacter K c) Θ P E
    selectedHeight upperHeight normLower normUpper a e

/-- Choices/identifications for the named actual expansion D-TARGET.
One finite buffered index determines the selected and upper-zero heights;
the contour height is the physical integration cutoff T. The arithmetic
row selector is fixed before the Mellin variables and is a subset of the
wider zero-control bin. Labels may overlap as row sets. Their pieces are
transported actual row contributions: a sampled receiving row need not
carry its own original kernel. The transport preserves the exact sum. -/
structure ActualHighPresentation (c : TargetContext K) : Type 1 where
  e : ℝ
  e_pos : 0 < e
  e_small : e ≤ min c.family.lamA c.lamB / 100
  euler : RowEulerData K
    ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K))) (targetData K c).probe
  companions : Finset (HeckeCharacter K)
  heightCount : ℕ
  heightIndex : ∀ Z T : ℝ, HighBlockIndex K c Z T → Fin (heightCount + 1)
  fixedRows : ∀ Z T : ℝ, HighBlockIndex K c Z T → Finset (HighRow K c)
  labels : ∀ Z T : ℝ, (b : HighBlockIndex K c Z T) → Finset (HighLabel K c Z T b)
  shiftedPiece : ∀ Z T : ℝ, (b : HighBlockIndex K c Z T) →
    HighLabel K c Z T b → HighRow K c → ℂ
  bin_range : ∀ Z T : ℝ, 1 ≤ Z → 1 ≤ T → ∀ b : HighBlockIndex K c Z T,
    51 / 100 ≤ (((targetData K c).expansion Z T).block b).bin ∧
      (((targetData K c).expansion Z T).block b).bin ≤ c.family.B
  fixedRows_in_bin : ∀ Z T : ℝ, 1 ≤ Z → 1 ≤ T → ∀ b : HighBlockIndex K c Z T,
    fixedRows Z T b ⊆
      highFixedRowBin K c (targetData K c).probe euler companions
        (3 * ((heightIndex Z T b).val + 1 : ℝ) * T)
        (3 * ((heightIndex Z T b).val + 2 : ℝ) * T)
        (Z ^ (((targetData K c).expansion Z T).block b).shell)
        (2 * Z ^ (((targetData K c).expansion Z T).block b).shell)
        (((targetData K c).expansion Z T).block b).bin e
  rows_in_fixedRows : ∀ Z T : ℝ, 1 ≤ Z → 1 ≤ T → ∀ b : HighBlockIndex K c Z T,
    ∀ ℓ : HighLabel K c Z T b,
      ((((targetData K c).expansion Z T).block b).amplitudeSet ℓ).rows ⊆ fixedRows Z T b
  block_identification : ∀ Z T : ℝ, 1 ≤ Z → 1 ≤ T →
    ∀ b : HighBlockIndex K c Z T,
      (((targetData K c).expansion Z T).block b).value =
        ∑ ℓ ∈ labels Z T b,
          ∑ u ∈ ((((targetData K c).expansion Z T).block b).amplitudeSet ℓ).rows,
            shiftedPiece Z T b ℓ u
  shifted_identification : ∀ Z T : ℝ, 1 ≤ Z → 1 ≤ T →
    ∀ b : HighBlockIndex K c Z T,
      (∑ ℓ ∈ labels Z T b,
        ∑ u ∈ ((((targetData K c).expansion Z T).block b).amplitudeSet ℓ).rows,
          shiftedPiece Z T b ℓ u) =
        ∑ u ∈ fixedRows Z T b,
          rowContourBox K _ (targetData K c).measures.haar (targetData K c).probe
            (targetCharacter K c) euler c.geometry (targetData K c).rayFilter u
            Z T
            ((((targetData K c).expansion Z T).block b).bin + 16 * e)
            (1 - (((targetData K c).expansion Z T).block b).bin - 6 * e) (17 / 50)

namespace ActualHighPresentation

variable {K} {c : TargetContext K}

/-- The same fixed allowance used by the actual raw shell schedule. -/
def zeta (_P : ActualHighPresentation K c) : ℝ := expansionShellAllowance K c

theorem zeta_pos (P : ActualHighPresentation K c) : 0 < P.zeta :=
  (ExpansionInterfaces.shellAllowance_spec c.family.lamA_pos).1

theorem zeta_small (P : ActualHighPresentation K c) : P.zeta < 1 / 48 :=
  (ExpansionInterfaces.shellAllowance_spec c.family.lamA_pos).2.1

theorem zeta_le_lamA (P : ActualHighPresentation K c) : P.zeta ≤ c.family.lamA :=
  (ExpansionInterfaces.shellAllowance_spec c.family.lamA_pos).2.2

/-- The actual block index determines its shell. This range is derived
from the common schedule, rather than stored as presentation data. -/
theorem shell_range (P : ActualHighPresentation K c)
    (Z T : ℝ) (_hZ : 1 ≤ Z) (_hT : 1 ≤ T) (b : HighBlockIndex K c Z T) :
    1 / 16 ≤ (((targetData K c).expansion Z T).block b).shell ∧
      (((targetData K c).expansion Z T).block b).shell ≤ 13 / 16 + P.zeta := by
  have h := highExpansion_shell_range K c Z T b
  exact ⟨h.1, h.2.le⟩

/-- The physical coordinate cutoff used by `rowContourBox`. -/
def contourHeight (_P : ActualHighPresentation K c) (_Z T : ℝ)
    (_b : HighBlockIndex K c _Z T) : ℝ := T

def selectedHeight (P : ActualHighPresentation K c) (Z T : ℝ)
    (b : HighBlockIndex K c Z T) : ℝ :=
  3 * ((P.heightIndex Z T b).val + 1 : ℝ) * T

def upperHeight (P : ActualHighPresentation K c) (Z T : ℝ)
    (b : HighBlockIndex K c Z T) : ℝ :=
  3 * ((P.heightIndex Z T b).val + 2 : ℝ) * T

/-- The finite index is fixed independently of the later scale and height. -/
theorem heights_uniform (P : ActualHighPresentation K c) (Z T : ℝ)
    (hT : 0 ≤ T) (b : HighBlockIndex K c Z T) :
    0 ≤ P.contourHeight Z T b ∧ 0 ≤ P.selectedHeight Z T b ∧
    0 ≤ P.upperHeight Z T b ∧
    P.contourHeight Z T b ≤ 3 * (P.heightCount + 2 : ℝ) * (1 + T) ∧
    P.selectedHeight Z T b ≤ 3 * (P.heightCount + 2 : ℝ) * (1 + T) ∧
    P.upperHeight Z T b ≤ 3 * (P.heightCount + 2 : ℝ) * (1 + T) := by
  have hi : (P.heightIndex Z T b).val ≤ P.heightCount :=
    Nat.lt_succ_iff.mp (P.heightIndex Z T b).isLt
  have hi' : ((P.heightIndex Z T b).val : ℝ) ≤ P.heightCount := by exact_mod_cast hi
  have hn : (0 : ℝ) ≤ P.heightCount := Nat.cast_nonneg _
  have hi0 : (0 : ℝ) ≤ (P.heightIndex Z T b).val := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_right hi' hT
  dsimp only [contourHeight, selectedHeight, upperHeight]
  refine ⟨hT, by positivity, by positivity, ?_, ?_, ?_⟩ <;> nlinarith

/-- All labels, including inactive labels, inherit the fixed arithmetic support. -/
theorem rows_in_bin (P : ActualHighPresentation K c)
    (Z T : ℝ) (hZ : 1 ≤ Z) (hT : 1 ≤ T) (b : HighBlockIndex K c Z T)
    (ℓ : HighLabel K c Z T b) :
    ((((targetData K c).expansion Z T).block b).amplitudeSet ℓ).rows ⊆
      highFixedRowBin K c (targetData K c).probe P.euler P.companions
        (P.selectedHeight Z T b) (P.upperHeight Z T b)
        (Z ^ (((targetData K c).expansion Z T).block b).shell)
        (2 * Z ^ (((targetData K c).expansion Z T).block b).shell)
        (((targetData K c).expansion Z T).block b).bin P.e :=
  (P.rows_in_fixedRows Z T hZ hT b ℓ).trans (P.fixedRows_in_bin Z T hZ hT b)

end ActualHighPresentation

section PhysicalPresentationConstructor

open Expansion.Project ExpansionInterfaces
open HeckeGeneral.ThetaSkeleton.Global

attribute [local instance] Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar
  expansionNormOneSpace expansionNormOneBorel

variable (c : TargetContext K)

local instance actualPresentation_sectorFintype :
    Fintype (SixthUnitClasses K (places K c)) := Fintype.ofFinite _

local notation "q" => expansionPhysicalParameters K c
local notation "Eactual" => HighBinActualEuler.arithmeticHighEulerData K (places K c)
  (probeData K c) (targetCharacter K c)

/-- Decode the original raw block index; no second shell choice is made. -/
def expansionScheduledShell (Z T : ℝ) (b : HighBlockIndex K c Z T) :
    Fin (shellCount Z (1 / 16) (13 / 16 + expansionShellAllowance K c)) :=
  physicalRecipeShellIndex K (places K c) c.family.B (q).e (expansionShellAllowance K c) Z
    ((expansionRecipeRaw K c).rawBlockIndex Z T b)

/-- The buffered height/bin and sector of that same raw block. -/
def expansionScheduledChoice (Z T : ℝ) (b : HighBlockIndex K c Z T) :
    PhysicalRecipeChoice K (places K c) c.family.B (q).e :=
  physicalRecipeChoice K (places K c) c.family.B (q).e (expansionShellAllowance K c) Z
    ((expansionRecipeRaw K c).rawBlockIndex Z T b)

/-- The actual clipped, selected arithmetic rows of the original block. -/
def expansionFixedRows (Z T : ℝ) (b : HighBlockIndex K c Z T) : Finset (HighRow K c) :=
  physicalRecipeRows K (places K c) (probeData K c) Eactual c.family.omega
    (targetCharacter K c) (representative K c).val.property (expansionBoundary_lower K c)
    c.family.B_upper (q).e_pos c.family.boundary (expansionShellAllowance K c) Z T
    (expansionScheduledShell K c Z T b) (expansionScheduledChoice K c Z T b)

/-- Exactly the original amplitude alphabet inside the fixed finite one. -/
def expansionRetainedLabels (Z T : ℝ) (b : HighBlockIndex K c Z T) :
    Finset (HighLabel K c Z T b) :=
  physicalRecipeRetainedLabels K (places K c) (expansionBoundary_lower K c)
    c.family.B_upper (q).e_pos c.geometry (q).width (q).width_pos
    (expansionScheduledChoice K c Z T b)

/-- The genuine finite-pattern transport of the original compensated kernel. -/
def expansionShiftedPiece (Z T : ℝ) (b : HighBlockIndex K c Z T)
    (l : HighLabel K c Z T b) (u : HighRow K c) : ℂ :=
  physicalRecipeShiftedPiece K (places K c) (probeData K c) Eactual c.family.omega
    (targetCharacter K c) (representative K c).val.property (expansionBoundary_lower K c)
    c.family.B_upper (q).e_pos c.family.boundary c.geometry (probeMeasures K c).haar ∅
    c.family.lamA (expansionShellAllowance K c) (q).width (q).k (q).width_pos Z T
    (expansionScheduledShell K c Z T b) (expansionScheduledChoice K c Z T b) l u

theorem expansionScheduled_scale (Z T : ℝ) (b : HighBlockIndex K c Z T) :
    1 < Z ∧ 0 ≤ T := by
  have hs := highExpansion_scale_of_block K c Z T b
  exact ⟨(by norm_num : (1 : ℝ) < 2 ^ (16 : ℕ)).trans_le hs.1,
    zero_le_one.trans hs.2⟩

theorem expansionScheduled_bin (Z T : ℝ) (b : HighBlockIndex K c Z T) :
    (((targetData K c).expansion Z T).block b).bin =
      (expansionScheduledChoice K c Z T b).1.center := by
  letI : ∀ p : places K c, MeasurableSpace (p.val.adicCompletion K) :=
    (probeMeasures K c).localSpace
  letI : ∀ p : places K c, BorelSpace (p.val.adicCompletion K) :=
    (probeMeasures K c).localBorel
  letI : ∀ p : places K c, ((probeMeasures K c).haar p).IsAddHaarMeasure :=
    (probeMeasures K c).haar_isAddHaar
  exact physicalRecipeScheduledBlock_bin K (places K c) (probeData K c) Eactual c.family.omega
    (targetCharacter K c) (representative K c).val.property (expansionBoundary_lower K c)
    c.family.B_upper (q).e_pos c.family.boundary c.geometry (probeMeasures K c).haar ∅
    c.family.lamA (expansionShellAllowance K c) (q).width (q).k (q).width_pos Z T
    (expansionScheduledShell K c Z T b) (expansionScheduledChoice K c Z T b)

theorem expansionScheduled_shell (Z T : ℝ) (b : HighBlockIndex K c Z T) :
    (((targetData K c).expansion Z T).block b).shell =
      shellExponent Z (1 / 16) (expansionScheduledShell K c Z T b).val := rfl

-- HB-PRESENT | revised Prop.6.3, pp.41–42; §7.1 pp.43–44.
-- Every field is read from the original physical recipe.  Its transported
-- pieces integrate the actual kernel, including on the default source
-- branch.  Original-minus-final fixed-bin boundaries are handled before
-- the amplitude partition, in the actual expansion tail.
def actualHighPresentation : ActualHighPresentation K c := by
  letI : IsTotallyComplex K := Expansion.ActualProbeContext.totallyComplex K (axiomChoice K c)
  letI : ∀ p : places K c, MeasurableSpace (p.val.adicCompletion K) :=
    (probeMeasures K c).localSpace
  letI : ∀ p : places K c, BorelSpace (p.val.adicCompletion K) :=
    (probeMeasures K c).localBorel
  letI : ∀ p : places K c, ((probeMeasures K c).haar p).IsAddHaarMeasure :=
    (probeMeasures K c).haar_isAddHaar
  have hAllowed : AllowedGeneratorInput K (places K c) (probeData K c).arithmetic :=
    Expansion.ActualProbeContext.allowedGenerators K (axiomChoice K c)
  refine
    { e := (q).e
      e_pos := (q).e_pos
      e_small := expansionPhysicalParameters_e_losses K c
      euler := Eactual
      companions := {1}
      heightCount := physicalRecipeHeightBound c.family.B (q).e
      heightIndex := fun Z T b => physicalRecipePresentationHeightIndex K (places K c)
        c.family.B (q).e (expansionScheduledChoice K c Z T b)
      fixedRows := expansionFixedRows K c
      labels := expansionRetainedLabels K c
      shiftedPiece := expansionShiftedPiece K c
      bin_range := ?_
      fixedRows_in_bin := ?_
      rows_in_fixedRows := ?_
      block_identification := ?_
      shifted_identification := ?_ }
  · intro Z T _hZ _hT b
    exact physicalRecipeScheduledBlock_bin_range K (places K c) (probeData K c) Eactual
      c.family.omega (targetCharacter K c) (representative K c).val.property
      (expansionBoundary_lower K c) c.family.B_upper (q).e_pos c.family.boundary
      c.geometry (probeMeasures K c).haar ∅ c.family.lamA (expansionShellAllowance K c)
      (q).width (q).k (q).width_pos Z T
      (expansionScheduledShell K c Z T b) (expansionScheduledChoice K c Z T b)
  · intro Z T _hZ _hT b
    rw [expansionScheduled_bin, expansionScheduled_shell]
    exact physicalRecipeRows_in_bin K (places K c) (probeData K c) Eactual c.family.omega
      (targetCharacter K c) (representative K c).val.property (expansionBoundary_lower K c)
      c.family.B_upper (q).e_pos c.family.boundary (expansionShellAllowance K c) Z T
      (expansionScheduled_scale K c Z T b).1
      (expansionScheduledShell K c Z T b) (expansionScheduledChoice K c Z T b)
  · intro Z T _hZ _hT b l
    exact physicalRecipeScheduledBlock_rows_subset K (places K c) (probeData K c)
      c.family.omega (targetCharacter K c) c.geometry Eactual
      (representative K c).val.property (expansionBoundary_lower K c) c.family.B_upper
      (q).e_pos c.family.boundary (probeMeasures K c).haar ∅ c.family.lamA
      (expansionShellAllowance K c) (q).width (q).k (q).width_pos Z T
      (expansionScheduled_scale K c Z T b).1 (expansionScheduled_scale K c Z T b).2
      (expansionScheduledShell K c Z T b) (expansionScheduledChoice K c Z T b) l
  · intro Z T _hZ _hT b
    exact actual_physicalRecipeScheduledBlock_identification K (excludedPlaces K c)
      (Expansion.ActualProbeContext.allLocalMeasures K)
      (Expansion.ActualProbeContext.finiteAdeleMeasure K) (probeData K c) c.family.omega
      (targetCharacter K c) hAllowed c.geometry ∅ (representative K c).val.property
      (expansionBoundary_lower K c) c.family.B_upper (q).e_pos
      (expansionPhysicalParameters_e_sweep K c) c.family.boundary c.family.lamA
      (expansionShellAllowance K c) (q).width (q).k (q).width_pos Z T
      (expansionScheduled_scale K c Z T b).1 (expansionScheduled_scale K c Z T b).2
      (expansionScheduledShell K c Z T b) (expansionScheduledChoice K c Z T b)
  · intro Z T _hZ _hT b
    rw [expansionScheduled_bin]
    exact actual_physicalRecipeShiftedPiece_sum K (excludedPlaces K c)
      (Expansion.ActualProbeContext.allLocalMeasures K)
      (Expansion.ActualProbeContext.finiteAdeleMeasure K) (probeData K c) c.family.omega
      (targetCharacter K c) hAllowed c.geometry ∅ (representative K c).val.property
      (expansionBoundary_lower K c) c.family.B_upper (q).e_pos
      (expansionPhysicalParameters_e_sweep K c) c.family.boundary c.family.lamA
      (expansionShellAllowance K c) (q).width (q).k (q).width_pos Z T
      (expansionScheduled_scale K c Z T b).1 (expansionScheduled_scale K c Z T b).2
      (expansionScheduledShell K c Z T b) (expansionScheduledChoice K c Z T b)

end PhysicalPresentationConstructor

#print axioms actualHighPresentation

/-- The full factor at an exceptional prime uses its finite rational table;
there is no division by a possibly zero Gauss polynomial. -/
def highEulerFactor (c : TargetContext K) (P : ActualHighPresentation K c)
    (Q : Finset (ExteriorPrime K ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))))
    (u : HighRow K c)
    (p : ExteriorPrime K ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K))))
    (s w z : ℂ) : ℂ :=
  if hp : p ∈ rowExceptionalPrimes K _ Q u then
    finiteEulerRationalValue (P.euler.exceptionalFactor Q u ⟨p, hp⟩)
      (p.val.asIdeal.absNorm : ℝ) s w z
  else localRowCorrection K _ (targetData K c).probe (targetCharacter K c)
    (P.euler.rows.character u) p s w z

/-- The actual nonexceptional branch has uniform Euler decay throughout
the bin range, including zero and negative real parts of w. The finite
exceptional tables and the open-domain calibration remain separate work. -/
theorem highEulerFactor_regular_bound (c : TargetContext K)
    (P : ActualHighPresentation K c) (Z T : ℝ) (hZ : 1 ≤ Z) (hT : 1 ≤ T)
    (b : HighBlockIndex K c Z T)
    (Q : Finset (ExteriorPrime K ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))))
    (u : HighRow K c)
    (p : ExteriorPrime K ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K))))
    (hp : p ∉ rowExceptionalPrimes K _ Q u) (s w z : ℂ)
    (hs : s.re = (((targetData K c).expansion Z T).block b).bin + 16 * P.e)
    (hw : w.re = 1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e)
    (hz : z.re = 17 / 50) :
    ‖highEulerFactor K c P Q u p s w z - 1‖ ≤
      (11 / negativeStripEulerMargin) *
        (p.val.asIdeal.absNorm : ℝ) ^ (-1 - 10 * P.e) := by
  have hbin := P.bin_range Z T hZ hT b
  have habin : (((targetData K c).expansion Z T).block b).bin ≤ 1 :=
    hbin.2.trans c.family.B_upper
  have he : P.e ≤ 1 / 10000 := by
    have hmin : min c.family.lamA c.lamB ≤ c.family.lamA :=
      min_le_left _ _
    have hsmall := P.e_small
    have hlam := c.family.lamA_small
    linarith
  simpa only [highEulerFactor, dif_neg hp] using
    (localRowCorrection_negativeStrip_bound K _ (targetData K c).probe
      (targetCharacter K c) (P.euler.rows.character u) p
      hbin.1 habin P.e_pos.le he s w z hs hw hz)

/-- Actual open-domain calibration plus the dynamic-contour Euler error.
The older positive-w region alone does not cover a=1, where w=-6e. -/
def FullHighEulerControl (c : TargetContext K) (P : ActualHighPresentation K c) : Prop :=
  TRowEulerInput K _ (targetData K c).probe (targetCharacter K c) P.euler ∧
  ∃ C cutoff : ℝ, 0 < C ∧ 1 ≤ cutoff ∧
    ∀ Z T : ℝ, 1 ≤ Z → 1 ≤ T → ∀ b : HighBlockIndex K c Z T,
    ∀ Q : Finset (ExteriorPrime K ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))),
    ∀ u ∈ highFixedRowBin K c (targetData K c).probe P.euler P.companions (P.selectedHeight Z T b) (P.upperHeight Z T b)
      (Z ^ (((targetData K c).expansion Z T).block b).shell)
      (2 * Z ^ (((targetData K c).expansion Z T).block b).shell)
      (((targetData K c).expansion Z T).block b).bin P.e,
    ∀ p : ExteriorPrime K ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K))),
      p ∉ Q → cutoff ≤ (p.val.asIdeal.absNorm : ℝ) → ∀ s w z : ℂ,
      s.re = (((targetData K c).expansion Z T).block b).bin + 16 * P.e →
      w.re = 1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e →
      z.re = 17 / 50 →
      ‖highEulerFactor K c P Q u p s w z - 1‖ ≤
        C * (p.val.asIdeal.absNorm : ℝ) ^
          (if p.val.asIdeal ∣ u.ideal.val.val then -10 * P.e else -1 - 10 * P.e)

/-- The remaining Euler estimate concerns only the actual finite rational
tables at exceptional row primes outside Q. The regular-prime estimate is
already a theorem and is not a field of this proposition. -/
def HighExceptionalEulerControl (c : TargetContext K)
    (P : ActualHighPresentation K c) : Prop :=
  ∃ C cutoff : ℝ, 0 < C ∧ 1 ≤ cutoff ∧
    ∀ Z T : ℝ, 1 ≤ Z → 1 ≤ T → ∀ b : HighBlockIndex K c Z T,
    ∀ Q : Finset (ExteriorPrime K ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))),
    ∀ u ∈ highFixedRowBin K c (targetData K c).probe P.euler P.companions
      (P.selectedHeight Z T b) (P.upperHeight Z T b)
      (Z ^ (((targetData K c).expansion Z T).block b).shell)
      (2 * Z ^ (((targetData K c).expansion Z T).block b).shell)
      (((targetData K c).expansion Z T).block b).bin P.e,
    ∀ p : ExteriorPrime K ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K))),
    ∀ hp : p ∈ rowExceptionalPrimes K _ Q u,
      p ∉ Q → cutoff ≤ (p.val.asIdeal.absNorm : ℝ) → ∀ s w z : ℂ,
      s.re = (((targetData K c).expansion Z T).block b).bin + 16 * P.e →
      w.re = 1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e →
      z.re = 17 / 50 →
      ‖finiteEulerRationalValue (P.euler.exceptionalFactor Q u ⟨p, hp⟩)
          (p.val.asIdeal.absNorm : ℝ) s w z - 1‖ ≤
        C * (p.val.asIdeal.absNorm : ℝ) ^
          (if p.val.asIdeal ∣ u.ideal.val.val then -10 * P.e else -1 - 10 * P.e)

-- OBLIGATION HB-EULER-INITIAL | revised (6.10), Prop.6.3 pp.38–42.
-- Identify the actual four-ideal row Fourier series with the actual Euler
-- continuation on its initial open absolute-convergence domain.
theorem highInitialEulerControl (c : TargetContext K) :
    TRowEulerInput K _ (targetData K c).probe (targetCharacter K c)
      (actualHighPresentation K c).euler := by
  sorry

-- OBLIGATION HB-EULER-EXCEPTIONAL | revised (6.13), Prop.6.3 pp.38–42.
-- Prove a uniform constant and cutoff for the actual finite rational tables
-- at exceptional row primes outside Q. No regular-prime error is assumed.
theorem highExceptionalEulerControl (c : TargetContext K) :
    HighExceptionalEulerControl K c (actualHighPresentation K c) := by
  sorry

/-- The full Euler interface is assembled from its initial calibration,
the remaining exceptional-table estimate, and the proved regular estimate.
The maximum chooses one uniform constant for both kinds of primes. -/
theorem fullHighEulerControl_of_initial_exceptional (c : TargetContext K)
    (P : ActualHighPresentation K c)
    (hinit : TRowEulerInput K _ (targetData K c).probe (targetCharacter K c) P.euler)
    (hexceptional : HighExceptionalEulerControl K c P) :
    FullHighEulerControl K c P := by
  obtain ⟨C, cutoff, hC, hcutoff, hexceptional⟩ := hexceptional
  let C₀ : ℝ := 11 / negativeStripEulerMargin
  have hC₀ : 0 < C₀ := div_pos (by norm_num) negativeStripEulerMargin_pos
  refine ⟨hinit, max C C₀, cutoff, lt_of_lt_of_le hC (le_max_left _ _), hcutoff, ?_⟩
  intro Z T hZ hT b Q u hu p hpQ hcutoffp s w z hs hw hz
  let q : ℝ := (p.val.asIdeal.absNorm : ℝ)
  let β : ℝ := if p.val.asIdeal ∣ u.ideal.val.val then -10 * P.e else -1 - 10 * P.e
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  have hpow : 0 ≤ q ^ β := Real.rpow_nonneg hq0 _
  by_cases hp : p ∈ rowExceptionalPrimes K _ Q u
  · have htable := hexceptional Z T hZ hT b Q u hu p hp hpQ hcutoffp s w z hs hw hz
    have hfactor : ‖highEulerFactor K c P Q u p s w z - 1‖ ≤ C * q ^ β := by
      simpa only [highEulerFactor, dif_pos hp] using htable
    exact hfactor.trans (mul_le_mul_of_nonneg_right (le_max_left C C₀) hpow)
  · have hregular := highEulerFactor_regular_bound K c P Z T hZ hT b Q u p hp
      s w z hs hw hz
    have hq1 : 1 ≤ q := by
      have h : 1 < p.val.asIdeal.absNorm := one_lt_primeIdeal_absNorm K p.val
      change (1 : ℝ) ≤ (p.val.asIdeal.absNorm : ℝ)
      exact_mod_cast h.le
    have hexponent : -1 - 10 * P.e ≤ β := by
      dsimp only [β]
      split_ifs <;> linarith
    calc
      ‖highEulerFactor K c P Q u p s w z - 1‖ ≤ C₀ * q ^ (-1 - 10 * P.e) := hregular
      _ ≤ C₀ * q ^ β := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hq1 hexponent) hC₀.le
      _ ≤ max C C₀ * q ^ β := mul_le_mul_of_nonneg_right (le_max_right C C₀) hpow

-- OBLIGATION HB-EULER | revised (6.10),(6.13), Prop.6.3 pp.38–42.
-- The full statement is unchanged. The two remaining Euler-specific
-- obligations are the initial calibration and exceptional finite-table
-- estimate above; upstream actual-presentation obligations still remain.
theorem fullHighEulerControl (c : TargetContext K) :
    FullHighEulerControl K c (actualHighPresentation K c) := by
  exact fullHighEulerControl_of_initial_exceptional K c (actualHighPresentation K c)
    (highInitialEulerControl K c) (highExceptionalEulerControl K c)

def HighPureNormPoleExclusion (c : TargetContext K) (P : ActualHighPresentation K c) : Prop :=
  ∀ u : HighRow K c, ¬ principalFrequencyRow K _ u →
    ∀ t : ℝ, P.euler.rows.character u ≠ heckeNormTwist K t

-- OBLIGATION HB-POLE | revised §6.3–6.6 pp.38–42, §4 live background.
-- Original coefficient calibration identifies the whole actual Kummer
-- character. Its proved faithfulness detects the principal row, including
-- the unit-ideal sectors; the original allowed-generator fields are retained.
theorem highPureNormPoleExclusion (c : TargetContext K) :
    HighPureNormPoleExclusion K c (actualHighPresentation K c) := by
  intro u hu t
  exact HeckeGeneral.ThetaSkeleton.Physical.rowCharacterInput_ne_normTwist_of_not_principal
    K (places K c) (probeData K c) (actualHighPresentation K c).euler.rows
    (allowedGenerators K c) u hu t

def HighConductorDeficit (c : TargetContext K) (P : ActualHighPresentation K c) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ u : HighRow K c,
    ((finiteConductor K (P.euler.rows.character u)).val.absNorm : ℝ) ≤
      C * (u.ideal.val.val.radical.absNorm : ℝ)

-- OBLIGATION HB-CONDUCTOR | revised Prop.6.3 proof p.41.
-- The actual Kummer conductor bound and proved whole-character
-- identification supply one fixed S constant for every original row provider.
-- No character-identification or conductor bound is added as a premise.
theorem highConductorDeficit (c : TargetContext K) :
    HighConductorDeficit K c (actualHighPresentation K c) := by
  change HeckeGeneral.ThetaSkeleton.Physical.ActualConductorTransfer.HighRadicalBound K
    ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))
    (targetData K c).probe (actualHighPresentation K c).euler
  exact ActualCanonicalRowConsumers.highRadicalBound_for_every_provider K _
    (targetData K c).probe (actualHighPresentation K c).euler

def HighLabelUniformity (c : TargetContext K) (P : ActualHighPresentation K c) : Prop :=
  ∃ A C ceiling Z₀ : ℝ, 0 ≤ A ∧ 0 < C ∧ 0 < ceiling ∧ 1 ≤ Z₀ ∧
    ∀ Z T : ℝ, Z₀ ≤ Z → 1 ≤ T → T ≤ Z ^ ceiling →
      ∀ b : HighBlockIndex K c Z T,
        ((P.labels Z T b).card : ℝ) ≤ C * Z ^ (c.lamB / 4) * (1 + T) ^ A

-- OBLIGATION HB-LABEL-HEIGHT | revised Prop.6.3 pp.41–42, §7.1 p.43.
-- The single recipe uses one fixed finite label type before Z, T and τ.
-- Cardinality follows from that actual definition. The three height bounds
-- are the separate theorem `ActualHighPresentation.heights_uniform` above.
-- The construction of the raw expansion and actual presentation remains
-- D-EXPANSION/HB-PRESENT; no analytic norm-form estimate is asserted here.
theorem highLabelUniformity (c : TargetContext K) :
    HighLabelUniformity K c (actualHighPresentation K c) := by
  let N : ℕ := (expansionRecipeRaw K c).labelCount
  refine ⟨0, (N : ℝ) + 1, 1, 1, le_rfl, by positivity, zero_lt_one, le_rfl, ?_⟩
  intro Z T hZ _hT _hceiling b
  have hcard : ((actualHighPresentation K c).labels Z T b).card ≤ N := by
    exact card_finset_fin_le
      (((actualHighPresentation K c).labels Z T b) : Finset (Fin N))
  have hcard' : (((actualHighPresentation K c).labels Z T b).card : ℝ) ≤ N := by
    exact_mod_cast hcard
  have hp : 1 ≤ Z ^ (c.lamB / 4) :=
    Real.one_le_rpow hZ (by linarith [c.lamB_pos])
  simpa only [Real.rpow_zero, mul_one] using
    hcard'.trans ((by linarith : (N : ℝ) ≤ N + 1).trans
      (le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ N + 1) hp))

/-- Row-cardinality-free exponent. The later count contributes exactly dR. -/
def highRowExponent (c : TargetContext K) (Z T : ℝ)
    (b : HighBlockIndex K c Z T) (ℓ : HighLabel K c Z T b) : ℝ :=
  3 / 16 + moderateExponent
    (((targetData K c).expansion Z T).block b).shell
    (2 * (((targetData K c).expansion Z T).block b).bin - 1)
    ((((targetData K c).expansion Z T).block b).amplitudeSet ℓ).mean 0

theorem moderateExponent_count_identity (d δ q R : ℝ) :
    moderateExponent d δ q R = moderateExponent d δ q 0 + d * R := by
  unfold moderateExponent
  ring

/-- The norm-form bound for the actual shifted contribution, before inserting
any row count. The mean is the full correction's amplitude, not its unmarked
part; q/6 in moderateExponent is a power of Z, not a power of U. -/
def HighShiftedNormForm (c : TargetContext K) (P : ActualHighPresentation K c) : Prop :=
  ∃ A C ceiling Z₀ : ℝ, 0 ≤ A ∧ 0 < C ∧ 0 < ceiling ∧ 1 ≤ Z₀ ∧
    ∀ Z T : ℝ, Z₀ ≤ Z → 1 ≤ T → T ≤ Z ^ ceiling →
    ∀ b : HighBlockIndex K c Z T, ∀ ℓ ∈ P.labels Z T b,
      (∑ u ∈ ((((targetData K c).expansion Z T).block b).amplitudeSet ℓ).rows,
        ‖P.shiftedPiece Z T b ℓ u‖) ≤
      C * (((((targetData K c).expansion Z T).block b).amplitudeSet ℓ).rows.card : ℝ) *
        Z ^ (highRowExponent K c Z T b ℓ + c.lamB / 4) * (1 + T) ^ A

-- OBLIGATION HB-NORMFORM | revised (6.24), Prop.6.3 pp.41–42; Q(20.4).
-- Actual contour integrals + full correction + fixed-type gamma seminorms
-- must give this estimate for all a≤B≤1, including a=1. No row count or
-- final highBin estimate is assumed. Dependencies are deliberately explicit.
theorem highShiftedNormForm (c : TargetContext K)
    (hEuler : FullHighEulerControl K c (actualHighPresentation K c))
    (hPole : HighPureNormPoleExclusion K c (actualHighPresentation K c))
    (hCond : HighConductorDeficit K c (actualHighPresentation K c)) :
    HighShiftedNormForm K c (actualHighPresentation K c) := by
  sorry

/-- Whole fixed-bin boundary, summed over the actual retained block family.
The subtraction is between actual initial and final fixed-bin row contours;
no moving amplitude label occurs in this definition. -/
def wholeBinBoundary (c : TargetContext K) (P : ActualHighPresentation K c)
    (Z T : ℝ) : ℂ :=
  ∑ b : HighBlockIndex K c Z T,
    ((∑ u ∈ P.fixedRows Z T b,
      rowContourBox K _ (targetData K c).measures.haar (targetData K c).probe
        (targetCharacter K c) P.euler c.geometry (targetData K c).rayFilter u
        Z (P.contourHeight Z T b) (c.family.B + 20 * P.e)
        (1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e) (17 / 50)) -
    (∑ u ∈ P.fixedRows Z T b,
      rowContourBox K _ (targetData K c).measures.haar (targetData K c).probe
        (targetCharacter K c) P.euler c.geometry (targetData K c).rayFilter u
        Z (P.contourHeight Z T b)
        ((((targetData K c).expansion Z T).block b).bin + 16 * P.e)
        (1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e) (17 / 50)))

/-- Arbitrary external tail orders, in the existing formal height-tail sense.
The expansion identity must include this SAME whole-bin boundary in its tail. -/
def HighBoundaryControl (c : TargetContext K) (P : ActualHighPresentation K c) : Prop :=
  PowerHeightTailBound (wholeBinBoundary K c P)

-- OBLIGATION HB-MOVE-BOUNDARY | revised Prop.6.3 pp.41–42, especially final
-- paragraph p.42: initial s=B+20e, w=1-a-6e; margin ≥14e, final margin10e.
-- Existing BufferedFixedBinContour only defines the final fixed-bin integral.
-- One must supply the actual move, horizontal faces and tail uniformity;
-- neither TRowEulerInput nor the bin's zero inequalities prove them alone.
theorem highBoundaryControl (c : TargetContext K)
    (hEuler : FullHighEulerControl K c (actualHighPresentation K c))
    (hPole : HighPureNormPoleExclusion K c (actualHighPresentation K c))
    (hCond : HighConductorDeficit K c (actualHighPresentation K c))
    (hLabels : HighLabelUniformity K c (actualHighPresentation K c)) :
    HighBoundaryControl K c (actualHighPresentation K c) := by
  sorry

/-- Boundary consumer for Expansion.EX-TAIL, deliberately separate from
highBin: independent saving is not forced into an arbitrary Ebar budget. -/
theorem wholeBoundaryTail (c : TargetContext K) :
    PowerHeightTailBound (wholeBinBoundary K c (actualHighPresentation K c)) := by
  exact highBoundaryControl K c (fullHighEulerControl K c)
    (highPureNormPoleExclusion K c) (highConductorDeficit K c) (highLabelUniformity K c)

/-- Exactly TSource.highBin, with the named actual D-TARGET and representative.
Ac is outside A′/ceiling; kc follows τ; k′/Z₀ precede b,R,Ebar and all labels. -/
def HighBinInput (c : TargetContext K) : Prop :=
  ∀ Ac : ℝ, 0 ≤ Ac → ∃ A' ceiling : ℝ, 0 ≤ A' ∧ 0 < ceiling ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∀ kc : ℝ, 0 ≤ kc →
    ∃ k' Z₀ : ℝ, 0 ≤ k' ∧ 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
    ∀ b : HighBlockIndex K c Z (Z ^ τ),
    ∀ R : HighLabel K c Z (Z ^ τ) b → ℝ, ∀ Ebar : ℝ,
      (∀ ℓ, 0 ≤ R ℓ ∧ R ℓ ≤ 2) →
      (∀ ℓ, (((((targetData K c).expansion Z (Z ^ τ)).block b).amplitudeSet ℓ).rows.card : ℝ) ≤
        kc * (Z ^ (((targetData K c).expansion Z (Z ^ τ)).block b).shell) ^
          (R ℓ + c.family.lamA) * (1 + Z ^ τ) ^ Ac) →
      (∀ ℓ, moderateExponent (((targetData K c).expansion Z (Z ^ τ)).block b).shell
        (2 * (((targetData K c).expansion Z (Z ^ τ)).block b).bin - 1)
        ((((targetData K c).expansion Z (Z ^ τ)).block b).amplitudeSet ℓ).mean
        (R ℓ) ≤ Ebar) →
      ‖(((targetData K c).expansion Z (Z ^ τ)).block b).value‖ ≤
        k' * Z ^ (3 / 16 + Ebar + c.family.lamA + c.lamB) * (1 + Z ^ τ) ^ A'

namespace HighCountAssembly

/-- Insert a row-cardinality bound, retaining its exact `d * R` exponent.
The only shell restriction needed for the loss is `d ≤ 1`. -/
theorem piece_count_bound
    (Z Y C kc N d R la lb m E Ac A : ℝ)
    (hZ : 1 ≤ Z) (hY : 0 < Y) (hC : 0 ≤ C) (hkc : 0 ≤ kc)
    (hla : 0 ≤ la) (hd : d ≤ 1)
    (hcount : N ≤ kc * (Z ^ d) ^ (R + la) * Y ^ Ac)
    (hexponent : m + d * R ≤ E) :
    C * N * Z ^ (3 / 16 + m + lb / 4) * Y ^ A ≤
      (C * kc) * Z ^ (3 / 16 + E + la + lb / 4) * Y ^ (Ac + A) := by
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hdla : d * la ≤ la := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hd hla
  have hp : d * (R + la) + (3 / 16 + m + lb / 4) ≤
      3 / 16 + E + la + lb / 4 := by nlinarith
  calc
    C * N * Z ^ (3 / 16 + m + lb / 4) * Y ^ A ≤
        C * (kc * (Z ^ d) ^ (R + la) * Y ^ Ac) *
          Z ^ (3 / 16 + m + lb / 4) * Y ^ A := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hY.le _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZpos.le _)
      exact mul_le_mul_of_nonneg_left hcount hC
    _ = (C * kc) * Z ^ (d * (R + la) + (3 / 16 + m + lb / 4)) *
        Y ^ (Ac + A) := by
      rw [← Real.rpow_mul hZpos.le,
        Real.rpow_add hZpos (d * (R + la)) (3 / 16 + m + lb / 4),
        Real.rpow_add hY Ac A]
      ring
    _ ≤ (C * kc) * Z ^ (3 / 16 + E + la + lb / 4) * Y ^ (Ac + A) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hY.le _)
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ hp) (mul_nonneg hC hkc)

/-- Sum the actual complex row contributions; labels need not be disjoint. -/
theorem norm_label_sum_le {ι κ : Type*} (labels : Finset ι)
    (rows : ι → Finset κ) (piece : ι → κ → ℂ) (M : ℝ)
    (hpiece : ∀ ℓ ∈ labels, (∑ u ∈ rows ℓ, ‖piece ℓ u‖) ≤ M) :
    ‖∑ ℓ ∈ labels, ∑ u ∈ rows ℓ, piece ℓ u‖ ≤ (labels.card : ℝ) * M := by
  classical
  calc
    ‖∑ ℓ ∈ labels, ∑ u ∈ rows ℓ, piece ℓ u‖ ≤
        ∑ ℓ ∈ labels, ‖∑ u ∈ rows ℓ, piece ℓ u‖ :=
      norm_sum_le labels (fun ℓ => ∑ u ∈ rows ℓ, piece ℓ u)
    _ ≤ ∑ _ℓ ∈ labels, M := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      exact (norm_sum_le (rows ℓ) (piece ℓ)).trans (hpiece ℓ hℓ)
    _ = (labels.card : ℝ) * M := by simp

/-- The two quarter-losses consume only half of the available `lb` loss. -/
theorem label_loss_bound
    (Z Y CL CS kc L la lb E Ac AS AL : ℝ)
    (hZ : 1 ≤ Z) (hY : 0 < Y)
    (hCL : 0 ≤ CL) (hCS : 0 ≤ CS) (hkc : 0 ≤ kc) (hlb : 0 ≤ lb)
    (hlabels : L ≤ CL * Z ^ (lb / 4) * Y ^ AL) :
    L * ((CS * kc) * Z ^ (3 / 16 + E + la + lb / 4) * Y ^ (Ac + AS)) ≤
      (CL * CS * kc) * Z ^ (3 / 16 + E + la + lb) * Y ^ (Ac + AS + AL) := by
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hM : 0 ≤ (CS * kc) * Z ^ (3 / 16 + E + la + lb / 4) *
      Y ^ (Ac + AS) := by positivity
  calc
    L * ((CS * kc) * Z ^ (3 / 16 + E + la + lb / 4) * Y ^ (Ac + AS)) ≤
        (CL * Z ^ (lb / 4) * Y ^ AL) *
          ((CS * kc) * Z ^ (3 / 16 + E + la + lb / 4) * Y ^ (Ac + AS)) :=
      mul_le_mul_of_nonneg_right hlabels hM
    _ = (CL * CS * kc) * Z ^ (lb / 4 + (3 / 16 + E + la + lb / 4)) *
        Y ^ (Ac + AS + AL) := by
      rw [Real.rpow_add hZpos (lb / 4) (3 / 16 + E + la + lb / 4),
        Real.rpow_add hY (Ac + AS) AL]
      ring
    _ ≤ (CL * CS * kc) * Z ^ (3 / 16 + E + la + lb) * Y ^ (Ac + AS + AL) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hY.le _)
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg hCL hCS) hkc)
      exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

/-- The counting assembly works for the same arbitrary presentation in both
piece estimates. All choices respect the original `HighBinInput` order. -/
theorem highBin_of_presentation_piece_controls (c : TargetContext K)
    (P : ActualHighPresentation K c)
    (hLabels : HighLabelUniformity K c P)
    (hShifted : HighShiftedNormForm K c P) :
    HighBinInput K c := by
  classical
  obtain ⟨AL, CL, ceilingL, ZL, hAL, hCL, hceilingL, hZL, hlabels⟩ := hLabels
  obtain ⟨AS, CS, ceilingS, ZS, hAS, hCS, hceilingS, hZS, hshifted⟩ := hShifted
  intro Ac hAc
  refine ⟨Ac + AS + AL, min ceilingL ceilingS, by linarith,
    lt_min hceilingL hceilingS, ?_⟩
  intro τ hτ hτceiling kc hkc
  refine ⟨CL * CS * kc, max ZL ZS,
    mul_nonneg (mul_nonneg hCL.le hCS.le) hkc,
    le_trans hZL (le_max_left _ _), ?_⟩
  intro Z hZ b R Ebar _hR hcount hEbar
  have hZL' : ZL ≤ Z := le_trans (le_max_left _ _) hZ
  have hZS' : ZS ≤ Z := le_trans (le_max_right _ _) hZ
  have hZ1 : 1 ≤ Z := le_trans hZL hZL'
  have hT : 1 ≤ Z ^ τ := Real.one_le_rpow hZ1 hτ.le
  have hY : 0 < 1 + Z ^ τ := by linarith
  have hTL : Z ^ τ ≤ Z ^ ceilingL := Real.rpow_le_rpow_of_exponent_le hZ1
    (le_trans hτceiling (min_le_left _ _))
  have hTS : Z ^ τ ≤ Z ^ ceilingS := Real.rpow_le_rpow_of_exponent_le hZ1
    (le_trans hτceiling (min_le_right _ _))
  have hd : (((targetData K c).expansion Z (Z ^ τ)).block b).shell ≤ 1 := by
    have hshell := (P.shell_range Z (Z ^ τ) hZ1 hT b).2
    have hzeta := P.zeta_small
    linarith
  have hpiece : ∀ ℓ ∈ P.labels Z (Z ^ τ) b,
      (∑ u ∈ ((((targetData K c).expansion Z (Z ^ τ)).block b).amplitudeSet ℓ).rows,
        ‖P.shiftedPiece Z (Z ^ τ) b ℓ u‖) ≤
      (CS * kc) * Z ^ (3 / 16 + Ebar + c.family.lamA + c.lamB / 4) *
        (1 + Z ^ τ) ^ (Ac + AS) := by
    intro ℓ hℓ
    have hm :
        moderateExponent (((targetData K c).expansion Z (Z ^ τ)).block b).shell
            (2 * (((targetData K c).expansion Z (Z ^ τ)).block b).bin - 1)
            ((((targetData K c).expansion Z (Z ^ τ)).block b).amplitudeSet ℓ).mean 0 +
          (((targetData K c).expansion Z (Z ^ τ)).block b).shell * R ℓ ≤ Ebar := by
      rw [← moderateExponent_count_identity]
      exact hEbar ℓ
    have hins := piece_count_bound Z (1 + Z ^ τ) CS kc
      (((((targetData K c).expansion Z (Z ^ τ)).block b).amplitudeSet ℓ).rows.card : ℝ)
      (((targetData K c).expansion Z (Z ^ τ)).block b).shell (R ℓ)
      c.family.lamA c.lamB
      (moderateExponent (((targetData K c).expansion Z (Z ^ τ)).block b).shell
        (2 * (((targetData K c).expansion Z (Z ^ τ)).block b).bin - 1)
        ((((targetData K c).expansion Z (Z ^ τ)).block b).amplitudeSet ℓ).mean 0)
      Ebar Ac AS hZ1 hY hCS.le hkc c.family.lamA_pos.le hd (hcount ℓ) hm
    exact (hshifted Z (Z ^ τ) hZS' hT hTS b ℓ hℓ).trans
      (by simpa only [highRowExponent] using hins)
  rw [P.block_identification Z (Z ^ τ) hZ1 hT b]
  exact (norm_label_sum_le (P.labels Z (Z ^ τ) b)
    (fun ℓ => ((((targetData K c).expansion Z (Z ^ τ)).block b).amplitudeSet ℓ).rows)
    (P.shiftedPiece Z (Z ^ τ) b) _ hpiece).trans
      (label_loss_bound Z (1 + Z ^ τ) CL CS kc
        ((P.labels Z (Z ^ τ) b).card : ℝ) c.family.lamA c.lamB Ebar Ac AS AL
        hZ1 hY hCL.le hCS.le hkc c.lamB_pos.le
        (hlabels Z (Z ^ τ) hZL' hT hTL b))

end HighCountAssembly

-- OBLIGATION HB-COUNT-ASSEMBLY | revised (6.24), pp.41–42; §7.1 pp.43–44.
-- Pure finite summation/real powers remains explicit: block identification,
-- triangle, shifted-piece bound, count_identity, d<1, and finite-label loss.
-- Intersect the ceilings BEFORE τ, add Ac to the fixed height degree, and
-- absorb the two lamB/4 losses. Empty labels give value=0 by identification.
-- No I/P count theorem is used: the displayed bounded-range counts are inputs
-- of the exact highBin field, not a new assumption of the final theorem.
theorem highBin_of_piece_controls (c : TargetContext K)
    (hLabels : HighLabelUniformity K c (actualHighPresentation K c))
    (hShifted : HighShiftedNormForm K c (actualHighPresentation K c)) :
    HighBinInput K c := by
  exact HighCountAssembly.highBin_of_presentation_piece_controls K c
    (actualHighPresentation K c) hLabels hShifted

/-- The intended TSource.highBin field for the named actual data. All admitted
dependencies are above, not extra hypotheses on the family or on its target. -/
theorem highBin (c : TargetContext K) : HighBinInput K c := by
  have hEuler := fullHighEulerControl K c
  have hPole := highPureNormPoleExclusion K c
  have hCond := highConductorDeficit K c
  have hLabels := highLabelUniformity K c
  have hShifted := highShiftedNormForm K c hEuler hPole hCond
  exact highBin_of_piece_controls K c hLabels hShifted

/-- A projection adapter records that HighBinInput has the formal field type;
it does not construct the other three TSource fields. -/
theorem highBin_field_adapter (c : TargetContext K)
    (hT : TSource c.geometry (targetCharacter K c) (targetData K c)
      c.family.B c.family.lamA c.lamB) : HighBinInput K c :=
  hT.highBin

end HeckeSkeleton
