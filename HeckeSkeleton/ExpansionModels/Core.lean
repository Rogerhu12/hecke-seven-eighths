import HeckeSkeleton.ExpansionModels.SharedWitnessRecipe
import HeckeSkeleton.ExpansionModels.WitnessHeightNormalization
import HeckeSkeleton.ExpansionModels.RecipeSchedule

/-!
# One data recipe for the expansion and all moment models

This module contains data constructors and finite-polynomial identities.
The inverse family has independent scales U,D and six fixed coordinates.
The first three coordinates are one common physical point; real and
imaginary witness parameters are ideal-indexed maps.  The same fields
generate source values and moment values.  No calibration, detector bound,
admissibility predicate, or energy estimate is stored in the recipe.

The named construction of the actual recipe remains D-EXPANSION in Base.
Consequently identities about these projections are not a construction of
the missing analytic expansion.  The finite label and block schedule are
part of that one outstanding data construction.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeGeneral.Analysis.ExpansionRecipe

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

abbrev RecipeVector := Fin 6 → ℝ

def recipePhysicalPoint (ξ : RecipeVector) : Fin 3 → ℝ :=
  fun j => ξ ⟨j.val, by omega⟩

def recipeCutoffTwist (W : IdealTest K) (V : ℝ → ℂ) (ratio : ℝ)
    (β ν : NonzeroIdeal K → ℝ) : IdealTest K where
  profile u _ y := W.profile u 0 y * V (ratio * y) *
    profilePower (-(β u : ℂ) + (ν u : ℂ) * Complex.I) y
  support u _ D := (W.support u 0 D).filter
    (fun I => V (ratio * (idealNorm K I / D)) ≠ 0)
  support_spec u _ D I := by
    rw [Finset.mem_filter, W.support_spec]
    constructor
    · rintro ⟨hW, hV⟩
      exact mul_ne_zero (mul_ne_zero hW hV) (profilePower_ne_zero _ _)
    · intro h
      have hWV := left_ne_zero_of_mul h
      exact ⟨left_ne_zero_of_mul hWV, right_ne_zero_of_mul hWV⟩

/-- Fixed algebraic and profile choices shared by every source scale. -/
structure RecipeFamily (ψ : HeckeCharacter K) (g : PrimeWindowGeometry) where
  presentationCount : ℕ
  presentationCount_pos : 0 < presentationCount
  presentation : Fin presentationCount → PolynomialPresentation K ψ
  inverseAnnular : IdealTest K
  plainAnnular : IdealTest K
  cutoff : ℝ → ℂ
  frequencyScale : ℝ
  slotTime : Fin g.slots → (Fin 3 → ℝ) → ℝ
  slotPower : Fin g.slots → (Fin 3 → ℝ) → ℂ
  slotCoefficient : Fin g.slots → HeckeCharacter K

variable {K}
variable {ψ : HeckeCharacter K} {g : PrimeWindowGeometry}

def RecipeFamily.physicalGeometry (F : RecipeFamily K ψ g)
    (p : Fin 3 → ℝ) : SlotGeometry K where
  slotCount := g.slots
  slots j := (analyticMomentPrimeWindow K g j).freezeTwist
    (F.slotTime j p) (F.slotPower j p)

variable (K)
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)
variable (ω ψ : HeckeCharacter K) (g : PrimeWindowGeometry)

/-- The unmarked model is independent in U,D and has no source-index or
selected-slot argument.  Original complete-ideal masks remain unchanged. -/
def RecipeFamily.inverseFamily (F : RecipeFamily K ψ g)
    (U D : ℝ) (s : SixthUnitClasses K S) (ξ : RecipeVector)
    (σ τ : NonzeroIdeal K → RecipeVector) : MomentData K ω ψ :=
  sharedMomentData K S P R ω ψ
    (F.presentation (_root_.ExpansionRecipe.decodePresentation
      F.presentationCount F.presentationCount_pos (ξ 4)))
    (zeroSlotGeometry K) Fin.elim0 s
    (recipeCutoffTwist K F.inverseAnnular F.cutoff (D / U ^ (2 * ξ 3))
      (fun u => σ u 0) (fun u => F.frequencyScale * τ u 0))
    (zeroIdealTest K)

def RecipeFamily.plainTest (F : RecipeFamily K ψ g)
    (σ τ : NonzeroIdeal K → RecipeVector) : IdealTest K :=
  F.plainAnnular.freezeTwist (fun _ => 0)
    (fun u => -(σ u 0 : ℂ) + (F.frequencyScale * τ u 0 : ℝ) * Complex.I)

/-- The two plain tests are identical and all slots use the same physical
point, independently of every ideal-indexed witness parameter. -/
def RecipeFamily.fullModel (F : RecipeFamily K ψ g)
    (U D : ℝ) (s : SixthUnitClasses K S) (ξ : RecipeVector)
    (σ τ : NonzeroIdeal K → RecipeVector) : MomentData K ω ψ :=
  { F.inverseFamily K S P R ω ψ g U D s ξ σ τ with
    plainTest₁ := F.plainTest K ψ g σ τ
    plainTest₂ := F.plainTest K ψ g σ τ
    geometry := F.physicalGeometry (recipePhysicalPoint ξ)
    slotCoefficient := F.slotCoefficient }

def RecipeFamily.slotModel (F : RecipeFamily K ψ g)
    (p : Fin 3 → ℝ) (s : SixthUnitClasses K S) : MomentData K ω ψ :=
  sharedMomentData K S P R ω ψ
    (F.presentation ⟨0, F.presentationCount_pos⟩)
    (F.physicalGeometry p) F.slotCoefficient s
    (zeroIdealTest K) (zeroIdealTest K)

/-- Continuous row parameters are kept inside one finite witness choice. -/
structure RecipeWitnessData (F : RecipeFamily K ψ g) where
  inverseLength : ℝ
  plainLength : ℝ
  presentation : Fin F.presentationCount
  realShifts : NonzeroIdeal K → RecipeVector
  imagShifts : NonzeroIdeal K → RecipeVector

variable {K S P R ω ψ g}

def RecipeWitnessData.heights {F : RecipeFamily K ψ g}
    (w : RecipeWitnessData K ψ g F) (p : Fin 3 → ℝ) (t T : ℝ) : RecipeVector :=
  _root_.ExpansionRecipe.sourceHeightVector p t
    (_root_.ExpansionRecipe.finitePresentationCode w.presentation) T

theorem RecipeWitnessData.physicalPoint_heights {F : RecipeFamily K ψ g}
    (w : RecipeWitnessData K ψ g F) (p : Fin 3 → ℝ) (t T : ℝ) :
    recipePhysicalPoint (w.heights p t T) = p := by
  funext j
  fin_cases j <;> rfl

theorem RecipeWitnessData.heights_cutoff {F : RecipeFamily K ψ g}
    (w : RecipeWitnessData K ψ g F) (p : Fin 3 → ℝ) (t T : ℝ) :
    2 * (w.heights p t T) 3 = t := by
  change 2 * (t / 2) = t
  ring

theorem RecipeWitnessData.heights_presentation {F : RecipeFamily K ψ g}
    (w : RecipeWitnessData K ψ g F) (p : Fin 3 → ℝ) (t T : ℝ) :
    _root_.ExpansionRecipe.decodePresentation F.presentationCount F.presentationCount_pos
      ((w.heights p t T) 4) = w.presentation :=
  _root_.ExpansionRecipe.decodePresentation_code _ _ _

theorem RecipeWitnessData.heights_norm_eq {F : RecipeFamily K ψ g}
    (w : RecipeWitnessData K ψ g F) (p : Fin 3 → ℝ) (t T : ℝ)
    (hT : 1 ≤ T) (hp : ‖p‖ ≤ T) (ht : 1 ≤ t ∧ t ≤ 3 / 2) :
    ‖w.heights p t T‖ = T :=
  _root_.ExpansionRecipe.sourceHeightVector_norm_eq p t _ T hT hp ht
    ⟨_root_.ExpansionRecipe.finitePresentationCode_nonneg w.presentation,
      (_root_.ExpansionRecipe.finitePresentationCode_lt_one w.presentation).le⟩

def RecipeWitnessData.model {F : RecipeFamily K ψ g}
    (w : RecipeWitnessData K ψ g F) (p : Fin 3 → ℝ) (t T U : ℝ)
    (s : SixthUnitClasses K S) : MomentData K ω ψ :=
  F.fullModel K S P R ω ψ g U (U ^ w.inverseLength) s (w.heights p t T)
    w.realShifts w.imagShifts

/-- The finite code and half-cutoff coordinate recover exactly the chosen
arithmetic presentation and the original ratio D/U^t. -/
theorem RecipeWitnessData.model_eq_shared {F : RecipeFamily K ψ g}
    (w : RecipeWitnessData K ψ g F) (p : Fin 3 → ℝ) (t T U : ℝ)
    (s : SixthUnitClasses K S) :
    w.model (P := P) (R := R) (ω := ω) p t T U s =
      sharedMomentData K S P R ω ψ (F.presentation w.presentation)
        (F.physicalGeometry p) F.slotCoefficient s
        (recipeCutoffTwist K F.inverseAnnular F.cutoff
          (U ^ w.inverseLength / U ^ t) (fun u => w.realShifts u 0)
          (fun u => F.frequencyScale * w.imagShifts u 0))
        (F.plainTest K ψ g w.realShifts w.imagShifts) := by
  unfold RecipeWitnessData.model RecipeFamily.fullModel RecipeFamily.inverseFamily
  rw [RecipeWitnessData.heights_presentation, RecipeWitnessData.heights_cutoff,
    RecipeWitnessData.physicalPoint_heights]
  rfl

/-- Witness choices change no physical prime polynomial.  All selected
prime factors use the same three physical coordinates. -/
theorem RecipeWitnessData.primePolynomial_model {F : RecipeFamily K ψ g}
    (w : RecipeWitnessData K ψ g F) (p : Fin 3 → ℝ) (t T U : ℝ)
    (s : SixthUnitClasses K S) (j : Fin g.slots) (u : NonzeroIdeal K)
    (Z v : ℝ) :
    primePolynomial (w.model (P := P) (R := R) (ω := ω) p t T U s) j u Z v =
      primePolynomial (F.slotModel K S P R ω ψ g p s) j u Z v := by
  dsimp only [primePolynomial, RecipeWitnessData.model,
    RecipeFamily.fullModel, RecipeFamily.slotModel]
  rw [RecipeWitnessData.physicalPoint_heights]
  rfl

theorem RecipeWitnessData.selectedSlotProduct {F : RecipeFamily K ψ g}
    (w : RecipeWitnessData K ψ g F) (p : Fin 3 → ℝ) (t T : ℝ)
    (s : SixthUnitClasses K S) (d : ℝ) (hd : 0 < d)
    (J : Finset (Fin g.slots)) (u : NonzeroIdeal K) {Z : ℝ} (hZ : 0 < Z) :
    slotProduct (((w.model (P := P) (R := R) (ω := ω) p t T (Z ^ d) s).changeSlotBase
      d hd).restrictSlots J) u (Z ^ d) 0 =
        ∏ j ∈ J, primePolynomial (F.slotModel K S P R ω ψ g p s) j u Z 0 := by
  calc
    _ = ∏ j ∈ J,
        primePolynomial (w.model (P := P) (R := R) (ω := ω) p t T (Z ^ d) s) j u Z 0 :=
      selectedSlotProduct_changeSlotBase
        (w.model (P := P) (R := R) (ω := ω) p t T (Z ^ d) s) d hd J u hZ 0
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _hj
      exact w.primePolynomial_model (P := P) (R := R) (ω := ω) p t T (Z ^ d) s j u Z 0

def RecipeWitnessData.toWitness {F : RecipeFamily K ψ g}
    (w : RecipeWitnessData K ψ g F) (rows : Finset (FrequencyRow K S))
    (p : Fin 3 → ℝ) (t T U : ℝ) : WitnessSubdivision (FrequencyRow K S) where
  rows := rows
  inverseLength := w.inverseLength
  plainLength := w.plainLength
  inverseValue u := inversePolynomial (w.model (P := P) (R := R) (ω := ω) p t T U u.sector)
    u.ideal.val (U ^ w.inverseLength) 0
  plainValue u := plainPolynomial (w.model (P := P) (R := R) (ω := ω) p t T U u.sector)
    (F.plainTest K ψ g w.realShifts w.imagShifts) u.ideal.val (U ^ w.plainLength) 0

variable (K S ψ g)

/-- A physical amplitude label has one sector and one common physical
point.  Finite subdivisions select rows, not a new physical prime profile. -/
structure RecipeAmplitudeData (F : RecipeFamily K ψ g) where
  candidates : Finset (FrequencyRow K S)
  sector : SixthUnitClasses K S
  physical : Fin 3 → ℝ
  amplitude : Fin g.slots → ℝ
  witnessCount : ℝ → ℕ
  witnessChoice : (t : ℝ) → FrequencyRow K S → Fin (witnessCount t)
  witness : (t : ℝ) → Fin (witnessCount t) → RecipeWitnessData K ψ g F

variable {K S ψ g}

def RecipeAmplitudeData.rows {F : RecipeFamily K ψ g}
    (A : RecipeAmplitudeData K S ψ g F) (U : ℝ) : Finset (FrequencyRow K S) :=
  (frequencyRows K S (2 * U)).filter fun u => u ∈ A.candidates ∧ u.sector = A.sector

def RecipeAmplitudeData.toAmplitude {F : RecipeFamily K ψ g}
    (A : RecipeAmplitudeData K S ψ g F) (Z T U : ℝ) :
    AmplitudeSet (FrequencyRow K S) g.slots where
  rows := A.rows U
  amplitude := A.amplitude
  slotValue j u := primePolynomial (F.slotModel K S P R ω ψ g A.physical u.sector)
    j u.ideal.val Z 0
  subdivisionCount := A.witnessCount
  subdivision t j := (A.witness t j).toWitness (P := P) (R := R) (ω := ω)
    ((A.rows U).filter fun u => A.witnessChoice t u = j) A.physical t T U

variable (K S ψ g)

structure RecipeBlockData (F : RecipeFamily K ψ g) (labelCount : ℕ) where
  bin : ℝ
  value : ℂ
  amplitude : Fin labelCount → RecipeAmplitudeData K S ψ g F

variable {K S ψ g}

def RecipeBlockData.toBlock {F : RecipeFamily K ψ g} {n : ℕ}
    (b : RecipeBlockData K S ψ g F n) (d Z T : ℝ) :
    ModerateBlock (FrequencyRow K S) g.slots where
  shell := d
  bin := b.bin
  value := b.value
  Label := Fin n
  amplitudeSet l := (b.amplitude l).toAmplitude (P := P) (R := R) (ω := ω) Z T (Z ^ d)

variable (K S ψ g)

/-- The raw global recipe. Its finite schedule is explicit. The actual
detector and physical integral must construct these data in D-EXPANSION;
none of their desired analytic conclusions is a field here. -/
structure RecipeExpansion (ζ : ℝ) where
  family : RecipeFamily K ψ g
  labelCount : ℕ
  bufferMultiplicity : ℕ
  principal : ℝ → ℝ → ℂ
  small : ℝ → ℝ → ℂ
  large : ℝ → ℝ → ℂ
  tail : ℝ → ℝ → ℂ
  blocks : ∀ Z T : ℝ,
    Fin (ExpansionInterfaces.shellCount Z (1 / 16) (13 / 16 + ζ) * bufferMultiplicity) →
      RecipeBlockData K S ψ g family labelCount

variable {K S ψ g} {ζ : ℝ}

def RecipeExpansion.scheduledCount (E : RecipeExpansion K S ψ g ζ) (Z : ℝ) : ℕ :=
  _root_.ExpansionRecipe.scheduledBlockCount E.bufferMultiplicity ζ Z

def RecipeExpansion.activeCount (E : RecipeExpansion K S ψ g ζ) (Z T : ℝ) : ℕ :=
  _root_.ExpansionRecipe.activeBlockCount E.bufferMultiplicity ζ Z T

theorem RecipeExpansion.active_of_index (E : RecipeExpansion K S ψ g ζ)
    (Z T : ℝ) (b : Fin (E.activeCount Z T)) :
    (2 : ℝ) ^ (16 : ℕ) ≤ Z ∧ 1 ≤ T :=
  _root_.ExpansionRecipe.activeBlockGuard E.bufferMultiplicity ζ Z T b

def RecipeExpansion.rawBlockIndex (E : RecipeExpansion K S ψ g ζ)
    (Z T : ℝ) (b : Fin (E.activeCount Z T)) : Fin (E.scheduledCount Z) :=
  _root_.ExpansionRecipe.rawBlockIndex E.bufferMultiplicity ζ Z T b

theorem RecipeExpansion.bufferMultiplicity_pos_of_index (E : RecipeExpansion K S ψ g ζ)
    (Z T : ℝ) (b : Fin (E.activeCount Z T)) : 0 < E.bufferMultiplicity :=
  _root_.ExpansionRecipe.multiplicity_pos_of_block E.bufferMultiplicity ζ Z T b

/-- Decode the actual dyadic shell from the finite block schedule.  The
remaining residue is the fixed buffered-bin choice. -/
def RecipeExpansion.shellIndex (E : RecipeExpansion K S ψ g ζ)
    (Z T : ℝ) (b : Fin (E.activeCount Z T)) :
    Fin (ExpansionInterfaces.shellCount Z (1 / 16) (13 / 16 + ζ)) :=
  _root_.ExpansionRecipe.blockShellIndex E.bufferMultiplicity ζ Z T b

def RecipeExpansion.shell (E : RecipeExpansion K S ψ g ζ)
    (Z T : ℝ) (b : Fin (E.activeCount Z T)) : ℝ :=
  _root_.ExpansionRecipe.blockShell E.bufferMultiplicity ζ Z T b

theorem RecipeExpansion.shell_range (E : RecipeExpansion K S ψ g ζ)
    (Z T : ℝ) (b : Fin (E.activeCount Z T)) :
    1 / 16 ≤ E.shell Z T b ∧ E.shell Z T b < 13 / 16 + ζ :=
  _root_.ExpansionRecipe.blockShell_range E.bufferMultiplicity ζ Z T b

def RecipeExpansion.toHigh (E : RecipeExpansion K S ψ g ζ) (Z T : ℝ) :
    HighExpansion (FrequencyRow K S) g.slots where
  principal := E.principal Z T
  small := E.small Z T
  large := E.large Z T
  tail := E.tail Z T
  blockCount := E.activeCount Z T
  block b := (E.blocks Z T (E.rawBlockIndex Z T b)).toBlock
    (P := P) (R := R) (ω := ω) (E.shell Z T b) Z T

theorem RecipeExpansion.toHigh_blockCount_le (E : RecipeExpansion K S ψ g ζ) (Z T : ℝ) :
    (E.toHigh (P := P) (R := R) (ω := ω) Z T).blockCount ≤ E.scheduledCount Z :=
  _root_.ExpansionRecipe.activeBlockCount_le E.bufferMultiplicity ζ Z T

theorem RecipeExpansion.toHigh_blockCount_eq (E : RecipeExpansion K S ψ g ζ) (Z T : ℝ)
    (hZ : (2 : ℝ) ^ (16 : ℕ) ≤ Z) (hT : 1 ≤ T) :
    (E.toHigh (P := P) (R := R) (ω := ω) Z T).blockCount = E.scheduledCount Z :=
  _root_.ExpansionRecipe.activeBlockCount_eq E.bufferMultiplicity ζ Z T hZ hT

/-- Every label, including inactive labels, has the original physical norm
envelope by the definition of its finite arithmetic row set. -/
theorem RecipeExpansion.toHigh_rows_in_norm_envelope (E : RecipeExpansion K S ψ g ζ)
    (Z T : ℝ) (b : Fin (E.toHigh (P := P) (R := R) (ω := ω) Z T).blockCount)
    (l : ((E.toHigh (P := P) (R := R) (ω := ω) Z T).block b).Label) :
    ((((E.toHigh (P := P) (R := R) (ω := ω) Z T).block b).amplitudeSet l).rows) ⊆
      frequencyRows K S (2 * Z ^ ((E.toHigh (P := P) (R := R) (ω := ω) Z T).block b).shell) :=
  Finset.filter_subset _ _

end HeckeGeneral.Analysis.ExpansionRecipe