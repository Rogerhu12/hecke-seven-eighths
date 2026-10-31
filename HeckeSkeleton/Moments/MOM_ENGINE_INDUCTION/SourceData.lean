import HeckeSkeleton.Base
import HeckeGeneral.Analysis.MomentInputs

/-!
# Source indices and actual moment models before choosing an expansion

One source datum fixes the complete scale-indexed expansion and the actual
row-cutoff exponent before any uniform-bound constants are chosen.  The
dependent block, amplitude and subdivision indices all refer to that same
expansion.  No concrete unfinished expansion or model choice appears in
these types.

The model fields are the original `MomentData` families, with independent
unmarked scales and the original evaluated height and shift parameters.
Every energy is the corresponding literal finite polynomial sum.  This
module supplies no energy estimate, profile-control assumption or analytic
construction of the source data.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- One fixed expansion and its row enumeration convention.  These are
data only; all estimates and geometric properties are separate. -/
structure MomentSourceData (c : TargetContext K) : Type 1 where
  expansion : ℝ → ℝ → HighExpansion (FrequencyRow K (places K c)) c.geometry.slots
  rowExponent : ℝ → ℝ

/-- The original block, amplitude, witness and selected-slot index,
parameterized by the source datum rather than a global admitted choice. -/
structure SourceMomentIndexFor (c : TargetContext K)
    (S : MomentSourceData K c) (Z T : ℝ) : Type 1 where
  block : Fin (S.expansion Z T).blockCount
  label : ((S.expansion Z T).block block).Label
  t : ℝ
  t_lower : 1 ≤ t
  t_upper : t ≤ 3 / 2
  subdivision : Fin
    ((((S.expansion Z T).block block).amplitudeSet label).subdivisionCount t)
  selected : Finset (Fin c.geometry.slots)

variable {K} {c : TargetContext K} {S : MomentSourceData K c} {Z T : ℝ}

abbrev momentBlock (i : SourceMomentIndexFor K c S Z T) :=
  (S.expansion Z T).block i.block

abbrev momentAmplitude (i : SourceMomentIndexFor K c S Z T) :=
  (momentBlock i).amplitudeSet i.label

abbrev momentWitness (i : SourceMomentIndexFor K c S Z T) :=
  (momentAmplitude i).subdivision i.t i.subdivision

def momentBase (i : SourceMomentIndexFor K c S Z T) : ℝ :=
  Z ^ (momentBlock i).shell

def rowWidth (i : SourceMomentIndexFor K c S Z T) : ℝ :=
  S.rowExponent (momentBase i)

def selectedLength (i : SourceMomentIndexFor K c S Z T) : ℝ :=
  ∑ _j ∈ i.selected,
    HeckeGeneral.ThetaSkeleton.TIP.slotLength c.geometry.slots (momentBlock i).shell

def SourceMomentIndexFor.noSlots (i : SourceMomentIndexFor K c S Z T) :
    SourceMomentIndexFor K c S Z T := { i with selected := ∅ }

def inverseParameters (i : SourceMomentIndexFor K c S Z T) : RealParameters :=
  ⟨rowWidth i, (momentWitness i).inverseLength, selectedLength i, 0, 0, 0,
    2 * c.family.B - 1⟩

def pairedParameters (i : SourceMomentIndexFor K c S Z T) : RealParameters :=
  ⟨rowWidth i, 0, selectedLength i, 0, (momentWitness i).plainLength,
    (momentWitness i).plainLength, 2 * c.family.B - 1⟩

def inverseCapacity (i : SourceMomentIndexFor K c S Z T) : Prop :=
  (momentWitness i).inverseLength + 2 * selectedLength i ≤ 1 - 2 * c.family.lamA ∧
    2 * (momentWitness i).inverseLength + 8 * selectedLength i ≤ 3 - 2 * c.family.lamA

/-- The physical capacity is still measured relative to power one, even
when the actual row enumeration uses a fixed enlarged envelope. -/
def pairedCapacity (i : SourceMomentIndexFor K c S Z T) : Prop :=
  (∀ j ∈ i.selected,
    HeckeGeneral.ThetaSkeleton.TIP.slotLength c.geometry.slots (momentBlock i).shell ≤
      (momentMesh K c.family).val) ∧
    2 * (momentWitness i).plainLength +
      6 * (2 * c.family.B - 1) * selectedLength i ≤ 1

variable (K)

/-- Actual inverse, paired and independent unmarked polynomial families
for the same source indices.  No energy or admissibility estimate is a field. -/
structure SourceMomentModelsFor (c : TargetContext K) (S : MomentSourceData K c) where
  dimension : ℕ
  inverse : ∀ Z T, SourceMomentIndexFor K c S Z T →
    SixthUnitClasses K (places K c) → (Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
      MomentData K c.family.omega (targetCharacter K c)
  paired : ∀ Z T, SourceMomentIndexFor K c S Z T →
    SixthUnitClasses K (places K c) → (Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
      MomentData K c.family.omega (targetCharacter K c)
  unmarked : ℝ → ℝ → SixthUnitClasses K (places K c) →
    (Fin dimension → ℝ) → (NonzeroIdeal K → Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
      MomentData K c.family.omega (targetCharacter K c)
  heights : ∀ Z T, SourceMomentIndexFor K c S Z T → Fin dimension → ℝ
  realShifts : ∀ Z T, SourceMomentIndexFor K c S Z T → NonzeroIdeal K → Fin dimension → ℝ
  imagShifts : ∀ Z T, SourceMomentIndexFor K c S Z T → NonzeroIdeal K → Fin dimension → ℝ

variable {K}

abbrev inverseModel (M : SourceMomentModelsFor K c S)
    (i : SourceMomentIndexFor K c S Z T) (s : SixthUnitClasses K (places K c)) :=
  M.inverse Z T i s (M.heights Z T i) (M.realShifts Z T i) (M.imagShifts Z T i)

abbrev pairedModel (M : SourceMomentModelsFor K c S)
    (i : SourceMomentIndexFor K c S Z T) (s : SixthUnitClasses K (places K c)) :=
  M.paired Z T i s (M.heights Z T i) (M.realShifts Z T i) (M.imagShifts Z T i)

abbrev unmarkedModel (M : SourceMomentModelsFor K c S)
    (i : SourceMomentIndexFor K c S Z T) (s : SixthUnitClasses K (places K c)) :=
  M.unmarked (momentBase i) ((momentBase i) ^ (momentWitness i).inverseLength)
    s (M.heights Z T i) (M.realShifts Z T i) (M.imagShifts Z T i)

local instance momentSectorFintype : Fintype (SixthUnitClasses K (places K c)) :=
  Fintype.ofFinite _

def markedModelEnergy (M : SourceMomentModelsFor K c S)
    (i : SourceMomentIndexFor K c S Z T) : ℝ :=
  ∑ s : SixthUnitClasses K (places K c),
    inverseEnergy (inverseModel M i s) (inverseParameters i) (momentBase i) 0

def pairedModelEnergy (M : SourceMomentModelsFor K c S)
    (i : SourceMomentIndexFor K c S Z T) : ℝ :=
  ∑ s : SixthUnitClasses K (places K c),
    pairedEnergy (pairedModel M i s) (pairedParameters i) (momentBase i) 0

def unmarkedBallEnergy (d : MomentData K c.family.omega (targetCharacter K c))
    (U D : ℝ) : ℝ :=
  ∑ u ∈ (d.rows (2 * U)).filter (SixthPowerFreeIdeal (K := K)),
    ‖inversePolynomial d u D 0‖ ^ 2

def amplifiedModelEnergy (M : SourceMomentModelsFor K c S)
    (i : SourceMomentIndexFor K c S Z T) : ℝ :=
  ∑ s : SixthUnitClasses K (places K c),
    unmarkedBallEnergy (unmarkedModel M i s)
      (momentBase i) ((momentBase i) ^ (momentWitness i).inverseLength)

/-- Original uniform order: the fixed source/model family precedes the
height degree and ceiling, which precede tau and its scalar and threshold. -/
def UniformMomentBound
    (E power : ∀ Z T, SourceMomentIndexFor K c S Z T → ℝ)
    (eligible : ∀ Z T, SourceMomentIndexFor K c S Z T → Prop) : Prop :=
  ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∃ Z₀ k : ℝ, 1 ≤ Z₀ ∧ 0 ≤ k ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ∀ i : SourceMomentIndexFor K c S Z (Z ^ τ),
        51 / 100 < (momentBlock i).bin → eligible Z (Z ^ τ) i →
          E Z (Z ^ τ) i ≤
            k * momentBase i ^ (power Z (Z ^ τ) i + c.family.lamA) * (1 + Z ^ τ) ^ A

/-- The existing prime-product premise on the same actual rows and masks,
with the physical source exponent retained. -/
def PairedPrimeProductBound (M : SourceMomentModelsFor K c S) (κ : ℝ) : Prop :=
  UniformMomentBound
    (fun _ _ i => ∑ s : SixthUnitClasses K (places K c),
      ∑ u ∈ pairedRows (pairedModel M i s) (pairedParameters i) (momentBase i),
        ‖slotProduct (pairedModel M i s) u (momentBase i) 0‖ ^ 2)
    (fun _ _ i => 1 + κ * selectedLength i)
    (fun _ _ i => pairedCapacity i)

end HeckeSkeleton.Moments.EngineInduction.Source
