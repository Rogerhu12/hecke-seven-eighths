import HeckeSkeleton.Base
import HeckeGeneral.Analysis.MomentInputs
import HeckeSkeleton.ExpansionModels.ScaleCutoff
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileControl
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SixthPowerSeed

/-!
# A fixed source for indices, models, and uniform moment statements

The complete scale-indexed expansion and its row enumeration convention are
fixed before the height degree, ceiling, tau, threshold, or bound constant.
Every block, amplitude, witness and selected-slot index refers to that same
source.  No unfinished actual expansion is selected in these definitions.

The fields of `SourceMomentModelsFor` are actual `MomentData` and parameter
maps; all energies below are literal finite sums of the original polynomials.
Calibration, row eligibility and profile control are predicates on this one
family, not data fields containing a desired moment estimate.

This shared layer does not import `Moments`.  The named actual aliases are
instantiated there, after choosing the actual raw recipe.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]

/-- One complete source, including its row-envelope convention. -/
structure MomentSourceData (c : TargetContext K) : Type 1 where
  expansion : ℝ → ℝ → HighExpansion (FrequencyRow K (places K c)) c.geometry.slots
  rowExponent : ℝ → ℝ

local instance sourceMomentSectorFintype (c : TargetContext K) :
    Fintype (SixthUnitClasses K (places K c)) := Fintype.ofFinite _

/-- The index belongs to the ONE actual expansion, including its original
selected slots. No arbitrary finite row family is substituted. -/
structure SourceMomentIndexFor (c : TargetContext K)
    (E : MomentSourceData K c) (Z T : ℝ) : Type 1 where
  block : Fin (E.expansion Z T).blockCount
  label : ((E.expansion Z T).block block).Label
  t : ℝ
  t_lower : 1 ≤ t
  t_upper : t ≤ 3 / 2
  subdivision : Fin
    ((((E.expansion Z T).block block).amplitudeSet label).subdivisionCount t)
  selected : Finset (Fin c.geometry.slots)

variable {K}
variable {c : TargetContext K} {E : MomentSourceData K c} {Z T : ℝ}
abbrev momentBlockFor (i : SourceMomentIndexFor K c E Z T) :=
  (E.expansion Z T).block i.block
abbrev momentAmplitudeFor (i : SourceMomentIndexFor K c E Z T) :=
  (momentBlockFor i).amplitudeSet i.label
abbrev momentWitnessFor (i : SourceMomentIndexFor K c E Z T) :=
  (momentAmplitudeFor i).subdivision i.t i.subdivision
def momentBaseFor (i : SourceMomentIndexFor K c E Z T) : ℝ := Z ^ (momentBlockFor i).shell
def selectedLengthFor (i : SourceMomentIndexFor K c E Z T) : ℝ :=
  ∑ _j ∈ i.selected,
    HeckeGeneral.ThetaSkeleton.TIP.slotLength c.geometry.slots (momentBlockFor i).shell
def SourceMomentIndexFor.noSlots (i : SourceMomentIndexFor K c E Z T) :
    SourceMomentIndexFor K c E Z T := { i with selected := ∅ }

/-- The physical shell extends to 2U.  Only the row-enumeration exponent
changes; the actual inverse, plain and prime polynomial scales remain U. -/
def momentRowExponent (U : ℝ) : ℝ :=
  if 1 < U then _root_.ExpansionRecipe.dyadicMassExponent U else 1

def rowWidthFor (i : SourceMomentIndexFor K c E Z T) : ℝ :=
  E.rowExponent (momentBaseFor i)

def inverseParametersFor (i : SourceMomentIndexFor K c E Z T) : RealParameters :=
  ⟨rowWidthFor i, (momentWitnessFor i).inverseLength,
    selectedLengthFor i, 0, 0, 0, 2 * c.family.B - 1⟩
def pairedParametersFor (i : SourceMomentIndexFor K c E Z T) : RealParameters :=
  ⟨rowWidthFor i, 0, selectedLengthFor i, 0, (momentWitnessFor i).plainLength,
    (momentWitnessFor i).plainLength, 2 * c.family.B - 1⟩

/-- Revised full range, with the genuine unrestricted zero-slot alternative. -/
def ExtendedPRegionFor (a : RealParameters) : Prop :=
  3 / 4 ≤ a.κ ∧ a.κ ≤ 1 ∧
    (a.z = 0 ∨ (0 < a.z ∧ a.n₁ + a.n₂ + 6 * a.κ * a.z ≤ a.m + a.q))

def inverseCapacityFor (i : SourceMomentIndexFor K c E Z T) : Prop :=
  (momentWitnessFor i).inverseLength + 2 * selectedLengthFor i ≤ 1 - 2 * c.family.lamA ∧
  2 * (momentWitnessFor i).inverseLength + 8 * selectedLengthFor i ≤ 3 - 2 * c.family.lamA
def pairedCapacityFor (i : SourceMomentIndexFor K c E Z T) : Prop :=
  (∀ j ∈ i.selected,
    HeckeGeneral.ThetaSkeleton.TIP.slotLength c.geometry.slots (momentBlockFor i).shell ≤
      (momentMesh K c.family).val) ∧
  2 * (momentWitnessFor i).plainLength +
    6 * (2 * c.family.B - 1) * selectedLengthFor i ≤ 1


variable (K)

/-- One family, with a finite physical/witness height vector and independent
rowwise real/imaginary twists. The unmarked family has INDEPENDENT U,D.
Tests, backgrounds and masks are actual data; no energy is a field. -/
structure SourceMomentModelsFor (c : TargetContext K) (E : MomentSourceData K c) where
  dimension : ℕ
  inverse : ∀ Z T, SourceMomentIndexFor K c E Z T →
    SixthUnitClasses K (places K c) → (Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
      MomentData K c.family.omega (targetCharacter K c)
  paired : ∀ Z T, SourceMomentIndexFor K c E Z T →
    SixthUnitClasses K (places K c) → (Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
      MomentData K c.family.omega (targetCharacter K c)
  unmarked : ℝ → ℝ → SixthUnitClasses K (places K c) →
    (Fin dimension → ℝ) → (NonzeroIdeal K → Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
      MomentData K c.family.omega (targetCharacter K c)
  heights : ∀ Z T, SourceMomentIndexFor K c E Z T → Fin dimension → ℝ
  realShifts : ∀ Z T, SourceMomentIndexFor K c E Z T → NonzeroIdeal K → Fin dimension → ℝ
  imagShifts : ∀ Z T, SourceMomentIndexFor K c E Z T → NonzeroIdeal K → Fin dimension → ℝ


def momentRowCharacters (c : TargetContext K) : RowCharacterInput K (places K c) (probeData K c) :=
  arithmeticRowCharacterInput K (places K c) (probeData K c)


variable {K}

abbrev inverseModelFor (M : SourceMomentModelsFor K c E) (i : SourceMomentIndexFor K c E Z T)
    (s : SixthUnitClasses K (places K c)) :=
  M.inverse Z T i s (M.heights Z T i) (M.realShifts Z T i) (M.imagShifts Z T i)
abbrev pairedModelFor (M : SourceMomentModelsFor K c E) (i : SourceMomentIndexFor K c E Z T)
    (s : SixthUnitClasses K (places K c)) :=
  M.paired Z T i s (M.heights Z T i) (M.realShifts Z T i) (M.imagShifts Z T i)
abbrev unmarkedModelFor (M : SourceMomentModelsFor K c E) (i : SourceMomentIndexFor K c E Z T)
    (s : SixthUnitClasses K (places K c)) :=
  M.unmarked (momentBaseFor i) ((momentBaseFor i) ^ (momentWitnessFor i).inverseLength)
    s (M.heights Z T i) (M.realShifts Z T i) (M.imagShifts Z T i)

/-- Original complete-ideal zeros, including redundant sixth powers. -/
def originalMomentMask (u : NonzeroIdeal K) (I : Ideal (𝓞 K)) : Bool :=
  if (∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I →
    p ∉ places K c ∧ (6 : 𝓞 K) ∉ p.asIdeal) ∧
    IsCoprime I u.val then true else false

/-- Literal polynomial calibration. Sector dependence is retained, and the
two plain factors are both matched, with their actual conjugated profiles. -/
structure SourcePolynomialCalibrationFor (R : RowCharacterInput K (places K c) (probeData K c))
    (M : SourceMomentModelsFor K c E) : Prop where
  character : ∀ Z T (i : SourceMomentIndexFor K c E Z T) u,
    u ∈ (momentWitnessFor i).rows →
      (inverseModelFor M i u.sector).rowCharacter u.ideal.val = R.character u ∧
      (pairedModelFor M i u.sector).rowCharacter u.ideal.val = R.character u
  mask : ∀ Z T (i : SourceMomentIndexFor K c E Z T) s u I,
    (inverseModelFor M i s).commonMask u I = originalMomentMask (c := c) u I ∧
    (pairedModelFor M i s).commonMask u I = originalMomentMask (c := c) u I
  inverse : ∀ Z T (i : SourceMomentIndexFor K c E Z T) u,
    u ∈ (momentWitnessFor i).rows →
      (momentWitnessFor i).inverseValue u =
        inversePolynomial (inverseModelFor M i u.sector) u.ideal.val
          ((momentBaseFor i) ^ (momentWitnessFor i).inverseLength) 0
  plain₁ : ∀ Z T (i : SourceMomentIndexFor K c E Z T) u,
    u ∈ (momentWitnessFor i).rows →
      (momentWitnessFor i).plainValue u =
        plainPolynomial (pairedModelFor M i u.sector)
          (pairedModelFor M i u.sector).plainTest₁ u.ideal.val
          ((momentBaseFor i) ^ (momentWitnessFor i).plainLength) 0
  plain₂ : ∀ Z T (i : SourceMomentIndexFor K c E Z T) u,
    u ∈ (momentWitnessFor i).rows →
      (momentWitnessFor i).plainValue u =
        plainPolynomial (pairedModelFor M i u.sector)
          (pairedModelFor M i u.sector).plainTest₂ u.ideal.val
          ((momentBaseFor i) ^ (momentWitnessFor i).plainLength) 0
  inverse_slots : ∀ Z T (i : SourceMomentIndexFor K c E Z T) u,
    u ∈ (momentWitnessFor i).rows →
      (∏ j ∈ i.selected, (momentAmplitudeFor i).slotValue j u) =
        slotProduct (inverseModelFor M i u.sector) u.ideal.val (momentBaseFor i) 0
  paired_slots : ∀ Z T (i : SourceMomentIndexFor K c E Z T) u,
    u ∈ (momentWitnessFor i).rows →
      (∏ j ∈ i.selected, (momentAmplitudeFor i).slotValue j u) =
        slotProduct (pairedModelFor M i u.sector) u.ideal.val (momentBaseFor i) 0
  unmarked : ∀ Z T (i : SourceMomentIndexFor K c E Z T) u,
    u ∈ (momentWitnessFor i).rows →
      (momentWitnessFor i).inverseValue u =
        inversePolynomial (unmarkedModelFor M i u.sector) u.ideal.val
          ((momentBaseFor i) ^ (momentWitnessFor i).inverseLength) 0

/-- The base ideal, original sector and complete common mask must survive
the true source reindex. Large complete norm alone cannot prove this. -/
structure SourceRowEligibilityFor (M : SourceMomentModelsFor K c E) : Prop where
  /-- The actual strict widths r+2z<m and 2r+8z<3m, not the old ceiling. -/
  inverse_region : ∀ Z T (i : SourceMomentIndexFor K c E Z T),
    inverseCapacityFor i → MIRegion (inverseParametersFor i)
  /-- Full kappa <= 1, retaining the unrestricted z=0 branch. -/
  paired_region : ∀ Z T (i : SourceMomentIndexFor K c E Z T),
    pairedCapacityFor i → ExtendedPRegionFor (pairedParametersFor i)
  inverse_rows : ∀ Z T (i : SourceMomentIndexFor K c E Z T) u,
    u ∈ (momentWitnessFor i).rows →
      u.ideal.val ∈ (inverseModelFor M i u.sector).rows
        ((momentBaseFor i) ^ (inverseParametersFor i).m)
  paired_rows : ∀ Z T (i : SourceMomentIndexFor K c E Z T) u,
    u ∈ (momentWitnessFor i).rows →
      u.ideal.val ∈ pairedRows (pairedModelFor M i u.sector) (pairedParametersFor i) (momentBaseFor i)
  unmarked_rows : ∀ Z T (i : SourceMomentIndexFor K c E Z T) u,
    u ∈ (momentWitnessFor i).rows →
      u.ideal.val ∈ (unmarkedModelFor M i u.sector).rows (2 * momentBaseFor i) ∧
      SixthPowerFreeIdeal (K := K) u.ideal.val
  fiber : Function.Injective
    (fun u : FrequencyRow K (places K c) => (u.ideal.val, u.sector))
  geometry : ∀ Z T (i : SourceMomentIndexFor K c E Z T) s,
    (inverseModelFor M i s).geometry.totalLength = selectedLengthFor i ∧
    (pairedModelFor M i s).geometry.totalLength = selectedLengthFor i
  paired_finite_slots : ∀ Z T (i : SourceMomentIndexFor K c E Z T) s j,
    FiniteOrder ((pairedModelFor M i s).slotCoefficient j)

/-- The actual evaluation parameters lie in the profile quantification region.
This is geometric control of a fixed family, not an energy estimate. -/
def SourceMomentParameterControlFor (M : SourceMomentModelsFor K c E) : Prop :=
  ∀ Z T (i : SourceMomentIndexFor K c E Z T),
    ‖M.heights Z T i‖ ≤ T ∧
      (∀ u, ‖M.realShifts Z T i u‖ ≤ 8) ∧
      (∀ u, ‖M.imagShifts Z T i u‖ ≤ 1 + ‖M.heights Z T i‖)

/-- The plain-length range is fixed for the entire all-scale source. -/
def SourceWitnessLengthBoundFor (E : MomentSourceData K c) (L : ℝ) : Prop :=
  ∀ Z T (i : SourceMomentIndexFor K c E Z T),
    0 ≤ (momentWitnessFor i).inverseLength ∧
      0 ≤ (momentWitnessFor i).plainLength ∧ (momentWitnessFor i).plainLength ≤ L

/-- All marked inverse, plain, and prime slices of the one fixed source.
The constants precede the entire family, including all row-local shifts. -/
def MarkedMomentProfileControlFor (M : SourceMomentModelsFor K c E) : Prop :=
  ∀ J : ℕ, ∀ A : ℝ, 0 ≤ A →
    ∃ C H a b : ℝ, 0 < C ∧ 0 ≤ H ∧ 0 < a ∧ a < b ∧
      ∀ Z T (i : SourceMomentIndexFor K c E Z T), 1 ≤ Z → 1 ≤ T →
      ∀ s (ξ : Fin M.dimension → ℝ) σ τ,
        ‖ξ‖ ≤ T → (∀ u, ‖σ u‖ ≤ 8) → (∀ u, ‖τ u‖ ≤ 1 + ‖ξ‖) →
        ∀ d ∈ [M.inverse Z T i s ξ σ τ, M.paired Z T i s ξ σ τ],
          Moments.UniformAmplify.ModelProfileControl d J A C H a b T


/-- Independent U,D are retained in the unmarked profile family, with the
same parameter region as the marked family and no restriction on D/U^t. -/
def UnmarkedMomentProfileControlFor (M : SourceMomentModelsFor K c E) : Prop :=
  ∀ J : ℕ, ∀ A : ℝ, 0 ≤ A →
    ∃ C H a b : ℝ, 0 < C ∧ 0 ≤ H ∧ 0 < a ∧ a < b ∧
      ∀ U D T : ℝ, 1 ≤ U → 1 ≤ D → 1 ≤ T →
      ∀ s (ξ : Fin M.dimension → ℝ) σ τ,
        ‖ξ‖ ≤ T → (∀ u, ‖σ u‖ ≤ 8) → (∀ u, ‖τ u‖ ≤ 1 + ‖ξ‖) →
          Moments.UniformAmplify.ModelProfileControl (M.unmarked U D s ξ σ τ)
            J A C H a b T

/-- Whole source control includes every ideal/prime profile, the genuinely
independent unmarked scales, and the actual evaluation parameter box.
The explicit norm-twist mixed derivative and weighted Fourier theorems are
proved from the same primitive profile formulas in MOM_UNIFORM_AMPLIFY. -/
structure WholeMomentProfileControlFor (M : SourceMomentModelsFor K c E) : Prop where
  marked : MarkedMomentProfileControlFor M
  unmarked : UnmarkedMomentProfileControlFor M
  parameters : SourceMomentParameterControlFor M
  lengths : ∃ L : ℝ, 0 ≤ L ∧ SourceWitnessLengthBoundFor E L

instance {M : SourceMomentModelsFor K c E} :
    CoeFun (WholeMomentProfileControlFor M) (fun _ => MarkedMomentProfileControlFor M) :=
  ⟨WholeMomentProfileControlFor.marked⟩


/-- Profile bounds apply to the evaluated models at their original height T. -/
theorem WholeMomentProfileControlFor.evaluated
    {M : SourceMomentModelsFor K c E}
    (h : WholeMomentProfileControlFor M) (hp : SourceMomentParameterControlFor M) :
    ∀ J : ℕ, ∀ A : ℝ, 0 ≤ A →
      ∃ C H a b : ℝ, 0 < C ∧ 0 ≤ H ∧ 0 < a ∧ a < b ∧
        ∀ Z T (i : SourceMomentIndexFor K c E Z T), 1 ≤ Z → 1 ≤ T →
        ∀ s, ∀ d ∈ [inverseModelFor M i s, pairedModelFor M i s],
          Moments.UniformAmplify.ModelProfileControl d J A C H a b T := by
  intro J A hA
  obtain ⟨C, H, a, b, hC, hH, ha, hab, hbound⟩ := h J A hA
  refine ⟨C, H, a, b, hC, hH, ha, hab, ?_⟩
  intro Z T i hZ hT s d hd
  exact hbound Z T i hZ hT s (M.heights Z T i)
    (M.realShifts Z T i) (M.imagShifts Z T i)
    (hp Z T i).1 (hp Z T i).2.1 (hp Z T i).2.2 d hd


def markedModelEnergyFor (M : SourceMomentModelsFor K c E) {Z T}
    (i : SourceMomentIndexFor K c E Z T) : ℝ :=
  ∑ s : SixthUnitClasses K (places K c),
    inverseEnergy (inverseModelFor M i s) (inverseParametersFor i) (momentBaseFor i) 0
def pairedModelEnergyFor (M : SourceMomentModelsFor K c E) {Z T}
    (i : SourceMomentIndexFor K c E Z T) : ℝ :=
  ∑ s : SixthUnitClasses K (places K c),
    pairedEnergy (pairedModelFor M i s) (pairedParametersFor i) (momentBaseFor i) 0

def unmarkedBallEnergy (d : MomentData K c.family.omega (targetCharacter K c))
    (U D : ℝ) : ℝ :=
  ∑ u ∈ (d.rows (2 * U)).filter (SixthPowerFreeIdeal (K := K)),
    ‖inversePolynomial d u D 0‖ ^ 2
def amplifiedModelEnergyFor (M : SourceMomentModelsFor K c E) {Z T}
    (i : SourceMomentIndexFor K c E Z T) : ℝ :=
  ∑ s : SixthUnitClasses K (places K c),
    unmarkedBallEnergy (unmarkedModelFor M i s)
      (momentBaseFor i) ((momentBaseFor i) ^ (momentWitnessFor i).inverseLength)

/-- Constants are for the ENTIRE actual index/profile family. Height order
and ceiling precede tau; threshold and scalar may depend on that fixed tau. -/
def UniformMomentBoundFor
    (energy : ∀ Z T, SourceMomentIndexFor K c E Z T → ℝ)
    (power : ∀ Z T, SourceMomentIndexFor K c E Z T → ℝ)
    (eligible : ∀ Z T, SourceMomentIndexFor K c E Z T → Prop) : Prop :=
  ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∃ Z₀ k : ℝ, 1 ≤ Z₀ ∧ 0 ≤ k ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ∀ i : SourceMomentIndexFor K c E Z (Z ^ τ),
        51 / 100 < (momentBlockFor i).bin → eligible Z (Z ^ τ) i →
          energy Z (Z ^ τ) i ≤
            k * (momentBaseFor i) ^ (power Z (Z ^ τ) i + c.family.lamA) * (1 + Z ^ τ) ^ A


/-- The zero-slot canonical input controls complete rows and a common
majorant over every strict smaller polynomial scale of the same inherited
profile.  This is the scale-supremum input used in the paper's sixth-power
amplification, before independent U,D are optimized. -/
def StrictUnmarkedMomentBoundFor (M : SourceMomentModelsFor K c E) : Prop :=
  Moments.UniformAmplify.CompleteUnmarkedScaleSupBound M.unmarked


structure CanonicalInverseModelBoundsFor (M : SourceMomentModelsFor K c E) : Prop where
  marked : UniformMomentBoundFor
    (fun _ _ i => markedModelEnergyFor M i)
    (fun _ _ i => rowWidthFor i)
    (fun _ _ i => inverseCapacityFor i)
  unmarked_strict : StrictUnmarkedMomentBoundFor M

def SixthPowerMaskIdentityFor (M : SourceMomentModelsFor K c E) : Prop :=
  ∀ U D s ξ σ τ (u : NonzeroIdeal K) (a : ExteriorIdeal K (places K c)),
    (M.unmarked U D s ξ σ τ).allowedRow u →
      (M.unmarked U D s ξ σ τ).allowedRow (u * a.val ^ 6) ∧
      (M.unmarked U D s ξ σ τ).rowCharacter (u * a.val ^ 6) =
        (M.unmarked U D s ξ σ τ).rowCharacter u ∧
      ∀ I : Ideal (𝓞 K),
        maskValue (M.unmarked U D s ξ σ τ) (u * a.val ^ 6) I =
          maskValue (M.unmarked U D s ξ σ τ) u I *
            (if IsCoprime I a.val.val then 1 else 0)

def AmplifiedIndependentMomentBoundFor (M : SourceMomentModelsFor K c E) : Prop :=
  ∀ a ε : ℝ, 0 < a → 0 < ε →
    ∃ C A h : ℝ, 0 < C ∧ 0 ≤ A ∧ 0 < h ∧
      ∀ U D : ℝ, 1 ≤ U → 1 ≤ D →
      ∀ (ξ : Fin M.dimension → ℝ) σ τ,
        ‖ξ‖ ≤ (U * D) ^ h → (∀ u, ‖σ u‖ ≤ 8) →
        (∀ u, ‖τ u‖ ≤ 1 + ‖ξ‖) →
        (∑ s : SixthUnitClasses K (places K c),
          unmarkedBallEnergy (M.unmarked U D s ξ σ τ) U D) ≤
          C * max U (U ^ (1 / 6 : ℝ) * D ^ (5 * (1 + a) / 6)) *
            (U * D) ^ ε * (1 + ‖ξ‖) ^ A


/-- These are inequalities for the ACTUAL selected finite prime products,
not arbitrary sublists in P. At kappa1 no zero-free premise is supplied. -/
def PairedPrimeProductBoundFor (M : SourceMomentModelsFor K c E) (κ : ℝ) : Prop :=
  UniformMomentBoundFor
    (fun _ _ i => ∑ s : SixthUnitClasses K (places K c),
      ∑ u ∈ pairedRows (pairedModelFor M i s) (pairedParametersFor i) (momentBaseFor i),
        ‖slotProduct (pairedModelFor M i s) u (momentBaseFor i) 0‖ ^ 2)
    (fun _ _ i => 1 + κ * selectedLengthFor i)
    (fun _ _ i => pairedCapacityFor i)


def physicalInverseEnergyFor {Z T} (i : SourceMomentIndexFor K c E Z T) : ℝ :=
  ∑ u ∈ (momentWitnessFor i).rows,
    ‖(momentWitnessFor i).inverseValue u *
      ∏ j ∈ i.selected, (momentAmplitudeFor i).slotValue j u‖ ^ 2
def physicalPlainEnergyFor {Z T} (i : SourceMomentIndexFor K c E Z T) : ℝ :=
  ∑ u ∈ (momentWitnessFor i).rows,
    ‖(momentWitnessFor i).plainValue u ^ 2 *
      ∏ j ∈ i.selected, (momentAmplitudeFor i).slotValue j u‖ ^ 2
def physicalUnmarkedEnergyFor {Z T} (i : SourceMomentIndexFor K c E Z T) : ℝ :=
  ∑ u ∈ (momentWitnessFor i).rows, ‖(momentWitnessFor i).inverseValue u‖ ^ 2


end HeckeSkeleton

#print axioms HeckeSkeleton.SourceMomentIndexFor
#print axioms HeckeSkeleton.SourceMomentModelsFor
#print axioms HeckeSkeleton.SourcePolynomialCalibrationFor
#print axioms HeckeSkeleton.SourceRowEligibilityFor
#print axioms HeckeSkeleton.WholeMomentProfileControlFor
#print axioms HeckeSkeleton.UniformMomentBoundFor
#print axioms HeckeSkeleton.WholeMomentProfileControlFor.evaluated
