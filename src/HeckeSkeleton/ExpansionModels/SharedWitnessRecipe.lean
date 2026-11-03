import HeckeGeneral.Analysis.DecomposedWitnessMomentData
import HeckeGeneral.Analysis.MomentSlotScaleChange
import HeckeGeneral.Analysis.TInputSeparatedProfiles

/-!
# Shared actual Hecke-polynomial recipe

Project adapter over the actual Hecke finite-polynomial definitions.

This file does not import `HeckeSkeleton` and does not define an arbitrary
`highExpansion`.  It supplies the data constructor which the actual detector
and expansion should use together.  Both copies of the plain test are the
same actual test.  Inverse/plain supports, complete masks, row characters and
all physical slots are preserved by selected-slot reindexing.

The data arguments are finite backgrounds, actual tests and actual arithmetic
rows.  No zero-detection theorem, saturation estimate, moment bound, or
analytic admissibility assertion is an argument of the calibration theorem.
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
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)
variable (ω ψ : HeckeCharacter K)

/-- Algebraic presentation data.  These are exactly the finite-background
requirements already present in `MomentData`, with no analytic estimate. -/
structure PolynomialPresentation where
  theta : Finset (HeckeCharacter K)
  theta_finite : ∀ θ ∈ theta, FiniteOrder θ
  inverseBackground : HeckeCharacter K
  direction : ℤ
  direction_spec : direction = -1 ∨ direction = 1
  directed_background : inverseBackground ^ (-direction) ∈ theta ∨
    ∃ θ ∈ theta, inverseBackground ^ (-direction) = ψ * θ
  plainBackground : HeckeCharacter K
  plain_background_spec :
    plainBackground = 1 ∨ plainBackground = ψ ∨ plainBackground = ψ⁻¹

/-- The empty ideal test is only used to evaluate physical prime slots, whose
definitions never inspect inverse/plain tests.  Detector tests remain V,W. -/
def zeroIdealTest : IdealTest K where
  profile _ _ _ := 0
  support _ _ _ := ∅
  support_spec _ _ _ _ := by simp

/-- The two plain factors are literally equal tests.  The complete-ideal row
enumeration and fixed S/6/coprimality masks come from the existing constructor. -/
def sharedMomentData (a : PolynomialPresentation K ψ)
    (g : SlotGeometry K) (slotCoefficient : Fin g.slotCount → HeckeCharacter K)
    (ξ : SixthUnitClasses K S) (V W : IdealTest K) : MomentData K ω ψ :=
  { decomposedWitnessMomentData K S P R ω ψ ξ V W W g with
    theta := a.theta
    theta_finite := a.theta_finite
    inverseBackground := a.inverseBackground
    direction := a.direction
    direction_spec := a.direction_spec
    directed_background := a.directed_background
    plainBackground := a.plainBackground
    plain_background_spec := a.plain_background_spec
    slotCoefficient := slotCoefficient }

variable {K S P R ω ψ}

theorem sharedMomentData_prime_independent_of_witness_tests
    (a : PolynomialPresentation K ψ) (g : SlotGeometry K)
    (c : Fin g.slotCount → HeckeCharacter K) (ξ : SixthUnitClasses K S)
    (V W V' W' : IdealTest K) (j : Fin g.slotCount)
    (I : NonzeroIdeal K) (Z t : ℝ) :
    primePolynomial (sharedMomentData K S P R ω ψ a g c ξ V W) j I Z t =
      primePolynomial (sharedMomentData K S P R ω ψ a g c ξ V' W') j I Z t := rfl

theorem sixthPowerFreePart_of_frequencyRow (u : FrequencyRow K S) :
    sixthPowerFreePart u.ideal.val = u.ideal.val := by
  apply (primeExponentEquiv (R := 𝓞 K)).injective
  apply Finsupp.ext
  intro p
  change primeExponents (sixthPowerFreePart u.ideal.val) p = primeExponents u.ideal.val p
  rw [primeExponents_sixthPowerFreePart, Nat.mod_eq_of_lt (u.sixthPowerFree p)]

theorem frequencyRow_eq_of_ideal_sector (u v : FrequencyRow K S)
    (hi : u.ideal = v.ideal) (hs : u.sector = v.sector) : u = v := by
  cases u
  cases v
  cases hi
  cases hs
  rfl

/-- Fixed-sector refinement uses this literal arithmetic embedding, not
an asserted bound on a possibly noninjective projection to ideals. -/
def frequencyRowIdealSectorEmbedding :
    FrequencyRow K S ↪ NonzeroIdeal K × SixthUnitClasses K S where
  toFun u := (u.ideal.val, u.sector)
  inj' := by
    intro u v h
    exact frequencyRow_eq_of_ideal_sector u v
      (Subtype.ext (congrArg Prod.fst h)) (congrArg Prod.snd h)

theorem decomposedFrequencyRow_of_frequencyRow (u : FrequencyRow K S) :
    decomposedFrequencyRow K S u.ideal u.sector = u := by
  have hi : exteriorSixthPowerFreePart S u.ideal = u.ideal :=
    Subtype.ext (sixthPowerFreePart_of_frequencyRow u)
  exact frequencyRow_eq_of_ideal_sector _ u hi rfl

theorem completeIdealRowCharacter_of_frequencyRow (u : FrequencyRow K S) :
    completeIdealRowCharacter K S P R u.sector u.ideal.val = R.character u := by
  rw [completeIdealRowCharacter_exterior, decomposedFrequencyRow_of_frequencyRow]

variable (K S P R ω ψ)

/-- A finite detector subdivision stores tests and lengths, never a second
independently chosen inverse/plain value.  Its rows may subsequently be
filtered by the actual detector or by amplitude bins. -/
structure WitnessRecipe where
  rows : Finset (FrequencyRow K S)
  inverseLength : ℝ
  plainLength : ℝ
  inverseTest : SixthUnitClasses K S → IdealTest K
  plainTest : SixthUnitClasses K S → IdealTest K

variable {K S P R ω ψ}

def WitnessRecipe.data (w : WitnessRecipe K S)
    (a : PolynomialPresentation K ψ) (g : SlotGeometry K)
    (c : Fin g.slotCount → HeckeCharacter K) (ξ : SixthUnitClasses K S) :
    MomentData K ω ψ :=
  sharedMomentData K S P R ω ψ a g c ξ (w.inverseTest ξ) (w.plainTest ξ)

/-- The source witness value is evaluated from the same actual finite ideal
sums that will be used by all marked and unmarked moment models. -/
def WitnessRecipe.toWitness (w : WitnessRecipe K S)
    (a : PolynomialPresentation K ψ) (g : SlotGeometry K)
    (c : Fin g.slotCount → HeckeCharacter K) (U : ℝ) :
    WitnessSubdivision (FrequencyRow K S) where
  rows := w.rows
  inverseLength := w.inverseLength
  plainLength := w.plainLength
  inverseValue u := inversePolynomial (w.data (P := P) (R := R) (ω := ω) a g c u.sector)
    u.ideal.val (U ^ w.inverseLength) 0
  plainValue u := plainPolynomial (w.data (P := P) (R := R) (ω := ω) a g c u.sector)
    (w.plainTest u.sector) u.ideal.val (U ^ w.plainLength) 0

def WitnessRecipe.selectedModel (w : WitnessRecipe K S)
    (a : PolynomialPresentation K ψ) (g : SlotGeometry K)
    (c : Fin g.slotCount → HeckeCharacter K) (d : ℝ) (hd : 0 < d)
    (J : Finset (Fin g.slotCount)) (ξ : SixthUnitClasses K S) : MomentData K ω ψ :=
  ((w.data (P := P) (R := R) (ω := ω) a g c ξ).changeSlotBase d hd).restrictSlots J

def WitnessRecipe.unmarkedModel (w : WitnessRecipe K S)
    (a : PolynomialPresentation K ψ) (g : SlotGeometry K)
    (c : Fin g.slotCount → HeckeCharacter K) (ξ : SixthUnitClasses K S) :
    MomentData K ω ψ :=
  { w.data (P := P) (R := R) (ω := ω) a g c ξ with
    geometry := zeroSlotGeometry K
    slotCoefficient := Fin.elim0 }

/-- Physical slot values use the label's fixed geometry and presentation,
independent of the witness subdivision, its cutoff, and its rowwise heights. -/
def physicalSlotValue (a : PolynomialPresentation K ψ) (g : SlotGeometry K)
    (c : Fin g.slotCount → HeckeCharacter K) (Z : ℝ)
    (j : Fin g.slotCount) (u : FrequencyRow K S) : ℂ :=
  primePolynomial (sharedMomentData K S P R ω ψ a g c u.sector
    (zeroIdealTest K) (zeroIdealTest K)) j u.ideal.val Z 0

/-- All five value identities needed by SourcePolynomialCalibration.  The
inverse and plain identities are definitional; the slot identity uses the
already proved actual change of base and selected-slot finite product. -/
theorem WitnessRecipe.polynomial_calibration (w : WitnessRecipe K S)
    (a : PolynomialPresentation K ψ) (g : SlotGeometry K)
    (c : Fin g.slotCount → HeckeCharacter K) (d : ℝ) (hd : 0 < d)
    (J : Finset (Fin g.slotCount)) {Z : ℝ} (hZ : 0 < Z)
    (u : FrequencyRow K S) :
    let W := w.toWitness (P := P) (R := R) (ω := ω) a g c (Z ^ d)
    let M := w.selectedModel (P := P) (R := R) (ω := ω) a g c d hd J u.sector
    let M₀ := w.unmarkedModel (P := P) (R := R) (ω := ω) a g c u.sector
    W.inverseValue u = inversePolynomial M u.ideal.val ((Z ^ d) ^ w.inverseLength) 0 ∧
    W.plainValue u = plainPolynomial M M.plainTest₁ u.ideal.val
      ((Z ^ d) ^ w.plainLength) 0 ∧
    W.plainValue u = plainPolynomial M M.plainTest₂ u.ideal.val
      ((Z ^ d) ^ w.plainLength) 0 ∧
    (∏ j ∈ J, physicalSlotValue (P := P) (R := R) (ω := ω) a g c Z j u) =
      slotProduct M u.ideal.val (Z ^ d) 0 ∧
    W.inverseValue u = inversePolynomial M₀ u.ideal.val
      ((Z ^ d) ^ w.inverseLength) 0 := by
  dsimp only
  refine ⟨rfl, rfl, rfl, ?_, rfl⟩
  symm
  rw [WitnessRecipe.selectedModel, selectedSlotProduct_changeSlotBase
    (w.data (P := P) (R := R) (ω := ω) a g c u.sector) d hd J u.ideal.val hZ 0]
  apply Finset.prod_congr rfl
  intro j _hj
  rfl

/-- Original character and complete common mask survive all slot operations. -/
theorem WitnessRecipe.character_and_mask (w : WitnessRecipe K S)
    (a : PolynomialPresentation K ψ) (g : SlotGeometry K)
    (c : Fin g.slotCount → HeckeCharacter K) (d : ℝ) (hd : 0 < d)
    (J : Finset (Fin g.slotCount)) (u : FrequencyRow K S)
    (I : Ideal (𝓞 K)) :
    (w.selectedModel (P := P) (R := R) (ω := ω) a g c d hd J u.sector).rowCharacter
      u.ideal.val = R.character u ∧
    (w.selectedModel (P := P) (R := R) (ω := ω) a g c d hd J u.sector).commonMask
      u.ideal.val I = completeIdealCommonMask K S u.ideal.val I := by
  exact ⟨completeIdealRowCharacter_of_frequencyRow (P := P) (R := R) u, rfl⟩

/-- The current skeleton's marked source cutoff cannot contain any member
of its physical dyadic shell.  This applies to every possible MomentData,
so changing the test or background cannot repair the cutoff mismatch. -/
theorem physical_dyadic_row_not_in_moment_rows
    (M : MomentData K ω ψ) (u : FrequencyRow K S) (U : ℝ)
    (hU : U < frequencyRowNorm K S u) :
    u.ideal.val ∉ M.rows U := by
  intro hu
  have hn := ((M.rows_spec U u.ideal.val).mp hu).2
  change frequencyRowNorm K S u ≤ U at hn
  exact (not_lt_of_ge hn) hU

/-- The same obstruction affects paired moments at the existing m=1,q=0. -/
theorem physical_dyadic_row_not_in_paired_rows
    (M : MomentData K ω ψ) (u : FrequencyRow K S) (U : ℝ)
    (a : RealParameters) (hm : a.m = 1) (hq : a.q = 0)
    (hU : U < frequencyRowNorm K S u) :
    u.ideal.val ∉ pairedRows M a U := by
  intro hu
  have hmem := (Finset.mem_filter.mp hu).1
  simp only [hm, hq, add_zero, Real.rpow_one] at hmem
  exact physical_dyadic_row_not_in_moment_rows M u U hU hmem

/-- Full row locality for genuine IdealTest constructors.  A test recipe
consumes only the parameters at the row currently being evaluated. -/
def rowLocalIdealTest {Parameter : Type*}
    (W : NonzeroIdeal K → Parameter → IdealTest K)
    (p : NonzeroIdeal K → Parameter) : IdealTest K :=
  IdealTest.rowwise fun u => W u (p u)

theorem rowLocalIdealTest_local {Parameter : Type*}
    (W : NonzeroIdeal K → Parameter → IdealTest K)
    (p q : NonzeroIdeal K → Parameter) (u : NonzeroIdeal K)
    (hpq : p u = q u) :
    (∀ t y, (rowLocalIdealTest W p).profile u t y =
      (rowLocalIdealTest W q).profile u t y) ∧
    (∀ t D, (rowLocalIdealTest W p).support u t D =
      (rowLocalIdealTest W q).support u t D) := by
  constructor <;> intros <;> simp only [rowLocalIdealTest, IdealTest.rowwise, hpq]

end HeckeGeneral.Analysis.ExpansionRecipe
