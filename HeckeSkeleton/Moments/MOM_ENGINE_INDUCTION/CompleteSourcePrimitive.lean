import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MovingRecipeArithmetic
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActualAtomPhases
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OriginalAtomConsumers
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.DataPrimitiveExtension
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.PrimitiveReflectionCalibration

/-!
# The concrete complete-row dictionary in the recursive source family

The additional data primitive is the canonical original-moving-row recipe on
every allowed ideal. Its original factors, powers, finite correction and
remaining ideal are fixed throughout the row sum. The literal full Boolean
mask, the original fixed theta set containing
every slot coefficient, and actual independence of the final
evaluation-time argument. None of its fields
is a polynomial estimate, a completed local output, or an arbitrarily
chosen arithmetic phase dictionary.

The original root can have row-dependent plain profiles. A norm-profile
recipe is therefore constructed only after the actual two-plain Mellin
replacement. The arithmetic atoms and their phase identity at every
original quotient point are derived from the complete-row dictionary.
The same construction applies after slots disappear, because its domain
is all allowed rows rather than the parent's old paired-row filter.

The moving recipe is the canonical CompleteMovingRowRecipe; the atom and
per-atom phase interfaces retain their original quotient and complete row.
The source theta specialization is kept in a separate actual-source module.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical

universe u

variable {K : Type} [Field K] [NumberField K] {c : TargetContext K}

/-- Actual source data before any finite polynomial is evaluated. The
remaining ideal depends on the model, but not on its arithmetic row. -/
structure CompleteSourceData (c : TargetContext K) (theta : Finset (HeckeCharacter K))
    (d : MomentData K c.family.omega (targetCharacter K c)) where
  recipe : EngineStep.CompleteMovingRowRecipe (axiomChoice K c).A
    (probeData K c) (momentRowCharacters K c) (fun _ : PUnit => d)
  theta_eq : d.theta = theta
  slot_characters : ∀ i, d.slotCoefficient i ∈ theta
  timeIndependent : ProfileTimeIndependent d

/-- This predicate is added before the actual reflection factory creates
its child labels. Its witness consists only of original data identities. -/
def completeSourcePrimitive (c : TargetContext K) (theta : Finset (HeckeCharacter K))
    (d : MomentData K c.family.omega (targetCharacter K c)) : Prop :=
  Nonempty (CompleteSourceData c theta d)

namespace CompleteSourceData

variable {theta : Finset (HeckeCharacter K)}
variable {d : MomentData K c.family.omega (targetCharacter K c)}

/-- Compatibility accessor for the canonical recipe. The original factors,
correction and remaining ideal are not reconstructed from a mask identity. -/
def rows (D : CompleteSourceData c theta d) := D.recipe

/-- The exact effective coprimality ideal appearing in the canonical full
joint budget. The original remaining ideal remains `D.recipe.remaining`. -/
def remaining (D : CompleteSourceData c theta d) : NonzeroIdeal K :=
  D.recipe.moving.fullMaskSupport D.recipe.remaining

/-- This equality preserves the original mask even for nonsquarefree
remaining ideals. It makes no norm assertion on the original ideal. -/
theorem mask (D : CompleteSourceData c theta d) (u : NonzeroIdeal K)
    (I : Ideal (𝓞 K)) :
    d.commonMask u I = (completeIdealCommonMask K (places K c) u I &&
      decide (IsCoprime I D.remaining.val)) :=
  completeMovingRowRecipe_mask D.recipe PUnit.unit u I

/-- Only literal fields are transported. In particular, the selected
sector function and the fixed remaining ideal are kept verbatim. -/
def transport (D : CompleteSourceData c theta d)
    (other : MomentData K c.family.omega (targetCharacter K c))
    (allowed : ∀ u, other.allowedRow u → d.allowedRow u)
    (character : other.rowCharacter = d.rowCharacter)
    (mask : other.commonMask = d.commonMask) (htheta : other.theta = d.theta)
    (hslots : ∀ i, other.slotCoefficient i ∈ theta)
    (htime : ProfileTimeIndependent other) : CompleteSourceData c theta other where
  recipe := D.recipe.ofAllowedSubset (other := fun _ : PUnit => other)
    (fun _ u hu => allowed u hu) (fun _ => character)
    (fun _ => mask) (fun _ => htheta)
  theta_eq := htheta.trans D.theta_eq
  slot_characters := hslots
  timeIndependent := htime

def freezeMomentTime (D : CompleteSourceData c theta d) (time : ℝ) :
    CompleteSourceData c theta (EngineInduction.freezeMomentTime d time) :=
  D.transport _ (fun _ hu => hu) rfl rfl rfl D.slot_characters
    (profileTimeIndependent_freezeMomentTime d time)

/-- Both arithmetic dictionaries survive the actual common-frequency
normalization. No row-independence premise on the original tests occurs. -/
def normalizedMellinPlainData (D : CompleteSourceData c theta d)
    (B₁ B₂ : SmoothAnnularTest) (P : ℝ) (hP : 1 ≤ P)
    (E : ℝ) (hE : 1 ≤ E) (J : ℕ) (frequency : ℝ × ℝ) :
    CompleteSourceData c theta
      (EngineInduction.normalizedMellinPlainData d B₁ B₂ P hP E hE J frequency) :=
  D.transport _ (fun _ hu => hu) rfl rfl rfl D.slot_characters
    (normalizedMellinPlainData_timeIndependent d D.timeIndependent
      B₁ B₂ P hP E hE J frequency)

/-- The actual reflection constructor changes one plain profile and
its length. All full-row arithmetic fields, original theta and slot
coefficients survive literally; no new slot character is admitted. -/
def fixedLineReflectionChild (n : Node K c.family.omega (targetCharacter K c))
    (D : CompleteSourceData c theta n.data) (first : Bool)
    (U E : ℝ) (hE : 1 ≤ E) (J : ℕ) (x : (ℕ × Bool) × ℝ) :
    CompleteSourceData c theta (n.fixedLineReflectionChild first U E hE J x).data :=
  D.transport _ (fun _ hu => hu) rfl rfl rfl D.slot_characters
    (D.timeIndependent.normalizedOrdinaryPowerChild first
      (reflectionFixedLine x.1.2) (-x.2) E hE J)

/-- Original ideal and prime atoms are constructed from the fixed
remaining mask and complete row character, not supplied as a new field. -/
def arithmeticAtoms (D : CompleteSourceData c theta d) :
    EngineStep.ParentArithmeticAtoms (ActualSIntegerOrbit K (places K c)) d :=
  completeMovingRowRecipe_arithmeticAtoms D.recipe PUnit.unit

/-- Every original quotient point has the actual complete residue phase,
including its exceptional zero support. The norm recipe is separate. -/
theorem phase_dictionary (D : CompleteSourceData c theta d)
    (W : EngineStep.NormProfileRecipe (fun _ : PUnit => d))
    (a : RealParameters) (U t Y₁ Y₂ : ℝ) :
    let raw := (D.arithmeticAtoms.constantAtoms W a U t).raw Y₁ Y₂
    (∀ I ∈ raw.leftColumns, ∀ q : ActualSIntegerOrbit K (places K c),
      raw.leftPhase q I = EngineStep.actualIdealResidue (A := (axiomChoice K c).A)
        (σ := complexEmbedding K c) I.val q.out.val) ∧
    (∀ I ∈ raw.rightColumns, ∀ q : ActualSIntegerOrbit K (places K c),
      raw.rightPhase q I = EngineStep.actualIdealResidue (A := (axiomChoice K c).A)
        (σ := complexEmbedding K c) I.val q.out.val) ∧
    (∀ i, ∀ p ∈ raw.slotColumns i, ∀ q : ActualSIntegerOrbit K (places K c),
      raw.primePhase q i p = EngineStep.actualIdealResidue (A := (axiomChoice K c).A)
        (σ := complexEmbedding K c) p.asIdeal q.out.val) :=
  completeMovingRowRecipe_actual_phase_dictionary c D.recipe PUnit.unit W a U t Y₁ Y₂

/-- The same original orbit dictionary may also be transported directly
through the literal fixed-line constructor. This uses the canonical
arithmetic transport and retains its row map and phase arrays. -/
def fixedLineArithmeticAtoms (n : Node K c.family.omega (targetCharacter K c))
    (D : CompleteSourceData c theta n.data) (first : Bool)
    (U E : ℝ) (hE : 1 ≤ E) (J : ℕ) (x : (ℕ × Bool) × ℝ) :
    EngineStep.ParentArithmeticAtoms (ActualSIntegerOrbit K (places K c))
      (n.fixedLineReflectionChild first U E hE J x).data :=
  arithmeticAtoms_fixedLineReflectionChild n D.arithmeticAtoms first U E hE J x

/-- The literal unlabelled Mellin input retains all source data. It is
not asserted earlier than its original recursive node. -/
def mellinStrictModel {Ω : Type u} [MeasurableSpace Ω]
    (n : Node K c.family.omega (targetCharacter K c))
    (D : CompleteSourceData c theta n.data)
    (cap J : ℕ) (A a b : ℝ) (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b)
    (P : ℝ) (hP : 1 ≤ P) (frequency : ℝ × ℝ) :
    CompleteSourceData c theta
      (n.mellinStrictModel (Ω := Ω) cap J A a b hA ha hab P hP frequency).data :=
  (D.freezeMomentTime 0).normalizedMellinPlainData
    (annularPlateau a b ha hab) (annularPlateau a b ha hab)
    (2 * P) (by linarith)
    (mellinStrictEnvelope (K := K) (ω := c.family.omega) (ψ := targetCharacter K c)
      (Ω := Ω) cap J A a b hA ha hab)
    (mellinStrictEnvelope_one_le (K := K) (ω := c.family.omega) (ψ := targetCharacter K c)
      (Ω := Ω) cap J A a b hA ha hab) J frequency

end CompleteSourceData

/-- This is the literal preservation callback consumed by the real
finite-rank reflection factory. It mentions no branch output or energy. -/
theorem completeSourcePrimitive_fixedLine (theta : Finset (HeckeCharacter K)) :
    FixedLineDataPreserved (completeSourcePrimitive c theta) := by
  rintro n first U E hE J x ⟨D⟩
  exact ⟨CompleteSourceData.fixedLineReflectionChild n D first U E hE J x⟩

/-- Only the actual Mellin inputs have the new row-independent plain
profiles, for all final times and every allowed arithmetic row. -/
def Node.mellinStrictModel_normProfileRecipe {Ω : Type u} [MeasurableSpace Ω]
    (n : Node K c.family.omega (targetCharacter K c))
    (cap J : ℕ) (A a b : ℝ) (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b)
    (P : ℝ) (hP : 1 ≤ P) :
    EngineStep.NormProfileRecipe (fun frequency : ℝ × ℝ =>
      (n.mellinStrictModel (Ω := Ω) cap J A a b hA ha hab P hP frequency).data) :=
  normProfileRecipe_normalizedMellinPlainData (EngineInduction.freezeMomentTime n.data 0)
    (annularPlateau a b ha hab) (annularPlateau a b ha hab)
    (2 * P) (by linarith)
    (mellinStrictEnvelope (K := K) (ω := c.family.omega) (ψ := targetCharacter K c)
      (Ω := Ω) cap J A a b hA ha hab)
    (mellinStrictEnvelope_one_le (K := K) (ω := c.family.omega) (ψ := targetCharacter K c)
      (Ω := Ω) cap J A a b hA ha hab) J

namespace Source

/-- Every literal recipe root has the whole-row recipe and remaining
ideal one. Its theta and slot-character identities are original source
data and are proved for the actual recipe in the separate specialization.
An arbitrary RecipeFamily is not assumed to have finite slot characters. -/
def recipeRootCompleteSourceData
    (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
      c.geometry (expansionShellAllowance K c)) {Z T : ℝ}
    (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
    (s : SixthUnitClasses K (places K c)) (theta : Finset (HeckeCharacter K))
    (htheta : (recipeRoot R i s).data.theta = theta)
    (hslots : ∀ j, (recipeRoot R i s).data.slotCoefficient j ∈ theta) :
    CompleteSourceData c theta (recipeRoot R i s).data where
  recipe := (show EngineStep.CompleteRowRecipe (axiomChoice K c).A
      (probeData K c) (momentRowCharacters K c)
      (fun _ : PUnit => (recipeRoot R i s).data) from {
        sector := fun _ => s
        exterior := fun _ _ hu => hu
        character := fun _ _ _ => rfl }).toMoving 1
      (fun _ => recipeRoot_remainingMask R i s)
  theta_eq := htheta
  slot_characters := hslots
  timeIndependent := recipeRoot_timeIndependent R i s

end Source

end HeckeSkeleton.Moments.EngineInduction
