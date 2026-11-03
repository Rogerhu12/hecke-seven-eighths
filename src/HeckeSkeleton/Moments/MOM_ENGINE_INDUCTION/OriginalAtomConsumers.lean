import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentArithmeticAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MellinProfileNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActualCommonReflection

/-!
# Original norm and arithmetic dictionaries for actual induction children

The canonical atom API is used from the immutable MOM_ENGINE_STEP commit
`fd6acc7066706d250730aed6a100e05d60f1b8f6`.  Its orbit type, row map,
arithmetic coefficients and phase arrays are retained by every consumer
below.  No copy of the canonical structures is introduced.

The two Mellin windows have literal norm profiles for every row and every
final time.  A one-plain reflection inherits the unreplaced profile from
the original norm recipe.  All profile normalizers are independent of
the arithmetic row.  The canonical `.constantAtoms` operation can then
be applied at arbitrary subsequent parameters, scales and times.

The dual functional equation uses the inverse whole character, but the
literal fixed-line child uses the original character after the proved
conjugation of its absolute square.  Thus its background is definitionally
the original background.  This file does not transport a dictionary to
an arbitrary moment model whose background has been inverted.

These are individual-profile and individual-arithmetic identities.  The
actual positive orbital chart and the periodic-column identification on
the new finite carrier remain separate source inputs.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical

universe u v

variable {K : Type} [Field K] [NumberField K]
variable {omegaCharacter psiCharacter : HeckeCharacter K}

/-- Both normalized Mellin profiles are independent of every original
row and of the final time, before any finite polynomial is formed. -/
def normProfileRecipe_normalizedMellinPlainData
    (d : MomentData K omegaCharacter psiCharacter)
    (B₁ B₂ : SmoothAnnularTest) (P : ℝ) (hP : 1 ≤ P)
    (E : ℝ) (hE : 1 ≤ E) (J : ℕ) :
    EngineStep.NormProfileRecipe
      (fun frequency : ℝ × ℝ =>
        normalizedMellinPlainData d B₁ B₂ P hP E hE J frequency) where
  left frequency _ y :=
    (((ordinaryProfileEnvelope E J frequency.1)⁻¹ : ℝ) : ℂ) *
      annularMellinWindow B₁ frequency.1 y
  right frequency _ y :=
    (((ordinaryProfileEnvelope E J frequency.2)⁻¹ : ℝ) : ℂ) *
      annularMellinWindow B₂ frequency.2 y
  left_eq frequency row _ time y := by
    change (((ordinaryProfileEnvelope E J frequency.1)⁻¹ : ℝ) : ℂ) *
      (annularMellinWindow B₁ frequency.1 y * profilePower 0 y) = _
    rw [profilePower_zero, mul_one]
  right_eq frequency row _ time y := by
    change (((ordinaryProfileEnvelope E J frequency.2)⁻¹ : ℝ) : ℂ) *
      (annularMellinWindow B₂ frequency.2 y * profilePower 0 y) = _
    rw [profilePower_zero, mul_one]

/-- Time freezing preserves a literal norm recipe on every allowed row. -/
def normProfileRecipe_freezeMomentTime
    (d : MomentData K omegaCharacter psiCharacter)
    (W : EngineStep.NormProfileRecipe (fun _ : PUnit => d)) (time : ℝ) :
    EngineStep.NormProfileRecipe (fun _ : PUnit => freezeMomentTime d time) where
  left _ _ := W.left PUnit.unit time
  right _ _ := W.right PUnit.unit time
  left_eq _ row hrow finalTime y := by
    change d.plainTest₁.profile row time y * profilePower 0 y = _
    rw [profilePower_zero, mul_one, W.left_eq PUnit.unit row hrow]
  right_eq _ row hrow finalTime y := by
    change d.plainTest₂.profile row time y * profilePower 0 y = _
    rw [profilePower_zero, mul_one, W.right_eq PUnit.unit row hrow]

/-- The selected plain becomes the actual fixed power window.  The
other norm profile is inherited from the parent's original dictionary. -/
def normProfileRecipe_ordinaryPowerChild {X : Type u}
    (d : MomentData K omegaCharacter psiCharacter)
    (W : EngineStep.NormProfileRecipe (fun _ : PUnit => d)) (first : Bool)
    (sigma frequency : X → ℝ) :
    EngineStep.NormProfileRecipe
      (fun x => ordinaryPowerChild K d first (sigma x) (frequency x)) where
  left x time y := if first then ordinaryPowerWindow (sigma x) (frequency x) y
    else W.left PUnit.unit time y
  right x time y := if first then W.right PUnit.unit time y
    else ordinaryPowerWindow (sigma x) (frequency x) y
  left_eq x row hrow time y := by
    cases first with
    | false => exact W.left_eq PUnit.unit row hrow time y
    | true =>
      change ordinaryPowerWindow (sigma x) (frequency x) y * profilePower 0 y = _
      rw [profilePower_zero, mul_one]
      simp
  right_eq x row hrow time y := by
    cases first with
    | false =>
      change ordinaryPowerWindow (sigma x) (frequency x) y * profilePower 0 y = _
      rw [profilePower_zero, mul_one]
      simp
    | true => exact W.right_eq PUnit.unit row hrow time y

/-- The genuine positive frequency envelope scales each original norm
profile uniformly in the arithmetic row. -/
def normProfileRecipe_normalizedOrdinaryPowerChild {X : Type u}
    (d : MomentData K omegaCharacter psiCharacter)
    (W : EngineStep.NormProfileRecipe (fun _ : PUnit => d)) (first : Bool)
    (sigma frequency : X → ℝ) (E : ℝ) (hE : 1 ≤ E) (J : ℕ) :
    EngineStep.NormProfileRecipe
      (fun x => normalizedOrdinaryPowerChild d first (sigma x) (frequency x) E hE J) where
  left x time y := (((ordinaryProfileEnvelope E J (frequency x))⁻¹ : ℝ) : ℂ) *
    (normProfileRecipe_ordinaryPowerChild d W first sigma frequency).left x time y
  right x time y := (((ordinaryProfileEnvelope E J (frequency x))⁻¹ : ℝ) : ℂ) *
    (normProfileRecipe_ordinaryPowerChild d W first sigma frequency).right x time y
  left_eq x row hrow time y := by
    change (((ordinaryProfileEnvelope E J (frequency x))⁻¹ : ℝ) : ℂ) *
      (ordinaryPowerChild K d first (sigma x) (frequency x)).plainTest₁.profile row time y = _
    rw [(normProfileRecipe_ordinaryPowerChild d W first sigma frequency).left_eq x row hrow]
  right_eq x row hrow time y := by
    change (((ordinaryProfileEnvelope E J (frequency x))⁻¹ : ℝ) : ℂ) *
      (ordinaryPowerChild K d first (sigma x) (frequency x)).plainTest₂.profile row time y = _
    rw [(normProfileRecipe_ordinaryPowerChild d W first sigma frequency).right_eq x row hrow]

/-- Both the line and frequency are common to all rows of a literal
fixed-line reflection child.  Its changed dyadic length is irrelevant
to the primitive profile identity. -/
def normProfileRecipe_fixedLineReflectionChild
    (n : Node K omegaCharacter psiCharacter)
    (W : EngineStep.NormProfileRecipe (fun _ : PUnit => n.data)) (first : Bool)
    (U E : ℝ) (hE : 1 ≤ E) (J : ℕ) :
    EngineStep.NormProfileRecipe
      (fun x : (ℕ × Bool) × ℝ => (n.fixedLineReflectionChild first U E hE J x).data) :=
  normProfileRecipe_normalizedOrdinaryPowerChild n.data W first
    (fun x : (ℕ × Bool) × ℝ => reflectionFixedLine x.1.2) (fun x => -x.2) E hE J

variable {Q : Type v}

/-- The same original orbit dictionary survives time freezing. -/
def arithmeticAtoms_freezeMomentTime
    {d : MomentData K omegaCharacter psiCharacter}
    (T : EngineStep.ParentArithmeticAtoms Q d) (time : ℝ) :
    EngineStep.ParentArithmeticAtoms Q (freezeMomentTime d time) :=
  T.transport _ id (fun _ h => h) rfl rfl rfl (fun _ => rfl)

/-- The two norm windows and the independent positive normalizers do
not alter any arithmetic atom, phase array, row map or common zero mask. -/
def arithmeticAtoms_normalizedMellinPlainData
    {d : MomentData K omegaCharacter psiCharacter}
    (T : EngineStep.ParentArithmeticAtoms Q d)
    (B₁ B₂ : SmoothAnnularTest) (P : ℝ) (hP : 1 ≤ P)
    (E : ℝ) (hE : 1 ≤ E) (J : ℕ) (frequency : ℝ × ℝ) :
    EngineStep.ParentArithmeticAtoms Q
      (normalizedMellinPlainData d B₁ B₂ P hP E hE J frequency) :=
  T.transport _ id (fun _ h => h) rfl rfl rfl (fun _ => rfl)

/-- This is the literal normalized power child with the original plain
background; the inverse dual character has already been conjugated in
the separate exact energy calibration. -/
def arithmeticAtoms_normalizedOrdinaryPowerChild
    {d : MomentData K omegaCharacter psiCharacter}
    (T : EngineStep.ParentArithmeticAtoms Q d)
    (first : Bool) (sigma frequency E : ℝ) (hE : 1 ≤ E) (J : ℕ) :
    EngineStep.ParentArithmeticAtoms Q
      (normalizedOrdinaryPowerChild d first sigma frequency E hE J) :=
  T.transport _ id (fun _ h => h) rfl rfl rfl (fun _ => rfl)

/-- The arithmetic dictionary on the final actual fixed-line child
uses exactly the original Q, row map and phase arrays. -/
def arithmeticAtoms_fixedLineReflectionChild
    (n : Node K omegaCharacter psiCharacter)
    (T : EngineStep.ParentArithmeticAtoms Q n.data) (first : Bool)
    (U E : ℝ) (hE : 1 ≤ E) (J : ℕ) (x : (ℕ × Bool) × ℝ) :
    EngineStep.ParentArithmeticAtoms Q
      (n.fixedLineReflectionChild first U E hE J x).data :=
  arithmeticAtoms_normalizedOrdinaryPowerChild T first
    (reflectionFixedLine x.1.2) (-x.2) E hE J

end HeckeSkeleton.Moments.EngineInduction
