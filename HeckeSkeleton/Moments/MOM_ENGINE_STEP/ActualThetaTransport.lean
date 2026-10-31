import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CharacterRecipePreservation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteThetaAction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondExceptionalPartition

/-!
# The actual finite correction action, without a subgroup hypothesis

Only the particular correction attached to each original row must
permute the original finite theta set.  The source character identity
then implies identical exceptional status.  This is a raw finite
arithmetic dictionary: it contains no row count, moment estimate or
final child admissibility.

The inverse correction and simultaneous whole conjugation are derived.
Conjugating only one of the characters is stated with that inverse
character explicitly; it is not silently identified with the original
character's exceptional status.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F]

/-- MOM_BASE supplies the actual correction action and the individual
source-character identity.  The correction may depend on the original
row, but neither field depends on the Fourier parameters. -/
structure ActualThetaTransport (theta : Finset (HeckeCharacter F)) (H : Type*) where
  correction : H → HeckeCharacter F
  action : ∀ h, ActualThetaAction theta (correction h)
  left : H → HeckeCharacter F
  right : H → HeckeCharacter F
  character : ∀ h, left h = correction h * right h

namespace ActualThetaTransport

variable {theta : Finset (HeckeCharacter F)} {H : Type*}
variable (T : ActualThetaTransport theta H)

def exceptional (h : H) : Prop := T.left h ∈ theta

theorem same_exceptional (h : H) : T.left h ∈ theta ↔ T.right h ∈ theta := by
  rw [T.character h]
  exact (T.action h).mul_mem_iff (T.right h)

theorem right_exceptional (h : H) : T.right h ∈ theta ↔ T.exceptional h :=
  (T.same_exceptional h).symm

theorem ratio_eq_correction (h : H) : T.left h / T.right h = T.correction h := by
  rw [T.character h]
  group

/-- The actual finite-set action supplies the existing exceptional
partition. The subgroup consists of corrections stabilizing theta;
it is not a subgroup presentation of theta itself. -/
def toPairedFiniteCharacters : PairedFiniteCharacters theta H where
  subgroup := ActualThetaAction.stabilizer theta
  action χ hχ := hχ
  left := T.left
  right := T.right
  ratio_mem h := by
    change ActualThetaAction theta (T.left h / T.right h)
    rw [T.ratio_eq_correction h]
    exact T.action h

@[simp] theorem toPairedFiniteCharacters_exceptional (h : H) :
    T.toPairedFiniteCharacters.exceptional h ↔ T.exceptional h := Iff.rfl

@[simp] theorem toPairedFiniteCharacters_mem_subgroup (χ : HeckeCharacter F) :
    χ ∈ T.toPairedFiniteCharacters.subgroup ↔ ActualThetaAction theta χ := Iff.rfl

theorem reciprocal_character (h : H) : T.right h = (T.correction h)⁻¹ * T.left h := by
  rw [T.character h]
  group

theorem whole_conjugate_character (h : H) :
    (T.left h)⁻¹ = (T.correction h)⁻¹ * (T.right h)⁻¹ := by
  rw [T.character h]
  group

/-- Both whole-conjugated characters have the same exceptional status,
even when inversion does not preserve theta itself. -/
theorem whole_conjugate_exceptional (h : H) :
    (T.left h)⁻¹ ∈ theta ↔ (T.right h)⁻¹ ∈ theta := by
  rw [T.whole_conjugate_character h]
  exact (T.action h).inv_mul_mem_iff ((T.right h)⁻¹)

def swap : ActualThetaTransport theta H where
  correction h := (T.correction h)⁻¹
  action h := (T.action h).inv
  left := T.right
  right := T.left
  character := T.reciprocal_character

def wholeConjugate : ActualThetaTransport theta H where
  correction h := (T.correction h)⁻¹
  action h := (T.action h).inv
  left h := (T.left h)⁻¹
  right h := (T.right h)⁻¹
  character := T.whole_conjugate_character

def comap {J : Type*} (f : J → H) : ActualThetaTransport theta J where
  correction h := T.correction (f h)
  action h := T.action (f h)
  left h := T.left (f h)
  right h := T.right (f h)
  character h := T.character (f h)

/-- When the literal source formula has a conjugated right character,
the primitive product identity is recorded with that exact orientation.
The resulting right exception is about right^-1, with no extra closure
assumption hidden in the interpretation. -/
def ofConjugatedRight
    (correction left right : H → HeckeCharacter F)
    (action : ∀ h, ActualThetaAction theta (correction h))
    (character : ∀ h, left h = correction h * (right h)⁻¹) :
    ActualThetaTransport theta H where
  correction := correction
  action := action
  left := left
  right h := (right h)⁻¹
  character := character

theorem conjugated_right_exceptional
    (correction left right : H → HeckeCharacter F)
    (action : ∀ h, ActualThetaAction theta (correction h))
    (character : ∀ h, left h = correction h * (right h)⁻¹) (h : H) :
    left h ∈ theta ↔ (right h)⁻¹ ∈ theta :=
  (ofConjugatedRight correction left right action character).same_exceptional h

theorem nonexceptional_left (h : H) (hh : ¬ T.exceptional h) : T.left h ∉ theta := hh

theorem nonexceptional_right (h : H) (hh : ¬ T.exceptional h) : T.right h ∉ theta := by
  intro hmem
  exact hh ((T.right_exceptional h).mp hmem)

/-- Actual raw data and their literal row maps use the same finite
classification.  The zero-slot exclusion is proved from the original
principal membership condition, so it also survives deleting the last
slot.  No moment inequality is a premise. -/
theorem actual_nonexceptional {X : Type*} {ω ψ : HeckeCharacter F}
    (left right : X → MomentData F ω ψ) (a b : RealParameters)
    (leftRow rightRow : H → HeckeGeneral.Analysis.NonzeroIdeal F)
    (left_theta : ∀ ξ, (left ξ).theta = theta)
    (right_theta : ∀ ξ, (right ξ).theta = theta)
    (left_character : ∀ ξ h, (left ξ).rowCharacter (leftRow h) = T.left h)
    (right_character : ∀ ξ h, (right ξ).rowCharacter (rightRow h) = T.right h)
    (left_principal : ∀ ξ u,
      (left ξ).plainBackground * (left ξ).rowCharacter u = 1 →
        (left ξ).rowCharacter u ∈ (left ξ).theta)
    (right_principal : ∀ ξ u,
      (right ξ).plainBackground * (right ξ).rowCharacter u = 1 →
        (right ξ).rowCharacter u ∈ (right ξ).theta)
    (ξ : X) (h : H) (hh : ¬ T.exceptional h) :
    (if a.z = 0 then (left ξ).plainBackground * (left ξ).rowCharacter (leftRow h) ≠ 1
      else (left ξ).rowCharacter (leftRow h) ∉ (left ξ).theta) ∧
    (if b.z = 0 then (right ξ).plainBackground * (right ξ).rowCharacter (rightRow h) ≠ 1
      else (right ξ).rowCharacter (rightRow h) ∉ (right ξ).theta) := by
  have hl : (left ξ).rowCharacter (leftRow h) ∉ (left ξ).theta := by
    rw [left_theta ξ, left_character ξ h]
    exact T.nonexceptional_left h hh
  have hr : (right ξ).rowCharacter (rightRow h) ∉ (right ξ).theta := by
    rw [right_theta ξ, right_character ξ h]
    exact T.nonexceptional_right h hh
  constructor
  · split_ifs
    · exact fun he => hl (left_principal ξ _ he)
    · exact hl
  · split_ifs
    · exact fun he => hr (right_principal ξ _ he)
    · exact hr

end ActualThetaTransport

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualThetaAction.inv
#print axioms HeckeSkeleton.Moments.EngineStep.ActualThetaTransport.toPairedFiniteCharacters
#print axioms HeckeSkeleton.Moments.EngineStep.ActualThetaTransport.whole_conjugate_exceptional
#print axioms HeckeSkeleton.Moments.EngineStep.ActualThetaTransport.actual_nonexceptional
