import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ProfileDictionary
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormIndependentProfiles

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Actual finite tests for the global original profile formula

The test evaluates the prescribed formula on every real argument. Its
finite support is obtained from the same original test at the divided
scale and an exact nonvanishing filter. Thus its values away from the
original finite source carrier are fixed as well. The new arithmetic
row and height do not change the already selected parent representative.
-/

noncomputable section
open scoped Classical NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

namespace ProfileFormula

theorem original_ne_zero_of_value_ne_zero (f : ProfileFormula)
    (ξ : EngineParameter) (x : ℝ) (h : f.value ξ x ≠ 0) :
    f.original (f.dilation * x) ≠ 0 := by
  intro hzero
  simp [value, hzero] at h

theorem scalar_ne_zero_of_value_ne_zero (f : ProfileFormula)
    (ξ : EngineParameter) (x : ℝ) (h : f.value ξ x ≠ 0) :
    f.scalar ≠ 0 := by
  intro hzero
  simp [value, hzero] at h

theorem argument_pos_of_value_ne_zero (f : ProfileFormula)
    (ξ : EngineParameter) (x : ℝ) (h : f.value ξ x ≠ 0) : 0 < x := by
  by_contra hx
  simp [value, hx] at h

theorem quotient_argument (dilation scale norm : ℝ) :
    norm / (scale / dilation) = dilation * (norm / scale) := by
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- The exact finite test obtained from the named original ideal test.
Its support construction works at every real scale, including zero. -/
def idealTest (f : ProfileFormula) (original : IdealTest K)
    (row : NonzeroIdeal K) (time : ℝ)
    (original_eq : ∀ x, f.original x = original.profile row time x)
    (ξ : EngineParameter) : IdealTest K where
  profile _ _ := f.value ξ
  support _ _ scale := (original.support row time (scale / f.dilation)).filter
    (fun I => f.value ξ (idealNorm K I / scale) ≠ 0)
  support_spec _ _ scale I := by
    rw [Finset.mem_filter]
    constructor
    · exact And.right
    · intro h
      refine ⟨?_, h⟩
      apply (original.support_spec row time (scale / f.dilation) I).mpr
      rw [quotient_argument, ← original_eq]
      exact original_ne_zero_of_value_ne_zero f ξ _ h

@[simp] theorem idealTest_profile (f : ProfileFormula) (original : IdealTest K)
    (row : NonzeroIdeal K) (time : ℝ)
    (original_eq : ∀ x, f.original x = original.profile row time x)
    (ξ : EngineParameter) (u : NonzeroIdeal K) (t x : ℝ) :
    (f.idealTest original row time original_eq ξ).profile u t x = f.value ξ x := rfl

/-- A prime occurrence keeps the length of its named original slot. -/
def primeWindow (f : ProfileFormula) (original : PrimeWindow K) (time : ℝ)
    (original_eq : ∀ x, f.original x = original.profile time x)
    (ξ : EngineParameter) : PrimeWindow K where
  length := original.length
  length_pos := original.length_pos
  profile _ := f.value ξ
  support _ scale := (original.support time (scale / f.dilation)).filter
    (fun p => f.value ξ ((Ideal.absNorm p.asIdeal : ℝ) / scale) ≠ 0)
  support_spec _ scale p := by
    rw [Finset.mem_filter]
    constructor
    · exact And.right
    · intro h
      refine ⟨?_, h⟩
      apply (original.support_spec time (scale / f.dilation) p).mpr
      rw [quotient_argument, ← original_eq]
      exact original_ne_zero_of_value_ne_zero f ξ _ h

@[simp] theorem primeWindow_profile (f : ProfileFormula) (original : PrimeWindow K)
    (time : ℝ) (original_eq : ∀ x, f.original x = original.profile time x)
    (ξ : EngineParameter) (t x : ℝ) :
    (f.primeWindow original time original_eq ξ).profile t x = f.value ξ x := rfl

@[simp] theorem primeWindow_length (f : ProfileFormula) (original : PrimeWindow K)
    (time : ℝ) (original_eq : ∀ x, f.original x = original.profile time x)
    (ξ : EngineParameter) :
    (f.primeWindow original time original_eq ξ).length = original.length := rfl

end ProfileFormula

namespace OriginalProfileFormula

variable {c : TargetContext K} {call : Call c} {input : ProfileInput call}
variable (f : OriginalProfileFormula input)

theorem inverse_original (hkind : f.kind = .inverse) (x : ℝ) :
    f.formula.original x = call.node.data.inverseTest.profile f.row f.time x := by
  rw [f.original, hkind]
  exact (input.raw.inverse_eq f.row f.time x).symm

theorem left_original (hkind : f.kind = .plain false) (x : ℝ) :
    f.formula.original x = call.node.data.plainTest₁.profile f.row f.time x := by
  rw [f.original, hkind]
  exact (input.raw.left_eq f.row f.time x).symm

theorem right_original (hkind : f.kind = .plain true) (x : ℝ) :
    f.formula.original x = call.node.data.plainTest₂.profile f.row f.time x := by
  rw [f.original, hkind]
  exact (input.raw.right_eq f.row f.time x).symm

theorem prime_original (slot : Fin call.node.data.geometry.slotCount)
    (hkind : f.kind = .prime slot) (x : ℝ) :
    f.formula.original x = (call.node.data.geometry.slots slot).profile f.time x := by
  rw [f.original, hkind]
  exact (input.raw.prime_eq slot f.time x).symm

def inverseTest (hkind : f.kind = .inverse) (ξ : EngineParameter) : IdealTest K :=
  f.formula.idealTest call.node.data.inverseTest f.row f.time (f.inverse_original hkind) ξ

def leftTest (hkind : f.kind = .plain false) (ξ : EngineParameter) : IdealTest K :=
  f.formula.idealTest call.node.data.plainTest₁ f.row f.time (f.left_original hkind) ξ

def rightTest (hkind : f.kind = .plain true) (ξ : EngineParameter) : IdealTest K :=
  f.formula.idealTest call.node.data.plainTest₂ f.row f.time (f.right_original hkind) ξ

def primeTest (slot : Fin call.node.data.geometry.slotCount)
    (hkind : f.kind = .prime slot) (ξ : EngineParameter) : PrimeWindow K :=
  f.formula.primeWindow (call.node.data.geometry.slots slot) f.time
    (f.prime_original slot hkind) ξ

@[simp] theorem inverseTest_profile (hkind : f.kind = .inverse)
    (ξ : EngineParameter) (u : NonzeroIdeal K) (t x : ℝ) :
    (f.inverseTest hkind ξ).profile u t x = f.formula.value ξ x := rfl

@[simp] theorem leftTest_profile (hkind : f.kind = .plain false)
    (ξ : EngineParameter) (u : NonzeroIdeal K) (t x : ℝ) :
    (f.leftTest hkind ξ).profile u t x = f.formula.value ξ x := rfl

@[simp] theorem rightTest_profile (hkind : f.kind = .plain true)
    (ξ : EngineParameter) (u : NonzeroIdeal K) (t x : ℝ) :
    (f.rightTest hkind ξ).profile u t x = f.formula.value ξ x := rfl

@[simp] theorem primeTest_profile (slot : Fin call.node.data.geometry.slotCount)
    (hkind : f.kind = .prime slot) (ξ : EngineParameter) (t x : ℝ) :
    (f.primeTest slot hkind ξ).profile t x = f.formula.value ξ x := rfl

@[simp] theorem primeTest_length (slot : Fin call.node.data.geometry.slotCount)
    (hkind : f.kind = .prime slot) (ξ : EngineParameter) :
    (f.primeTest slot hkind ξ).length = (call.node.data.geometry.slots slot).length := rfl

end OriginalProfileFormula

/-- Once the arithmetic constructor installs the two specified original
tests, norm independence holds on every allowed ideal, at every time. -/
def normProfiles_of_originalTests {c : TargetContext K} {call : Call c}
    {input : ProfileInput call}
    (data : EngineParameter → MomentData K c.family.omega (targetCharacter K c))
    (left right : OriginalProfileFormula input)
    (left_kind : left.kind = .plain false) (right_kind : right.kind = .plain true)
    (left_eq : ∀ ξ, (data ξ).plainTest₁ = left.leftTest left_kind ξ)
    (right_eq : ∀ ξ, (data ξ).plainTest₂ = right.rightTest right_kind ξ) :
    NormProfileRecipe data where
  left ξ _ := left.formula.value ξ
  right ξ _ := right.formula.value ξ
  left_eq ξ u _ t x := by rw [left_eq]; rfl
  right_eq ξ u _ t x := by rw [right_eq]; rfl

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.ProfileFormula.idealTest
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.ProfileFormula.primeWindow
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalProfileFormula.leftTest
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.normProfiles_of_originalTests
