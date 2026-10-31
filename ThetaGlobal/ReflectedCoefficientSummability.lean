import ThetaGlobal.ReflectedCoefficientModel
import ThetaGlobal.ReflectedIdealMajorant

/-!
# Marked reflected summability with the full scalar coefficient proved

This closes the standalone convergence theorem. The infinite arithmetic index
retains three independent ideals and all finite mark/frozen/unit choices.
The full scalar coefficient is the literal formula in ReflectedCoefficientModel.
The specialization to nonzero number-field ideals proves its counting input from
Mathlib; neither a global coefficient bound nor summability is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.ReflectedCoefficientSummability

open ThetaGlobal.ReflectedAbsolute ThetaGlobal.ReflectedCoefficientModel
open scoped Classical BigOperators nonZeroDivisors

variable {P I A U : Type} [CommMonoid A] [Finite U]

/-- Keep only the restrictions needed to make the two prime-set choices finite.
Every actual project's reflection index maps into this larger space. -/
abbrev AdmissibleIndex (d : Frame P I) :=
  {i : Index P I U // i.activeMarks ⊆ d.marks ∧ i.activeFrozen ⊆ d.frozenPrimes}

abbrev Branch (d : Frame P I) :=
  {a : Finset P // a ∈ d.marks.powerset} ×
  {f : Finset P // f ∈ d.frozenPrimes.powerset} × U

instance branch_finite (d : Frame P I) : Finite (Branch (U := U) d) := by
  dsimp only [Branch]
  infer_instance

def encode (d : Frame P I) (i : AdmissibleIndex (U := U) d) :
    Branch (U := U) d × I × I × I :=
  ((⟨i.val.activeMarks, Finset.mem_powerset.mpr i.property.1⟩,
    ⟨i.val.activeFrozen, Finset.mem_powerset.mpr i.property.2⟩,
    i.val.unitSector), i.val.numeratorFrozen, i.val.c, i.val.n)

theorem encode_injective (d : Frame P I) :
    Function.Injective (encode (U := U) d) := by
  intro i j h
  apply Subtype.ext
  have hmarks : i.val.activeMarks = j.val.activeMarks := congrArg (fun x => x.1.1.val) h
  have hfrozen : i.val.activeFrozen = j.val.activeFrozen := congrArg (fun x => x.1.2.1.val) h
  have hunit : i.val.unitSector = j.val.unitSector := congrArg (fun x => x.1.2.2) h
  have ha : i.val.numeratorFrozen = j.val.numeratorFrozen := congrArg (fun x => x.2.1) h
  have hc : i.val.c = j.val.c := congrArg (fun x => x.2.2.1) h
  have hn : i.val.n = j.val.n := congrArg (fun x => x.2.2.2) h
  cases i with
  | mk i hi =>
    cases j with
    | mk j hj =>
      cases i
      cases j
      cases hmarks
      cases hfrozen
      cases hunit
      cases ha
      cases hc
      cases hn
      rfl

variable (D : ScalarData P I A U) (d : Frame P I)

def scale (X : ℝ) (b : Branch (U := U) d) : ℝ :=
  X / (D.normI d.moving * D.normI (D.primeSetIdeal b.2.1.val) *
    D.normI (D.primeSetIdeal b.1.val)) ^ 2

theorem scale_pos {X : ℝ} (hX : 0 < X) (b : Branch (U := U) d) :
    0 < scale D d X b := by
  apply div_pos hX
  apply sq_pos_of_pos
  exact mul_pos
    (mul_pos (lt_of_lt_of_le zero_lt_one (D.normI_ge_one _))
      (lt_of_lt_of_le zero_lt_one (D.normI_ge_one _)))
    (lt_of_lt_of_le zero_lt_one (D.normI_ge_one _))

def arithmeticBound (b : Branch (U := U) d) : ℝ :=
  frozenBound D d b.2.1.val * rowBound D d

theorem arithmeticBound_nonneg (b : Branch (U := U) d) :
    0 ≤ arithmeticBound D d b :=
  mul_nonneg (frozenBound_nonneg D d _) (rowBound_nonneg D d)

/-- Exact literal coefficient and the project's three-ideal positive argument. -/
def reflectedTerm {C : Type*} (sector : AdmissibleIndex (U := U) d → C)
    (kernel : C → ℝ → ℂ) (X : ℝ) (i : AdmissibleIndex (U := U) d) : ℂ :=
  reflectedCoefficient D d i.val * kernel (sector i)
    (X * D.normI i.val.numeratorFrozen * D.normI i.val.c * D.normI i.val.n ^ 3 /
      (D.normI d.moving * D.normI (activeFrozenIdeal D i.val) *
        D.normI (activeMarkedIdeal D i.val)) ^ 2)

/-- Generic norm series version. The arithmetic bound is proved from the exact
finite-sum formula and local unit-norm facts, not an extra premise. -/
theorem summable_reflectedTerm {C : Type*}
    (hcount : Summable (fun a => inverseSquare (D.normI a)))
    (sector : AdmissibleIndex (U := U) d → C)
    (kernel : C → ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (htail : ∀ c y, 0 < y → ‖kernel c y‖ ≤ B * inverseSquare y)
    {X : ℝ} (hX : 0 < X) :
    Summable (reflectedTerm D d sector kernel X) := by
  have h := summable_reflected_of_quadratic_tail D.normI D.normI_ge_one hcount
    (encode d) (encode_injective d) sector (scale D d X) (arithmeticBound D d)
    (scale_pos D d hX) (arithmeticBound_nonneg D d)
    (fun i => reflectedCoefficient D d i.val)
    (fun i => norm_reflectedCoefficient_le D d i.val)
    kernel B hB htail
  apply h.congr
  intro i
  unfold reflectedTerm
  congr 1
  congr 1
  simp only [scale, encode, activeFrozenIdeal, activeMarkedIdeal, div_eq_mul_inv]
  ring

/-- Subsets of the ambient index can impose all actual arithmetic masks and
support restrictions without any additional convergence assumption. -/
theorem summable_reflectedTerm_on {C J : Type*}
    (hcount : Summable (fun a => inverseSquare (D.normI a)))
    (embed : J → AdmissibleIndex (U := U) d) (hembed : Function.Injective embed)
    (sector : AdmissibleIndex (U := U) d → C)
    (kernel : C → ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (htail : ∀ c y, 0 < y → ‖kernel c y‖ ≤ B * inverseSquare y)
    {X : ℝ} (hX : 0 < X) :
    Summable (fun j => reflectedTerm D d sector kernel X (embed j)) :=
  (summable_reflectedTerm D d hcount sector kernel B hB htail hX).comp_injective hembed

section NumberField

open NumberField
variable (K : Type) [Field K] [NumberField K]
variable (DK : ScalarData P ((Ideal (𝓞 K))⁰) A U)
variable (dK : Frame P ((Ideal (𝓞 K))⁰))

/-- Actual number-field ideal specialization. The only norm identification is
with the literal absolute ideal norm; Mathlib proves the required ideal sum. -/
theorem summable_numberField_reflectedTerm {C : Type*}
    (hNorm : ∀ a, DK.normI a = ReflectedIdealMajorant.positiveIdealNorm K a)
    (sector : AdmissibleIndex (U := U) dK → C)
    (kernel : C → ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (htail : ∀ c y, 0 < y → ‖kernel c y‖ ≤ B * inverseSquare y)
    {X : ℝ} (hX : 0 < X) :
    Summable (reflectedTerm DK dK sector kernel X) := by
  apply summable_reflectedTerm DK dK _ sector kernel B hB htail hX
  simpa only [hNorm] using ReflectedIdealMajorant.summable_positiveIdealNorm_inverseSquare K

/-- The same fully counted theorem for any subtype of nonzero integral ideals,
in particular ideals prime to the actual finite set S. No extension of residue
characters to ideals meeting S is necessary. -/
theorem summable_numberField_subtype_reflectedTerm
    (Q : (Ideal (𝓞 K))⁰ → Prop)
    (DS : ScalarData P {a : (Ideal (𝓞 K))⁰ // Q a} A U)
    (dS : Frame P {a : (Ideal (𝓞 K))⁰ // Q a}) {C : Type*}
    (hNorm : ∀ a, DS.normI a = ReflectedIdealMajorant.positiveIdealNorm K a.val)
    (sector : AdmissibleIndex (U := U) dS → C)
    (kernel : C → ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (htail : ∀ c y, 0 < y → ‖kernel c y‖ ≤ B * inverseSquare y)
    {X : ℝ} (hX : 0 < X) :
    Summable (reflectedTerm DS dS sector kernel X) := by
  apply summable_reflectedTerm DS dS _ sector kernel B hB htail hX
  simpa only [Function.comp_def, hNorm] using
    (ReflectedIdealMajorant.summable_positiveIdealNorm_inverseSquare K).subtype Q

end NumberField
end ThetaGlobal.ReflectedCoefficientSummability

