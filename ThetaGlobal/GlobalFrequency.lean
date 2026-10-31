import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.NormNum

/-!
# Reflected frequency reconstruction on nonzero support

The full project index deliberately retains coefficients that vanish
locally.  Its map to frequency valuations is therefore not injective.
The explicit one-prime example below has exponent `1` in an inactive
branch and exponent `3 - 2 = 1` in an active branch.  In the latter
branch the ordinary `j = 0, e = 3` local Weyl coefficient vanishes.

On nonzero support, a newly active ordinary `j = 0` prime has numerator
exponent zero, and an active mark also has numerator exponent zero.
These facts make the optional active set exactly the set of negative
valuations.  The mandatory active primes are those of nonzero ordinary
digit.  Once that set is recovered, the squarefree/cube decomposition is
unique.  `supported_valuation_injective` proves this reconstruction.

The model records exterior valuation data only; the separate unit-sector
dictionary with actual rational frequencies remains an arithmetic step.
-/

noncomputable section
open scoped Classical

namespace ThetaGlobal.GlobalFrequency

variable {P : Type*}

structure Branch (P : Type*) where
  active : Set P
  a : P → ℕ
  c : P → ℕ
  n : P → ℕ

theorem Branch.ext {b b' : Branch P} (hactive : b.active = b'.active)
    (ha : b.a = b'.a) (hc : b.c = b'.c) (hn : b.n = b'.n) : b = b' := by
  cases b
  cases b'
  cases hactive
  cases ha
  cases hc
  cases hn
  rfl

/-- The fixed moving-row denominator has been subtracted from both
sides, leaving precisely the active frozen/mark denominator. -/
def valuation (b : Branch P) (p : P) : ℤ :=
  (b.a p : ℤ) + (b.c p : ℤ) + 3 * (b.n p : ℤ) -
    if p ∈ b.active then 2 else 0

/-- The valuation restrictions in the enlarged index before removing
locally zero coefficients. -/
structure RawAdmissible (b : Branch P) : Prop where
  a_outside : ∀ p, p ∉ b.active → b.a p = 0
  c_active : ∀ p, p ∈ b.active → b.c p = 0
  n_active : ∀ p, p ∈ b.active → b.n p = 0
  c_squarefree : ∀ p, b.c p ≤ 1
  a_digits : ∀ p, b.a p % 3 ≠ 2

/-- The extra local zero information required for an injective global
parametrization.  The hypothesis `optional_zero` is a support statement
from the exterior local table, not a global reflection conclusion. -/
structure Supported (mandatory : Set P) (b : Branch P) : Prop
    extends RawAdmissible b where
  mandatory_active : mandatory ⊆ b.active
  optional_zero : ∀ p, p ∈ b.active → p ∉ mandatory → b.a p = 0

theorem active_iff_mandatory_or_negative (mandatory : Set P) (b : Branch P)
    (hb : Supported mandatory b) (p : P) :
    p ∈ b.active ↔ p ∈ mandatory ∨ valuation b p < 0 := by
  constructor
  · intro hp
    by_cases hm : p ∈ mandatory
    · exact Or.inl hm
    · right
      have ha := hb.optional_zero p hp hm
      have hc := hb.c_active p hp
      have hn := hb.n_active p hp
      simp [valuation, hp, ha, hc, hn]
  · rintro (hm | hv)
    · exact hb.mandatory_active hm
    · by_contra hp
      have ha := hb.a_outside p hp
      simp only [valuation, hp, if_false, ha, Nat.cast_zero, zero_add, sub_zero] at hv
      omega

/-- For a fixed active branch, the frozen exponent and the
squarefree/cube exponents are determined by the frequency valuations. -/
theorem fixed_active_coordinates_unique (b b' : Branch P)
    (hb : RawAdmissible b) (hb' : RawAdmissible b')
    (hactive : b.active = b'.active) (hv : valuation b = valuation b') :
    b.a = b'.a ∧ b.c = b'.c ∧ b.n = b'.n := by
  have hpoint (p : P) : b.a p = b'.a p ∧ b.c p = b'.c p ∧ b.n p = b'.n p := by
    have he := congrFun hv p
    by_cases hp : p ∈ b.active
    · have hp' : p ∈ b'.active := hactive ▸ hp
      have hc := hb.c_active p hp
      have hc' := hb'.c_active p hp'
      have hn := hb.n_active p hp
      have hn' := hb'.n_active p hp'
      simp only [valuation, hp, hp', if_true, hc, hc', hn, hn', Nat.cast_zero,
        add_zero, mul_zero] at he
      omega
    · have hp' : p ∉ b'.active := hactive ▸ hp
      have ha := hb.a_outside p hp
      have ha' := hb'.a_outside p hp'
      have hc := hb.c_squarefree p
      have hc' := hb'.c_squarefree p
      simp only [valuation, hp, hp', if_false, ha, ha', Nat.cast_zero,
        zero_add, sub_zero] at he
      omega
  exact ⟨funext (fun p => (hpoint p).1), funext (fun p => (hpoint p).2.1),
    funext (fun p => (hpoint p).2.2)⟩

/-- The whole exterior numerical index is injective after deleting the
local zero branches. -/
theorem supported_valuation_injective (mandatory : Set P)
    (b b' : Branch P) (hb : Supported mandatory b) (hb' : Supported mandatory b')
    (hv : valuation b = valuation b') : b = b' := by
  have hactive : b.active = b'.active := by
    apply Set.ext
    intro p
    rw [active_iff_mandatory_or_negative mandatory b hb,
      active_iff_mandatory_or_negative mandatory b' hb', congrFun hv p]
  obtain ⟨ha, hc, hn⟩ := fixed_active_coordinates_unique b b'
    hb.toRawAdmissible hb'.toRawAdmissible hactive hv
  exact Branch.ext hactive ha hc hn

def inactiveDuplicate : Branch Unit where
  active := ∅
  a := fun _ => 0
  c := fun _ => 1
  n := fun _ => 0

def activeDuplicate : Branch Unit where
  active := Set.univ
  a := fun _ => 3
  c := fun _ => 0
  n := fun _ => 0

theorem inactiveDuplicate_admissible : RawAdmissible inactiveDuplicate where
  a_outside := by intros; rfl
  c_active := by intro p hp; exact False.elim hp
  n_active := by intros; rfl
  c_squarefree := by intro p; change 1 ≤ 1; decide
  a_digits := by intro p; change (0 : ℕ) % 3 ≠ 2; decide

theorem activeDuplicate_admissible : RawAdmissible activeDuplicate where
  a_outside := by intro p hp; exact False.elim (hp (Set.mem_univ p))
  c_active := by intros; rfl
  n_active := by intros; rfl
  c_squarefree := by intro p; change (0 : ℕ) ≤ 1; decide
  a_digits := by intro p; change (3 : ℕ) % 3 ≠ 2; decide

/-- Two distinct raw indices have the same actual integer valuation. -/
theorem duplicate_same_valuation : valuation inactiveDuplicate = valuation activeDuplicate := by
  funext p
  norm_num [valuation, inactiveDuplicate, activeDuplicate]

theorem duplicate_indices_distinct : inactiveDuplicate ≠ activeDuplicate := by
  intro h
  have hs := congrArg Branch.active h
  have he : (Set.univ : Set Unit) = ∅ := hs.symm
  have : (Unit.unit : Unit) ∈ (∅ : Set Unit) := he ▸ Set.mem_univ Unit.unit
  exact this

theorem activeDuplicate_excluded_from_nonzero_support :
    ¬ Supported (∅ : Set Unit) activeDuplicate := by
  intro h
  have he := h.optional_zero Unit.unit (Set.mem_univ _) (by simp)
  norm_num [activeDuplicate] at he

end ThetaGlobal.GlobalFrequency
