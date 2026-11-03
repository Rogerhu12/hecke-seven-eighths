import HeckeGeneral.Arithmetic.SIntegerModulus
import HeckeGeneral.Arithmetic.SIntegerOrbits
import Mathlib.NumberTheory.NumberField.ClassNumber

/-! Actual finite ideal-class reduction of the moving
ordinary period. This supplies a scalar ideal equality; the trace-lattice
image identity, norm scale and compact inverse-map estimate are still
separate obligations. No principal ideal assumption is made on O_K. -/

noncomputable section
namespace HeckeGeneral.Arithmetic
open NumberField IsDedekindDomain
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

/-- An actual nonzero integral representative for each class. The index
is the full finite class group; no ideal sector is discarded. -/
def periodClassRepresentative (q : ClassGroup (𝓞 K)) : (Ideal (𝓞 K))⁰ :=
  Classical.choose (ClassGroup.mk0_surjective q)

@[simp] theorem periodClassRepresentative_class (q : ClassGroup (𝓞 K)) :
    ClassGroup.mk0 (periodClassRepresentative K q) = q :=
  Classical.choose_spec (ClassGroup.mk0_surjective q)

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (M : (Ideal (𝓞 K))⁰)

/-- The actual ordinary period, including a supplied nonzero ordinary
conductor ideal. Its underlying ideal is literally `(contraction(c) * P_S) * M`. -/
def sIntegerMovingPeriod (c : NonzeroRingElements (S.integer K)) :
    (Ideal (𝓞 K))⁰ :=
  (⟨sIntegerModulusContraction K S c.val,
      mem_nonZeroDivisors_of_ne_zero
        (sIntegerModulusContraction_ne_bot K S c.val c.property)⟩ *
    (∏ v : S, (⟨v.val.asIdeal,
      mem_nonZeroDivisors_of_ne_zero v.val.ne_bot⟩ : (Ideal (𝓞 K))⁰))) * M

/-- The moving period is a genuine scalar multiple of one member of the
fixed finite family. The scalar is in K itself, not a chosen FractionRing. -/
theorem exists_movingPeriod_class_scalar
    (c : NonzeroRingElements (S.integer K)) :
    ∃ q : ClassGroup (𝓞 K), ∃ x : K, ∃ hx : x ≠ 0,
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
          ((periodClassRepresentative K q).val : FractionalIdeal (𝓞 K)⁰ K) =
        ((sIntegerMovingPeriod K S M c).val : FractionalIdeal (𝓞 K)⁰ K) := by
  let P := sIntegerMovingPeriod K S M c
  let q := ClassGroup.mk0 P
  obtain ⟨x, hx, heq⟩ :=
    (ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring K).mp
      (periodClassRepresentative_class K q)
  exact ⟨q, x, hx, heq⟩

end HeckeGeneral.Arithmetic
