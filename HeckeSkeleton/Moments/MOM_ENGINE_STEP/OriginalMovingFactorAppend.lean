import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalMovingSupportWindows
import DedekindZetaZeroFree.LFunctions.Hecke.ExteriorIdealEulerProducts
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Appending the original moving-factor lists

The appended data contain the old elements and exponents followed by
the new ones.  Their characters and complete ideals are computed from
the same original probe.  The displayed support is the radical of the
union of both original supports, including every exponent-zero factor.

The fixed remaining deletion ideal is kept separate and unchanged.
All complete-mask identities below use that same remaining ideal on
both sides; only the new displayed moving support is appended.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open UniqueFactorizationMonoid HeckePort.IdealMobiusDivisorSum HeckePort.Moments
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical CommonSupportMass

namespace OriginalMovingFactors

variable {K : Type} [Field K] [NumberField K] {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable (D E : OriginalMovingFactors A P R)

/-- Literal concatenation.  No multiplication of elements or reduction
of exponents is performed before the original displayed support is
computed. -/
def append : OriginalMovingFactors A P R where
  count := D.count + E.count
  element := Fin.append D.element E.element
  power := Fin.append D.power E.power

@[simp] theorem append_count : (D.append E).count = D.count + E.count := rfl

@[simp] theorem append_element_left (i : Fin D.count) :
    (D.append E).element (Fin.castAdd E.count i) = D.element i :=
  Fin.append_left _ _ _

@[simp] theorem append_element_right (i : Fin E.count) :
    (D.append E).element (Fin.natAdd D.count i) = E.element i :=
  Fin.append_right _ _ _

@[simp] theorem append_power_left (i : Fin D.count) :
    (D.append E).power (Fin.castAdd E.count i) = D.power i :=
  Fin.append_left _ _ _

@[simp] theorem append_power_right (i : Fin E.count) :
    (D.append E).power (Fin.natAdd D.count i) = E.power i :=
  Fin.append_right _ _ _

@[simp] theorem append_factorIdeal_left (i : Fin D.count) :
    (D.append E).factorIdeal (Fin.castAdd E.count i) = D.factorIdeal i := by
  simp only [factorIdeal, decomposition, orbit, append_element_left]

@[simp] theorem append_factorIdeal_right (i : Fin E.count) :
    (D.append E).factorIdeal (Fin.natAdd D.count i) = E.factorIdeal i := by
  simp only [factorIdeal, decomposition, orbit, append_element_right]

@[simp] theorem append_factorCharacter_left (i : Fin D.count) :
    (D.append E).factorCharacter (Fin.castAdd E.count i) = D.factorCharacter i := by
  simp only [factorCharacter, decomposition, orbit, append_element_left]

@[simp] theorem append_factorCharacter_right (i : Fin E.count) :
    (D.append E).factorCharacter (Fin.natAdd D.count i) = E.factorCharacter i := by
  simp only [factorCharacter, decomposition, orbit, append_element_right]

/-- The computed character is the full old character times the new
character.  Neither factor is asserted to belong to the theta family. -/
@[simp] theorem append_character : (D.append E).character = D.character * E.character := by
  change (∏ i : Fin (D.count + E.count),
    (D.append E).factorCharacter i ^ (D.append E).power i) =
      (∏ i, D.factorCharacter i ^ D.power i) * ∏ i, E.factorCharacter i ^ E.power i
  rw [Fin.prod_univ_add]
  simp only [append_factorCharacter_left, append_factorCharacter_right,
    append_power_left, append_power_right]

@[simp] theorem append_fullIdeal :
    (D.append E).fullIdeal = ExteriorIdealEuler.mul D.fullIdeal E.fullIdeal := by
  apply Subtype.ext
  change (∏ i : Fin (D.count + E.count), ((D.append E).factorIdeal i).val) =
    (∏ i, (D.factorIdeal i).val) * ∏ i, (E.factorIdeal i).val
  rw [Fin.prod_univ_add]
  simp only [append_factorIdeal_left, append_factorIdeal_right]

theorem append_fullIdeal_val :
    (D.append E).fullIdeal.val = D.fullIdeal.val * E.fullIdeal.val :=
  congrArg Subtype.val (D.append_fullIdeal E)

/-- Radical support depends on both entire lists, including repeated
factors and factors whose original exponent is zero. -/
theorem append_support_primes :
    primeSupport (D.append E).support.val =
      primeSupport D.support.val ∪ primeSupport E.support.val := by
  rw [(D.append E).support_primes, D.append_fullIdeal_val E,
    D.support_primes, E.support_primes]
  simp only [primeSupport, normalizedFactors_mul D.fullIdeal.property.1 E.fullIdeal.property.1,
    Multiset.toFinset_add]

theorem append_support_val :
    (D.append E).support.val =
      ∏ Q ∈ primeSupport D.support.val ∪ primeSupport E.support.val, Q := by
  rw [← squarefree_support_product_self (D.append E).support_squarefree,
    D.append_support_primes E]

theorem append_support_eq_radical_product :
    (D.append E).support.val =
      commonRadical (D.support.val * E.support.val) (D.support.val * E.support.val) := by
  rw [D.append_support_val E]
  unfold commonRadical
  rw [Finset.inter_self]
  simp only [primeSupport, normalizedFactors_mul D.support.property.1 E.support.property.1,
    Multiset.toFinset_add]

theorem append_support_dvd_product :
    (D.append E).support.val ∣ D.support.val * E.support.val := by
  rw [D.append_support_eq_radical_product E]
  exact (commonRadical_dvd _ _ (mul_ne_zero D.support.property.1 E.support.property.1)
    (mul_ne_zero D.support.property.1 E.support.property.1)).1

theorem append_support_norm_le :
    A.exteriorNorm (D.append E).support ≤ A.exteriorNorm D.support * A.exteriorNorm E.support := by
  have h := norm_le_of_dvd (mul_ne_zero D.support.property.1 E.support.property.1)
    (D.append_support_dvd_product E)
  change (Ideal.absNorm (D.append E).support.val : ℝ) ≤
    (Ideal.absNorm D.support.val : ℝ) * (Ideal.absNorm E.support.val : ℝ)
  simpa only [map_mul, Nat.cast_mul] using h

theorem coprime_append_support (I : Ideal (𝓞 K)) :
    IsCoprime I (D.append E).support.val ↔
      IsCoprime I D.support.val ∧ IsCoprime I E.support.val := by
  rw [coprime_support_iff I (D.append E).support.val (D.append E).support.property.1,
    coprime_support_iff I D.support.val D.support.property.1,
    coprime_support_iff I E.support.val E.support.property.1, D.append_support_primes E]
  exact Finset.forall_mem_union

/-- The original remaining ideal is present once on both sides. -/
theorem append_mask (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (I : Ideal (𝓞 K)) (base : Bool) :
    ((base && decide (IsCoprime I (D.append E).support.val)) &&
        decide (IsCoprime I remaining.val)) =
      (((base && decide (IsCoprime I D.support.val)) &&
        decide (IsCoprime I E.support.val)) && decide (IsCoprime I remaining.val)) := by
  simp only [D.coprime_append_support E I, Bool.decide_and, Bool.and_assoc]

theorem append_fullMaskSupport_primes (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    primeSupport ((D.append E).fullMaskSupport remaining).val =
      primeSupport (D.fullMaskSupport remaining).val ∪ primeSupport E.support.val := by
  rw [(D.append E).fullMaskSupport_primes remaining,
    D.append_support_primes E, D.fullMaskSupport_primes remaining]
  ac_rfl

theorem coprime_append_fullMaskSupport (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (I : Ideal (𝓞 K)) :
    IsCoprime I ((D.append E).fullMaskSupport remaining).val ↔
      IsCoprime I (D.fullMaskSupport remaining).val ∧ IsCoprime I E.support.val := by
  rw [coprime_support_iff I ((D.append E).fullMaskSupport remaining).val
      (nonZeroDivisors.ne_zero ((D.append E).fullMaskSupport remaining).property),
    coprime_support_iff I (D.fullMaskSupport remaining).val
      (nonZeroDivisors.ne_zero (D.fullMaskSupport remaining).property),
    coprime_support_iff I E.support.val E.support.property.1,
    D.append_fullMaskSupport_primes E remaining]
  exact Finset.forall_mem_union

/-- Appending new factors enlarges only the old complete support by
the new displayed support; the fixed remaining mask stays the same. -/
theorem append_fullMaskSupport_dvd_product (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ((D.append E).fullMaskSupport remaining).val ∣
      (D.fullMaskSupport remaining).val * E.support.val := by
  rw [← squarefree_support_product_self ((D.append E).fullMaskSupport_squarefree remaining)]
  apply support_product_dvd
    (mul_ne_zero (nonZeroDivisors.ne_zero (D.fullMaskSupport remaining).property)
      E.support.property.1)
  rw [D.append_fullMaskSupport_primes E remaining]
  intro Q hQ
  change Q ∈ (normalizedFactors ((D.fullMaskSupport remaining).val * E.support.val)).toFinset
  rw [normalizedFactors_mul (nonZeroDivisors.ne_zero (D.fullMaskSupport remaining).property)
    E.support.property.1, Multiset.toFinset_add]
  exact hQ

theorem append_fullMaskSupport_norm_le (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    idealNorm K ((D.append E).fullMaskSupport remaining) ≤
      idealNorm K (D.fullMaskSupport remaining) * A.exteriorNorm E.support := by
  have h := norm_le_of_dvd
    (mul_ne_zero (nonZeroDivisors.ne_zero (D.fullMaskSupport remaining).property)
      E.support.property.1) (D.append_fullMaskSupport_dvd_product E remaining)
  change (Ideal.absNorm ((D.append E).fullMaskSupport remaining).val : ℝ) ≤
    (Ideal.absNorm (D.fullMaskSupport remaining).val : ℝ) * (Ideal.absNorm E.support.val : ℝ)
  simpa only [map_mul, Nat.cast_mul] using h

end OriginalMovingFactors
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalMovingFactors.append_character
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalMovingFactors.append_fullIdeal
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalMovingFactors.append_support_norm_le
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalMovingFactors.append_mask
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalMovingFactors.append_fullMaskSupport_norm_le
