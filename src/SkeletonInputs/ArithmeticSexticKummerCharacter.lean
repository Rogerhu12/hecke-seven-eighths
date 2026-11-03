import HeckeGeneral.Characters.HeckeCharacter
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
import GaloisCohomology.Kummer.Concrete.SimpleExtension
import GaloisCohomology.Kummer.Concrete.FiniteDualSeparation
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Tactic.NormNum

/-!
UNCOMPILED cache candidate, 2026-10-11.

An actual arithmetic-Artin/Kummer construction of a continuous sixth-order
Hecke character. The only mathematical arguments are a nonzero radicand,
an actual field embedding, and the presence of a primitive sixth root.
No RowCharacterInput, coefficient calibration, unramifiedness, theta, or
reciprocity conclusion is assumed. Compatibility of the upstream imports
with this project's Mathlib remains subject to the separate serial audit.

This file does NOT construct RowCharacterInput: identifying its actual
good-prime coefficients and preserving the original S-integer mask remain
separate arithmetic theorems.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Characters.ArithmeticKummerDraft

open NumberField KummerTheory

variable (K : Type) [Field K] [NumberField K]

private theorem six_ne_zero : (6 : K) ≠ 0 := by norm_num

/-- The actual embedding of sixth roots of unity into Circle. No topology
on K, and no continuity of the field embedding, is required. -/
def sixthRootsToCircle (embedding : K →+* ℂ) : nthRootsSubgroup K 6 →* Circle where
  toFun r := ⟨embedding (r.val : K), by
    apply mem_sphere_zero_iff_norm.mpr
    apply Complex.norm_eq_one_of_pow_eq_one (n := 6) _ (by decide)
    have hr : (r.val : K) ^ 6 = 1 :=
      congrArg (fun u : Kˣ => (u : K)) r.property
    rw [← map_pow, hr, map_one]⟩
  map_one' := by
    apply Circle.ext
    change embedding 1 = 1
    exact map_one embedding
  map_mul' r s := by
    apply Circle.ext
    change embedding ((r.val : K) * (s.val : K)) =
      embedding (r.val : K) * embedding (s.val : K)
    exact map_mul embedding _ _

theorem sixthRootsToCircle_pow (embedding : K →+* ℂ)
    (r : nthRootsSubgroup K 6) : sixthRootsToCircle K embedding r ^ 6 = 1 := by
  apply Circle.ext
  change embedding (r.val : K) ^ 6 = 1
  have hr : (r.val : K) ^ 6 = 1 :=
    congrArg (fun u : Kˣ => (u : K)) r.property
  rw [← map_pow, hr, map_one]

/-- A real chosen extension, not a supplied finite quotient. -/
abbrev sexticExtension (a : Kˣ) :=
  chosenSimpleKummerExtension K (6 : ℕ+) (six_ne_zero K) a

/-- Gal(E/K) -> mu6(E) -> mu6(K) -> Circle. The middle map is the inverse
of the canonical extension-of-scalars equivalence, so it preserves the
specified embedding of K's roots of unity. -/
def simpleSexticCircleHom (embedding : K →+* ℂ)
    (hmu : (primitiveRoots 6 K).Nonempty) (a : Kˣ) :
    Gal((sexticExtension K a)/K) →* Circle :=
  (sixthRootsToCircle K embedding).comp
    (((nthRootsSubgroupEquivOfPrimitiveRoots K (sexticExtension K a)
      (6 : ℕ+) hmu).symm.toMonoidHom).comp
        (chosenSimpleKummerRootCharacter K (6 : ℕ+) (six_ne_zero K) hmu a))

theorem simpleSexticCircleHom_pow (embedding : K →+* ℂ)
    (hmu : (primitiveRoots 6 K).Nonempty) (a : Kˣ)
    (g : Gal((sexticExtension K a)/K)) :
    simpleSexticCircleHom K embedding hmu a g ^ 6 = 1 :=
  sixthRootsToCircle_pow K embedding _

set_option maxRecDepth 2048 in
/-- Mathlib class group -> upstream class group -> arithmetic global Artin
-> the actual Kummer root quotient -> Circle.

The finite-dimensional and abelian-Galois facts are proved upstream.
NumberField E is explicitly derived; it is not a new primitive hypothesis.
Continuity of the final map uses the existing discrete Krull topology on
the Galois group of a finite-dimensional extension. -/
def arithmeticSexticKummerCharacter (embedding : K →+* ℂ)
    (hmu : (primitiveRoots 6 K).Nonempty) (a : Kˣ) : HeckeCharacter K := by
  let E := sexticExtension K a
  letI : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K (6 : ℕ+) (six_ne_zero K) a
  letI : NumberField E := NumberField.of_module_finite K E
  letI : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K (6 : ℕ+) (six_ne_zero K) hmu a
  let phi : Gal(E/K) →* Circle := simpleSexticCircleHom K embedding hmu a
  let artin :=
    GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom K E
  let comparison := (_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K).symm
  refine
    { toMonoidHom := phi.comp (artin.comp comparison.toMonoidHom)
      continuous_toFun := ?_ }
  have hphi : Continuous phi := continuous_of_discreteTopology
  exact hphi.comp
    ((GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_continuous
      K E).comp comparison.continuous)

theorem arithmeticSexticKummerCharacter_pow (embedding : K →+* ℂ)
    (hmu : (primitiveRoots 6 K).Nonempty) (a : Kˣ)
    (x : NumberField.IdeleClassGroup (𝓞 K) K) :
    arithmeticSexticKummerCharacter K embedding hmu a x ^ 6 = 1 := by
  let E := sexticExtension K a
  letI : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K (6 : ℕ+) (six_ne_zero K) a
  letI : NumberField E := NumberField.of_module_finite K E
  letI : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K (6 : ℕ+) (six_ne_zero K) hmu a
  change simpleSexticCircleHom K embedding hmu a
    (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom K E
      ((_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K).symm x)) ^ 6 = 1
  exact simpleSexticCircleHom_pow K embedding hmu a _

theorem arithmeticSexticKummerCharacter_finiteOrder (embedding : K →+* ℂ)
    (hmu : (primitiveRoots 6 K).Nonempty) (a : Kˣ) :
    FiniteOrder (arithmeticSexticKummerCharacter K embedding hmu a) := by
  apply (finiteOrder_iff_pointwise _).2
  exact ⟨6, by decide, arithmeticSexticKummerCharacter_pow K embedding hmu a⟩

end HeckeGeneral.Characters.ArithmeticKummerDraft
