import HeckeSkeleton.HeckeHighRowLRatio
import HeckeSkeleton.FiniteOrderKernelOpen
-- Internal imports first: skeleton/check.py requires them before any registered external import.
import HeckeGeneral.Characters.HeckeCharacter
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison
import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.Continuity

/-!
UNCOMPILED CACHE CANDIDATE, 2026-10-11. No Lean/Lake invocation.

The actual relative norm, transported through the genuine topological
comparison of upstream and Mathlib ideles/idele classes. No norm map or
continuity conclusion is supplied as a hypothesis. Every upstream import
already belongs to the frozen 808 closure; that queue is unchanged.

The extension is an arbitrary finite extension of number fields. No Galois,
abelian, roots-of-unity, conductor or character-calibration hypothesis occurs.
This constructs pullback and its literal evaluation/multiplicativity/finite
order properties. It supplies neither an L-function factorization nor the
pole_matching field needed for HeckeFactorizationDescentData.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeGeneral.Characters.NormPullbackDraft

open NumberField

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L]

/-- The actual upstream idele-class norm is continuous by quotient descent
of the proved continuous relative idele norm. -/
def upstreamIdeleClassNormContinuous :
    _root_.IdeleClassGroup L →ₜ* _root_.IdeleClassGroup K where
  toMonoidHom := _root_.ideleClassNorm K L
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk
      (_root_.IdeleGroup.principalSubgroup L)).continuous_iff.mpr
    have h : Continuous (fun a : _root_.IdeleGroup L =>
        QuotientGroup.mk' (_root_.IdeleGroup.principalSubgroup K)
          (_root_.IdeleGroup.norm K L a)) :=
      QuotientGroup.continuous_mk.comp (_root_.IdeleGroup.norm_continuous K L)
    exact h.congr (fun _ => rfl)

@[simp] theorem upstreamIdeleClassNormContinuous_apply
    (x : _root_.IdeleClassGroup L) :
    upstreamIdeleClassNormContinuous K L x = _root_.ideleClassNorm K L x := rfl

/-- The genuine relative norm on Mathlib's adelic-unit idele groups. -/
def mathlibIdeleNorm :
    NumberField.IdeleGroup (𝓞 L) L →ₜ* NumberField.IdeleGroup (𝓞 K) K where
  toMonoidHom :=
    (_root_.IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv K).toMonoidHom.comp
      ((_root_.IdeleGroup.ideleNormContinuousMonoidHom K L).toMonoidHom.comp
        (_root_.IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv L).symm.toMonoidHom)
  continuous_toFun :=
    (_root_.IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv K).continuous.comp
      ((_root_.IdeleGroup.ideleNormContinuousMonoidHom K L).continuous.comp
        (_root_.IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv L).symm.continuous)

@[simp] theorem mathlibIdeleNorm_apply (x : NumberField.IdeleGroup (𝓞 L) L) :
    mathlibIdeleNorm K L x =
      (_root_.IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv K)
        (_root_.IdeleGroup.norm K L
          ((_root_.IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv L).symm x)) := rfl

/-- The genuine relative norm on Mathlib's quotient-topological class groups. -/
def mathlibIdeleClassNorm :
    NumberField.IdeleClassGroup (𝓞 L) L →ₜ* NumberField.IdeleClassGroup (𝓞 K) K where
  toMonoidHom :=
    (_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K).toMonoidHom.comp
      ((upstreamIdeleClassNormContinuous K L).toMonoidHom.comp
        (_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib L).symm.toMonoidHom)
  continuous_toFun :=
    (_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K).continuous.comp
      ((upstreamIdeleClassNormContinuous K L).continuous.comp
        (_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib L).symm.continuous)

@[simp] theorem mathlibIdeleClassNorm_apply
    (x : NumberField.IdeleClassGroup (𝓞 L) L) :
    mathlibIdeleClassNorm K L x =
      (_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K)
        (_root_.ideleClassNorm K L
          ((_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib L).symm x)) := rfl

/-- Literal compatibility with the quotient maps, without a supplied norm
comparison or an abstract class-group map. -/
theorem mathlibIdeleClassNorm_ideleClassMap (x : NumberField.IdeleGroup (𝓞 L) L) :
    mathlibIdeleClassNorm K L (ideleClassMap L x) =
      ideleClassMap K (mathlibIdeleNorm K L x) := by
  change
    (_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K)
      (_root_.ideleClassNorm K L
        (QuotientGroup.mk' (_root_.IdeleGroup.principalSubgroup L)
          ((_root_.IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv L).symm x))) = _
  exact congrArg
    (fun y : _root_.IdeleClassGroup K =>
      (_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K) y)
    (_root_.ideleClassNorm_mk K L
      ((_root_.IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv L).symm x))

/-- Precomposition with the actual norm, bundled as a character-group hom. -/
def heckeNormPullback : HeckeCharacter K →* HeckeCharacter L :=
  pullbackHom (mathlibIdeleClassNorm K L)

@[simp] theorem heckeNormPullback_apply
    (χ : HeckeCharacter K) (x : NumberField.IdeleClassGroup (𝓞 L) L) :
    heckeNormPullback K L χ x = χ (mathlibIdeleClassNorm K L x) := rfl

/-- Calculation on an actual upstream idele-class representative. -/
theorem heckeNormPullback_comparison_apply (χ : HeckeCharacter K)
    (x : _root_.IdeleClassGroup L) :
    heckeNormPullback K L χ
        ((_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib L) x) =
      χ ((_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K)
        (_root_.ideleClassNorm K L x)) := by
  change χ ((_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K)
    (_root_.ideleClassNorm K L
      ((_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib L).symm
        ((_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib L) x)))) = _
  rw [(_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib L).symm_apply_apply]

/-- Literal idele evaluation through the actual norm. -/
theorem toIdeleCharacter_heckeNormPullback (χ : HeckeCharacter K)
    (x : NumberField.IdeleGroup (𝓞 L) L) :
    toIdeleCharacter L (heckeNormPullback K L χ) x =
      toIdeleCharacter K χ (mathlibIdeleNorm K L x) := by
  change χ (mathlibIdeleClassNorm K L (ideleClassMap L x)) =
    χ (ideleClassMap K (mathlibIdeleNorm K L x))
  rw [mathlibIdeleClassNorm_ideleClassMap]

@[simp] theorem heckeNormPullback_one : heckeNormPullback K L 1 = 1 :=
  map_one (heckeNormPullback K L)

@[simp] theorem heckeNormPullback_mul (χ θ : HeckeCharacter K) :
    heckeNormPullback K L (χ * θ) = heckeNormPullback K L χ * heckeNormPullback K L θ :=
  map_mul (heckeNormPullback K L) χ θ

@[simp] theorem heckeNormPullback_pow (χ : HeckeCharacter K) (n : ℕ) :
    heckeNormPullback K L (χ ^ n) = heckeNormPullback K L χ ^ n :=
  map_pow (heckeNormPullback K L) χ n

@[simp] theorem heckeNormPullback_zpow (χ : HeckeCharacter K) (n : ℤ) :
    heckeNormPullback K L (χ ^ n) = heckeNormPullback K L χ ^ n :=
  map_zpow (heckeNormPullback K L) χ n

@[simp] theorem heckeNormPullback_inv (χ : HeckeCharacter K) :
    heckeNormPullback K L χ⁻¹ = (heckeNormPullback K L χ)⁻¹ :=
  map_inv (heckeNormPullback K L) χ

theorem heckeNormPullback_finiteOrder {χ : HeckeCharacter K} (hχ : FiniteOrder χ) :
    FiniteOrder (heckeNormPullback K L χ) :=
  (heckeNormPullback K L).isOfFinOrder hχ

/-- Any specified exponent is preserved; exact order need not be preserved. -/
theorem heckeNormPullback_pow_eq_one (χ : HeckeCharacter K) (n : ℕ)
    (hχ : χ ^ n = 1) : heckeNormPullback K L χ ^ n = 1 := by
  rw [← heckeNormPullback_pow, hχ, heckeNormPullback_one]

end HeckeGeneral.Characters.NormPullbackDraft
