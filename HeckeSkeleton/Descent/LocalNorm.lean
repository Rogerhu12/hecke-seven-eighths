import HeckeSkeleton.ActualHeckeNormPullback
import HeckeGeneral.Characters.LocalComponent
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.OnePlaceBaseNorm

/-!
Adapted from the 2026-10-11 local-norm cache for the actual Descent interface.

For every finite place w over v, including ramified places, the actual
Hecke norm pullback has local component chi_v composed with the actual
completed field norm. All local maps and compatibility identities are
constructed/proved; none is supplied as a hypothesis. Neither Galois nor
unramified assumptions occur. The actual completed field norm is also
proved continuous by projecting the continuous actual global idele norm.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeSkeleton.Descent.LocalNorm

open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped NumberField
open HeckeGeneral.Characters.NormPullbackDraft

section SingleField

variable (F : Type*) [Field F] [NumberField F]

/-- The actual topological idele comparison respects the project's local map. -/
theorem comparison_localIdeleEmbedding
    (v : HeightOneSpectrum (𝓞 F)) (y : (v.adicCompletion F)ˣ) :
    (_root_.IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F)
        (_root_.IdeleGroup.finitePlaceIdele v y) = localIdeleEmbedding F v y := by
  exact _root_.IdeleGroup.equivAdeleRingUnits_finitePlaceIdele F v y

theorem comparison_symm_localIdeleEmbedding
    (v : HeightOneSpectrum (𝓞 F)) (y : (v.adicCompletion F)ˣ) :
    (_root_.IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm
        (localIdeleEmbedding F v y) = _root_.IdeleGroup.finitePlaceIdele v y := by
  rw [← comparison_localIdeleEmbedding F v y]
  exact (_root_.IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm_apply_apply _

/-- The actual topological class comparison respects the project's local class map. -/
theorem comparison_localIdeleClassMap
    (v : HeightOneSpectrum (𝓞 F)) (y : (v.adicCompletion F)ˣ) :
    (_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib F)
        (_root_.IdeleGroup.finitePlaceIdeleClass v y) = localIdeleClassMap F v y := by
  exact _root_.IdeleGroup.ideleClassGroupEquivMathlib_finitePlaceIdeleClass F v y

theorem comparison_symm_localIdeleClassMap
    (v : HeightOneSpectrum (𝓞 F)) (y : (v.adicCompletion F)ˣ) :
    (_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib F).symm
        (localIdeleClassMap F v y) = _root_.IdeleGroup.finitePlaceIdeleClass v y := by
  rw [← comparison_localIdeleClassMap F v y]
  exact (_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib F).symm_apply_apply _

end SingleField

section Relative

variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
variable [Algebra F K] [FiniteDimensional F K]

/-- The genuine determinant norm on the completed local fields, on units.
The completion algebra is the actual finite-place completion map. -/
def actualLocalNorm (v : HeightOneSpectrum (𝓞 F))
    (W : {w : HeightOneSpectrum (𝓞 K) // _root_.finitePlaceBelow (K := F) w = v}) :
    (W.1.adicCompletion K)ˣ →* (v.adicCompletion F)ˣ := by
  letI : Algebra (v.adicCompletion F) (W.1.adicCompletion K) :=
    (_root_.finitePlaceAdicCompletionMap F K v W).toAlgebra
  exact LocalFieldTheory.normUnits (v.adicCompletion F) (W.1.adicCompletion K)

/-- Literal one-place idele norm equality, valid at every finite place. -/
theorem upstreamNorm_finitePlaceIdele (v : HeightOneSpectrum (𝓞 F))
    (W : {w : HeightOneSpectrum (𝓞 K) // _root_.finitePlaceBelow (K := F) w = v})
    (y : (W.1.adicCompletion K)ˣ) :
    _root_.IdeleGroup.norm F K (_root_.IdeleGroup.finitePlaceIdele W.1 y) =
      _root_.IdeleGroup.finitePlaceIdele v (actualLocalNorm F K v W y) := by
  letI : Algebra (v.adicCompletion F) (W.1.adicCompletion K) :=
    (_root_.finitePlaceAdicCompletionMap F K v W).toAlgebra
  exact _root_.IdeleGroup.norm_finitePlaceIdele_eq_finitePlaceIdele_normUnits v W y

/-- The project's genuine idele norm obeys the same one-place identity. -/
theorem mathlibIdeleNorm_localIdeleEmbedding (v : HeightOneSpectrum (𝓞 F))
    (W : {w : HeightOneSpectrum (𝓞 K) // _root_.finitePlaceBelow (K := F) w = v})
    (y : (W.1.adicCompletion K)ˣ) :
    mathlibIdeleNorm F K (localIdeleEmbedding K W.1 y) =
      localIdeleEmbedding F v (actualLocalNorm F K v W y) := by
  rw [mathlibIdeleNorm_apply, comparison_symm_localIdeleEmbedding,
    upstreamNorm_finitePlaceIdele, comparison_localIdeleEmbedding]

/-- The actual class norm commutes with local insertion, including ramified places. -/
theorem mathlibIdeleClassNorm_localIdeleClassMap (v : HeightOneSpectrum (𝓞 F))
    (W : {w : HeightOneSpectrum (𝓞 K) // _root_.finitePlaceBelow (K := F) w = v})
    (y : (W.1.adicCompletion K)ˣ) :
    mathlibIdeleClassNorm F K (localIdeleClassMap K W.1 y) =
      localIdeleClassMap F v (actualLocalNorm F K v W y) := by
  change mathlibIdeleClassNorm F K (ideleClassMap K (localIdeleEmbedding K W.1 y)) =
    ideleClassMap F (localIdeleEmbedding F v (actualLocalNorm F K v W y))
  rw [mathlibIdeleClassNorm_ideleClassMap, mathlibIdeleNorm_localIdeleEmbedding]

/-- Continuity of the genuine local norm, deduced from actual global maps.
This proof does not postulate compatibility or a substitute local norm map. -/
theorem actualLocalNorm_continuous (v : HeightOneSpectrum (𝓞 F))
    (W : {w : HeightOneSpectrum (𝓞 K) // _root_.finitePlaceBelow (K := F) w = v}) :
    Continuous (actualLocalNorm F K v W) := by
  have h : Continuous (fun y : (W.1.adicCompletion K)ˣ =>
      _root_.IdeleGroup.finiteComponent v
        (_root_.IdeleGroup.norm F K
          ((_root_.IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv K).symm
            (localIdeleEmbedding K W.1 y)))) :=
    (_root_.IdeleGroup.finiteComponentContinuous v).continuous.comp
      ((_root_.IdeleGroup.norm_continuous F K).comp
        ((_root_.IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv K).symm.continuous.comp
          (localIdeleEmbedding K W.1).continuous))
  exact h.congr (fun y => by
    rw [comparison_symm_localIdeleEmbedding, upstreamNorm_finitePlaceIdele,
      _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same])

/-- The actual completed field norm, now bundled with its proved continuity. -/
def actualLocalNormContinuous (v : HeightOneSpectrum (𝓞 F))
    (W : {w : HeightOneSpectrum (𝓞 K) // _root_.finitePlaceBelow (K := F) w = v}) :
    (W.1.adicCompletion K)ˣ →ₜ* (v.adicCompletion F)ˣ where
  toMonoidHom := actualLocalNorm F K v W
  continuous_toFun := actualLocalNorm_continuous F K v W

/-- Pointwise local-component identity for arbitrary finite places and characters. -/
theorem localComponent_heckeNormPullback_apply (χ : HeckeCharacter F)
    (v : HeightOneSpectrum (𝓞 F))
    (W : {w : HeightOneSpectrum (𝓞 K) // _root_.finitePlaceBelow (K := F) w = v})
    (y : (W.1.adicCompletion K)ˣ) :
    localComponent K W.1 (heckeNormPullback F K χ) y =
      localComponent F v χ (actualLocalNorm F K v W y) := by
  change χ (mathlibIdeleClassNorm F K (localIdeleClassMap K W.1 y)) =
    χ (localIdeleClassMap F v (actualLocalNorm F K v W y))
  rw [mathlibIdeleClassNorm_localIdeleClassMap]

/-- Equality of the actual continuous local characters, not just selected values. -/
theorem localComponent_heckeNormPullback (χ : HeckeCharacter F)
    (v : HeightOneSpectrum (𝓞 F))
    (W : {w : HeightOneSpectrum (𝓞 K) // _root_.finitePlaceBelow (K := F) w = v}) :
    localComponent K W.1 (heckeNormPullback F K χ) =
      (localComponent F v χ).comp (actualLocalNormContinuous F K v W) := by
  apply ContinuousMonoidHom.ext
  intro y
  exact localComponent_heckeNormPullback_apply F K χ v W y

end Relative
end HeckeSkeleton.Descent.LocalNorm
