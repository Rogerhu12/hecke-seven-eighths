import ThetaGlobal.GlobalProjectHighKExtraction
import ThetaGlobal.FiniteHighKDirect
import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ProbeAndUniformSection

/-!
# The extracted S-sheet profiles are the actual normalized Mellin pair

The direct cutoff forces the identity sixth-power class.  The reflected
mask is the literal finite Mellin table mask with the inverse Axiom
Hilbert square.  Both sheet integrals retain the same high K-type source
scalar and the same reflected local normalization constant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.GlobalProjectSheetProfiles

open NumberField MeasureTheory DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton.Global
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η) (θ : HeckeCharacter F)
  (C : FiniteFixedSource.Source R θ) (L : FiniteLocalHighK.Input R θ C)

local notation "D" => C.projected.base.factorization
local notation "Q" => C.projected.base.sources
local notation "T" => C.projected.base.realization
local notation "k" => QuotientGroup.mk' R.A.sixthPowers
local notation "B" => R.probe.correction.B
local notation "Sf" => (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))

local instance : C.transport.groupHaar.IsHaarMeasure := C.transport.groupHaar_isHaar

def sourceScalar (u : R.A.UnitQuotient) : ℂ :=
  fourier R Q.dq (FiniteHighKTensor.source R D u L.vector) 1

def commonScalar (u : R.A.UnitQuotient) : ℂ :=
  sourceScalar R θ C L u * FiniteLocalHighK.reflectedConstant R θ C L

theorem commonScalar_ne_zero (u : R.A.UnitQuotient) : commonScalar R θ C L u ≠ 0 :=
  mul_ne_zero (FiniteHighKTensor.source_scalar_nonzero R D
    (FiniteFixedSource.Source.period_nonzero R θ C) u L.vector L.source_nonzero)
    (FiniteLocalHighK.reflectedConstant_nonzero R θ C L)

def skeletonClass (κ : R.A.V) : SixthLocalClasses F Sf :=
  (ProjectFiniteClass.skeletonAxiomClassEquiv R.A).symm κ

theorem direct_weight_profile (u : R.A.UnitQuotient) (κ : R.A.V) (z : R.A.G) :
    GlobalProjectUnfolding.directWeight R (GlobalTargetPeriod.period R θ u) B κ z *
      GlobalProjectHighKExtraction.directProfile R D u L.vector z =
      (if κ ∈ B then 1 else 0) *
        FiniteDirectMellin.directTensor R C.projected.cutoffs (sourceScalar R θ C L u)
          (FiniteNormalizedMellin.archProfile R θ C L false) z := by
  by_cases hz : k z = 1
  · simp only [GlobalProjectUnfolding.directWeight, hz, mul_one,
      Subgroup.inv_mem_iff, GlobalProjectHighKExtraction.directProfile]
    rw [mul_assoc, FiniteHighKDirect.directTensor_eq R θ C L]
    rfl
  · rw [GlobalProjectHighKExtraction.directProfile,
      FiniteHighKDirect.global_diagonal_class_support R θ C L u z hz,
      FiniteHighKDirect.directTensor_class_support R θ C L u z hz]
    simp

theorem reflected_weight_profile (u : R.A.UnitQuotient) (κ : R.A.V) (z : R.A.G) :
    GlobalProjectUnfolding.reflectedWeight R (GlobalTargetPeriod.period R θ u) B κ z *
      GlobalProjectHighKExtraction.reflectedProfile R D u L.vector z =
      FiniteSheetMellin.reflectedTensor R D θ (sourceScalar R θ C L u)
        (FiniteNormalizedMellin.archProfile R θ C L true) u (skeletonClass R κ) z := by
  have h := FiniteHighKWeyl.reflectedTensor_eq R D C.fullArchProduct
    (FiniteFixedSource.Source.period_nonzero R θ C) θ u L.vector L.source_nonzero
    (skeletonClass R κ) z
  have hm := FiniteHighKWeyl.table_mask_literal R (skeletonClass R κ) z
  simp only [skeletonClass, MulEquiv.apply_symm_apply] at hm
  rw [hm] at h
  have harch : FiniteHighKWeyl.archLocal R D θ u L.vector =
      FiniteNormalizedMellin.archProfile R θ C L true := by
    funext w t
    exact FiniteLocalHighK.reflected_archLocal R θ C L u w t
  rw [harch] at h
  by_cases hb : κ * (k z)⁻¹ ∈ B
  · simpa only [GlobalProjectUnfolding.reflectedWeight,
      GlobalProjectConvention.paperHilbert, GlobalProjectHighKExtraction.reflectedProfile,
      sourceScalar, if_pos hb, one_mul, inv_pow, mul_assoc] using h
  · simpa only [GlobalProjectUnfolding.reflectedWeight,
      GlobalProjectHighKExtraction.reflectedProfile, sourceScalar, if_neg hb,
      zero_mul] using h

/-- Sheet Haar is the pushforward of the original norm-one Haar under
the exact same norm splitting used in the Mellin product. -/
theorem sheet_integral (w : InfinitePlace F) (x : PositiveAxis) (f : R.A.G → ℂ) :
    (∫ z : Sheet R.A x, f z.val ∂sheetHaar R.A w C.transport.groupHaar x) =
      @integral R.A.G1 ℂ _ _ (borel _) R.probe.domain.measure
        (fun z => f (FiniteSheetMellin.sheetEquiv R w (x, z))) := by
  rw [sheetHaar, GaussianSmoothing.kernelHaar_eq_probe,
    integral_map_equiv (sheetTranslation R.A w x).toMeasurableEquiv]
  rw [GaussianSmoothing.probeHaar_integral]
  rfl

theorem direct_sheet (u : R.A.UnitQuotient) (κ : R.A.V)
    (w : InfinitePlace F) (x : PositiveAxis) :
    (∫ z : Sheet R.A x,
      GlobalProjectUnfolding.directWeight R (GlobalTargetPeriod.period R θ u) B κ z.val *
        GlobalProjectHighKExtraction.directProfile R D u L.vector z.val
      ∂sheetHaar R.A w C.transport.groupHaar x) =
      (if κ ∈ B then 1 else 0) * commonScalar R θ C L u *
        FiniteNormalizedMellin.direct R θ C L w x := by
  simp_rw [direct_weight_profile R θ C L]
  rw [integral_const_mul, sheet_integral R θ C]
  change (if κ ∈ B then (1 : ℂ) else 0) *
    FiniteDirectMellin.directSheet R C.projected.cutoffs (sourceScalar R θ C L u)
      (FiniteNormalizedMellin.archProfile R θ C L false) w x = _
  rw [FiniteNormalizedMellin.direct_common_normalization R θ C L]
  simp only [commonScalar, mul_assoc]

theorem reflected_sheet (u : R.A.UnitQuotient) (κ : R.A.V)
    (w : InfinitePlace F) (x : PositiveAxis) :
    (∫ z : Sheet R.A x,
      GlobalProjectUnfolding.reflectedWeight R (GlobalTargetPeriod.period R θ u) B κ z.val *
        GlobalProjectHighKExtraction.reflectedProfile R D u L.vector z.val
      ∂sheetHaar R.A w C.transport.groupHaar x) =
      commonScalar R θ C L u *
        FiniteNormalizedMellin.reflected R θ C L u (skeletonClass R κ) w x := by
  simp_rw [reflected_weight_profile R θ C L]
  rw [sheet_integral R θ C]
  exact FiniteNormalizedMellin.reflected_common_normalization R θ C L
    (sourceScalar R θ C L u) u (skeletonClass R κ) w x

end ThetaGlobal.GlobalProjectSheetProfiles
