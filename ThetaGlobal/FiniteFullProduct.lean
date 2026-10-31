import ThetaGlobal.FiniteCanonicalSource
import ThetaGlobal.FiniteCoreProduct
import ThetaGlobal.GlobalProjectExterior
import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.WeylGeometry
import DedekindZetaZeroFree.Theta.Whittaker.LocalFunctionalsFromGlobalPeriods
import DedekindZetaZeroFree.Theta.Whittaker.Uniqueness.ComplexTorusTranslates

/-!
# The full matrix product for the same frozen pure tensor

`FullArchProduct` is an intermediate property of a source map.  It is
proved for the explicit canonical source and is preserved by the actual
finite projector in `FiniteProjectedFullSource`.  It is not an additional
global input for the final construction.  The normalization everywhere is
the Fourier coefficient at one of this very tensor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
noncomputable section
attribute [local instance] ContinuousLinearMap.addCommGroup

namespace ThetaGlobal.FiniteFullProduct

open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.FourierContinuation.ComplexLines
open DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
open DedekindZetaZeroFree.KPLiteralScalarHCCompactOrbit
open DedekindZetaZeroFree.KPCplxCharacterHaar
open DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open ThetaGlobal.FiniteCoreProduct
open scoped Classical NumberField BigOperators

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T)

def archRatio (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p.val)
    (w : InfinitePlace F) (a : ComplexPGL2) : ℂ :=
  stageCoefficient R D s x (projectiveSlot R w a) / stageCoefficient R D s x 1

def FullArchProduct : Prop :=
  ∀ (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p.val),
    (∀ w : InfinitePlace F, Sum.inl w ∈ s.val) →
    stageCoefficient R D s x 1 ≠ 0 →
    ∀ (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
      (b : InfinitePlace F → ComplexGL2),
    stageCoefficient R D s x ((finiteBase (R := R) a).val *
      archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12 b) =
    stageCoefficient R D s x (finiteBase (R := R) a).val *
      ∏ w, archRatio R D s x w (Matrix.ProjGenLinGroup.mk (b w))

/-- Each single-place ratio is the actual local Whittaker matrix
coefficient of that archimedean component.  This property is proved for
the canonical source and retained by source normalization/projection. -/
def LocalArchRatio : Prop :=
  ∀ (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p.val)
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val),
    stageCoefficient R D s x 1 ≠ 0 →
    ∀ (M : KPCplxActualImage.Theta traceFrequency →L[ℂ] ℂ),
      M ∈ KPCplxWhittakerUnique.whittakerSpace traceFrequency traceCharacter →
      M (harmonicInclusion (x ⟨Sum.inl w, hw⟩)) ≠ 0 →
      ∀ a : ComplexPGL2,
        archRatio R D s x w a =
          M (KPCplxActualImage.imageAction traceFrequency a
            (harmonicInclusion (x ⟨Sum.inl w, hw⟩))) /
          M (harmonicInclusion (x ⟨Sum.inl w, hw⟩))

/-- The stored archimedean linear functional is the restriction of an
actual continuous Whittaker functional. The source construction proves
this certificate and retains it when only the selected tensor changes. -/
def LocalWhittakerForms : Prop :=
  ∀ w : InfinitePlace F,
    ∃ M : KPCplxActualImage.Theta traceFrequency →L[ℂ] ℂ,
      M ∈ KPCplxWhittakerUnique.whittakerSpace traceFrequency traceCharacter ∧
      ∀ v : KPGlobalResidualConstruction.complexCore,
        M (harmonicInclusion v) = D.ell (Sum.inl w) v

/-- Local Whittaker uniqueness transfers nonvanishing from any actual
Whittaker functional to the stored source functional. The latter is
nonzero by its detected tensor, before a high K-type vector is chosen. -/
theorem local_value_nonzero_of_whittaker
    (hForms : LocalWhittakerForms R D) (w : InfinitePlace F)
    (M : KPCplxActualImage.Theta traceFrequency →L[ℂ] ℂ)
    (hM : M ∈ KPCplxWhittakerUnique.whittakerSpace traceFrequency traceCharacter)
    (v : KPGlobalResidualConstruction.complexCore)
    (hv : M (harmonicInclusion v) ≠ 0) :
    D.ell (Sum.inl w) v ≠ 0 := by
  obtain ⟨L, hL, hrestriction⟩ := hForms w
  obtain ⟨u, hu⟩ :=
    ExteriorWhittakerValues.StoredWhittaker.exists_nonzero_value R D (Sum.inl w)
  have hLne : L ≠ 0 := by
    intro hzero
    apply hu
    simpa only [hzero, ContinuousLinearMap.zero_apply] using (hrestriction u).symm
  have hcompare := KPWildComplexWhittakerDictionary.continuousWhittaker_comparison
    traceFrequency traceCharacter traceCharacter_continuous traceCharacter_ne_one
    L M hL hM v hv
  change L = (L (harmonicInclusion v) / M (harmonicInclusion v)) • M at hcompare
  intro hzero
  apply hLne
  simpa only [hrestriction v, hzero, zero_div, zero_smul] using hcompare

/-- The property follows from the existing arbitrary-vector completed
period theorem for the literal canonical residue source. -/
theorem canonical_fullArchProduct
    (N : TraceHaarTransport R) (B : FiniteCanonicalSource.Seed R) (hR : RootAligned R) :
    FullArchProduct R (FiniteCanonicalSource.factorization R N B hR) := by
  intro s x hw hx a b
  exact FiniteCanonicalSource.core_full_matrix_product R N B hR s x hw hx a b

theorem canonical_localArchRatio
    (N : TraceHaarTransport R) (B : FiniteCanonicalSource.Seed R) (hR : RootAligned R) :
    LocalArchRatio R (FiniteCanonicalSource.factorization R N B hR) := by
  intro s x w hw hx M hM hMx a
  have h := actualStage_period_ratio R B.model B.fibers
    FiniteCanonicalSource.localHaar FiniteCanonicalSource.localHaar_integer N
    s x w hw 1 (by simp) M hM hMx a
  simp only [one_mul] at h
  change actualStagePeriod R B.model B.fibers
    FiniteCanonicalSource.localHaar FiniteCanonicalSource.localHaar_integer N
    s x (projectiveSlot R w a) /
      actualStagePeriod R B.model B.fibers
        FiniteCanonicalSource.localHaar FiniteCanonicalSource.localHaar_integer N s x 1 = _
  rw [h, mul_div_cancel_right₀ _ hx]

theorem normalized_full_matrix_product (hfull : FullArchProduct R D)
    (s : RestrictedTensorSimple.Level D.bad) (hs : s.val = D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p.val)
    (hx : stageCoefficient R D s x 1 ≠ 0)
    (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (b : InfinitePlace F → ComplexGL2) :
    stageCoefficient R D s x ((finiteBase (R := R) a).val *
      archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12 b) =
    stageCoefficient R D s x 1 *
      (∏ q : R.A.Sf, D.ell (Sum.inr q.val)
        (finiteAction R D a (Sum.inr q.val)
          (x ⟨Sum.inr q.val, finite_mem R D s hs q⟩)) /
        D.ell (Sum.inr q.val) (x ⟨Sum.inr q.val, finite_mem R D s hs q⟩)) *
      ∏ w, archRatio R D s x w (Matrix.ProjGenLinGroup.mk (b w)) := by
  rw [hfull s x (arch_mem R D s hs) hx a b,
    normalized_matrix_product R D a s hs x hx]

theorem frozen_fullExteriorInvariant
    (s : RestrictedTensorSimple.Level D.bad) (hs : s.val = D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p.val) :
    GlobalProjectExterior.FullExteriorInvariant R (stageFunction R D s x) := by
  have he : s = GlobalProjectExterior.badStage R D := Subtype.ext hs
  subst s
  exact GlobalProjectExterior.badVector_fullExteriorInvariant R D x

/-- The exterior Weyl coordinates disappear for every frozen tensor,
because all exterior slots are the unchanged spherical references. -/
theorem frozen_fourier_right_sWeyl
    (s : RestrictedTensorSimple.Level D.bad) (hs : s.val = D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p.val) (g : Group R) :
    stageCoefficient R D s x
      (g * KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12) =
    stageCoefficient R D s x (g * tupleLift R (sWeylTuple R)) := by
  have hi (q : KPAdditiveQuotient F) := frozen_fullExteriorInvariant R D s hs x
    (exteriorWeylTuple R) (exteriorWeylTuple_mem R)
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) *
      (g * tupleLift R (sWeylTuple R)))
  have he : tupleLift R (sWeylTuple R) * tupleLift R (exteriorWeylTuple R) =
      KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 := by
    rw [← map_mul]
    simp only [exteriorWeylTuple, mul_inv_cancel_left] <;> rfl
  unfold stageCoefficient MomentSources.fourier
  apply integral_congr_ae
  filter_upwards [] with q
  have h := hi q
  change stageFunction R D s x
    ((_ * (g * tupleLift R (sWeylTuple R))) * tupleLift R (exteriorWeylTuple R)) = _ at h
  rw [mul_assoc, mul_assoc, he] at h
  rw [h]

/-- Exact global reflected product before normalizing each finite slot. -/
theorem frozen_weyl_product (hfull : FullArchProduct R D)
    (s : RestrictedTensorSimple.Level D.bad) (hs : s.val = D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p.val)
    (hx : stageCoefficient R D s x 1 ≠ 0) (z : R.A.G) :
    stageCoefficient R D s x
      (MomentSources.diagonal R z *
        KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12) =
    stageCoefficient R D s x 1 *
      (∏ q : R.A.Sf, D.ell (Sum.inr q.val)
        (finiteAction R D (finiteWeylRaw R z) (Sum.inr q.val)
          (x ⟨Sum.inr q.val, finite_mem R D s hs q⟩)) /
        D.ell (Sum.inr q.val) (x ⟨Sum.inr q.val, finite_mem R D s hs q⟩)) *
      ∏ w, archRatio R D s x w
        (Matrix.ProjGenLinGroup.mk (archWeylMatrix R z w)) := by
  rw [frozen_fourier_right_sWeyl R D s hs x,
    diagonal_sWeyl_geometry R z]
  exact normalized_full_matrix_product R D hfull s hs x hx
    (finiteWeylRaw R z) (archWeylMatrix R z)

end ThetaGlobal.FiniteFullProduct

#print axioms ThetaGlobal.FiniteFullProduct.canonical_fullArchProduct
#print axioms ThetaGlobal.FiniteFullProduct.frozen_weyl_product

#print axioms ThetaGlobal.FiniteFullProduct.local_value_nonzero_of_whittaker
