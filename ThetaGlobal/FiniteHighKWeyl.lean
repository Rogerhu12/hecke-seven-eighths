import ThetaGlobal.FiniteFullProduct
import ThetaGlobal.FiniteHighKTensor
import ThetaGlobal.FiniteSheetMellin
import ThetaGlobal.GlobalTargetPeriod

/-!
# The actual high K-type reflected Fourier coefficient is the Mellin tensor

The finite local ratios in the full global Weyl product are identified
with the normalized actual canonical vectors used in the coefficient
table.  The target Hecke period and inverse Hilbert-square mask then give
the literal tensor integrated in `FiniteSheetMellin`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.FiniteHighKWeyl

open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.KPCplxCharacterHaar
open DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.FiniteCoreProduct ThetaGlobal.FiniteCanonicalVectors
open ThetaGlobal.ProjectedFiniteMellin
open scoped Classical NumberField BigOperators

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T)

theorem finiteAction_weyl (z : R.A.G) (p : R.A.Sf) (φ : Vector R D p) :
    finiteAction R D (finiteWeylRaw R z) (Sum.inr p.val) φ =
      action R D p (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12
        (Sum.inr p.val) (z.2 p))
        (action R D p (KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12
          (Sum.inr p.val)) φ) := by
  have he := DigitMasks.localIdele_finite R z p.val p.property
  unfold finiteAction finiteWeylRaw
  rw [he, map_mul, map_mul] <;> rfl

theorem normalized_finiteWeyl (u : R.A.UnitQuotient) (z : R.A.G) (p : R.A.Sf) :
    D.ell (Sum.inr p.val)
      (finiteAction R D (finiteWeylRaw R z) (Sum.inr p.val)
        (selectedFiniteVector R D u p)) /
      D.ell (Sum.inr p.val) (selectedFiniteVector R D u p) =
    weylValue R D p (normalizedSelectedVector R D u p) (z.2 p) := by
  rw [finiteAction_weyl]
  simp only [weylValue, normalizedSelectedVector, map_smul, smul_eq_mul,
    div_eq_mul_inv, mul_comm]

def archArgument (w : InfinitePlace F) (z : w.Completionˣ) : ComplexPGL2 :=
  Matrix.ProjGenLinGroup.mk
    (KPCplxCharacterHaar.diagonal
      (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (R.A.complex_place w)).toMonoidHom z) * weyl)

def archLocal (θ : HeckeCharacter F) (u : R.A.UnitQuotient)
    (arch : InfinitePlace F → KPGlobalResidualConstruction.complexCore)
    (w : InfinitePlace F) (z : w.Completionˣ) : ℂ :=
  (infiniteComponent F w θ z : ℂ)⁻¹ *
    FiniteFullProduct.archRatio R D (frozenStage R D u)
      (FiniteHighKTensor.tuple R D u arch) w (archArgument R w z)

theorem global_weyl_product
    (hfull : FiniteFullProduct.FullArchProduct R D)
    (hn : ∀ u, fourier R Q.dq (T.theta u) 1 ≠ 0)
    (u : R.A.UnitQuotient)
    (arch : InfinitePlace F → KPGlobalResidualConstruction.complexCore)
    (harch : ∀ w, D.ell (Sum.inl w) (arch w) ≠ 0) (z : R.A.G) :
    fourier R Q.dq (FiniteHighKTensor.source R D u arch)
      (MomentSources.diagonal R z *
        KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12) =
      fourier R Q.dq (FiniteHighKTensor.source R D u arch) 1 *
        (∏ p : R.A.Sf,
          weylValue R D p (normalizedSelectedVector R D u p) (z.2 p)) *
        ∏ w, FiniteFullProduct.archRatio R D (frozenStage R D u)
          (FiniteHighKTensor.tuple R D u arch) w (archArgument R w (z.1 w)) := by
  have h := FiniteFullProduct.frozen_weyl_product R D hfull
    (frozenStage R D u) (frozenStage_exact R D u) (FiniteHighKTensor.tuple R D u arch)
    (FiniteHighKTensor.source_scalar_nonzero R D hn u arch harch) z
  simpa only [FiniteHighKTensor.tuple_finite, normalized_finiteWeyl,
    archArgument, archWeylMatrix] using h

theorem period_split (θ : HeckeCharacter F) (u : R.A.UnitQuotient) (z : R.A.G) :
    GlobalTargetPeriod.period R θ u z =
      (∏ w : InfinitePlace F, (infiniteComponent F w θ (z.1 w) : ℂ)⁻¹) *
        ∏ p : R.A.Sf, (TargetFinitePeriod.localPeriod R θ u p (z.2 p) : ℂ) := by
  have hc : QuotientGroup.mk' R.A.sixthPowers z =
      QuotientGroup.mk' R.A.sixthPowers (1, z.2) := by
    apply (ProjectFiniteClass.axiomFiniteClassEquiv R.A).injective
    rfl
  have hp : TargetFinitePeriod.sectorPhaseHom R u z =
      TargetFinitePeriod.sectorPhaseHom R u (1, z.2) := by
    change R.σ ((R.A.H_S6 _ (QuotientGroup.mk' R.A.sixthPowers z) : Fˣ) : F) = _
    rw [hc]
  rw [GlobalTargetPeriod.period_spec, TargetFinitePeriod.localPeriod_product, hp,
    mul_inv_rev, Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  ring

/-- The table's class mask is the literal Axiom inverse-square mask of
the full S-local point, including its chosen allowed complement. -/
theorem table_mask_literal
    (κ : SixthLocalClasses F (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))))
    (z : R.A.G) :
    ProjectFiniteClass.reflectedClassMask R.A R.probe.correction.B R.σ κ
      (ProjectFiniteClass.assemble R.A (fun p => QuotientGroup.mk (z.2 p))) =
    if ProjectFiniteClass.skeletonAxiomClassEquiv R.A κ *
        (QuotientGroup.mk' R.A.sixthPowers z)⁻¹ ∈ R.probe.correction.B then
      (R.σ ((R.A.H_S6 (ProjectFiniteClass.skeletonAxiomClassEquiv R.A κ)
        (QuotientGroup.mk' R.A.sixthPowers z) : Fˣ) : F) ^ 2)⁻¹
    else 0 := by
  have he : ProjectFiniteClass.skeletonAxiomClassEquiv R.A
      (ProjectFiniteClass.assemble R.A (fun p => QuotientGroup.mk (z.2 p))) =
      QuotientGroup.mk' R.A.sixthPowers z := by
    apply (ProjectFiniteClass.axiomFiniteClassEquiv R.A).injective
    simp only [ProjectFiniteClass.skeletonAxiomClassEquiv, MulEquiv.trans_apply,
      MulEquiv.apply_symm_apply, ProjectFiniteClass.assemble,
      ProjectFiniteClass.axiomFiniteClassEquiv_mk]
  rw [ProjectFiniteClass.reflectedClassMask_spec, he]

/-- The literal weighted reflected Fourier coefficient equals the actual
finite/archimedean tensor whose Mellin transform has already been proved.
There is no global reflection identity among the hypotheses. -/
theorem reflectedTensor_eq
    (hfull : FiniteFullProduct.FullArchProduct R D)
    (hn : ∀ u, fourier R Q.dq (T.theta u) 1 ≠ 0)
    (θ : HeckeCharacter F) (u : R.A.UnitQuotient)
    (arch : InfinitePlace F → KPGlobalResidualConstruction.complexCore)
    (harch : ∀ w, D.ell (Sum.inl w) (arch w) ≠ 0)
    (κ : SixthLocalClasses F (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))))
    (z : R.A.G) :
    ProjectFiniteClass.reflectedClassMask R.A R.probe.correction.B R.σ κ
      (ProjectFiniteClass.assemble R.A (fun p => QuotientGroup.mk (z.2 p))) *
      GlobalTargetPeriod.period R θ u z *
      fourier R Q.dq (FiniteHighKTensor.source R D u arch)
        (MomentSources.diagonal R z *
          KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12) =
    FiniteSheetMellin.reflectedTensor R D θ
      (fourier R Q.dq (FiniteHighKTensor.source R D u arch) 1)
      (archLocal R D θ u arch) u κ z := by
  rw [global_weyl_product R D hfull hn u arch harch, period_split]
  simp only [FiniteSheetMellin.reflectedTensor, ProjectedFiniteIntegral.finiteMellinIntegrand,
    archLocal, Complex.cpow_zero, mul_one, Finset.prod_mul_distrib]
  ring

end ThetaGlobal.FiniteHighKWeyl

#print axioms ThetaGlobal.FiniteHighKWeyl.global_weyl_product
#print axioms ThetaGlobal.FiniteHighKWeyl.reflectedTensor_eq
