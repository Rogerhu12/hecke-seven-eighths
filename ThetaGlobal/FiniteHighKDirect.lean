module

public import ThetaGlobal.FiniteNormalizedMellin

/-!
# The actual high K-type direct coefficient and its finite cutoff

The finite diagonal product is recovered from the projected source's
proved radial identity.  Replacing its archimedean components preserves
that finite product.  The direct unfolding weight uses the positive
infinity character, while the reflected weight uses its inverse.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
noncomputable section

namespace ThetaGlobal.FiniteHighKDirect

open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources DedekindZetaZeroFree.ThetaExpansion
open DedekindZetaZeroFree.KPAdelicCoverRestrictedProduct
open DedekindZetaZeroFree.KPLiteralScalarHCCompactOrbit
open DedekindZetaZeroFree.KPCplxCharacterHaar
open DedekindZetaZeroFree.FourierContinuation.ComplexLines
open DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.FiniteCoreProduct ThetaGlobal.ProjectedFiniteMellin
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def finiteDiagonalRaw (z : R.A.G) (q : KPFinitePlace F) :
    KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) :=
  if hq : q ∈ R.A.Sf then
    KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) (z.2 ⟨q, hq⟩)
  else 1

def archDiagonalMatrix (z : R.A.G) (w : InfinitePlace F) : ComplexGL2 :=
  KPCplxCharacterHaar.diagonal
    (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (R.A.complex_place w)).toMonoidHom (z.1 w))

theorem diagonal_geometry (z : R.A.G) :
    MomentSources.diagonal R z =
      (finiteBase (R := R) (finiteDiagonalRaw R z)).val *
        archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12 (archDiagonalMatrix R z) := by
  rw [finiteBase_val]
  change tupleLift R (KPRationalAdelicSplitting.ATuple F R.A.zeta12
    R.A.primitive_zeta12 (localIdele R z)) =
      tupleLift R (finiteTuple (R := R) (finiteDiagonalRaw R z)) *
        tupleLift R (KPLiteralChamber.sectionTuple F R.A.zeta12
          R.A.primitive_zeta12 (archDiagonalMatrix R z))
  rw [← map_mul]
  apply congrArg (tupleLift R)
  apply RestrictedProduct.ext
  intro p
  cases p with
  | inl w =>
    change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
      (Units.map (adeleEval F (Sum.inl w)) (localIdele R z)) =
        finiteTuple (R := R) (finiteDiagonalRaw R z) (Sum.inl w) * _
    rw [SheetRescaling.localIdele_eval_arch R z w,
      finiteTuple_off (finiteDiagonalRaw R z) (Sum.inl w) (fun _ => Sum.inl_ne_inr), one_mul]
    change KPLocalCover.CubicGL2Raw.mk _ _ = KPLocalCover.CubicGL2Raw.mk _ _
    simp only [KPLocalCover.sectionMap]
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [archDiagonalMatrix, KPCplxCharacterHaar.diagonal, KubotaRankTwo.d,
        Matrix.GeneralLinearGroup.map]
    change (z.1 w : w.Completion) =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).symm
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w))
          (z.1 w : w.Completion))
    exact ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (R.A.complex_place w)).symm_apply_apply _).symm
  | inr q =>
    change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)
      (Units.map (adeleEval F (Sum.inr q)) (localIdele R z)) =
        finiteTuple (R := R) (finiteDiagonalRaw R z) (Sum.inr q) * 1
    rw [mul_one]
    by_cases hq : q ∈ R.A.Sf
    · rw [DigitMasks.localIdele_finite R z q hq,
        finiteTuple_at (finiteDiagonalRaw R z) ⟨q, hq⟩, finiteDiagonalRaw, dif_pos hq]
    · rw [DigitMasks.localIdele_exterior R z q hq, KPStandardLocalRootLifts.A_one,
        finiteTuple_off (finiteDiagonalRaw R z) (Sum.inr q)
          (fun p h => hq (Sum.inr.inj h ▸ p.property))]

theorem archDiagonalMatrix_one (z : ∀ p : R.A.Sf, (p.val.adicCompletion F)ˣ) :
    archDiagonalMatrix R (1, z) = 1 := by
  funext w
  simp only [archDiagonalMatrix, Prod.fst, Pi.one_apply, map_one]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [KPCplxCharacterHaar.diagonal]

theorem finiteBase_diagonal (z : ∀ p : R.A.Sf, (p.val.adicCompletion F)ˣ) :
    (finiteBase (R := R) (finiteDiagonalRaw R (1, z))).val =
      MomentSources.diagonal R (1, z) := by
  rw [diagonal_geometry, archDiagonalMatrix_one, map_one, mul_one]

theorem cutoffProduct_eq_indicator (B : FirstRootCutoffs R)
    (z : ∀ p : R.A.Sf, (p.val.adicCompletion F)ˣ) :
    FiniteDirectMellin.cutoffProduct R B z =
      if ∀ p, z p ∈ B.cutoff p then 1 else 0 := by
  by_cases hz : ∀ p, z p ∈ B.cutoff p
  · simp [FiniteDirectMellin.cutoffProduct, hz]
  · obtain ⟨p, hp⟩ := not_forall.mp hz
    rw [if_neg hz]
    exact Finset.prod_eq_zero (Finset.mem_univ p) (Set.indicator_of_notMem hp _)

variable (θ : HeckeCharacter F) (C : FiniteFixedSource.Source R θ)
variable (L : FiniteLocalHighK.Input R θ C)

local notation "D" => C.projected.base.factorization
local notation "Q" => C.projected.base.sources
local notation "T" => C.projected.base.realization

def finiteProduct (u : R.A.UnitQuotient)
    (z : ∀ p : R.A.Sf, (p.val.adicCompletion F)ˣ) : ℂ :=
  ∏ p : R.A.Sf, D.ell (Sum.inr p.val)
    (finiteAction R D (finiteDiagonalRaw R (1, z)) (Sum.inr p.val)
      (selectedFiniteVector R D u p)) /
      D.ell (Sum.inr p.val) (selectedFiniteVector R D u p)

theorem selected_finite_product (u : R.A.UnitQuotient)
    (z : ∀ p : R.A.Sf, (p.val.adicCompletion F)ˣ) :
    finiteProduct R θ C u z = FiniteDirectMellin.cutoffProduct R C.projected.cutoffs z := by
  have hn := FiniteFixedSource.Source.period_nonzero R θ C u
  have hsource : stageFunction R D (frozenStage R D u) (frozenTuple R D u) = T.theta u :=
    selected_source_provenance R D u
  have hfin := normalized_matrix_product R D (finiteDiagonalRaw R (1, z))
    (frozenStage R D u) (frozenStage_exact R D u) (frozenTuple R D u)
    (by simpa only [stageCoefficient, hsource] using hn)
  rw [finiteBase_diagonal] at hfin
  change fourier R Q.dq (stageFunction R D _ _) (MomentSources.diagonal R (1, z)) =
    fourier R Q.dq (stageFunction R D _ _) 1 * finiteProduct R θ C u z at hfin
  rw [hsource] at hfin
  have hrad : fourier R Q.dq (T.theta u) (MomentSources.diagonal R (1, z)) =
      FiniteDirectMellin.cutoffProduct R C.projected.cutoffs z *
        fourier R Q.dq (T.theta u) 1 := by
    rw [C.projected.radial, ← ThetaExpansion.diagonal_one R, C.projected.radial,
      cutoffProduct_eq_indicator]
    simp only [firstRootRadialProfile, firstRootSphericalProduct, Prod.fst_one,
      Prod.snd_one, Pi.one_apply, Subgroup.one_mem, implies_true, if_true, one_mul]
  apply mul_left_cancel₀ hn
  exact hfin.symm.trans (hrad.trans (mul_comm _ _))

theorem global_diagonal_product (u : R.A.UnitQuotient) (z : R.A.G) :
    fourier R Q.dq (FiniteHighKTensor.source R D u L.vector) (MomentSources.diagonal R z) =
      fourier R Q.dq (FiniteHighKTensor.source R D u L.vector) 1 *
        FiniteDirectMellin.cutoffProduct R C.projected.cutoffs z.2 *
        ∏ w : InfinitePlace F,
          L.functional w (KPCplxActualImage.imageAction
            FourierContinuation.ComplexLines.traceFrequency
            (Matrix.ProjGenLinGroup.mk (archDiagonalMatrix R z w))
            (harmonicInclusion (L.vector w))) /
          L.functional w (harmonicInclusion (L.vector w)) := by
  rw [diagonal_geometry]
  have h := FiniteFullProduct.normalized_full_matrix_product R D C.fullArchProduct
    (frozenStage R D u) (frozenStage_exact R D u) (FiniteHighKTensor.tuple R D u L.vector)
    (FiniteHighKTensor.source_scalar_nonzero R D
      (FiniteFixedSource.Source.period_nonzero R θ C) u L.vector L.source_nonzero)
    (finiteDiagonalRaw R z) (archDiagonalMatrix R z)
  simp only [FiniteHighKTensor.tuple_finite,
    FiniteLocalHighK.archRatio_local R θ C L] at h
  change _ = _ * finiteProduct R θ C u z.2 * _ at h
  rw [selected_finite_product R θ C] at h
  exact h

/-- The actual finite target period is trivial on the projected cutoff.
Consequently the inverse period in the direct unfolding has positive
archimedean Hecke components. -/
theorem inverse_period_cutoff (u : R.A.UnitQuotient) (z : R.A.G) :
    (GlobalTargetPeriod.period R θ u z)⁻¹ *
        FiniteDirectMellin.cutoffProduct R C.projected.cutoffs z.2 =
      (∏ w : InfinitePlace F, (infiniteComponent F w θ (z.1 w) : ℂ)) *
        FiniteDirectMellin.cutoffProduct R C.projected.cutoffs z.2 := by
  by_cases hz : ∀ p, z.2 p ∈ C.projected.cutoffs.cutoff p
  · have hfinite : (∏ p : R.A.Sf,
        (TargetFinitePeriod.localPeriod R θ u p (z.2 p) : ℂ)) = 1 := by
      apply Finset.prod_eq_one
      intro p _
      rw [TargetFinitePeriod.localPeriod_on_cutoff R θ C.projected.cutoffs
        C.target_kernel u p (z.2 p) (hz p), Circle.coe_one]
    rw [FiniteHighKWeyl.period_split, hfinite, mul_one,
      ← Finset.prod_inv_distrib, inv_inv]
  · have hzero : FiniteDirectMellin.cutoffProduct R C.projected.cutoffs z.2 = 0 := by
      rw [cutoffProduct_eq_indicator, if_neg hz]
    rw [hzero, mul_zero, mul_zero]

/-- Literal direct weighted Fourier coefficient of the same high K-type
source used in the Weyl/reflected product. -/
theorem directTensor_eq (u : R.A.UnitQuotient) (z : R.A.G) :
    (GlobalTargetPeriod.period R θ u z)⁻¹ *
      fourier R Q.dq (FiniteHighKTensor.source R D u L.vector)
        (MomentSources.diagonal R z) =
    FiniteDirectMellin.directTensor R C.projected.cutoffs
      (fourier R Q.dq (FiniteHighKTensor.source R D u L.vector) 1)
      (FiniteNormalizedMellin.archProfile R θ C L false) z := by
  rw [global_diagonal_product R θ C L]
  calc
    _ = fourier R Q.dq (FiniteHighKTensor.source R D u L.vector) 1 *
        ((GlobalTargetPeriod.period R θ u z)⁻¹ *
          FiniteDirectMellin.cutoffProduct R C.projected.cutoffs z.2) *
        ∏ w : InfinitePlace F,
          L.functional w (KPCplxActualImage.imageAction traceFrequency
            (Matrix.ProjGenLinGroup.mk (archDiagonalMatrix R z w))
            (harmonicInclusion (L.vector w))) /
          L.functional w (harmonicInclusion (L.vector w)) := by ring
    _ = _ := by
      rw [inverse_period_cutoff R θ C]
      simp only [FiniteDirectMellin.directTensor,
        FiniteNormalizedMellin.archProfile, FiniteLocalHighK.localProfile,
        FiniteLocalHighK.localArgument, Bool.false_eq_true, if_false, mul_one,
        mul_div_assoc, Finset.prod_mul_distrib, archDiagonalMatrix]
      ring

/-- A nonzero direct finite factor forces the full S-local sixth class
to be one.  Infinite coordinates introduce no class obstruction. -/
theorem cutoff_class_one (B : FirstRootCutoffs R) (z : R.A.G)
    (hz : ∀ p, z.2 p ∈ B.cutoff p) :
    QuotientGroup.mk' R.A.sixthPowers z = 1 := by
  apply (ProjectFiniteClass.axiomFiniteClassEquiv R.A).injective
  rw [map_one, ProjectFiniteClass.axiomFiniteClassEquiv_mk]
  funext p
  exact (QuotientGroup.eq_one_iff _).mpr (B.sixth p (z.2 p) (hz p))

theorem global_diagonal_class_support (u : R.A.UnitQuotient) (z : R.A.G)
    (hz : QuotientGroup.mk' R.A.sixthPowers z ≠ 1) :
    fourier R Q.dq (FiniteHighKTensor.source R D u L.vector)
      (MomentSources.diagonal R z) = 0 := by
  have hcut : ¬ ∀ p, z.2 p ∈ C.projected.cutoffs.cutoff p :=
    fun h => hz (cutoff_class_one R C.projected.cutoffs z h)
  rw [global_diagonal_product R θ C L, cutoffProduct_eq_indicator,
    if_neg hcut, mul_zero, zero_mul]

theorem directTensor_class_support (u : R.A.UnitQuotient) (z : R.A.G)
    (hz : QuotientGroup.mk' R.A.sixthPowers z ≠ 1) :
    FiniteDirectMellin.directTensor R C.projected.cutoffs
      (fourier R Q.dq (FiniteHighKTensor.source R D u L.vector) 1)
      (FiniteNormalizedMellin.archProfile R θ C L false) z = 0 := by
  rw [← directTensor_eq R θ C L u z, global_diagonal_class_support R θ C L u z hz,
    mul_zero]

end ThetaGlobal.FiniteHighKDirect

#print axioms ThetaGlobal.FiniteHighKDirect.global_diagonal_product
#print axioms ThetaGlobal.FiniteHighKDirect.directTensor_eq
#print axioms ThetaGlobal.FiniteHighKDirect.global_diagonal_class_support
