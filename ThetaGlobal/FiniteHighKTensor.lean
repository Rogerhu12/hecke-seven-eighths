import ThetaGlobal.FiniteProjectedMellin
import ThetaGlobal.FiniteCoreProduct

/-!
# Replacing only the archimedean vectors, with the exact scalar retained

The finite Mellin table uses the actual finite components of the selected
target-projected tensor.  A high K-type replacement changes its complex
components and retains those finite components literally.  This module
records both facts, and computes the new source's Fourier coefficient at
one from its actual local functionals.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.FiniteHighKTensor

open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open ThetaGlobal.ProjectedFiniteMellin ThetaGlobal.FiniteCoreProduct
open scoped Classical NumberField BigOperators

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T)

def tuple (u : R.A.UnitQuotient)
    (arch : InfinitePlace F → KPGlobalResidualConstruction.complexCore) :
    ∀ p : (frozenStage R D u).val, actualLocal R D.finiteData p.val :=
  fun p => match p with
    | ⟨Sum.inl w, _⟩ => arch w
    | ⟨Sum.inr q, hp⟩ => frozenTuple R D u ⟨Sum.inr q, hp⟩

/-- Every finite vector used in the shell table is unchanged by the
archimedean replacement.  There is no new finite-vector choice. -/
theorem tuple_finite (u : R.A.UnitQuotient)
    (arch : InfinitePlace F → KPGlobalResidualConstruction.complexCore) (p : R.A.Sf) :
    tuple R D u arch ⟨Sum.inr p.val, finite_mem_frozen R D u p⟩ =
      selectedFiniteVector R D u p := rfl

def source (u : R.A.UnitQuotient)
    (arch : InfinitePlace F → KPGlobalResidualConstruction.complexCore) : Functions R :=
  stageFunction R D (frozenStage R D u) (tuple R D u arch)

theorem source_same_residue (u : R.A.UnitQuotient)
    (arch : InfinitePlace F → KPGlobalResidualConstruction.complexCore) :
    source R D u arch ∈ sameResidueModule T := D.core_same_residue _

/-- Exact global normalization of the high K-type source.  In particular
this scalar need not equal that of the original selected source. -/
theorem source_scalar (u : R.A.UnitQuotient)
    (arch : InfinitePlace F → KPGlobalResidualConstruction.complexCore) :
    fourier R Q.dq (source R D u arch) 1 =
      (∏ w : InfinitePlace F, D.ell (Sum.inl w) (arch w)) *
        ∏ p : R.A.Sf, D.ell (Sum.inr p.val) (selectedFiniteVector R D u p) :=
  scalar_product R D (frozenStage R D u) (frozenStage_exact R D u) (tuple R D u arch)

theorem source_scalar_nonzero
    (hn : ∀ u, fourier R Q.dq (T.theta u) 1 ≠ 0)
    (u : R.A.UnitQuotient)
    (arch : InfinitePlace F → KPGlobalResidualConstruction.complexCore)
    (harch : ∀ w, D.ell (Sum.inl w) (arch w) ≠ 0) :
    fourier R Q.dq (source R D u arch) 1 ≠ 0 := by
  rw [source_scalar]
  exact mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun w _ => harch w))
    (Finset.prod_ne_zero_iff.mpr
      (fun p _ => selectedFiniteVector_nonzero R D hn u p))

/-- Finite matrix coefficients of the high K-type replacement are exactly
the old selected finite local ratios times its *new* global scalar. -/
theorem finite_matrix_product
    (hn : ∀ u, fourier R Q.dq (T.theta u) 1 ≠ 0)
    (u : R.A.UnitQuotient)
    (arch : InfinitePlace F → KPGlobalResidualConstruction.complexCore)
    (harch : ∀ w, D.ell (Sum.inl w) (arch w) ≠ 0)
    (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :
    fourier R Q.dq (source R D u arch)
        (SheetRescaling.WeylTensorTransport.finiteBase (R := R) a).val =
      fourier R Q.dq (source R D u arch) 1 *
        ∏ p : R.A.Sf,
          D.ell (Sum.inr p.val)
            (FiniteCoreProduct.finiteAction R D a (Sum.inr p.val)
              (selectedFiniteVector R D u p)) /
          D.ell (Sum.inr p.val) (selectedFiniteVector R D u p) :=
  normalized_matrix_product R D a (frozenStage R D u) (frozenStage_exact R D u)
    (tuple R D u arch) (source_scalar_nonzero R D hn u arch harch)

end ThetaGlobal.FiniteHighKTensor

#print axioms ThetaGlobal.FiniteHighKTensor.source_scalar
#print axioms ThetaGlobal.FiniteHighKTensor.finite_matrix_product
