import DedekindZetaZeroFree.Theta.Whittaker.Sources.LocalLineExistence
import ThetaGlobal.FiniteArchProduct

/-!
# A source whose actual canonical residue map remains visible

The public upstream source-existence chain forgets the canonical model,
fiber data and core map used in its proof.  Retaining that data lets the
arbitrary high K-type archimedean product theorem apply to the very same
source factorization used for finite Mellin coefficients.

`seed_nonempty` is the original proved construction, strengthened only by
remembering its witnesses.  The local measures and tensor map below are
the literal ones in `canonicalTensorLocalLines`; all provenance statements
are definitional equalities.  No new arithmetic choice is made here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.FiniteCanonicalSource

open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources DedekindZetaZeroFree.FourierContinuation
open DedekindZetaZeroFree.FourierContinuation.LiteralSource
open DedekindZetaZeroFree.FourierContinuation.ComplexLines
open DedekindZetaZeroFree.KPGlobalTorusFiniteStages
open DedekindZetaZeroFree.KPLiteralScalarHCCompactOrbit
open DedekindZetaZeroFree.KPCplxCharacterHaar
open DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open scoped Classical NumberField BigOperators

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)

/-- The explicit witnesses already produced in the upstream source
construction.  The nonzero period is proved in `seed_nonempty`. -/
structure Seed where
  model : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12
  fibers : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 model
  exceptional_eq : fibers.exceptional = R.A.Sf
  initial : ∀ j : bad R.A model fibers, Plus R.A model fibers j.val
  initial_nonzero :
    fourier R (KPWildKernelUpperBound.quotientHaar F)
      (coreResidue R model fibers (RestrictedTensorSimple.stageInclusion _ _ _
        ⟨bad R.A model fibers, le_rfl⟩ (PiTensorProduct.tprod ℂ initial))) 1 ≠ 0

include N in
theorem seed_nonempty : Nonempty (Seed R) := by
  obtain ⟨P, C, hP, hC⟩ :=
    EisensteinReferenceSections.FrozenFibers.exists_model_fibers R.A R.classKilled
  obtain ⟨u, hu⟩ := exists_initial_plus_fourier_ne_zero_normalized R P C N hC
  exact ⟨⟨P, C, hC, u, hu⟩⟩

/-- Normalized local additive Haar used in the canonical exceptional
representation, exactly as in the existing source construction. -/
def localHaar (q : KPFinitePlace F) : Measure (q.adicCompletion F) :=
  Measure.addHaarMeasure (TensorSeedSource.integerCompacts q)

local instance (q : KPFinitePlace F) : (localHaar (F := F) q).IsAddHaarMeasure := by
  dsimp only [localHaar]
  infer_instance

theorem localHaar_integer (q : KPFinitePlace F) :
    localHaar (F := F) q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1 :=
  Measure.addHaarMeasure_self

variable (B : Seed R) (hR : RootAligned R)

def localLines : TensorLocalLines R N :=
  canonicalTensorLocalLines R B.model B.fibers localHaar localHaar_integer hR N
    B.exceptional_eq B.initial
    (coreFlatInsertion_initial_exterior_spherical R B.model B.fibers B.exceptional_eq
      (PiTensorProduct.tprod ℂ B.initial)) B.initial_nonzero

/-- This factorization keeps the literal canonical residue map. -/
def factorization : SourceFactorization R (localLines R N B hR).sources
    (localLines R N B hR).realization :=
  (localLines R N B hR).factorization

theorem factorization_finiteData :
    (factorization R N B hR).finiteData =
      actualImageData R B.model B.fibers localHaar localHaar_integer := rfl

theorem factorization_references :
    (factorization R N B hR).references =
      actualReference R B.model B.fibers localHaar localHaar_integer := rfl

theorem factorization_bad :
    (factorization R N B hR).bad = bad R.A B.model B.fibers := rfl

theorem factorization_coreMap :
    (factorization R N B hR).coreMap =
      actualCoreResidue R B.model B.fibers localHaar localHaar_integer N := rfl

theorem factorization_quotientHaar :
    (localLines R N B hR).sources.dq = KPWildKernelUpperBound.quotientHaar F := rfl

/-- Native local Lie actions are inherited from the same explicit map. -/
theorem factorization_native :
    RootDerivatives.SourceNativeLie R (factorization R N B hR) :=
  canonicalCovariantNative_native R B.model B.fibers localHaar localHaar_integer hR N
    B.exceptional_eq B.initial
    (coreFlatInsertion_initial_exterior_spherical R B.model B.fibers B.exceptional_eq
      (PiTensorProduct.tprod ℂ B.initial)) B.initial_nonzero

def haarFactorizedSource : JointHaarFactorizedSources R N :=
  jointHaarFactorizedSources_of_factorization
    (localLines R N B hR).toJointRealizedFlatSources (factorization R N B hR)

/-- The source Fourier period and the arbitrary-vector canonical period
are literally equal, including their additive-quotient Haar. -/
theorem corePeriod_eq
    (s : RestrictedTensorSimple.Level (factorization R N B hR).bad)
    (x : ∀ j : s.val, actualLocal R (factorization R N B hR).finiteData j.val)
    (g : Group R) :
    fourier R (localLines R N B hR).sources.dq
      ((factorization R N B hR).coreMap
        (RestrictedTensorSimple.stageInclusion _ (factorization R N B hR).references
          (factorization R N B hR).bad s (PiTensorProduct.tprod ℂ x))) g =
      actualStagePeriod R B.model B.fibers localHaar localHaar_integer N s x g := rfl

/-- Full high K-type matrix product for this exact source `R,D,N`.
The same actual finite source vector and global scalar are retained. -/
theorem core_full_matrix_product
    (s : RestrictedTensorSimple.Level (factorization R N B hR).bad)
    (x : ∀ j : s.val, actualLocal R (factorization R N B hR).finiteData j.val)
    (hw : ∀ w : InfinitePlace F, Sum.inl w ∈ s.val)
    (hx : actualStagePeriod R B.model B.fibers localHaar localHaar_integer N s x 1 ≠ 0)
    (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (b : InfinitePlace F → ComplexGL2) :
    fourier R (localLines R N B hR).sources.dq
      ((factorization R N B hR).coreMap
        (RestrictedTensorSimple.stageInclusion _ (factorization R N B hR).references
          (factorization R N B hR).bad s (PiTensorProduct.tprod ℂ x)))
        ((finiteBase (R := R) a).val *
          archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12 b) =
      actualStagePeriod R B.model B.fibers localHaar localHaar_integer N s x
        (finiteBase (R := R) a).val *
      ∏ w, FiniteArchProduct.archRatio R B.model B.fibers localHaar localHaar_integer N s x w
        (Matrix.ProjGenLinGroup.mk (b w)) :=
  FiniteArchProduct.full_matrix_product R B.model B.fibers localHaar localHaar_integer N
    s x hw hx a b

end ThetaGlobal.FiniteCanonicalSource

#print axioms ThetaGlobal.FiniteCanonicalSource.seed_nonempty
#print axioms ThetaGlobal.FiniteCanonicalSource.factorization_coreMap
#print axioms ThetaGlobal.FiniteCanonicalSource.factorization_native
#print axioms ThetaGlobal.FiniteCanonicalSource.core_full_matrix_product
