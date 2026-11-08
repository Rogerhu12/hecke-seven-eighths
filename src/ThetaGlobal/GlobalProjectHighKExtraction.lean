module

public import ThetaGlobal.GlobalProjectForwardExtraction
public import ThetaGlobal.GlobalProjectHighKReflection

@[expose] public section

/-!
# The signed extraction uses the actual high K-type source

The frozen stage of the selected projected tensor is exactly `D.bad`.
Transporting along that equality identifies the high K-type replacement
with the arbitrary frozen tensor of the exterior extraction theorems.
The formulas below therefore concern the same source as the proved
compact-domain Fourier reflection.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.GlobalProjectHighKExtraction

open NumberField MeasureTheory DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.OrbitExpansion ThetaGlobal.GlobalProjectExterior
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)
  {Q : AdmissibleFlatSources R} {T : Realization R Q}
  (D : SourceFactorization R Q T)

def seed (u : R.A.UnitQuotient)
    (arch : InfinitePlace F → KPGlobalResidualConstruction.complexCore) :
    ∀ p : D.bad, actualLocal R D.finiteData p.val :=
  fun p => FiniteHighKTensor.tuple R D u arch
    ⟨p.val, (ProjectedFiniteMellin.frozenStage_exact R D u).symm ▸ p.property⟩

theorem source_eq_badVector (u : R.A.UnitQuotient)
    (arch : InfinitePlace F → KPGlobalResidualConstruction.complexCore) :
    FiniteHighKTensor.source R D u arch = (badVector R D (seed R D u arch)).val :=
  fixedStage_eq_badVector R D (ProjectedFiniteMellin.frozenStage R D u)
    (ProjectedFiniteMellin.frozenStage_exact R D u) (FiniteHighKTensor.tuple R D u arch)

theorem vector_eq_badVector (u : R.A.UnitQuotient)
    (arch : InfinitePlace F → KPGlobalResidualConstruction.complexCore) :
    GlobalProjectHighKReflection.vector R D u arch = badVector R D (seed R D u arch) :=
  Subtype.ext (source_eq_badVector R D u arch)

def directProfile (u : R.A.UnitQuotient)
    (arch : InfinitePlace F → KPGlobalResidualConstruction.complexCore) (y : R.A.G) : ℂ :=
  fourier R Q.dq (FiniteHighKTensor.source R D u arch) (diagonal R y)

def reflectedProfile (u : R.A.UnitQuotient)
    (arch : InfinitePlace F → KPGlobalResidualConstruction.complexCore) (y : R.A.G) : ℂ :=
  fourier R Q.dq (FiniteHighKTensor.source R D u arch)
    (diagonal R y * KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)

theorem forward_average (hR : RootAligned R) (u : R.A.UnitQuotient)
    (arch : InfinitePlace F → KPGlobalResidualConstruction.complexCore)
    (m : ThetaReflectionData.Row R.A)
    (c : GlobalProjectWeightedDigits.Digits R m → ℂ) (x : Fˣ) (y : R.A.G) :
    (∑ d, c d * GlobalCoreSource.rationalPeriod T
      (GlobalProjectHighKReflection.vector R D u arch) (x : F)
      (signedArgument R m true y d)) =
      (GlobalProjectDigitProduct.forwardCoefficient R m c x *
        ∏ᶠ p : ThetaBranch.ExteriorPrime R.A, D.exteriorValue R p x) *
        GlobalProjectConvention.paperHilbert R
          (QuotientGroup.mk' R.A.sixthPowers (R.A.diagonal x))
          (QuotientGroup.mk' R.A.sixthPowers y) ^ 2 *
          directProfile R D u arch (R.A.diagonal x * y) := by
  rw [vector_eq_badVector]
  simpa only [directProfile, source_eq_badVector,
    GlobalProjectForwardExtraction.directProfile] using
    GlobalProjectForwardExtraction.forward_average R D hR (seed R D u arch) m c x y

theorem reverse_average (hR : RootAligned R) (u : R.A.UnitQuotient)
    (arch : InfinitePlace F → KPGlobalResidualConstruction.complexCore)
    (m : ThetaReflectionData.Row R.A)
    (c : GlobalProjectWeightedDigits.Digits R m → ℂ) (x : Fˣ) (y : R.A.G) :
    (∑ d, c d * GlobalCoreSource.rationalPeriod T
      (GlobalProjectHighKReflection.vector R D u arch) (x : F)
      (signedArgument R m false y d)) =
      GlobalProjectSignedExtraction.reverseCoefficient R D m c x *
        GlobalProjectConvention.paperHilbert R
          (QuotientGroup.mk' R.A.sixthPowers (R.A.diagonal x))
          (QuotientGroup.mk' R.A.sixthPowers y⁻¹) ^ 2 *
          reflectedProfile R D u arch (R.A.diagonal x / y) := by
  rw [vector_eq_badVector]
  simpa only [reflectedProfile, source_eq_badVector,
    GlobalProjectSignedExtraction.reflectedProfile] using
    GlobalProjectSignedExtraction.reverse_average R D hR (seed R D u arch) m c x y

end ThetaGlobal.GlobalProjectHighKExtraction
