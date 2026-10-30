module

public import ThetaGlobal.GlobalProjectLiteralDigitWeights
public import ThetaGlobal.FiniteHighKTensor

@[expose] public section

/-!
# Concrete marked Fourier reflection for the actual high K-type tensor

The vector below changes only the archimedean components of the actual
selected projected tensor.  Its residual-module membership and full
exterior compact invariance are proved.  A compact measurable fundamental
domain is supplied by the existing S-unit tiling theorem.  Thus the
reflection here takes no automorphy, summability, constant-term vanishing,
or fundamental-domain existence as additional inputs.

This is the rational-period stage of the seed identity.  Local evaluation
and the arithmetic supported-frequency reindexing still have to identify
its two series with the project's literal ideal coefficient expressions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.GlobalProjectHighKReflection

open NumberField DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open DedekindZetaZeroFree.ThetaSheetExactUnfolding
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton MeasureTheory
open scoped NumberField Classical Topology BigOperators

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)
  {Q : AdmissibleFlatSources R} {T : Realization R Q}
  (D : SourceFactorization R Q T)

def vector (u : R.A.UnitQuotient)
    (arch : InfinitePlace F → KPGlobalResidualConstruction.complexCore) :
    sameResidueModule T :=
  ⟨FiniteHighKTensor.source R D u arch, FiniteHighKTensor.source_same_residue R D u arch⟩

theorem vector_exterior (u : R.A.UnitQuotient)
    (arch : InfinitePlace F → KPGlobalResidualConstruction.complexCore) :
    GlobalProjectExterior.FullExteriorInvariant R (vector R D u arch).val :=
  GlobalProjectExterior.fixedStage_fullExteriorInvariant R D
    (ProjectedFiniteMellin.frozenStage R D u) (ProjectedFiniteMellin.frozenStage_exact R D u)
    (FiniteHighKTensor.tuple R D u arch)

def series (u : R.A.UnitQuotient)
    (arch : InfinitePlace F → KPGlobalResidualConstruction.complexCore)
    (m : ThetaReflectionData.Row R.A)
    (c : GlobalProjectWeightedDigits.Digits R m → ℂ)
    (θ : HeckeCharacter F) (w : InfinitePlace F)
    (μG : Measure R.A.G) [μG.IsHaarMeasure] (l : PositiveAxis)
    (Ω : Set (Sheet R.A l)) (b : Bool) : ℂ :=
  ∑' a : Fˣ, ∫ y in Ω,
    GlobalProjectUnfolding.weight R (GlobalTargetPeriod.period R θ u) R.probe.correction.B y.val *
      ∑ d, c d * GlobalCoreSource.rationalPeriod T (vector R D u arch) (a : F)
        (signedArgument R m b y.val d) ∂sheetHaar R.A w μG l

/-- The actual high-K vector with literal ordinary/punctured/marked
project weights satisfies the rational-frequency reflection identity.
The remaining `ResidualConstantTerm` is the selected source's proved
radial model, not a constant-term hypothesis about this high-K vector. -/
theorem exists_compact_domain_literal_reflection
    (C : ResidualConstantTerm R Q T)
    (Adata : ThetaArithmeticData F (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))))
    (u : R.A.UnitQuotient)
    (arch : InfinitePlace F → KPGlobalResidualConstruction.complexCore)
    (m : ThetaReflectionData.Row R.A)
    (j : GlobalProjectWeightedDigits.Places R m → Fin 6)
    (marked : GlobalProjectWeightedDigits.Places R m → Bool)
    (θ : HeckeCharacter F) (hS : conductorPlaces F θ ⊆ R.A.Sf)
    (w : InfinitePlace F)
    (hk : heckeComplexWeight F w (R.A.complex_place w) θ ≠ 0)
    (μG : Measure R.A.G) [μG.IsHaarMeasure] (l : PositiveAxis) :
    ∃ Ω : Set (Sheet R.A l), MeasurableSet Ω ∧ IsCompact (closure Ω) ∧
      IsFundamentalDomain R.A.Gamma1 Ω (sheetHaar R.A w μG l) ∧
      series R D u arch m (GlobalProjectLiteralDigitWeights.tensorWeight R Adata m j marked)
        θ w μG l Ω true =
      series R D u arch m (GlobalProjectLiteralDigitWeights.tensorWeight R Adata m j marked)
        θ w μG l Ω false := by
  obtain ⟨Ω, hΩm, hΩc, _, hΩ⟩ := exists_sheetFundamentalDomain R.A w μG l
  refine ⟨Ω, hΩm, hΩc, hΩ, ?_⟩
  exact GlobalProjectWeightedSheet.target_sheet_fourier_identity R m
    (GlobalProjectLiteralDigitWeights.tensorWeight R Adata m j marked)
    (GlobalProjectLiteralDigitWeights.tensorWeight_reindexInvariant R Adata m j marked)
    C (vector R D u arch) (vector_exterior R D u arch) θ hS u w hk μG l Ω hΩ hΩc

end ThetaGlobal.GlobalProjectHighKReflection
