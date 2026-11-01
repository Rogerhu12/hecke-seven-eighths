import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalExistingBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalPairBinding

/-!
# The stored original theta class is the actual exceptional source

The already computed extraction and binding determine the same rows,
residual ideals, allocations and Fourier locations. Reciprocal profile
balancing preserves both complete centered columns. This exact identity
therefore connects the paid terminal factory to the original stored
integrand, with the first scalar pair outside and the second common
atoms still in its row weight.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable {ν : Measure (FiniteAdeleRing (𝓞 K) K)} [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

local instance canonicalLiteralExceptionalStoredSourceCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace ActualGaussStage.CoveredClassKey

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualGaussStage (E := ℝ) hΓ μv hDiff G finiteTest}
variable {LC RC : SourceCartesianCover G.columns G.ideal}
variable (v : s.CoveredClassKey LC RC)
variable (leftAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (LC.branch v.2.2.1).slotCount)
variable (rightAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (RC.branch v.2.2.2.1).slotCount)
variable (exceptional : s.CoverHybridPredicates LC RC)
variable (firstKernel : SchwartzMap ℝ ℂ) (x : ι → ℝ) (j : v.AllocationKey)
variable (firstSign : ℝ) (hlive : (v.leaf exceptional firstKernel x j).Live)
variable (X : (v.leaf exceptional firstKernel x j).ConstantAtomExtraction)
variable (binding : X.leaf.OrdinaryBinding
  (v.literalRectangles leftAtoms rightAtoms exceptional firstKernel x j firstSign hlive))
variable (leftScalar rightScalar : ℂ)
variable (hleftScalar : leftScalar ≠ 0) (hrightScalar : rightScalar ≠ 0)
variable (leftBalance rightBalance : Bool → ℝ)
variable (hleftBalance : ∀ r, 0 < leftBalance r)
variable (hrightBalance : ∀ r, 0 < rightBalance r)


variable {theta : Finset (HeckeCharacter K)}
variable (Q : PairedFiniteCharacters theta
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ))
variable (hpredicate : (v.leaf exceptional firstKernel x j).exceptional = Q.exceptional)
variable (thetaPair : theta × theta)

local notation "baseRows" => v.literalSupportedRows leftAtoms rightAtoms
local notation "classRows" => baseRows.restrictRows (Q.thetaClass thetaPair)
local notation "allocation" => v.literalAllocation exceptional firstKernel x j hlive
local notation "leftTable" =>
  ((v.literalLeftAtoms leftAtoms).scale leftScalar⁻¹).balancePlain leftBalance
local notation "rightTable" =>
  ((v.literalRightAtoms rightAtoms).scale rightScalar⁻¹).balancePlain rightBalance
local notation "leftIdeal" => fun i => v.block.leftResidual (v.leftReindex.index i)
local notation "rightIdeal" => fun i => v.block.rightResidual (v.rightReindex.index i)
local notation "leftColumns" => (Finset.mem_filter.mp allocation.property).2.2.1
local notation "rightColumns" => (Finset.mem_filter.mp allocation.property).2.2.2
local notation "leftFrame" =>
  (leftTable.factors classRows .left j.2.1 leftIdeal v.leftReindex.ideal_product firstSign false).
    frame C j.1.val j.2.2.1.val leftColumns
local notation "rightFrame" =>
  (rightTable.factors classRows .right j.2.1 rightIdeal v.rightReindex.ideal_product
    (-firstSign) false).frame C j.1.val j.2.2.2.val rightColumns
local notation "EL" => CanonicalLiteralExceptionalFactory.comparison
  leftTable (SecondColumnSide.left.phase PUnit.{1} j.2.1)
local notation "ER" => CanonicalLiteralExceptionalFactory.comparison
  rightTable (SecondColumnSide.right.phase PUnit.{1} j.2.1)

include binding hpredicate hleftBalance hrightBalance in
/-- This identity uses the actual redistributed common extraction.
Every side frame is computed from the same residual atom table and the
same original allocation. Neither whole centered column is separated
before its absolute value is taken. -/
theorem literalStripOuter_theta_integrand (z : ℝ × ℝ) :
    ((X.stripOuter leftScalar rightScalar hleftScalar hrightScalar).
      thetaClassLeaf Q thetaPair).exceptionalIntegrand z =
        leftFrame.exceptionalMagnitude rightFrame EL ER Q (WithLp.toLp 2 z) := by
  have hb := (v.stripExistingOuterBinding leftAtoms rightAtoms exceptional
    firstKernel x j firstSign hlive X binding leftScalar rightScalar
    hleftScalar hrightScalar leftBalance rightBalance hleftBalance hrightBalance).
      thetaClass_integrand Q hpredicate thetaPair z
  have hp := CanonicalLiteralExceptionalPairBinding.theta_pair_magnitude
    baseRows Q thetaPair leftTable rightTable j.2.1 leftIdeal rightIdeal
    v.leftReindex.ideal_product v.rightReindex.ideal_product firstSign j.1.val
    j.2.2.1.val j.2.2.2.val leftColumns rightColumns (WithLp.toLp 2 z)
  have hl : leftTable.whole = ((v.literalLeftAtoms leftAtoms).scale leftScalar⁻¹).whole :=
    funext (((v.literalLeftAtoms leftAtoms).scale leftScalar⁻¹).
      balancePlain_whole leftBalance hleftBalance)
  have hr : rightTable.whole = ((v.literalRightAtoms rightAtoms).scale rightScalar⁻¹).whole :=
    funext (((v.literalRightAtoms rightAtoms).scale rightScalar⁻¹).
      balancePlain_whole rightBalance hrightBalance)
  rw [hl, hr] at hp
  exact hb.trans hp

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalStripOuter_theta_integrand
