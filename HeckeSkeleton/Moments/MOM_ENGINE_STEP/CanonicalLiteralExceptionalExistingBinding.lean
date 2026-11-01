import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralStripExistingBinding

/-!
# Keep the actual second common row after the first scalar extraction

The original direct, main and residual constructors already supply the
atom extraction and its coefficient dictionary. In particular, after
norm-factor redistribution those objects contain the newly computed
second common coefficient. This transformation uses precisely that
binding, and moves only the first scalar pair to the outer weight.

No coefficient identity, row classification or source estimate is
assumed afresh. The actual rows, both kernels and both column sets are
the ones in the supplied original construction.
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

local instance canonicalLiteralExceptionalExistingBindingCircleCharacterFintype :
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

/-- In contrast with the ordinary stripped dictionary, the rows here
contain exactly the actual second common atoms. The two first scalars
are already in the outer weight of `stripOuter`. -/
def stripExistingOuterBinding :
    (X.stripOuter leftScalar rightScalar hleftScalar hrightScalar).OrdinaryBinding
      (v.literalStripOuterRectangles leftAtoms rightAtoms exceptional firstKernel x j
        leftScalar rightScalar firstSign hlive leftBalance rightBalance
          hleftBalance hrightBalance) := by
  let stripped := v.stripExistingOrdinaryBinding leftAtoms rightAtoms
    exceptional firstKernel x j firstSign hlive X binding
    leftScalar rightScalar hleftScalar hrightScalar
    leftBalance rightBalance hleftBalance hrightBalance
  exact
    { rows := binding.rows
      rows_zero := binding.rows_zero
      left := binding.left
      right := binding.right
      exceptional := binding.exceptional
      rowWeight := binding.rowWeight
      leftCoefficient := stripped.leftCoefficient
      rightCoefficient := stripped.rightCoefficient
      leftPoint := binding.leftPoint
      rightPoint := binding.rightPoint }

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.stripExistingOuterBinding
