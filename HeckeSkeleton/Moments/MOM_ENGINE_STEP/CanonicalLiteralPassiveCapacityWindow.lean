import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActiveCapacityWindow
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveActivity
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAllocationAtoms

set_option linter.unusedSectionVars false

/-!
# Small raw-scale errors on the same active passive sources

The passive table keeps quotient scales of an additional actual
allocation. These scales can only decrease the original scale product.
Its own source activity excludes the absent ordinary comparison
rectangle, so the original first and second extraction norm windows
apply without claiming that the earlier signed source was nonzero.

The already computed capacity error is then exactly the small error;
no capacity or normalized child is replaced.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open HeckePort.IdealMobiusDivisorSum
open WholeAllocation

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}

local instance canonicalLiteralPassiveCapacityWindowCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)

/-- An original occurrence allocation divides the two plain scales
by integral norms and removes positive-length slots. -/
theorem allocate_scaleProduct_le (B : ActualColumnAllocation K k) (r : Bool) :
    (d.allocate B).scaleProduct r ≤ d.scaleProduct r := by
  sorry

end CanonicalLiteralRectangles.Atoms

namespace CanonicalLiteralPassiveSource

variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)
variable (paid : FixedChildCharacters K B.keep.card)

theorem table_scaleProduct_le (r : Bool) :
    (table W B A paid).scaleProduct r ≤ d.scaleProduct r := by
  sorry

end CanonicalLiteralPassiveSource

namespace ActualGaussStage.CoveredClassKey

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualGaussStage (E := ℝ) hΓ μv hDiff G finiteTest}
variable {LC RC : SourceCartesianCover G.columns G.ideal}
variable (v : s.CoveredClassKey LC RC)


variable {H J : Type*} [Fintype J] [DecidableEq J]
variable (rows : ActualSecondCorrelationRows A σ H J)

/-- The new passive source supplies the activity used here. -/
theorem literalLeftAtoms_passiveActiveRawError
    (atoms : CanonicalLiteralRectangles.Atoms (K := K) v.literalLeftParent.slotCount)
    (scalar : ℂ) (balance : Bool → ℝ)
    (W : (((v.literalLeftAtoms atoms).scale scalar).balancePlain balance).ProfileData)
    (B : ActualColumnAllocation K v.leftSlots)
    (paid : FixedChildCharacters K B.keep.card)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (label : { a // a ∈ CanonicalLiteralPassiveSource.labels W B A M })
    (side : SecondColumnSide) (firstSign : ℝ) (r : Bool)
    (hactive : ¬ ∀ ξ,
      (CanonicalLiteralPassiveFrames.frame W B A paid C rows side M label firstSign r)
        .source.energy (σ := σ) ξ = 0)
    (a : RealParameters) (step : ℝ)
    (geometry : OriginalNominalGeometry (K := K) a atoms.base step)
    (hsecond : geometry.ideals.second.val = v.1.val.1)
    (annulus : ℝ) (hannulus : 1 ≤ annulus) (cap : ℕ)
    (hcap : v.literalLeftParent.slotCount ≤ cap)
    (hprime : atoms.PrimeNormWindow annulus)
    (hslots : ∀ i, v.literalLeftParent.reindex.slots i = atoms.slots i)
    (hfirst : ∀ r, r = false ∨ atoms.centered = true →
      atoms.scaleProduct r * (Ideal.absNorm geometry.literalFirstExtraction.val : ℝ) ≤
        annulus ^ cap * atoms.base ^ (a.n₁ + a.n₂ + a.z))
    (error : ℝ) (hthreshold : annulus ^ (2 * cap) ≤ atoms.base ^ error) :
    (CanonicalLiteralPassiveSource.table W B A paid).computedRawError
      geometry.skeleton.rawDegree error r = error := by
  sorry

/-- The new passive source supplies the activity used here. -/
theorem literalRightAtoms_passiveActiveRawError
    (atoms : CanonicalLiteralRectangles.Atoms (K := K) v.literalRightParent.slotCount)
    (scalar : ℂ) (balance : Bool → ℝ)
    (W : (((v.literalRightAtoms atoms).scale scalar).balancePlain balance).ProfileData)
    (B : ActualColumnAllocation K v.literalRightBranch.keep.card)
    (paid : FixedChildCharacters K B.keep.card)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (label : { a // a ∈ CanonicalLiteralPassiveSource.labels W B A M })
    (side : SecondColumnSide) (firstSign : ℝ) (r : Bool)
    (hactive : ¬ ∀ ξ,
      (CanonicalLiteralPassiveFrames.frame W B A paid C rows side M label firstSign r)
        .source.energy (σ := σ) ξ = 0)
    (a : RealParameters) (step : ℝ)
    (geometry : OriginalNominalGeometry (K := K) a atoms.base step)
    (hsecond : geometry.ideals.second.val = v.1.val.2)
    (annulus : ℝ) (hannulus : 1 ≤ annulus) (cap : ℕ)
    (hcap : v.literalRightParent.slotCount ≤ cap)
    (hprime : atoms.PrimeNormWindow annulus)
    (hslots : ∀ i, v.literalRightParent.reindex.slots i = atoms.slots i)
    (hfirst : ∀ r, r = false ∨ atoms.centered = true →
      atoms.scaleProduct r * (Ideal.absNorm geometry.literalFirstExtraction.val : ℝ) ≤
        annulus ^ cap * atoms.base ^ (a.n₁ + a.n₂ + a.z))
    (error : ℝ) (hthreshold : annulus ^ (2 * cap) ≤ atoms.base ^ error) :
    (CanonicalLiteralPassiveSource.table W B A paid).computedRawError
      geometry.skeleton.rawDegree error r = error := by
  sorry

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.allocate_scaleProduct_le

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveSource.table_scaleProduct_le

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalLeftAtoms_passiveActiveRawError

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalRightAtoms_passiveActiveRawError
