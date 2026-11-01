import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCoveredScaleProduct
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralComputedLengths
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralInactiveRectangle

/-!
# The existing capacity error on each actual active rectangle

The first norm window is the output of the six original direct/main/
pool scale theorems. This module composes it with the stored second
occurrence extraction. Original source activity itself excludes the
absent ordinary rectangle, before using its scale product.

Constant stripping and reciprocal plain balancing preserve these
scales. The computed capacity error therefore equals the preselected
small error on the same actual source. No capacity input, normalized
child, removed set or profile radius is replaced.
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

local instance canonicalLiteralActiveCapacityWindowCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace ActualGaussStage.CoveredClassKey

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualGaussStage (E := ℝ) hΓ μv hDiff G finiteTest}
variable {LC RC : SourceCartesianCover G.columns G.ideal}
variable (v : s.CoveredClassKey LC RC)


variable {H J : Type*} [Fintype J] [DecidableEq J]
variable (rows : ActualSecondCorrelationRows A σ H J)

/-- The activity belongs to the actual allocated left table. Its
first window is supplied by `literalLeftDirectAtoms_originalScale_of_domain`
or the corresponding actual main/pool theorem. -/
theorem literalLeftAtoms_activeRawError
    (atoms : CanonicalLiteralRectangles.Atoms (K := K) v.literalLeftParent.slotCount)
    (scalar : ℂ) (balance : Bool → ℝ)
    (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
    (ideal : AllocationColumn K v.leftSlots → A.Exterior)
    (hideal : ∀ i ∈ childCartesianColumns (v.literalLeftAtoms atoms).plain₁
      (v.literalLeftAtoms atoms).plain₂ (v.literalLeftAtoms atoms).slots,
      (ideal i).val = allocationColumnIdeal i)
    (firstSign : ℝ) (r : Bool) (L : Ideal (𝓞 K))
    (selection : primeSupport L → Finset (Fin (v.leftSlots + 2)))
    (hne : (pairedAllocatedColumns L selection (v.literalLeftAtoms atoms).plain₁
      (v.literalLeftAtoms atoms).plain₂ (v.literalLeftAtoms atoms).slots
      id id HeightOneSpectrum.asIdeal).Nonempty)
    (hactive : ¬ ∀ ξ,
      (((((v.literalLeftAtoms atoms).scale scalar).balancePlain balance).factors
        rows side χ ideal hideal firstSign r).frame C L selection hne).source.energy
          (σ := σ) ξ = 0)
    (a : RealParameters) (step : ℝ)
    (geometry : OriginalNominalGeometry (K := K) a atoms.base step)
    (hsecond : geometry.ideals.second.val = v.1.val.1)
    (B : ℝ) (hB : 1 ≤ B) (cap : ℕ) (hcap : v.literalLeftParent.slotCount ≤ cap)
    (hprime : atoms.PrimeNormWindow B)
    (hslots : ∀ i, v.literalLeftParent.reindex.slots i = atoms.slots i)
    (hfirst : ∀ r, r = false ∨ atoms.centered = true →
      atoms.scaleProduct r * (Ideal.absNorm geometry.literalFirstExtraction.val : ℝ) ≤
        B ^ cap * atoms.base ^ (a.n₁ + a.n₂ + a.z))
    (error : ℝ) (hthreshold : B ^ (2 * cap) ≤ atoms.base ^ error) :
    (((v.literalLeftAtoms atoms).scale scalar).balancePlain balance).computedRawError
      geometry.skeleton.rawDegree error r = error := by
  let d := ((v.literalLeftAtoms atoms).scale scalar).balancePlain balance
  have hpresent : r = false ∨ atoms.centered = true :=
    d.active_rectangle C rows side χ ideal hideal firstSign L selection hne r hactive
  have hb := v.literalLeftAtoms_secondScale atoms B hB cap hcap hprime hslots
    geometry.literalFirstExtraction.val (a.n₁ + a.n₂ + a.z) r (hfirst r hpresent)
  rw [← hsecond] at hb
  exact d.computedRawError_eq_of_two_norms geometry B cap error r hb hthreshold

/-- The activity belongs to the actual allocated right table. Its
first window is supplied by `literalRightDirectAtoms_originalScale_of_domain`
or the corresponding actual main/pool theorem. -/
theorem literalRightAtoms_activeRawError
    (atoms : CanonicalLiteralRectangles.Atoms (K := K) v.literalRightParent.slotCount)
    (scalar : ℂ) (balance : Bool → ℝ)
    (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
    (ideal : AllocationColumn K v.literalRightBranch.keep.card → A.Exterior)
    (hideal : ∀ i ∈ childCartesianColumns (v.literalRightAtoms atoms).plain₁
      (v.literalRightAtoms atoms).plain₂ (v.literalRightAtoms atoms).slots,
      (ideal i).val = allocationColumnIdeal i)
    (firstSign : ℝ) (r : Bool) (L : Ideal (𝓞 K))
    (selection : primeSupport L → Finset (Fin (v.literalRightBranch.keep.card + 2)))
    (hne : (pairedAllocatedColumns L selection (v.literalRightAtoms atoms).plain₁
      (v.literalRightAtoms atoms).plain₂ (v.literalRightAtoms atoms).slots
      id id HeightOneSpectrum.asIdeal).Nonempty)
    (hactive : ¬ ∀ ξ,
      (((((v.literalRightAtoms atoms).scale scalar).balancePlain balance).factors
        rows side χ ideal hideal firstSign r).frame C L selection hne).source.energy
          (σ := σ) ξ = 0)
    (a : RealParameters) (step : ℝ)
    (geometry : OriginalNominalGeometry (K := K) a atoms.base step)
    (hsecond : geometry.ideals.second.val = v.1.val.2)
    (B : ℝ) (hB : 1 ≤ B) (cap : ℕ) (hcap : v.literalRightParent.slotCount ≤ cap)
    (hprime : atoms.PrimeNormWindow B)
    (hslots : ∀ i, v.literalRightParent.reindex.slots i = atoms.slots i)
    (hfirst : ∀ r, r = false ∨ atoms.centered = true →
      atoms.scaleProduct r * (Ideal.absNorm geometry.literalFirstExtraction.val : ℝ) ≤
        B ^ cap * atoms.base ^ (a.n₁ + a.n₂ + a.z))
    (error : ℝ) (hthreshold : B ^ (2 * cap) ≤ atoms.base ^ error) :
    (((v.literalRightAtoms atoms).scale scalar).balancePlain balance).computedRawError
      geometry.skeleton.rawDegree error r = error := by
  let d := ((v.literalRightAtoms atoms).scale scalar).balancePlain balance
  have hpresent : r = false ∨ atoms.centered = true :=
    d.active_rectangle C rows side χ ideal hideal firstSign L selection hne r hactive
  have hb := v.literalRightAtoms_secondScale atoms B hB cap hcap hprime hslots
    geometry.literalFirstExtraction.val (a.n₁ + a.n₂ + a.z) r (hfirst r hpresent)
  rw [← hsecond] at hb
  exact d.computedRawError_eq_of_two_norms geometry B cap error r hb hthreshold

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalLeftAtoms_activeRawError
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalRightAtoms_activeRawError
