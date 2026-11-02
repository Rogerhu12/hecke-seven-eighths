import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCoveredLeaf
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralScaleProduct

set_option linter.unusedSectionVars false

/-!
# Scale products on the same second common-support leaf

The preceding actual direct/main/pool theorems prove the first bound
from the original individual prime windows. This module composes that
proved bound with the second stored occurrence extraction. Both full
frozen ideals and both fixed annulus costs remain visible.

The final source identity concerns the original allocation's
`beforeLength`. Constant extraction and reciprocal plain balancing
preserve it, so the same inequality fills the capacity input for the
same already constructed child frame.
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

local instance canonicalLiteralCoveredScaleProductCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace ActualGaussStage.CoveredClassKey

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualGaussStage (E := ℝ) hΓ μv hDiff G finiteTest}
variable {LC RC : SourceCartesianCover G.columns G.ideal}
variable (v : s.CoveredClassKey LC RC)

/-- Composition with the actual second extraction. `hfirst` is the
output of the original-table scale theorem, not a new source premise. -/
theorem literalLeftAtoms_secondScale
    (atoms : CanonicalLiteralRectangles.Atoms (K := K) v.literalLeftParent.slotCount)
    (B : ℝ) (hB : 1 ≤ B) (cap : ℕ) (hcap : v.literalLeftParent.slotCount ≤ cap)
    (hprime : atoms.PrimeNormWindow B)
    (hslots : ∀ i, v.literalLeftParent.reindex.slots i = atoms.slots i)
    (first : Ideal (𝓞 K)) (total : ℝ) (rectangle : Bool)
    (hfirst : atoms.scaleProduct rectangle * (Ideal.absNorm first : ℝ) ≤
      B ^ cap * atoms.base ^ total) :
    (v.literalLeftAtoms atoms).scaleProduct rectangle *
        ((Ideal.absNorm first : ℝ) * (Ideal.absNorm v.1.val.1 : ℝ)) ≤
      B ^ (2 * cap) * atoms.base ^ total := by
  sorry

/-- Composition with the actual second extraction. `hfirst` is the
output of the original-table scale theorem, not a new source premise. -/
theorem literalRightAtoms_secondScale
    (atoms : CanonicalLiteralRectangles.Atoms (K := K) v.literalRightParent.slotCount)
    (B : ℝ) (hB : 1 ≤ B) (cap : ℕ) (hcap : v.literalRightParent.slotCount ≤ cap)
    (hprime : atoms.PrimeNormWindow B)
    (hslots : ∀ i, v.literalRightParent.reindex.slots i = atoms.slots i)
    (first : Ideal (𝓞 K)) (total : ℝ) (rectangle : Bool)
    (hfirst : atoms.scaleProduct rectangle * (Ideal.absNorm first : ℝ) ≤
      B ^ cap * atoms.base ^ total) :
    (v.literalRightAtoms atoms).scaleProduct rectangle *
        ((Ideal.absNorm first : ℝ) * (Ideal.absNorm v.1.val.2 : ℝ)) ≤
      B ^ (2 * cap) * atoms.base ^ total := by
  sorry

end ActualGaussStage.CoveredClassKey

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)

/-- Exact division by the two genuine frozen norms. The input is the
already proved product bound and its fixed annulus threshold. -/
theorem scaleProduct_le_power_of_two_norms
    (first second : Ideal (𝓞 K)) (hfirst : first ≠ 0) (hsecond : second ≠ 0)
    (B : ℝ) (cap : ℕ) (total error : ℝ) (rectangle : Bool)
    (hbound : d.scaleProduct rectangle *
      ((Ideal.absNorm first : ℝ) * (Ideal.absNorm second : ℝ)) ≤
        B ^ (2 * cap) * d.base ^ total)
    (herror : B ^ (2 * cap) ≤ d.base ^ error) :
    d.scaleProduct rectangle ≤ d.base ^
      (total - idealLogLength d.base first - idealLogLength d.base second + error) := by
  sorry

/-- This is the literal pre-allocation length product of the actual
frame. The right source's negative phases do not change any scale. -/
theorem factors_source_scaleProduct
    {H J : Type*} [Fintype J] [DecidableEq J]
    (R : ActualSecondCorrelationRows A σ H J)
    (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
    (ideal : AllocationColumn K k → A.Exterior)
    (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
      (ideal i).val = allocationColumnIdeal i)
    (firstSign : ℝ) (rectangle : Bool) (L : Ideal (𝓞 K))
    (selection : primeSupport L → Finset (Fin (k + 2)))
    (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
      id id HeightOneSpectrum.asIdeal).Nonempty) :
    let f := (d.factors R side χ ideal hideal firstSign rectangle).frame C L selection hne
    f.source.scale₁ * f.source.scale₂ * f.source.base ^ f.source.beforeLength =
      d.scaleProduct rectangle := by
  sorry

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalLeftAtoms_secondScale
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalRightAtoms_secondScale
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.scaleProduct_le_power_of_two_norms
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.factors_source_scaleProduct
