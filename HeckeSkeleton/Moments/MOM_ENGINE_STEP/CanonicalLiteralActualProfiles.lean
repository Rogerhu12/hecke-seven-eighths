import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAllocatedSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCoveredLeaf

/-!
# Original profile and support data on the six actual source tables

The only analytic input is the original profile window at an original
paired row.  Each constructor below follows the definition of its
actual direct, main or pool atom table: original tests, first common
extraction, the two literal transforms, the original atlas transport,
and the complete first deletion.  The output bundles the existing
`ProfileData` and `SupportData`; it is not another input to the engine.

The same transport then supplies the second extraction on an actual
covered leaf.  No whole coefficient, final support property, or new
ordinary-row reference is assumed.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open HeckePort.IdealMobiusDivisorSum MeasureTheory

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralActualProfiles

/-- A return value containing only the two already defined certificates
for the same atom table. Both fields are constructed from original data. -/
structure ProfileSupport {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)
    (excluded : Finset (Ideal (𝓞 K))) where
  profiles : d.ProfileData
  support : d.SupportData excluded

namespace ProfileSupport

variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable {excluded : Finset (Ideal (𝓞 K))}

def extract (E : ProfileSupport d excluded) {S : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots S)
    (hS : ∀ p ∈ S, Prime p) : ProfileSupport (d.extract b) (excluded ∪ S) where
  profiles := E.profiles.extract b
  support := E.support.extract b hS

def deleteMask (E : ProfileSupport d excluded)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ProfileSupport (d.deleteMask M) excluded where
  profiles := E.profiles.deleteMask M
  support := E.support.deleteMask M

def secondInput (E : ProfileSupport d excluded)
    {S : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots S)
    {A : SArithmeticData K} {σ : K →+* ℂ}
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
    (hS : ∀ p ∈ S, Prime p)
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ) :
    ProfileSupport
      (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂) (excluded ∪ S) where
  profiles := E.profiles.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
    firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂
  support := E.support.secondInput (σ := σ) b P R hS power firstFixed poolFixed unitFixed
    firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂

def onAtlas (E : ProfileSupport d excluded) {A : SArithmeticData K} {ι : Type*}
    {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (index : AllocationColumn K k → ι)
    (e : T.literalDictionary = ⟨k, (d.plain₁, d.plain₂), d.slots, index⟩) :
    ProfileSupport (d.onAtlas T (congrArg Sigma.fst e).symm) excluded where
  profiles := E.profiles.onAtlas T (congrArg Sigma.fst e).symm
  support := E.support.onAtlas T index e

/-- On an already chosen equal-size atlas, only the actual individual
support identities are needed. No whole-column identity is involved. -/
def onAtlasOfFields (E : ProfileSupport d excluded) {A : SArithmeticData K} {ι : Type*}
    {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (count : k = T.slotCount)
    (hleft : T.reindex.plain₁ = d.plain₁) (hright : T.reindex.plain₂ = d.plain₂)
    (hslot : ∀ i, T.reindex.slots (Fin.cast count i) = d.slots i) :
    ProfileSupport (d.onAtlas T count) excluded := by
  cases count
  refine ⟨E.profiles.onAtlas T rfl, ?_⟩
  refine
    { left_avoids := ?_
      right_avoids := ?_
      slot_avoids := ?_
      left_mem := ?_
      right_mem := ?_
      slot_mem := ?_ }
  · intro I hI
    exact E.support.left_avoids I (hleft ▸ hI)
  · intro I hI
    exact E.support.right_avoids I (hright ▸ hI)
  · intro j p hp
    exact E.support.slot_avoids j p (hslot j ▸ hp)
  · intro r I hI havoid
    change I.val ∈ T.reindex.plain₁
    rw [hleft]
    exact E.support.left_mem r I hI havoid
  · intro r I hI havoid
    change I.val ∈ T.reindex.plain₂
    rw [hright]
    exact E.support.right_mem r I hI havoid
  · intro j p hp havoid
    change p ∈ T.reindex.slots j
    rw [hslot j]
    exact E.support.slot_mem j p hp havoid

end ProfileSupport
end CanonicalLiteralActualProfiles

namespace CanonicalLiteralRectangles.Atoms

/-- Retargeting the actual atlas only casts the original slot index;
all plain characters, twists, masks and finite ray factors are unchanged. -/
theorem onAtlas_characters {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)
    {A : SArithmeticData K} {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (count : k = T.slotCount) :
    (d.onAtlas T count).characters = d.characters.selectSlots (Fin.cast count.symm) := by
  cases count
  rfl

end CanonicalLiteralRectangles.Atoms

namespace CanonicalLiteralPhaseCalibration

/-- Any actual atlas cast or later retained-slot map composes with the
original character index. The complete three phases and deletion stay
the literal original source recipe. -/
theorem sourceCharacters_selectSlots
    {A : SArithmeticData K}
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
    (F : FixedPhases A) {ω ψ : HeckeCharacter K} (parent : MomentData K ω ψ)
    (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
    (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) {k n : ℕ}
    (index : Fin k → Fin parent.geometry.slotCount) (select : Fin n → Fin k) :
    (sourceCharacters P R F parent oldMoving correction remaining extra index).selectSlots select =
      sourceCharacters P R F parent oldMoving correction remaining extra
        (fun i => index (select i)) := rfl

end CanonicalLiteralPhaseCalibration

namespace CompleteMovingRowRecipe

open CanonicalLiteralActualProfiles

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*}
variable {data : X → MomentData K ω ψ}

/-- The reference is an original paired row. In particular an empty
later correlation or ordinary-row carrier requires no chosen element. -/
def literalOriginalProfileSupport (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
    (W : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
    (href : reference ∈ pairedRows (data ξ) a Z)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)} {bound : ℝ}
    (original : RawProfileWindow rowDomain heightDomain window seminorms (data ξ) bound)
    (hreference : reference ∈ rowDomain) (ht : t ∈ heightDomain)
    (hwindow : window ⊆ Set.Ioi 0) :
    ProfileSupport (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂)
      (primeSupport A.cS) where
  profiles := Q.literalOriginalProfileDataOfWindow ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    reference (((data ξ).rows_spec _ reference).mp (Finset.mem_filter.mp href).1).1
    original hreference ht hwindow
  support := Q.literalOriginalSupportData ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ reference href

end CompleteMovingRowRecipe

section CoveredLeaves

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

local instance canonicalLiteralActualProfilesCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace ActualGaussStage.CoveredClassKey

open CanonicalLiteralActualProfiles

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualGaussStage (E := ℝ) hΓ μv hDiff G finiteTest}
variable {LC RC : SourceCartesianCover G.columns G.ideal}
variable (v : s.CoveredClassKey LC RC)
variable {excluded : Finset (Ideal (𝓞 K))}

/-- The second extraction and its original left residual atlas carry
the already constructed certificates. The three equalities are the
original individual support identities, all reflexive for the computed
direct/main/pool tables. -/
def literalLeftProfileSupport
    (leftAtoms : CanonicalLiteralRectangles.Atoms (K := K) (LC.branch v.2.2.1).slotCount)
    (E : ProfileSupport leftAtoms excluded)
    (hleft : v.literalLeftParent.reindex.plain₁ = leftAtoms.plain₁)
    (hright : v.literalLeftParent.reindex.plain₂ = leftAtoms.plain₂)
    (hslot : ∀ i, v.literalLeftParent.reindex.slots i = leftAtoms.slots i) :
    ProfileSupport (v.literalLeftAtoms leftAtoms) (excluded ∪ primeSupport v.1.val.1) := by
  let original := E.onAtlasOfFields v.literalLeftParent rfl hleft hright hslot
  let extracted := original.extract v.literalLeftBranch (fun _ hp => support_prime hp)
  refine extracted.onAtlasOfFields v.literalLeftResidualAtlas rfl ?_ ?_ ?_
  · change v.leftReindex.plain₁ = _
    rw [SourceCartesianAtlas.residualReindex_plain₁]
  · change v.leftReindex.plain₂ = _
    rw [SourceCartesianAtlas.residualReindex_plain₂]
  · intro i
    change v.leftReindex.slots i = _
    rw [SourceCartesianAtlas.residualReindex_slots]

/-- The right table uses the same second prime support and its own
actual extracted ideal and occurrence indices. -/
def literalRightProfileSupport
    (rightAtoms : CanonicalLiteralRectangles.Atoms (K := K)
      (RC.branch v.2.2.2.1).slotCount)
    (E : ProfileSupport rightAtoms excluded)
    (hleft : v.literalRightParent.reindex.plain₁ = rightAtoms.plain₁)
    (hright : v.literalRightParent.reindex.plain₂ = rightAtoms.plain₂)
    (hslot : ∀ i, v.literalRightParent.reindex.slots i = rightAtoms.slots i) :
    ProfileSupport (v.literalRightAtoms rightAtoms) (excluded ∪ primeSupport v.1.val.1) := by
  let original := E.onAtlasOfFields v.literalRightParent rfl hleft hright hslot
  let extracted := original.extract v.literalRightBranch (fun _ hp => support_prime hp)
  refine extracted.onAtlasOfFields v.literalRightResidualAtlas rfl ?_ ?_ ?_
  · change v.rightReindex.plain₁ = _
    rw [SourceCartesianAtlas.residualReindex_plain₁]
  · change v.rightReindex.plain₂ = _
    rw [SourceCartesianAtlas.residualReindex_plain₂]
  · intro i
    change v.rightReindex.slots i = _
    rw [SourceCartesianAtlas.residualReindex_slots]

end ActualGaussStage.CoveredClassKey
end CoveredLeaves

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralActualProfiles.ProfileSupport.onAtlasOfFields
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.onAtlas_characters
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPhaseCalibration.sourceCharacters_selectSlots
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalProfileSupport
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalLeftProfileSupport
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalRightProfileSupport
