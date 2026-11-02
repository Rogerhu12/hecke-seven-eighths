import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralProduction

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# One literal input descriptor for every physical source tag

The descriptor records an original occurrence branch and its existing
source atlas.  Direct, main and valuation sources differ only in these
stored coordinates and the three generated phase elements.  The two
transforms, scalar extraction, balancing and profile normalization are
computed by the same functions below.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
variable {k : ℕ}

structure LiteralInput (d : CanonicalLiteralRectangles.Atoms (K := K) k)
    (atlas : SourceCartesianAtlas columns ideal) where
  firstSupport : Finset (Ideal (𝓞 K))
  firstSupport_prime : ∀ p ∈ firstSupport, Prime p
  firstBranch : SupportCartesianBranch d.plain₁ d.plain₂ d.slots firstSupport
  count : firstBranch.keep.card = atlas.slotCount
  power : A.Exterior
  phases : CanonicalLiteralPhaseCalibration.FixedPhases A

namespace LiteralInput

variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable {atlas : SourceCartesianAtlas columns ideal}
variable (input : LiteralInput d atlas)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (δ₁ δ₂ : ℝ)

def deletion : HeckeGeneral.Analysis.NonzeroIdeal K :=
  literalDeletionIdeal input.firstSupport input.firstSupport_prime

def scalar : ℂ :=
  d.commonScalar input.firstBranch *
    (((A.exteriorNorm input.power ^ δ₁ : ℝ) : ℂ) *
      actualIdealResidue (A := A) (σ := σ) input.power.val input.phases.firstElement)

def balance : Bool → ℝ :=
  CanonicalLiteralBalancedSchwartz.balance d input.firstBranch δ₁ δ₂

def transformed : CanonicalLiteralRectangles.Atoms (K := K) input.firstBranch.keep.card :=
  d.secondInput (σ := σ) input.firstBranch P R input.power
    input.phases.firstIdeal input.phases.poolIdeal input.phases.unitIdeal
    input.phases.firstElement input.phases.poolElement input.phases.unitElement
    input.phases.first_generates input.phases.pool_generates input.phases.unit_generates δ₁ δ₂

def atoms : CanonicalLiteralRectangles.Atoms (K := K) atlas.slotCount :=
  ((input.transformed (σ := σ) P R δ₁ δ₂).onAtlas atlas input.count).deleteMask input.deletion

def strippedAtoms : CanonicalLiteralRectangles.Atoms (K := K) atlas.slotCount :=
  ((input.atoms (σ := σ) P R δ₁ δ₂).scale (input.scalar (σ := σ) δ₁)⁻¹).balancePlain
    (input.balance δ₁ δ₂)

variable (W : d.ProfileData)

def transformedProfiles : (input.transformed (σ := σ) P R δ₁ δ₂).ProfileData :=
  W.secondInput (σ := σ) input.firstBranch P R input.power
    input.phases.firstIdeal input.phases.poolIdeal input.phases.unitIdeal
    input.phases.firstElement input.phases.poolElement input.phases.unitElement
    input.phases.first_generates input.phases.pool_generates input.phases.unit_generates δ₁ δ₂

def profiles : (input.atoms (σ := σ) P R δ₁ δ₂).ProfileData :=
  ((input.transformedProfiles (σ := σ) P R δ₁ δ₂ W).onAtlas atlas input.count)
    .deleteMask input.deletion

def strippedProfiles : (input.strippedAtoms (σ := σ) P R δ₁ δ₂).ProfileData :=
  ((input.profiles (σ := σ) P R δ₁ δ₂ W).scale (input.scalar (σ := σ) δ₁)⁻¹)
    .balancePlain (input.balance δ₁ δ₂)

/-- The occurrence map is the first keep map followed by the original
parent map.  Its data do not depend on a Fourier variable or activity. -/
def slots {ω ψ : HeckeCharacter K} (parent : MomentData K ω ψ)
    (original : OriginalSlotDictionary parent d.length) :
    OriginalSlotDictionary parent (input.atoms (σ := σ) P R δ₁ δ₂).length where
  index := ⟨fun j => original.index
    (SlotRestriction.index input.firstBranch.keep (Fin.cast input.count.symm j)), by sorry⟩
  length_eq := by sorry

variable {window : Set ℝ} (E : W.SchwartzModel window)

/-- The radius data come from the original Schwartz representatives.
Only individual seminorm inequalities appear as proof arguments. -/
def computedProfiles (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (orders : Finset (ℕ × ℕ)) (B : ℝ) (hB : 0 ≤ B) (hδhi : δ₁ + δ₂ ≤ 1 / 2)
    (hleft : ∀ r, (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders orders)).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.left r) ≤ B)
    (hright : ∀ r, (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders orders)).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) ≤ B)
    (hslot : ∀ j, (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders orders)).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.slot j) ≤ B)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ Set.Ioo (1 : ℝ) 2) :
    CanonicalLiteralFullKappaInput.ComputedProfiles
      (input.strippedProfiles (σ := σ) P R δ₁ δ₂ W) window orders B :=
  let initial := CanonicalLiteralFullKappaInput.scalarFreeBalanced (σ := σ) E
    input.firstBranch P R input.power
    input.phases.firstIdeal input.phases.poolIdeal input.phases.unitIdeal
    input.phases.firstElement input.phases.poolElement input.phases.unitElement
    input.phases.first_generates input.phases.pool_generates input.phases.unit_generates
    δ₁ δ₂ hcompact hpositive orders B hB hδhi hleft hright hslot hprime
  let transported := CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenScaleBalance
    (input.scalar (σ := σ) δ₁)⁻¹ (input.balance δ₁ δ₂) initial atlas input.count
  CanonicalLiteralFullKappaInput.ComputedProfiles.deleteMaskThenScaleBalance
    (input.scalar (σ := σ) δ₁)⁻¹ (input.balance δ₁ δ₂) transported input.deletion

end LiteralInput
end HeckeSkeleton.Moments.EngineStepV2
