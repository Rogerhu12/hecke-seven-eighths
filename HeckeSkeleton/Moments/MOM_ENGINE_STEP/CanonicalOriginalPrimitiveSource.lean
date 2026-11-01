import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalFirstTerminals
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveFirstSource

/-!
# The fixed-box factory is the same literal primitive first source

The literal engine internally puts the full old support into `q` while
preserving the original total width.  The fixed-box estimates are applied directly at
these internal parameters to its already chosen original-recipe source.
This bridge does not choose a new chart, physical cutoff, prime pool or
Fourier kernel.  Its original windows therefore apply to that same
source, and its parent energy remains the original one.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalOriginalParentFactory

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]
variable {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {Index : Type*} {data : Index → MomentData K ω ψ}
variable (box : FixedBox) (Q : CompleteMovingRowRecipe A P R data)
variable (W : NormProfileRecipe data) (index : Index)
variable (C : A.GeneralArithmeticContext σ η hS)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (hZ : 1 < Z)
variable (hfull : Q.FullJointBudget Z (a.m + a.q)) (centered : Bool)
variable (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)

local notation "internal" => Q.fullSupportParameters a Z

/-- The exact primitive source of the literal dispatcher, with only
the original fixed cutoff and unused ordinary scales filled in. -/
def primitiveSource :=
  Q.literalPrimitiveFirstSource μv ν C hroot hemb W index a Z t
    (comparisonScale centered Z a.n₁ Y₁) (comparisonScale centered Z a.n₂ Y₂)
    hZ hfull
    centered (box.cutoff Z) (box.cutoff_ge_one hZ.le) δ hδ hδhalf

local notation "source" => primitiveSource μv ν box Q W index C hroot hemb
  a Z t Y₁ Y₂ hZ hfull centered δ hδ hδhalf

/-- This is the original recipe's own primitive source, with its
internal full-support parameters. No exterior-normalized replacement
recipe is used by this bridge. -/
theorem primitiveSource_eq_originalSource :
    source = Q.canonicalFullSupportDirectFirstSource μv ν C hroot hemb W index
      internal Z t
      (comparisonScale centered Z a.n₁ Y₁) (comparisonScale centered Z a.n₂ Y₂)
      (zero_lt_one.trans hZ)
      (by simpa only [Q.fullSupportParameters_width] using hfull)
      centered (box.cutoff Z) (box.cutoff_ge_one hZ.le) δ hδ hδhalf := rfl

@[simp] theorem primitiveSource_fiber : source.fiber = 1 := rfl

@[simp] theorem primitiveSource_mask : source.mask = ∅ := rfl

/-- Only the distribution between `m` and `q` changes internally.
Both the comparison scales and parent normalization preserve the
original actual energy. -/
theorem primitiveSource_parent :
    pairedStageEnergy centered (data index) internal Z t
        (comparisonScale centered Z a.n₁ Y₁) (comparisonScale centered Z a.n₂ Y₂) /
          Z ^ (internal.m + internal.q) =
      pairedStageEnergy centered (data index) a Z t Y₁ Y₂ / Z ^ (a.m + a.q) := by
  rw [Q.fullSupportParameters_width]
  change pairedStageEnergy centered (data index)
      (withSupportLength a (Q.fullSupportLength Z)) Z t
      (comparisonScale centered Z a.n₁ Y₁) (comparisonScale centered Z a.n₂ Y₂) /
      Z ^ (a.m + a.q) = _
  rw [pairedStageEnergy_withSupportLength, same_parent_energy]

variable {floor padding : ℝ}
variable (domain : PairedEngineDomain centered (data index) a Z Y₁ Y₂ floor padding)
variable (hwidth : a.m + a.q ≤ box.widthMax) (hpadding : padding ≤ box.paddingMax)
variable (hcap : (data index).geometry.slotCount ≤ box.cap) (hlarge : box.threshold ≤ Z)
variable (orders sTail sZero : Finset (ℕ × ℕ)) (amplitude : ℝ) (hamplitude : 1 ≤ amplitude)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window
  (OriginalProfileAtomBounds.profileOrders orders) (data index) amplitude)
variable (hrows : ∀ u ∈ pairedRows (data index) a Z, u ∈ rowDomain)
variable (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic box.annulus)

/-- The original first windows, including the sharp zero-product
window, are supplied for the dispatcher's exact primitive source. -/
def primitiveFirstWindows :
    FirstDualOriginalWindows
      (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) C
      source.columns source.ideal source.block source.profiles source.radius source.mask
      sTail sZero (2 * (box.cap + 2)) Z (box.cutoff Z) box.columnBound box.tailDegree
      box.tailSaving box.decay := by
  have domain' := domain.withSupportLength (Q.fullSupportLength Z)
  have hfull' : Q.FullJointBudget Z (internal.m + internal.q) := by
    simpa only [Q.fullSupportParameters_width] using hfull
  have hwidth' : internal.m + internal.q ≤ box.widthMax := by
    simpa only [Q.fullSupportParameters_width] using hwidth
  have hrows' : ∀ u ∈ pairedRows (data index) internal Z, u ∈ rowDomain := by
    simpa only [CompleteMovingRowRecipe.fullSupportParameters, pairedRows_withSupportLength]
      using hrows
  obtain ⟨hY₁, hY₂, hn₁, hn₂, hY₁le, hY₂le, hcolumn, hwidthBound⟩ :=
    original_scale_windows box domain' hwidth' hpadding
  exact Q.canonicalFullSupportFirstWindows W index internal Z t
    (comparisonScale centered Z a.n₁ Y₁) (comparisonScale centered Z a.n₂ Y₂) C
    box.cap orders amplitude box.annulus box.loss box.plainBound box.plainBound
    box.columnBound box.tailSaving box.decay hamplitude box.annulus_ge_one box.loss_pos.le
    box.columnBound_nonneg hcap (box.annulus_bound hlarge) centered
    (originalComparisonDomain domain') hY₁ hY₂ hn₁ hn₂ hY₁le hY₂le profiles hrows' ht hwindow
    hcolumn hwidthBound sTail sZero

end HeckeSkeleton.Moments.EngineStep.CanonicalOriginalParentFactory

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalParentFactory.primitiveSource_eq_originalSource
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalParentFactory.primitiveSource_parent
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalParentFactory.primitiveFirstWindows
