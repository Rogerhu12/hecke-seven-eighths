import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalBlockRowSectors
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSupportedRowMass

/-!
# The original sector on the actual ordinary arithmetic rows

Moving the two common atoms into the row weight changes no arithmetic
row.  Deleting correlation-zero rows and then taking the ordinary rows
changes only their membership proofs.  The pattern and sector already
fixed by the original physical row label therefore give the literal
`PatternSector` dictionary on this same final row carrier.

The constructors below select no row and no child.  In particular they
do not need an ordinary-source witness or a normalized family in order
to choose the arithmetic data used by that family.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CanonicalOriginalPhaseCalibration

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
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
variable {C : A.GeneralArithmeticContext σ η htrace}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}

namespace SecondBlockProfileChart

variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius D)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (hpattern : chart.NonunitLabelStable) (hsector : chart.SectorLabelStable P)
variable (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
variable (label : Fin (chart.rowLabelCount + 1))

/-- Two successive restrictions retain the exact original arithmetic
extraction, even after its common scalar has been moved into the weight. -/
def originalReweightedPatternSector
    (weight : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → ℂ)
    (keep₁ keep₂ : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Prop)
    (h : ((({ chart.actualRows M X hX label with weight := weight }).restrictRows keep₁)
      .restrictRows keep₂).live) :
    PatternSector P
      ((({ chart.actualRows M X hX label with weight := weight }).restrictRows keep₁)
        .restrictRows keep₂) C
      (chart.originalNonunitPattern M X hX label) (chart.originalSector P M X hX label) := by
  let R₁ := { chart.actualRows M X hX label with weight := weight }
  let R₂ := R₁.restrictRows keep₁
  let h₁ : R₂.live := R₂.liveInclusion keep₂ h
  let h₀ : (chart.actualRows M X hX label).live := R₁.liveInclusion keep₁ h₁
  let hp := chart.originalPatternSector P hpattern hsector M X hX label h₀
  exact ⟨⟨h, hp.val.property⟩, hp.property⟩

@[simp] theorem originalReweightedPatternSector_val_val
    (weight : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → ℂ)
    (keep₁ keep₂ : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Prop)
    (h : ((({ chart.actualRows M X hX label with weight := weight }).restrictRows keep₁)
      .restrictRows keep₂).live) :
    (chart.originalReweightedPatternSector P hpattern hsector M X hX label
      weight keep₁ keep₂ h).val.val = h := rfl

variable {kLeft kRight : ℕ}
variable (leftAtoms : FrozenSourceAtoms A σ
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
  (chart.actualRows M X hX label).rows kLeft)
variable (rightAtoms : FrozenSourceAtoms A σ
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
  (chart.actualRows M X hX label).rows kRight)
variable (exceptional : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Prop)

/-- This is the carrier used by the actual common-atom mass dictionary
and the ordinary rectangle frames.  All four row updates are literal. -/
def originalSupportedPatternSector
    (h : ((((chart.actualRows M X hX label).withCommonAtoms leftAtoms rightAtoms)
        .restrictRows (fun q => (chart.actualRows M X hX label).correlation q ≠ 0))
      .restrictRows (fun q => ¬exceptional q)).live) :
    PatternSector P
      ((((chart.actualRows M X hX label).withCommonAtoms leftAtoms rightAtoms)
          .restrictRows (fun q => (chart.actualRows M X hX label).correlation q ≠ 0))
        .restrictRows (fun q => ¬exceptional q)) C
      (chart.originalNonunitPattern M X hX label) (chart.originalSector P M X hX label) :=
  chart.originalReweightedPatternSector P hpattern hsector M X hX label
    (fun q => (chart.actualRows M X hX label).weight q *
      leftAtoms.value q * star (rightAtoms.value q))
    (fun q => (chart.actualRows M X hX label).correlation q ≠ 0)
    (fun q => ¬exceptional q) h

@[simp] theorem originalSupportedPatternSector_val_val
    (h : ((((chart.actualRows M X hX label).withCommonAtoms leftAtoms rightAtoms)
        .restrictRows (fun q => (chart.actualRows M X hX label).correlation q ≠ 0))
      .restrictRows (fun q => ¬exceptional q)).live) :
    (chart.originalSupportedPatternSector P hpattern hsector M X hX label
      leftAtoms rightAtoms exceptional h).val.val = h := rfl

end SecondBlockProfileChart
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.originalReweightedPatternSector
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.originalSupportedPatternSector
