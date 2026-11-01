import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPatternChildWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalPhaseCalibration

/-!
# The actual extracted sector is fixed before the second row partition

The original common block and negative orbit representative determine
the complete correlation and its extracted row before any row label is
chosen.  Its sixth-unit sector can therefore be included in the
original finite character coordinate.  Correlation-zero rows use the
fixed identity sector; their contribution is already exactly zero.

Equality of the resulting labels fixes both the original nonunit
pattern and the actual extracted sector.  The fixed values are selected
from the original physical row set, with defaults for an empty label,
before normalization.  No nonempty ordinary-source premise is used.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open CanonicalOriginalPhaseCalibration

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U}
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

namespace FirstCommonCharacterBlock

variable (b : FirstCommonCharacterBlock fullI fullJ DE)
variable (C : A.GeneralArithmeticContext σ η htrace)

/-- Only original common ideals and the original negative orbit
representative occur in this total function. -/
def originalRowCorrelation
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) : ℂ :=
  generatedIdealCorrelation (σ := σ) b.commonLeftIdeal b.commonRightIdeal
    (engineAllowedGenerator C b.commonLeftIdeal) (engineAllowedGenerator C b.commonRightIdeal)
    (engineAllowedGenerator_generates C _) (engineAllowedGenerator_generates C _) (-q.out.val)

def originalRowFactor
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) : A.R :=
  primePowerProductGenerator C b.primes
      (fun i => min (b.leftMultiplicity i) (b.rightMultiplicity i)) *
    nonunitFrequencyGenerator C b.primes b.leftMultiplicity b.rightMultiplicity (-q.out.val)

def originalRowNormFactor
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) : ℝ :=
  (Ideal.absNorm (gcd b.commonLeftIdeal.val b.commonRightIdeal.val) : ℝ) *
    A.exteriorNorm
      (nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-q.out.val))

/-- The same chosen arithmetic extraction as `actualRows.extractedRow`,
without a reference to the row carrier or to a future row label. -/
def originalRowExtraction
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    (hc : b.originalRowCorrelation C q ≠ 0) :
    ActualChildRow
      (ProbeOrbitNormSum.principalExterior A ⟨-q.out.val, neg_ne_zero.mpr q.out.property⟩)
      (-q.out.val) (b.originalRowFactor C q) (b.originalRowNormFactor C q) :=
  Classical.choice (exists_actual_extracted_child_row_of_generates C b.primes
    b.primes_injective b.leftMultiplicity b.rightMultiplicity
    (engineAllowedGenerator C b.commonLeftIdeal) (engineAllowedGenerator C b.commonRightIdeal)
    (engineAllowedGenerator_generates C _) (engineAllowedGenerator_generates C _)
    (ProbeOrbitNormSum.principalExterior A ⟨-q.out.val, neg_ne_zero.mpr q.out.property⟩)
    (-q.out.val)
    (ProbeOrbitNormSum.principalExterior_generates A
      ⟨-q.out.val, neg_ne_zero.mpr q.out.property⟩) hc)

def originalRowSector
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) :=
  if hc : b.originalRowCorrelation C q ≠ 0 then
    (b.originalRowExtraction C q hc).sector P
  else 1

/-- This augments the finite classification label, not the parent's
set of Hecke characters. It is chosen before the Poisson row partition. -/
def sectorCharacter
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    {Θ : Type*}
    (character : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    Θ × SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) :=
  (character q, b.originalRowSector C P q)

end FirstCommonCharacterBlock

local instance canonicalBlockRowSectorsFintype :
    Fintype (SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) := Fintype.ofFinite _

namespace OriginalBlockGaussRowClassifier

variable (C : A.GeneralArithmeticContext σ η htrace)
variable (b : FirstCommonCharacterBlock fullI fullJ DE)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))

/-- The true finite row code fixes the extracted sector as well as the
old character label. No conclusion about an arbitrary row subset is used. -/
theorem sector_eq_of_label_eq {Θ : Type*} [Fintype Θ] (dimension width : ℕ)
    (character : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
    (dyad : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
      Fin dimension → Fin (width + 1))
    (q q' : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    (he : label C b dimension width (b.sectorCharacter C P character) dyad q =
      label C b dimension width (b.sectorCharacter C P character) dyad q') :
    b.originalRowSector C P q = b.originalRowSector C P q' :=
  congrArg Prod.snd ((label_eq_iff C b dimension width
    (b.sectorCharacter C P character) dyad q q').mp he).2.1

end OriginalBlockGaussRowClassifier

section Charts

variable [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
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
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}

namespace SecondBlockProfileChart

variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius D)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))

def SectorLabelStable : Prop :=
  ∀ q q' : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ,
    chart.rowLabel q = chart.rowLabel q' →
      b.originalRowSector C P q = b.originalRowSector C P q'

/-- The actual source chooses precisely the same extracted row as
the pre-label arithmetic construction. Different membership proofs do
not alter that row, its generator, its ideal or its unit sector. -/
theorem actualRows_sector_eq_original
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (h : (chart.actualRows M X hX label).live) :
    ((chart.actualRows M X hX label).extractedRow C h).sector P =
      b.originalRowSector C P h.val := by
  have hc : b.originalRowCorrelation C h.val ≠ 0 := (Finset.mem_filter.mp h.property).2
  rw [FirstCommonCharacterBlock.originalRowSector, dif_pos hc]
  rfl

/-- The fixed sector is chosen from the original physical class.
Empty classes use one; no ordinary or normalized-family witness occurs. -/
def originalSector
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1)) :
    SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) :=
  if hrows : (chart.actualRows M X hX label).rows.Nonempty then
    b.originalRowSector C P hrows.choose
  else 1

theorem actualRows_originalSector
    (hclass : chart.SectorLabelStable P)
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (h : (chart.actualRows M X hX label).live) :
    ((chart.actualRows M X hX label).extractedRow C h).sector P =
      chart.originalSector P M X hX label := by
  have hh := (Finset.mem_filter.mp h.property).1
  have hrows : (chart.actualRows M X hX label).rows.Nonempty := ⟨h.val, hh⟩
  rw [chart.actualRows_sector_eq_original P M X hX label h,
    originalSector, dif_pos hrows]
  exact hclass h.val hrows.choose
    ((chart.actualRows_original_rowLabel M X hX label ⟨h.val, hh⟩).trans
      (chart.actualRows_original_rowLabel M X hX label
        ⟨hrows.choose, hrows.choose_spec⟩).symm)

/-- This is the original live row with both arithmetic identities
proved internally. It is the exact input to the literal phase and
allocated-profile dictionaries, including an empty ordinary source. -/
def originalPatternSector
    (hpattern : chart.NonunitLabelStable) (hsector : chart.SectorLabelStable P)
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (h : (chart.actualRows M X hX label).live) :
    PatternSector P (chart.actualRows M X hX label) C
      (chart.originalNonunitPattern M X hX label) (chart.originalSector P M X hX label) :=
  ⟨chart.originalNonunitClass hpattern M X hX label h,
    chart.actualRows_originalSector P hsector M X hX label h⟩

@[simp] theorem originalPatternSector_val_val
    (hpattern : chart.NonunitLabelStable) (hsector : chart.SectorLabelStable P)
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (h : (chart.actualRows M X hX label).live) :
    (chart.originalPatternSector P hpattern hsector M X hX label h).val.val = h := rfl

end SecondBlockProfileChart
end Charts

section CanonicalStage

variable [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
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
variable {C : A.GeneralArithmeticContext σ η htrace}

namespace ActualGaussStage

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
variable {ι : Type*} (G : ActualGaussSource C ι)
variable (retainedScale Z g : ℝ) (hscale : 0 < retainedScale) (hZ : 0 < Z)
variable (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
variable (hnorm : ∀ h ∈ G.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable {Θ : Type*} [Fintype Θ]
variable (dimension width : ℕ)
variable (character : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

/-- The existing canonical source is partitioned by a computed finite
sector together with its original labels.  G, its full column masks,
the two continuous kernels and the physical cutoff are not modified. -/
def canonicalUnmaskedSectorRowBallByBlock :
    ActualGaussStage (E := ℝ) hΓ μv hDiff G
      (HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft.rowBallFiniteFamily K A.Sf 1) :=
  canonicalUnmaskedRowBallByBlock (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
    dimension width
    (fun DE => (canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal
      DE.val DE.property).sectorCharacter C P (character DE)) dyad

theorem canonicalUnmaskedSectorRowBallByBlock_sectorLabelStable
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : (∅ : Finset (HeightOneSpectrum A.R)).powerset) :
    ((canonicalUnmaskedSectorRowBallByBlock (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      P δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad).charts DE D).SectorLabelStable P := by
  intro q q' he
  exact OriginalBlockGaussRowClassifier.sector_eq_of_label_eq C
    (canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property)
    P dimension width (character DE) (dyad DE) q q' he

theorem canonicalUnmaskedSectorRowBallByBlock_nonunitLabelStable
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : (∅ : Finset (HeightOneSpectrum A.R)).powerset) :
    ((canonicalUnmaskedSectorRowBallByBlock (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      P δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad).charts DE D).NonunitLabelStable :=
  canonicalUnmaskedRowBallByBlock_nonunitLabelStable
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
    dimension width
    (fun DE => (canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal
      DE.val DE.property).sectorCharacter C P (character DE)) dyad DE D

/-- The extra finite factor is fixed by the original field and S.
It is independent of the row, Fourier parameters and moving scale. -/
theorem sectorCharacter_card (Θ : Type*) [Fintype Θ] :
    Fintype.card (Θ × SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) =
      Fintype.card Θ * Fintype.card
        (SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) :=
  Fintype.card_prod _ _

end ActualGaussStage
end CanonicalStage

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.originalRowExtraction
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.actualRows_sector_eq_original
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.originalPatternSector
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock_sectorLabelStable
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock_nonunitLabelStable
