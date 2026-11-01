import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalUnmaskedBlockStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFullDeletionWindows

/-!
# The original block labels already fix the moving frequency class

The physical rows of `actualRows` are filtered by the chart's existing
row label. For a chart with the actual divided-frequency classifier,
all live rows of one label therefore have the same nonunit pattern.
The resulting equivalence with that pattern's `NonunitClass` is the
identity on the original live rows; it creates no further row partition
and leaves the original extraction and its sector untouched.

Both canonical block-stage constructors prove this classifier property
from their original finite row code. The full-deletion child window
then accepts an anchor and any original live row directly, with no
pattern-membership certificate or completed support bound from the
caller. The child budget is fixed by the anchor of that existing label.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.Moments CommonSupportMass

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
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {C : A.GeneralArithmeticContext σ η htrace}

section Charts

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

/-- This is only a property of the original finite classifier. The
canonical constructors below prove it from their divided-frequency code. -/
def NonunitLabelStable : Prop :=
  ∀ q q' : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ,
    chart.rowLabel q = chart.rowLabel q' → ∀ i : Fin b.primeCount,
      nonunitFrequencySaving C (b.primes i) (b.leftMultiplicity i) (b.rightMultiplicity i)
          (-q.out.val) ↔
        nonunitFrequencySaving C (b.primes i) (b.leftMultiplicity i) (b.rightMultiplicity i)
          (-q'.out.val)

/-- Both filters are the original ones: the physical row label and
the nonzero full correlation. No new carrier is introduced. -/
theorem actualRows_live_rowLabel
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (h : (chart.actualRows M X hX label).live) : chart.rowLabel h.val = label := by
  have hrow : h.val ∈ (chart.actualRows M X hX label).rows :=
    (Finset.mem_filter.mp h.property).1
  exact (Finset.mem_filter.mp hrow).2

theorem actualRows_live_nonunitPattern_eq (hclass : chart.NonunitLabelStable)
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (anchor h : (chart.actualRows M X hX label).live) :
    actualNonunitPattern C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val) =
      actualNonunitPattern C b.primes b.leftMultiplicity b.rightMultiplicity (-anchor.val.out.val) := by
  funext i
  apply decide_eq_decide.mpr
  exact hclass h.val anchor.val
    ((chart.actualRows_live_rowLabel M X hX label h).trans
      (chart.actualRows_live_rowLabel M X hX label anchor).symm) i

/-- Every live row is in the anchor's actual pattern class. This
merely attaches a proved identity to the same original live row. -/
def actualRows_liveNonunitClass (hclass : chart.NonunitLabelStable)
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (anchor h : (chart.actualRows M X hX label).live) :
    (chart.actualRows M X hX label).NonunitClass C
      (actualNonunitPattern C b.primes b.leftMultiplicity b.rightMultiplicity (-anchor.val.out.val)) :=
  ⟨h, chart.actualRows_live_nonunitPattern_eq hclass M X hX label anchor h⟩

@[simp] theorem actualRows_liveNonunitClass_val (hclass : chart.NonunitLabelStable)
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (anchor h : (chart.actualRows M X hX label).live) :
    (chart.actualRows_liveNonunitClass hclass M X hX label anchor h).val = h := rfl

/-- The class is the full original live carrier, with an identity
underlying map. In particular there is no new fibre or sector count. -/
def actualRows_liveNonunitClassEquiv (hclass : chart.NonunitLabelStable)
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (anchor : (chart.actualRows M X hX label).live) :
    (chart.actualRows M X hX label).live ≃
      (chart.actualRows M X hX label).NonunitClass C
        (actualNonunitPattern C b.primes b.leftMultiplicity b.rightMultiplicity (-anchor.val.out.val)) where
  toFun := chart.actualRows_liveNonunitClass hclass M X hX label anchor
  invFun h := h.val
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

@[simp] theorem actualRows_liveNonunitClassEquiv_apply_val (hclass : chart.NonunitLabelStable)
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (anchor h : (chart.actualRows M X hX label).live) :
    ((chart.actualRows_liveNonunitClassEquiv hclass M X hX label anchor) h).val = h := rfl

end SecondBlockProfileChart

section Empty

variable {Dempty : (∅ : Finset (HeightOneSpectrum A.R)).powerset}

namespace SecondBlockProfileChart

variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius Dempty.val)

/-- The full-deletion window consumes the original live rows directly.
Pattern membership and the fixed class budget are proved internally;
the actual extracted row, its original sector, and the child data remain
those already used by the canonical full-deletion construction. -/
theorem canonicalOriginalChild_allowed_on_live_rowLabel
    (hclass : chart.NonunitLabelStable)
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
    (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
    (retainedScale Z g a₀ q wo cutoffExponent : ℝ)
    (hscale : 0 < retainedScale) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hleft : ∀ i ∈ left, A.exteriorNorm (fullI i) ≤ Z ^ a₀)
    (hright : ∀ j ∈ right, A.exteriorNorm (fullJ j) ≤ Z ^ a₀)
    (old : A.Exterior) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hremaining : remaining.val ∣ old.val)
    (hold : A.exteriorNorm old ≤ Z ^ (q + wo))
    (anchor h : (chart.actualRows ∅ X hX label).live)
    {ω ψ : HeckeCharacter K} (parent : MomentData K ω ψ)
    (correction : HeckeCharacter K) (hcorr : correction = 1 ∨ correction ∈ parent.theta)
    (sector : HeckeGeneral.Analysis.NonzeroIdeal K →
      SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (inverseTest leftTest rightTest : IdealTest K) (geometry : SlotGeometry K)
    (index : Fin geometry.slotCount → Fin parent.geometry.slotCount) :
    (CanonicalOriginalChildData.data parent
      (secondOriginalMovingFactors P Rchar C b.primes b.leftMultiplicity b.rightMultiplicity
        (actualNonunitPattern C b.primes b.leftMultiplicity b.rightMultiplicity (-anchor.val.out.val)))
      correction hcorr sector
      (remaining * secondSixthRootNonzeroIdeal b.primes b.leftMultiplicity b.rightMultiplicity)
      (Z ^ (secondCommonChildWidth Z a₀ q wo (Real.log retainedScale / Real.log Z) g
        (primePowerProduct b.primes b.leftMultiplicity).val
        (primePowerProduct b.primes b.rightMultiplicity).val
        (unitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-anchor.val.out.val)).val
        (nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-anchor.val.out.val)).val +
        idealLogLength Z (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val +
        cutoffExponent))
      inverseTest leftTest rightTest geometry index).allowedRow
        ((chart.actualRows ∅ X hX label).extractedRow C h).momentIdeal := by
  exact chart.canonicalOriginalChild_allowed_on_fullDeletion_class P Rchar X hX label
    retainedScale Z g a₀ q wo cutoffExponent hscale hZ hradius hcutoff hleft hright
    old remaining hremaining hold
    (actualNonunitPattern C b.primes b.leftMultiplicity b.rightMultiplicity (-anchor.val.out.val))
    (chart.actualRows_liveNonunitClass hclass ∅ X hX label anchor anchor)
    (chart.actualRows_liveNonunitClass hclass ∅ X hX label anchor h)
    parent correction hcorr sector inverseTest leftTest rightTest geometry index

end SecondBlockProfileChart
end Empty
end Charts

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

namespace ActualGaussStage

variable (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
variable {ι : Type*} (G : ActualGaussSource C ι)
variable (retainedScale Z g : ℝ) (hscale : 0 < retainedScale) (hZ : 0 < Z)
variable (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
variable (hnorm : ∀ h ∈ G.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable {Θ : Type*} [Fintype Θ] (dimension width : ℕ)

section Masked

variable (mask : Finset (HeightOneSpectrum A.R))
variable (havoid : ∀ h ∈ G.rows, ∀ p ∈ mask, h ∉ p.asIdeal)
variable (hcolumn : ∀ i ∈ G.columns, IsCoprime (G.generator i)
  (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) mask).val)
variable (character : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  mask.powerset → SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  mask.powerset → SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

/-- The actual canonical per-block classifier supplies the stable
nonunit flags without an additional premise about the source. -/
theorem canonicalRowBallByBlock_nonunitLabelStable
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val)) (D : mask.powerset) :
    ((canonicalRowBallByBlock (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδhalf G retainedScale Z g hscale hZ mask cutoff hcutoff
      hnorm havoid hcolumn dimension width character dyad).charts DE D).NonunitLabelStable := by
  intro q q' he i
  exact canonicalRowBallByBlock_nonunitSaving_iff_of_rowLabel_eq
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    δ hδ hδhalf G retainedScale Z g hscale hZ mask cutoff hcutoff
    hnorm havoid hcolumn dimension width character dyad DE D q q' he i

end Masked

section Unmasked

variable (character : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

theorem canonicalUnmaskedRowBallByBlock_nonunitLabelStable
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : (∅ : Finset (HeightOneSpectrum A.R)).powerset) :
    ((canonicalUnmaskedRowBallByBlock (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad).charts DE D).NonunitLabelStable := by
  intro q q' he i
  exact canonicalRowBallByBlock_nonunitSaving_iff_of_rowLabel_eq
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    δ hδ hδhalf G retainedScale Z g hscale hZ ∅ cutoff hcutoff hnorm
    G.emptyMask_row_avoidance G.emptyMask_columns_coprime
    dimension width (fun DE _ => character DE) (fun DE _ => dyad DE)
    DE D q q' he i

/-- This constructs the identity class equivalence on every existing
label of the actual unmasked stage. It neither reindexes sectors nor
introduces a Cartesian product with all possible finite patterns. -/
def canonicalUnmaskedRowBallByBlock_liveNonunitClassEquiv :
    let stage := canonicalUnmaskedRowBallByBlock
      (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad
    ∀ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
    ∀ D : (∅ : Finset (HeightOneSpectrum A.R)).powerset,
    let chart := stage.charts DE D
    ∀ label : Fin (chart.rowLabelCount + 1),
    let S := chart.actualRows ∅ cutoff hcutoff label
    ∀ anchor : S.live,
      S.live ≃ S.NonunitClass C
        (actualNonunitPattern C S.primes S.leftMultiplicity S.rightMultiplicity
          (S.frequency anchor.val)) := by
  dsimp only
  intro DE D label anchor
  exact ((canonicalUnmaskedRowBallByBlock
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
    dimension width character dyad).charts DE D).actualRows_liveNonunitClassEquiv
      (canonicalUnmaskedRowBallByBlock_nonunitLabelStable
        (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
        δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
        dimension width character dyad DE D)
      ∅ cutoff hcutoff label anchor

end Unmasked
end ActualGaussStage
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.actualRows_live_nonunitPattern_eq
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.actualRows_liveNonunitClassEquiv
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.canonicalOriginalChild_allowed_on_live_rowLabel
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalRowBallByBlock_nonunitLabelStable
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalUnmaskedRowBallByBlock_nonunitLabelStable
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalUnmaskedRowBallByBlock_liveNonunitClassEquiv
