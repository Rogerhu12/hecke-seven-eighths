import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondHybridChart
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SourceCartesianAtlas

/-!
# The complete actual second source reaches hybrid branches

The original common-source columns are partitioned by their computed
extracted occurrence tuples.  Every residual Cartesian dictionary is
constructed from the original EXPANSION atlas, and every actual row label
is separated before any row Cauchy estimate.  The bound starts from the
original finite transformedRow sum, so exceptional whole-centered
products are never inferred from an earlier paired-energy bound.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "Arch" => mixedEmbedding.euclidean.mixedSpace K

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η htrace}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {hΓ hDiff μv}

namespace SecondBlockProfileChart

variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius D)
variable (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)

/-- The exceptional test is fixed by the original finite row label,
the two actual occurrence labels, the finite ray character and the two
whole-divisor allocations, before either continuous Fourier variable. -/
abbrev SupportHybridPredicates :=
  ∀ label : Fin (chart.rowLabelCount + 1),
    ∀ a : LA.labels (primeSupport DE.1) DE.1,
    ∀ e : RA.labels (primeSupport DE.1) DE.2,
    ∀ S : Ideal (𝓞 K), ((PUnit × PUnit) →* Circle) →
      (primeSupport S → Finset (Fin ((LA.branch (primeSupport DE.1) DE.1 a).keep.card + 2))) →
      (primeSupport S → Finset (Fin ((RA.branch (primeSupport DE.1) DE.2 e).keep.card + 2))) →
      Q → Prop

def supportHybridClassCost
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (exceptional : chart.SupportHybridPredicates LA RA) : ℝ :=
  ∑ a : LA.labels (primeSupport DE.1) DE.1,
    ∑ e : RA.labels (primeSupport DE.1) DE.2,
      chart.hybridClassCost M X hX label
        (LA.residualReindex (primeSupport DE.1) DE.1 b.leftResidual
          (fun i _ => b.left_residual i) a)
        (RA.residualReindex (primeSupport DE.1) DE.2 b.rightResidual
          (fun j _ => b.right_residual j) e)
        (exceptional label a e)

def supportHybridCost
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (exceptional : chart.SupportHybridPredicates LA RA) : ℝ :=
  ∑ label : Fin (chart.rowLabelCount + 1),
    chart.supportHybridClassCost LA RA M X hX label exceptional

/-- One complete source row class is split by the real support-key
images, before any norm or Cauchy step.  The original coefficients may be
whole centered differences. -/
theorem support_hybrid_class_bound
    (hsupport : primeSupport DE.1 = primeSupport DE.2)
    (hleft : ∀ i, ∃ u : Kˣ, (u : K) = (b.leftGenerator i : K) ∧
      A.IsAllowed C.correction.B u)
    (hright : ∀ j, ∃ u : Kˣ, (u : K) = (b.rightGenerator j : K) ∧
      A.IsAllowed C.correction.B u)
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (exceptional : chart.SupportHybridPredicates LA RA) :
    ‖∑ t ∈ (chart.actualRows M X hX label).rows,
      ∑ i ∈ b.leftColumns left, ∑ j ∈ b.rightColumns right,
        (b.secondPair hΓ hDiff C profiles i j).transformedRow
          μv hDiff finiteTest radius D t‖ ≤
      chart.supportHybridClassCost LA RA M X hX label exceptional := by
  change ‖∑ t ∈ (chart.actualRows M X hX label).rows,
    ∑ i ∈ LA.commonColumns (primeSupport DE.1) DE.1,
    ∑ j ∈ RA.commonColumns (primeSupport DE.1) DE.2,
      (b.secondPair hΓ hDiff C profiles i j).transformedRow
        μv hDiff finiteTest radius D t‖ ≤ _
  rw [LA.sum_pair_rows RA (chart.actualRows M X hX label).rows
    (primeSupport DE.1) DE.1 DE.2]
  unfold supportHybridClassCost
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro e _
  exact chart.class_hybrid_bound_on hsupport hleft hright M X hX label
    (LA.commonFibre (primeSupport DE.1) DE.1 a)
    (RA.commonFibre (primeSupport DE.1) DE.2 e)
    (LA.commonFibre_subset (primeSupport DE.1) DE.1 a)
    (RA.commonFibre_subset (primeSupport DE.1) DE.2 e)
    (LA.residualReindex (primeSupport DE.1) DE.1 b.leftResidual
      (fun i _ => b.left_residual i) a)
    (RA.residualReindex (primeSupport DE.1) DE.2 b.rightResidual
      (fun j _ => b.right_residual j) e)
    (exceptional label a e)

/-- The whole nonzero orbital source uses the same physical cutoff as
its actual zero and tail terms.  This is a direct replacement for a
post-Cauchy kernel-cost exit. -/
theorem support_hybrid_bound
    (hsupport : primeSupport DE.1 = primeSupport DE.2)
    (hleft : ∀ i, ∃ u : Kˣ, (u : K) = (b.leftGenerator i : K) ∧
      A.IsAllowed C.correction.B u)
    (hright : ∀ j, ∃ u : Kˣ, (u : K) = (b.rightGenerator j : K) ∧
      A.IsAllowed C.correction.B u)
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (exceptional : chart.SupportHybridPredicates LA RA) :
    let source := b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX
    ‖∑ t ∈ source.rows, ∑ i ∈ source.leftColumns, ∑ j ∈ source.rightColumns,
      (source.pairs i j).transformedRow μv hDiff finiteTest radius D t‖ ≤
      chart.supportHybridCost LA RA M X hX exceptional := by
  dsimp only
  unfold supportHybridCost
  rw [sum_actual_row_labels
    (b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX).rows chart.rowLabel]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro label _
  exact chart.support_hybrid_class_bound LA RA hsupport hleft hright
    M X hX label exceptional

end SecondBlockProfileChart

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.support_hybrid_class_bound
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.support_hybrid_bound

