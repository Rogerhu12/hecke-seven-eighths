import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondHybridSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SourceCartesianCover

/-!
# Actual second sources through their genuine Cartesian covers

The original Gauss source can have common-support and valuation
constraints that couple its occurrences.  Its actual finite cover is
split first.  Each Cartesian fibre is then split at the second common
support, and reaches the complete hybrid allocation identity.

Every row set below is computed from the original full source.  In
particular the supremum of all pairwise inverse radii, and hence the
physical cutoff, is not recomputed on a smaller column fibre.
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
variable {profiles : ι → κ → SchwartzMap Arch ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {hΓ hDiff μv}

namespace SecondBlockProfileChart

variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius D)
variable {left₀ : Finset ι} {right₀ : Finset κ}
variable (LA : SourceCartesianAtlas left₀ fullI) (RA : SourceCartesianAtlas right₀ fullJ)

/-- The exceptional test is fixed by the original finite row label,
the two actual occurrence labels, the finite ray character and the two
whole-divisor allocations, before either continuous Fourier variable. -/
abbrev SubsetSupportHybridPredicates :=
  ∀ label : Fin (chart.rowLabelCount + 1),
    ∀ a : LA.labels (primeSupport DE.1) DE.1,
    ∀ e : RA.labels (primeSupport DE.1) DE.2,
    ∀ S : Ideal (𝓞 K), ((PUnit × PUnit) →* Circle) →
      (primeSupport S → Finset (Fin ((LA.branch (primeSupport DE.1) DE.1 a).keep.card + 2))) →
      (primeSupport S → Finset (Fin ((RA.branch (primeSupport DE.1) DE.2 e).keep.card + 2))) →
      Q → Prop

def subsetHybridClassCost
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (exceptional : chart.SubsetSupportHybridPredicates LA RA) : ℝ :=
  ∑ a : LA.labels (primeSupport DE.1) DE.1,
    ∑ e : RA.labels (primeSupport DE.1) DE.2,
      chart.hybridClassCost M X hX label
        (LA.residualReindex (primeSupport DE.1) DE.1 b.leftResidual
          (fun i _ => b.left_residual i) a)
        (RA.residualReindex (primeSupport DE.1) DE.2 b.rightResidual
          (fun j _ => b.right_residual j) e)
        (exceptional label a e)

def subsetHybridCost
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (exceptional : chart.SubsetSupportHybridPredicates LA RA) : ℝ :=
  ∑ label : Fin (chart.rowLabelCount + 1),
    chart.subsetHybridClassCost LA RA M X hX label exceptional

/-- One complete source row class is split by the real support-key
images, before any norm or Cauchy step.  The original coefficients may be
whole centered differences. -/
theorem subset_hybrid_class_bound
    (hleft₀ : left₀ ⊆ left) (hright₀ : right₀ ⊆ right)
    (hsupport : primeSupport DE.1 = primeSupport DE.2)
    (hleft : ∀ i, ∃ u : Kˣ, (u : K) = (b.leftGenerator i : K) ∧
      A.IsAllowed C.correction.B u)
    (hright : ∀ j, ∃ u : Kˣ, (u : K) = (b.rightGenerator j : K) ∧
      A.IsAllowed C.correction.B u)
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (exceptional : chart.SubsetSupportHybridPredicates LA RA) :
    ‖∑ t ∈ (chart.actualRows M X hX label).rows,
      ∑ i ∈ LA.commonColumns (primeSupport DE.1) DE.1,
      ∑ j ∈ RA.commonColumns (primeSupport DE.1) DE.2,
        (b.secondPair hΓ hDiff C profiles i j).transformedRow
          μv hDiff finiteTest radius D t‖ ≤
      chart.subsetHybridClassCost LA RA M X hX label exceptional := by
  rw [LA.sum_pair_rows RA (chart.actualRows M X hX label).rows
    (primeSupport DE.1) DE.1 DE.2]
  unfold subsetHybridClassCost
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro e _
  exact chart.class_hybrid_bound_on hsupport hleft hright M X hX label
    (LA.commonFibre (primeSupport DE.1) DE.1 a)
    (RA.commonFibre (primeSupport DE.1) DE.2 e)
    (by
      intro i hi
      have hc := LA.commonFibre_subset (primeSupport DE.1) DE.1 a hi
      obtain ⟨hi₀, he⟩ := Finset.mem_filter.mp hc
      exact Finset.mem_filter.mpr ⟨hleft₀ hi₀, he⟩)
    (by
      intro j hj
      have hc := RA.commonFibre_subset (primeSupport DE.1) DE.2 e hj
      obtain ⟨hj₀, he⟩ := Finset.mem_filter.mp hc
      exact Finset.mem_filter.mpr ⟨hright₀ hj₀, he⟩)
    (LA.residualReindex (primeSupport DE.1) DE.1 b.leftResidual
      (fun i _ => b.left_residual i) a)
    (RA.residualReindex (primeSupport DE.1) DE.2 b.rightResidual
      (fun j _ => b.right_residual j) e)
    (exceptional label a e)

/-- The whole nonzero orbital source uses the same physical cutoff as
its actual zero and tail terms.  This is a direct replacement for a
post-Cauchy kernel-cost exit. -/
theorem subset_hybrid_bound
    (hleft₀ : left₀ ⊆ left) (hright₀ : right₀ ⊆ right)
    (hsupport : primeSupport DE.1 = primeSupport DE.2)
    (hleft : ∀ i, ∃ u : Kˣ, (u : K) = (b.leftGenerator i : K) ∧
      A.IsAllowed C.correction.B u)
    (hright : ∀ j, ∃ u : Kˣ, (u : K) = (b.rightGenerator j : K) ∧
      A.IsAllowed C.correction.B u)
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (exceptional : chart.SubsetSupportHybridPredicates LA RA) :
    let source := b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX
    ‖∑ t ∈ source.rows,
      ∑ i ∈ LA.commonColumns (primeSupport DE.1) DE.1,
      ∑ j ∈ RA.commonColumns (primeSupport DE.1) DE.2,
        (source.pairs i j).transformedRow μv hDiff finiteTest radius D t‖ ≤
      chart.subsetHybridCost LA RA M X hX exceptional := by
  dsimp only
  unfold subsetHybridCost
  rw [sum_actual_row_labels
    (b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX).rows chart.rowLabel]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro label _
  exact chart.subset_hybrid_class_bound LA RA hleft₀ hright₀ hsupport hleft hright
    M X hX label exceptional


variable (LC : SourceCartesianCover left fullI) (RC : SourceCartesianCover right fullJ)

/-- Every finite exceptional predicate is selected before continuous
Fourier parameters, after the true original cover labels. -/
abbrev CoverHybridPredicates :=
  ∀ a : LC.labels, ∀ e : RC.labels,
    chart.SubsetSupportHybridPredicates (LC.branch a) (RC.branch e)

def coverHybridCost
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (exceptional : chart.CoverHybridPredicates LC RC) : ℝ :=
  ∑ a : LC.labels, ∑ e : RC.labels,
    chart.subsetHybridCost (LC.branch a) (RC.branch e) M X hX (exceptional a e)

/-- The complete original second source enters actual hybrid branches
without an assumption that its unsplit residual columns are Cartesian.
The finite label sums and the original physical rows are retained
literally; no total kernel or source estimate is an input. -/
theorem cover_hybrid_bound
    (hsupport : primeSupport DE.1 = primeSupport DE.2)
    (hleft : ∀ i, ∃ u : Kˣ, (u : K) = (b.leftGenerator i : K) ∧
      A.IsAllowed C.correction.B u)
    (hright : ∀ j, ∃ u : Kˣ, (u : K) = (b.rightGenerator j : K) ∧
      A.IsAllowed C.correction.B u)
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (exceptional : chart.CoverHybridPredicates LC RC) :
    let source := b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX
    ‖∑ t ∈ source.rows, ∑ i ∈ source.leftColumns, ∑ j ∈ source.rightColumns,
      (source.pairs i j).transformedRow μv hDiff finiteTest radius D t‖ ≤
      chart.coverHybridCost LC RC M X hX exceptional := by
  dsimp only
  change ‖∑ t ∈ (b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX).rows,
    ∑ i ∈ left.filter (fun i =>
      HeckePort.Moments.Support.supportExtract (fullI i).val (primeSupport DE.1) = DE.1),
    ∑ j ∈ right.filter (fun j =>
      HeckePort.Moments.Support.supportExtract (fullJ j).val (primeSupport DE.1) = DE.2),
      (b.secondPair hΓ hDiff C profiles i j).transformedRow
        μv hDiff finiteTest radius D t‖ ≤ _
  rw [LC.sum_pair_rows RC
    (b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX).rows]
  unfold coverHybridCost
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro e _
  exact chart.subset_hybrid_bound (LC.branch a) (RC.branch e)
    (LC.fibre_subset a.val) (RC.fibre_subset e.val)
    hsupport hleft hright M X hX (exceptional a e)

end SecondBlockProfileChart

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.subset_hybrid_bound
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.cover_hybrid_bound

