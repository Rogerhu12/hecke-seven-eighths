import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PreCauchySource

/-!
# The actual second chart reaches its hybrid allocated children

The input Cartesian dictionaries refer to retained source subsets.  They
can therefore be the real occurrence-support branches constructed by
`SupportCartesianBranch` and the actual valuation subtypes of the one
prime pool.  The original chart and coefficient functions are retained.

The proof begins with the actual complex orbital row sum.  It applies
the true per-pair Poisson coefficient identity, reindexes the retained
source columns, and only then invokes the complete common-correlation,
Möbius, finite-phase and whole-occurrence allocation identities.  The
exceptional part is a sum of same-row products of whole centered
polynomials.  No post-Cauchy cost is used as a premise.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum

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

/-- The literal positive hybrid cost of one retained column branch and
one actual row label.  Both whole coefficient functions and the original
Schwartz kernel are the ones supplied by the original source chart. -/
def hybridClassCost
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    {left₀ : Finset ι} {right₀ : Finset κ} {k l : ℕ}
    (L : CartesianSourceReindex left₀ b.leftResidual k)
    (R : CartesianSourceReindex right₀ b.rightResidual l)
    (exceptional : ∀ S : Ideal (𝓞 K), ((PUnit × PUnit) →* Circle) →
      (primeSupport S → Finset (Fin (k + 2))) →
      (primeSupport S → Finset (Fin (l + 2))) → Q → Prop) : ℝ :=
  secondResidualHybridCost PUnit chart.kernel
    (chart.actualRows M X hX label).rows
    (chart.actualRows M X hX label).frequency
    L.plain₁ L.plain₂ L.slots R.plain₁ R.plain₂ R.slots
    b.commonLeftIdeal b.commonRightIdeal
    (fun i => b.leftResidual (L.index i)) (fun j => b.rightResidual (R.index j))
    (engineAllowedGenerator C b.commonLeftIdeal) (engineAllowedGenerator C b.commonRightIdeal)
    (engineAllowedGenerator_generates C _) (engineAllowedGenerator_generates C _)
    (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (1 : Circle))
    (chart.actualRows M X hX label).weight
    (fun i => chart.sourceLeftCoefficient (L.index i))
    (fun j => chart.sourceRightCoefficient (R.index j))
    (fun h i => chart.leftPoint h (L.index i))
    (fun h j => chart.rightPoint h (R.index j)) exceptional

/-- A real source branch reaches actual hybrid children.  The only
branch inputs are retained-support inclusions and the primitive
individual-column expansion dictionaries.  Common correlation,
reciprocal phases, allocation and the exceptional row split are proved
inside the reduction. -/
theorem class_hybrid_bound_on
    (hsupport : primeSupport DE.1 = primeSupport DE.2)
    (hleft : ∀ i, ∃ u : Kˣ, (u : K) = (b.leftGenerator i : K) ∧
      A.IsAllowed C.correction.B u)
    (hright : ∀ j, ∃ u : Kˣ, (u : K) = (b.rightGenerator j : K) ∧
      A.IsAllowed C.correction.B u)
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (left₀ : Finset ι) (right₀ : Finset κ)
    (hleft₀ : left₀ ⊆ b.leftColumns left)
    (hright₀ : right₀ ⊆ b.rightColumns right)
    {k l : ℕ}
    (L : CartesianSourceReindex left₀ b.leftResidual k)
    (R : CartesianSourceReindex right₀ b.rightResidual l)
    (exceptional : ∀ S : Ideal (𝓞 K), ((PUnit × PUnit) →* Circle) →
      (primeSupport S → Finset (Fin (k + 2))) →
      (primeSupport S → Finset (Fin (l + 2))) → Q → Prop) :
    ‖∑ t ∈ (chart.actualRows M X hX label).rows,
      ∑ i ∈ left₀, ∑ j ∈ right₀,
        (b.secondPair hΓ hDiff C profiles i j).transformedRow
          μv hDiff finiteTest radius D t‖ ≤
      chart.hybridClassCost M X hX label L R exceptional := by
  let rows := (chart.actualRows M X hX label).rows
  let q : Q → ℂ := fun t => secondOrbitalScalar radius D * chart.weight t
  let summand : Q → ι → κ → ℂ := fun t i j =>
    (if IsCoprime (b.leftResidual i).val (b.rightResidual j).val then
      generatedIdealCorrelation (σ := σ) (b.secondLeftIdeal i) (b.secondRightIdeal j)
        (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
        (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j)
        (b.secondLeft_generates C i) (b.secondRight_generates C j) (-t.out.val)
      else 0) *
      (chart.sourceLeftCoefficient i * star (chart.sourceRightCoefficient j)) *
        chart.kernel (chart.leftPoint t i + chart.rightPoint t j)
  have hsource :
      (∑ t ∈ rows, ∑ i ∈ left₀, ∑ j ∈ right₀,
        (b.secondPair hΓ hDiff C profiles i j).transformedRow
          μv hDiff finiteTest radius D t) =
      ∑ t ∈ rows, q t * ∑ i ∈ left₀, ∑ j ∈ right₀, summand t i j := by
    have h := actual_second_source_chart_identity (hΓ := hΓ) (hS := hDiff)
      (μv := μv) chart.kernel rows left₀ right₀
      b.secondLeftIdeal b.secondRightIdeal
      (fun i => engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
      (fun j => engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j)
      (b.secondLeft_generates C) (b.secondRight_generates C)
      (fun i j => IsCoprime (b.leftResidual i).val (b.rightResidual j).val)
      profiles finiteTest radius D
      (fun i hi => chart.left_mask i (hleft₀ hi))
      (fun j hj => chart.right_mask j (hright₀ hj))
      chart.weight chart.leftCoefficient chart.rightCoefficient chart.leftPoint chart.rightPoint
      (fun t _ i hi j hj hc => chart.profile t i (hleft₀ hi) j (hright₀ hj) hc)
    simpa only [FirstCommonCharacterBlock.secondPair, sourceLeftCoefficient,
      sourceRightCoefficient, q, summand] using h
  have hreindex :
      (∑ t ∈ rows, q t * ∑ i ∈ left₀, ∑ j ∈ right₀, summand t i j) =
      ∑ t ∈ rows, q t * ∑ i ∈ L.cartesian, ∑ j ∈ R.cartesian,
        summand t (L.index i) (R.index j) := by
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    rw [L.sum_reindex]
    apply Finset.sum_congr rfl
    intro i _
    exact R.sum_reindex (fun j => summand t (L.index i) j)
  obtain ⟨hDa, hEa, hDb, hEb⟩ := b.second_coprimalities hsupport
  calc
    _ = ‖∑ t ∈ rows, q t * ∑ i ∈ L.cartesian, ∑ j ∈ R.cartesian,
        summand t (L.index i) (R.index j)‖ := congrArg norm (hsource.trans hreindex)
    _ ≤ _ := by
      exact actual_second_residual_hybrid_allocated_bound (Ray := PUnit)
        chart.kernel rows (fun t : Q => -t.out.val)
        L.plain₁ L.plain₂ L.slots R.plain₁ R.plain₂ R.slots
        b.commonLeftIdeal b.commonRightIdeal
        (fun i => b.leftResidual (L.index i)) (fun j => b.rightResidual (R.index j))
        L.ideal_product R.ideal_product
        (fun i => b.secondLeftIdeal (L.index i))
        (fun j => b.secondRightIdeal (R.index j))
        (fun _ => rfl) (fun _ => rfl)
        (engineAllowedGenerator C b.commonLeftIdeal)
        (engineAllowedGenerator C b.commonRightIdeal)
        (fun i => b.leftGenerator (L.index i)) (fun j => b.rightGenerator (R.index j))
        (engineAllowedGenerator_generates C _) (engineAllowedGenerator_generates C _)
        (fun i => b.left_generates (L.index i)) (fun j => b.right_generates (R.index j))
        (fun i => b.secondLeft_generates C (L.index i))
        (fun j => b.secondRight_generates C (R.index j))
        (fun i => hDa (L.index i)) (fun i => hEa (L.index i))
        (fun j => hDb (R.index j)) (fun j => hEb (R.index j))
        (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (1 : Circle))
        (fun i j hc => by
          simpa only [Circle.coe_one] using
            b.secondPhase_one hΓ C hsupport hleft hright (L.index i) (R.index j) hc)
        q (fun i => chart.sourceLeftCoefficient (L.index i))
        (fun j => chart.sourceRightCoefficient (R.index j))
        (fun t i => chart.leftPoint t (L.index i))
        (fun t j => chart.rightPoint t (R.index j)) exceptional

end SecondBlockProfileChart

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.class_hybrid_bound_on

