import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondHybridAllocation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SupportKernelPartition

/-!
# The actual second source before Cauchy

These identities expose the original complex orbital source, retain its
whole coefficients, and reindex its actual finite column branches before
any norm or row Cauchy estimate.  The only analytic calibration is the
original pointwise profile chart for each retained row/pair.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments

section FiniteColumns

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {H α β Λ Ω : Type*}

private theorem sum_columns_by_label {M : Type*} [AddCommMonoid M]
    (S : Finset α) (label : α → Λ) (c : α → M) :
    (∑ i ∈ S, c i) = ∑ a ∈ S.image label, ∑ i ∈ S.filter (fun i => label i = a), c i :=
  (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem label hi) c).symm

/-- An exact partition of the original coupled form.  In particular it
may precede the exceptional/ordinary row split on every resulting branch. -/
theorem joint_kernel_column_partition
    (F : 𝓢(V, ℂ)) (rows : Finset H) (left : Finset α) (right : Finset β)
    (labelLeft : α → Λ) (labelRight : β → Ω)
    (q : H → ℂ) (c : H → α → ℂ) (d : H → β → ℂ)
    (x : H → α → V) (y : H → β → V) :
    jointKernelPairing F rows left right q c d x y =
      ∑ ab ∈ (left.image labelLeft).product (right.image labelRight),
        jointKernelPairing F rows (left.filter (fun i => labelLeft i = ab.1))
          (right.filter (fun j => labelRight j = ab.2)) q c d x y := by
  simp only [jointKernelPairing, Finset.product_eq_sprod, Finset.sum_product]
  simp_rw [sum_columns_by_label left labelLeft, sum_columns_by_label right labelRight]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := rows) (t := left.image labelLeft)]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [Finset.sum_comm (s := left.filter (fun i => labelLeft i = a))
    (t := right.image labelRight)]
  rw [Finset.sum_comm (s := rows) (t := right.image labelRight)]

variable {K : Type} [Field K] [NumberField K] {A : SArithmeticData K}
variable {k l : ℕ}

theorem CartesianSourceReindex.joint_kernel_reindex
    (left : Finset α) (right : Finset β) (IA : α → A.Exterior) (IB : β → A.Exterior)
    (L : CartesianSourceReindex left IA k) (R : CartesianSourceReindex right IB l)
    (F : 𝓢(V, ℂ)) (rows : Finset H) (q : H → ℂ)
    (c : H → α → ℂ) (d : H → β → ℂ)
    (x : H → α → V) (y : H → β → V) :
    jointKernelPairing F rows left right q c d x y =
      jointKernelPairing F rows L.cartesian R.cartesian q
        (fun h i => c h (L.index i)) (fun h j => d h (R.index j))
        (fun h i => x h (L.index i)) (fun h j => y h (R.index j)) := by
  unfold jointKernelPairing
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  rw [L.sum_reindex]
  apply Finset.sum_congr rfl
  intro i _
  exact R.sum_reindex (fun j => c h (L.index i) * star (d h j) *
    F (x h (L.index i) + y h j))

end FiniteColumns

section ActualOrbitalSource

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)

local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "Arch" => mixedEmbedding.euclidean.mixedSpace K

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- The full orbital source becomes its actual complete correlation
form by applying the genuine Poisson coefficient identity to each
retained pair.  No aggregate transform equality is assumed. -/
theorem actual_second_source_chart_identity {ι κ : Type*}
    (F : 𝓢(E, ℂ)) (rows : Finset Q) (left : Finset ι) (right : Finset κ)
    (I : ι → A.Exterior) (J : κ → A.Exterior)
    (a : ι → A.R) (b : κ → A.R)
    (ha : ∀ i, A.Generates (I i) (a i)) (hb : ∀ j, A.Generates (J j) (b j))
    (gate : ι → κ → Prop)
    (profiles : ι → κ → SchwartzMap Arch ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (hleftMask : ∀ i ∈ left,
      IsCoprime (a i) (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (hrightMask : ∀ j ∈ right,
      IsCoprime (b j) (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (q : Q → ℂ) (c : ι → ℂ) (f : κ → ℂ)
    (x : Q → ι → E) (y : Q → κ → E)
    (hprofile : ∀ t ∈ rows, ∀ i ∈ left, ∀ j ∈ right, gate i j →
      (generatedOriginalColumn (σ := σ) hΓ (I i) (a i) (ha i)).secondProfile μv hS
        (generatedOriginalColumn (σ := σ) hΓ (J j) (b j) (hb j))
        (profiles i j) finiteTest radius D t =
          q t * (c i * star (f j)) * F (x t i + y t j)) :
    let L := fun i => generatedOriginalColumn (σ := σ) hΓ (I i) (a i) (ha i)
    let R := fun j => generatedOriginalColumn (σ := σ) hΓ (J j) (b j) (hb j)
    let δ := (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
    (∑ t ∈ rows, ∑ i ∈ left, ∑ j ∈ right,
      (((L i).pair hS (R j) (profiles i j)).gated (gate i j)).transformedRow
        μv hS finiteTest radius D t) =
      ∑ t ∈ rows, (secondOrbitalScalar radius D * q t) *
        ∑ i ∈ left, ∑ j ∈ right,
          (if gate i j then generatedIdealCorrelation (σ := σ) (I i) (J j)
            (a i) (b j) (ha i) (hb j) (-t.out.val) else 0) *
            ((c i * (L i).divisorPhase δ) * star (f j * (R j).divisorPhase δ)) *
              F (x t i + y t j) := by
  dsimp only
  let L := fun i => generatedOriginalColumn (σ := σ) hΓ (I i) (a i) (ha i)
  let R := fun j => generatedOriginalColumn (σ := σ) hΓ (J j) (b j) (hb j)
  let δ := (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [ParentPeriodicPair.gated_transformedRow]
  by_cases hij : gate i j
  · rw [if_pos hij, if_pos hij,
      (L i).transformedRow_out μv hS (R j) (profiles i j) finiteTest radius D
        (hleftMask i hi) (hrightMask j hj) t]
    rw [hprofile t ht i hi j hj hij, generatedColumn_correlation]
    simp only [star_mul, δ]
    ring
  · simp only [if_neg hij, zero_mul, mul_zero]

end ActualOrbitalSource

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.joint_kernel_column_partition
#print axioms HeckeSkeleton.Moments.EngineStep.CartesianSourceReindex.joint_kernel_reindex
#print axioms HeckeSkeleton.Moments.EngineStep.actual_second_source_chart_identity

