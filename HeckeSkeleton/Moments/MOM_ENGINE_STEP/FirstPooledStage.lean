import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDivisorPool
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonNormalization

/-!
# The actual parent through the first transform and one fixed pool

The arithmetic pool data are calibrated only at individual column ideals,
generators, finite carriers, and a pointwise original profile multiplier.
The complete active Gauss factor is bounded internally by the square
root of its actual norm. The source transform, common kernel, and pool
inequalities are all proved providers. No whole transformed or parent
energy comparison occurs among the inputs.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

theorem sIntegerOrbit_out_val_injective : Function.Injective (fun q : Q => q.out.val) := by
  intro q q' he
  exact Quotient.out_injective (Subtype.ext he)

variable {hΓ μv}
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap V ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Zpool ell eps : ℝ}

/-- Primitive calibration from one actual first source to the earlier
pool. Both complete residual columns and every physical orbit are kept. -/
structure FirstBlockPoolData
    (chart : FirstBlockProfileChart (E := E) hΓ μv b C left right profiles finiteTest radius D)
    (P : PowerScaleExteriorPool A bad Zpool ell eps)
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X) where
  leftData : FirstGaussPoolData C P ι
  rightData : FirstGaussPoolData C P κ
  divisorPools : FirstDivisorPoolData leftData rightData
  left_columns : leftData.columns = b.leftColumns left
  right_columns : rightData.columns = b.rightColumns right
  left_ideal : leftData.ideal = b.leftResidual
  right_ideal : rightData.ideal = b.rightResidual
  left_generator : leftData.generator = b.leftGenerator
  right_generator : rightData.generator = b.rightGenerator
  left_rows : ((b.finiteSource hΓ C left right profiles M radius X hX).rows.image
    (fun t : Q => t.out.val)) ⊆ leftData.rows
  right_rows : ((b.finiteSource hΓ C left right profiles M radius X hX).rows.image
    (fun t : Q => -t.out.val)) ⊆ rightData.rows
  weightBound : ℝ
  weight_nonneg : 0 ≤ weightBound
  weight_bound : ∀ t ∈ (b.finiteSource hΓ C left right profiles M radius X hX).rows,
    ‖chart.weight t‖ ≤ weightBound

namespace FirstBlockPoolData

variable {chart : FirstBlockProfileChart (E := E) hΓ μv b C left right profiles finiteTest radius D}
variable {P : PowerScaleExteriorPool A bad Zpool ell eps}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}

def rowBound (p : FirstBlockPoolData chart P M X hX) : ℝ :=
  p.weightBound * Real.sqrt (A.exteriorNorm
    (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity))

theorem rowBound_nonneg (p : FirstBlockPoolData chart P M X hX) : 0 ≤ p.rowBound :=
  mul_nonneg p.weight_nonneg (Real.sqrt_nonneg _)

/-- The genuine active factor, including its divisor character and
the original Moebius coefficient, is bounded internally. -/
theorem common_weight_bound (p : FirstBlockPoolData chart P M X hX)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (t : Q) (ht : t ∈ (b.finiteSource hΓ C left right profiles M radius X hX).rows) :
    let r := actualActiveColumn hΓ C b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity
    let δ := (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
    ‖chart.weight t * ((moebius (IdealMobiusMask.primeProduct D) : ℂ) *
      (r.character (Ideal.Quotient.mk _ δ) *
        actualSIntegerGauss K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hDiff r.modulus r.nonzero r.character t.out.val))‖ ≤
      p.rowBound := by
  dsimp only
  have hmu : ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ ≤ 1 := by
    unfold moebius
    split_ifs <;> simp
  have hactive := actual_sInteger_active_divisor_gauss_norm_le_sqrt C hDiff
    b.primes b.primes_injective b.leftMultiplicity b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val t.out.val
  rw [norm_mul, norm_mul]
  apply mul_le_mul (p.weight_bound t ht) _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    p.weight_nonneg
  exact (mul_le_mul hmu hactive (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

def pooledCost (p : FirstBlockPoolData chart P M X hX) : ℝ :=
  let a := fun i => generatedOriginalColumn (σ := σ) hΓ
    (b.leftResidual i) (b.leftGenerator i) (b.left_generates i)
  let a' := fun j => generatedOriginalColumn (σ := σ) hΓ
    (b.rightResidual j) (b.rightGenerator j) (b.right_generates j)
  let r := actualActiveColumn hΓ C b.primes b.primes_injective
    b.leftMultiplicity b.rightMultiplicity
  let δ := (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
  firstDivisorPooledResidualCost PUnit.{1} chart.kernel p.leftData p.rightData p.divisorPools
    (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (1 : Circle)) p.rowBound
    (fun i => chart.leftCoefficient i * firstLeftDivisorFactor (a i) r δ)
    (fun j => chart.rightCoefficient j * firstRightDivisorFactor (a' j) r δ)
    chart.leftPoint chart.rightPoint

include profiles in
theorem kernelCost_le_pool (p : FirstBlockPoolData chart P M X hX)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0) :
    chart.kernelCost hDiff M X hX ≤ p.pooledCost := by
  let a := fun i => generatedOriginalColumn (σ := σ) hΓ
    (b.leftResidual i) (b.leftGenerator i) (b.left_generates i)
  let a' := fun j => generatedOriginalColumn (σ := σ) hΓ
    (b.rightResidual j) (b.rightGenerator j) (b.right_generates j)
  let r := actualActiveColumn hΓ C b.primes b.primes_injective
    b.leftMultiplicity b.rightMultiplicity
  let δ := (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
  have he := first_residual_cost_le_divisor_pool (Ray := PUnit.{1}) (hΓ := hΓ)
    chart.kernel p.leftData p.rightData p.divisorPools hDiff
    (b.finiteSource hΓ C left right profiles M radius X hX).rows (fun t : Q => t.out.val)
    sIntegerOrbit_out_val_injective.injOn p.left_rows p.right_rows
    (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (1 : Circle))
    (fun t : Q => (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
      (r.character (Ideal.Quotient.mk _ δ) *
        actualSIntegerGauss K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hDiff r.modulus r.nonzero r.character t.out.val))
    chart.weight p.rowBound p.rowBound_nonneg (fun t ht => p.common_weight_bound hDiff t ht)
    (fun i => chart.leftCoefficient i * firstLeftDivisorFactor (a i) r δ)
    (fun j => chart.rightCoefficient j * firstRightDivisorFactor (a' j) r δ)
    chart.leftPoint chart.rightPoint
  simpa only [FirstBlockProfileChart.kernelCost, FirstCommonCharacterBlock.finiteSource,
    pooledCost, a, a', r, δ, p.left_columns, p.right_columns, p.left_ideal, p.right_ideal,
    p.left_generator, p.right_generator] using he

end FirstBlockPoolData

section Parent

variable (hΓ μv)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- The actual parent energy through the genuine first orbital transform
and one fixed arithmetic pool. Constants and seminorms are chosen before
the pool scale, source indices, and all common Fourier parameters. -/
theorem parent_first_stage_pool_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ L < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Ctail : ℝ, 0 ≤ Ctail ∧
    ∀ (Zpool ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Zpool ell eps),
    ∀ {ι : Type*} (columns : Finset ι) (fullI : ι → A.Exterior)
      (afull : ι → A.R) (hafull : ∀ i, A.Generates (fullI i) (afull i))
      (profiles : ι → ι → SchwartzMap V ℂ) (radius : {r : ℝ // 0 < r})
      (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X),
    let blocks := fun DE : commonSupportPool columns columns (fun i => (fullI i).val)
        (fun j => (fullI j).val) =>
      canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
    let sources := fun DE => (blocks DE).finiteSource hΓ C columns columns profiles M radius X hX
    ∀ charts : ∀ DE, ∀ D : ((blocks DE).mask M).powerset,
      FirstBlockProfileChart (E := E) hΓ μv (blocks DE) C columns columns profiles
        finiteTest radius D.val,
    ∀ pools : ∀ DE, ∀ D : ((blocks DE).mask M).powerset,
      FirstBlockPoolData (charts DE D) P M X hX,
    ∀ {ω ψ₀ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ₀)
      (a : RealParameters) (t Y₁ Y₂ : ℝ) (B : ℕ),
    ParentSourceCalibration centered d a Zpool t Y₁ Y₂ columns
      (fun i j => (generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i)).originalPair
        (generatedOriginalColumn (σ := σ) hΓ (fullI j) (afull j) (hafull j)) (profiles i j))
      (sIntegerFiniteTestFunction K A.Sf finiteTest) radius M B →
    pairedStageEnergy centered d a Zpool t Y₁ Y₂ ≤
      (B : ℝ) * ∑ DE,
        (‖(sources DE).zeroTerm μv hDiff finiteTest‖ +
          (∑ D : ((blocks DE).mask M).powerset, (pools DE D).pooledCost) +
          Ctail * X ^ (1 - decay) *
            ∑ i ∈ (sources DE).leftColumns, ∑ j ∈ (sources DE).rightColumns,
              seminorms.sup (schwartzSeminormFamily ℂ V ℂ) ((sources DE).pairs i j).profile *
                ((sources DE).pairs i j).truncationMass (sources DE).mask radius) := by
  obtain ⟨seminorms, Ctail, hC, hparent⟩ :=
    parent_first_stage_bound (E := E) (hΓ := hΓ) (μv := μv) (ν := ν) (μ := μ)
      C hDiff finiteTest hlc hcs decay hdecay order horder hdegree
  refine ⟨seminorms, Ctail, hC, ?_⟩
  intro Zpool ell eps bad P ι columns fullI afull hafull profiles radius M X hX
  dsimp only
  intro charts pools ω ψ₀ centered d a t Y₁ Y₂ B cal
  have hp := hparent columns fullI afull hafull profiles radius M X hX
    charts centered d a Zpool t Y₁ Y₂ B cal
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro DE _
  refine add_le_add ?_ le_rfl
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro D _
  exact (pools DE D).kernelCost_le_pool hDiff

end Parent

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.common_weight_bound
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.kernelCost_le_pool
#print axioms HeckeSkeleton.Moments.EngineStep.parent_first_stage_pool_bound
