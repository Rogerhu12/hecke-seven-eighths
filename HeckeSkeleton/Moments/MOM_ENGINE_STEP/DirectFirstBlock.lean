import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectFirstReduction

/-!
# The actual first block enters the direct Gauss family

All coefficients and row bounds come from the original first profile
chart and its actual common factor. The data do not contain a prime pool:
zero-slot input therefore needs no artificial positive pool witness.
The same original internal divisor and finite phase labels are retained.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open UniqueFactorizationMonoid
open HeckePort.Moments HeckePort.Moments.MobiusRegroup

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

variable {hΓ μv}
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}

/-- Primitive calibration of the original unamplified Gauss columns,
without a positive pool, density, or amplification parameter. -/
structure FirstBlockDirectData
    {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
    (chart : FirstBlockProfileChart (E := E) hΓ μv b C left right profiles finiteTest radius D)
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X) where
  leftData : DirectGaussData C ι
  rightData : DirectGaussData C κ
  left_columns : leftData.columns = b.leftColumns left
  right_columns : rightData.columns = b.rightColumns right
  left_ideal : leftData.ideal = b.leftResidual
  right_ideal : rightData.ideal = b.rightResidual
  left_generator : leftData.generator = b.leftGenerator
  right_generator : rightData.generator = b.rightGenerator
  left_rows : (((b.finiteSource hΓ C left right profiles M radius X hX).divisorRows D).image
    (fun t : Q => t.out.val)) ⊆ leftData.rows
  right_rows : (((b.finiteSource hΓ C left right profiles M radius X hX).divisorRows D).image
    (fun t : Q => -t.out.val)) ⊆ rightData.rows
  weightBound : ℝ
  weight_nonneg : 0 ≤ weightBound
  weight_bound : ∀ t ∈ ((b.finiteSource hΓ C left right profiles M radius X hX).divisorRows D),
    ‖chart.weight t‖ ≤ weightBound

namespace FirstBlockDirectData

variable {chart : FirstBlockProfileChart (E := E) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}

def rowBound (p : FirstBlockDirectData chart M X hX) : ℝ :=
  p.weightBound * Real.sqrt (A.exteriorNorm
    (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity))

theorem rowBound_nonneg (p : FirstBlockDirectData chart M X hX) : 0 ≤ p.rowBound :=
  mul_nonneg p.weight_nonneg (Real.sqrt_nonneg _)

/-- The genuine active factor, including its divisor character and
the original Moebius coefficient, is bounded internally. -/
theorem common_weight_bound (p : FirstBlockDirectData chart M X hX)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (t : Q) (ht : t ∈ ((b.finiteSource hΓ C left right profiles M radius X hX).divisorRows D)) :
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


local instance directFirstBlockCircleCharacterFintype : Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

def originalLeftCoefficient (p : FirstBlockDirectData chart M X hX) (i : ι) : ℂ :=
  let a := generatedOriginalColumn (σ := σ) hΓ
    (b.leftResidual i) (b.leftGenerator i) (b.left_generates i)
  let r := actualActiveColumn hΓ C b.primes b.primes_injective
    b.leftMultiplicity b.rightMultiplicity
  let δ := (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
  chart.leftCoefficient i * firstLeftDivisorFactor a r δ

def originalRightCoefficient (p : FirstBlockDirectData chart M X hX) (j : κ) : ℂ :=
  let a := generatedOriginalColumn (σ := σ) hΓ
    (b.rightResidual j) (b.rightGenerator j) (b.right_generates j)
  let r := actualActiveColumn hΓ C b.primes b.primes_injective
    b.leftMultiplicity b.rightMultiplicity
  let δ := (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
  chart.rightCoefficient j * firstRightDivisorFactor a r δ

def linearizedCost (p : FirstBlockDirectData chart M X hX)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit.{1} × PUnit.{1}) →* Circle) → ℝ) : ℝ :=
  firstDirectLinearizedCost PUnit.{1} chart.kernel p.leftData p.rightData hDiff
    (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (1 : Circle)) p.rowBound
    NL NR p.originalLeftCoefficient p.originalRightCoefficient chart.leftPoint chart.rightPoint

/-- The literal first source is bounded by direct original Gauss
energies under the original common Fourier measure. -/
theorem kernelCost_le_linearized (p : FirstBlockDirectData chart M X hX)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit.{1} × PUnit.{1}) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ) :
    chart.kernelCost hDiff M X hX ≤ p.linearizedCost hDiff NL NR := by
  let r := actualActiveColumn hΓ C b.primes b.primes_injective
    b.leftMultiplicity b.rightMultiplicity
  let δ := (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
  have he := first_residual_cost_le_direct_linearized (Ray := PUnit.{1}) (hΓ := hΓ)
    chart.kernel p.leftData p.rightData hDiff
    ((b.finiteSource hΓ C left right profiles M radius X hX).divisorRows D) (fun t : Q => t.out.val)
    sIntegerOrbit_out_val_injective.injOn p.left_rows p.right_rows
    (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (1 : Circle))
    (fun t : Q => (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
      (r.character (Ideal.Quotient.mk _ δ) *
        actualSIntegerGauss K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hDiff
          r.modulus r.nonzero r.character t.out.val))
    chart.weight p.rowBound p.rowBound_nonneg (fun t ht => p.common_weight_bound hDiff t ht)
    NL NR hNL hNR (fun i => p.originalLeftCoefficient i)
    (fun j => p.originalRightCoefficient j)
    chart.leftPoint chart.rightPoint
  simpa only [FirstBlockProfileChart.kernelCost, FirstCommonCharacterBlock.finiteSource,
    linearizedCost, originalLeftCoefficient, originalRightCoefficient, r, δ,
    p.left_columns, p.right_columns, p.left_ideal, p.right_ideal,
    p.left_generator, p.right_generator] using he

end FirstBlockDirectData

namespace FirstBlockPoolData

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {chart : FirstBlockProfileChart (E := E) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}

/-- The amplified input can forget its pool fields when using the
same direct entrance; this is not needed to construct a direct input. -/
def toDirect (p : FirstBlockPoolData chart P M X hX) : FirstBlockDirectData chart M X hX where
  leftData := p.leftData.originalData
  rightData := p.rightData.originalData
  left_columns := p.left_columns
  right_columns := p.right_columns
  left_ideal := p.left_ideal
  right_ideal := p.right_ideal
  left_generator := p.left_generator
  right_generator := p.right_generator
  left_rows := p.left_rows
  right_rows := p.right_rows
  weightBound := p.weightBound
  weight_nonneg := p.weight_nonneg
  weight_bound := p.weight_bound

end FirstBlockPoolData

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.common_weight_bound
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.kernelCost_le_linearized
