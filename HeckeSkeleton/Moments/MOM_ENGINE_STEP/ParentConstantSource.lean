import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentRawSourceInput
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GaussEnergySource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GaussStagePhaseTransport

/-!
# Constructing the mixed source for fixed original profile columns

The individual arithmetic dictionaries separate actual Hecke values and
their complete masks from the orbit phases.  The original plain norm
profiles are independent of the orbit; this includes the literal fixed
annular power profiles.  Their scalar coefficients, both comparison
rectangles and every slot are computed before the orbital variable.

A single original positive orbital test then constructs every mixed
pair profile by scalar multiplication.  Its Gram identities are proved,
including the whole centered difference.  The first transformed chart
also transports these individual scalars through the actual Fourier and
orbital operations, so its Schwartz kernel is unchanged.

This constructor does not infer orbit independence from a rowwise
seminorm bound.  A genuinely row-dependent original test still needs
the more general primitive mixed-profile construction.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis MeasureTheory

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

namespace ParentRawAtoms

variable {Q : Type*} {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable (raw : ParentRawAtoms Q d a Z t Y₁ Y₂)

/-- Constancy is specified on individual atoms, before any product or
centering.  In particular it is not a whole-polynomial hypothesis. -/
structure ConstantValues where
  left : Bool → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ
  right : Bool → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ
  prime : Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 K) → ℂ
  left_eq : ∀ comparison q I, raw.leftCoefficient comparison q I = left comparison I
  right_eq : ∀ comparison q I, raw.rightCoefficient comparison q I = right comparison I
  prime_eq : ∀ q i p, raw.primeCoefficient q i p = prime i p

namespace ConstantValues

variable {raw} (values : raw.ConstantValues)

def rectangle (comparison : Bool) (i : raw.Column) : ℂ :=
  values.left comparison i.1.1 * values.right comparison i.1.2 *
    ∏ j, values.prime j (i.2 j)

def coefficient (centered : Bool) (i : raw.Column) : ℂ :=
  values.rectangle false i - if centered then values.rectangle true i else 0

theorem rectangle_eq (comparison : Bool) (q : Q) (i : raw.Column) :
    raw.rectangleCoefficient comparison q i = values.rectangle comparison i := by
  simp only [rectangleCoefficient, rectangle, values.left_eq, values.right_eq, values.prime_eq]

theorem coefficient_eq (centered : Bool) (q : Q) (i : raw.Column) :
    raw.coefficient centered q i = values.coefficient centered i := by
  rw [raw.coefficient_eq_rectangles, values.rectangle_eq, values.rectangle_eq]
  rfl

end ConstantValues
end ParentRawAtoms

/-- Original one-ideal/one-prime arithmetic identities and literal norm
profiles.  No Fourier profile or aggregate estimate is a field.  The
same record works at every pair of comparison scales. -/
structure ParentConstantAtoms (Q : Type*) (d : MomentData K ω ψ)
    (a : RealParameters) (Z t : ℝ) where
  rowMap : HeckeGeneral.Analysis.NonzeroIdeal K → Q
  leftArithmetic : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ
  rightArithmetic : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ
  primeArithmetic : Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 K) → ℂ
  leftPhase : Q → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ
  rightPhase : Q → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ
  primePhase : Q → Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 K) → ℂ
  leftProfile : ℝ → ℂ
  rightProfile : ℝ → ℂ
  left_arithmetic : ∀ u ∈ pairedRows d a Z, ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K,
    heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I * maskValue d u I.val =
      leftArithmetic I * leftPhase (rowMap u) I
  right_arithmetic : ∀ u ∈ pairedRows d a Z, ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K,
    heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I * maskValue d u I.val =
      rightArithmetic I * rightPhase (rowMap u) I
  prime_arithmetic : ∀ u ∈ pairedRows d a Z, ∀ i p,
    primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p * maskValue d u p.asIdeal =
      primeArithmetic i p * primePhase (rowMap u) i p
  left_profile : ∀ u ∈ pairedRows d a Z, ∀ y, d.plainTest₁.profile u t y = leftProfile y
  right_profile : ∀ u ∈ pairedRows d a Z, ∀ y, d.plainTest₂.profile u t y = rightProfile y

namespace ParentConstantAtoms

variable {Q : Type*} {d : MomentData K ω ψ} {a : RealParameters} {Z t : ℝ}
variable (atoms : ParentConstantAtoms Q d a Z t)

def leftValue (N : ℝ) (I : HeckeGeneral.Analysis.NonzeroIdeal K) : ℂ :=
  (Real.sqrt N : ℂ)⁻¹ * (atoms.leftArithmetic I * atoms.leftProfile (idealNorm K I / N))

def rightValue (N : ℝ) (I : HeckeGeneral.Analysis.NonzeroIdeal K) : ℂ :=
  (Real.sqrt N : ℂ)⁻¹ * (atoms.rightArithmetic I * atoms.rightProfile (idealNorm K I / N))

def primeValue (i : Fin d.geometry.slotCount) (p : HeightOneSpectrum (𝓞 K)) : ℂ :=
  (Real.sqrt (Z ^ (d.geometry.slots i).length) : ℂ)⁻¹ *
    (atoms.primeArithmetic i p * (d.geometry.slots i).profile t
      ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length))

/-- The whole centered coefficient is computed from the original
characters, masks, profiles and all four actual scales. -/
def raw (Y₁ Y₂ : ℝ) : ParentRawAtoms Q d a Z t Y₁ Y₂ where
  rowMap := atoms.rowMap
  leftCoefficient comparison _ := atoms.leftValue (if comparison then Y₁ else Z ^ a.n₁)
  rightCoefficient comparison _ := atoms.rightValue (if comparison then Y₂ else Z ^ a.n₂)
  primeCoefficient _ := atoms.primeValue
  leftPhase := atoms.leftPhase
  rightPhase := atoms.rightPhase
  primePhase := atoms.primePhase
  left comparison u hu I := by
    dsimp only [parentPlainAtom, leftValue]
    rw [atoms.left_profile u hu]
    have h := atoms.left_arithmetic u hu I
    calc
      _ = (Real.sqrt (if comparison then Y₁ else Z ^ a.n₁) : ℂ)⁻¹ *
          ((heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I * maskValue d u I.val) *
            atoms.leftProfile (idealNorm K I / (if comparison then Y₁ else Z ^ a.n₁))) := by ring
      _ = _ := by rw [h]; ring
  right comparison u hu I := by
    dsimp only [parentPlainAtom, rightValue]
    rw [atoms.right_profile u hu]
    have h := atoms.right_arithmetic u hu I
    calc
      _ = (Real.sqrt (if comparison then Y₂ else Z ^ a.n₂) : ℂ)⁻¹ *
          ((heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I * maskValue d u I.val) *
            atoms.rightProfile (idealNorm K I / (if comparison then Y₂ else Z ^ a.n₂))) := by ring
      _ = _ := by rw [h]; ring
  prime u hu i p := by
    dsimp only [parentPrimeAtom, primeValue]
    have h := atoms.prime_arithmetic u hu i p
    calc
      _ = (Real.sqrt (Z ^ (d.geometry.slots i).length) : ℂ)⁻¹ *
          ((primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p * maskValue d u p.asIdeal) *
            (d.geometry.slots i).profile t
              ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length)) := by ring
      _ = _ := by rw [h]; ring

def values (Y₁ Y₂ : ℝ) : (atoms.raw Y₁ Y₂).ConstantValues where
  left comparison := atoms.leftValue (if comparison then Y₁ else Z ^ a.n₁)
  right comparison := atoms.rightValue (if comparison then Y₂ else Z ^ a.n₂)
  prime := atoms.primeValue
  left_eq _ _ _ := rfl
  right_eq _ _ _ := rfl
  prime_eq _ _ _ := rfl

/-- Replacing either original plain by a fixed annular power test only
changes these two literal norm profiles.  All arithmetic dictionaries,
rows, phases and slots are retained.  The caller supplies the two actual
profile identities, which are definitional for the power-window tests. -/
def withPlainTests (W₁ W₂ : IdealTest K) (f₁ f₂ : ℝ → ℂ)
    (hW₁ : ∀ u ∈ pairedRows d a Z, ∀ y, W₁.profile u t y = f₁ y)
    (hW₂ : ∀ u ∈ pairedRows d a Z, ∀ y, W₂.profile u t y = f₂ y) :
    ParentConstantAtoms Q { d with plainTest₁ := W₁, plainTest₂ := W₂ } a Z t where
  rowMap := atoms.rowMap
  leftArithmetic := atoms.leftArithmetic
  rightArithmetic := atoms.rightArithmetic
  primeArithmetic := atoms.primeArithmetic
  leftPhase := atoms.leftPhase
  rightPhase := atoms.rightPhase
  primePhase := atoms.primePhase
  leftProfile := f₁
  rightProfile := f₂
  left_arithmetic := atoms.left_arithmetic
  right_arithmetic := atoms.right_arithmetic
  prime_arithmetic := atoms.prime_arithmetic
  left_profile := hW₁
  right_profile := hW₂

end ParentConstantAtoms

section CommonProfile

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)} [Γ.FiniteIndex]
local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable {raw : ParentRawAtoms Q d a Z t Y₁ Y₂}
variable (values : raw.ConstantValues)
variable {φ : SchwartzMap V ℂ}
variable {finiteTest : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ}
variable {radius : {r : ℝ // 0 < r}} {mask : Finset (HeightOneSpectrum OS)} {fiberBound : ℕ}
variable (chart : GaussEnergyChart (pairedRows d a Z) raw.rowMap (fun _ => 1)
  φ finiteTest radius mask fiberBound)

/-- One original positive Haar profile supplies all four actual pair
profiles.  Their Gram identity is proved by the original integral's
scalar linearity, rather than supplied as a mixed-profile assumption. -/
def ParentRawAtoms.ConstantValues.rectangleProfiles :
    ParentRectangleProfiles raw finiteTest radius
      (fun q => (gaussSourceProfile φ finiteTest radius q).re) where
  profile comparison₁ comparison₂ i j :=
    (values.rectangle comparison₁ i * star (values.rectangle comparison₂ j)) • φ
  gram comparison₁ comparison₂ i _ j _ q := by
    rw [sUnitOrbitalProfile_tensor_smul, smul_eq_mul]
    change (values.rectangle comparison₁ i * star (values.rectangle comparison₂ j)) *
      gaussSourceProfile φ finiteTest radius q = _
    rw [chart.profile_eq_real q, values.rectangle_eq, values.rectangle_eq]
    ring

theorem ParentRawAtoms.ConstantValues.wholeProfile_eq (centered : Bool) (i j : raw.Column) :
    (values.rectangleProfiles chart).wholeProfile centered i j =
      (values.coefficient centered i * star (values.coefficient centered j)) • φ := by
  ext x
  cases centered <;>
    simp [ParentRectangleProfiles.wholeProfile, ParentRawAtoms.ConstantValues.rectangleProfiles,
      ParentRawAtoms.ConstantValues.coefficient, star_sub, smul_eq_mul] <;> ring

/-- This constructs the original full source from one actual positive
row test and the individual periodic phase dictionary.  In particular
neither the original Gram identity nor its centered version is an input. -/
def ParentRawAtoms.ConstantValues.toRawOrbitalInput
    (hTest : Continuous finiteTest) (hTestcs : HasCompactSupport finiteTest)
    (centered : Bool) (template : raw.Column → raw.Column → ParentPeriodicPair K S Γ)
    (periodic : ∀ i ∈ raw.columns, ∀ j ∈ raw.columns, ∀ q,
      (template i j).orbitWeight q = raw.phase q i * star (raw.phase q j)) :
    ParentRawOrbitalInput S Γ centered raw
      ((values.rectangleProfiles chart).pairs centered template) finiteTest radius mask fiberBound :=
  (values.rectangleProfiles chart).toRawOrbitalInput hTest hTestcs centered template mask fiberBound
    chart.profile_nonneg chart.row_weight chart.row_mask chart.fiber periodic

/-- The original multiplicative character descends through the actual
subgroup.  This is before either Gauss transform. -/
def OrbitalGaussColumn.originalOrbit (c : OrbitalGaussColumn K S Γ) : Q → ℂ :=
  sIntegerPeriodicOrbitWeight K (S : Set (HeightOneSpectrum (𝓞 K))) Γ c.modulus c.character
    (fun u x => by simp only [map_mul, c.invariant, one_mul])

@[simp] theorem OrbitalGaussColumn.originalOrbit_mk (c : OrbitalGaussColumn K S Γ)
    (x : NonzeroRingElements OS) :
    c.originalOrbit (Quotient.mk _ x) = c.character (Ideal.Quotient.mk _ x.val) := rfl

theorem OrbitalGaussColumn.originalPair_orbitWeight
    (c e : OrbitalGaussColumn K S Γ) (φ : SchwartzMap V ℂ) (q : Q) :
    (c.originalPair e φ).orbitWeight q = c.originalOrbit q * star (e.originalOrbit q) := by
  refine Quotient.inductionOn q ?_
  intro x
  simp only [OrbitalGaussColumn.originalPair_orbit_mk, OrbitalGaussColumn.originalOrbit_mk]

/-- The literal generated character columns give the periodic identity
internally.  The only character dictionary is for one complete ideal;
the complete Gram profile and parent expansion are both constructed. -/
def ParentRawAtoms.ConstantValues.actualCalibration
    (hTest : Continuous finiteTest) (hTestcs : HasCompactSupport finiteTest)
    (centered : Bool) (col : raw.Column → OrbitalGaussColumn K S Γ)
    (phase : ∀ i ∈ raw.columns, ∀ q, raw.phase q i = (col i).originalOrbit q) :
    ParentSourceCalibration centered d a Z t Y₁ Y₂ raw.columns
      (fun i j => (col i).originalPair (col j)
        ((values.coefficient centered i * star (values.coefficient centered j)) • φ))
      finiteTest radius mask fiberBound := by
  let template := fun i j => (col i).originalPair (col j) φ
  have periodic : ∀ i ∈ raw.columns, ∀ j ∈ raw.columns, ∀ q,
      (template i j).orbitWeight q = raw.phase q i * star (raw.phase q j) := by
    intro i hi j hj q
    rw [phase i hi q, phase j hj q]
    exact (col i).originalPair_orbitWeight (col j) φ q
  let source := values.toRawOrbitalInput chart hTest hTestcs centered template periodic
  have hpairs : (values.rectangleProfiles chart).pairs centered template =
      fun i j => (col i).originalPair (col j)
        ((values.coefficient centered i * star (values.coefficient centered j)) • φ) := by
    funext i j
    change { template i j with profile := (values.rectangleProfiles chart).wholeProfile centered i j } = _
    rw [values.wholeProfile_eq chart centered i j]
    rfl
  rw [← hpairs]
  exact source.toCalibration

/-- The raw mixed profiles use exactly the seminorms of one original
test, with explicit individual coefficient factors. -/
theorem ParentRawAtoms.ConstantValues.pairProfile_seminorm
    (seminorms : Finset (ℕ × ℕ)) (centered : Bool) (i j : raw.Column) :
    seminorms.sup (schwartzSeminormFamily ℂ V ℂ)
        ((values.coefficient centered i * star (values.coefficient centered j)) • φ) =
      ‖values.coefficient centered i‖ * ‖values.coefficient centered j‖ *
        seminorms.sup (schwartzSeminormFamily ℂ V ℂ) φ := by
  rw [map_smul_eq_mul, norm_mul, norm_star]

end CommonProfile

section FirstTransform

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

/-- Actual trace Fourier and orbital linearity, with the same pair
modulus, dual radius and Poisson normalization. -/
theorem ParentPeriodicPair.transformedProfile_smul
    (p : ParentPeriodicPair K A.Sf Γ) (c : ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R)) (q : Q) :
    ({ p with profile := c • p.profile } : ParentPeriodicPair K A.Sf Γ).
        transformedProfile μv finiteTest radius D q =
      c * p.transformedProfile μv finiteTest radius D q := by
  unfold ParentPeriodicPair.transformedProfile
  dsimp only [ParentPeriodicPair.dualRadius]
  rw [engine_traceSchwartzFourier_smul, sUnitOrbitalProfile_tensor_smul, smul_eq_mul]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap V ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}

/-- All original constant column coefficients, including one whole
centered coefficient, are inserted into an actual first chart without
changing its Schwartz kernel or its orbital/column locations. -/
def FirstBlockProfileChart.withCoefficients
    (chart : FirstBlockProfileChart (E := E) hΓ μv b C left right profiles finiteTest radius D)
    (c : ι → ℂ) (e : κ → ℂ) :
    FirstBlockProfileChart (E := E) hΓ μv b C left right
      (fun i j => (c i * star (e j)) • profiles i j) finiteTest radius D where
  kernel := chart.kernel
  weight := chart.weight
  leftCoefficient i := c i * chart.leftCoefficient i
  rightCoefficient j := e j * chart.rightCoefficient j
  leftPoint := chart.leftPoint
  rightPoint := chart.rightPoint
  rowPoint := chart.rowPoint
  profile q i hi j hj hcop := by
    have he :
        ((generatedOriginalColumn (σ := σ) hΓ (b.leftResidual i) (b.leftGenerator i)
            (b.left_generates i)).originalTriple
          (generatedOriginalColumn (σ := σ) hΓ (b.rightResidual j) (b.rightGenerator j)
            (b.right_generates j))
          (actualActiveColumn hΓ C b.primes b.primes_injective
            b.leftMultiplicity b.rightMultiplicity)
          ((c i * star (e j)) • profiles i j)) =
        { (generatedOriginalColumn (σ := σ) hΓ (b.leftResidual i) (b.leftGenerator i)
            (b.left_generates i)).originalTriple
          (generatedOriginalColumn (σ := σ) hΓ (b.rightResidual j) (b.rightGenerator j)
            (b.right_generates j))
          (actualActiveColumn hΓ C b.primes b.primes_injective
            b.leftMultiplicity b.rightMultiplicity) (profiles i j) with
          profile := (c i * star (e j)) • profiles i j } := rfl
    rw [he, ParentPeriodicPair.transformedProfile_smul,
      chart.profile q i hi j hj hcop]
    simp only [star_mul]
    ring

theorem FirstBlockProfileChart.withCoefficients_kernel
    (chart : FirstBlockProfileChart (E := E) hΓ μv b C left right profiles finiteTest radius D)
    (c : ι → ℂ) (e : κ → ℂ) :
    (FirstBlockProfileChart.withCoefficients hΓ μv chart c e).kernel = chart.kernel := rfl

end FirstTransform
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.raw
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.ConstantValues.toRawOrbitalInput
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.ConstantValues.actualCalibration
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockProfileChart.withCoefficients
