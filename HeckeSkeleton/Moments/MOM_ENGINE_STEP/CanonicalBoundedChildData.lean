import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalCoreProfileIdentification
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalChildFourierControl

/-!
# Actual child data with the original bounded profiles

The original parent profile is evaluated at its actual source anchor and
height, before the residual row and both Fourier variables. Its value at
the physical norm argument is unchanged. The retained slots are literal
original occurrences, and the arithmetic child is the already proved
complete quotient row with the full moving prefix and deletion mask.

The bounded Gauss compensation is then installed as a profile update.
Both its original finite seminorm window and its arithmetic dictionary
are constructed here. Neither a transformed profile window nor a
completed child calibration is supplied.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalBoundedChildData

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open CanonicalLogProfiles OriginalGaussProfileCompensation
open OriginalClippedGaussProfiles CanonicalSecondFactorAssembly

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

/-- Freeze only the original evaluation arguments. The ideal support
continues to use the original physical norm scale. -/
def originalIdealTest (W : IdealTest K) (anchor : HeckeGeneral.Analysis.NonzeroIdeal K) (height : ℝ) : IdealTest K where
  profile _ _ y := W.profile anchor height y
  support _ _ N := W.support anchor height N
  support_spec _ _ N I := W.support_spec anchor height N I

/-- A retained original occurrence keeps its original length. -/
def originalPrimeWindow (W : PrimeWindow K) (height : ℝ) : PrimeWindow K where
  length := W.length
  length_pos := W.length_pos
  profile _ y := W.profile height y
  support _ N := W.support height N
  support_spec _ N p := W.support_spec height N p

def originalGeometry (parent : MomentData K ω ψ) {k : ℕ}
    (index : Fin k → Fin parent.geometry.slotCount) (height : ℝ) : SlotGeometry K where
  slotCount := k
  slots i := originalPrimeWindow (parent.geometry.slots (index i)) height

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (parent : MomentData K ω ψ)
variable (prefix : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
variable (hcorr : correction = 1 ∨ correction ∈ parent.theta)
variable (C : A.GeneralArithmeticContext σ η hS) (primes : ι → ExteriorPrime A)
variable (m n : ι → ℕ) (pattern : ι → Bool)
variable (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (budget : ℝ)
variable (anchor : HeckeGeneral.Analysis.NonzeroIdeal K) (height : ℝ) {k : ℕ}
variable (index : Fin k → Fin parent.geometry.slotCount)

/-- The child arithmetic is computed from the original source factors.
Every profile is an actual original profile at the source evaluation. -/
def baseData : MomentData K ω ψ :=
  CanonicalMovingPhaseCalibration.childData P R parent prefix correction hcorr
    C primes m n pattern sector remaining budget
    (originalIdealTest parent.inverseTest anchor height)
    (originalIdealTest parent.plainTest₁ anchor height)
    (originalIdealTest parent.plainTest₂ anchor height)
    (originalGeometry parent index height) index

local notation "base" => baseData parent prefix correction hcorr C primes m n pattern sector
  remaining budget anchor height index

@[simp] theorem baseData_count : base.geometry.slotCount = k := rfl
@[simp] theorem baseData_length (i : Fin k) :
    (base.geometry.slots i).length = (parent.geometry.slots (index i)).length := rfl
@[simp] theorem baseData_left (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t y : ℝ) :
    base.plainTest₁.profile u t y = parent.plainTest₁.profile anchor height y := rfl
@[simp] theorem baseData_right (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t y : ℝ) :
    base.plainTest₂.profile u t y = parent.plainTest₂.profile anchor height y := rfl
@[simp] theorem baseData_prime (i : Fin k) (t y : ℝ) :
    (base.geometry.slots i).profile t y =
      (parent.geometry.slots (index i)).profile height y := rfl

section OriginalWindow

variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)} {P₀ : ℝ}
variable (raw : RawProfileWindow rowDomain heightDomain window orders parent P₀)
variable (hanchor : anchor ∈ rowDomain) (hheight : height ∈ heightDomain)

/-- The original window is transported by literal evaluation and slot
selection. Its coefficient remains the original seminorm coefficient. -/
def baseRawWindow : RawProfileWindow Set.univ Set.univ window orders base P₀ where
  inverseRep _ _ := raw.inverseRep anchor height
  leftRep _ _ := raw.leftRep anchor height
  rightRep _ _ := raw.rightRep anchor height
  primeRep i _ := raw.primeRep (index i) height
  inverse_eq _ _ y := raw.inverse_eq anchor height y
  left_eq _ _ y := raw.left_eq anchor height y
  right_eq _ _ y := raw.right_eq anchor height y
  prime_eq i _ y := raw.prime_eq (index i) height y
  inverse_support _ _ _ _ := raw.inverse_support anchor hanchor height hheight
  left_support _ _ _ _ := raw.left_support anchor hanchor height hheight
  right_support _ _ _ _ := raw.right_support anchor hanchor height hheight
  prime_support i _ _ := raw.prime_support (index i) height hheight
  inverse_bound _ _ _ _ := raw.inverse_bound anchor hanchor height hheight
  left_bound _ _ _ _ := raw.left_bound anchor hanchor height hheight
  right_bound _ _ _ _ := raw.right_bound anchor hanchor height hheight
  prime_bound i _ _ := raw.prime_bound (index i) height hheight

variable (hpositive : window ⊆ Set.Ioi 0)

include raw hanchor hheight hpositive in
theorem base_left_positive : PositivePlainProfile base.plainTest₁ := by
  intro u t y hy
  change parent.plainTest₁.profile anchor height y ≠ 0 at hy
  rw [raw.left_eq] at hy
  exact hpositive (raw.left_support anchor hanchor height hheight hy)

include raw hanchor hheight hpositive in
theorem base_right_positive : PositivePlainProfile base.plainTest₂ := by
  intro u t y hy
  change parent.plainTest₂.profile anchor height y ≠ 0 at hy
  rw [raw.right_eq] at hy
  exact hpositive (raw.right_support anchor hanchor height hheight hy)

include raw hanchor hheight hpositive in
theorem base_prime_positive (i : Fin k) : PositivePrimeProfile (base.geometry.slots i) := by
  intro t y hy
  change (parent.geometry.slots (index i)).profile height y ≠ 0 at hy
  rw [raw.prime_eq] at hy
  exact hpositive (raw.prime_support (index i) height hheight hy)

end OriginalWindow

section BoundedProfiles

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)} {P₀ : ℝ}
variable (raw : RawProfileWindow rowDomain heightDomain window orders parent P₀)
variable (hanchor : anchor ∈ rowDomain) (hheight : height ∈ heightDomain)
variable (hpositive : window ⊆ Set.Ioi 0)
variable (G₁ G₂ : ℝ) (G : Fin k → ℝ) (D₁ D₂ : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (B δ₁ δ₂ : ℝ) (hG₁ : 0 < G₁) (hG₂ : 0 < G₂)
variable (hG : ∀ i, 0 < G i) (hB : 1 ≤ B)
variable (firstDirection secondDirection : V)

local notation "hleft" => base_left_positive parent prefix correction hcorr C primes m n
  pattern sector remaining budget anchor height index raw hanchor hheight hpositive
local notation "hright" => base_right_positive parent prefix correction hcorr C primes m n
  pattern sector remaining budget anchor height index raw hanchor hheight hpositive
local notation "hslot" => base_prime_positive parent prefix correction hcorr C primes m n
  pattern sector remaining budget anchor height index raw hanchor hheight hpositive
local notation "scalars" => profileScalars base G₁ G₂ G D₁ D₂ B δ₁ δ₂ hG₁ hG₂ hG hB
local notation "leftAtom" => atom G₁ (idealNorm K D₁) δ₁ δ₂ firstDirection secondDirection
local notation "rightAtom" => atom G₂ (idealNorm K D₂) δ₁ δ₂ firstDirection secondDirection
local notation "slotAtom" => fun i => atom (G i) 1 δ₁ δ₂ firstDirection secondDirection

def boundedData (ξ : V) : MomentData K ω ψ :=
  clippedData base G₁ G₂ G D₁ D₂ B δ₁ δ₂ hG₁ hG₂ hG hB
    hleft hright hslot firstDirection secondDirection ξ

local notation "bounded" => boundedData parent prefix correction hcorr C primes m n pattern sector
  remaining budget anchor height index raw hanchor hheight hpositive
  G₁ G₂ G D₁ D₂ B δ₁ δ₂ hG₁ hG₂ hG hB firstDirection secondDirection

@[simp] theorem boundedData_left (ξ : V) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t y : ℝ) :
    (bounded ξ).plainTest₁.profile u t y =
      ((scalars.left : ℂ) * parent.plainTest₁.profile anchor height y) *
        leftAtom.multiplier ξ y := rfl

@[simp] theorem boundedData_right (ξ : V) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t y : ℝ) :
    (bounded ξ).plainTest₂.profile u t y =
      ((scalars.right : ℂ) * parent.plainTest₂.profile anchor height y) *
        rightAtom.multiplier ξ y := rfl

@[simp] theorem boundedData_prime (ξ : V) (i : Fin k) (t y : ℝ) :
    ((bounded ξ).geometry.slots i).profile t y =
      ((scalars.prime i : ℂ) * (parent.geometry.slots (index i)).profile height y) *
        (slotAtom i).multiplier ξ y := rfl

/-- The finite Fourier-control package is the literal data used here.
Its base profiles and its slot occurrences are already constructed. -/
def originalLogProfiles : CanonicalLogProfiles.OriginalLogProfiles K ω ψ V where
  original := scalars.data base
  left := leftAtom
  right := rightAtom
  slot := slotAtom
  left_positive := scalars.left_positive base hleft
  right_positive := scalars.right_positive base hright
  slot_positive := scalars.prime_positive base hslot

theorem boundedData_eq_originalLogProfiles (ξ : V) :
    bounded ξ =
      (originalLogProfiles parent prefix correction hcorr C primes m n pattern sector
        remaining budget anchor height index raw hanchor hheight hpositive
        G₁ G₂ G D₁ D₂ B δ₁ δ₂ hG₁ hG₂ hG hB firstDirection secondDirection).moving ξ := rfl

/-- The bounded update changes only the original profiles. It is the
same complete arithmetic child for every value of both Fourier modes. -/
theorem boundedData_eq_childData (ξ : V) :
    bounded ξ = CanonicalMovingPhaseCalibration.childData P R parent prefix correction hcorr
      C primes m n pattern sector remaining budget
      (bounded ξ).inverseTest (bounded ξ).plainTest₁ (bounded ξ).plainTest₂
      (bounded ξ).geometry index := rfl

def movingRecipe : CompleteMovingRowRecipe A P R bounded :=
  CanonicalMovingPhaseCalibration.movingRecipe P R parent prefix correction hcorr
    C primes m n pattern sector remaining budget
    (fun ξ => (bounded ξ).inverseTest) (fun ξ => (bounded ξ).plainTest₁)
    (fun ξ => (bounded ξ).plainTest₂) (fun ξ => (bounded ξ).geometry) (fun _ => index)

theorem movingRecipe_fullJointBudget (Z width : ℝ) (hbudget : budget = Z ^ width) :
    (movingRecipe parent prefix correction hcorr C primes m n pattern sector
      remaining budget anchor height index raw hanchor hheight hpositive
      G₁ G₂ G D₁ D₂ B δ₁ δ₂ hG₁ hG₂ hG hB firstDirection secondDirection).FullJointBudget Z width := by
  intro ξ u hu
  exact hu.2.trans_eq hbudget

variable {Ih : A.Exterior} {h g : A.R} {factor : ℝ}

/-- The actual arithmetic dictionary is proved on every row of its
fixed pattern and unit sector. There is no carrier-only premise. -/
def calibration
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (row : ActualChildRow Ih h g factor)
    (hfactor : g = secondSixthRootGenerator C primes m n ^ 6 *
      secondActiveFrequencyGenerator C primes m n pattern)
    (hsector : row.sector P = sector) (ξ : V) :
    (movingSourceCharacters parent correction prefix remaining index).Calibration (σ := σ)
      (bounded ξ) rfl row.momentIdeal g row.element :=
  CanonicalMovingPhaseCalibration.calibration P R parent prefix correction hcorr
    C primes m n pattern sector remaining budget
    (bounded ξ).inverseTest (bounded ξ).plainTest₁ (bounded ξ).plainTest₂
    (bounded ξ).geometry index hone hroot hemb row hfactor hsector

def negativeCalibration
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (row : ActualChildRow Ih h g factor)
    (hfactor : g = secondSixthRootGenerator C primes m n ^ 6 *
      secondActiveFrequencyGenerator C primes m n pattern)
    (hsector : row.sector P = sector) (ξ : V) :
    (movingSourceCharacters parent correction prefix remaining index).Calibration (σ := σ)
      (bounded ξ) rfl row.momentIdeal (-g) row.element :=
  CanonicalMovingPhaseCalibration.negativeCalibration P R parent prefix correction hcorr
    C primes m n pattern sector remaining budget
    (bounded ξ).inverseTest (bounded ξ).plainTest₁ (bounded ξ).plainTest₂
    (bounded ξ).geometry index hone hroot hemb row hfactor hsector

section ActualProfileValues

open CanonicalCoreProfileIdentification

variable (W : NormProfileRecipe (fun _ : PUnit => parent))
variable (hallowed : parent.allowedRow anchor) (hwindow : window ⊆ Set.Iic B)
variable (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ : δ₁ + δ₂ ≤ 1 / 2)
variable (slope secondSlope : ℝ)

local notation "actualData" => boundedData parent prefix correction hcorr C primes m n pattern sector
  remaining budget anchor height index raw hanchor hheight hpositive
  G₁ G₂ G D₁ D₂ B δ₁ δ₂ hG₁ hG₂ hG hB
  (CanonicalCoreProfileIdentification.firstDirection slope)
  (CanonicalCoreProfileIdentification.secondDirection secondSlope)

/-- The actual left field from the original core dictionary calibrates
to this very child data. The only scale identity is the literal two
original norm divisions, before the later allocated divisor. -/
include hallowed hwindow hδ₁ hδ₂ hδ in
theorem left_profile
    (N : ℝ) (hN : 0 < N) (firstDivisor allocatedDivisor I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hscale : G₁ = N / idealNorm K firstDivisor / idealNorm K D₁)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t ξ ζ : ℝ) :
    rawPlainWeight (W.left PUnit.unit height) N firstDivisor D₁ δ₁ δ₂ 0 slope
        (allocatedDivisor * I) *
        jointPhase (WithLp.toLp 2 (ξ, ζ))
          (Real.log (idealNorm K (D₁ * (allocatedDivisor * I))) •
              CanonicalCoreProfileIdentification.firstDirection slope +
            Real.log (idealNorm K (allocatedDivisor * I)) •
              CanonicalCoreProfileIdentification.secondDirection secondSlope) =
      (actualData (WithLp.toLp 2 (ξ, ζ))).plainTest₁.profile u t
        (idealNorm K I / (G₁ / idealNorm K allocatedDivisor)) := by
  rw [boundedData_left, W.left_eq PUnit.unit anchor hallowed height]
  change _ = ((clippedScalar G₁ (idealNorm K D₁) B δ₁ δ₂ : ℂ) *
    W.left PUnit.unit height (idealNorm K I / (G₁ / idealNorm K allocatedDivisor))) *
      (atom G₁ (idealNorm K D₁) δ₁ δ₂
        (CanonicalCoreProfileIdentification.firstDirection slope)
        (CanonicalCoreProfileIdentification.secondDirection secondSlope)).multiplier
        (WithLp.toLp 2 (ξ, ζ)) (idealNorm K I / (G₁ / idealNorm K allocatedDivisor))
  rw [hscale]
  exact rawPlainWeight_allocated_joint_clipped (W.left PUnit.unit height) N hN
    firstDivisor D₁ allocatedDivisor I B δ₁ δ₂ ξ ζ slope secondSlope hB hδ₁ hδ₂ hδ
    (normRecipe_left_annulus parent W raw hwindow anchor hallowed hanchor height hheight)

include hallowed hwindow hδ₁ hδ₂ hδ in
theorem right_profile
    (N : ℝ) (hN : 0 < N) (firstDivisor allocatedDivisor I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hscale : G₂ = N / idealNorm K firstDivisor / idealNorm K D₂)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t ξ ζ : ℝ) :
    rawPlainWeight (W.right PUnit.unit height) N firstDivisor D₂ δ₁ δ₂ 0 slope
        (allocatedDivisor * I) *
        jointPhase (WithLp.toLp 2 (ξ, ζ))
          (Real.log (idealNorm K (D₂ * (allocatedDivisor * I))) •
              CanonicalCoreProfileIdentification.firstDirection slope +
            Real.log (idealNorm K (allocatedDivisor * I)) •
              CanonicalCoreProfileIdentification.secondDirection secondSlope) =
      (actualData (WithLp.toLp 2 (ξ, ζ))).plainTest₂.profile u t
        (idealNorm K I / (G₂ / idealNorm K allocatedDivisor)) := by
  rw [boundedData_right, W.right_eq PUnit.unit anchor hallowed height]
  change _ = ((clippedScalar G₂ (idealNorm K D₂) B δ₁ δ₂ : ℂ) *
    W.right PUnit.unit height (idealNorm K I / (G₂ / idealNorm K allocatedDivisor))) *
      (atom G₂ (idealNorm K D₂) δ₁ δ₂
        (CanonicalCoreProfileIdentification.firstDirection slope)
        (CanonicalCoreProfileIdentification.secondDirection secondSlope)).multiplier
        (WithLp.toLp 2 (ξ, ζ)) (idealNorm K I / (G₂ / idealNorm K allocatedDivisor))
  rw [hscale]
  exact rawPlainWeight_allocated_joint_clipped (W.right PUnit.unit height) N hN
    firstDivisor D₂ allocatedDivisor I B δ₁ δ₂ ξ ζ slope secondSlope hB hδ₁ hδ₂ hδ
    (normRecipe_right_annulus parent W raw hwindow anchor hallowed hanchor height hheight)

include hwindow hδ₁ hδ₂ hδ in
theorem prime_profile (i : Fin k) (q : HeightOneSpectrum (𝓞 K)) (t ξ ζ : ℝ) :
    rawPrimeWeight ((parent.geometry.slots (index i)).profile height) (G i)
        δ₁ δ₂ 0 slope q *
        jointPhase (WithLp.toLp 2 (ξ, ζ))
          (Real.log (Ideal.absNorm q.asIdeal : ℝ) •
              CanonicalCoreProfileIdentification.firstDirection slope +
            Real.log (Ideal.absNorm q.asIdeal : ℝ) •
              CanonicalCoreProfileIdentification.secondDirection secondSlope) =
      ((actualData (WithLp.toLp 2 (ξ, ζ))).geometry.slots i).profile t
        ((Ideal.absNorm q.asIdeal : ℝ) / G i) := by
  rw [boundedData_prime]
  apply rawPrimeWeight_joint_clipped ((parent.geometry.slots (index i)).profile height)
    (G i) (hG i) q B δ₁ δ₂ ξ ζ slope secondSlope hB hδ₁ hδ₂ hδ
  intro y hy
  apply hwindow
  apply raw.prime_support (index i) height hheight
  simpa only [raw.prime_eq] using hy

end ActualProfileValues

end BoundedProfiles

section UniformWindow

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable (orders : Finset (ℕ × ℕ)) (P₀ : ℝ)
variable (raw : RawProfileWindow rowDomain heightDomain window
  (sourceOrders orders) parent P₀)
variable (hanchor : anchor ∈ rowDomain) (hheight : height ∈ heightDomain)
variable (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
variable (G₁ G₂ : ℝ) (G : Fin k → ℝ) (D₁ D₂ : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (B δ₁ δ₂ : ℝ) (hG₁ : 0 < G₁) (hG₂ : 0 < G₂)
variable (hG : ∀ i, 0 < G i) (hB : 1 ≤ B)
variable (firstDirection secondDirection : V)

/-- Actual retained occurrences cannot exceed the original slot cap. -/
theorem count_le_original (hindex : Function.Injective index) :
    k ≤ parent.geometry.slotCount := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective index hindex

/-- This is the actual bounded child's finite seminorm window. All
support and coefficient facts are obtained from the original window at
the actual source anchor and height. The constant has no moving scale,
common ideal, row, label, or Fourier-parameter dependence. -/
def uniformWindow (δ : ℝ) (R₀ j cap : ℕ)
    (hP : 0 ≤ P₀) (hindex : Function.Injective index)
    (hcap : parent.geometry.slotCount ≤ cap)
    (hj : j ≤ R₀) (hexponent : δ₁ + δ₂ = (j : ℝ) * δ) (ξ : V) :
    RawProfileWindow Set.univ Set.univ window orders
      (boundedData parent prefix correction hcorr C primes m n pattern sector
        remaining budget anchor height index raw hanchor hheight hpositive
        G₁ G₂ G D₁ D₂ B δ₁ δ₂ hG₁ hG₂ hG hB firstDirection secondDirection ξ)
      (signedAmplitudeConstant window hcompact hpositive orders δ R₀ cap
          (‖firstDirection‖ + ‖secondDirection‖) *
        Real.sqrt B * P₀ * (1 + ‖ξ‖) ^ (orders.sup Prod.snd)) := by
  let w := baseRawWindow parent prefix correction hcorr C primes m n pattern sector
    remaining budget anchor height index raw hanchor hheight
  exact OriginalClippedGaussProfiles.rawWindow base G₁ G₂ G D₁ D₂ B δ₁ δ₂
    hG₁ hG₂ hG hB
    (base_left_positive parent prefix correction hcorr C primes m n pattern sector
      remaining budget anchor height index raw hanchor hheight hpositive)
    (base_right_positive parent prefix correction hcorr C primes m n pattern sector
      remaining budget anchor height index raw hanchor hheight hpositive)
    (base_prime_positive parent prefix correction hcorr C primes m n pattern sector
      remaining budget anchor height index raw hanchor hheight hpositive)
    firstDirection secondDirection hcompact hpositive orders δ R₀ j cap P₀ hP
    ((count_le_original parent index hindex).trans hcap) hj hexponent w
    (fun _ _ => closure_minimal
      (raw.left_support anchor hanchor height hheight) hcompact.isClosed)
    (fun _ _ => closure_minimal
      (raw.right_support anchor hanchor height hheight) hcompact.isClosed)
    (fun i _ => closure_minimal
      (raw.prime_support (index i) height hheight) hcompact.isClosed) ξ

end UniformWindow

end HeckeSkeleton.Moments.EngineStep.CanonicalBoundedChildData

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalBoundedChildData.baseRawWindow
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalBoundedChildData.boundedData_eq_originalLogProfiles
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalBoundedChildData.calibration
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalBoundedChildData.negativeCalibration
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalBoundedChildData.left_profile
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalBoundedChildData.prime_profile
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalBoundedChildData.uniformWindow
