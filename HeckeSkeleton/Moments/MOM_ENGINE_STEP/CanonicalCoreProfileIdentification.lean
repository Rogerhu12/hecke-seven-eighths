import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActualSecondRectangles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActualPoolRectangles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalClippedGaussProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NestedHilbertPhase

/-!
# The computed core weights are the bounded original signed profiles

These identities expose the literal weights of the constructed second
rectangles. They combine the original first Fourier phase and the
original second phase in the Hilbert product, reconstruct the original
profile argument through both extractions, and apply the proved bounded
Gauss compensation. No transformed-profile identity is supplied.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalCoreProfileIdentification

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open CanonicalSecondFactorAssembly CanonicalActualSecondRectangles
open CanonicalEffectiveChildSupport OriginalGaussProfileCompensation
open OriginalClippedGaussProfiles

variable {K : Type} [Field K] [NumberField K]

def firstDirection (slope : ℝ) : WithLp 2 (ℝ × ℝ) := WithLp.toLp 2 (slope, 0)
def secondDirection (slope : ℝ) : WithLp 2 (ℝ × ℝ) := WithLp.toLp 2 (0, slope)

/-- The two original signs occur in separate coordinates. The second
sign is `-1` for a left source and `1` after the right source removes its
single whole conjugation. The first sign is left unchanged. -/
theorem phase_pair (slope secondSlope x y ξ ζ : ℝ) :
    jointPhase (WithLp.toLp 2 (ξ, ζ))
        (x • firstDirection slope + y • secondDirection secondSlope) =
      jointPhase ξ (slope * x) * jointPhase ζ (secondSlope * y) := by
  have he : x • firstDirection slope + y • secondDirection secondSlope =
      WithLp.toLp 2 (slope * x, secondSlope * y) := by
    apply (WithLp.ofLp_injective 2)
    change (x * slope + y * 0, x * 0 + y * secondSlope) =
      (slope * x, secondSlope * y)
    ext <;> ring
  rw [he, jointPhase_toLp_pair]

theorem normLogWeight_nonzero (exponent ξ slope : ℝ) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    normLogWeight exponent ξ slope I.val =
      ((idealNorm K I ^ exponent : ℝ) : ℂ) *
        jointPhase ξ (slope * Real.log (idealNorm K I)) := by
  simp only [normLogWeight, MonoidHom.mul_apply,
    CanonicalSecondRectangularFactors.normPower, logPhaseHom,
    MonoidHom.coe_mk, OneHom.coe_mk, if_neg (nonZeroDivisors.coe_ne_zero I)] <;> rfl

theorem normPower_nonzero (exponent : ℝ) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    CanonicalSecondRectangularFactors.normPower exponent I.val =
      ((idealNorm K I ^ exponent : ℝ) : ℂ) := rfl

private theorem norm_mul (D I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    idealNorm K (D * I) = idealNorm K D * idealNorm K I := by
  change (Ideal.absNorm (D.val * I.val) : ℝ) = _
  rw [map_mul, Nat.cast_mul] <;> rfl

/-- Both quotients reconstruct the same original profile argument. -/
theorem twice_quotient_norm_ratio (D₁ D₂ I : HeckeGeneral.Analysis.NonzeroIdeal K) (N : ℝ) :
    idealNorm K (D₁ * (D₂ * I)) / N =
      idealNorm K I / (N / idealNorm K D₁ / idealNorm K D₂) := by
  rw [quotient_norm_ratio D₂ I (N / idealNorm K D₁),
    quotient_norm_ratio D₁ (D₂ * I) N]

/-- This function is the literal field of the computed core table.
The earlier common norm remains inside the first inverse norm. -/
def rawPlainWeight (W : ℝ → ℂ) (N : ℝ) (D₁ D₂ : HeckeGeneral.Analysis.NonzeroIdeal K)
    (δ₁ δ₂ ξ slope : ℝ) (I : HeckeGeneral.Analysis.NonzeroIdeal K) : ℂ :=
  (Real.sqrt (N / idealNorm K D₁ / idealNorm K D₂) : ℂ) *
    ((W (idealNorm K (D₁ * (D₂ * I)) / N) *
        normLogWeight (δ₁ - 1) ξ slope (D₂ * I).val) *
      CanonicalSecondRectangularFactors.normPower δ₂ I.val)

/-- The actual twice-extracted plain profile, including both Fourier
phases, equals the bounded scale-one profile at every original ideal. -/
theorem rawPlainWeight_eq_clipped
    (W : ℝ → ℂ) (N : ℝ) (hN : 0 < N) (D₁ D₂ I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (B δ₁ δ₂ ξ ζ slope secondSlope : ℝ) (hB : 1 ≤ B)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (hW : ∀ y, W y ≠ 0 → y ≤ B) :
    rawPlainWeight W N D₁ D₂ δ₁ δ₂ ξ slope I *
        jointPhase ζ (secondSlope * Real.log (idealNorm K I)) =
      ((clippedScalar (N / idealNorm K D₁ / idealNorm K D₂)
          (idealNorm K D₂) B δ₁ δ₂ : ℂ) *
        W (idealNorm K I / (N / idealNorm K D₁ / idealNorm K D₂))) *
        (atom (N / idealNorm K D₁ / idealNorm K D₂) (idealNorm K D₂) δ₁ δ₂
          (firstDirection slope) (secondDirection secondSlope)).multiplier
          (WithLp.toLp 2 (ξ, ζ))
          (idealNorm K I / (N / idealNorm K D₁ / idealNorm K D₂)) := by
  have hG : 0 < N / idealNorm K D₁ / idealNorm K D₂ :=
    div_pos (div_pos hN (idealNorm_pos K D₁)) (idealNorm_pos K D₂)
  have hc := clipped_multiplier_identity
    (N / idealNorm K D₁ / idealNorm K D₂) (idealNorm K D₂) (idealNorm K I)
    B δ₁ δ₂ hG (one_le_idealNorm K D₂) (one_le_idealNorm K I) hB hδ₁ hδ₂ hδ W hW
    (firstDirection slope) (secondDirection secondSlope) (WithLp.toLp 2 (ξ, ζ))
  rw [phase_pair] at hc
  simp only [rawPlainWeight, normLogWeight_nonzero, normPower_nonzero,
    norm_mul D₂ I, twice_quotient_norm_ratio]
  convert hc using 1 <;> simp only [Complex.ofReal_mul] <;> ring

def rawPrimeWeight (W : ℝ → ℂ) (N δ₁ δ₂ ξ slope : ℝ)
    (p : HeightOneSpectrum (𝓞 K)) : ℂ :=
  (Real.sqrt N : ℂ) *
    ((W ((Ideal.absNorm p.asIdeal : ℝ) / N) * normLogWeight (δ₁ - 1) ξ slope p.asIdeal) *
      CanonicalSecondRectangularFactors.normPower δ₂ p.asIdeal)

theorem rawPrimeWeight_eq_clipped
    (W : ℝ → ℂ) (N : ℝ) (hN : 0 < N) (p : HeightOneSpectrum (𝓞 K))
    (B δ₁ δ₂ ξ ζ slope secondSlope : ℝ) (hB : 1 ≤ B)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (hW : ∀ y, W y ≠ 0 → y ≤ B) :
    rawPrimeWeight W N δ₁ δ₂ ξ slope p * jointPhase ζ (secondSlope * Real.log (Ideal.absNorm p.asIdeal : ℝ)) =
      ((clippedScalar N 1 B δ₁ δ₂ : ℂ) * W ((Ideal.absNorm p.asIdeal : ℝ) / N)) *
        (atom N 1 δ₁ δ₂ (firstDirection slope) (secondDirection secondSlope)).multiplier
          (WithLp.toLp 2 (ξ, ζ)) ((Ideal.absNorm p.asIdeal : ℝ) / N) := by
  let I : HeckeGeneral.Analysis.NonzeroIdeal K := ⟨p.asIdeal, mem_nonZeroDivisors_of_ne_zero p.ne_bot⟩
  have hc := clipped_multiplier_identity N 1 (idealNorm K I) B δ₁ δ₂ hN le_rfl
    (one_le_idealNorm K I) hB hδ₁ hδ₂ hδ W hW
    (firstDirection slope) (secondDirection secondSlope) (WithLp.toLp 2 (ξ, ζ))
  rw [phase_pair] at hc
  simp only [one_mul] at hc
  have hl := normLogWeight_nonzero (δ₁ - 1) ξ slope I
  have hp := normPower_nonzero δ₂ I
  change normLogWeight (δ₁ - 1) ξ slope p.asIdeal = _ at hl
  change CanonicalSecondRectangularFactors.normPower δ₂ p.asIdeal = _ at hp
  rw [rawPrimeWeight, hl, hp]
  convert hc using 1 <;> simp only [Complex.ofReal_mul] <;> ring

/-- The first Fourier mode can be moved to an original location before
any capacity child is selected. The remaining coefficient is fixed. -/
theorem rawPlainWeight_eq_zero_mul_phase
    (W : ℝ → ℂ) (N : ℝ) (D₁ D₂ I : HeckeGeneral.Analysis.NonzeroIdeal K) (δ₁ δ₂ ξ slope : ℝ) :
    rawPlainWeight W N D₁ D₂ δ₁ δ₂ ξ slope I =
      rawPlainWeight W N D₁ D₂ δ₁ δ₂ 0 slope I *
        jointPhase ξ (slope * Real.log (idealNorm K (D₂ * I))) := by
  simp only [rawPlainWeight, normLogWeight_nonzero, jointPhase, inner_zero_left,
    AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
  ring

theorem rawPrimeWeight_eq_zero_mul_phase
    (W : ℝ → ℂ) (N δ₁ δ₂ ξ slope : ℝ) (p : HeightOneSpectrum (𝓞 K)) :
    rawPrimeWeight W N δ₁ δ₂ ξ slope p =
      rawPrimeWeight W N δ₁ δ₂ 0 slope p *
        jointPhase ξ (slope * Real.log (Ideal.absNorm p.asIdeal : ℝ)) := by
  let I : HeckeGeneral.Analysis.NonzeroIdeal K := ⟨p.asIdeal, mem_nonZeroDivisors_of_ne_zero p.ne_bot⟩
  have hξ := normLogWeight_nonzero (δ₁ - 1) ξ slope I
  have hzero := normLogWeight_nonzero (δ₁ - 1) 0 slope I
  change normLogWeight (δ₁ - 1) ξ slope p.asIdeal = _ at hξ
  change normLogWeight (δ₁ - 1) 0 slope p.asIdeal = _ at hzero
  simp only [rawPrimeWeight, hξ, hzero, jointPhase, inner_zero_left,
    AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
  ring

/-- The literal Fourier-independent weight and the joint location
produce the same bounded profile on every original ideal. -/
theorem rawPlainWeight_joint_clipped
    (W : ℝ → ℂ) (N : ℝ) (hN : 0 < N) (D₁ D₂ I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (B δ₁ δ₂ ξ ζ slope secondSlope : ℝ) (hB : 1 ≤ B)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (hW : ∀ y, W y ≠ 0 → y ≤ B) :
    rawPlainWeight W N D₁ D₂ δ₁ δ₂ 0 slope I *
        jointPhase (WithLp.toLp 2 (ξ, ζ))
          (Real.log (idealNorm K (D₂ * I)) • firstDirection slope +
            Real.log (idealNorm K I) • secondDirection secondSlope) =
      ((clippedScalar (N / idealNorm K D₁ / idealNorm K D₂)
          (idealNorm K D₂) B δ₁ δ₂ : ℂ) *
        W (idealNorm K I / (N / idealNorm K D₁ / idealNorm K D₂))) *
        (atom (N / idealNorm K D₁ / idealNorm K D₂) (idealNorm K D₂) δ₁ δ₂
          (firstDirection slope) (secondDirection secondSlope)).multiplier
          (WithLp.toLp 2 (ξ, ζ))
          (idealNorm K I / (N / idealNorm K D₁ / idealNorm K D₂)) := by
  rw [phase_pair, ← mul_assoc, ← rawPlainWeight_eq_zero_mul_phase]
  exact rawPlainWeight_eq_clipped W N hN D₁ D₂ I B δ₁ δ₂ ξ ζ slope secondSlope
    hB hδ₁ hδ₂ hδ hW

theorem rawPrimeWeight_joint_clipped
    (W : ℝ → ℂ) (N : ℝ) (hN : 0 < N) (p : HeightOneSpectrum (𝓞 K))
    (B δ₁ δ₂ ξ ζ slope secondSlope : ℝ) (hB : 1 ≤ B)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (hW : ∀ y, W y ≠ 0 → y ≤ B) :
    rawPrimeWeight W N δ₁ δ₂ 0 slope p *
        jointPhase (WithLp.toLp 2 (ξ, ζ))
          (Real.log (Ideal.absNorm p.asIdeal : ℝ) • firstDirection slope +
            Real.log (Ideal.absNorm p.asIdeal : ℝ) • secondDirection secondSlope) =
      ((clippedScalar N 1 B δ₁ δ₂ : ℂ) * W ((Ideal.absNorm p.asIdeal : ℝ) / N)) *
        (atom N 1 δ₁ δ₂ (firstDirection slope) (secondDirection secondSlope)).multiplier
          (WithLp.toLp 2 (ξ, ζ)) ((Ideal.absNorm p.asIdeal : ℝ) / N) := by
  rw [phase_pair, ← mul_assoc, ← rawPrimeWeight_eq_zero_mul_phase]
  exact rawPrimeWeight_eq_clipped W N hN p B δ₁ δ₂ ξ ζ slope secondSlope
    hB hδ₁ hδ₂ hδ hW

/-- The later allocated divisor changes the physical profile scale.
The compensation still uses the original frame scale, so no extra
square root of that allocated divisor is inserted. -/
theorem rawPlainWeight_allocated_joint_clipped
    (W : ℝ → ℂ) (N : ℝ) (hN : 0 < N) (D₁ D₂ E I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (B δ₁ δ₂ ξ ζ slope secondSlope : ℝ) (hB : 1 ≤ B)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (hW : ∀ y, W y ≠ 0 → y ≤ B) :
    rawPlainWeight W N D₁ D₂ δ₁ δ₂ 0 slope (E * I) *
        jointPhase (WithLp.toLp 2 (ξ, ζ))
          (Real.log (idealNorm K (D₂ * (E * I))) • firstDirection slope +
            Real.log (idealNorm K (E * I)) • secondDirection secondSlope) =
      ((clippedScalar (N / idealNorm K D₁ / idealNorm K D₂)
          (idealNorm K D₂) B δ₁ δ₂ : ℂ) *
        W (idealNorm K I /
          ((N / idealNorm K D₁ / idealNorm K D₂) / idealNorm K E))) *
        (atom (N / idealNorm K D₁ / idealNorm K D₂) (idealNorm K D₂) δ₁ δ₂
          (firstDirection slope) (secondDirection secondSlope)).multiplier
          (WithLp.toLp 2 (ξ, ζ))
          (idealNorm K I /
            ((N / idealNorm K D₁ / idealNorm K D₂) / idealNorm K E)) := by
  simp only [quotient_norm_ratio E I]
  exact rawPlainWeight_joint_clipped W N hN D₁ D₂ (E * I) B δ₁ δ₂ ξ ζ slope secondSlope
    hB hδ₁ hδ₂ hδ hW

section OriginalWindows

variable {ω ψ : HeckeCharacter K}
variable (d : MomentData K ω ψ) (W : NormProfileRecipe (fun _ : PUnit => d))
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)} {P B : ℝ}
variable (w : RawProfileWindow rowDomain heightDomain window orders d P)
variable (hwindow : window ⊆ Set.Iic B)
variable (anchor : HeckeGeneral.Analysis.NonzeroIdeal K) (hanchor : d.allowedRow anchor)
variable (hanchorDomain : anchor ∈ rowDomain) (t : ℝ) (ht : t ∈ heightDomain)

/-- The norm-profile representative inherits the original support at
the original source anchor. It is not supplied with a moving window. -/
include w hwindow hanchor hanchorDomain ht in
theorem normRecipe_left_annulus (y : ℝ) (hy : W.left PUnit.unit t y ≠ 0) : y ≤ B := by
  apply hwindow
  apply w.left_support anchor hanchorDomain t ht
  change w.leftRep anchor t y ≠ 0
  rw [← w.left_eq anchor t y, W.left_eq PUnit.unit anchor hanchor t y]
  exact hy

include w hwindow hanchor hanchorDomain ht in
theorem normRecipe_right_annulus (y : ℝ) (hy : W.right PUnit.unit t y ≠ 0) : y ≤ B := by
  apply hwindow
  apply w.right_support anchor hanchorDomain t ht
  change w.rightRep anchor t y ≠ 0
  rw [← w.right_eq anchor t y, W.right_eq PUnit.unit anchor hanchor t y]
  exact hy

end OriginalWindows

section ActualCoreFields

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable [IsPrincipalIdealRing A.R]
variable {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (x : X)
variable (W : NormProfileRecipe (fun _ : PUnit => data x))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (hZ : 1 < Z)
variable (S₁ S₂ : Finset (Ideal (𝓞 K)))
variable (S : Fin (data x).geometry.slotCount → Finset (HeightOneSpectrum (𝓞 K)))
variable (firstCommon : A.Exterior)
variable (b₁ : SupportCartesianBranch S₁ S₂ S (primeSupport firstCommon.val))
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {τ : Type*} [Fintype τ] [DecidableEq τ]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (primes : τ → ExteriorPrime A) (m n : τ → ℕ) (firstRight : Bool)
variable (δ : NonzeroRingElements A.R) (firstTilt ξ : ℝ)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
variable (hemb : P.arithmetic.embedding = σ)
variable (J₁ : AllocationColumn K b₁.keep.card → A.Exterior)
variable (hJ₁ : ∀ i ∈ b₁.residualColumns, (J₁ i).val = allocationColumnIdeal i)
variable (hactive : ∀ i ∈ b₁.residualColumns,
  IsCoprime (J₁ i).val (firstActiveIdeal primes m n).val)
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (rows : ActualSecondCorrelationRows A σ H ι)
variable (side : SecondColumnSide) (χ : (PUnit × PUnit) →* Circle)
variable (secondCommon : A.Exterior)
local notation "L₁" => SupportCartesian.plainResidual S₁
  (primeSupport firstCommon.val) b₁.plainExtract₁
local notation "L₂" => SupportCartesian.plainResidual S₂
  (primeSupport firstCommon.val) b₁.plainExtract₂
local notation "idx₁" => SlotRestriction.index b₁.keep
local notation "Slots" => fun j => SupportCartesian.primeLive
  (S (idx₁ j)) (primeSupport firstCommon.val)
variable (b₂ : SupportCartesianBranch L₁ L₂ Slots (primeSupport secondCommon.val))
variable (J₂ : AllocationColumn K b₂.keep.card → A.Exterior)
variable (hJ₂ : ∀ i ∈ b₂.residualColumns, (J₂ i).val = allocationColumnIdeal i)
variable (secondTilt : ℝ) (rowOffset : H → ℝ)
variable (comparison : Bool)
variable (hcomparison : comparison = true →
  0 < Y₁ ∧ 0 < Y₂ ∧ Y₁ * Y₂ = Z ^ a.n₁ * Z ^ a.n₂)
local notation "idx₂" => SlotRestriction.index b₂.keep
local notation "factors" => originalSecondResidualCoreFactors Q x W a Z t Y₁ Y₂ hZ
  S₁ S₂ S firstCommon b₁ C primes m n firstRight δ firstTilt ξ hroot hemb
  J₁ hJ₁ hactive rows side χ secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison

/-- The actual constructed field, with both original extractions. -/
theorem core_leftWeight (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (factors).dictionary.leftWeight I =
      rawPlainWeight (W.left PUnit.unit t) (if comparison then Y₁ else Z ^ a.n₁)
        b₁.plainDivisor₁ b₂.plainDivisor₁ firstTilt secondTilt ξ
        (if firstRight then 1 else -1) I := rfl

theorem core_rightWeight (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (factors).dictionary.rightWeight I =
      rawPlainWeight (W.right PUnit.unit t) (if comparison then Y₂ else Z ^ a.n₂)
        b₁.plainDivisor₂ b₂.plainDivisor₂ firstTilt secondTilt ξ
        (if firstRight then 1 else -1) I := rfl

theorem core_slotWeight (j : Fin b₂.keep.card) (p : HeightOneSpectrum (𝓞 K)) :
    (factors).dictionary.slotWeight j p =
      rawPrimeWeight (((data x).geometry.slots (idx₁ (idx₂ j))).profile t)
        (Z ^ ((data x).geometry.slots (idx₁ (idx₂ j))).length)
        firstTilt secondTilt ξ (if firstRight then 1 else -1) p := rfl

variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)} {P₀ B : ℝ}
variable (raw : RawProfileWindow rowDomain heightDomain window orders (data x) P₀)
variable (hwindow : window ⊆ Set.Iic B) (hB : 1 ≤ B)
variable (hfirst : 0 ≤ firstTilt) (hsecond : 0 ≤ secondTilt)
variable (htilts : firstTilt + secondTilt ≤ 1 / 2)
variable (anchor : HeckeGeneral.Analysis.NonzeroIdeal K) (hanchor : (data x).allowedRow anchor)
variable (hanchorDomain : anchor ∈ rowDomain) (ht : t ∈ heightDomain)

local notation "N₁" => if comparison then Y₁ else Z ^ a.n₁
local notation "N₂" => if comparison then Y₂ else Z ^ a.n₂
local notation "G₁" => N₁ / idealNorm K b₁.plainDivisor₁ / idealNorm K b₂.plainDivisor₁
local notation "G₂" => N₂ / idealNorm K b₁.plainDivisor₂ / idealNorm K b₂.plainDivisor₂
local notation "slope" => if firstRight then 1 else -1

/-- This conclusion identifies the actual computed source field with
the bounded profile, directly from the original parent window. It also
applies at each later allocated ideal `D * I`. -/
include raw hwindow hB hfirst hsecond htilts hanchor hanchorDomain ht in
theorem core_leftWeight_clipped (I : HeckeGeneral.Analysis.NonzeroIdeal K) (ζ secondSlope : ℝ) :
    (factors).dictionary.leftWeight I * jointPhase ζ (secondSlope * Real.log (idealNorm K I)) =
      ((clippedScalar G₁ (idealNorm K b₂.plainDivisor₁) B firstTilt secondTilt : ℂ) *
        W.left PUnit.unit t (idealNorm K I / G₁)) *
        (atom G₁ (idealNorm K b₂.plainDivisor₁) firstTilt secondTilt
          (firstDirection slope) (secondDirection secondSlope)).multiplier
          (WithLp.toLp 2 (ξ, ζ)) (idealNorm K I / G₁) := by
  have hN : 0 < N₁ := by
    cases comparison
    · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    · exact (hcomparison rfl).1
  change rawPlainWeight (W.left PUnit.unit t) N₁ b₁.plainDivisor₁ b₂.plainDivisor₁
    firstTilt secondTilt ξ slope I * jointPhase ζ (secondSlope * Real.log (idealNorm K I)) = _
  exact rawPlainWeight_eq_clipped (W.left PUnit.unit t) N₁ hN
    b₁.plainDivisor₁ b₂.plainDivisor₁ I B firstTilt secondTilt ξ ζ slope secondSlope
    hB hfirst hsecond htilts
    (normRecipe_left_annulus (data x) W raw hwindow anchor hanchor hanchorDomain t ht)

include raw hwindow hB hfirst hsecond htilts hanchor hanchorDomain ht in
theorem core_rightWeight_clipped (I : HeckeGeneral.Analysis.NonzeroIdeal K) (ζ secondSlope : ℝ) :
    (factors).dictionary.rightWeight I * jointPhase ζ (secondSlope * Real.log (idealNorm K I)) =
      ((clippedScalar G₂ (idealNorm K b₂.plainDivisor₂) B firstTilt secondTilt : ℂ) *
        W.right PUnit.unit t (idealNorm K I / G₂)) *
        (atom G₂ (idealNorm K b₂.plainDivisor₂) firstTilt secondTilt
          (firstDirection slope) (secondDirection secondSlope)).multiplier
          (WithLp.toLp 2 (ξ, ζ)) (idealNorm K I / G₂) := by
  have hN : 0 < N₂ := by
    cases comparison
    · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    · exact (hcomparison rfl).2.1
  change rawPlainWeight (W.right PUnit.unit t) N₂ b₁.plainDivisor₂ b₂.plainDivisor₂
    firstTilt secondTilt ξ slope I * jointPhase ζ (secondSlope * Real.log (idealNorm K I)) = _
  exact rawPlainWeight_eq_clipped (W.right PUnit.unit t) N₂ hN
    b₁.plainDivisor₂ b₂.plainDivisor₂ I B firstTilt secondTilt ξ ζ slope secondSlope
    hB hfirst hsecond htilts
    (normRecipe_right_annulus (data x) W raw hwindow anchor hanchor hanchorDomain t ht)

include raw hwindow hB hfirst hsecond htilts ht in
theorem core_slotWeight_clipped (j : Fin b₂.keep.card)
    (p : HeightOneSpectrum (𝓞 K)) (ζ secondSlope : ℝ) :
    let G := Z ^ ((data x).geometry.slots (idx₁ (idx₂ j))).length
    (factors).dictionary.slotWeight j p * jointPhase ζ (secondSlope * Real.log (Ideal.absNorm p.asIdeal : ℝ)) =
      ((clippedScalar G 1 B firstTilt secondTilt : ℂ) *
        ((data x).geometry.slots (idx₁ (idx₂ j))).profile t
          ((Ideal.absNorm p.asIdeal : ℝ) / G)) *
        (atom G 1 firstTilt secondTilt (firstDirection slope) (secondDirection secondSlope)).multiplier
          (WithLp.toLp 2 (ξ, ζ)) ((Ideal.absNorm p.asIdeal : ℝ) / G) := by
  dsimp only
  change rawPrimeWeight (((data x).geometry.slots (idx₁ (idx₂ j))).profile t)
    (Z ^ ((data x).geometry.slots (idx₁ (idx₂ j))).length)
    firstTilt secondTilt ξ slope p * jointPhase ζ (secondSlope * Real.log (Ideal.absNorm p.asIdeal : ℝ)) = _
  apply rawPrimeWeight_eq_clipped
    (((data x).geometry.slots (idx₁ (idx₂ j))).profile t)
    (Z ^ ((data x).geometry.slots (idx₁ (idx₂ j))).length)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) p B firstTilt secondTilt ξ ζ slope secondSlope
    hB hfirst hsecond htilts
  intro y hy
  apply hwindow
  apply raw.prime_support (idx₁ (idx₂ j)) t ht
  simpa only [raw.prime_eq] using hy

end ActualCoreFields

section ActualPoolCoreFields

open CanonicalActualPoolRectangles

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable [IsPrincipalIdealRing A.R]
variable {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (x : X)
variable (W : NormProfileRecipe (fun _ : PUnit => data x))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ)
variable (S₁ S₂ : Finset (Ideal (𝓞 K)))
variable (S : Fin (data x).geometry.slotCount → Finset (HeightOneSpectrum (𝓞 K)))
variable (firstCommon : A.Exterior) (p : ExteriorPrime A) (v : ℕ) (hv : 0 < v)
variable (b₁ : SupportCartesianBranch S₁ S₂ S
  (primeSupport (combinedCommon firstCommon p v).val))
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {τ : Type*} [Fintype τ] [DecidableEq τ]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (primes : τ → ExteriorPrime A) (m n : τ → ℕ) (firstRight : Bool)
variable (δ : NonzeroRingElements A.R) (firstTilt ξ : ℝ)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
variable (hemb : P.arithmetic.embedding = σ)
variable (J₁ : AllocationColumn K b₁.keep.card → A.Exterior)
variable (hJ₁ : ∀ i ∈ b₁.residualColumns, (J₁ i).val = allocationColumnIdeal i)
variable (hactive : ∀ i ∈ b₁.residualColumns,
  IsCoprime (J₁ i).val (firstActiveIdeal primes m n).val)
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (rows : ActualSecondCorrelationRows A σ H ι)
variable (side : SecondColumnSide) (χ : (PUnit × PUnit) →* Circle)
variable (secondCommon : A.Exterior)
local notation "common" => combinedCommon firstCommon p v
local notation "L₁" => SupportCartesian.plainResidual S₁
  (primeSupport (common).val) b₁.plainExtract₁
local notation "L₂" => SupportCartesian.plainResidual S₂
  (primeSupport (common).val) b₁.plainExtract₂
local notation "idx₁" => SlotRestriction.index b₁.keep
local notation "Slots" => fun j => SupportCartesian.primeLive
  (S (idx₁ j)) (primeSupport (common).val)
variable (b₂ : SupportCartesianBranch L₁ L₂ Slots (primeSupport secondCommon.val))
variable (J₂ : AllocationColumn K b₂.keep.card → A.Exterior)
variable (hJ₂ : ∀ i ∈ b₂.residualColumns, (J₂ i).val = allocationColumnIdeal i)
variable (secondTilt : ℝ) (rowOffset : H → ℝ) (hZ : 1 < Z)
variable (comparison : Bool)
variable (hcomparison : comparison = true →
  0 < Y₁ ∧ 0 < Y₂ ∧ Y₁ * Y₂ = Z ^ a.n₁ * Z ^ a.n₂)
local notation "idx₂" => SlotRestriction.index b₂.keep
local notation "factors" => originalPoolSecondCoreFactors Q x W a Z t Y₁ Y₂
  S₁ S₂ S firstCommon p v hv b₁ C primes m n firstRight δ firstTilt ξ hroot hemb
  J₁ hJ₁ hactive side χ rows secondCommon b₂ J₂ hJ₂ secondTilt rowOffset hZ
  comparison hcomparison

/-- The extra pool character and prime-power scalar leave the residual
analytic weights unchanged. The original common divisor here is the
actual combined support-and-pool divisor. -/
theorem pool_core_leftWeight (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (factors).dictionary.leftWeight I =
      rawPlainWeight (W.left PUnit.unit t) (if comparison then Y₁ else Z ^ a.n₁)
        b₁.plainDivisor₁ b₂.plainDivisor₁ firstTilt secondTilt ξ
        (if firstRight then 1 else -1) I := rfl

theorem pool_core_rightWeight (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (factors).dictionary.rightWeight I =
      rawPlainWeight (W.right PUnit.unit t) (if comparison then Y₂ else Z ^ a.n₂)
        b₁.plainDivisor₂ b₂.plainDivisor₂ firstTilt secondTilt ξ
        (if firstRight then 1 else -1) I := rfl

theorem pool_core_slotWeight (j : Fin b₂.keep.card) (q : HeightOneSpectrum (𝓞 K)) :
    (factors).dictionary.slotWeight j q =
      rawPrimeWeight (((data x).geometry.slots (idx₁ (idx₂ j))).profile t)
        (Z ^ ((data x).geometry.slots (idx₁ (idx₂ j))).length)
        firstTilt secondTilt ξ (if firstRight then 1 else -1) q := rfl

end ActualPoolCoreFields

end HeckeSkeleton.Moments.EngineStep.CanonicalCoreProfileIdentification

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalCoreProfileIdentification.rawPlainWeight_eq_clipped
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalCoreProfileIdentification.rawPrimeWeight_eq_clipped
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalCoreProfileIdentification.core_leftWeight
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalCoreProfileIdentification.rawPlainWeight_allocated_joint_clipped
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalCoreProfileIdentification.core_leftWeight_clipped
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalCoreProfileIdentification.pool_core_leftWeight
