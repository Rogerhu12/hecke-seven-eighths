import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalHeckePrimeAnalytic
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.UnrestrictedSixthCapacity
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFiniteKernelMass

/-!
# The full-kappa input constructs the same normalized side and Fourier radius

The original data and clipped data retain all their individual profiles.
The actual Hecke zero-free input supplies the retained-prime estimate.
The common radius is enlarged within the literal polynomial-radius
family, so the existing exact kernel-mass and integrability theorems
continue to apply to this very normalization.

Only the prime profiles use their original (1,2) support. The two plain
profiles keep their full original annular window, including clipping.
The complete pre-removal envelope cost is paid below; no completed
child, total mass, or normalized-prime estimate is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open PrimeCancellation.Analytic

namespace CanonicalFullKappaPrime

variable {U E : Type*} [NormedAddCommGroup U] [NormedAddCommGroup E]

/-- This coefficient keeps the actual radius in the same polynomial
family required by the common Fourier kernel. -/
def enlargedCoefficient (B R : ℝ) : ℝ := R * (1 + B)

theorem enlargedCoefficient_nonneg {B R : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R) :
    0 ≤ enlargedCoefficient B R := mul_nonneg hR (by linarith)

/-- The extra constant term is paid together with every original
profile, before deciding which slots are retained. -/
theorem radius_mul_le_enlarged (B R : ℝ) (hR : 0 ≤ R)
    (J₁ J₂ : ℕ) (z : U × E) :
    polynomialProfileRadius B J₁ J₂ z * R ≤
      polynomialProfileRadius (enlargedCoefficient B R) J₁ J₂ z := by
  have hp : 1 ≤ (1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂ :=
    one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (by linarith [norm_nonneg z.1]))
      (one_le_pow₀ (by linarith [norm_nonneg z.2]))
  have hmul := mul_le_mul_of_nonneg_left hp hR
  unfold polynomialProfileRadius enlargedCoefficient
  nlinarith

theorem radius_le_enlarged (B R : ℝ) (hB : 0 ≤ B) (hR : 1 ≤ R)
    (J₁ J₂ : ℕ) (z : U × E) :
    polynomialProfileRadius B J₁ J₂ z ≤
      polynomialProfileRadius (enlargedCoefficient B R) J₁ J₂ z :=
  (le_mul_of_one_le_right (polynomialProfileRadius_pos B hB J₁ J₂ z).le hR).trans
    (radius_mul_le_enlarged B R (zero_le_one.trans hR) J₁ J₂ z)

/-- A bound on the exact coefficient used by the standard paired
Fourier mass theorem. The exponent is the full number of profiles. -/
theorem paired_envelopeConstant_le (B₁ B₂ R : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hR : 1 ≤ R) (n₁ n₂ : ℕ) :
    pairedProfileEnvelopeConstant (enlargedCoefficient B₁ R)
      (enlargedCoefficient B₂ R) n₁ n₂ ≤
      (2 * R) ^ ((n₁ + 2) + (n₂ + 2)) *
        pairedProfileEnvelopeConstant B₁ B₂ n₁ n₂ := by
  have hsingle (B : ℝ) (hB : 0 ≤ B) :
      1 + enlargedCoefficient B R ≤ (2 * R) * (1 + B) := by
    have hprod : 1 ≤ R * (1 + B) :=
      one_le_mul_of_one_le_of_one_le hR (by linarith)
    unfold enlargedCoefficient
    nlinarith
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  calc
    _ ≤ ((2 * R) * (1 + B₁)) ^ (n₁ + 2) *
        ((2 * R) * (1 + B₂)) ^ (n₂ + 2) :=
      mul_le_mul
        (pow_le_pow_left₀ (by
          have := enlargedCoefficient_nonneg hB₁ hR0
          linarith) (hsingle B₁ hB₁) _)
        (pow_le_pow_left₀ (by
          have := enlargedCoefficient_nonneg hB₂ hR0
          linarith) (hsingle B₂ hB₂) _)
        (pow_nonneg (by
          have := enlargedCoefficient_nonneg hB₂ hR0
          linarith) _)
        (pow_nonneg (by positivity) _)
    _ = _ := by
      simp only [pairedProfileEnvelopeConstant, mul_pow, pow_add]
      ring

end CanonicalFullKappaPrime

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {U E H : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable {s : ActualAllocatedSource A (WithLp 2 (U × E)) H k}

namespace ActualAllocatedSource.Calibration

variable (D : s.Calibration (σ := σ) ω ψ)
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {rowInput : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable (Q : CompleteMovingRowRecipe A P rowInput D.data)

/-- These are original single-profile, length and analytic windows.
Both windows refer to the same actual calibration. In particular there
is no assumption about the normalized profiles or the chosen child. -/
structure FullKappaProfileInput
    (rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K))
    (heightDomain window : Set ℝ) (seminorms : Finset (ℕ × ℕ))
    (B : ℝ) (J₁ J₂ : ℕ) (δ lengthBound analyticHeight width : ℝ) where
  coefficient_nonneg : 0 ≤ B
  orders : CanonicalFullKappaPrime.orders ⊆ seminorms
  raw : ∀ ξ, RawProfileWindow rowDomain heightDomain window seminorms (D.data ξ)
    (polynomialProfileRadius B J₁ J₂ (WithLp.ofLp ξ))
  clipped : ∀ ξ, RawProfileWindow rowDomain heightDomain window seminorms (D.clippedData ξ)
    (polynomialProfileRadius B J₁ J₂ (WithLp.ofLp ξ))
  annulus : ℝ
  annulus_one : 1 ≤ annulus
  window_upper : ∀ x ∈ window, x ≤ annulus
  prime_support : ∀ ξ i,
    Function.support ((raw ξ).primeRep i (D.height ξ) : ℝ → ℂ) ⊆ Set.Ioo (1 : ℝ) 2
  rows : ∀ ξ, ∀ u ∈ pairedRows (D.data ξ) D.parameters s.base, u ∈ rowDomain
  height : ∀ ξ, D.height ξ ∈ heightDomain
  delta_pos : 0 < δ
  delta_le : δ ≤ 1 / 4
  length_nonneg : 0 ≤ lengthBound
  length_le : ∀ i, s.childLength i ≤ lengthBound
  kappa_lower : 3 / 4 ≤ D.parameters.κ
  kappa_upper : D.parameters.κ ≤ 1
  full_support : Q.FullJointBudget s.base width
  analytic : ∀ _hκ : D.parameters.κ < 1, ∀ ξ,
    ∀ u, u ∈ pairedRows (D.data ξ) D.parameters s.base →
    ∀ i : Fin s.allocation.keep.card,
      ZeroFreeData (heckeContinuation K ((D.data ξ).rowCharacter u *
        (D.data ξ).slotCoefficient
          (lengthSlot (D.data ξ) s.allocation.keep.card (D.count ξ) i)))
        ((D.parameters.κ + 1) / 2)
  analytic_height : ∀ hκ : D.parameters.κ < 1, ∀ ξ,
    ∀ u, ∀ hu : u ∈ pairedRows (D.data ξ) D.parameters s.base,
    ∀ i : Fin s.allocation.keep.card,
      heightConstant (analytic hκ ξ u hu i) + 3 * ((analytic hκ ξ u hu i).k : ℝ) ≤
        analyticHeight

namespace FullKappaProfileInput

variable {D Q}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)}
variable {B δ lengthBound analyticHeight width : ℝ} {J₁ J₂ : ℕ}
variable (W : D.FullKappaProfileInput Q rowDomain heightDomain window seminorms
  B J₁ J₂ δ lengthBound analyticHeight width)

/-- The explicit original analytic cost is common to every Fourier
parameter and every retained slot of this source. -/
def factor (W : D.FullKappaProfileInput Q rowDomain heightDomain window seminorms
    B J₁ J₂ δ lengthBound analyticHeight width) : ℝ :=
  CanonicalFullKappaPrime.radiusFactor K s.base δ lengthBound
  (CanonicalHeckePrimeAnalytic.degreeBound K) analyticHeight
  (CompleteMovingRowRecipe.primeMaskLogBound A s.base width)

theorem factor_one : 1 ≤ W.factor :=
  CanonicalFullKappaPrime.one_le_radiusFactor _ _ _ _ _ _
    s.base_gt_one.le W.delta_pos.le W.length_nonneg

def coefficient : ℝ := CanonicalFullKappaPrime.enlargedCoefficient B W.factor

theorem coefficient_nonnegative : 0 ≤ W.coefficient :=
  CanonicalFullKappaPrime.enlargedCoefficient_nonneg W.coefficient_nonneg
    (zero_le_one.trans W.factor_one)

def amplitude (ξ : WithLp 2 (U × E)) : ℝ :=
  polynomialProfileRadius W.coefficient J₁ J₂ (WithLp.ofLp ξ)

theorem amplitude_pos (ξ : WithLp 2 (U × E)) : 0 < W.amplitude ξ :=
  polynomialProfileRadius_pos _ W.coefficient_nonnegative _ _ _

theorem original_amplitude_le (ξ : WithLp 2 (U × E)) :
    polynomialProfileRadius B J₁ J₂ (WithLp.ofLp ξ) ≤ W.amplitude ξ :=
  CanonicalFullKappaPrime.radius_le_enlarged B W.factor W.coefficient_nonneg
    W.factor_one J₁ J₂ (WithLp.ofLp ξ)

theorem original_amplitude_mul_factor_le (ξ : WithLp 2 (U × E)) :
    polynomialProfileRadius B J₁ J₂ (WithLp.ofLp ξ) * W.factor ≤ W.amplitude ξ :=
  CanonicalFullKappaPrime.radius_mul_le_enlarged B W.factor
    (zero_le_one.trans W.factor_one) J₁ J₂ (WithLp.ofLp ξ)

/-- The complete original raw profile representatives are unchanged. -/
def rawWindow (ξ : WithLp 2 (U × E)) :
    RawProfileWindow rowDomain heightDomain window seminorms (D.data ξ) (W.amplitude ξ) :=
  (W.raw ξ).mono (W.original_amplitude_le ξ)

/-- The actual clipping is the original one. Only its common positive
normalizing amplitude increases. -/
def clippedWindow (ξ : WithLp 2 (U × E)) :
    RawProfileWindow rowDomain heightDomain window seminorms
      (D.clippedData ξ) (W.amplitude ξ) :=
  (W.clipped ξ).mono (W.original_amplitude_le ξ)

/-- All prime bounds of this actual source are produced internally.
Their exact factorization is amplitude squared times the constant one. -/
def atoms : D.OriginalCapacityAtoms where
  leftAnnulus := W.annulus
  rightAnnulus := W.annulus
  leftAnnulus_one := W.annulus_one
  rightAnnulus_one := W.annulus_one
  left_window ξ u hu x hx :=
    (W.raw ξ).original_left_profile_upper W.annulus W.window_upper
      u (W.rows ξ u hu) (D.height ξ) (W.height ξ) x hx
  right_window ξ u hu x hx :=
    (W.raw ξ).original_right_profile_upper W.annulus W.window_upper
      u (W.rows ξ u hu) (D.height ξ) (W.height ξ) x hx
  primeBound ξ _ := W.amplitude ξ ^ 2
  primeBound_nonneg ξ _ := sq_nonneg _
  prime_bound ξ u hu i := by
    let j := lengthSlot (D.data ξ) s.allocation.keep.card (D.count ξ) i
    have hlen : ((D.data ξ).geometry.slots j).length = s.childLength i :=
      D.clipped_lengths ξ i
    have hprof : CanonicalFullKappaPrime.orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        ((W.raw ξ).primeRep j (D.height ξ)) ≤
        polynomialProfileRadius B J₁ J₂ (WithLp.ofLp ξ) := by
      apply Seminorm.finset_sup_apply_le (polynomialProfileRadius_pos B W.coefficient_nonneg _ _ _).le
      intro p hp
      exact (Seminorm.le_finset_sup_apply (W.orders hp)).trans
        ((W.raw ξ).prime_bound j (D.height ξ) (W.height ξ))
    have hallowed : (D.data ξ).allowedRow u :=
      (((D.data ξ).rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1
    have hb := CanonicalFullKappaPrime.raw_prime_bound_radius
      (D.data ξ) j u s.base (D.height ξ) D.parameters.κ δ lengthBound
      (CanonicalHeckePrimeAnalytic.degreeBound K) analyticHeight
      (CompleteMovingRowRecipe.primeMaskLogBound A s.base width)
      (polynomialProfileRadius B J₁ J₂ (WithLp.ofLp ξ))
      s.base_gt_one.le W.kappa_lower W.kappa_upper W.delta_pos W.delta_le
      (hlen.trans_le (W.length_le i)) (polynomialProfileRadius_pos B W.coefficient_nonneg _ _ _).le
      ((W.raw ξ).primeRep j (D.height ξ)) ((W.raw ξ).prime_eq j (D.height ξ))
      (W.prime_support ξ j) hprof (Q.primeDeletionIdeal u) (Q.deleted_prime_dvd ξ u)
      (Q.primeDeletionIdeal_log_le s.base width (zero_lt_one.trans s.base_gt_one)
        W.full_support ξ u hallowed)
      (fun hκ => OriginalPrimeAnalyticData.ofHecke _ _ (W.analytic hκ ξ u hu i))
      (fun hκ => W.analytic_height hκ ξ u hu i)
    rw [hlen] at hb
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans s.base_gt_one).le _)
    exact pow_le_pow_left₀
      (mul_nonneg (polynomialProfileRadius_pos B W.coefficient_nonneg _ _ _).le
        (zero_le_one.trans W.factor_one))
      (W.original_amplitude_mul_factor_le ξ) 2

@[simp] theorem atoms_primeBound (ξ : WithLp 2 (U × E)) (i : Fin s.allocation.keep.card) :
    W.atoms.primeBound ξ i = W.amplitude ξ ^ 2 * 1 := by rw [mul_one]; rfl

@[simp] theorem amplitude_toLp (z : U × E) :
    W.amplitude (WithLp.toLp 2 z) = polynomialProfileRadius W.coefficient J₁ J₂ z := rfl

end FullKappaProfileInput
end ActualAllocatedSource.Calibration

namespace SecondSideNormalization

variable [IsPrincipalIdealRing A.R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {side : SecondColumnSide}
variable (f : SecondSideFrame (V := WithLp 2 (U × E)) C R Ray side k)
variable (D : f.source.Calibration (σ := σ) ω ψ)
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {rowInput : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable (Q : CompleteMovingRowRecipe A P rowInput D.data)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)}
variable {B δ lengthBound analyticHeight width : ℝ} {J₁ J₂ : ℕ}
variable (profiles : D.FullKappaProfileInput Q rowDomain heightDomain window seminorms
  B J₁ J₂ δ lengthBound analyticHeight width)
variable (parent : MomentData K ω ψ) (a : RealParameters) (step : ℝ)
variable (G : OriginalNominalGeometry (K := K) a f.source.base step)
variable (binding : D.OriginalSixthLengthBinding parent a step G
  (idealLogLength f.source.base
    (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val))
variable (hm : ∀ i, 0 < R.leftMultiplicity i) (hn : ∀ i, 0 < R.rightMultiplicity i)
variable (pattern : ι → Bool)
variable (hsecond : G.ideals.second.val = (primePowerProduct R.primes R.leftMultiplicity).val)
variable (hopposite : G.ideals.secondOpposite.val =
  (primePowerProduct R.primes R.rightMultiplicity).val)
variable (hunit : G.ideals.unitPart.val =
  (secondPatternUnitIdeal R.primes R.leftMultiplicity R.rightMultiplicity pattern).val)
variable (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
variable (hfit : parent.geometry.fitsMesh mesh)

/-- The producer's actual frame, pattern and sixth-root capacity ledger
now give a complete side normalization. The original chosen calibration,
all profiles and every mask remain fixed; slot bounds are the constant one. -/
def ofFullKappaOriginalSixthPattern :
    SecondSideNormalization f ω ψ rowDomain heightDomain window seminorms :=
  ofOriginalSixthPattern f D parent a step G binding hm hn pattern hsecond hopposite hunit
    hstep mesh hmesh hfit profiles.atoms rowDomain heightDomain window seminorms
    profiles.amplitude profiles.amplitude_pos (fun _ => 1) (fun _ => zero_le_one)
    profiles.atoms_primeBound profiles.clippedWindow

@[simp] theorem ofFullKappaOriginalSixthPattern_calibration :
    (ofFullKappaOriginalSixthPattern f D Q profiles parent a step G binding hm hn pattern
      hsecond hopposite hunit hstep mesh hmesh hfit).calibration = D := rfl

@[simp] theorem ofFullKappaOriginalSixthPattern_radius (z : U × E) :
    (ofFullKappaOriginalSixthPattern f D Q profiles parent a step G binding hm hn pattern
      hsecond hopposite hunit hstep mesh hmesh hfit).normalizedCapacityData.radius
        (WithLp.toLp 2 z) = polynomialProfileRadius profiles.coefficient J₁ J₂ z := rfl

@[simp] theorem ofFullKappaOriginalSixthPattern_primeBound (i : Fin f.source.allocation.keep.card) :
    (ofFullKappaOriginalSixthPattern f D Q profiles parent a step G binding hm hn pattern
      hsecond hopposite hunit hstep mesh hmesh hfit).normalizedCapacityData.primeBound i = 1 := rfl

end SecondSideNormalization

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFullKappaPrime.paired_envelopeConstant_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.FullKappaProfileInput.atoms
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideNormalization.ofFullKappaOriginalSixthPattern
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideNormalization.ofFullKappaOriginalSixthPattern_radius
