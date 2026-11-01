import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualExceptionalAmplitude
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OrdinaryExceptionalAmplitude
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFactorFreeSchwartz
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActualCharacters

/-!
# The exceptional charts of the literal original profiles

The two logarithmic coordinates give one real norm-twist parameter.
An allocated divisor contributes a constant unit phase; it does not
change the smooth profile or its seminorms.  The finite support follows
from the original occurrence support and the complete arithmetic mask.

The scale-free representatives are those already constructed from the
original parent profiles.  Their two centered copies agree before any
ideal sum is taken.  The ordinary branch uses only its original copy.
No identity of a complete polynomial or an exceptional estimate is an
input to the pointwise constructions below.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support
open HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralExceptionalCharts

local notation "Joint" => WithLp 2 (ℝ × ℝ)

/-- The original two Fourier variables remain arbitrary. -/
def time (firstSign : ℝ) (ξ : Joint) : ℝ :=
  -(2 * Real.pi * inner ℝ ξ (CanonicalLiteralLocations.direction firstSign))

theorem phase_log (firstSign : ℝ) (ξ : Joint) (N : ℝ) (hN : 0 < N) :
    jointPhase ξ (-Real.log N • CanonicalLiteralLocations.direction firstSign) =
      (N : ℂ) ^ (Complex.I * (time firstSign ξ : ℂ)) := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Complex.cpow_def_of_ne_zero hN', ← Complex.ofReal_log hN.le]
  simp only [jointPhase, Real.fourierChar_apply, inner_smul_right, time,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
  congr 1
  ring

theorem phase_ideal (firstSign : ℝ) (ξ : Joint) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    jointPhase ξ (CanonicalLiteralLocations.plain firstSign I) =
      (Ideal.absNorm I.val : ℂ) ^ (Complex.I * (time firstSign ξ : ℂ)) := by
  simpa only [CanonicalLiteralLocations.plain, idealNorm, Complex.ofReal_natCast] using
    phase_log firstSign ξ (idealNorm K I) (idealNorm_pos K I)

theorem plain_mul (firstSign : ℝ) (B I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    CanonicalLiteralLocations.plain firstSign (B * I) =
      CanonicalLiteralLocations.plain firstSign B +
        CanonicalLiteralLocations.plain firstSign I := by
  simp only [CanonicalLiteralLocations.plain,
    CanonicalLiteralProfileData.idealNorm_mul,
    Real.log_mul (idealNorm_pos K B).ne' (idealNorm_pos K I).ne',
    neg_add, add_smul]

theorem phase_mul (firstSign : ℝ) (ξ : Joint) (B I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    jointPhase ξ (CanonicalLiteralLocations.plain firstSign (B * I)) =
      jointPhase ξ (CanonicalLiteralLocations.plain firstSign B) *
        (Ideal.absNorm I.val : ℂ) ^ (Complex.I * (time firstSign ξ : ℂ)) := by
  rw [plain_mul, jointPhase_add, phase_ideal]

/-- The divisor phase is the same in both original rectangles. -/
def profile (firstSign : ℝ) (ξ : Joint) (B : HeckeGeneral.Analysis.NonzeroIdeal K)
    (φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  jointPhase ξ (CanonicalLiteralLocations.plain firstSign B) • φ

@[simp] theorem profile_apply (firstSign : ℝ) (ξ : Joint) (B : HeckeGeneral.Analysis.NonzeroIdeal K)
    (φ : 𝓢(ℝ, ℂ)) (y : ℝ) :
    profile firstSign ξ B φ y =
      jointPhase ξ (CanonicalLiteralLocations.plain firstSign B) * φ y := rfl

theorem profile_support (firstSign : ℝ) (ξ : Joint) (B : HeckeGeneral.Analysis.NonzeroIdeal K)
    (φ : 𝓢(ℝ, ℂ)) : tsupport (profile firstSign ξ B φ) ⊆ tsupport φ :=
  tsupport_smul_subset_right
    (fun _ : ℝ => jointPhase ξ (CanonicalLiteralLocations.plain firstSign B)) φ

theorem profile_seminorm (firstSign : ℝ) (ξ : Joint) (B : HeckeGeneral.Analysis.NonzeroIdeal K)
    (φ : 𝓢(ℝ, ℂ)) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (profile firstSign ξ B φ) =
      s.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
  rw [profile, map_smul_eq_mul, norm_jointPhase, one_mul]

/-- Negative source locations are represented by the same original
profile at the opposite joint Fourier mode. -/
def orientedMode (negative : Bool) (ξ : Joint) : Joint :=
  if negative then -ξ else ξ

def orientChart {A : SArithmeticData K} {σ : K →+* ℂ}
    {χ θ : HeckeCharacter K} {M Ψ : Ideal (𝓞 K) →* ℂ}
    {g h : A.R} {mask : Ideal (𝓞 K)} {W : ℝ → ℂ} {t N : ℝ}
    {columns : Finset (HeckeGeneral.Analysis.NonzeroIdeal K)} {w : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ}
    {x : HeckeGeneral.Analysis.NonzeroIdeal K → Joint} (negative : Bool) (ξ : Joint)
    (H : ExceptionalPlainChart (σ := σ) χ θ M g h Ψ mask W t N
      columns w x (orientedMode negative ξ)) :
    ExceptionalPlainChart (σ := σ) χ θ M g h Ψ mask W t N columns w
      (fun I => CanonicalLiteralProfileData.orientedLocation negative (x I)) ξ := by
  cases negative with
  | false => exact H
  | true =>
      refine { coefficient := H.coefficient, support := H.support, profile := ?_ }
      intro I hI
      have he := H.profile I hI
      change w I * jointPhase (-ξ) (x I) = _ at he
      change w I * jointPhase ξ (-(x I)) = _
      simpa only [jointPhase, inner_neg_left, inner_neg_right] using he

section LiteralProfiles

variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable {W : d.ProfileData} {window : Set ℝ}
variable (E : W.SchwartzModel window)

theorem left_quotient_eval (r : Bool) (B I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    E.left r (idealNorm K I / (d.scale₁ r / idealNorm K B)) =
      d.rectangleLeftWeight r (B * I) := by
  rw [CanonicalLiteralProfileData.quotient_argument]
  exact (E.left_eq r 1 0 _).symm.trans (W.left_eval r 1 0 (B * I))

theorem right_quotient_eval (r : Bool) (B I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    E.right r (idealNorm K I / (d.scale₂ r / idealNorm K B)) =
      d.rightWeight r (B * I) := by
  rw [CanonicalLiteralProfileData.quotient_argument]
  exact (E.right_eq r 1 0 _).symm.trans (W.right_eval r 1 0 (B * I))

/-- This is the full allocated occurrence, including the logarithm of
its actual divisor. The quotient scale is never replaced. -/
theorem left_profile (r : Bool) (firstSign : ℝ) (ξ : Joint) (B I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    d.rectangleLeftWeight r (B * I) *
        jointPhase ξ (CanonicalLiteralLocations.plain firstSign (B * I)) =
      (Ideal.absNorm I.val : ℂ) ^ (Complex.I * (time firstSign ξ : ℂ)) *
        profile firstSign ξ B (E.left r)
          ((Ideal.absNorm I.val : ℝ) / (d.scale₁ r / idealNorm K B)) := by
  change _ = _ * profile firstSign ξ B (E.left r)
    (idealNorm K I / (d.scale₁ r / idealNorm K B))
  rw [profile_apply, left_quotient_eval E, phase_mul]
  ring

theorem right_profile (r : Bool) (firstSign : ℝ) (ξ : Joint) (B I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    d.rightWeight r (B * I) *
        jointPhase ξ (CanonicalLiteralLocations.plain firstSign (B * I)) =
      (Ideal.absNorm I.val : ℂ) ^ (Complex.I * (time firstSign ξ : ℂ)) *
        profile firstSign ξ B (E.right r)
          ((Ideal.absNorm I.val : ℝ) / (d.scale₂ r / idealNorm K B)) := by
  change _ = _ * profile firstSign ξ B (E.right r)
    (idealNorm K I / (d.scale₂ r / idealNorm K B))
  rw [profile_apply, right_quotient_eval E, phase_mul]
  ring

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {excluded : Finset (Ideal (𝓞 K))}
variable (support : d.SupportData excluded) (B : ActualColumnAllocation K k)
variable (g h : A.R) (Ψ : Ideal (𝓞 K) →* ℂ) (mask : Ideal (𝓞 K))

/-- The complete original arithmetic mask contains the deleted
primes. This only transports its coprimality to those same primes. -/
theorem avoids_of_coprime
    (hdeleted : ∀ p ∈ excluded, p ∣ mask) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : IsCoprime I.val mask) : CanonicalLiteralSupport.Avoids I.val excluded := by
  intro p hp
  exact hI.of_isCoprime_of_dvd_right (hdeleted p hp)

include support in
/-- Construct the first actual plain chart from its individual
profile and the original arithmetic coefficient identity. -/
def leftChart (hplain : B.plain₁ = d.plain₁)
    (havoid : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K, IsCoprime I.val mask →
      CanonicalLiteralSupport.Avoids I.val excluded)
    (coefficient : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K,
      sourcePlainCoefficient d.characters.plain d.characters.plainTwist d.characters.mask I *
        actualIdealResidue (A := A) (σ := σ) I.val (g * h) =
          (if IsCoprime I.val mask then (1 : ℂ) else 0) * Ψ I.val)
    (r : Bool) (firstSign : ℝ) (ξ : Joint) :
    ExceptionalPlainChart (σ := σ) d.characters.plain d.characters.plainTwist
      d.characters.mask g h Ψ mask
      (profile firstSign ξ (B.plainDivisor 0) (E.left r))
      (time firstSign ξ) (d.scale₁ r / idealNorm K (B.plainDivisor 0))
      B.childPlain₁ (fun I => d.rectangleLeftWeight r (B.plainDivisor 0 * I))
      (fun I => CanonicalLiteralLocations.plain firstSign (B.plainDivisor 0 * I)) ξ where
  coefficient I _ := coefficient I
  profile I _ := left_profile E r firstSign ξ (B.plainDivisor 0) I
  support I hI _ hprofile := by
    have hw : d.rectangleLeftWeight r (B.plainDivisor 0 * I) ≠ 0 := by
      rw [profile_apply] at hprofile
      have he := right_ne_zero_of_mul hprofile
      change E.left r (idealNorm K I /
        (d.scale₁ r / idealNorm K (B.plainDivisor 0))) ≠ 0 at he
      rwa [left_quotient_eval E] at he
    change I ∈ nonzeroQuotientMomentSupport (B.plainDivisor 0).val B.plain₁
    apply (mem_nonzeroQuotientMomentSupport _
      (nonZeroDivisors.coe_ne_zero (B.plainDivisor 0)) _ I).mpr
    rw [hplain]
    exact support.left_mem r (B.plainDivisor 0 * I) hw (fun p hp =>
      (support.leftDivisor_avoids B hplain p hp).mul_left
        (havoid I hI p hp))

include support in
/-- The second plain occurrence has its own true quotient scale and
the same complete inducing character and mask. -/
def rightChart (hplain : B.plain₂ = d.plain₂)
    (havoid : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K, IsCoprime I.val mask →
      CanonicalLiteralSupport.Avoids I.val excluded)
    (coefficient : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K,
      sourcePlainCoefficient d.characters.plain d.characters.plainTwist d.characters.mask I *
        actualIdealResidue (A := A) (σ := σ) I.val (g * h) =
          (if IsCoprime I.val mask then (1 : ℂ) else 0) * Ψ I.val)
    (r : Bool) (firstSign : ℝ) (ξ : Joint) :
    ExceptionalPlainChart (σ := σ) d.characters.plain d.characters.plainTwist
      d.characters.mask g h Ψ mask
      (profile firstSign ξ (B.plainDivisor (Fin.succ 0)) (E.right r))
      (time firstSign ξ) (d.scale₂ r / idealNorm K (B.plainDivisor (Fin.succ 0)))
      B.childPlain₂ (fun I => d.rightWeight r (B.plainDivisor (Fin.succ 0) * I))
      (fun I => CanonicalLiteralLocations.plain firstSign
        (B.plainDivisor (Fin.succ 0) * I)) ξ where
  coefficient I _ := coefficient I
  profile I _ := right_profile E r firstSign ξ (B.plainDivisor (Fin.succ 0)) I
  support I hI _ hprofile := by
    have hw : d.rightWeight r (B.plainDivisor (Fin.succ 0) * I) ≠ 0 := by
      rw [profile_apply] at hprofile
      have he := right_ne_zero_of_mul hprofile
      change E.right r (idealNorm K I /
        (d.scale₂ r / idealNorm K (B.plainDivisor (Fin.succ 0)))) ≠ 0 at he
      rwa [right_quotient_eval E] at he
    change I ∈ nonzeroQuotientMomentSupport (B.plainDivisor (Fin.succ 0)).val B.plain₂
    apply (mem_nonzeroQuotientMomentSupport _
      (nonZeroDivisors.coe_ne_zero (B.plainDivisor (Fin.succ 0))) _ I).mpr
    rw [hplain]
    exact support.right_mem r (B.plainDivisor (Fin.succ 0) * I) hw (fun p hp =>
      (support.rightDivisor_avoids B hplain p hp).mul_left
        (havoid I hI p hp))

end LiteralProfiles

section CommonProfiles

variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable {W : d.ProfileData} {window : Set ℝ}
variable (E : W.SchwartzModel window)

/-- Equality of the two representatives, before ideal evaluation.
The original constructor below proves this for a centered parent. -/
def SamePlainProfiles : Prop :=
  E.left true = E.left false ∧ E.right true = E.right false

theorem samePlainProfiles_extract
    (hc : SamePlainProfiles E) {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) :
    SamePlainProfiles (E.extract b) := hc

theorem samePlainProfiles_onAtlas
    (hc : SamePlainProfiles E) {A : SArithmeticData K} {ι : Type*}
    {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (count : k = T.slotCount) :
    SamePlainProfiles (E.onAtlas T count) := by
  cases count
  exact hc

theorem samePlainProfiles_deleteMask (hc : SamePlainProfiles E)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K) : SamePlainProfiles (E.deleteMask M) := hc

theorem samePlainProfiles_scale (hc : SamePlainProfiles E) (c : ℂ) :
    SamePlainProfiles (E.scale c) := by
  exact ⟨congrArg (fun φ : 𝓢(ℝ, ℂ) => c • φ) hc.1, hc.2⟩

variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (power firstFixed poolFixed unitFixed : A.Exterior)
variable (firstElement poolElement unitElement : A.R)
variable (hfirst : A.Generates firstFixed firstElement)
variable (hpool : A.Generates poolFixed poolElement)
variable (hunit : A.Generates unitFixed unitElement)
variable (δ₁ δ₂ : ℝ)

local notation "combinedScalar" => (d.commonScalar b *
  (((A.exteriorNorm power ^ δ₁ : ℝ) : ℂ) *
    actualIdealResidue (A := A) (σ := σ) power.val firstElement)) *
      (d.twoStageProfileFactor b δ₁ δ₂ : ℂ)

/-- Actual removal of the two scale factors leaves the same power of
the profile variable in both centered rectangles. This also covers a
zero original common scalar. -/
theorem samePlainProfiles_factorFreeSecondInput (hc : SamePlainProfiles E)
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0) :
    SamePlainProfiles (E.factorFreeSecondInput (σ := σ) b P R
      power firstFixed poolFixed unitFixed firstElement poolElement unitElement
      hfirst hpool hunit δ₁ δ₂ hcompact hpositive) := by
  constructor
  · apply SchwartzMap.ext
    intro y
    change CanonicalLiteralSchwartzProfiles.powerSchwartz window hcompact hpositive
      (combinedScalar⁻¹ * combinedScalar) (CanonicalLiteralProfileScalars.exponent δ₁ δ₂)
      (E.left true) (E.left_support true) y =
      CanonicalLiteralSchwartzProfiles.powerSchwartz window hcompact hpositive
        (combinedScalar⁻¹ * combinedScalar) (CanonicalLiteralProfileScalars.exponent δ₁ δ₂)
        (E.left false) (E.left_support false) y
    rw [CanonicalLiteralSchwartzProfiles.powerSchwartz_apply,
      CanonicalLiteralSchwartzProfiles.powerSchwartz_apply, hc.1]
  · apply SchwartzMap.ext
    intro y
    change CanonicalLiteralSchwartzProfiles.powerSchwartz window hcompact hpositive
      1 (CanonicalLiteralProfileScalars.exponent δ₁ δ₂)
      (E.right true) (E.right_support true) y =
      CanonicalLiteralSchwartzProfiles.powerSchwartz window hcompact hpositive
        1 (CanonicalLiteralProfileScalars.exponent δ₁ δ₂)
        (E.right false) (E.right_support false) y
    rw [CanonicalLiteralSchwartzProfiles.powerSchwartz_apply,
      CanonicalLiteralSchwartzProfiles.powerSchwartz_apply, hc.2]

end CommonProfiles

section OriginalCommonProfiles

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}

/-- Both copies are the same original profile at the same original
row and height. This precedes every child and every Fourier mode. -/
theorem original_samePlainProfiles (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
    (W : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (reference : HeckeGeneral.Analysis.NonzeroIdeal K) (href : (data ξ).allowedRow reference)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
    {seminorms : Finset (ℕ × ℕ)} {bound : ℝ}
    (original : RawProfileWindow rowDomain heightDomain window seminorms (data ξ) bound)
    (hreference : reference ∈ rowDomain) (ht : t ∈ heightDomain)
    (hwindow : window ⊆ Set.Ioi 0) (hclosed : IsClosed window) :
    SamePlainProfiles (Q.literalOriginalSchwartzModel ξ W a Z t Y₁ Y₂ true
      hZ hY₁ hY₂ reference href original hreference ht hwindow hclosed) := ⟨rfl, rfl⟩

end OriginalCommonProfiles

section ActualRows

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable {ω ψ : HeckeCharacter K}
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (C : A.GeneralArithmeticContext σ η hS)
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (S : ActualSecondCorrelationRows A σ H ι) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (hone : (1 : HeckeCharacter K) ∈ parent.theta)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (row : CanonicalOriginalPhaseCalibration.PatternSector P S C pattern ν)
variable (he : S.literalCharacter C P R F oldMoving correction pattern ν
  row.val.val.val ∈ parent.theta)
variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (recipe : CanonicalLiteralActualCharacters.Recipe P R F parent oldMoving
  correction remaining extra d)

/-- Both source sides keep their original full frequency. -/
def signedFrequency (g : A.R) (negative : Bool) : A.R := if negative then -g else g

local notation "actualMask" => CanonicalLiteralExceptionalCharacters.rowMask
  P R F oldMoving C S.primes S.leftMultiplicity S.rightMultiplicity pattern
    (remaining * extra) (S.extractedRow C row.val.val).momentIdeal
local notation "actualCharacter" => CanonicalLiteralExceptionalCharacters.catalogue
  ψ parent.theta (CanonicalLiteralExceptionalCharacters.rowIndex P R F parent
    oldMoving correction C S pattern ν row he)

include hcorr hone hroot hemb recipe in
/-- The original exceptional membership chooses the inducing entry.
The input recipe is the actual composed slot map; its constructors are
already supplied for every literal direct and pooled source. -/
theorem actualCoefficient (negative : Bool) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    sourcePlainCoefficient d.characters.plain d.characters.plainTwist d.characters.mask I *
      actualIdealResidue (A := A) (σ := σ) I.val
        (signedFrequency (S.factor C row.val.val.val) negative *
          (S.extractedRow C row.val.val).element) =
      (if IsCoprime I.val actualMask then (1 : ℂ) else 0) * actualCharacter I.val := by
  rw [recipe.characters]
  cases negative with
  | false =>
      exact CanonicalLiteralExceptionalCharacters.actual_plain_of_exceptional
        P R F parent oldMoving correction hcorr C S pattern ν remaining extra
        recipe.slots.index hone hroot hemb row he I
  | true =>
      exact CanonicalLiteralExceptionalCharacters.actual_negative_plain
        P R F parent oldMoving correction hcorr C S pattern ν remaining extra
        recipe.slots.index hone hroot hemb row
        ⟨S.literalCharacter C P R F oldMoving correction pattern ν row.val.val.val, he⟩ rfl I

variable {W : d.ProfileData} {window : Set ℝ} (E : W.SchwartzModel window)
variable (firstSupport : Finset (Ideal (𝓞 K)))
variable (hfirst : ∀ q ∈ firstSupport, Prime q)
variable (hextra : extra = literalDeletionIdeal firstSupport hfirst)
variable (hm : ∀ i, 0 < S.leftMultiplicity i) (hn : ∀ i, 0 < S.rightMultiplicity i)
variable (support : d.SupportData ((primeSupport A.cS ∪ firstSupport) ∪
  primeSupport (primePowerProduct S.primes S.leftMultiplicity).val))
variable (B : ActualColumnAllocation K k)

include hcorr hone hroot hemb recipe hfirst hextra hm hn support in
/-- The first actual chart contains no supplied exceptional character
identity, support inclusion for the child, or polynomial identity. -/
def actualLeftChart (hplain : B.plain₁ = d.plain₁)
    (negative r : Bool) (firstSign : ℝ) (ξ : Joint) :
    ExceptionalPlainChart (σ := σ) d.characters.plain d.characters.plainTwist
      d.characters.mask (signedFrequency (S.factor C row.val.val.val) negative)
      (S.extractedRow C row.val.val).element actualCharacter actualMask
      (profile firstSign (orientedMode negative ξ) (B.plainDivisor 0) (E.left r))
      (time firstSign (orientedMode negative ξ))
      (d.scale₁ r / idealNorm K (B.plainDivisor 0))
      B.childPlain₁ (fun I => d.rectangleLeftWeight r (B.plainDivisor 0 * I))
      (fun I => CanonicalLiteralProfileData.orientedLocation negative
        (CanonicalLiteralLocations.plain firstSign (B.plainDivisor 0 * I))) ξ :=
  orientChart negative ξ (leftChart E support B _ _ _ _ hplain
    (fun I hI => CanonicalLiteralExceptionalCharacters.rowMask_avoids_original
      P R F oldMoving C S.primes S.leftMultiplicity S.rightMultiplicity pattern
      remaining extra firstSupport hfirst hextra hm hn
      (S.extractedRow C row.val.val).momentIdeal I hI)
    (actualCoefficient P R F parent oldMoving correction hcorr C S pattern ν
      remaining extra hone hroot hemb row he recipe negative)
    r firstSign (orientedMode negative ξ))

include hcorr hone hroot hemb recipe hfirst hextra hm hn support in
/-- The second plain chart uses the same complete mask and catalogue
entry, with its own original quotient scale and divisor. -/
def actualRightChart (hplain : B.plain₂ = d.plain₂)
    (negative r : Bool) (firstSign : ℝ) (ξ : Joint) :
    ExceptionalPlainChart (σ := σ) d.characters.plain d.characters.plainTwist
      d.characters.mask (signedFrequency (S.factor C row.val.val.val) negative)
      (S.extractedRow C row.val.val).element actualCharacter actualMask
      (profile firstSign (orientedMode negative ξ)
        (B.plainDivisor (Fin.succ 0)) (E.right r))
      (time firstSign (orientedMode negative ξ))
      (d.scale₂ r / idealNorm K (B.plainDivisor (Fin.succ 0)))
      B.childPlain₂ (fun I => d.rightWeight r (B.plainDivisor (Fin.succ 0) * I))
      (fun I => CanonicalLiteralProfileData.orientedLocation negative
        (CanonicalLiteralLocations.plain firstSign (B.plainDivisor (Fin.succ 0) * I))) ξ :=
  orientChart negative ξ (rightChart E support B _ _ _ _ hplain
    (fun I hI => CanonicalLiteralExceptionalCharacters.rowMask_avoids_original
      P R F oldMoving C S.primes S.leftMultiplicity S.rightMultiplicity pattern
      remaining extra firstSupport hfirst hextra hm hn
      (S.extractedRow C row.val.val).momentIdeal I hI)
    (actualCoefficient P R F parent oldMoving correction hcorr C S pattern ν
      remaining extra hone hroot hemb row he recipe negative)
    r firstSign (orientedMode negative ξ))

include hcorr hone hroot hemb recipe hfirst hextra hm hn support in
/-- Four actual charts with one pair of smooth profiles. The scale
product is the original centered identity; all quotient denominators
are the literal allocation divisors. The positive lower endpoint is
computed here, rather than supplied as a later exceptional bound. -/
def actualCenteredSource (hplain₁ : B.plain₁ = d.plain₁)
    (hplain₂ : B.plain₂ = d.plain₂) (hc : SamePlainProfiles E)
    (hscale : d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false)
    (negative : Bool) (firstSign : ℝ) (ξ : Joint) :
    AllocatedExceptionalSource (V := Joint) (σ := σ) actualCharacter
      (profile firstSign (orientedMode negative ξ) (B.plainDivisor 0) (E.left false))
      (profile firstSign (orientedMode negative ξ)
        (B.plainDivisor (Fin.succ 0)) (E.right false))
      (signedFrequency (S.factor C row.val.val.val) negative)
      (S.extractedRow C row.val.val).element k := by
  let q₁ (r : Bool) := d.scale₁ r / idealNorm K (B.plainDivisor 0)
  let q₂ (r : Bool) := d.scale₂ r / idealNorm K (B.plainDivisor (Fin.succ 0))
  have hq₁ (r : Bool) : 0 < q₁ r :=
    div_pos (d.scale₁_pos r) (idealNorm_pos K (B.plainDivisor 0))
  have hq₂ (r : Bool) : 0 < q₂ r :=
    div_pos (d.scale₂_pos r) (idealNorm_pos K (B.plainDivisor (Fin.succ 0)))
  let HL (r : Bool) := actualLeftChart P R F parent oldMoving correction hcorr C S
    pattern ν remaining extra hone hroot hemb row he recipe E firstSupport hfirst
    hextra hm hn support B hplain₁ negative r firstSign ξ
  let HR (r : Bool) := actualRightChart P R F parent oldMoving correction hcorr C S
    pattern ν remaining extra hone hroot hemb row he recipe E firstSupport hfirst
    hextra hm hn support B hplain₂ negative r firstSign ξ
  refine {
    allocation := B
    characters := d.characters
    X₁ := d.scale₁ false
    X₂ := d.scale₂ false
    Y₁ := d.scale₁ true
    Y₂ := d.scale₂ true
    Zslot := d.base
    length := d.length
    w₁ := d.rectangleLeftWeight false
    w₂ := d.rightWeight false
    v₁ := d.rectangleLeftWeight true
    v₂ := d.rightWeight true
    w := d.slotWeight
    x₁ := fun I => CanonicalLiteralProfileData.orientedLocation negative
      (CanonicalLiteralLocations.plain firstSign I)
    x₂ := fun I => CanonicalLiteralProfileData.orientedLocation negative
      (CanonicalLiteralLocations.plain firstSign I)
    x := fun j p => CanonicalLiteralProfileData.orientedLocation negative
      (CanonicalLiteralLocations.prime firstSign j p)
    ξ := ξ
    mask := actualMask
    time := time firstSign (orientedMode negative ξ)
    product := q₁ false * q₂ false
    lower := min (min (q₁ false) (q₂ false)) (min (q₁ true) (q₂ true))
    lower_pos := lt_min (lt_min (hq₁ false) (hq₂ false)) (lt_min (hq₁ true) (hq₂ true))
    X₁_lower := (min_le_left _ _).trans (min_le_left _ _)
    X₂_lower := (min_le_left _ _).trans (min_le_right _ _)
    Y₁_lower := (min_le_right _ _).trans (min_le_left _ _)
    Y₂_lower := (min_le_right _ _).trans (min_le_right _ _)
    productX := rfl
    productY := ?_
    chartX₁ := HL false
    chartX₂ := HR false
    chartY₁ := ?_
    chartY₂ := ?_
  }
  · change d.scale₁ true / idealNorm K (B.plainDivisor 0) *
        (d.scale₂ true / idealNorm K (B.plainDivisor (Fin.succ 0))) =
      d.scale₁ false / idealNorm K (B.plainDivisor 0) *
        (d.scale₂ false / idealNorm K (B.plainDivisor (Fin.succ 0)))
    rw [div_mul_div_comm, div_mul_div_comm, hscale]
  · simpa only [hc.1] using HL true
  · simpa only [hc.2] using HR true

include hcorr hone hroot hemb recipe hfirst hextra hm hn support in
/-- The ordinary source only uses its one original rectangle. The
second copy in this carrier is never subtracted when `ordinaryValue`
is read, and no comparison-scale assumption enters the construction. -/
def actualOrdinarySource (hplain₁ : B.plain₁ = d.plain₁)
    (hplain₂ : B.plain₂ = d.plain₂)
    (negative : Bool) (firstSign : ℝ) (ξ : Joint) :
    AllocatedExceptionalSource (V := Joint) (σ := σ) actualCharacter
      (profile firstSign (orientedMode negative ξ) (B.plainDivisor 0) (E.left false))
      (profile firstSign (orientedMode negative ξ)
        (B.plainDivisor (Fin.succ 0)) (E.right false))
      (signedFrequency (S.factor C row.val.val.val) negative)
      (S.extractedRow C row.val.val).element k := by
  let q₁ := d.scale₁ false / idealNorm K (B.plainDivisor 0)
  let q₂ := d.scale₂ false / idealNorm K (B.plainDivisor (Fin.succ 0))
  let HL := actualLeftChart P R F parent oldMoving correction hcorr C S
    pattern ν remaining extra hone hroot hemb row he recipe E firstSupport hfirst
    hextra hm hn support B hplain₁ negative false firstSign ξ
  let HR := actualRightChart P R F parent oldMoving correction hcorr C S
    pattern ν remaining extra hone hroot hemb row he recipe E firstSupport hfirst
    hextra hm hn support B hplain₂ negative false firstSign ξ
  exact {
    allocation := B
    characters := d.characters
    X₁ := d.scale₁ false
    X₂ := d.scale₂ false
    Y₁ := d.scale₁ false
    Y₂ := d.scale₂ false
    Zslot := d.base
    length := d.length
    w₁ := d.rectangleLeftWeight false
    w₂ := d.rightWeight false
    v₁ := d.rectangleLeftWeight false
    v₂ := d.rightWeight false
    w := d.slotWeight
    x₁ := fun I => CanonicalLiteralProfileData.orientedLocation negative
      (CanonicalLiteralLocations.plain firstSign I)
    x₂ := fun I => CanonicalLiteralProfileData.orientedLocation negative
      (CanonicalLiteralLocations.plain firstSign I)
    x := fun j p => CanonicalLiteralProfileData.orientedLocation negative
      (CanonicalLiteralLocations.prime firstSign j p)
    ξ := ξ
    mask := actualMask
    time := time firstSign (orientedMode negative ξ)
    product := q₁ * q₂
    lower := min q₁ q₂
    lower_pos := lt_min
      (div_pos (d.scale₁_pos false) (idealNorm_pos K (B.plainDivisor 0)))
      (div_pos (d.scale₂_pos false) (idealNorm_pos K (B.plainDivisor (Fin.succ 0))))
    X₁_lower := min_le_left _ _
    X₂_lower := min_le_right _ _
    Y₁_lower := min_le_left _ _
    Y₂_lower := min_le_right _ _
    productX := rfl
    productY := rfl
    chartX₁ := HL
    chartX₂ := HR
    chartY₁ := HL
    chartY₂ := HR
  }

variable (hplain₁ : B.plain₁ = d.plain₁) (hplain₂ : B.plain₂ = d.plain₂)
variable (negative : Bool) (firstSign : ℝ) (ξ : Joint)

/-- Reading the constructed value gives the entire literal centered
polynomial, with its common allocation and both original locations.
It does not apply an inequality or replace either rectangle. -/
theorem actualCenteredSource_value (hc : SamePlainProfiles E)
    (hscale : d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false) :
    (actualCenteredSource P R F parent oldMoving correction hcorr C S pattern ν
      remaining extra hone hroot hemb row he recipe E firstSupport hfirst hextra hm hn
      support B hplain₁ hplain₂ hc hscale negative firstSign ξ).value =
    jointFourierColumn B.columns
      (fun i => rawSourceCoefficient (σ := σ) d.characters
        (signedFrequency (S.factor C row.val.val.val) negative)
        (S.extractedRow C row.val.val).element (d.scale₁ false) (d.scale₂ false)
        d.base d.length (d.rectangleLeftWeight false) (d.rightWeight false) d.slotWeight i -
        rawSourceCoefficient (σ := σ) d.characters
          (signedFrequency (S.factor C row.val.val.val) negative)
          (S.extractedRow C row.val.val).element (d.scale₁ true) (d.scale₂ true)
          d.base d.length (d.rectangleLeftWeight true) (d.rightWeight true) d.slotWeight i)
      (rawSourceLocation
        (fun I => CanonicalLiteralProfileData.orientedLocation negative
          (CanonicalLiteralLocations.plain firstSign I))
        (fun I => CanonicalLiteralProfileData.orientedLocation negative
          (CanonicalLiteralLocations.plain firstSign I))
        (fun j p => CanonicalLiteralProfileData.orientedLocation negative
          (CanonicalLiteralLocations.prime firstSign j p))) ξ := rfl

/-- The original ordinary polynomial is read directly, without the
unused comparison scales or a centered-scale hypothesis. -/
theorem actualOrdinarySource_value :
    (actualOrdinarySource P R F parent oldMoving correction hcorr C S pattern ν
      remaining extra hone hroot hemb row he recipe E firstSupport hfirst hextra hm hn
      support B hplain₁ hplain₂ negative firstSign ξ).ordinaryValue =
    jointFourierColumn B.columns
      (rawSourceCoefficient (σ := σ) d.characters
        (signedFrequency (S.factor C row.val.val.val) negative)
        (S.extractedRow C row.val.val).element (d.scale₁ false) (d.scale₂ false)
        d.base d.length (d.rectangleLeftWeight false) (d.rightWeight false) d.slotWeight)
      (rawSourceLocation
        (fun I => CanonicalLiteralProfileData.orientedLocation negative
          (CanonicalLiteralLocations.plain firstSign I))
        (fun I => CanonicalLiteralProfileData.orientedLocation negative
          (CanonicalLiteralLocations.plain firstSign I))
        (fun j p => CanonicalLiteralProfileData.orientedLocation negative
          (CanonicalLiteralLocations.prime firstSign j p))) ξ := rfl

end ActualRows

end CanonicalLiteralExceptionalCharts
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharts.phase_log
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharts.leftChart
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharts.rightChart
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharts.original_samePlainProfiles
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharts.samePlainProfiles_factorFreeSecondInput
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharts.actualCoefficient
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharts.actualLeftChart
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharts.actualRightChart
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharts.actualCenteredSource
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharts.actualOrdinarySource
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharts.actualCenteredSource_value
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalCharts.actualOrdinarySource_value
