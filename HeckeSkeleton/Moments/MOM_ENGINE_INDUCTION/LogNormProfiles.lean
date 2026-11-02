import HeckeGeneral.Analysis.TInputSeparatedProfiles
import Mathlib.Analysis.Complex.Circle

/-!
# Log-norm Fourier columns as actual moment profiles

The scalar Fourier phase `exp (2π i ξ log y)` is a pure imaginary
`profilePower`.  The existing `freezeTwist` and `separatedProfiles`
constructors therefore realize these columns as actual `IdealTest` and
`PrimeWindow` values, with their exact original finite supports.

These are the termwise profile equalities required by the child dictionary
when its location is the logarithm of the norm ratio.  They do not apply to
an arbitrary additive embedding coordinate.  The transform producer must
still identify its kernel chart with these scalar norm coordinates and
control the resulting profile family uniformly.  Prime frequencies and
times remain fixed per slot, independently of the moving arithmetic row.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open scoped BigOperators Classical

variable {K : Type} [Field K] [NumberField K]

/-- The complex power corresponding to the analyst's Fourier convention. -/
def logNormPower (ξ : ℝ) : ℂ := (2 * Real.pi * ξ : ℝ) * Complex.I

/-- A scalar phase depending only on the norm ratio. -/
def logNormPhase (ξ y : ℝ) : ℂ := (Real.fourierChar (ξ * Real.log y) : ℂ)

theorem profilePower_logNorm (ξ y : ℝ) :
    profilePower (logNormPower ξ) y = logNormPhase ξ y := by
  simp only [profilePower, logNormPower, logNormPhase, Real.fourierChar_apply,
    Complex.ofReal_mul]
  congr 1
  ring

@[simp] theorem logNormPhase_norm (ξ y : ℝ) : ‖logNormPhase ξ y‖ = 1 :=
  Circle.norm_coe _

/-- Pure imaginary powers preserve the exact profile supremum used in the
absolute width-floor estimate, for arbitrary Fourier frequency. -/
theorem idealTest_logNorm_profile_norm (W : IdealTest K)
    (time frequency : NonzeroIdeal K → ℝ) (u : NonzeroIdeal K) (t y : ℝ) :
    ‖(W.freezeTwist time (fun v => logNormPower (frequency v))).profile u t y‖ =
      ‖W.profile u (time u) y‖ := by
  simp only [IdealTest.freezeTwist, norm_mul, profilePower_logNorm, logNormPhase_norm, mul_one]

theorem primeWindow_logNorm_profile_norm (W : PrimeWindow K) (time frequency t y : ℝ) :
    ‖(W.freezeTwist time (logNormPower frequency)).profile t y‖ = ‖W.profile time y‖ := by
  simp only [PrimeWindow.freezeTwist, norm_mul, profilePower_logNorm, logNormPhase_norm, mul_one]

/-- Annular support as a function of the real ratio is also unchanged. -/
theorem idealTest_logNorm_profile_support (W : IdealTest K)
    (time frequency : NonzeroIdeal K → ℝ) (u : NonzeroIdeal K) (t : ℝ) :
    Function.support ((W.freezeTwist time (fun v => logNormPower (frequency v))).profile u t) =
      Function.support (W.profile u (time u)) := by
  ext y
  change (W.profile u (time u) y * profilePower (logNormPower (frequency u)) y ≠ 0) ↔
    W.profile u (time u) y ≠ 0
  exact ⟨left_ne_zero_of_mul, fun h => mul_ne_zero h (profilePower_ne_zero _ _)⟩

theorem primeWindow_logNorm_profile_support (W : PrimeWindow K) (time frequency t : ℝ) :
    Function.support ((W.freezeTwist time (logNormPower frequency)).profile t) =
      Function.support (W.profile time) := by
  ext y
  change (W.profile time y * profilePower (logNormPower frequency) y ≠ 0) ↔
    W.profile time y ≠ 0
  exact ⟨left_ne_zero_of_mul, fun h => mul_ne_zero h (profilePower_ne_zero _ _)⟩

/-- This equality has the `weight * phase = new profile` orientation used
by the actual child-term dictionary. -/
theorem idealTest_logNorm_calibration (W : IdealTest K)
    (time frequency : NonzeroIdeal K → ℝ) (u I : NonzeroIdeal K) (N t : ℝ) :
    W.profile u (time u) (idealNorm K I / N) *
        logNormPhase (frequency u) (idealNorm K I / N) =
      (W.freezeTwist time (fun v => logNormPower (frequency v))).profile
        u t (idealNorm K I / N) := by
  simp only [IdealTest.freezeTwist, profilePower_logNorm]

/-- A prime phase uses one frequency for the whole slot. -/
theorem primeWindow_logNorm_calibration (W : PrimeWindow K)
    (time frequency P t : ℝ) (p : HeightOneSpectrum (𝓞 K)) :
    W.profile time ((Ideal.absNorm p.asIdeal : ℝ) / P) *
        logNormPhase frequency ((Ideal.absNorm p.asIdeal : ℝ) / P) =
      (W.freezeTwist time (logNormPower frequency)).profile
        t ((Ideal.absNorm p.asIdeal : ℝ) / P) := by
  simp only [PrimeWindow.freezeTwist, profilePower_logNorm]

variable {ω ψ : HeckeCharacter K}

/-- Actual separated data at a common interface time.  Only norm profiles
change; arithmetic coefficients, rows, masks and slot lengths are retained. -/
def logNormSeparatedProfiles (d : MomentData K ω ψ)
    (inverseTime plainTime₁ plainTime₂ : NonzeroIdeal K → ℝ)
    (inverseFrequency plainFrequency₁ plainFrequency₂ : NonzeroIdeal K → ℝ)
    (slotTime slotFrequency : Fin d.geometry.slotCount → ℝ) : MomentData K ω ψ :=
  d.separatedProfiles inverseTime plainTime₁ plainTime₂
    (fun u => logNormPower (inverseFrequency u))
    (fun u => logNormPower (plainFrequency₁ u))
    (fun u => logNormPower (plainFrequency₂ u))
    slotTime (fun i => logNormPower (slotFrequency i))

variable (d : MomentData K ω ψ)
    (inverseTime plainTime₁ plainTime₂ : NonzeroIdeal K → ℝ)
    (inverseFrequency plainFrequency₁ plainFrequency₂ : NonzeroIdeal K → ℝ)
    (slotTime slotFrequency : Fin d.geometry.slotCount → ℝ)

local notation "d'" => logNormSeparatedProfiles d inverseTime plainTime₁ plainTime₂
  inverseFrequency plainFrequency₁ plainFrequency₂ slotTime slotFrequency

@[simp] theorem logNormSeparatedProfiles_mask (u : NonzeroIdeal K) (I : Ideal (𝓞 K)) :
    maskValue d' u I = maskValue d u I := rfl

@[simp] theorem logNormSeparatedProfiles_rows (a : RealParameters) (Z : ℝ) :
    pairedRows d' a Z = pairedRows d a Z := rfl

@[simp] theorem logNormSeparatedProfiles_rowCharacter (u : NonzeroIdeal K) :
    (d').rowCharacter u = d.rowCharacter u := rfl

@[simp] theorem logNormSeparatedProfiles_slotCount :
    (d').geometry.slotCount = d.geometry.slotCount := rfl

@[simp] theorem logNormSeparatedProfiles_slotLength (i : Fin d.geometry.slotCount) :
    ((d').geometry.slots i).length = (d.geometry.slots i).length := rfl

@[simp] theorem logNormSeparatedProfiles_totalLength :
    (d').geometry.totalLength = d.geometry.totalLength := rfl

@[simp] theorem logNormSeparatedProfiles_fitsMesh (mesh : ℝ) :
    (d').geometry.fitsMesh mesh ↔ d.geometry.fitsMesh mesh := Iff.rfl

theorem logNormSeparatedProfiles_plain₁ (u I : NonzeroIdeal K) (N t : ℝ) :
    d.plainTest₁.profile u (plainTime₁ u) (idealNorm K I / N) *
        logNormPhase (plainFrequency₁ u) (idealNorm K I / N) =
      (d').plainTest₁.profile u t (idealNorm K I / N) := by
  exact idealTest_logNorm_calibration d.plainTest₁ plainTime₁ plainFrequency₁ u I N t

theorem logNormSeparatedProfiles_plain₂ (u I : NonzeroIdeal K) (N t : ℝ) :
    d.plainTest₂.profile u (plainTime₂ u) (idealNorm K I / N) *
        logNormPhase (plainFrequency₂ u) (idealNorm K I / N) =
      (d').plainTest₂.profile u t (idealNorm K I / N) := by
  exact idealTest_logNorm_calibration d.plainTest₂ plainTime₂ plainFrequency₂ u I N t

theorem logNormSeparatedProfiles_prime (i : Fin d.geometry.slotCount)
    (p : HeightOneSpectrum (𝓞 K)) (P t : ℝ) :
    (d.geometry.slots i).profile (slotTime i) ((Ideal.absNorm p.asIdeal : ℝ) / P) *
        logNormPhase (slotFrequency i) ((Ideal.absNorm p.asIdeal : ℝ) / P) =
      ((d').geometry.slots i).profile t ((Ideal.absNorm p.asIdeal : ℝ) / P) := by
  exact primeWindow_logNorm_calibration (d.geometry.slots i)
    (slotTime i) (slotFrequency i) P t p

/-- The complete first plain polynomial, including the original common
mask and literal Hecke coefficient, is the separated Fourier column. -/
theorem logNormSeparatedProfiles_plainPolynomial₁ (u : NonzeroIdeal K) (N : ℝ) :
    plainPolynomial d' (d').plainTest₁ u N 0 =
      (Real.sqrt N : ℂ)⁻¹ * ∑ I ∈ d.plainTest₁.support u (plainTime₁ u) N,
        heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I *
          (d.plainTest₁.profile u (plainTime₁ u) (idealNorm K I / N) *
            logNormPhase (plainFrequency₁ u) (idealNorm K I / N)) *
          maskValue d u I.val := by
  simp only [plainPolynomial, logNormSeparatedProfiles, MomentData.separatedProfiles,
    IdealTest.freezeTwist, profilePower_logNorm, maskValue] <;> rfl

theorem logNormSeparatedProfiles_plainPolynomial₂ (u : NonzeroIdeal K) (N : ℝ) :
    plainPolynomial d' (d').plainTest₂ u N 0 =
      (Real.sqrt N : ℂ)⁻¹ * ∑ I ∈ d.plainTest₂.support u (plainTime₂ u) N,
        heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I *
          (d.plainTest₂.profile u (plainTime₂ u) (idealNorm K I / N) *
            logNormPhase (plainFrequency₂ u) (idealNorm K I / N)) *
          maskValue d u I.val := by
  simp only [plainPolynomial, logNormSeparatedProfiles, MomentData.separatedProfiles,
    IdealTest.freezeTwist, profilePower_logNorm, maskValue] <;> rfl

/-- The slot polynomial retains its slot coefficient and common mask. -/
theorem logNormSeparatedProfiles_primePolynomial (i : Fin d.geometry.slotCount)
    (u : NonzeroIdeal K) (Z : ℝ) :
    primePolynomial d' i u Z 0 =
      let P := Z ^ (d.geometry.slots i).length
      (Real.sqrt P : ℂ)⁻¹ * ∑ p ∈ (d.geometry.slots i).support (slotTime i) P,
        primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p *
          ((d.geometry.slots i).profile (slotTime i) ((Ideal.absNorm p.asIdeal : ℝ) / P) *
            logNormPhase (slotFrequency i) ((Ideal.absNorm p.asIdeal : ℝ) / P)) *
          maskValue d u p.asIdeal := by
  simp only [primePolynomial, logNormSeparatedProfiles, MomentData.separatedProfiles,
    SlotGeometry.freezeTwists, PrimeWindow.freezeTwist, profilePower_logNorm, maskValue] <;> rfl

end HeckeSkeleton.Moments.EngineInduction
