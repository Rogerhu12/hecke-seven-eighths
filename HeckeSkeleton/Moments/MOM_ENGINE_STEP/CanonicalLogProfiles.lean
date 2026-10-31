import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalLogNormLocations
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentArithmeticAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CompleteRowRecipe
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SlotMeshPreservation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Original profiles with their actual log-norm Fourier factors

The common row translation is removed from the original energy before
using this constructor.  The remaining scale, offset and direction are
fixed single-occurrence data; none has a moving-row argument.  The
Fourier parameter is then arbitrary.

The multiplier uses the actual real power, cast to the complex numbers.
Support preservation is proved only from positivity of the original
profile support.  In particular no nonvanishing claim is made at a
nonpositive profile argument.  At a quotient-ideal norm ratio the scale
is exactly the norm of the original product ideal.

All arithmetic fields and every original slot length are retained.
The norm recipe is constructed from the original profile identity, and
the row, character, arithmetic and slot recipes refer to this literal
profile update.  The existing capacity-child transports can therefore
be applied to the same subsequently chosen children.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

namespace CanonicalLogProfiles

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Parameters of one original occurrence, fixed before the Fourier
variable and independent of the moving arithmetic row. -/
structure Atom (V : Type*) where
  scale : ℝ
  scale_pos : 0 < scale
  exponent : ℝ
  offset : V
  direction : V

namespace Atom

variable (p : Atom V)

def location (y : ℝ) : V := p.offset + Real.log (p.scale * y) • p.direction

def multiplier (ξ : V) (y : ℝ) : ℂ :=
  (((p.scale * y) ^ p.exponent : ℝ) : ℂ) * jointPhase ξ (p.location y)

private theorem phase_ne_zero (ξ x : V) : jointPhase ξ x ≠ 0 := by
  intro h
  have hn := norm_jointPhase ξ x
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

theorem multiplier_ne_zero (ξ : V) {y : ℝ} (hy : 0 < y) :
    p.multiplier ξ y ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast (Real.rpow_pos_of_pos (mul_pos p.scale_pos hy) p.exponent).ne'
  · exact phase_ne_zero ξ (p.location y)

theorem norm_multiplier (ξ : V) {y : ℝ} (hy : 0 < y) :
    ‖p.multiplier ξ y‖ = (p.scale * y) ^ p.exponent := by
  rw [multiplier, norm_mul, norm_jointPhase, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (mul_pos p.scale_pos hy) p.exponent)]

/-- The actual scale cancels before the logarithm or real power is
evaluated.  No approximation of the norm variable is used. -/
theorem multiplier_ratio (ξ : V) (N : ℝ) :
    p.multiplier ξ (N / p.scale) =
      ((N ^ p.exponent : ℝ) : ℂ) *
        jointPhase ξ (p.offset + Real.log N • p.direction) := by
  have hscale : p.scale * (N / p.scale) = N := by
    rw [mul_comm, div_mul_cancel₀ _ p.scale_pos.ne']
  simp only [multiplier, location, hscale]

variable {K : Type} [Field K] [NumberField K]

private theorem idealNorm_mul (B I : NonzeroIdeal K) :
    idealNorm K (B * I) = idealNorm K B * idealNorm K I := by
  change (Ideal.absNorm (B.val * I.val) : ℝ) =
    (Ideal.absNorm B.val : ℝ) * (Ideal.absNorm I.val : ℝ)
  rw [map_mul, Nat.cast_mul]

/-- The child scale is the original scale divided by the actual
allocated ideal norm.  Its multiplier still uses the full original
product ideal, including the divisor occurrence. -/
theorem multiplier_quotient_norm (ξ : V) (B I : NonzeroIdeal K) :
    p.multiplier ξ (idealNorm K I / (p.scale / idealNorm K B)) =
      ((idealNorm K (B * I) ^ p.exponent : ℝ) : ℂ) *
        jointPhase ξ (p.offset + Real.log (idealNorm K (B * I)) • p.direction) := by
  have hscale : p.scale * (idealNorm K I / (p.scale / idealNorm K B)) =
      idealNorm K (B * I) := by
    rw [idealNorm_mul]
    field_simp [p.scale_pos.ne', (idealNorm_pos K B).ne'] <;> ring
  simp only [multiplier, location, hscale]

end Atom

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- Positivity belongs to the original profile window, before any log
multiplier is introduced. -/
def PositivePlainProfile (W : IdealTest K) : Prop :=
  ∀ u t y, W.profile u t y ≠ 0 → 0 < y

def PositivePrimeProfile (W : PrimeWindow K) : Prop :=
  ∀ t y, W.profile t y ≠ 0 → 0 < y

namespace Atom

variable (p : Atom V)

/-- The support is the exact original support at every scale and time. -/
def idealTest (W : IdealTest K) (positive : PositivePlainProfile W) (ξ : V) :
    IdealTest K where
  profile u t y := W.profile u t y * p.multiplier ξ y
  support := W.support
  support_spec u t N I := by
    rw [W.support_spec]
    constructor
    · intro h
      exact mul_ne_zero h (p.multiplier_ne_zero ξ (positive u t _ h))
    · exact left_ne_zero_of_mul

/-- Each prime occurrence keeps its original length and support. -/
def primeWindow (W : PrimeWindow K) (positive : PositivePrimeProfile W) (ξ : V) :
    PrimeWindow K where
  length := W.length
  length_pos := W.length_pos
  profile t y := W.profile t y * p.multiplier ξ y
  support := W.support
  support_spec t N q := by
    rw [W.support_spec]
    constructor
    · intro h
      exact mul_ne_zero h (p.multiplier_ne_zero ξ (positive t _ h))
    · exact left_ne_zero_of_mul

theorem idealTest_positive (W : IdealTest K) (positive : PositivePlainProfile W) (ξ : V) :
    PositivePlainProfile (p.idealTest W positive ξ) := by
  intro u t y h
  exact positive u t y (left_ne_zero_of_mul h)

theorem primeWindow_positive (W : PrimeWindow K) (positive : PositivePrimeProfile W) (ξ : V) :
    PositivePrimeProfile (p.primeWindow W positive ξ) := by
  intro t y h
  exact positive t y (left_ne_zero_of_mul h)

/-- This is the literal single-ideal profile identity needed by the
allocated calibration after the original ideal is written as `B * I`. -/
theorem idealTest_quotient_profile (W : IdealTest K) (positive : PositivePlainProfile W)
    (ξ : V) (u B I : NonzeroIdeal K) (t : ℝ) :
    (p.idealTest W positive ξ).profile u t
        (idealNorm K I / (p.scale / idealNorm K B)) =
      (W.profile u t (idealNorm K I / (p.scale / idealNorm K B)) *
          ((idealNorm K (B * I) ^ p.exponent : ℝ) : ℂ)) *
        jointPhase ξ (p.offset + Real.log (idealNorm K (B * I)) • p.direction) := by
  change W.profile u t _ * p.multiplier ξ _ = _
  rw [p.multiplier_quotient_norm]
  exact (mul_assoc _ _ _).symm

/-- No extra normalization or logarithmic error is inserted into an
original prime occurrence. -/
theorem primeWindow_profile (W : PrimeWindow K) (positive : PositivePrimeProfile W)
    (ξ : V) (q : HeightOneSpectrum (𝓞 K)) (t : ℝ) :
    (p.primeWindow W positive ξ).profile t ((Ideal.absNorm q.asIdeal : ℝ) / p.scale) =
      (W.profile t ((Ideal.absNorm q.asIdeal : ℝ) / p.scale) *
          (((Ideal.absNorm q.asIdeal : ℝ) ^ p.exponent : ℝ) : ℂ)) *
        jointPhase ξ (p.offset + Real.log (Ideal.absNorm q.asIdeal : ℝ) • p.direction) := by
  change W.profile t _ * p.multiplier ξ _ = _
  rw [p.multiplier_ratio]
  exact (mul_assoc _ _ _).symm

end Atom

section Data

variable (d : MomentData K ω ψ)
variable (left right : Atom V) (slot : Fin d.geometry.slotCount → Atom V)
variable (hleft : PositivePlainProfile d.plainTest₁)
variable (hright : PositivePlainProfile d.plainTest₂)
variable (hslot : ∀ i, PositivePrimeProfile (d.geometry.slots i))

/-- This is constructed from the original tests once the common row
phase has been removed from the original energy.  It leaves the inverse
test, arithmetic row recipe, mask and all slot coefficients untouched. -/
def data (ξ : V) : MomentData K ω ψ :=
  { d with
    plainTest₁ := left.idealTest d.plainTest₁ hleft ξ
    plainTest₂ := right.idealTest d.plainTest₂ hright ξ
    geometry :=
      { slotCount := d.geometry.slotCount
        slots i := (slot i).primeWindow (d.geometry.slots i) (hslot i) ξ } }

/-- Norm dependence is derived from the original row-independent tests.
The actual log-norm factor has no moving-row parameter. -/
def normProfiles (W : NormProfileRecipe (fun _ : PUnit => d)) :
    NormProfileRecipe (data d left right slot hleft hright hslot) where
  left ξ t y := W.left PUnit.unit t y * left.multiplier ξ y
  right ξ t y := W.right PUnit.unit t y * right.multiplier ξ y
  left_eq ξ u hu t y := by
    change d.plainTest₁.profile u t y * left.multiplier ξ y = _
    rw [W.left_eq PUnit.unit u hu t y]
  right_eq ξ u hu t y := by
    change d.plainTest₂.profile u t y * right.multiplier ξ y = _
    rw [W.right_eq PUnit.unit u hu t y]

/-- For a literal original parent, the background, theta set and whole
row-character function are preserved by reduction. -/
def parentCharacters :
    ParentCharacterRecipe d (data d left right slot hleft hright hslot) false d.rowCharacter where
  background _ := rfl
  rowCharacter _ := rfl
  theta _ := rfl

/-- If the original branch already carries a whole-conjugation choice,
that same original choice is retained; it is not made after Fourier. -/
def originalParentCharacters {parent : MomentData K ω ψ} {conjugated : Bool}
    {row : NonzeroIdeal K → HeckeCharacter K}
    (original : ParentCharacterRecipe parent (fun _ : PUnit => d) conjugated row) :
    ParentCharacterRecipe parent (data d left right slot hleft hright hslot) conjugated row where
  background _ := original.background PUnit.unit
  rowCharacter _ := original.rowCharacter PUnit.unit
  theta _ := original.theta PUnit.unit

/-- All original allowed rows remain calibrated, including any rows
that become paired rows after the last slot is deleted. -/
def completeRows {A : SArithmeticData K}
    {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
    {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
    (original : CompleteRowRecipe A P R (fun _ : PUnit => d)) :
    CompleteRowRecipe A P R (data d left right slot hleft hright hslot) where
  sector := original.sector
  exterior _ u hu := original.exterior PUnit.unit u hu
  character _ u hu := original.character PUnit.unit u hu

/-- The individual arithmetic identities are unchanged, with their
original row map, zero extensions, masks and phase arrays. -/
def arithmeticAtoms {Q : Type*} (original : ParentArithmeticAtoms Q d) (ξ : V) :
    ParentArithmeticAtoms Q (data d left right slot hleft hright hslot ξ) :=
  original.transport _ id (fun _ h => h) rfl rfl rfl (fun _ => rfl)

/-- Every slot remains the same original occurrence.  This can be
composed with an earlier original-slot embedding before capacity. -/
def slots (ξ : V) : SlotLengthEmbedding d (data d left right slot hleft hright hslot ξ) where
  index := ⟨fun i => i, fun _ _ h => h⟩
  length_eq _ := rfl

def originalSlots {parent : MomentData K ω ψ}
    (original : SlotLengthEmbedding parent d) (ξ : V) :
    SlotLengthEmbedding parent (data d left right slot hleft hright hslot ξ) where
  index := original.index
  length_eq := original.length_eq

/-- The single-ideal and single-prime arithmetic dictionary is exactly
the old one; only the explicitly displayed profiles were multiplied. -/
def termCalibration {A : SArithmeticData K} {σ : K →+* ℂ} {k : ℕ}
    {T : FixedChildCharacters K k} {count : d.geometry.slotCount = k}
    {u : NonzeroIdeal K} {g h : A.R}
    (original : T.Calibration (σ := σ) d count u g h) (ξ : V) :
    T.Calibration (σ := σ) (data d left right slot hleft hright hslot ξ) count u g h where
  fixedRay_mem_theta := original.fixedRay_mem_theta
  plain := original.plain
  slot := original.slot

end Data
end CanonicalLogProfiles
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.Atom.multiplier_quotient_norm
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.Atom.idealTest_quotient_profile
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.normProfiles
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.completeRows
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.arithmeticAtoms
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.originalSlots
