import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralLocations

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Global profiles at the actual logarithmic Fourier locations

The logarithm is taken at the norm of the original ideal, including
both extracted plain divisors. Its constant scale contribution is the
translation of the global profile formula. The original representative,
dilation, power and scalar are retained at every real argument.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

namespace ProfileFormula

@[simp] theorem linear_zero (a : ℝ × ℝ) : linear a 0 = 0 := by
  change a.1 * 0 + a.2 * 0 = 0
  simp

@[simp] theorem value_zero (f : ProfileFormula) (x : ℝ) :
    f.value 0 x = if 0 < x then
      f.scalar *
        (if f.conjugate then star (f.original (f.dilation * x))
         else f.original (f.dilation * x)) * (x ^ f.power : ℝ) else 0 := by
  simp only [value, linear_zero, zero_mul, zero_add, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, mul_one]

/-- The actual linear logarithmic phase of one occurrence. -/
def withLogPhase (f : ProfileFormula) (a b : ℝ × ℝ) : ProfileFormula :=
  { f with phase := a, translation := b }

theorem logPhase_inner (a b : ℝ × ℝ) (ξ : EngineParameter) (x : ℝ) :
    inner ℝ ξ (WithLp.toLp 2 b + Real.log x • WithLp.toLp 2 a) =
      linear a ξ * Real.log x + linear b ξ := by
  rw [inner_add_right, real_inner_smul_right]
  simp only [WithLp.prod_inner_apply, WithLp.ofLp_toLp, Real.inner_apply, linear]
  ring

/-- This equality is global, including the zero extension on the
nonpositive real axis. -/
theorem withLogPhase_value (f : ProfileFormula) (a b : ℝ × ℝ)
    (ξ : EngineParameter) (x : ℝ) :
    (f.withLogPhase a b).value ξ x = f.value 0 x *
      jointPhase ξ (WithLp.toLp 2 b + Real.log x • WithLp.toLp 2 a) := by
  rw [jointPhase, Real.fourierChar_apply, logPhase_inner, value_zero]
  by_cases hx : 0 < x
  · simp only [value, withLogPhase, hx, if_true]
  · simp only [value, withLogPhase, hx, if_false, zero_mul]

/-- The translation records the original scale, before any divisor
extraction. It is not a freely chosen Fourier normalizer. -/
def atScale (f : ProfileFormula) (a : ℝ × ℝ) (scale : ℝ) : ProfileFormula :=
  f.withLogPhase a (a.1 * Real.log scale, a.2 * Real.log scale)

theorem value_zero_ne_zero_of_atScale (f : ProfileFormula) (a : ℝ × ℝ)
    (scale : ℝ) (ξ : EngineParameter) (x : ℝ)
    (h : (f.atScale a scale).value ξ x ≠ 0) : f.value 0 x ≠ 0 := by
  rw [atScale, withLogPhase_value] at h
  exact left_ne_zero_of_mul h

theorem scale_translation (a : ℝ × ℝ) (scale : ℝ) :
    WithLp.toLp 2 (a.1 * Real.log scale, a.2 * Real.log scale) =
      Real.log scale • WithLp.toLp 2 a := by
  change WithLp.toLp 2 (a.1 * Real.log scale, a.2 * Real.log scale) =
    WithLp.toLp 2 (Real.log scale * a.1, Real.log scale * a.2)
  congr 1
  apply Prod.ext <;> dsimp <;> ring

theorem atScale_value (f : ProfileFormula) (a : ℝ × ℝ)
    (scale : ℝ) (hscale : 0 < scale) (ξ : EngineParameter) (x : ℝ) :
    (f.atScale a scale).value ξ x =
      f.value 0 x * jointPhase ξ (Real.log (scale * x) • WithLp.toLp 2 a) := by
  rw [atScale, withLogPhase_value]
  by_cases hx : 0 < x
  · rw [scale_translation, ← add_smul, Real.log_mul hscale.ne' hx.ne']
  · simp only [value_zero, hx, if_false, zero_mul]

theorem atScale_ratio (f : ProfileFormula) (a : ℝ × ℝ)
    (scale : ℝ) (hscale : 0 < scale) (ξ : EngineParameter) (norm : ℝ) :
    (f.atScale a scale).value ξ (norm / scale) =
      f.value 0 (norm / scale) * jointPhase ξ (Real.log norm • WithLp.toLp 2 a) := by
  rw [atScale_value f a scale hscale]
  have hcancel : scale * (norm / scale) = norm := by
    rw [mul_comm, div_mul_cancel₀ _ hscale.ne']
  rw [hcancel]

variable {K : Type} [Field K] [NumberField K]

theorem norm_mul (B I : NonzeroIdeal K) :
    idealNorm K (B * I) = idealNorm K B * idealNorm K I := by
  change (Ideal.absNorm (B.val * I.val) : ℝ) =
    (Ideal.absNorm B.val : ℝ) * (Ideal.absNorm I.val : ℝ)
  rw [map_mul, Nat.cast_mul]

theorem divided_scale_argument (B I : NonzeroIdeal K) (scale : ℝ) :
    idealNorm K I / (scale / idealNorm K B) = idealNorm K (B * I) / scale := by
  rw [norm_mul, quotient_argument]
  ring

/-- Quotienting by an actual ideal changes the profile argument, while
the Fourier phase still sees the full original product ideal. -/
theorem atScale_quotient (f : ProfileFormula) (a : ℝ × ℝ)
    (scale : ℝ) (hscale : 0 < scale) (ξ : EngineParameter) (B I : NonzeroIdeal K) :
    (f.atScale a scale).value ξ (idealNorm K I / (scale / idealNorm K B)) =
      f.value 0 (idealNorm K (B * I) / scale) *
        jointPhase ξ (Real.log (idealNorm K (B * I)) • WithLp.toLp 2 a) := by
  rw [divided_scale_argument]
  exact atScale_ratio f a scale hscale ξ _

/-- Both original signs occur before Fourier separation. -/
def signedDirection (side : Bool) (firstSign : ℝ) : ℝ × ℝ :=
  if side then (firstSign, 1) else (-firstSign, -1)

theorem signedDirection_plain (side : Bool) (firstSign : ℝ) (I : NonzeroIdeal K) :
    Real.log (idealNorm K I) • WithLp.toLp 2 (signedDirection side firstSign) =
      if side then -CanonicalLiteralLocations.plain firstSign I
      else CanonicalLiteralLocations.plain firstSign I := by
  cases side
  · change WithLp.toLp 2 (Real.log (idealNorm K I) * -firstSign,
      Real.log (idealNorm K I) * -1) =
      WithLp.toLp 2 (-Real.log (idealNorm K I) * firstSign,
        -Real.log (idealNorm K I) * 1)
    congr 1
    apply Prod.ext <;> dsimp <;> ring
  · change Real.log (idealNorm K I) • WithLp.toLp 2 (firstSign, 1) =
      -(-Real.log (idealNorm K I) • WithLp.toLp 2 (firstSign, 1))
    rw [neg_smul, neg_neg]

theorem signedDirection_prime {k : ℕ} (side : Bool) (firstSign : ℝ)
    (i : Fin k) (q : HeightOneSpectrum (𝓞 K)) :
    Real.log (Ideal.absNorm q.asIdeal : ℝ) • WithLp.toLp 2
        (signedDirection side firstSign) =
      if side then -CanonicalLiteralLocations.prime firstSign i q
      else CanonicalLiteralLocations.prime firstSign i q := by
  cases side
  · change WithLp.toLp 2 (Real.log (Ideal.absNorm q.asIdeal : ℝ) * -firstSign,
      Real.log (Ideal.absNorm q.asIdeal : ℝ) * -1) =
      WithLp.toLp 2 (-Real.log (Ideal.absNorm q.asIdeal : ℝ) * firstSign,
        -Real.log (Ideal.absNorm q.asIdeal : ℝ) * 1)
    congr 1
    apply Prod.ext <;> dsimp <;> ring
  · change Real.log (Ideal.absNorm q.asIdeal : ℝ) • WithLp.toLp 2 (firstSign, 1) =
      -(-Real.log (Ideal.absNorm q.asIdeal : ℝ) • WithLp.toLp 2 (firstSign, 1))
    rw [neg_smul, neg_neg]

theorem actual_plain (f : ProfileFormula) (side : Bool) (firstSign scale : ℝ)
    (hscale : 0 < scale) (ξ : EngineParameter) (B I : NonzeroIdeal K) :
    (f.atScale (signedDirection side firstSign) scale).value ξ
        (idealNorm K I / (scale / idealNorm K B)) =
      f.value 0 (idealNorm K (B * I) / scale) *
        jointPhase ξ (if side then -CanonicalLiteralLocations.plain firstSign (B * I)
          else CanonicalLiteralLocations.plain firstSign (B * I)) := by
  rw [atScale_quotient f _ scale hscale, signedDirection_plain]

theorem actual_prime {k : ℕ} (f : ProfileFormula) (side : Bool)
    (firstSign scale : ℝ) (hscale : 0 < scale) (ξ : EngineParameter)
    (i : Fin k) (q : HeightOneSpectrum (𝓞 K)) :
    (f.atScale (signedDirection side firstSign) scale).value ξ
        ((Ideal.absNorm q.asIdeal : ℝ) / scale) =
      f.value 0 ((Ideal.absNorm q.asIdeal : ℝ) / scale) *
        jointPhase ξ (if side then -CanonicalLiteralLocations.prime firstSign i q
          else CanonicalLiteralLocations.prime firstSign i q) := by
  rw [atScale_ratio f _ scale hscale, signedDirection_prime side firstSign i q]

end ProfileFormula

namespace OriginalProfileFormula

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {input : ProfileInput call}

/-- The named original representative and its row and time are retained. -/
def atScale (f : OriginalProfileFormula input) (a : ℝ × ℝ) (scale : ℝ) :
    OriginalProfileFormula input where
  kind := f.kind
  row := f.row
  time := f.time
  formula := f.formula.atScale a scale
  original := f.original

@[simp] theorem atScale_kind (f : OriginalProfileFormula input)
    (a : ℝ × ℝ) (scale : ℝ) : (f.atScale a scale).kind = f.kind := rfl

@[simp] theorem atScale_scalar (f : OriginalProfileFormula input)
    (a : ℝ × ℝ) (scale : ℝ) :
    (f.atScale a scale).formula.scalar = f.formula.scalar := rfl

@[simp] theorem atScale_dilation (f : OriginalProfileFormula input)
    (a : ℝ × ℝ) (scale : ℝ) :
    (f.atScale a scale).formula.dilation = f.formula.dilation := rfl

end OriginalProfileFormula

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.ProfileFormula.withLogPhase_value
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.ProfileFormula.actual_plain
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.ProfileFormula.actual_prime
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalProfileFormula.atScale
