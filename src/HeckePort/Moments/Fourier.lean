import HeckePort.Moments.Support

/-!
# Fourier expansion of full-modulus correlations

Port of openai/math `OAI/NumberTheory/DirichletL/Moments/Fourier.lean` (revision `fd4aeeb2`)
from `ℤ[ω]` to `𝓞 K`.

openai uses the trace character `quotientTrace d hd : Residue d → ℂ` of the cubic Eisenstein
field (`ConcreteTraceCRT`), its primitivity
(`GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive`) and its compatibility with scaling
(`quotientTrace_conductor_scale`).  Here the family of additive characters is the structure
`TraceFamily` (the data `ψ d`, primitivity for `d ≠ 0`, and the scaling identity `scale`, which
are precisely those three facts).  Over a number field `K`, `ψ d` is `x ↦ e(Tr(x/(d √D))/…)` for the
different `D`; its construction belongs to the theta layer.

Ported: `frequencyReduction`, `quotientTrace_scaled` (as the field `TraceFamily.scale`),
`residueGauss` (as a finite sum), `fourierSum_scaled`, `gauss_correlation` (openai
`actual_gauss_correlation`), `normalizedResidueGauss` and `normalized_gauss_correlation`.
Not ported: `residueGauss_supported_mk` (identifies `residueGauss` with the sextic Gauss sum of
`ProbePhysical`, specific to the sextic character of `ℤ[ω]`).
-/

noncomputable section

namespace HeckePort.Moments.Fourier

open scoped NumberField BigOperators Classical
open HeckePort.Moments HeckePort.Moments.CommonSupport

variable {K : Type*} [Field K] [NumberField K]

def frequencyReduction (d m : 𝓞 K) (h : d ∣ m) : Residue m →+* Residue d :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr h)

@[simp] theorem frequencyReduction_mk (d m : 𝓞 K) (h : d ∣ m) (x : 𝓞 K) :
    frequencyReduction d m h (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

/-- The additive characters `quotientTrace d` of the residue rings, with the three properties
of openai's file. -/
structure TraceFamily (K : Type*) [Field K] [NumberField K] where
  ψ : ∀ d : 𝓞 K, AddChar (Residue d) ℂ
  prim : ∀ d : 𝓞 K, d ≠ 0 → (ψ d).IsPrimitive
  scale : ∀ (d a m : 𝓞 K) (hm : m = d * a) (h : Residue m) (x : Residue d),
    ψ m (h * scaledResidue d a m hm x) =
      ψ d (frequencyReduction d m (hm ▸ dvd_mul_right d a) h * x)

variable (T : TraceFamily K)

/-- openai `residueGauss`, as a finite sum. -/
def residueGauss (d : 𝓞 K) [Fintype (Residue d)] (χ : MulChar (Residue d) ℂ)
    (h : Residue d) : ℂ :=
  ∑ x : Residue d, χ x * T.ψ d (h * x)

theorem fourierSum_scaled (d a m : 𝓞 K) (hm : m = d * a)
    [Fintype (Residue d)] [Fintype (Residue m)] (χ : MulChar (Residue d) ℂ) (h : Residue m) :
    fourierSum (T.ψ m) (scaledResidue d a m hm) χ h =
      residueGauss T d χ (frequencyReduction d m (hm ▸ dvd_mul_right d a) h) := by
  simp only [fourierSum, residueGauss, T.scale d a m hm]

theorem gauss_correlation (u v : 𝓞 K) (hu : u ≠ 0) (hv : v ≠ 0)
    [Fintype (Residue u)] [Fintype (Residue v)] [Fintype (Residue (u * v))]
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ) (j : 𝓞 K) :
    (∑ h : Residue (u * v),
      residueGauss T u χu (frequencyReduction u (u * v) (dvd_mul_right u v) h) *
        star (residueGauss T v χv (frequencyReduction v (u * v) (dvd_mul_left v u) h)) *
          T.ψ (u * v) (-(h * Ideal.Quotient.mk _ j))) =
      (Fintype.card (Residue (u * v)) : ℂ) * fullModulusCorrelation u v χu χv j := by
  have h := fullModulusCorrelation_fourier u v χu χv j (T.ψ (u * v))
    (T.prim _ (mul_ne_zero hu hv))
  simp_rw [fourierSum_scaled T u v (u * v) rfl,
    fourierSum_scaled T v u (u * v) (mul_comm u v)] at h
  exact h

def normalizedResidueGauss (d : 𝓞 K) [Fintype (Residue d)] (χ : MulChar (Residue d) ℂ)
    (h : Residue d) : ℂ :=
  residueGauss T d χ h / (Real.sqrt (Ideal.absNorm (Ideal.span {d}) : ℝ) : ℂ)

theorem normalized_gauss_correlation (u v : 𝓞 K) (hu : u ≠ 0) (hv : v ≠ 0)
    [Fintype (Residue u)] [Fintype (Residue v)] [Fintype (Residue (u * v))]
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ) (j : 𝓞 K) :
    fullModulusCorrelation u v χu χv j =
      ((Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ) : ℂ))⁻¹ *
      ∑ h : Residue (u * v),
        normalizedResidueGauss T u χu (frequencyReduction u (u * v) (dvd_mul_right u v) h) *
          star (normalizedResidueGauss T v χv
            (frequencyReduction v (u * v) (dvd_mul_left v u) h)) *
          T.ψ (u * v) (-(h * Ideal.Quotient.mk _ j)) := by
  let ru : ℂ := Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ)
  let rv : ℂ := Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ)
  have hqu : (0 : ℝ) < Ideal.absNorm (Ideal.span {u}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hu))
  have hqv : (0 : ℝ) < Ideal.absNorm (Ideal.span {v}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hv))
  have hru : ru ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hqu).ne'
  have hrv : rv ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hqv).ne'
  have hsqu : ru ^ 2 = (Ideal.absNorm (Ideal.span {u}) : ℂ) := by
    dsimp only [ru]
    exact_mod_cast Real.sq_sqrt hqu.le
  have hsqv : rv ^ 2 = (Ideal.absNorm (Ideal.span {v}) : ℂ) := by
    dsimp only [rv]
    exact_mod_cast Real.sq_sqrt hqv.le
  have hcard : (Fintype.card (Residue (u * v)) : ℂ) = (ru * rv) ^ 2 := by
    have hc : Fintype.card (Residue (u * v)) = Ideal.absNorm (Ideal.span {u * v}) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    rw [hc, ← Ideal.span_singleton_mul_span_singleton, map_mul, Nat.cast_mul,
      ← hsqu, ← hsqv, mul_pow]
  have hterm (h : Residue (u * v)) :
      normalizedResidueGauss T u χu (frequencyReduction u (u * v) (dvd_mul_right u v) h) *
        star (normalizedResidueGauss T v χv
          (frequencyReduction v (u * v) (dvd_mul_left v u) h)) *
        T.ψ (u * v) (-(h * Ideal.Quotient.mk _ j)) =
      (residueGauss T u χu (frequencyReduction u (u * v) (dvd_mul_right u v) h) *
        star (residueGauss T v χv (frequencyReduction v (u * v) (dvd_mul_left v u) h)) *
        T.ψ (u * v) (-(h * Ideal.Quotient.mk _ j))) / (ru * rv) := by
    simp only [normalizedResidueGauss, star_div₀, Complex.star_def, Complex.conj_ofReal]
    dsimp only [ru, rv]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_div, gauss_correlation T u v hu hv χu χv j, hcard]
  change _ = (ru * rv)⁻¹ * ((ru * rv) ^ 2 * _ / (ru * rv))
  field_simp

end HeckePort.Moments.Fourier

end
