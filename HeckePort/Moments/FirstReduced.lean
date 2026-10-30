import HeckePort.Moments.FirstMixed
import HeckePort.Moments.Active

/-!
# Triple rows and their Poisson transform

Port of the formal part of openai/math `OAI/NumberTheory/DirichletL/Moments/FirstReduced.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`, over the trace family `Fourier.TraceFamily` and the
Poisson datum `Poisson.RadialPoissonData`.

Ported: `tripleRow`, `tripleResidue`, `tripleRow_mul`, `tripleFourier` (as a finite sum) and
`tripleRow_poisson` (the radial Poisson identity for a triple row, from the datum).  Not ported:
`tripleRow_radial_summable` (summability of the lattice sum, by
`actual_eisenstein_periodic_summable`), `masked_triple_poisson` (uses `tsum_masked_radial_dilations`,
the dilation structure of the `ℤ[ω]` lattice sum), `principalSexticRow_mul` and
`common_residual_reduced_poisson` (sextic row `principalSexticRow` and the masked dilations).
-/

noncomputable section

namespace HeckePort.Moments.FirstReduced

open scoped NumberField BigOperators Classical SchwartzMap
open HeckePort.Moments HeckePort.Moments.CommonSupport HeckePort.Moments.Fourier
open HeckePort.Moments.Poisson

variable {K : Type*} [Field K] [NumberField K]

def tripleRow (a b r : 𝓞 K) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ) (z : 𝓞 K) : ℂ :=
  χa (Ideal.Quotient.mk _ z) * χb (Ideal.Quotient.mk _ z) * G (Ideal.Quotient.mk _ z)

def tripleResidue (a b r : 𝓞 K) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ) (x : Residue (a * (b * r))) : ℂ :=
  χa (frequencyReduction a _ (dvd_mul_right _ _) x) *
    χb (frequencyReduction b _ (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x) *
    G (frequencyReduction r _ (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x)

@[simp] theorem tripleResidue_mk (a b r : 𝓞 K) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ) (z : 𝓞 K) :
    tripleResidue a b r χa χb G (Ideal.Quotient.mk _ z) = tripleRow a b r χa χb G z := by
  simp only [tripleResidue, tripleRow, frequencyReduction_mk]

theorem tripleRow_mul (a b r : 𝓞 K) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ)
    (hG : ∀ x y, G (x * y) = G x * G y) (x y : 𝓞 K) :
    tripleRow a b r χa χb G (x * y) = tripleRow a b r χa χb G x * tripleRow a b r χa χb G y := by
  simp only [tripleRow, map_mul, hG]
  ring

variable (T : TraceFamily K)

def tripleFourier (a b r : 𝓞 K) [Fintype (Residue (a * (b * r)))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (h : 𝓞 K) : ℂ :=
  ∑ x : Residue (a * (b * r)), tripleResidue a b r χa χb G x *
    T.ψ (a * (b * r)) (Ideal.Quotient.mk _ h * x)

variable {T} (R : RadialPoissonData T)

theorem tripleRow_poisson (a b r : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0) (hr : r ≠ 0)
    [Fintype (Residue (a * (b * r)))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (W : 𝓢(ℝ, ℂ)) (Kk : ℝ) (hK : 0 < Kk) :
    (∑' z : 𝓞 K, tripleRow a b r χa χb G z * W (R.norm2 z / Kk)) =
      ((Kk / R.norm2 (a * (b * r)) : ℝ) : ℂ) * ∑' h : 𝓞 K,
        tripleFourier T a b r χa χb G h *
          R.transform W (Kk * R.norm2 h / R.norm2 (a * (b * r))) := by
  have hh := R.poisson (a * (b * r)) (mul_ne_zero ha (mul_ne_zero hb hr))
    (tripleResidue a b r χa χb G) W Kk hK
  simpa only [tripleResidue_mk, tripleFourier, Complex.real_smul] using hh

end HeckePort.Moments.FirstReduced

end
