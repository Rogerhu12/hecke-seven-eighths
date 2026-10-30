import HeckePort.Moments.FirstPoisson

/-!
# Three-factor mixed Fourier transform

Port of openai/math `OAI/NumberTheory/DirichletL/Moments/FirstMixed.lean` (revision `fd4aeeb2`)
from `ℤ[ω]` to `𝓞 K`, over the trace family `Fourier.TraceFamily`.  The two-factor input
`ProbePhysical.coprime_mixed_fourier` (not in the shared set) is `FirstPoisson.coprime_mixed_fourier`.
The non-vanishing hypotheses `a, b, c ≠ 0` of openai (used to define `quotientTrace`) are not needed.
-/

noncomputable section

namespace HeckePort.Moments.FirstMixed

open scoped NumberField BigOperators Classical
open HeckePort.Moments HeckePort.Moments.CommonSupport HeckePort.Moments.Fourier
open HeckePort.Moments.FirstPoisson

variable {K : Type*} [Field K] [NumberField K]

theorem frequencyReduction_comp (d n M : 𝓞 K) (hd : d ∣ n) (hn : n ∣ M) (x : Residue M) :
    frequencyReduction d n hd (frequencyReduction n M hn x) =
      frequencyReduction d M (hd.trans hn) x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [frequencyReduction_mk]

theorem three_factor_mixed_fourier (T : TraceFamily K) (a b c : 𝓞 K)
    (habc : IsCoprime a (b * c)) (hbc : IsCoprime b c)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue c)]
    [Fintype (Residue (b * c))] [Fintype (Residue (a * (b * c)))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (G : Residue c → ℂ)
    (h : Residue (a * (b * c))) :
    (∑ x : Residue (a * (b * c)),
      χa (frequencyReduction a (a * (b * c)) (dvd_mul_right _ _) x) *
      χb (frequencyReduction b (a * (b * c)) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x) *
      G (frequencyReduction c (a * (b * c)) (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x) *
        T.ψ (a * (b * c)) (h * x)) =
      χa (Ideal.Quotient.mk _ (b * c)) * χb (Ideal.Quotient.mk _ (a * c)) *
        residueGauss T a χa (frequencyReduction a (a * (b * c)) (dvd_mul_right _ _) h) *
        residueGauss T b χb
          (frequencyReduction b (a * (b * c)) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) h) *
        (∑ y : Residue c, G (Ideal.Quotient.mk _ (a * b) * y) *
          T.ψ c (frequencyReduction c (a * (b * c))
            (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) h * y)) := by
  let F : Residue (b * c) → ℂ := fun y =>
    χb (frequencyReduction b (b * c) (dvd_mul_right _ _) y) *
      G (frequencyReduction c (b * c) (dvd_mul_left _ _) y)
  let h' := frequencyReduction (b * c) (a * (b * c)) (dvd_mul_left _ _) h
  have he (x : Residue (a * (b * c))) :
      χa (frequencyReduction a (a * (b * c)) (dvd_mul_right _ _) x) *
        F (frequencyReduction (b * c) (a * (b * c)) (dvd_mul_left _ _) x) =
      χa (frequencyReduction a (a * (b * c)) (dvd_mul_right _ _) x) *
        χb (frequencyReduction b (a * (b * c)) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x) *
        G (frequencyReduction c (a * (b * c)) (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x) := by
    dsimp only [F]
    rw [frequencyReduction_comp, frequencyReduction_comp]
    ring
  simp_rw [← he]
  rw [coprime_mixed_fourier T a (b * c) habc χa F h]
  have hf (y : Residue (b * c)) : F (Ideal.Quotient.mk _ a * y) =
      χb (Ideal.Quotient.mk _ a) *
        (χb (frequencyReduction b (b * c) (dvd_mul_right _ _) y) *
          G (Ideal.Quotient.mk _ a * frequencyReduction c (b * c) (dvd_mul_left _ _) y)) := by
    simp only [F, map_mul, frequencyReduction_mk]
    ring
  simp_rw [hf, mul_assoc]
  rw [← Finset.mul_sum]
  have hh := coprime_mixed_fourier T b c hbc χb
    (fun y => G (Ideal.Quotient.mk _ a * y)) h'
  simp only [mul_assoc] at hh
  rw [hh]
  simp only [h', frequencyReduction_comp, map_mul, mul_assoc]
  ring

end HeckePort.Moments.FirstMixed

end
