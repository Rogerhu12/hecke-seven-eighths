import HeckePort.Moments.Poisson

/-!
# The first Poisson step: coprime pairs of characters

Port of openai/math `OAI/NumberTheory/DirichletL/Moments/FirstPoisson.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`, over the trace family `Fourier.TraceFamily` and the
Poisson datum `Poisson.RadialPoissonData` (see `Moments/Fourier`, `Moments/Poisson`).

`coprime_mixed_fourier` is the Fourier transform of a product of a character modulo `a` and an
arbitrary function modulo `b` over `𝓞 / (a b)` for coprime `a, b`; it generalizes openai's
`coprime_character_fourier` (the case of a character modulo `b`, derived below) and also
`ProbePhysical.coprime_mixed_fourier` used by `Moments/FirstMixed`.
-/

noncomputable section

namespace HeckePort.Moments.FirstPoisson

open scoped NumberField BigOperators Classical SchwartzMap
open HeckePort.Moments HeckePort.Moments.CommonSupport HeckePort.Moments.Fourier
open HeckePort.Moments.Poisson

variable {K : Type*} [Field K] [NumberField K] (T : TraceFamily K)

lemma principalCRT_scaled_left (a b : 𝓞 K) (hcop : IsCoprime a b) (x : Residue a) :
    principalCRT a b hcop (scaledResidue a b (a * b) rfl x) =
      (Ideal.Quotient.mk _ b * x, 0) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [scaledResidue_mk, principalCRT_mk]
  have hb : Ideal.Quotient.mk (Ideal.span {b}) b = 0 :=
    (residue_eq_zero_iff_dvd b b).mpr dvd_rfl
  simp only [map_mul, hb, zero_mul]

lemma principalCRT_scaled_right (a b : 𝓞 K) (hcop : IsCoprime a b) (y : Residue b) :
    principalCRT a b hcop (scaledResidue b a (a * b) (mul_comm a b) y) =
      (0, Ideal.Quotient.mk _ a * y) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, principalCRT_mk]
  have ha : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
    (residue_eq_zero_iff_dvd a a).mpr dvd_rfl
  simp only [map_mul, ha, zero_mul]

theorem coprime_mixed_fourier (a b : 𝓞 K) (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (χa : MulChar (Residue a) ℂ) (G : Residue b → ℂ)
    (h : Residue (a * b)) :
    (∑ x : Residue (a * b),
      χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        G (frequencyReduction b (a * b) (dvd_mul_left b a) x) *
          T.ψ (a * b) (h * x)) =
      χa (Ideal.Quotient.mk _ b) *
        residueGauss T a χa (frequencyReduction a (a * b) (dvd_mul_right a b) h) *
        (∑ y : Residue b, G (Ideal.Quotient.mk _ a * y) *
          T.ψ b (frequencyReduction b (a * b) (dvd_mul_left b a) h * y)) := by
  let ua := residueUnit a b hcop
  let ub := residueUnit b a hcop.symm
  let e : Residue a × Residue b ≃ Residue (a * b) :=
    (ua.mulLeft.prodCongr ub.mulLeft).trans (principalCRT a b hcop).toEquiv.symm
  have heproj (x : Residue a × Residue b) : principalCRT a b hcop (e x) =
      ((ua : Residue a) * x.1, (ub : Residue b) * x.2) := by
    change (principalCRT a b hcop).toEquiv
      ((principalCRT a b hcop).toEquiv.symm ((ua : Residue a) * x.1, (ub : Residue b) * x.2)) = _
    exact (principalCRT a b hcop).toEquiv.apply_symm_apply _
  have he (x : Residue a × Residue b) : e x =
      scaledResidue a b (a * b) rfl x.1 + scaledResidue b a (a * b) (mul_comm a b) x.2 := by
    apply (principalCRT a b hcop).injective
    rw [heproj, map_add, principalCRT_scaled_left, principalCRT_scaled_right]
    simp only [Prod.mk_add_mk, add_zero, zero_add, ua, ub, residueUnit_coe]
  have hproj (x : Residue (a * b)) :
      (frequencyReduction a (a * b) (dvd_mul_right a b) x,
        frequencyReduction b (a * b) (dvd_mul_left b a) x) = principalCRT a b hcop x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [frequencyReduction_mk, principalCRT_mk]
  have hprojA (x : Residue a × Residue b) :
      frequencyReduction a (a * b) (dvd_mul_right a b) (e x) = Ideal.Quotient.mk _ b * x.1 := by
    have ht := congrArg Prod.fst (hproj (e x))
    rw [heproj] at ht
    simpa only [ua, residueUnit_coe] using ht
  have hprojB (x : Residue a × Residue b) :
      frequencyReduction b (a * b) (dvd_mul_left b a) (e x) = Ideal.Quotient.mk _ a * x.2 := by
    have ht := congrArg Prod.snd (hproj (e x))
    rw [heproj] at ht
    simpa only [ub, residueUnit_coe] using ht
  rw [← e.sum_comp]
  simp_rw [hprojA, hprojB]
  simp only [map_mul, he, mul_add, AddChar.map_add_eq_mul,
    T.scale a b (a * b) rfl, T.scale b a (a * b) (mul_comm a b)]
  simp only [Fintype.sum_prod_type, residueGauss]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem coprime_character_fourier (a b : 𝓞 K) (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (h : Residue (a * b)) :
    (∑ x : Residue (a * b),
      χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        χb (frequencyReduction b (a * b) (dvd_mul_left b a) x) *
          T.ψ (a * b) (h * x)) =
      χa (Ideal.Quotient.mk _ b) * χb (Ideal.Quotient.mk _ a) *
        residueGauss T a χa (frequencyReduction a (a * b) (dvd_mul_right a b) h) *
        residueGauss T b χb (frequencyReduction b (a * b) (dvd_mul_left b a) h) := by
  rw [coprime_mixed_fourier T a b hcop χa χb h]
  have hsum : (∑ y : Residue b, χb (Ideal.Quotient.mk _ a * y) *
      T.ψ b (frequencyReduction b (a * b) (dvd_mul_left b a) h * y)) =
      χb (Ideal.Quotient.mk _ a) *
        residueGauss T b χb (frequencyReduction b (a * b) (dvd_mul_left b a) h) := by
    simp only [residueGauss, map_mul, Finset.mul_sum, mul_assoc]
  rw [hsum]
  ring

theorem residueGauss_inverse (d : 𝓞 K) [Fintype (Residue d)]
    (χ : MulChar (Residue d) ℂ) (h : Residue d) :
    residueGauss T d χ⁻¹ h = star (residueGauss T d χ (-h)) := by
  have htrace (x : Residue d) : star (T.ψ d x) = T.ψ d (-x) := by
    rw [Complex.star_def, ← Complex.inv_eq_conj ((T.ψ d).norm_apply x),
      AddChar.map_neg_eq_inv]
  simp only [residueGauss, star_sum, star_mul, MulChar.star_apply', htrace,
    neg_mul, neg_neg]
  apply Finset.sum_congr rfl
  intro x _
  exact mul_comm _ _

theorem coprime_pair_fourier (a b : 𝓞 K) (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (h : Residue (a * b)) :
    (∑ x : Residue (a * b),
      χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        star (χb (frequencyReduction b (a * b) (dvd_mul_left b a) x)) *
          T.ψ (a * b) (h * x)) =
      χa (Ideal.Quotient.mk _ b) * star (χb (Ideal.Quotient.mk _ a)) *
        residueGauss T a χa (frequencyReduction a (a * b) (dvd_mul_right a b) h) *
        star (residueGauss T b χb (-(frequencyReduction b (a * b) (dvd_mul_left b a) h))) := by
  simp only [MulChar.star_apply']
  rw [coprime_character_fourier T a b hcop χa χb⁻¹ h, residueGauss_inverse]

variable {T} (R : RadialPoissonData T)

theorem coprime_pair_poisson (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (W : 𝓢(ℝ, ℂ)) (Kk : ℝ) (hK : 0 < Kk) :
    (∑' z : 𝓞 K, χa (Ideal.Quotient.mk _ z) * star (χb (Ideal.Quotient.mk _ z)) *
      W (R.norm2 z / Kk)) =
      ((Kk / R.norm2 (a * b) : ℝ) : ℂ) *
        (χa (Ideal.Quotient.mk _ b) * star (χb (Ideal.Quotient.mk _ a))) *
      ∑' j : 𝓞 K, residueGauss T a χa (Ideal.Quotient.mk _ j) *
        star (residueGauss T b χb (Ideal.Quotient.mk _ (-j))) *
        R.transform W (Kk * R.norm2 j / R.norm2 (a * b)) := by
  let P := fun x : Residue (a * b) =>
    χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
      star (χb (frequencyReduction b (a * b) (dvd_mul_left b a) x))
  have hcoeff (j : 𝓞 K) :
      (∑ r : Residue (a * b), P r * T.ψ (a * b) (Ideal.Quotient.mk _ j * r)) =
      (χa (Ideal.Quotient.mk _ b) * star (χb (Ideal.Quotient.mk _ a))) *
        (residueGauss T a χa (Ideal.Quotient.mk _ j) *
          star (residueGauss T b χb (Ideal.Quotient.mk _ (-j)))) := by
    have h := coprime_pair_fourier T a b hcop χa χb (Ideal.Quotient.mk _ j)
    simpa only [P, frequencyReduction_mk, map_neg, mul_assoc] using h
  have hpoisson := R.poisson (a * b) (mul_ne_zero ha hb) P W Kk hK
  have hmain : (∑' z : 𝓞 K, χa (Ideal.Quotient.mk _ z) * star (χb (Ideal.Quotient.mk _ z)) *
      W (R.norm2 z / Kk)) = (∑' z : 𝓞 K, P (Ideal.Quotient.mk _ z) * W (R.norm2 z / Kk)) := by
    apply tsum_congr
    intro z
    simp only [P, frequencyReduction_mk]
  rw [hmain, hpoisson]
  simp_rw [hcoeff, mul_assoc]
  simp_rw [tsum_mul_left]
  rw [Complex.real_smul]

end HeckePort.Moments.FirstPoisson

end
