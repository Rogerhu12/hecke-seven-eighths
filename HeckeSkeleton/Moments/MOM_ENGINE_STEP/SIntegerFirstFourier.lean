import HeckePort.Moments.CommonSupport
import HeckeGeneral.Arithmetic.SIntegerPeriodicFourier

/-!
# The first mixed finite transform on the actual S-integer quotients

The two coprime residual columns and the complete common factor split
by the genuine CRT.  The trace family used at the final entry point is
constructed from the actual positive S-local principal phase.  Its
scaling law and primitivity are proved here from the existing arithmetic
character, so no first-transform identity is supplied as a hypothesis.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open HeckePort.Moments HeckePort.Moments.CommonSupport
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open NumberField IsDedekindDomain

section Ring

variable {R : Type*} [CommRing R]

def completeFrequencyReduction (d m : R) (h : d ∣ m) : Residue m →+* Residue d :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr h)

@[simp] theorem completeFrequencyReduction_mk (d m : R) (h : d ∣ m) (x : R) :
    completeFrequencyReduction d m h (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

theorem completeFrequencyReduction_comp (d n m : R) (hd : d ∣ n) (hn : n ∣ m)
    (x : Residue m) :
    completeFrequencyReduction d n hd (completeFrequencyReduction n m hn x) =
      completeFrequencyReduction d m (hd.trans hn) x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- Only nonzero moduli enter the transform.  The value at zero is
irrelevant, and the scaling law records its nonzero hypotheses. -/
structure NonzeroModulusTrace (R : Type*) [CommRing R] where
  ψ : ∀ d : R, AddChar (Residue d) ℂ
  primitive : ∀ d, d ≠ 0 → (ψ d).IsPrimitive
  scale : ∀ (d a m : R), d ≠ 0 → a ≠ 0 → ∀ (hm : m = d * a)
    (h : Residue m) (x : Residue d),
    ψ m (h * scaledResidue d a m hm x) =
      ψ d (completeFrequencyReduction d m (hm ▸ dvd_mul_right d a) h * x)

def completeResidueGauss (T : NonzeroModulusTrace R) (d : R)
    [Fintype (Residue d)] (χ : MulChar (Residue d) ℂ) (h : Residue d) : ℂ :=
  ∑ x : Residue d, χ x * T.ψ d (h * x)

theorem mixed_principalCRT_scaled_left (a b : R) (hcop : IsCoprime a b) (x : Residue a) :
    principalCRT a b hcop (scaledResidue a b (a * b) rfl x) =
      (Ideal.Quotient.mk _ b * x, 0) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [scaledResidue_mk, principalCRT_mk]
  have hb : Ideal.Quotient.mk (Ideal.span {b}) b = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr dvd_rfl)
  simp only [map_mul, hb, zero_mul]

theorem mixed_principalCRT_scaled_right (a b : R) (hcop : IsCoprime a b) (y : Residue b) :
    principalCRT a b hcop (scaledResidue b a (a * b) (mul_comm a b) y) =
      (0, Ideal.Quotient.mk _ a * y) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, principalCRT_mk]
  have ha : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr dvd_rfl)
  simp only [map_mul, ha, zero_mul]

/-- The exact mixed Fourier factorization over a general ring. -/
theorem complete_coprime_mixed_fourier (T : NonzeroModulusTrace R)
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (χa : MulChar (Residue a) ℂ) (G : Residue b → ℂ) (h : Residue (a * b)) :
    (∑ x : Residue (a * b),
      χa (completeFrequencyReduction a (a * b) (dvd_mul_right a b) x) *
        G (completeFrequencyReduction b (a * b) (dvd_mul_left b a) x) *
          T.ψ (a * b) (h * x)) =
      χa (Ideal.Quotient.mk _ b) *
        completeResidueGauss T a χa
          (completeFrequencyReduction a (a * b) (dvd_mul_right a b) h) *
        (∑ y : Residue b, G (Ideal.Quotient.mk _ a * y) *
          T.ψ b (completeFrequencyReduction b (a * b) (dvd_mul_left b a) h * y)) := by
  let ua := residueUnit a b hcop
  let ub := residueUnit b a hcop.symm
  let e : Residue a × Residue b ≃ Residue (a * b) :=
    (ua.mulLeft.prodCongr ub.mulLeft).trans (principalCRT a b hcop).toEquiv.symm
  have heproj (x : Residue a × Residue b) : principalCRT a b hcop (e x) =
      ((ua : Residue a) * x.1, (ub : Residue b) * x.2) := by
    change (principalCRT a b hcop).toEquiv
      ((principalCRT a b hcop).toEquiv.symm
        ((ua : Residue a) * x.1, (ub : Residue b) * x.2)) = _
    exact (principalCRT a b hcop).toEquiv.apply_symm_apply _
  have he (x : Residue a × Residue b) : e x =
      scaledResidue a b (a * b) rfl x.1 +
        scaledResidue b a (a * b) (mul_comm a b) x.2 := by
    apply (principalCRT a b hcop).injective
    rw [heproj, map_add, mixed_principalCRT_scaled_left, mixed_principalCRT_scaled_right]
    simp only [Prod.mk_add_mk, add_zero, zero_add, ua, ub, residueUnit_coe]
  have hproj (x : Residue (a * b)) :
      (completeFrequencyReduction a (a * b) (dvd_mul_right a b) x,
        completeFrequencyReduction b (a * b) (dvd_mul_left b a) x) =
      principalCRT a b hcop x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [completeFrequencyReduction_mk, principalCRT_mk]
  have hprojA (x : Residue a × Residue b) :
      completeFrequencyReduction a (a * b) (dvd_mul_right a b) (e x) =
        Ideal.Quotient.mk _ b * x.1 := by
    have ht := congrArg Prod.fst (hproj (e x))
    rw [heproj] at ht
    simpa only [ua, residueUnit_coe] using ht
  have hprojB (x : Residue a × Residue b) :
      completeFrequencyReduction b (a * b) (dvd_mul_left b a) (e x) =
        Ideal.Quotient.mk _ a * x.2 := by
    have ht := congrArg Prod.snd (hproj (e x))
    rw [heproj] at ht
    simpa only [ub, residueUnit_coe] using ht
  rw [← e.sum_comp]
  simp_rw [hprojA, hprojB]
  simp only [map_mul, he, mul_add, AddChar.map_add_eq_mul,
    T.scale a b (a * b) ha hb rfl, T.scale b a (a * b) hb ha (mul_comm a b)]
  simp only [Fintype.sum_prod_type, completeResidueGauss]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem complete_three_factor_mixed_fourier [IsDomain R]
    (T : NonzeroModulusTrace R) (a b c : R) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (habc : IsCoprime a (b * c)) (hbc : IsCoprime b c)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue c)]
    [Fintype (Residue (b * c))] [Fintype (Residue (a * (b * c)))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (G : Residue c → ℂ)
    (h : Residue (a * (b * c))) :
    (∑ x : Residue (a * (b * c)),
      χa (completeFrequencyReduction a (a * (b * c)) (dvd_mul_right _ _) x) *
        χb (completeFrequencyReduction b (a * (b * c))
          (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x) *
        G (completeFrequencyReduction c (a * (b * c))
          (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x) *
        T.ψ (a * (b * c)) (h * x)) =
      χa (Ideal.Quotient.mk _ (b * c)) * χb (Ideal.Quotient.mk _ (a * c)) *
        completeResidueGauss T a χa
          (completeFrequencyReduction a (a * (b * c)) (dvd_mul_right _ _) h) *
        completeResidueGauss T b χb
          (completeFrequencyReduction b (a * (b * c))
            (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) h) *
        (∑ y : Residue c, G (Ideal.Quotient.mk _ (a * b) * y) *
          T.ψ c (completeFrequencyReduction c (a * (b * c))
            (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) h * y)) := by
  let H : Residue (b * c) → ℂ := fun y =>
    χb (completeFrequencyReduction b (b * c) (dvd_mul_right _ _) y) *
      G (completeFrequencyReduction c (b * c) (dvd_mul_left _ _) y)
  let h' := completeFrequencyReduction (b * c) (a * (b * c)) (dvd_mul_left _ _) h
  have he (x : Residue (a * (b * c))) :
      χa (completeFrequencyReduction a (a * (b * c)) (dvd_mul_right _ _) x) *
        H (completeFrequencyReduction (b * c) (a * (b * c)) (dvd_mul_left _ _) x) =
      χa (completeFrequencyReduction a (a * (b * c)) (dvd_mul_right _ _) x) *
        χb (completeFrequencyReduction b (a * (b * c))
          (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x) *
        G (completeFrequencyReduction c (a * (b * c))
          (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x) := by
    dsimp only [H]
    rw [completeFrequencyReduction_comp, completeFrequencyReduction_comp]
    ring
  simp_rw [← he]
  rw [complete_coprime_mixed_fourier T a (b * c) ha (mul_ne_zero hb hc) habc χa H h]
  have hf (y : Residue (b * c)) : H (Ideal.Quotient.mk _ a * y) =
      χb (Ideal.Quotient.mk _ a) *
        (χb (completeFrequencyReduction b (b * c) (dvd_mul_right _ _) y) *
          G (Ideal.Quotient.mk _ a *
            completeFrequencyReduction c (b * c) (dvd_mul_left _ _) y)) := by
    simp only [H, map_mul, completeFrequencyReduction_mk]
    ring
  simp_rw [hf, mul_assoc]
  rw [← Finset.mul_sum]
  have hh := complete_coprime_mixed_fourier T b c hb hc hbc χb
    (fun y => G (Ideal.Quotient.mk _ a * y)) h'
  simp only [mul_assoc] at hh
  rw [hh]
  simp only [h', completeFrequencyReduction_comp, map_mul, mul_assoc]
  ring

theorem completeResidueGauss_inverse (T : NonzeroModulusTrace R) (a : R)
    [Fintype (Residue a)] (χ : MulChar (Residue a) ℂ) (h : Residue a) :
    completeResidueGauss T a χ⁻¹ h = star (completeResidueGauss T a χ (-h)) := by
  have htrace (z : Residue a) : star (T.ψ a z) = T.ψ a (-z) := by
    simpa only [← starRingEnd_apply] using (AddChar.map_neg_eq_conj (T.ψ a) z).symm
  simp only [completeResidueGauss, star_sum, star_mul, MulChar.star_apply', htrace,
    neg_mul, neg_neg]
  apply Finset.sum_congr rfl
  intro x _
  exact mul_comm _ _

end Ring

section Actual

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
local notation "OS" => S.integer K

/-- The real S-local character at each nonzero modulus. -/
def actualSIntegerModulusPhase (a : OS) : AddChar (Residue a) ℂ :=
  if ha : a = 0 then 0 else sIntegerActualModulusAddCharacter K S hS a ha

theorem actualSIntegerModulusPhase_eq (a : OS) (ha : a ≠ 0) :
    actualSIntegerModulusPhase K S hS a = sIntegerActualModulusAddCharacter K S hS a ha := by
  simp only [actualSIntegerModulusPhase, dif_neg ha]

/-- The phase scaling is proved on representatives using cancellation in
the field, and therefore holds on the entire finite quotient. -/
def actualSIntegerTrace : NonzeroModulusTrace OS where
  ψ := actualSIntegerModulusPhase K S hS
  primitive a ha := by
    rw [actualSIntegerModulusPhase_eq K S hS a ha]
    exact sIntegerActualModulusAddCharacter_isPrimitive K S hS a ha
  scale d a m hd ha hm h x := by
    have hm0 : m ≠ 0 := by simpa only [hm] using mul_ne_zero hd ha
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective h
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [scaledResidue_mk, completeFrequencyReduction_mk,
      ← map_mul, ← map_mul, actualSIntegerModulusPhase_eq K S hS m hm0,
      actualSIntegerModulusPhase_eq K S hS d hd,
      sIntegerActualModulusAddCharacter_mk, sIntegerActualModulusAddCharacter_mk]
    congr 1
    have hd' : (d : K) ≠ 0 := by exact_mod_cast hd
    have ha' : (a : K) ≠ 0 := by exact_mod_cast ha
    rw [hm]
    push_cast
    field_simp
    <;> ring

theorem actualSIntegerTrace_psi (a : OS) (ha : a ≠ 0) :
    (actualSIntegerTrace K S hS).ψ a =
      sIntegerActualModulusAddCharacter K S hS a ha :=
  actualSIntegerModulusPhase_eq K S hS a ha

theorem actualSIntegerTrace_psi_mk (a : OS) (ha : a ≠ 0) (x : OS) :
    (actualSIntegerTrace K S hS).ψ a (Ideal.Quotient.mk _ x) =
      sLocalPrincipalPhase K S ((x : K) / (a : K)) := by
  change actualSIntegerModulusPhase K S hS a _ = _
  rw [actualSIntegerModulusPhase_eq K S hS a ha,
    sIntegerActualModulusAddCharacter_mk]

/-- The first finite transform with the actual S-local phase.  Both full
residual moduli and the arbitrary complete common factor are retained.
Taking the second character inverse gives `star(Gauss_b(-h))` by
`completeResidueGauss_inverse`. -/
theorem actual_sInteger_three_factor_fourier (a b c : OS)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (habc : IsCoprime a (b * c)) (hbc : IsCoprime b c)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue c)]
    [Fintype (Residue (b * c))] [Fintype (Residue (a * (b * c)))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (G : Residue c → ℂ)
    (h : Residue (a * (b * c))) :
    (∑ x : Residue (a * (b * c)),
      χa (completeFrequencyReduction a (a * (b * c)) (dvd_mul_right _ _) x) *
        χb (completeFrequencyReduction b (a * (b * c))
          (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x) *
        G (completeFrequencyReduction c (a * (b * c))
          (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x) *
        sIntegerActualModulusAddCharacter K S hS (a * (b * c))
          (mul_ne_zero ha (mul_ne_zero hb hc)) (h * x)) =
      χa (Ideal.Quotient.mk _ (b * c)) * χb (Ideal.Quotient.mk _ (a * c)) *
        completeResidueGauss (actualSIntegerTrace K S hS) a χa
          (completeFrequencyReduction a (a * (b * c)) (dvd_mul_right _ _) h) *
        completeResidueGauss (actualSIntegerTrace K S hS) b χb
          (completeFrequencyReduction b (a * (b * c))
            (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) h) *
        (∑ y : Residue c, G (Ideal.Quotient.mk _ (a * b) * y) *
          sIntegerActualModulusAddCharacter K S hS c hc
            (completeFrequencyReduction c (a * (b * c))
              (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) h * y)) := by
  have he := complete_three_factor_mixed_fourier (actualSIntegerTrace K S hS)
    a b c ha hb hc habc hbc χa χb G h
  simpa only [actualSIntegerTrace_psi K S hS
    (a * (b * c)) (mul_ne_zero ha (mul_ne_zero hb hc)),
    actualSIntegerTrace_psi K S hS c hc] using he

/-- Every moving-mask divisor is retained, even when it is a nonunit.
Its two residual character values are literal factors, and the complete
common function is evaluated at the dilated argument. -/
theorem actual_sInteger_three_factor_divisor_fourier (a b c : OS)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (habc : IsCoprime a (b * c)) (hbc : IsCoprime b c)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue c)]
    [Fintype (Residue (b * c))] [Fintype (Residue (a * (b * c)))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (G : Residue c → ℂ)
    (δ : OS) (h : Residue (a * (b * c))) :
    PeriodicFourier.divisorTransform
      (sIntegerActualModulusAddCharacter K S hS (a * (b * c))
        (mul_ne_zero ha (mul_ne_zero hb hc)))
      (fun x =>
        χa (completeFrequencyReduction a (a * (b * c)) (dvd_mul_right _ _) x) *
        χb (completeFrequencyReduction b (a * (b * c))
          (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x) *
        G (completeFrequencyReduction c (a * (b * c))
          (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x))
      (Ideal.Quotient.mk _ δ) h =
      (χa (Ideal.Quotient.mk _ δ) * χb (Ideal.Quotient.mk _ δ)) *
      (χa (Ideal.Quotient.mk _ (b * c)) * χb (Ideal.Quotient.mk _ (a * c)) *
        completeResidueGauss (actualSIntegerTrace K S hS) a χa
          (completeFrequencyReduction a (a * (b * c)) (dvd_mul_right _ _) h) *
        completeResidueGauss (actualSIntegerTrace K S hS) b χb
          (completeFrequencyReduction b (a * (b * c))
            (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) h) *
        (∑ y : Residue c,
          G (Ideal.Quotient.mk _ δ * (Ideal.Quotient.mk _ (a * b) * y)) *
          sIntegerActualModulusAddCharacter K S hS c hc
            (completeFrequencyReduction c (a * (b * c))
              (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) h * y))) := by
  let H : Residue c → ℂ := fun z => G (Ideal.Quotient.mk _ δ * z)
  have he := actual_sInteger_three_factor_fourier K S hS a b c ha hb hc habc hbc
    χa χb H h
  calc
    _ = (χa (Ideal.Quotient.mk _ δ) * χb (Ideal.Quotient.mk _ δ)) *
        ∑ x : Residue (a * (b * c)),
          χa (completeFrequencyReduction a (a * (b * c)) (dvd_mul_right _ _) x) *
          χb (completeFrequencyReduction b (a * (b * c))
            (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x) *
          H (completeFrequencyReduction c (a * (b * c))
            (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x) *
          sIntegerActualModulusAddCharacter K S hS (a * (b * c))
            (mul_ne_zero ha (mul_ne_zero hb hc)) (h * x) := by
      rw [PeriodicFourier.divisorTransform_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp only [map_mul, completeFrequencyReduction_mk, H]
      ring
    _ = _ := by rw [he]

end Actual

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actualSIntegerTrace
#print axioms HeckeSkeleton.Moments.EngineStep.actual_sInteger_three_factor_fourier
#print axioms HeckeSkeleton.Moments.EngineStep.actual_sInteger_three_factor_divisor_fourier
