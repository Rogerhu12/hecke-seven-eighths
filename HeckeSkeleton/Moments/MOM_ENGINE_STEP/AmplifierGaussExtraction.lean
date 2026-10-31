import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GaussPoolDictionary
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AmplifierDifference
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PrimePowerQuotientSupport

/-!
# Actual residual Gauss columns in the amplifier errors

For unit first modulus the complete column factors by the genuine
coprime Gauss CRT.  The prime-power part is the actual local table,
including its complex phase.  The residual column is unchanged under
sixth-power insertion at a prime outside its ideal.

All identities precede absolute values.  The same original coefficient
can therefore be multiplied through them without splitting a centered
difference.  The scalar depending on the row has norm one; the two
reciprocal character values form a fixed column factor.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open LocalFiniteSums CompatiblePrimeRawLocal MaskedQuotientCRT
open HeckePort.Moments HeckePort.Moments.CommonSupport
open HeckeGeneral.Arithmetic HeckeGeneral.Characters UniqueFactorizationMonoid

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

section Coprime

variable {R : Type*} [CommRing R]

theorem complete_coprime_gauss (T : NonzeroModulusTrace R)
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (hab : IsCoprime a b)
    [Fintype (CommonSupport.Residue a)] [Fintype (CommonSupport.Residue b)]
    [Fintype (CommonSupport.Residue (a * b))]
    (χa : MulChar (CommonSupport.Residue a) ℂ)
    (χb : MulChar (CommonSupport.Residue b) ℂ)
    (χab : MulChar (CommonSupport.Residue (a * b)) ℂ)
    (hχ : ∀ x, χab x =
      χa (completeFrequencyReduction a (a * b) (dvd_mul_right a b) x) *
        χb (completeFrequencyReduction b (a * b) (dvd_mul_left b a) x))
    (h : CommonSupport.Residue (a * b)) :
    completeResidueGauss T (a * b) χab h =
      (χa (Ideal.Quotient.mk _ b) * χb (Ideal.Quotient.mk _ a)) *
        completeResidueGauss T a χa
          (completeFrequencyReduction a (a * b) (dvd_mul_right a b) h) *
        completeResidueGauss T b χb
          (completeFrequencyReduction b (a * b) (dvd_mul_left b a) h) := by
  calc
    _ = ∑ x : CommonSupport.Residue (a * b),
        χa (completeFrequencyReduction a (a * b) (dvd_mul_right a b) x) *
          χb (completeFrequencyReduction b (a * b) (dvd_mul_left b a) x) *
            T.ψ (a * b) (h * x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hχ]
    _ = χa (Ideal.Quotient.mk _ b) *
        completeResidueGauss T a χa
          (completeFrequencyReduction a (a * b) (dvd_mul_right a b) h) *
        (∑ y : CommonSupport.Residue b, χb (Ideal.Quotient.mk _ a * y) *
          T.ψ b (completeFrequencyReduction b (a * b) (dvd_mul_left b a) h * y)) :=
      complete_coprime_mixed_fourier T a b ha hb hab χa χb h
    _ = _ := by
      have hs : (∑ y : CommonSupport.Residue b, χb (Ideal.Quotient.mk _ a * y) *
          T.ψ b (completeFrequencyReduction b (a * b) (dvd_mul_left b a) h * y)) =
          χb (Ideal.Quotient.mk _ a) * completeResidueGauss T b χb
            (completeFrequencyReduction b (a * b) (dvd_mul_left b a) h) := by
        unfold completeResidueGauss
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        rw [map_mul]
        ring
      rw [hs]
      ring

end Coprime

set_option maxHeartbeats 1600000 in
theorem actual_coprime_gauss
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent F v = 0)
    (I J IJ : A.Exterior) (hIJ : IJ.val = I.val * J.val)
    (a b h : A.R) (ha : A.Generates I a) (hb : A.Generates J b)
    (hab : A.Generates IJ (a * b)) (hcop : IsCoprime I.val J.val) :
    actualSIntegerGauss F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) hDiff
        (a * b) hab.1 (generatedIdealCharacter (σ := σ) IJ (a * b) hab) h =
      (generatedIdealCharacter (σ := σ) I a ha (Ideal.Quotient.mk _ b) *
        generatedIdealCharacter (σ := σ) J b hb (Ideal.Quotient.mk _ a)) *
      actualSIntegerGauss F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) hDiff
        a ha.1 (generatedIdealCharacter (σ := σ) I a ha) h *
      actualSIntegerGauss F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) hDiff
        b hb.1 (generatedIdealCharacter (σ := σ) J b hb) h := by
  letI := finite_sIntegerPrincipalResidue F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) a ha.1
  letI := finite_sIntegerPrincipalResidue F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) b hb.1
  letI := finite_sIntegerPrincipalResidue F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) (a * b) hab.1
  letI := Fintype.ofFinite (A.R ⧸ Ideal.span {a})
  letI := Fintype.ofFinite (A.R ⧸ Ideal.span {b})
  letI := Fintype.ofFinite (A.R ⧸ Ideal.span {a * b})
  have hchar (x : A.R ⧸ Ideal.span {a * b}) :
      generatedIdealCharacter (σ := σ) IJ (a * b) hab x =
        generatedIdealCharacter (σ := σ) I a ha
          (completeFrequencyReduction a (a * b) (dvd_mul_right a b) x) *
        generatedIdealCharacter (σ := σ) J b hb
          (completeFrequencyReduction b (a * b) (dvd_mul_left b a) x) := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact generatedIdealCharacter_mul I J IJ hIJ a b ha hb hab x
  exact complete_coprime_gauss
    (actualSIntegerTrace F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) hDiff)
    a b ha.1 hb.1 (generated_elements_coprime I J a b ha hb hcop)
    (generatedIdealCharacter (σ := σ) I a ha)
    (generatedIdealCharacter (σ := σ) J b hb)
    (generatedIdealCharacter (σ := σ) IJ (a * b) hab) hchar (Ideal.Quotient.mk _ h)

/-- The complete normalization factors with the actual ideal product. -/
theorem actual_coprime_unit_columns
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent F v = 0)
    (C : A.GeneralArithmeticContext σ η hS)
    (I J IJ : A.Exterior) (hIJ : IJ.val = I.val * J.val)
    (a b h : A.R) (ha : A.Generates I a) (hb : A.Generates J b)
    (hab : A.Generates IJ (a * b)) (hcop : IsCoprime I.val J.val) :
    actualFiniteColumn C (unitExterior A) IJ 1 (a * b)
        (unitExterior_generates A) hab h =
      (generatedIdealCharacter (σ := σ) I a ha (Ideal.Quotient.mk _ b) *
        generatedIdealCharacter (σ := σ) J b hb (Ideal.Quotient.mk _ a)) *
      actualFiniteColumn C (unitExterior A) I 1 a (unitExterior_generates A) ha h *
      actualFiniteColumn C (unitExterior A) J 1 b (unitExterior_generates A) hb h := by
  rw [actual_unit_column_eq_gauss_div_norm hDiff C,
    actual_unit_column_eq_gauss_div_norm hDiff C,
    actual_unit_column_eq_gauss_div_norm hDiff C,
    actual_coprime_gauss hDiff I J IJ hIJ a b h ha hb hab hcop]
  have hn : A.exteriorNorm IJ = A.exteriorNorm I * A.exteriorNorm J := by
    change (Ideal.absNorm IJ.val : ℝ) = _
    rw [hIJ, map_mul, Nat.cast_mul]
    rfl
  rw [hn, Complex.ofReal_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem primeExponent_unitExterior (p : ExteriorPrime A) :
    primeExponent p (unitExterior A) = 0 := by
  simp [primeExponent, unitExterior, idealPrimeExponent]

theorem unitExterior_allowed (C : A.GeneralArithmeticContext σ η hS) :
    A.IsAllowed C.correction.B
      (Units.mk0 ((1 : A.R) : F) (by exact_mod_cast (unitExterior_generates A).1)) := by
  change A.sClass (1 : Fˣ) ∈ C.correction.B
  rw [map_one]
  exact C.correction.B.one_mem

theorem actual_prime_power_allowed (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :
    A.IsAllowed C.correction.B
      (Units.mk0 ((generator C p ^ n : A.R) : F)
        (by exact_mod_cast (generator_power_generates C p n).1)) := by
  have he : Units.mk0 ((generator C p ^ n : A.R) : F)
      (by exact_mod_cast (generator_power_generates C p n).1) =
      (Units.mk0 (generator C p : F)
        (by exact_mod_cast (generator_generates C p).1)) ^ n := by
    apply Units.ext
    simp
  rw [he, SArithmeticData.IsAllowed, map_pow]
  exact C.correction.B.pow_mem (generator_allowed C p) n

theorem localUnitPart_unitExterior (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) :
    localUnitPart C p (unitExterior A) 1 (unitExterior_generates A) = 1 := by
  apply Units.ext
  apply Subtype.ext
  rw [localUnitPart_spec, primeExponent_unitExterior]
  simp

theorem localUnitPart_own_prime_power (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :
    localUnitPart C p (powerIdeal p n) (generator C p ^ n)
      (generator_power_generates C p n) = 1 := by
  apply Units.ext
  apply Subtype.ext
  rw [localUnitPart_spec, primeExponent_powerIdeal, if_pos rfl]
  have hπ : (generator C p : F) ≠ 0 := by
    exact_mod_cast (generator_generates C p).1
  have hu : algebraMap F (LocalField p) (generator C p : F) ≠ 0 :=
    (map_ne_zero (algebraMap F (LocalField p))).mpr hπ
  simp [uniformizer, map_pow, hu]

def amplifierRowPhase (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (Ih : A.Exterior) (h : A.R) (hh : A.Generates Ih h) : ℂ :=
  chiOnUnits (σ := σ) p (localUnitPart C p Ih h hh) ^ (-(n : ℤ))

theorem amplifierRowPhase_norm (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (Ih : A.Exterior) (h : A.R) (hh : A.Generates Ih h) :
    ‖amplifierRowPhase C p n Ih h hh‖ = 1 := by
  simp only [amplifierRowPhase, norm_zpow, chiOnUnits_norm, one_zpow]

/-- The actual normalized prime-power column is the local table at its
literal valuation, multiplied by a row-only phase. -/
theorem actual_prime_power_column (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (Ih : A.Exterior) (h : A.R) (hh : A.Generates Ih h)
    (P : Finset (ExteriorPrime A)) (hp : p ∈ P)
    (hSupportH : ∀ q : ExteriorPrime A, primeExponent q Ih ≠ 0 → q ∈ P) :
    actualFiniteColumn C (unitExterior A) (powerIdeal p n) 1 (generator C p ^ n)
      (unitExterior_generates A) (generator_power_generates C p n) h =
      amplifierRowPhase C p n Ih h hh * centralPrimePower C p n (primeExponent p Ih) := by
  have hcrt := whole_coefficient_full_prime_power_crt_norm C
    (unitExterior A) (powerIdeal p n) Ih 1 (generator C p ^ n) h
    (unitExterior_generates A) (generator_power_generates C p n) hh
    (unitExterior_allowed C) (actual_prime_power_allowed C p n) P
    (fun q hq => (hq (primeExponent_unitExterior q)).elim)
    (fun q hq => by
      by_cases hqp : q = p
      · simpa only [hqp] using hp
      · exact (hq (by rw [primeExponent_powerIdeal, if_neg hqp])).elim)
    hSupportH 1
  simp only [one_mul] at hcrt
  change actualFiniteColumn C (unitExterior A) (powerIdeal p n) 1 (generator C p ^ n)
    (unitExterior_generates A) (generator_power_generates C p n) h = _ at hcrt
  rw [hcrt, Finset.prod_eq_single p]
  · rw [primeExponent_powerIdeal, if_pos rfl, primeExponent_unitExterior,
      localUnitPart_unitExterior, localUnitPart_own_prime_power]
    change centralRawPrimePower C p n (primeExponent p Ih) 1 1
      (localUnitPart C p Ih h hh) = _
    rw [centralRawPrimePower_rescale]
    simp only [localUnitPhase, amplifierRowPhase, chiOnUnits, Units.val_one,
      map_one, one_zpow, mul_one]
  · intro q hq hqp
    rw [primeExponent_powerIdeal, if_neg hqp, primeExponent_unitExterior]
    change centralRawPrimePower C q 0 (primeExponent q Ih) _ _ _ = 1
    rw [centralRawPrimePower_rescale, centralPrimePower_zero]
    simp [localUnitPhase]
  · exact fun hnp => (hnp hp).elim

theorem amplifierRowPhase_insert (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (Ih : A.Exterior) (h : A.R) (hh : A.Generates Ih h) :
    amplifierRowPhase C p n (amplifiedExterior Ih p) (h * generator C p ^ 6)
      (amplifiedExterior_generates C Ih p h hh) =
        amplifierRowPhase C p n Ih h hh := by
  unfold amplifierRowPhase
  rw [localUnitPart_amplifiedExterior, chiOnUnits_sixth_mul]

/-- A real ideal with exact multiplicity n has a genuine exterior
quotient of multiplicity zero.  This supplies the residual modulus used
below from the original valuation predicate. -/
theorem exists_amplifier_residual_exterior (p : ExteriorPrime A) (n : ℕ)
    (I : A.Exterior) (hν : primeExponent p I = n) :
    ∃ J : A.Exterior, I.val = p.val.asIdeal ^ n * J.val ∧
      primeExponent p J = 0 ∧ IsCoprime p.val.asIdeal J.val := by
  have hd := PrimePowerQuotientSupport.prime_power_dvd_of_count p.val n I.val I.property.1 hν
  obtain ⟨J, hJ⟩ := hd
  have hJne : J ≠ 0 := (mul_ne_zero_iff.mp (hJ ▸ I.property.1)).2
  let Jr : A.Exterior := ⟨J, hJne, by
    apply top_unique
    rw [← I.property.2]
    apply sup_le_sup_right
    exact Ideal.dvd_iff_le.mp ⟨p.val.asIdeal ^ n, by rw [hJ, mul_comm]⟩⟩
  have hcount : (normalizedFactors J).count p.val.asIdeal = 0 := by
    have he := PrimePowerQuotientSupport.count_prime_power_mul p.val n J hJne
    rw [← hJ] at he
    change (normalizedFactors I.val).count p.val.asIdeal = n at hν
    omega
  have hnot : ¬p.val.asIdeal ∣ J := by
    intro hd
    have hm := (HeckePort.Moments.prime_mem_support_iff_dvd
      p.val.asIdeal J p.val.irreducible.prime hJne).mpr hd
    have hc := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hm)
    omega
  have hcop : IsCoprime p.val.asIdeal J := by
    rw [Ideal.isCoprime_iff_sup_eq]
    have hmax : p.val.asIdeal.IsMaximal := p.val.isPrime.isMaximal p.val.ne_bot
    exact hmax.out.2 _ (lt_of_le_of_ne le_sup_left (fun he =>
      hnot (Ideal.dvd_iff_le.mpr (sup_eq_left.mp he.symm))))
  exact ⟨Jr, hJ, hcount, hcop⟩


/-- A presentation chosen from the actual ideal quotient.  It is fixed
before the row variable and the Fourier parameter. -/
structure AmplifierResidualPresentation
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (n : ℕ) (I : A.Exterior) where
  residual : A.Exterior
  generator : A.R
  generates : A.Generates residual generator
  reconstructed : I.val = p.val.asIdeal ^ n * residual.val
  primitive : primeExponent p residual = 0
  coprime : IsCoprime p.val.asIdeal residual.val
  allowed : A.IsAllowed C.correction.B
    (Units.mk0 (generator : F) (by exact_mod_cast generates.1))

theorem exists_amplifier_residual_presentation
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (n : ℕ)
    (I : A.Exterior) (hν : primeExponent p I = n) :
    Nonempty (AmplifierResidualPresentation C p n I) := by
  obtain ⟨J, hIJ, hprim, hcop⟩ := exists_amplifier_residual_exterior p n I hν
  obtain ⟨a, u, ha, hua, hu⟩ := C.allowed_integral J
  refine ⟨⟨J, a, ha, hIJ, hprim, hcop, ?_⟩⟩
  have he : Units.mk0 (a : F) (by exact_mod_cast ha.1) = u := by
    apply Units.ext
    exact hua.symm
  rw [he]
  exact hu

def amplifierResidualPresentation
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (n : ℕ)
    (I : A.Exterior) (hν : primeExponent p I = n) :
    AmplifierResidualPresentation C p n I :=
  Classical.choice (exists_amplifier_residual_presentation C p n I hν)

namespace AmplifierResidualPresentation

variable {C : A.GeneralArithmeticContext σ η hS} {p : ExteriorPrime A} {n : ℕ}
  {I : A.Exterior}

theorem product_generates (R : AmplifierResidualPresentation C p n I) :
    A.Generates I (LocalFiniteSums.generator C p ^ n * R.generator) :=
  generated_product (powerIdeal p n) R.residual I R.reconstructed
    (LocalFiniteSums.generator C p ^ n) R.generator
    (generator_power_generates C p n) R.generates

theorem product_allowed (R : AmplifierResidualPresentation C p n I) :
    A.IsAllowed C.correction.B
      (Units.mk0 ((LocalFiniteSums.generator C p ^ n * R.generator : A.R) : F)
        (by exact_mod_cast R.product_generates.1)) := by
  have he : Units.mk0 ((LocalFiniteSums.generator C p ^ n * R.generator : A.R) : F)
      (by exact_mod_cast R.product_generates.1) =
      Units.mk0 ((LocalFiniteSums.generator C p ^ n : A.R) : F)
        (by exact_mod_cast (generator_power_generates C p n).1) *
      Units.mk0 (R.generator : F) (by exact_mod_cast R.generates.1) := by
    apply Units.ext
    rfl
  rw [he, SArithmeticData.IsAllowed, map_mul]
  exact C.correction.B.mul_mem (actual_prime_power_allowed C p n) R.allowed

theorem power_coprime (R : AmplifierResidualPresentation C p n I) :
    IsCoprime (powerIdeal p n).val R.residual.val := by
  simpa only [pow_one] using (R.coprime.pow :
    IsCoprime (p.val.asIdeal ^ n) (R.residual.val ^ 1))

theorem residual_support (R : AmplifierResidualPresentation C p n I)
    (P : Finset (ExteriorPrime A))
    (hSupport : ∀ q : ExteriorPrime A, primeExponent q I ≠ 0 → q ∈ P) :
    ∀ q : ExteriorPrime A, primeExponent q R.residual ≠ 0 → q ∈ P := by
  intro q hq
  apply hSupport q
  change (normalizedFactors I.val).count q.val.asIdeal ≠ 0
  rw [R.reconstructed, normalizedFactors_mul
    (pow_ne_zero n p.val.ne_bot) R.residual.property.1, Multiset.count_add]
  change (normalizedFactors (p.val.asIdeal ^ n)).count q.val.asIdeal +
    primeExponent q R.residual ≠ 0
  omega

def columnPhase (R : AmplifierResidualPresentation C p n I) : ℂ :=
  generatedIdealCharacter (σ := σ) (powerIdeal p n)
      (LocalFiniteSums.generator C p ^ n) (generator_power_generates C p n)
      (Ideal.Quotient.mk _ R.generator) *
    generatedIdealCharacter (σ := σ) R.residual R.generator R.generates
      (Ideal.Quotient.mk _ (LocalFiniteSums.generator C p ^ n))

/-- The original allowed generator is replaced through the existing
arithmetic recipe.  No literal equality of two chosen generators occurs. -/
theorem unit_column_factor (R : AmplifierResidualPresentation C p n I)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent F v = 0)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B D)
    (a : A.R) (ha : A.Generates I a)
    (hallowed : A.IsAllowed C.correction.B
      (Units.mk0 (a : F) (by exact_mod_cast ha.1))) (h : A.R) :
    actualFiniteColumn C (unitExterior A) I 1 a (unitExterior_generates A) ha h =
      R.columnPhase *
      actualFiniteColumn C (unitExterior A) (powerIdeal p n) 1
        (LocalFiniteSums.generator C p ^ n) (unitExterior_generates A)
          (generator_power_generates C p n) h *
      actualFiniteColumn C (unitExterior A) R.residual 1 R.generator
        (unitExterior_generates A) R.generates h := by
  have he := actual_gauss_column_generator_replacement C D hD I a
    (LocalFiniteSums.generator C p ^ n * R.generator) h ha R.product_generates
    hallowed R.product_allowed
  have hc :
      actualFiniteColumn C (unitExterior A) I 1 a (unitExterior_generates A) ha h =
        actualFiniteColumn C (unitExterior A) I 1
          (LocalFiniteSums.generator C p ^ n * R.generator)
          (unitExterior_generates A) R.product_generates h := by
    unfold actualFiniteColumn
    rw [he]
  rw [hc]
  exact actual_coprime_unit_columns hDiff C (powerIdeal p n) R.residual I
    R.reconstructed (LocalFiniteSums.generator C p ^ n) R.generator h
    (generator_power_generates C p n) R.generates R.product_generates R.power_coprime

/-- The real error column is the residual actual Gauss column with its
original complex local difference, a row-only phase, and a fixed column
phase.  The original coefficient has not been estimated or split. -/
theorem difference (R : AmplifierResidualPresentation C p n I)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent F v = 0)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B D)
    (a : A.R) (ha : A.Generates I a)
    (hallowed : A.IsAllowed C.correction.B
      (Units.mk0 (a : F) (by exact_mod_cast ha.1)))
    (Ih : A.Exterior) (h : A.R) (hh : A.Generates Ih h)
    (hunit : primeExponent p Ih = 0)
    (P : Finset (ExteriorPrime A)) (hp : p ∈ P)
    (hSupport : ∀ q : ExteriorPrime A, primeExponent q I ≠ 0 → q ∈ P)
    (hSupportH : ∀ q : ExteriorPrime A, primeExponent q Ih ≠ 0 → q ∈ P) :
    actualFiniteColumn C (unitExterior A) I 1 a (unitExterior_generates A) ha h -
      actualFiniteColumn C (unitExterior A) I 1 a (unitExterior_generates A) ha
        (h * LocalFiniteSums.generator C p ^ 6) =
      (centralPrimePower C p n 0 - centralPrimePower C p n 6) *
        amplifierRowPhase C p n Ih h hh * R.columnPhase *
        actualFiniteColumn C (unitExterior A) R.residual 1 R.generator
          (unitExterior_generates A) R.generates h := by
  have hSupportH' : ∀ q : ExteriorPrime A,
      primeExponent q (amplifiedExterior Ih p) ≠ 0 → q ∈ P := by
    intro q hq
    by_cases hqp : q = p
    · simpa only [hqp] using hp
    · apply hSupportH q
      simpa only [primeExponent_amplifiedExterior, if_neg hqp, add_zero] using hq
  have hinvariant := actualFiniteColumn_unchanged C (unitExterior A) R.residual Ih
    1 R.generator h (unitExterior_generates A) R.generates hh
    (unitExterior_allowed C) R.allowed P p hp
    (fun q hq => (hq (primeExponent_unitExterior q)).elim)
    (R.residual_support P hSupport) hSupportH (primeExponent_unitExterior p) hunit
    (by rw [R.primitive]; decide) (by rw [R.primitive]; decide) (by rw [R.primitive]; decide)
  rw [R.unit_column_factor hDiff D hD a ha hallowed h,
    R.unit_column_factor hDiff D hD a ha hallowed (h * LocalFiniteSums.generator C p ^ 6),
    hinvariant, actual_prime_power_column C p n Ih h hh P hp hSupportH,
    actual_prime_power_column C p n (amplifiedExterior Ih p)
      (h * LocalFiniteSums.generator C p ^ 6) (amplifiedExterior_generates C Ih p h hh)
      P hp hSupportH',
    amplifierRowPhase_insert, primeExponent_amplifiedExterior, if_pos rfl, hunit]
  norm_num only [zero_add]
  ring

end AmplifierResidualPresentation

/-- At a fixed valuation the same complex difference and row phase
factor outside the original whole polynomial. -/
theorem whole_amplifier_residual_gauss {ι : Type*}
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent F v = 0)
    (C : A.GeneralArithmeticContext σ η hS)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B D)
    (columns : Finset ι) (c : ι → ℂ)
    (I : ι → A.Exterior) (a : ι → A.R) (ha : ∀ i, A.Generates (I i) (a i))
    (hallowed : ∀ i ∈ columns, A.IsAllowed C.correction.B
      (Units.mk0 (a i : F) (by exact_mod_cast (ha i).1)))
    (p : ExteriorPrime A) (n : ℕ)
    (R : ∀ i, AmplifierResidualPresentation C p n (I i))
    (Ih : A.Exterior) (h : A.R) (hh : A.Generates Ih h) (hunit : primeExponent p Ih = 0)
    (P : Finset (ExteriorPrime A)) (hp : p ∈ P)
    (hSupport : ∀ i ∈ columns, ∀ q : ExteriorPrime A, primeExponent q (I i) ≠ 0 → q ∈ P)
    (hSupportH : ∀ q : ExteriorPrime A, primeExponent q Ih ≠ 0 → q ∈ P) :
    (∑ i ∈ columns, c i *
      (actualFiniteColumn C (unitExterior A) (I i) 1 (a i) (unitExterior_generates A) (ha i) h -
       actualFiniteColumn C (unitExterior A) (I i) 1 (a i) (unitExterior_generates A) (ha i)
         (h * generator C p ^ 6))) =
      (centralPrimePower C p n 0 - centralPrimePower C p n 6) *
        amplifierRowPhase C p n Ih h hh *
        (∑ i ∈ columns, (c i * (R i).columnPhase) *
          actualFiniteColumn C (unitExterior A) (R i).residual 1 (R i).generator
            (unitExterior_generates A) (R i).generates h) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(R i).difference hDiff D hD (a i) (ha i) (hallowed i hi)
    Ih h hh hunit P hp (hSupport i hi) hSupportH]
  ring


/-- The squared local saving is preserved exactly after residual
extraction.  The row phase disappears only after the entire sum is formed. -/
theorem whole_amplifier_residual_gauss_norm_sq {ι : Type*}
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent F v = 0)
    (C : A.GeneralArithmeticContext σ η hS)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B D)
    (columns : Finset ι) (c : ι → ℂ)
    (I : ι → A.Exterior) (a : ι → A.R) (ha : ∀ i, A.Generates (I i) (a i))
    (hallowed : ∀ i ∈ columns, A.IsAllowed C.correction.B
      (Units.mk0 (a i : F) (by exact_mod_cast (ha i).1)))
    (p : ExteriorPrime A) (n : ℕ)
    (R : ∀ i, AmplifierResidualPresentation C p n (I i))
    (Ih : A.Exterior) (h : A.R) (hh : A.Generates Ih h) (hunit : primeExponent p Ih = 0)
    (P : Finset (ExteriorPrime A)) (hp : p ∈ P)
    (hSupport : ∀ i ∈ columns, ∀ q : ExteriorPrime A, primeExponent q (I i) ≠ 0 → q ∈ P)
    (hSupportH : ∀ q : ExteriorPrime A, primeExponent q Ih ≠ 0 → q ∈ P) :
    ‖∑ i ∈ columns, c i *
      (actualFiniteColumn C (unitExterior A) (I i) 1 (a i) (unitExterior_generates A) (ha i) h -
       actualFiniteColumn C (unitExterior A) (I i) 1 (a i) (unitExterior_generates A) (ha i)
         (h * generator C p ^ 6))‖ ^ 2 =
      (if n = 1 then (Q p)⁻¹ else if n = 6 then (1 - (Q p)⁻¹) ^ 2
        else if n = 7 then (Q p)⁻¹ else 0) *
        ‖∑ i ∈ columns, (c i * (R i).columnPhase) *
          actualFiniteColumn C (unitExterior A) (R i).residual 1 (R i).generator
            (unitExterior_generates A) (R i).generates h‖ ^ 2 := by
  rw [whole_amplifier_residual_gauss hDiff C D hD columns c I a ha hallowed p n R
    Ih h hh hunit P hp hSupport hSupportH]
  simp only [norm_mul, amplifierRowPhase_norm, mul_one, mul_pow,
    centralPrimePower_difference_norm_sq]


end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_coprime_unit_columns
#print axioms HeckeSkeleton.Moments.EngineStep.actual_prime_power_column
#print axioms HeckeSkeleton.Moments.EngineStep.exists_amplifier_residual_presentation
#print axioms HeckeSkeleton.Moments.EngineStep.AmplifierResidualPresentation.difference
#print axioms HeckeSkeleton.Moments.EngineStep.whole_amplifier_residual_gauss


