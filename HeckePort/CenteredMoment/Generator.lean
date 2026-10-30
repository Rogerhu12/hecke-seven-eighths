import HeckeGeneral.Analysis.PrincipalGeneratorCalibration
import HeckeGeneral.Arithmetic.SIntegerModulus

/-!
# The allowed-generator character on ideals

General-field replacement for the character part of
`OAI.SevenEighths.CenteredMomentPrimary` (openai/math,
`OAI/NumberTheory/DirichletL/Moments/Primary.lean`, revision `fd4aeeb2`).

Over `ℤ[ω]` an ideal prime to `3` has a unique primary generator, and
`primaryIdealCharacter c χ I = χ (primaryGenerator I mod c)` is a monoid hom.
Over a general field the generator is the allowed generator `D.generator` of an
exterior ideal. It is multiplicative only up to sixth powers of S-units
(`AllowedGeneratorInput.multiplicative`), so the residue character must be
trivial on those sixth powers. The result is extended by zero off the exterior
ideals, as openai extends by zero off the ideals prime to `3`.
-/

noncomputable section

namespace HeckePort.CenteredMomentGenerator

open NumberField IsDedekindDomain HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- Nonzero ideals with no prime factor in `S`. -/
def IsExterior (I : Ideal (𝓞 K)) : Prop :=
  I ≠ ⊥ ∧ ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → p ∉ S

/-- The exterior ideal with underlying ideal `I`. -/
def toExterior (I : Ideal (𝓞 K)) (h : IsExterior K S I) : ExteriorIdeal K S :=
  ⟨⟨I, mem_nonZeroDivisors_of_ne_zero h.1⟩, h.2⟩

omit [Fintype S] in
theorem isExterior_mul_iff {I J : Ideal (𝓞 K)} :
    IsExterior K S (I * J) ↔ IsExterior K S I ∧ IsExterior K S J := by
  constructor
  · rintro ⟨h0, hS⟩
    exact ⟨⟨fun hI => h0 (by rw [hI, Ideal.bot_mul]), fun p hp => hS p (dvd_mul_of_dvd_left hp J)⟩,
      ⟨fun hJ => h0 (by rw [hJ, Ideal.mul_bot]), fun p hp => hS p (dvd_mul_of_dvd_right hp I)⟩⟩
  · rintro ⟨⟨hI0, hIS⟩, ⟨hJ0, hJS⟩⟩
    refine ⟨fun h => ?_, fun p hp => ?_⟩
    · rcases Ideal.mul_eq_bot.mp h with h | h
      exacts [hI0 h, hJ0 h]
    · rcases p.prime.dvd_mul.mp hp with h | h
      exacts [hIS p h, hJS p h]

omit [Fintype S] in
theorem isExterior_top : IsExterior K S ⊤ := by
  refine ⟨top_ne_bot, fun p hp => ?_⟩
  exact absurd (top_le_iff.mp (Ideal.dvd_iff_le.mp hp)) p.isPrime.ne_top

omit [Fintype S] in
theorem toExterior_mul {I J : Ideal (𝓞 K)} (hI : IsExterior K S I) (hJ : IsExterior K S J)
    (hIJ : IsExterior K S (I * J)) :
    toExterior K S (I * J) hIJ = exteriorMul K S (toExterior K S I hI) (toExterior K S J hJ) :=
  rfl

/-- Residue characters modulo `c` that are trivial on sixth powers of S-units. -/
def SixthPowerTrivial (c : S.integer K)
    (χ : MulChar (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) ℂ) : Prop :=
  ∀ u : S.unit K, χ (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u).val ^ 6)) = 1

/-- `χ` of the allowed generator, extended by zero off the exterior ideals. -/
def generatorCharacter (c : S.integer K)
    (χ : MulChar (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) ℂ)
    (I : Ideal (𝓞 K)) : ℂ :=
  if h : IsExterior K S I then χ (Ideal.Quotient.mk _ (D.generator (toExterior K S I h))) else 0

variable (c : S.integer K) (χ : MulChar (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) ℂ)

omit [Fintype S] in
theorem generatorCharacter_of_not {I : Ideal (𝓞 K)} (hI : ¬ IsExterior K S I) :
    generatorCharacter K S D c χ I = 0 :=
  dite_eq_right hI

omit [Fintype S] in
theorem generatorCharacter_bot : generatorCharacter K S D c χ ⊥ = 0 :=
  generatorCharacter_of_not K S D c χ (fun h => h.1 rfl)

theorem generatorCharacter_mul (hD : AllowedGeneratorInput K S D)
    (hχ : SixthPowerTrivial K S c χ) (I J : Ideal (𝓞 K)) :
    generatorCharacter K S D c χ (I * J) =
      generatorCharacter K S D c χ I * generatorCharacter K S D c χ J := by
  by_cases hI : IsExterior K S I
  · by_cases hJ : IsExterior K S J
    · have hIJ : IsExterior K S (I * J) := (isExterior_mul_iff K S).mpr ⟨hI, hJ⟩
      obtain ⟨u, hu⟩ := hD.multiplicative (toExterior K S I hI) (toExterior K S J hJ)
      simp only [generatorCharacter, dite_eq_left hIJ, dite_eq_left hI, dite_eq_left hJ]
      rw [toExterior_mul K S hI hJ hIJ, hu]
      simp only [map_mul, hχ u, one_mul]
    · rw [generatorCharacter_of_not K S D c χ (fun h => hJ ((isExterior_mul_iff K S).mp h).2),
        generatorCharacter_of_not K S D c χ hJ, mul_zero]
  · rw [generatorCharacter_of_not K S D c χ (fun h => hI ((isExterior_mul_iff K S).mp h).1),
      generatorCharacter_of_not K S D c χ hI, zero_mul]

theorem generatorCharacter_top (hD : AllowedGeneratorInput K S D)
    (hχ : SixthPowerTrivial K S c χ) : generatorCharacter K S D c χ ⊤ = 1 := by
  obtain ⟨u, hu⟩ := AllowedGeneratorInput.generator_eq_sixth_power_of_ideal_eq_one K S D hD
    (toExterior K S ⊤ (isExterior_top K S)) (Subtype.ext Ideal.one_eq_top.symm)
  rw [generatorCharacter, dite_eq_left (isExterior_top K S), hu, hχ u]

/-- The allowed-generator character as a monoid hom on ideals; openai's
`primaryIdealCharacter c χ`. -/
def generatorIdealHom (hD : AllowedGeneratorInput K S D) (hχ : SixthPowerTrivial K S c χ) :
    Ideal (𝓞 K) →* ℂ where
  toFun := generatorCharacter K S D c χ
  map_one' := by rw [Ideal.one_eq_top]; exact generatorCharacter_top K S D c χ hD hχ
  map_mul' := generatorCharacter_mul K S D c χ hD hχ

theorem generatorIdealHom_apply (hD : AllowedGeneratorInput K S D)
    (hχ : SixthPowerTrivial K S c χ) (I : Ideal (𝓞 K)) :
    generatorIdealHom K S D c χ hD hχ I = generatorCharacter K S D c χ I :=
  rfl

/-- openai's `QuadraticInitialBound.norm_finite_character_le_one`. -/
theorem norm_mulChar_le_one {R : Type*} [CommRing R] [Finite R] (ψ : MulChar R ℂ) (r : R) :
    ‖ψ r‖ ≤ 1 := by
  have : Fintype R := Fintype.ofFinite R
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    simpa only [MulChar.coe_equivToUnitHom] using
      (Complex.norm_eq_one_of_mem_rootsOfUnity (MulChar.apply_mem_rootsOfUnity (χ := ψ) u)).le
  · rw [MulChar.map_nonunit ψ hr, norm_zero]
    exact zero_le_one

theorem norm_generatorCharacter_le_one (hc : c ≠ 0) (I : Ideal (𝓞 K)) :
    ‖generatorCharacter K S D c χ I‖ ≤ 1 := by
  have := HeckeGeneral.Arithmetic.finite_sIntegerPrincipalResidue K S c hc
  unfold generatorCharacter
  split_ifs
  · exact norm_mulChar_le_one χ _
  · simp

omit [Fintype S] in
theorem generatorCharacter_mulChar (ξ : MulChar (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) ℂ)
    (I : Ideal (𝓞 K)) :
    generatorCharacter K S D c (χ * ξ) I =
      generatorCharacter K S D c χ I * generatorCharacter K S D c ξ I := by
  unfold generatorCharacter
  split_ifs
  · exact MulChar.mul_apply χ ξ _
  · exact (mul_zero 0).symm

omit [Fintype S] in
/-- Sums over exterior ideals are sums over all ideals; openai's
`tsum_primaryIdealCharacter_all`. -/
theorem tsum_exterior_eq (f : Ideal (𝓞 K) → ℂ) :
    (∑' I : ExteriorIdeal K S, generatorCharacter K S D c χ I.val.val * f I.val.val) =
      ∑' I : Ideal (𝓞 K), generatorCharacter K S D c χ I * f I := by
  have he : Function.Injective (fun I : ExteriorIdeal K S => I.val.val) :=
    fun I J h => Subtype.ext (Subtype.ext h)
  have hs : Function.support (fun I : Ideal (𝓞 K) => generatorCharacter K S D c χ I * f I) ⊆
      Set.range (fun I : ExteriorIdeal K S => I.val.val) := by
    intro I hI
    by_cases h : IsExterior K S I
    · exact ⟨toExterior K S I h, rfl⟩
    · exact (hI (by simp only [generatorCharacter_of_not K S D c χ h, zero_mul])).elim
  exact he.tsum_eq hs

end HeckePort.CenteredMomentGenerator
