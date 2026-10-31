import HeckeSkeleton.Moments.MOM_ENGINE_STEP.LocalAmplifier
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.LocalCorrelation
import DedekindZetaZeroFree.CharacterSums.Gauss.LocalUnitRescaling
import DedekindZetaZeroFree.CharacterSums.Gauss.PrimePowerChineseRemainders
import DedekindZetaZeroFree.CharacterSums.Gauss.FiniteSupportReciprocityCancellation
import HeckePort.Moments.CommonSupport
import HeckePort.Moments.Support

/-!
# Actual CRT factors for one amplifier prime

`centralRawPrimePower` is the existing raw local factor from the complete
prime-power CRT decomposition.  This file retains its unit phases and
connects it to the proven valuation table, with no primitivity or
coprimality replacement of the finite coefficient.
-/

noncomputable section
open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

namespace HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree LocalFiniteSums CompatiblePrimeRawLocal

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- The exact unit phase in the raw local CRT factor when the row modulus
is prime to the auxiliary prime. -/
def localUnitPhase (p : ExteriorPrime A) (n : ℕ)
    (s a h : (LocalIntegers p)ˣ) : ℂ :=
  chiOnUnits (σ := σ) p h ^ (-(n : ℤ)) *
    chiOnUnits (σ := σ) p s ^ (n : ℤ) * chiOnUnits (σ := σ) p a ^ (n : ℤ)

theorem chiOnUnits_norm (p : ExteriorPrime A) (u : (LocalIntegers p)ˣ) :
    ‖chiOnUnits (σ := σ) p u‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (chiOnUnits_pow_six p u) (by decide)

theorem localUnitPhase_norm (p : ExteriorPrime A) (n : ℕ)
    (s a h : (LocalIntegers p)ˣ) : ‖localUnitPhase (σ := σ) p n s a h‖ = 1 := by
  simp only [localUnitPhase, norm_mul, norm_zpow, chiOnUnits_norm, one_zpow, one_mul]

/-- Central normalization of every actual local factor used by full CRT. -/
def centralRawLocalFactor (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t k J : ℕ) (s a h : (LocalIntegers p)ˣ) : ℂ :=
  R C p t k J s a h / (Q p : ℂ) ^ t

/-- The auxiliary prime is chosen prime to the old row modulus. -/
def centralRawPrimePower (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n J : ℕ) (s a h : (LocalIntegers p)ˣ) : ℂ :=
  centralRawLocalFactor C p n 0 J s a h

theorem centralRawPrimePower_rescale (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n J : ℕ) (s a h : (LocalIntegers p)ˣ) :
    centralRawPrimePower C p n J s a h =
      localUnitPhase (σ := σ) p n s a h * centralPrimePower C p n J := by
  unfold centralRawPrimePower centralRawLocalFactor centralPrimePower localUnitPhase
  rw [R_unit_rescale]
  simp only [Nat.cast_zero, zero_sub, sub_zero]
  ring

theorem centralRawPrimePower_norm (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n J : ℕ) (s a h : (LocalIntegers p)ˣ) :
    ‖centralRawPrimePower C p n J s a h‖ = ‖centralPrimePower C p n J‖ := by
  rw [centralRawPrimePower_rescale, norm_mul, localUnitPhase_norm, one_mul]

theorem chiOnUnits_sixth_mul (p : ExteriorPrime A) (h u : (LocalIntegers p)ˣ) :
    chiOnUnits (σ := σ) p (h * u ^ 6) = chiOnUnits (σ := σ) p h := by
  calc
    _ = chiOnUnits (σ := σ) p h * chiOnUnits (σ := σ) p u ^ 6 := by
      simp only [chiOnUnits, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
    _ = _ := by rw [chiOnUnits_pow_six, mul_one]

theorem localUnitPhase_sixth_unit (p : ExteriorPrime A) (n : ℕ)
    (s a h u : (LocalIntegers p)ˣ) :
    localUnitPhase (σ := σ) p n s a (h * u ^ 6) =
      localUnitPhase (σ := σ) p n s a h := by
  simp only [localUnitPhase, chiOnUnits_sixth_mul]

/-- This invariance also includes positive depth in the old row modulus. -/
theorem rawLocalFactor_sixth_unit (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t k J : ℕ) (s a h u : (LocalIntegers p)ˣ) :
    R C p t k J s a (h * u ^ 6) = R C p t k J s a h := by
  rw [R_unit_rescale, R_unit_rescale, chiOnUnits_sixth_mul]

theorem centralRawLocalFactor_sixth_unit (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t k J : ℕ) (s a h u : (LocalIntegers p)ˣ) :
    centralRawLocalFactor C p t k J s a (h * u ^ 6) =
      centralRawLocalFactor C p t k J s a h := by
  unfold centralRawLocalFactor
  rw [rawLocalFactor_sixth_unit]

/-- Away from the insertion prime the local multiplier is a sixth power
of a unit, so the full raw factor, including its phase, is unchanged. -/
theorem centralRawPrimePower_sixth_unit (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n J : ℕ) (s a h u : (LocalIntegers p)ˣ) :
    centralRawPrimePower C p n J s a (h * u ^ 6) =
      centralRawPrimePower C p n J s a h := by
  rw [centralRawPrimePower_rescale, centralRawPrimePower_rescale, localUnitPhase_sixth_unit]

/-- The complete local factor, with its common unit phase, changes only
at the three valuations used by the one-pool amplifier. -/
theorem centralRawPrimePower_difference_support (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (s a h : (LocalIntegers p)ˣ)
    (hne : centralRawPrimePower C p n 0 s a h ≠ centralRawPrimePower C p n 6 s a h) :
    n = 1 ∨ n = 6 ∨ n = 7 := by
  apply centralPrimePower_difference_support C p n
  intro he
  apply hne
  rw [centralRawPrimePower_rescale, centralRawPrimePower_rescale, he]

theorem centralRawPrimePower_one_norm_sq (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (s a h : (LocalIntegers p)ˣ) :
    ‖centralRawPrimePower C p 1 0 s a h‖ ^ 2 = (Q p)⁻¹ := by
  rw [centralRawPrimePower_norm, centralPrimePower_one_norm_sq]

theorem centralRawPrimePower_six_norm_sq (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (s a h : (LocalIntegers p)ˣ) :
    ‖centralRawPrimePower C p 6 6 s a h‖ ^ 2 = (1 - (Q p)⁻¹) ^ 2 := by
  rw [centralRawPrimePower_norm, centralPrimePower_six_norm_sq]

theorem centralRawPrimePower_seven_norm_sq (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (s a h : (LocalIntegers p)ˣ) :
    ‖centralRawPrimePower C p 7 6 s a h‖ ^ 2 = (Q p)⁻¹ := by
  rw [centralRawPrimePower_norm, centralPrimePower_seven_norm_sq]

/-- The complete raw correction has exactly the same squared costs as
the local table, because its common unit phase has modulus one. -/
theorem centralRawPrimePower_difference_norm_sq
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (n : ℕ)
    (s a h : (LocalIntegers p)ˣ) :
    ‖centralRawPrimePower C p n 0 s a h - centralRawPrimePower C p n 6 s a h‖ ^ 2 =
      if n = 1 then (Q p)⁻¹
      else if n = 6 then (1 - (Q p)⁻¹) ^ 2
      else if n = 7 then (Q p)⁻¹ else 0 := by
  rw [centralRawPrimePower_rescale, centralRawPrimePower_rescale, ← mul_sub,
    norm_mul, localUnitPhase_norm, one_mul, centralPrimePower_difference_norm_sq]

/-- The same three rows include the local-unit change produced by the
global sixth-power insertion. -/
theorem centralRawPrimePower_amplified_difference_support
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (n : ℕ)
    (s a h u : (LocalIntegers p)ˣ)
    (hne : centralRawPrimePower C p n 0 s a h ≠
      centralRawPrimePower C p n 6 s a (h * u ^ 6)) :
    n = 1 ∨ n = 6 ∨ n = 7 := by
  rw [centralRawPrimePower_sixth_unit] at hne
  exact centralRawPrimePower_difference_support C p n s a h hne

/-- A complete CRT product changes only at valuations `1`, `6`, and `7`
of the one inserted prime.  The hypotheses state exactly what multiplication
of the frequency by that prime's sixth power does to each local valuation. -/
theorem rawCRT_product_difference_support
    (C : A.GeneralArithmeticContext σ η hS) (P : Finset (ExteriorPrime A))
    (p : ExteriorPrime A) (hp : p ∈ P)
    (t k J J' : ExteriorPrime A → ℕ)
    (s a h u : ∀ q : ExteriorPrime A, (LocalIntegers q)ˣ)
    (hk : k p = 0) (hJ : J p = 0) (hJ' : J' p = 6)
    (hother : ∀ q ∈ P, q ≠ p → J' q = J q)
    (hne : (∏ q ∈ P, centralRawLocalFactor C q (t q) (k q) (J q) (s q) (a q) (h q)) ≠
      ∏ q ∈ P, centralRawLocalFactor C q (t q) (k q) (J' q)
        (s q) (a q) (h q * u q ^ 6)) :
    t p = 1 ∨ t p = 6 ∨ t p = 7 := by
  by_contra hn
  apply hne
  apply Finset.prod_congr rfl
  intro q hq
  by_cases hqp : q = p
  · subst q
    rw [hk, hJ, hJ', centralRawLocalFactor_sixth_unit]
    change centralRawPrimePower C p (t p) 0 (s p) (a p) (h p) =
      centralRawPrimePower C p (t p) 6 (s p) (a p) (h p)
    by_contra hc
    exact hn (centralRawPrimePower_difference_support C p (t p) (s p) (a p) (h p) hc)
  · rw [hother q hq hqp, centralRawLocalFactor_sixth_unit]

open MaskedQuotientCRT

/-- The product normalization is the actual complete ideal norm. -/
theorem prime_power_norm_factorization (C : A.GeneralArithmeticContext σ η hS)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (P : Finset (ExteriorPrime A))
    (hSupport : ∀ p : ExteriorPrime A, primeExponent p I ≠ 0 → p ∈ P) :
    (∏ p ∈ P, (Q p : ℂ) ^ primeExponent p I) = (A.exteriorNorm I : ℂ) := by
  letI : Finite (FiniteTransform.Residue A.R.toSubring a) := by
    change Finite (A.R ⧸ Ideal.span {a})
    rw [ha.2]
    exact A.exteriorResidue_finite I
  letI : Fintype (FiniteTransform.Residue A.R.toSubring a) := Fintype.ofFinite _
  let e := MaskedPrimePowerCRTFactorization.quotientPiEquiv C I a ha P hSupport
  have hc := Fintype.card_congr e.toEquiv
  rw [Fintype.card_pi] at hc
  have hn : (Fintype.card (FiniteTransform.Residue A.R.toSubring a) : ℂ) =
      (A.exteriorNorm I : ℂ) := by
    rw [← Nat.card_eq_fintype_card]
    change (Nat.card (A.R ⧸ Ideal.span {a}) : ℂ) = _
    rw [ha.2, A.exteriorResidue_card]
    simp [SArithmeticData.exteriorNorm, idealNorm]
  calc
    _ = ∏ p : P, (Q p.val : ℂ) ^ primeExponent p.val I := by
      exact (Finset.prod_coe_sort P _).symm
    _ = ∏ p : P, (Fintype.card (Residue C p.val (primeExponent p.val I)) : ℂ) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact (localPrimePowerResidue_card C p.val _).symm
    _ = (Fintype.card (FiniteTransform.Residue A.R.toSubring a) : ℂ) := by
      exact_mod_cast hc.symm
    _ = _ := hn

/-- The full original finite coefficient, multiplied by an arbitrary whole
centered coefficient, has the exact complete CRT product.  The denominator
is displayed as a product of local norms so the normalization is reviewable. -/
theorem whole_coefficient_full_prime_power_crt
    (C : A.GeneralArithmeticContext σ η hS)
    (Is Ia Ih : A.Exterior) (s a h : A.R)
    (hs : A.Generates Is s) (ha : A.Generates Ia a) (hh : A.Generates Ih h)
    (hsAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (s : F) (by exact_mod_cast hs.1)))
    (haAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (a : F) (by exact_mod_cast ha.1)))
    (P : Finset (ExteriorPrime A))
    (hSupportS : ∀ p : ExteriorPrime A, primeExponent p Is ≠ 0 → p ∈ P)
    (hSupportA : ∀ p : ExteriorPrime A, primeExponent p Ia ≠ 0 → p ∈ P)
    (hSupportH : ∀ p : ExteriorPrime A, primeExponent p Ih ≠ 0 → p ∈ P)
    (whole : ℂ) :
    whole * MaskedQuotientCRT.coefficient C Is Ia s a h hs ha /
        (∏ p ∈ P, (Q p : ℂ) ^ primeExponent p Ia) =
      whole * ∏ p ∈ P,
        (R C p (primeExponent p Ia) (primeExponent p Is) (primeExponent p Ih)
          (localUnitPart C p Is s hs) (localUnitPart C p Ia a ha)
          (localUnitPart C p Ih h hh) / (Q p : ℂ) ^ primeExponent p Ia) := by
  rw [full_prime_power_crt C Is Ia Ih s a h hs ha hh hsAllowed haAllowed P
    hSupportS hSupportA hSupportH, Finset.prod_div_distrib]
  ring

/-- The complete finite coefficient has the same CRT formula with the
literal ideal norm in the central denominator. -/
theorem whole_coefficient_full_prime_power_crt_norm
    (C : A.GeneralArithmeticContext σ η hS)
    (Is Ia Ih : A.Exterior) (s a h : A.R)
    (hs : A.Generates Is s) (ha : A.Generates Ia a) (hh : A.Generates Ih h)
    (hsAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (s : F) (by exact_mod_cast hs.1)))
    (haAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (a : F) (by exact_mod_cast ha.1)))
    (P : Finset (ExteriorPrime A))
    (hSupportS : ∀ p : ExteriorPrime A, primeExponent p Is ≠ 0 → p ∈ P)
    (hSupportA : ∀ p : ExteriorPrime A, primeExponent p Ia ≠ 0 → p ∈ P)
    (hSupportH : ∀ p : ExteriorPrime A, primeExponent p Ih ≠ 0 → p ∈ P)
    (whole : ℂ) :
    whole * MaskedQuotientCRT.coefficient C Is Ia s a h hs ha / (A.exteriorNorm Ia : ℂ) =
      whole * ∏ p ∈ P,
        centralRawLocalFactor C p (primeExponent p Ia) (primeExponent p Is)
          (primeExponent p Ih) (localUnitPart C p Is s hs)
          (localUnitPart C p Ia a ha) (localUnitPart C p Ih h hh) := by
  rw [← prime_power_norm_factorization C Ia a ha P hSupportA]
  exact whole_coefficient_full_prime_power_crt C Is Ia Ih s a h hs ha hh
    hsAllowed haAllowed P hSupportS hSupportA hSupportH whole

section CompleteCommonSupport

open HeckePort.Moments HeckePort.Moments.CommonSupport

/-- The source's actual sextic character on the complete generated ideal. -/
def generatedIdealCharacter (I : A.Exterior) (a : A.R) (ha : A.Generates I a) :
    MulChar (A.R ⧸ Ideal.span {a}) ℂ :=
  GeneratorInvariance.transportCharacter _ _ ha.2.symm (A.sexticResiduePowerChar σ I 1)

theorem generatedIdealCharacter_mk (I : A.Exterior) (a : A.R)
    (ha : A.Generates I a) (x : A.R) :
    generatedIdealCharacter (σ := σ) I a ha (Ideal.Quotient.mk _ x) =
      σ (A.sexticResidue I x) := by
  rw [generatedIdealCharacter, transportCharacter_mk]
  have he : SArithmeticData.sexticExponent (1 : ℤ) = 1 := by decide
  rw [SArithmeticData.sexticResiduePowerChar, he, pow_one]
  by_cases hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal I) x)
  · change _ = σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)
    rw [← hx.unit_spec, MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe]
    rfl
  · rw [MulChar.map_nonunit _ hx]
    change 0 = σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)
    rw [MulChar.map_nonunit _ hx, map_zero]

/-- Character factorization is derived from the actual normalized sextic
family, including the original nonunit zeros. -/
theorem generatedIdealCharacter_mul (I J IJ : A.Exterior)
    (hIJ : IJ.val = I.val * J.val) (a b : A.R)
    (ha : A.Generates I a) (hb : A.Generates J b)
    (hab : A.Generates IJ (a * b)) (x : A.R) :
    generatedIdealCharacter (σ := σ) IJ (a * b) hab (Ideal.Quotient.mk _ x) =
      generatedIdealCharacter (σ := σ) I a ha (Ideal.Quotient.mk _ x) *
        generatedIdealCharacter (σ := σ) J b hb (Ideal.Quotient.mk _ x) := by
  simp only [generatedIdealCharacter_mk]
  rw [A.sexticResidueFamily_normalized.2.2 I J IJ hIJ x, map_mul]

/-- Ideal coprimality of genuine extracted pieces implies the exact
generator coprimality required by the finite CRT transform. -/
theorem generated_elements_coprime (I J : A.Exterior) (a b : A.R)
    (ha : A.Generates I a) (hb : A.Generates J b) (hcop : IsCoprime I.val J.val) :
    IsCoprime a b := by
  apply (Ideal.sup_eq_top_iff_isCoprime a b).mp
  rw [ha.2, hb.2]
  change Ideal.map (algebraMap (𝓞 F) A.R) I.val ⊔
    Ideal.map (algebraMap (𝓞 F) A.R) J.val = ⊤
  rw [← Ideal.map_sup, hcop.sup_eq, Ideal.map_top]

/-- Complete common-support extraction instantiated with the actual
source characters; no abstract character-factorization premise remains. -/
theorem actual_complete_common_support
    (ID IE IA IB IDA IEB : A.Exterior)
    (hIDA : IDA.val = ID.val * IA.val) (hIEB : IEB.val = IE.val * IB.val)
    (d e a b : A.R)
    (hd : A.Generates ID d) (he : A.Generates IE e)
    (ha : A.Generates IA a) (hb : A.Generates IB b)
    (hda : A.Generates IDA (d * a)) (heb : A.Generates IEB (e * b))
    (hca : IsCoprime (d * e) a) (hcb : IsCoprime (d * e) b) (hcab : IsCoprime a b)
    [Fintype (A.R ⧸ Ideal.span {d})] [Fintype (A.R ⧸ Ideal.span {e})]
    [Fintype (A.R ⧸ Ideal.span {a})] [Fintype (A.R ⧸ Ideal.span {b})]
    [Fintype (A.R ⧸ Ideal.span {d * a})] [Fintype (A.R ⧸ Ideal.span {e * b})]
    (j : A.R) :
    fullModulusCorrelation (d * a) (e * b)
      (generatedIdealCharacter (σ := σ) IDA (d * a) hda)
      (generatedIdealCharacter (σ := σ) IEB (e * b) heb) j =
      fullModulusCorrelation d e (generatedIdealCharacter (σ := σ) ID d hd)
        (generatedIdealCharacter (σ := σ) IE e he) j *
        (σ (A.sexticResidue IE a) * star (σ (A.sexticResidue IA e))) *
        (σ (A.sexticResidue IB d) * star (σ (A.sexticResidue ID b))) *
        (σ (A.sexticResidue IB a) * star (σ (A.sexticResidue IA b))) *
        σ (A.sexticResidue IA j) * star (σ (A.sexticResidue IB (-j))) := by
  have h := fullModulusCorrelation_complete_support d e a b hca hcb hcab
    (generatedIdealCharacter (σ := σ) ID d hd) (generatedIdealCharacter (σ := σ) IE e he)
    (generatedIdealCharacter (σ := σ) IA a ha) (generatedIdealCharacter (σ := σ) IB b hb)
    (generatedIdealCharacter (σ := σ) IDA (d * a) hda)
    (generatedIdealCharacter (σ := σ) IEB (e * b) heb)
    (generatedIdealCharacter_mul (σ := σ) ID IA IDA hIDA d a hd ha hda)
    (generatedIdealCharacter_mul (σ := σ) IE IB IEB hIEB e b he hb heb) j
  simpa only [generatedIdealCharacter_mk] using h

open HeckePort.Moments.Support

private theorem exterior_factor_support (I : A.Exterior) (J : Ideal (𝓞 F))
    (hJI : J ∣ I.val) : J ⊔ A.cS = ⊤ := by
  apply top_unique
  rw [← I.property.2]
  exact sup_le_sup_right (Ideal.dvd_iff_le.mp hJI) _

/-- The complete part supported on a chosen prime set, as a genuine exterior ideal. -/
def extractedExterior (I : A.Exterior) (S : Finset (Ideal (𝓞 F))) : A.Exterior :=
  ⟨supportExtract I.val S, supportExtract_ne_zero I.val S,
    exterior_factor_support I _ (by
      simpa only [support_reconstruct I.val I.property.1 S] using
        dvd_mul_right (supportExtract I.val S) (supportResidual I.val S))⟩

/-- The complementary part keeps every remaining prime multiplicity. -/
def residualExterior (I : A.Exterior) (S : Finset (Ideal (𝓞 F))) : A.Exterior :=
  ⟨supportResidual I.val S, supportResidual_ne_zero I.val S,
    exterior_factor_support I _ (by
      simpa only [support_reconstruct I.val I.property.1 S] using
        dvd_mul_left (supportResidual I.val S) (supportExtract I.val S))⟩

theorem extractedExterior_reconstruct (I : A.Exterior) (S : Finset (Ideal (𝓞 F))) :
    (extractedExterior I S).val * (residualExterior I S).val = I.val :=
  support_reconstruct I.val I.property.1 S

theorem generated_product (I J IJ : A.Exterior) (hIJ : IJ.val = I.val * J.val)
    (a b : A.R) (ha : A.Generates I a) (hb : A.Generates J b) :
    A.Generates IJ (a * b) := by
  refine ⟨mul_ne_zero ha.1 hb.1, ?_⟩
  rw [← Ideal.span_singleton_mul_span_singleton, ha.2, hb.2]
  change Ideal.map (algebraMap (𝓞 F) A.R) I.val *
    Ideal.map (algebraMap (𝓞 F) A.R) J.val =
      Ideal.map (algebraMap (𝓞 F) A.R) IJ.val
  rw [hIJ, Ideal.map_mul]

/-- Complete finite correlation associated with the specified actual generators. -/
def generatedIdealCorrelation (I J : A.Exterior) (a b : A.R)
    (ha : A.Generates I a) (hb : A.Generates J b) (j : A.R) : ℂ := by
  letI : Finite (A.R ⧸ Ideal.span {a}) := by
    rw [ha.2]
    exact A.exteriorResidue_finite I
  letI : Finite (A.R ⧸ Ideal.span {b}) := by
    rw [hb.2]
    exact A.exteriorResidue_finite J
  letI : Fintype (A.R ⧸ Ideal.span {a}) := Fintype.ofFinite _
  letI : Fintype (A.R ⧸ Ideal.span {b}) := Fintype.ofFinite _
  exact fullModulusCorrelation a b (generatedIdealCharacter (σ := σ) I a ha)
    (generatedIdealCharacter (σ := σ) J b hb) j

/-- Canonical common support is constructed from the normalized factors
of the original ideals.  It supplies all required coprimalities, so this
actual extraction theorem has no abstract common-support formula premise.
The parent is presented by the products of its two chosen factor generators. -/
theorem actual_canonical_common_support (I J : A.Exterior) (j : A.R) :
    let S := HeckePort.IdealMobiusDivisorSum.primeSupport I.val ∩
      HeckePort.IdealMobiusDivisorSum.primeSupport J.val
    let ID := extractedExterior I S
    let IE := extractedExterior J S
    let IA := residualExterior I S
    let IB := residualExterior J S
    ∀ (d e a b : A.R) (hd : A.Generates ID d) (he : A.Generates IE e)
      (ha : A.Generates IA a) (hb : A.Generates IB b),
    generatedIdealCorrelation (σ := σ) I J (d * a) (e * b)
      (generated_product ID IA I (extractedExterior_reconstruct I S).symm d a hd ha)
      (generated_product IE IB J (extractedExterior_reconstruct J S).symm e b he hb) j =
      generatedIdealCorrelation (σ := σ) ID IE d e hd he j *
        (σ (A.sexticResidue IE a) * star (σ (A.sexticResidue IA e))) *
        (σ (A.sexticResidue IB d) * star (σ (A.sexticResidue ID b))) *
        (σ (A.sexticResidue IB a) * star (σ (A.sexticResidue IA b))) *
        σ (A.sexticResidue IA j) * star (σ (A.sexticResidue IB (-j))) := by
  intro S ID IE IA IB d e a b hd he ha hb
  have hDa : IsCoprime ID.val IA.val := extracted_residual_coprime I.val I.val S
  have hEa : IsCoprime IE.val IA.val := extracted_residual_coprime J.val I.val S
  have hDb : IsCoprime ID.val IB.val := extracted_residual_coprime I.val J.val S
  have hEb : IsCoprime IE.val IB.val := extracted_residual_coprime J.val J.val S
  have hab : IsCoprime IA.val IB.val := common_support_residual_coprime I.val J.val
  have hca : IsCoprime (d * e) a :=
    (generated_elements_coprime ID IA d a hd ha hDa).mul_left
      (generated_elements_coprime IE IA e a he ha hEa)
  have hcb : IsCoprime (d * e) b :=
    (generated_elements_coprime ID IB d b hd hb hDb).mul_left
      (generated_elements_coprime IE IB e b he hb hEb)
  have hcab : IsCoprime a b := generated_elements_coprime IA IB a b ha hb hab
  have hda := generated_product ID IA I (extractedExterior_reconstruct I S).symm d a hd ha
  have heb := generated_product IE IB J (extractedExterior_reconstruct J S).symm e b he hb
  letI : Finite (A.R ⧸ Ideal.span {d}) := by rw [hd.2]; exact A.exteriorResidue_finite ID
  letI : Finite (A.R ⧸ Ideal.span {e}) := by rw [he.2]; exact A.exteriorResidue_finite IE
  letI : Finite (A.R ⧸ Ideal.span {a}) := by rw [ha.2]; exact A.exteriorResidue_finite IA
  letI : Finite (A.R ⧸ Ideal.span {b}) := by rw [hb.2]; exact A.exteriorResidue_finite IB
  letI : Finite (A.R ⧸ Ideal.span {d * a}) := by rw [hda.2]; exact A.exteriorResidue_finite I
  letI : Finite (A.R ⧸ Ideal.span {e * b}) := by rw [heb.2]; exact A.exteriorResidue_finite J
  letI : Fintype (A.R ⧸ Ideal.span {d}) := Fintype.ofFinite _
  letI : Fintype (A.R ⧸ Ideal.span {e}) := Fintype.ofFinite _
  letI : Fintype (A.R ⧸ Ideal.span {a}) := Fintype.ofFinite _
  letI : Fintype (A.R ⧸ Ideal.span {b}) := Fintype.ofFinite _
  letI : Fintype (A.R ⧸ Ideal.span {d * a}) := Fintype.ofFinite _
  letI : Fintype (A.R ⧸ Ideal.span {e * b}) := Fintype.ofFinite _
  exact actual_complete_common_support ID IE IA IB I J
    (extractedExterior_reconstruct I S).symm (extractedExterior_reconstruct J S).symm
    d e a b hd he ha hb hda heb hca hcb hcab j

end CompleteCommonSupport

section GeneratorReplacement

/-- At the unit first modulus the original double finite coefficient is
the ordinary finite Gauss column.  Lift independence justifies the zero
representative of the one-element first quotient. -/
theorem finiteCoefficient_unit_modulus (R : Subring F) (a h : R) (ha : a ≠ 0)
    [Fintype (FiniteTransform.Residue R (1 : R))]
    [Fintype (FiniteTransform.Residue R a)]
    (χ₁ : MulChar (FiniteTransform.Residue R (1 : R)) ℂ)
    (χa : MulChar (FiniteTransform.Residue R a) ℂ)
    (e : AddChar F ℂ) (he : FiniteTransform.IsTrivialOn R e) :
    FiniteTransform.finiteCoefficient R 1 a h χ₁ χa e =
      FiniteTransform.gaussSum R a χa e h := by
  letI : Subsingleton (FiniteTransform.Residue R (1 : R)) := by
    change Subsingleton (R ⧸ Ideal.span {(1 : R)})
    rw [Ideal.span_singleton_one]
    infer_instance
  letI : Unique (FiniteTransform.Residue R (1 : R)) :=
    ⟨⟨0⟩, fun x => Subsingleton.elim x 0⟩
  let ds : FiniteTransform.ResidueLifts R (1 : R) :=
    ⟨fun _ => 0, fun _ => Subsingleton.elim _ _⟩
  have hχ (x : FiniteTransform.Residue R (1 : R)) : χ₁ x = 1 := by
    rw [Subsingleton.elim x 1, map_one]
  have hcond (x : FiniteTransform.Residue R (1 : R)) :
      FiniteTransform.residueMap R 1 h = FiniteTransform.residueMap R 1 a * x :=
    Subsingleton.elim _ _
  rw [← FiniteTransform.finiteCoefficient_lifts_independent R 1 a h one_ne_zero ha
    χ₁ χa e he ds (FiniteTransform.canonicalLifts R a)]
  simp [FiniteTransform.finiteCoefficientWithLifts, FiniteTransform.gaussSum,
    FiniteTransform.gaussSumWithLifts, ds, hχ, hcond]

/-- The unit ideal, retained as an exterior ideal. -/
def unitExterior (A : SArithmeticData F) : A.Exterior :=
  ⟨⊤, top_ne_bot, by simp⟩

theorem unitExterior_generates (A : SArithmeticData F) :
    A.Generates (unitExterior A) (1 : A.R) := by
  refine ⟨one_ne_zero, ?_⟩
  simp [unitExterior, SArithmeticData.extendIdeal]

/-- Allowed presentations of the same complete ideals give the same
actual finite column at every frequency.  Compatibility is derived from
the source arithmetic recipes, rather than being postulated for the column. -/
theorem actual_finite_column_generator_replacement
    (C : A.GeneralArithmeticContext σ η hS)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B D)
    (Is Ia : A.Exterior) (s a s' a' h : A.R)
    (hs : A.Generates Is s) (ha : A.Generates Ia a)
    (hs' : A.Generates Is s') (ha' : A.Generates Ia a')
    (hsa : A.IsAllowed C.correction.B (Units.mk0 (s : F) (by exact_mod_cast hs.1)))
    (haa : A.IsAllowed C.correction.B (Units.mk0 (a : F) (by exact_mod_cast ha.1)))
    (hsa' : A.IsAllowed C.correction.B (Units.mk0 (s' : F) (by exact_mod_cast hs'.1)))
    (haa' : A.IsAllowed C.correction.B (Units.mk0 (a' : F) (by exact_mod_cast ha'.1))) :
    MaskedQuotientCRT.coefficient C Is Ia s' a' h hs' ha' =
      MaskedQuotientCRT.coefficient C Is Ia s a h hs ha := by
  have hCompatible := GlobalPairCancel.HasArithmeticRecipes.compatible
    A σ hS C.correction.B D hD
  have hOne : A.IsAllowed C.correction.B (1 : Fˣ) := by
    simp [SArithmeticData.IsAllowed]
  have he := GeneratorInvariance.coefficient_allowed_generator_replacement
    A D hCompatible C.classGroup_trivial C.correction.H C.correction.B
    C.correction.B_complement Ia (unitExterior A) Is (unitExterior A)
    a 1 s 1 a' 1 s' 1 h ha (unitExterior_generates A) hs (unitExterior_generates A)
    ha' (unitExterior_generates A) hs' (unitExterior_generates A)
    (Units.mk0 (a : F) (by exact_mod_cast ha.1)) 1
    (Units.mk0 (s : F) (by exact_mod_cast hs.1)) 1
    (Units.mk0 (a' : F) (by exact_mod_cast ha'.1)) 1
    (Units.mk0 (s' : F) (by exact_mod_cast hs'.1)) 1
    rfl rfl rfl rfl rfl rfl rfl rfl
    ⟨haa, hOne, hsa, hOne⟩ ⟨haa', hOne, hsa', hOne⟩
  have he' : GeneratorInvariance.coefficient A D s' a' h hs'.1 ha'.1 =
      GeneratorInvariance.coefficient A D s a h hs.1 ha.1 := by
    simpa only [one_pow, mul_one] using he
  rw [GlobalPairCancel.HasArithmeticRecipes.coefficient_eq_crt
      A σ η hS C.correction.B D hD C Is Ia s' a' h hs' ha',
    GlobalPairCancel.HasArithmeticRecipes.coefficient_eq_crt
      A σ η hS C.correction.B D hD C Is Ia s a h hs ha] at he'
  exact he'

/-- The generator replacement is made on the whole centered column,
before an absolute value, and preserves its actual central normalization. -/
theorem whole_finite_column_generator_replacement
    (C : A.GeneralArithmeticContext σ η hS)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B D)
    (Is Ia : A.Exterior) (s a s' a' h : A.R)
    (hs : A.Generates Is s) (ha : A.Generates Ia a)
    (hs' : A.Generates Is s') (ha' : A.Generates Ia a')
    (hsa : A.IsAllowed C.correction.B (Units.mk0 (s : F) (by exact_mod_cast hs.1)))
    (haa : A.IsAllowed C.correction.B (Units.mk0 (a : F) (by exact_mod_cast ha.1)))
    (hsa' : A.IsAllowed C.correction.B (Units.mk0 (s' : F) (by exact_mod_cast hs'.1)))
    (haa' : A.IsAllowed C.correction.B (Units.mk0 (a' : F) (by exact_mod_cast ha'.1)))
    (whole : ℂ) :
    whole * MaskedQuotientCRT.coefficient C Is Ia s' a' h hs' ha' /
        (A.exteriorNorm Ia : ℂ) =
      whole * MaskedQuotientCRT.coefficient C Is Ia s a h hs ha /
        (A.exteriorNorm Ia : ℂ) := by
  rw [actual_finite_column_generator_replacement C D hD Is Ia s a s' a' h
    hs ha hs' ha' hsa haa hsa' haa']

/-- The same allowed-generator replacement specialized to the actual
Gauss-column case, with no auxiliary first modulus. -/
theorem actual_gauss_column_generator_replacement
    (C : A.GeneralArithmeticContext σ η hS)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B D)
    (Ia : A.Exterior) (a a' h : A.R)
    (ha : A.Generates Ia a) (ha' : A.Generates Ia a')
    (haa : A.IsAllowed C.correction.B (Units.mk0 (a : F) (by exact_mod_cast ha.1)))
    (haa' : A.IsAllowed C.correction.B (Units.mk0 (a' : F) (by exact_mod_cast ha'.1))) :
    MaskedQuotientCRT.coefficient C (unitExterior A) Ia 1 a' h
      (unitExterior_generates A) ha' =
      MaskedQuotientCRT.coefficient C (unitExterior A) Ia 1 a h
        (unitExterior_generates A) ha := by
  apply actual_finite_column_generator_replacement C D hD (unitExterior A) Ia
    1 a 1 a' h (unitExterior_generates A) ha (unitExterior_generates A) ha'
  · simp [SArithmeticData.IsAllowed]
  · exact haa
  · simp [SArithmeticData.IsAllowed]
  · exact haa'

end GeneratorReplacement

end HeckeSkeleton.Moments.EngineStep
