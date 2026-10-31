import HeckeSkeleton.Moments.MOM_ENGINE_STEP.LocalAmplifier
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.LocalCorrelation
import DedekindZetaZeroFree.CharacterSums.Gauss.LocalUnitRescaling
import DedekindZetaZeroFree.CharacterSums.Gauss.PrimePowerChineseRemainders

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

end HeckeSkeleton.Moments.EngineStep
