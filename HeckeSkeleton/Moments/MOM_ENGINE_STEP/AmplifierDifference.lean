import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualPool

/-!
# Exact local differences inside the original whole amplifier polynomial

The actual sixth-power insertion changes one complete CRT factor. The
common unit phase and every other original factor are retained. At each
fixed valuation, the genuine complex difference from the local table
factors out of the whole polynomial before any absolute value. Thus its
one/six/seven squared sizes apply to the actual correction energy.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open LocalFiniteSums CompatiblePrimeRawLocal MaskedQuotientCRT

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

def actualCRTComplement (C : A.GeneralArithmeticContext σ η hS)
    (P : Finset (ExteriorPrime A)) (p : ExteriorPrime A)
    (t k J : ExteriorPrime A → ℕ)
    (s a h : ∀ q : ExteriorPrime A, (LocalIntegers q)ˣ) : ℂ :=
  ∏ q ∈ P.erase p, centralRawLocalFactor C q (t q) (k q) (J q) (s q) (a q) (h q)

/-- The complex difference, including the actual local unit phase, is
an exact identity for the complete CRT product. -/
theorem actualCRTColumn_difference_factor
    (C : A.GeneralArithmeticContext σ η hS)
    (P : Finset (ExteriorPrime A)) (p : ExteriorPrime A) (hp : p ∈ P)
    (t k J J' : ExteriorPrime A → ℕ)
    (s a h h' u : ∀ q : ExteriorPrime A, (LocalIntegers q)ˣ)
    (hk : k p = 0) (hJ : J p = 0) (hJ' : J' p = 6)
    (hother : ∀ q ∈ P, q ≠ p → J' q = J q)
    (hunit : ∀ q ∈ P, h' q = h q * u q ^ 6) :
    actualCRTColumn C P t k J s a h - actualCRTColumn C P t k J' s a h' =
      (centralPrimePower C p (t p) 0 - centralPrimePower C p (t p) 6) *
        (localUnitPhase (σ := σ) p (t p) (s p) (a p) (h p) *
          actualCRTComplement C P p t k J s a h) := by
  have hu : actualCRTColumn C P t k J' s a h' =
      actualCRTColumn C P t k J' s a h := by
    apply Finset.prod_congr rfl
    intro q hq
    rw [hunit q hq, centralRawLocalFactor_sixth_unit]
  rw [hu]
  have hrest : actualCRTComplement C P p t k J' s a h =
      actualCRTComplement C P p t k J s a h := by
    apply Finset.prod_congr rfl
    intro q hq
    rw [hother q (Finset.mem_erase.mp hq).2 (Finset.mem_erase.mp hq).1]
  have hsplit (M : ExteriorPrime A → ℕ) : actualCRTColumn C P t k M s a h =
      centralRawLocalFactor C p (t p) (k p) (M p) (s p) (a p) (h p) *
        actualCRTComplement C P p t k M s a h := by
    exact (Finset.mul_prod_erase P _ hp).symm
  rw [hsplit J, hsplit J', hrest, hk, hJ, hJ']
  change centralRawPrimePower C p (t p) 0 (s p) (a p) (h p) * _ -
    centralRawPrimePower C p (t p) 6 (s p) (a p) (h p) * _ = _
  rw [centralRawPrimePower_rescale, centralRawPrimePower_rescale]
  ring

def actualFiniteComplement (C : A.GeneralArithmeticContext σ η hS)
    (Is Ia Ih : A.Exterior) (s a h : A.R)
    (hs : A.Generates Is s) (ha : A.Generates Ia a) (hh : A.Generates Ih h)
    (P : Finset (ExteriorPrime A)) (p : ExteriorPrime A) : ℂ :=
  actualCRTComplement C P p
    (fun q => primeExponent q Ia) (fun q => primeExponent q Is) (fun q => primeExponent q Ih)
    (fun q => localUnitPart C q Is s hs) (fun q => localUnitPart C q Ia a ha)
    (fun q => localUnitPart C q Ih h hh)

def actualAmplifierResidualColumn (C : A.GeneralArithmeticContext σ η hS)
    (Is Ia Ih : A.Exterior) (s a h : A.R)
    (hs : A.Generates Is s) (ha : A.Generates Ia a) (hh : A.Generates Ih h)
    (P : Finset (ExteriorPrime A)) (p : ExteriorPrime A) : ℂ :=
  localUnitPhase (σ := σ) p (primeExponent p Ia)
      (localUnitPart C p Is s hs) (localUnitPart C p Ia a ha) (localUnitPart C p Ih h hh) *
    actualFiniteComplement C Is Ia Ih s a h hs ha hh P p

/-- The input is the original complete finite coefficient evaluated at
the original and literally amplified frequencies. All coordinate
relations are derived from their actual generated ideals. -/
theorem actualFiniteColumn_difference_factor
    (C : A.GeneralArithmeticContext σ η hS)
    (Is Ia Ih : A.Exterior) (s a h : A.R)
    (hs : A.Generates Is s) (ha : A.Generates Ia a) (hh : A.Generates Ih h)
    (hsAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (s : F) (by exact_mod_cast hs.1)))
    (haAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (a : F) (by exact_mod_cast ha.1)))
    (P : Finset (ExteriorPrime A)) (p : ExteriorPrime A) (hp : p ∈ P)
    (hSupportS : ∀ q : ExteriorPrime A, primeExponent q Is ≠ 0 → q ∈ P)
    (hSupportA : ∀ q : ExteriorPrime A, primeExponent q Ia ≠ 0 → q ∈ P)
    (hSupportH : ∀ q : ExteriorPrime A, primeExponent q Ih ≠ 0 → q ∈ P)
    (hk : primeExponent p Is = 0) (hJ : primeExponent p Ih = 0) :
    actualFiniteColumn C Is Ia s a hs ha h -
      actualFiniteColumn C Is Ia s a hs ha (h * generator C p ^ 6) =
      (centralPrimePower C p (primeExponent p Ia) 0 -
        centralPrimePower C p (primeExponent p Ia) 6) *
          actualAmplifierResidualColumn C Is Ia Ih s a h hs ha hh P p := by
  have hSupportH' : ∀ q : ExteriorPrime A,
      primeExponent q (amplifiedExterior Ih p) ≠ 0 → q ∈ P := by
    intro q hq
    by_cases hqp : q = p
    · simpa only [hqp] using hp
    · apply hSupportH q
      simpa only [primeExponent_amplifiedExterior, if_neg hqp, add_zero] using hq
  have hfirst := whole_coefficient_full_prime_power_crt_norm C Is Ia Ih s a h hs ha hh
    hsAllowed haAllowed P hSupportS hSupportA hSupportH 1
  have hsecond := whole_coefficient_full_prime_power_crt_norm C Is Ia (amplifiedExterior Ih p)
    s a (h * generator C p ^ 6) hs ha (amplifiedExterior_generates C Ih p h hh)
    hsAllowed haAllowed P hSupportS hSupportA hSupportH' 1
  simp only [one_mul] at hfirst hsecond
  unfold actualFiniteColumn
  rw [hfirst, hsecond]
  exact actualCRTColumn_difference_factor C P p hp
    (fun q => primeExponent q Ia) (fun q => primeExponent q Is)
    (fun q => primeExponent q Ih) (fun q => primeExponent q (amplifiedExterior Ih p))
    (fun q => localUnitPart C q Is s hs) (fun q => localUnitPart C q Ia a ha)
    (fun q => localUnitPart C q Ih h hh)
    (fun q => localUnitPart C q (amplifiedExterior Ih p) (h * generator C p ^ 6)
      (amplifiedExterior_generates C Ih p h hh))
    (fun q => localUnitPart C q (primeIdeal p) (generator C p) (generator_generates C p))
    hk hJ (by simp [primeExponent_amplifiedExterior, hJ])
    (by intro q _ hqp; simp [primeExponent_amplifiedExterior, hqp])
    (fun q _ => localUnitPart_amplifiedExterior C Ih p q h hh)

/-- The original coefficient remains whole. Only the genuinely common
complex local difference is pulled outside the specified valuation sum. -/
theorem whole_actual_valuation_error_factor {ι : Type*}
    (C : A.GeneralArithmeticContext σ η hS)
    (columns : Finset ι) (c : ι → ℂ)
    (Is Ia : ι → A.Exterior) (s a : ι → A.R)
    (hs : ∀ i, A.Generates (Is i) (s i)) (ha : ∀ i, A.Generates (Ia i) (a i))
    (hsAllowed : ∀ i ∈ columns, A.IsAllowed C.correction.B
      (Units.mk0 (s i : F) (by exact_mod_cast (hs i).1)))
    (haAllowed : ∀ i ∈ columns, A.IsAllowed C.correction.B
      (Units.mk0 (a i : F) (by exact_mod_cast (ha i).1)))
    (Ih : A.Exterior) (h : A.R) (hh : A.Generates Ih h)
    (P : Finset (ExteriorPrime A)) (p : ExteriorPrime A) (hp : p ∈ P)
    (hSupportS : ∀ i ∈ columns, ∀ q : ExteriorPrime A, primeExponent q (Is i) ≠ 0 → q ∈ P)
    (hSupportA : ∀ i ∈ columns, ∀ q : ExteriorPrime A, primeExponent q (Ia i) ≠ 0 → q ∈ P)
    (hSupportH : ∀ q : ExteriorPrime A, primeExponent q Ih ≠ 0 → q ∈ P)
    (hk : ∀ i ∈ columns, primeExponent p (Is i) = 0) (hJ : primeExponent p Ih = 0)
    (j : ℕ) :
    valuationError columns c
      (fun i z => actualFiniteColumn C (Is i) (Ia i) (s i) (a i) (hs i) (ha i) z)
      (fun i => primeExponent p (Ia i)) j h (h * generator C p ^ 6) =
      (centralPrimePower C p j 0 - centralPrimePower C p j 6) *
        (∑ i ∈ columns, if primeExponent p (Ia i) = j then
          c i * actualAmplifierResidualColumn C (Is i) (Ia i) Ih (s i) (a i) h
            (hs i) (ha i) hh P p else 0) := by
  unfold valuationError
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hj : primeExponent p (Ia i) = j
  · simp only [if_pos hj]
    rw [actualFiniteColumn_difference_factor C (Is i) (Ia i) Ih (s i) (a i) h
      (hs i) (ha i) hh (hsAllowed i hi) (haAllowed i hi) P p hp
      (hSupportS i hi) (hSupportA i hi) hSupportH (hk i hi) hJ, hj]
    ring
  · simp only [if_neg hj, mul_zero]

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actualFiniteColumn_difference_factor
#print axioms HeckeSkeleton.Moments.EngineStep.whole_actual_valuation_error_factor
