import HeckeSkeleton.Moments.MOM_ENGINE_STEP.LocalCRT
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.Pool
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.IdealPool

/-!
# One pool on the original normalized finite columns

`actual_finite_polynomial_amplification` and `actual_finite_pool_energy`
use the original `MaskedQuotientCRT.coefficient`, divided by the complete
ideal norm, at frequencies in the actual ring of S-integers.  Insertion
is literal multiplication by `generator C p ^ 6`.  Its valuation and
local-unit relations, and hence the error support at 1/6/7, are derived
from complete finite arithmetic.  The local-coordinate versions are
also recorded for use inside the CRT calculation.

The coefficient `c` is retained as a whole and is independent of the row.
This is the input after freezing and analytic separation of the original
row-dependent profiles; this module does not assert that separation.
-/

noncomputable section
open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

namespace HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree LocalFiniteSums CompatiblePrimeRawLocal

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- The complete centrally normalized CRT column at its genuine local data. -/
def actualCRTColumn (C : A.GeneralArithmeticContext σ η hS)
    (primes : Finset (ExteriorPrime A)) (t k J : ExteriorPrime A → ℕ)
    (s a h : ∀ q : ExteriorPrime A, (LocalIntegers q)ˣ) : ℂ :=
  ∏ q ∈ primes, centralRawLocalFactor C q (t q) (k q) (J q) (s q) (a q) (h q)

theorem actualCRTColumn_unchanged (C : A.GeneralArithmeticContext σ η hS)
    (primes : Finset (ExteriorPrime A)) (p : ExteriorPrime A) (hp : p ∈ primes)
    (t k J J' : ExteriorPrime A → ℕ)
    (s a h h' u : ∀ q : ExteriorPrime A, (LocalIntegers q)ˣ)
    (hk : k p = 0) (hJ : J p = 0) (hJ' : J' p = 6)
    (hother : ∀ q ∈ primes, q ≠ p → J' q = J q)
    (hunit : ∀ q ∈ primes, h' q = h q * u q ^ 6)
    (hne1 : t p ≠ 1) (hne6 : t p ≠ 6) (hne7 : t p ≠ 7) :
    actualCRTColumn C primes t k J' s a h' = actualCRTColumn C primes t k J s a h := by
  have he : actualCRTColumn C primes t k J' s a h' =
      ∏ q ∈ primes, centralRawLocalFactor C q (t q) (k q) (J' q)
        (s q) (a q) (h q * u q ^ 6) := by
    apply Finset.prod_congr rfl
    intro q hq
    rw [hunit q hq]
  rw [he]
  symm
  by_contra hne
  rcases rawCRT_product_difference_support C primes p hp t k J J' s a h u
      hk hJ hJ' hother hne with h | h | h
  · exact hne1 h
  · exact hne6 h
  · exact hne7 h

/-- One complete actual CRT polynomial obeys the three-error identity. -/
theorem actualCRT_polynomial_amplification {ι H : Type*}
    (C : A.GeneralArithmeticContext σ η hS)
    (columns : Finset ι) (c : ι → ℂ) (primes : Finset (ExteriorPrime A))
    (t k : ι → ExteriorPrime A → ℕ)
    (s a : ∀ i : ι, ∀ q : ExteriorPrime A, (LocalIntegers q)ˣ)
    (J : H → ExteriorPrime A → ℕ)
    (unitPart : ∀ h : H, ∀ q : ExteriorPrime A, (LocalIntegers q)ˣ)
    (h hAmp : H) (p : ExteriorPrime A) (hp : p ∈ primes)
    (u : ∀ q : ExteriorPrime A, (LocalIntegers q)ˣ)
    (hk : ∀ i ∈ columns, k i p = 0) (hJ : J h p = 0) (hJ' : J hAmp p = 6)
    (hother : ∀ q ∈ primes, q ≠ p → J hAmp q = J h q)
    (hunit : ∀ q ∈ primes, unitPart hAmp q = unitPart h q * u q ^ 6) :
    let G := fun i h => actualCRTColumn C primes (t i) (k i) (J h) (s i) (a i) (unitPart h)
    wholePolynomial columns c G h = wholePolynomial columns c G hAmp +
      valuationError columns c G (fun i => t i p) 1 h hAmp +
      valuationError columns c G (fun i => t i p) 6 h hAmp +
      valuationError columns c G (fun i => t i p) 7 h hAmp := by
  dsimp only
  apply whole_polynomial_amplification
  intro i hi h1 h6 h7
  exact actualCRTColumn_unchanged C primes p hp (t i) (k i) (J h) (J hAmp)
    (s i) (a i) (unitPart h) (unitPart hAmp) u (hk i hi) hJ hJ' hother hunit h1 h6 h7

/-- The one-pool energy inequality with the three-error column condition
discharged from actual finite arithmetic.  Only pool size, output-fiber
count and the literal local-coordinate transport remain as inputs. -/
theorem actualCRT_pool_energy {ι H : Type*} [DecidableEq H]
    (C : A.GeneralArithmeticContext σ η hS)
    (columns : Finset ι) (c : ι → ℂ) (primes : Finset (ExteriorPrime A))
    (t k : ι → ExteriorPrime A → ℕ)
    (s a : ∀ i : ι, ∀ q : ExteriorPrime A, (LocalIntegers q)ˣ)
    (J : H → ExteriorPrime A → ℕ)
    (unitPart : ∀ h : H, ∀ q : ExteriorPrime A, (LocalIntegers q)ˣ)
    (rows : Finset H) (pool : Finset (ExteriorPrime A))
    (allow : H → ExteriorPrime A → Prop) (amplify : H × ExteriorPrime A → H)
    (transport : ∀ h : H, ∀ p q : ExteriorPrime A, (LocalIntegers q)ˣ)
    (density multiplicity : ℝ) (hdensity : 0 < density)
    (hsize : ∀ h ∈ rows, density ≤ (pool.filter (allow h)).card)
    (hpool : pool ⊆ primes)
    (hk : ∀ h ∈ rows, ∀ p ∈ pool, allow h p → ∀ i ∈ columns, k i p = 0)
    (hJ : ∀ h ∈ rows, ∀ p ∈ pool, allow h p → J h p = 0)
    (hJ' : ∀ h ∈ rows, ∀ p ∈ pool, allow h p → J (amplify (h, p)) p = 6)
    (hother : ∀ h ∈ rows, ∀ p ∈ pool, allow h p →
      ∀ q ∈ primes, q ≠ p → J (amplify (h, p)) q = J h q)
    (hunit : ∀ h ∈ rows, ∀ p ∈ pool, allow h p →
      ∀ q ∈ primes, unitPart (amplify (h, p)) q = unitPart h q * transport h p q ^ 6)
    (hfiber : ∀ y ∈ (eligiblePairs rows pool allow).image amplify,
      (((eligiblePairs rows pool allow).filter (fun x => amplify x = y)).card : ℝ) ≤ multiplicity) :
    let G := fun i h => actualCRTColumn C primes (t i) (k i) (J h) (s i) (a i) (unitPart h)
    (∑ h ∈ rows, ‖wholePolynomial columns c G h‖ ^ 2) ≤ (4 / density) *
      (multiplicity * ∑ y ∈ (eligiblePairs rows pool allow).image amplify,
          ‖wholePolynomial columns c G y‖ ^ 2 +
       ∑ x ∈ eligiblePairs rows pool allow,
         (‖valuationError columns c G (fun i => t i x.2) 1 x.1 (amplify x)‖ ^ 2 +
          ‖valuationError columns c G (fun i => t i x.2) 6 x.1 (amplify x)‖ ^ 2 +
          ‖valuationError columns c G (fun i => t i x.2) 7 x.1 (amplify x)‖ ^ 2)) := by
  dsimp only
  apply whole_polynomial_pool_energy columns c _ (fun p i => t i p)
    rows pool allow amplify density multiplicity hdensity hsize
  · intro h hh p hp hallow i hi h1 h6 h7
    exact actualCRTColumn_unchanged C primes p (hpool hp) (t i) (k i)
      (J h) (J (amplify (h, p))) (s i) (a i) (unitPart h) (unitPart (amplify (h, p)))
      (transport h p) (hk h hh p hp hallow i hi) (hJ h hh p hp hallow)
      (hJ' h hh p hp hallow) (hother h hh p hp hallow) (hunit h hh p hp hallow) h1 h6 h7
  · exact hfiber

/-- The original finite coefficient with its complete central denominator. -/
def actualFiniteColumn (C : A.GeneralArithmeticContext σ η hS)
    (Is Ia : A.Exterior) (s a : A.R)
    (hs : A.Generates Is s) (ha : A.Generates Ia a) (h : A.R) : ℂ :=
  MaskedQuotientCRT.coefficient C Is Ia s a h hs ha / (A.exteriorNorm Ia : ℂ)

/-- Outside the three correction depths the actual finite column is
unchanged by inserting the chosen prime's sixth power. -/
theorem actualFiniteColumn_unchanged (C : A.GeneralArithmeticContext σ η hS)
    (Is Ia Ih : A.Exterior) (s a h : A.R)
    (hs : A.Generates Is s) (ha : A.Generates Ia a) (hh : A.Generates Ih h)
    (hsAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (s : F) (by exact_mod_cast hs.1)))
    (haAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (a : F) (by exact_mod_cast ha.1)))
    (primes : Finset (ExteriorPrime A)) (p : ExteriorPrime A) (hp : p ∈ primes)
    (hSupportS : ∀ q : ExteriorPrime A, MaskedQuotientCRT.primeExponent q Is ≠ 0 → q ∈ primes)
    (hSupportA : ∀ q : ExteriorPrime A, MaskedQuotientCRT.primeExponent q Ia ≠ 0 → q ∈ primes)
    (hSupportH : ∀ q : ExteriorPrime A, MaskedQuotientCRT.primeExponent q Ih ≠ 0 → q ∈ primes)
    (hk : MaskedQuotientCRT.primeExponent p Is = 0)
    (hJ : MaskedQuotientCRT.primeExponent p Ih = 0)
    (h1 : MaskedQuotientCRT.primeExponent p Ia ≠ 1)
    (h6 : MaskedQuotientCRT.primeExponent p Ia ≠ 6)
    (h7 : MaskedQuotientCRT.primeExponent p Ia ≠ 7) :
    actualFiniteColumn C Is Ia s a hs ha (h * generator C p ^ 6) =
      actualFiniteColumn C Is Ia s a hs ha h := by
  symm
  by_contra hne
  have hne' : (1 : ℂ) * MaskedQuotientCRT.coefficient C Is Ia s a h hs ha /
      (A.exteriorNorm Ia : ℂ) ≠
      (1 : ℂ) * MaskedQuotientCRT.coefficient C Is Ia s a (h * generator C p ^ 6) hs ha /
        (A.exteriorNorm Ia : ℂ) := by
    simpa only [one_mul, actualFiniteColumn] using hne
  rcases actual_frequency_insertion_support C Is Ia Ih s a h hs ha hh
      hsAllowed haAllowed primes p hp hSupportS hSupportA hSupportH hk hJ 1 hne'
      with hn | hn | hn
  · exact h1 hn
  · exact h6 hn
  · exact h7 hn

/-- The whole finite polynomial and all three of its error polynomials
are built from the original finite columns at actual ring frequencies.
No local-coordinate transport is an input to this identity. -/
theorem actual_finite_polynomial_amplification {ι : Type*}
    (C : A.GeneralArithmeticContext σ η hS)
    (columns : Finset ι) (c : ι → ℂ)
    (Is Ia : ι → A.Exterior) (s a : ι → A.R)
    (hs : ∀ i, A.Generates (Is i) (s i)) (ha : ∀ i, A.Generates (Ia i) (a i))
    (hsAllowed : ∀ i ∈ columns, A.IsAllowed C.correction.B
      (Units.mk0 (s i : F) (by exact_mod_cast (hs i).1)))
    (haAllowed : ∀ i ∈ columns, A.IsAllowed C.correction.B
      (Units.mk0 (a i : F) (by exact_mod_cast (ha i).1)))
    (primes : Finset (ExteriorPrime A))
    (hSupportS : ∀ i ∈ columns, ∀ q : ExteriorPrime A,
      MaskedQuotientCRT.primeExponent q (Is i) ≠ 0 → q ∈ primes)
    (hSupportA : ∀ i ∈ columns, ∀ q : ExteriorPrime A,
      MaskedQuotientCRT.primeExponent q (Ia i) ≠ 0 → q ∈ primes)
    (Ih : A.Exterior) (h : A.R) (hh : A.Generates Ih h)
    (hSupportH : ∀ q : ExteriorPrime A, MaskedQuotientCRT.primeExponent q Ih ≠ 0 → q ∈ primes)
    (p : ExteriorPrime A) (hp : p ∈ primes)
    (hk : ∀ i ∈ columns, MaskedQuotientCRT.primeExponent p (Is i) = 0)
    (hJ : MaskedQuotientCRT.primeExponent p Ih = 0) :
    let G := fun i z => actualFiniteColumn C (Is i) (Ia i) (s i) (a i) (hs i) (ha i) z
    let ν := fun i => MaskedQuotientCRT.primeExponent p (Ia i)
    let hAmp := h * generator C p ^ 6
    wholePolynomial columns c G h = wholePolynomial columns c G hAmp +
      valuationError columns c G ν 1 h hAmp + valuationError columns c G ν 6 h hAmp +
      valuationError columns c G ν 7 h hAmp := by
  dsimp only
  apply whole_polynomial_amplification
  intro i hi h1 h6 h7
  exact actualFiniteColumn_unchanged C (Is i) (Ia i) Ih (s i) (a i) h
    (hs i) (ha i) hh (hsAllowed i hi) (haAllowed i hi) primes p hp
    (hSupportS i hi) (hSupportA i hi) hSupportH (hk i hi) hJ h1 h6 h7

/-- Literal multiplication on S-integer frequencies, with no choice of
a new canonical generator inserted into the definition. -/
def actualFrequencyAmplify (C : A.GeneralArithmeticContext σ η hS)
    (x : A.R × ExteriorPrime A) : A.R := x.1 * generator C x.2 ^ 6

/-- One averaging pool for the original finite columns.  The density and
fiber count are stated on the actual ring frequencies and prime labels;
the whole coefficient and all three correction polynomials are unchanged.
In particular this statement makes no equality assertion about separately
chosen generators of the amplified ideal. -/
theorem actual_finite_pool_energy {ι : Type*}
    (C : A.GeneralArithmeticContext σ η hS)
    (columns : Finset ι) (c : ι → ℂ)
    (Is Ia : ι → A.Exterior) (s a : ι → A.R)
    (hs : ∀ i, A.Generates (Is i) (s i)) (ha : ∀ i, A.Generates (Ia i) (a i))
    (hsAllowed : ∀ i ∈ columns, A.IsAllowed C.correction.B
      (Units.mk0 (s i : F) (by exact_mod_cast (hs i).1)))
    (haAllowed : ∀ i ∈ columns, A.IsAllowed C.correction.B
      (Units.mk0 (a i : F) (by exact_mod_cast (ha i).1)))
    (primes : Finset (ExteriorPrime A))
    (hSupportS : ∀ i ∈ columns, ∀ q : ExteriorPrime A,
      MaskedQuotientCRT.primeExponent q (Is i) ≠ 0 → q ∈ primes)
    (hSupportA : ∀ i ∈ columns, ∀ q : ExteriorPrime A,
      MaskedQuotientCRT.primeExponent q (Ia i) ≠ 0 → q ∈ primes)
    (rows : Finset A.R) (frequencyIdeal : A.R → A.Exterior)
    (hrows : ∀ h ∈ rows, A.Generates (frequencyIdeal h) h)
    (hSupportH : ∀ h ∈ rows, ∀ q : ExteriorPrime A,
      MaskedQuotientCRT.primeExponent q (frequencyIdeal h) ≠ 0 → q ∈ primes)
    (pool : Finset (ExteriorPrime A)) (hpool : pool ⊆ primes)
    (allow : A.R → ExteriorPrime A → Prop)
    (hk : ∀ h ∈ rows, ∀ p ∈ pool, allow h p → ∀ i ∈ columns,
      MaskedQuotientCRT.primeExponent p (Is i) = 0)
    (hJ : ∀ h ∈ rows, ∀ p ∈ pool, allow h p →
      MaskedQuotientCRT.primeExponent p (frequencyIdeal h) = 0)
    (density multiplicity : ℝ) (hdensity : 0 < density)
    (hsize : ∀ h ∈ rows, density ≤ (pool.filter (allow h)).card)
    (hfiber : ∀ y ∈ (eligiblePairs rows pool allow).image (actualFrequencyAmplify C),
      (((eligiblePairs rows pool allow).filter
        (fun x => actualFrequencyAmplify C x = y)).card : ℝ) ≤ multiplicity) :
    let G := fun i z => actualFiniteColumn C (Is i) (Ia i) (s i) (a i) (hs i) (ha i) z
    let ν := fun p i => MaskedQuotientCRT.primeExponent p (Ia i)
    let eligible := eligiblePairs rows pool allow
    (∑ h ∈ rows, ‖wholePolynomial columns c G h‖ ^ 2) ≤ (4 / density) *
      (multiplicity * ∑ y ∈ eligible.image (actualFrequencyAmplify C),
          ‖wholePolynomial columns c G y‖ ^ 2 +
       ∑ x ∈ eligible,
         (‖valuationError columns c G (ν x.2) 1 x.1 (actualFrequencyAmplify C x)‖ ^ 2 +
          ‖valuationError columns c G (ν x.2) 6 x.1 (actualFrequencyAmplify C x)‖ ^ 2 +
          ‖valuationError columns c G (ν x.2) 7 x.1 (actualFrequencyAmplify C x)‖ ^ 2)) := by
  dsimp only
  apply whole_polynomial_pool_energy columns c _
    (fun p i => MaskedQuotientCRT.primeExponent p (Ia i))
    rows pool allow (actualFrequencyAmplify C) density multiplicity hdensity hsize
  · intro h hh p hp hallow i hi h1 h6 h7
    exact actualFiniteColumn_unchanged C (Is i) (Ia i) (frequencyIdeal h) (s i) (a i) h
      (hs i) (ha i) (hrows h hh) (hsAllowed i hi) (haAllowed i hi) primes p (hpool hp)
      (hSupportS i hi) (hSupportA i hi) (hSupportH h hh)
      (hk h hh p hp hallow i hi) (hJ h hh p hp hallow) h1 h6 h7
  · exact hfiber

/-- Two exterior ideals generated by the same actual element are equal. -/
theorem generatedIdeal_unique {I J : A.Exterior} {x : A.R}
    (hI : A.Generates I x) (hJ : A.Generates J x) : I = J := by
  apply A.exteriorIdealEquiv.injective
  apply Subtype.ext
  rw [A.exteriorIdealEquiv_apply, A.exteriorIdealEquiv_apply, ← hI.2, ← hJ.2]

/-- A fiber of literal frequency insertion injects into the auxiliary
prime ideals dividing its actual output ideal.  Cancellation takes place
in the S-integer ring, so no canonical-generator equality is needed. -/
theorem actualFrequencyAmplify_fiber_count (C : A.GeneralArithmeticContext σ η hS)
    (pairs : Finset (A.R × ExteriorPrime A)) (rowIdeal : A.R → A.Exterior)
    (hrows : ∀ x ∈ pairs, A.Generates (rowIdeal x.1) x.1)
    (I : A.Exterior) (y : A.R) (hy : A.Generates I y)
    (houtput : ∀ x ∈ pairs, actualFrequencyAmplify C x = y)
    (Z ell B : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ x ∈ pairs, Z ^ ell ≤ (Ideal.absNorm x.2.val.asIdeal : ℝ))
    (hupper : (Ideal.absNorm I.val : ℝ) ≤ Z ^ B) :
    (pairs.card : ℝ) ≤ B / ell := by
  refine indexed_large_prime_ideal_count pairs (fun x => x.2.val.asIdeal) ?_
    (fun x _ => x.2.val.prime) I.val I.property.1 ?_ Z ell B hZ hell hlower hupper
  · intro x hx x' hx' heq
    have hp : x.2 = x'.2 :=
      Subtype.ext (HeightOneSpectrum.asIdeal_injective heq)
    have hfirst : x.1 = x'.1 := by
      apply mul_right_cancel₀ (pow_ne_zero 6 (generator_generates C x.2).1)
      change actualFrequencyAmplify C x = x'.1 * generator C x.2 ^ 6
      rw [houtput x hx, hp]
      exact (houtput x' hx').symm
    exact Prod.ext hfirst hp
  · intro x hx
    have hg := amplifiedExterior_generates C (rowIdeal x.1) x.2 x.1 (hrows x hx)
    change A.Generates (amplifiedExterior (rowIdeal x.1) x.2)
      (actualFrequencyAmplify C x) at hg
    rw [houtput x hx] at hg
    have heq := generatedIdeal_unique hg hy
    rw [← congrArg Subtype.val heq, amplifiedExterior_val]
    exact (dvd_pow_self x.2.val.asIdeal (by decide : 6 ≠ 0)).trans (dvd_mul_right _ _)

/-- The physical frequency fibers have the same bounded multiplicity as
the ideal fibers: the single sixth-power insertion changes the output
norm exponent from `M` to at most `M + 6L`. -/
theorem actualFrequencyAmplify_output_fibers (C : A.GeneralArithmeticContext σ η hS)
    (rows : Finset A.R) (rowIdeal : A.R → A.Exterior)
    (hrows : ∀ h ∈ rows, A.Generates (rowIdeal h) h)
    (pool : Finset (ExteriorPrime A)) (allow : A.R → ExteriorPrime A → Prop)
    (Z ell M L : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hpl : ∀ p ∈ pool, Z ^ ell ≤ (Ideal.absNorm p.val.asIdeal : ℝ))
    (hpu : ∀ p ∈ pool, (Ideal.absNorm p.val.asIdeal : ℝ) ≤ Z ^ L)
    (hhu : ∀ h ∈ rows, (Ideal.absNorm (rowIdeal h).val : ℝ) ≤ Z ^ M) :
    ∀ y ∈ (eligiblePairs rows pool allow).image (actualFrequencyAmplify C),
      (((eligiblePairs rows pool allow).filter
        (fun x => actualFrequencyAmplify C x = y)).card : ℝ) ≤ (M + 6 * L) / ell := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  have hmem (z : A.R × ExteriorPrime A) (hz : z ∈ eligiblePairs rows pool allow) :
      z.1 ∈ rows ∧ z.2 ∈ pool :=
    Finset.mem_product.mp (Finset.mem_filter.mp hz).1
  refine actualFrequencyAmplify_fiber_count C _ rowIdeal ?_
    (amplifiedExterior (rowIdeal x.1) x.2) (actualFrequencyAmplify C x)
    (amplifiedExterior_generates C (rowIdeal x.1) x.2 x.1 (hrows x.1 (hmem x hx).1))
    ?_ Z ell (M + 6 * L) hZ hell ?_ ?_
  · intro z hz
    exact hrows z.1 (hmem z (Finset.mem_filter.mp hz).1).1
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · intro z hz
    exact hpl z.2 (hmem z (Finset.mem_filter.mp hz).1).2
  · have hn := idealAmplify_norm ((rowIdeal x.1).val, x.2.val.asIdeal) Z M L
      (zero_lt_one.trans hZ) (hhu x.1 (hmem x hx).1) (hpu x.2 (hmem x hx).2)
    simpa only [idealAmplify, amplifiedExterior_val] using hn

/-- One common pool excludes the old frequency ideal and the fixed
frozen ideal.  Every first modulus is required to divide that fixed ideal. -/
def actualPrimeEligible (frozen : Ideal (𝓞 F)) (I : A.Exterior)
    (p : ExteriorPrime A) : Prop :=
  ¬p.val.asIdeal ∣ I.val ∧ ¬p.val.asIdeal ∣ frozen

theorem primeExponent_zero_of_not_dvd (I : A.Exterior) (p : ExteriorPrime A)
    (hp : ¬p.val.asIdeal ∣ I.val) : MaskedQuotientCRT.primeExponent p I = 0 := by
  change (UniqueFactorizationMonoid.normalizedFactors I.val).count p.val.asIdeal = 0
  exact Multiset.count_eq_zero.mpr
    (fun hm => hp (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hm))

/-- The actual prime-label pool loses at most `M/ell + B/ell` labels to
the frequency and all frozen moduli together. -/
theorem actual_prime_pool_eligible_count (pool : Finset (ExteriorPrime A))
    (frozen : Ideal (𝓞 F)) (I : A.Exterior) (hfrozen : frozen ≠ 0)
    (Z ell B M density : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ p ∈ pool, Z ^ ell ≤ (Ideal.absNorm p.val.asIdeal : ℝ))
    (hfrozenNorm : (Ideal.absNorm frozen : ℝ) ≤ Z ^ B)
    (hrowNorm : (Ideal.absNorm I.val : ℝ) ≤ Z ^ M)
    (hpool : density + M / ell + B / ell ≤ (pool.card : ℝ)) :
    density ≤ ((pool.filter (actualPrimeEligible frozen I)).card : ℝ) := by
  let rowBad := pool.filter (fun p => p.val.asIdeal ∣ I.val)
  let frozenBad := pool.filter (fun p => p.val.asIdeal ∣ frozen)
  have hinj : Function.Injective (fun p : ExteriorPrime A => p.val.asIdeal) := by
    intro p q hpq
    exact Subtype.ext (HeightOneSpectrum.asIdeal_injective hpq)
  have hrow : (rowBad.card : ℝ) ≤ M / ell :=
    indexed_large_prime_ideal_count rowBad (fun p => p.val.asIdeal) hinj.injOn
      (fun p _ => p.val.prime) I.val I.property.1
      (fun p hp => (Finset.mem_filter.mp hp).2) Z ell M hZ hell
      (fun p hp => hlower p (Finset.mem_filter.mp hp).1) hrowNorm
  have hfroz : (frozenBad.card : ℝ) ≤ B / ell :=
    indexed_large_prime_ideal_count frozenBad (fun p => p.val.asIdeal) hinj.injOn
      (fun p _ => p.val.prime) frozen hfrozen
      (fun p hp => (Finset.mem_filter.mp hp).2) Z ell B hZ hell
      (fun p hp => hlower p (Finset.mem_filter.mp hp).1) hfrozenNorm
  have he : pool.filter (actualPrimeEligible frozen I) = pool \ (rowBad ∪ frozenBad) := by
    ext p
    simp only [Finset.mem_filter, actualPrimeEligible, Finset.mem_sdiff,
      Finset.mem_union, rowBad, frozenBad]
    tauto
  rw [he]
  exact eligible_count_after_deletions pool rowBad frozenBad (M / ell) (B / ell)
    density hrow hfroz hpool

/-- The complete one-pool inequality on actual finite coefficients, with
both eligible-pool size and physical-frequency multiplicity derived from
ideal norms.  Its arithmetic hypotheses are the original generator data,
complete CRT support, prime-norm windows and one raw pool-size lower bound. -/
theorem actual_finite_pool_energy_from_norms {ι : Type*}
    (C : A.GeneralArithmeticContext σ η hS)
    (columns : Finset ι) (c : ι → ℂ)
    (Is Ia : ι → A.Exterior) (s a : ι → A.R)
    (hs : ∀ i, A.Generates (Is i) (s i)) (ha : ∀ i, A.Generates (Ia i) (a i))
    (hsAllowed : ∀ i ∈ columns, A.IsAllowed C.correction.B
      (Units.mk0 (s i : F) (by exact_mod_cast (hs i).1)))
    (haAllowed : ∀ i ∈ columns, A.IsAllowed C.correction.B
      (Units.mk0 (a i : F) (by exact_mod_cast (ha i).1)))
    (primes : Finset (ExteriorPrime A))
    (hSupportS : ∀ i ∈ columns, ∀ q : ExteriorPrime A,
      MaskedQuotientCRT.primeExponent q (Is i) ≠ 0 → q ∈ primes)
    (hSupportA : ∀ i ∈ columns, ∀ q : ExteriorPrime A,
      MaskedQuotientCRT.primeExponent q (Ia i) ≠ 0 → q ∈ primes)
    (rows : Finset A.R) (rowIdeal : A.R → A.Exterior)
    (hrows : ∀ h ∈ rows, A.Generates (rowIdeal h) h)
    (hSupportH : ∀ h ∈ rows, ∀ q : ExteriorPrime A,
      MaskedQuotientCRT.primeExponent q (rowIdeal h) ≠ 0 → q ∈ primes)
    (pool : Finset (ExteriorPrime A)) (hpool : pool ⊆ primes)
    (frozen : Ideal (𝓞 F)) (hfrozen : frozen ≠ 0)
    (hFirstModulus : ∀ i ∈ columns, (Is i).val ∣ frozen)
    (Z ell M L B density : ℝ) (hZ : 1 < Z) (hell : 0 < ell) (hdensity : 0 < density)
    (hpl : ∀ p ∈ pool, Z ^ ell ≤ (Ideal.absNorm p.val.asIdeal : ℝ))
    (hpu : ∀ p ∈ pool, (Ideal.absNorm p.val.asIdeal : ℝ) ≤ Z ^ L)
    (hhu : ∀ h ∈ rows, (Ideal.absNorm (rowIdeal h).val : ℝ) ≤ Z ^ M)
    (hfrozenNorm : (Ideal.absNorm frozen : ℝ) ≤ Z ^ B)
    (hpoolSize : density + M / ell + B / ell ≤ (pool.card : ℝ)) :
    let G := fun i z => actualFiniteColumn C (Is i) (Ia i) (s i) (a i) (hs i) (ha i) z
    let ν := fun p i => MaskedQuotientCRT.primeExponent p (Ia i)
    let allow := fun h p => actualPrimeEligible frozen (rowIdeal h) p
    let eligible := eligiblePairs rows pool allow
    (∑ h ∈ rows, ‖wholePolynomial columns c G h‖ ^ 2) ≤ (4 / density) *
      (((M + 6 * L) / ell) * ∑ y ∈ eligible.image (actualFrequencyAmplify C),
          ‖wholePolynomial columns c G y‖ ^ 2 +
       ∑ x ∈ eligible,
         (‖valuationError columns c G (ν x.2) 1 x.1 (actualFrequencyAmplify C x)‖ ^ 2 +
          ‖valuationError columns c G (ν x.2) 6 x.1 (actualFrequencyAmplify C x)‖ ^ 2 +
          ‖valuationError columns c G (ν x.2) 7 x.1 (actualFrequencyAmplify C x)‖ ^ 2)) := by
  dsimp only
  refine actual_finite_pool_energy C columns c Is Ia s a hs ha hsAllowed haAllowed
    primes hSupportS hSupportA rows rowIdeal hrows hSupportH pool hpool
    (fun h p => actualPrimeEligible frozen (rowIdeal h) p)
    ?_ ?_ density ((M + 6 * L) / ell) hdensity ?_ ?_
  · intro h hh p hp hallow i hi
    exact primeExponent_zero_of_not_dvd (Is i) p
      (fun hdiv => hallow.2 (hdiv.trans (hFirstModulus i hi)))
  · intro h hh p hp hallow
    exact primeExponent_zero_of_not_dvd (rowIdeal h) p hallow.1
  · intro h hh
    exact actual_prime_pool_eligible_count pool frozen (rowIdeal h) hfrozen
      Z ell B M density hZ hell hpl hfrozenNorm (hhu h hh) hpoolSize
  · exact actualFrequencyAmplify_output_fibers C rows rowIdeal hrows pool
      (fun h p => actualPrimeEligible frozen (rowIdeal h) p) Z ell M L hZ hell hpl hpu hhu

end HeckeSkeleton.Moments.EngineStep
