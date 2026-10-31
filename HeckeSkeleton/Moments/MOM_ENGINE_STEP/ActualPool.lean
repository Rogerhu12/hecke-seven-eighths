import HeckeSkeleton.Moments.MOM_ENGINE_STEP.LocalCRT
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.Pool

/-!
# One pool on the actual normalized local CRT columns

The Gauss column here is the product of the actual `CompatiblePrimeRawLocal.R`
factors, centrally normalized at the complete modulus.  `LocalCRT` proves
its equality with the original finite coefficient divided by the complete
ideal norm.  The hypotheses of the transport theorem describe the change
of local valuation and unit coordinates under one sixth-power insertion.
The support of the error at 1/6/7 is derived from the actual local table.

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

end HeckeSkeleton.Moments.EngineStep
