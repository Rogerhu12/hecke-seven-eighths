import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PrimePool
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualPool

/-!
# The PIT pool on the actual exterior-prime labels

The prime ideal theorem supplies a single pool after excluding the fixed
set `A.Sf` together with any additional fixed bad primes.  Relabelling its
ideals as `ExteriorPrime A` preserves the carrier and cardinality exactly.
The resulting witness supplies both the uniform row-deletion bound and the
one-pool inequality on the original finite coefficients.
-/

noncomputable section
open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

namespace HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree LocalFiniteSums

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- A genuine prime ideal avoiding the fixed inverted primes has the
required exterior-prime label.  Its coprimality is proved from that
avoidance, rather than supplied as an unrelated exterior condition. -/
def exteriorPrimeOfIdeal (A : SArithmeticData F) (p : Ideal (𝓞 F))
    (hp : Prime p) (hbad : ∀ v ∈ A.Sf, p ≠ v.asIdeal) : ExteriorPrime A := by
  refine ⟨HeightOneSpectrum.ofPrime hp, ?_⟩
  change p ⊔ (∏ v ∈ A.Sf, v.asIdeal) = ⊤
  apply Ideal.sup_prod_eq_top
  intro v hv
  exact ((HeightOneSpectrum.ofPrime hp).isCoprime_of_ne v
    (fun he => hbad v hv (congrArg HeightOneSpectrum.asIdeal he))).sup_eq

/-- The same ideal carrier, with its actual exterior-prime labels. -/
def primePoolExteriorLift (A : SArithmeticData F) (pool : Finset (Ideal (𝓞 F)))
    (hprime : ∀ p ∈ pool, Prime p)
    (hbad : ∀ p ∈ pool, ∀ v ∈ A.Sf, p ≠ v.asIdeal) : Finset (ExteriorPrime A) :=
  pool.attach.image (fun p => exteriorPrimeOfIdeal A p.val
    (hprime p.val p.property) (hbad p.val p.property))

theorem mem_primePoolExteriorLift (A : SArithmeticData F)
    (pool : Finset (Ideal (𝓞 F))) (hprime : ∀ p ∈ pool, Prime p)
    (hbad : ∀ p ∈ pool, ∀ v ∈ A.Sf, p ≠ v.asIdeal) (p : ExteriorPrime A) :
    p ∈ primePoolExteriorLift A pool hprime hbad ↔ p.val.asIdeal ∈ pool := by
  unfold primePoolExteriorLift
  constructor
  · intro hp
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hp
    have he : q.val = p.val.asIdeal :=
      congrArg (fun v : ExteriorPrime A => v.val.asIdeal) hqp
    exact he ▸ q.property
  · intro hp
    refine Finset.mem_image.mpr ⟨⟨p.val.asIdeal, hp⟩, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    exact HeightOneSpectrum.asIdeal_injective rfl

/-- Relabelling creates no multiplicity and loses no prime. -/
theorem card_primePoolExteriorLift (A : SArithmeticData F)
    (pool : Finset (Ideal (𝓞 F))) (hprime : ∀ p ∈ pool, Prime p)
    (hbad : ∀ p ∈ pool, ∀ v ∈ A.Sf, p ≠ v.asIdeal) :
    (primePoolExteriorLift A pool hprime hbad).card = pool.card := by
  unfold primePoolExteriorLift
  rw [Finset.card_image_of_injective _ (by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun v : ExteriorPrime A => v.val.asIdeal) hpq)]
  exact Finset.card_attach _

theorem image_primePoolExteriorLift (A : SArithmeticData F)
    (pool : Finset (Ideal (𝓞 F))) (hprime : ∀ p ∈ pool, Prime p)
    (hbad : ∀ p ∈ pool, ∀ v ∈ A.Sf, p ≠ v.asIdeal) :
    (primePoolExteriorLift A pool hprime hbad).image (fun p => p.val.asIdeal) = pool := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (mem_primePoolExteriorLift A pool hprime hbad q).mp hq
  · intro hp
    let q := exteriorPrimeOfIdeal A p (hprime p hp) (hbad p hp)
    refine Finset.mem_image.mpr ⟨q, ?_, rfl⟩
    exact (mem_primePoolExteriorLift A pool hprime hbad q).mpr hp

/-- A pool obtained at the specified power scale.  Here `ell` is the
upper norm exponent; the lower norm exponent is `ell / 2`. -/
structure PowerScaleExteriorPool (A : SArithmeticData F)
    (bad : Finset (HeightOneSpectrum (𝓞 F))) (Z ell eps : ℝ) where
  primes : Finset (ExteriorPrime A)
  base_gt_one : 1 < Z
  exponent_pos : 0 < ell
  size_lower : Z ^ (ell - eps) ≤ (primes.card : ℝ)
  norm_lower : ∀ p ∈ primes, Z ^ (ell / 2) ≤ (Ideal.absNorm p.val.asIdeal : ℝ)
  norm_upper : ∀ p ∈ primes, (Ideal.absNorm p.val.asIdeal : ℝ) ≤ Z ^ ell
  avoids : ∀ p ∈ primes, ∀ v ∈ bad, p.val.asIdeal ≠ v.asIdeal

/-- Actual PIT pools with actual exterior-prime labels, excluding `A.Sf`
automatically.  The witness is chosen once, independently of every later
row, frozen ideal, column and correction valuation. -/
theorem exists_power_scale_exterior_pool (A : SArithmeticData F)
    (bad : Finset (HeightOneSpectrum (𝓞 F))) (ell eps : ℝ)
    (hell : 0 < ell) (heps : 0 < eps) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      Nonempty (PowerScaleExteriorPool A bad Z ell eps) := by
  obtain ⟨Z₀, hZ₀, hpools⟩ :=
    exists_power_scale_prime_ideal_pool F (bad ∪ A.Sf) ell eps hell heps
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZ
  obtain ⟨pool, hcard, hnorm, hbad⟩ := hpools Z hZ
  let hprime : ∀ p ∈ pool, Prime p := fun p hp => (hnorm p hp).1
  let hSf : ∀ p ∈ pool, ∀ v ∈ A.Sf, p ≠ v.asIdeal :=
    fun p hp v hv => hbad p hp v (Finset.mem_union_right bad hv)
  let lifted := primePoolExteriorLift A pool hprime hSf
  refine ⟨{
    primes := lifted
    base_gt_one := hZ₀.trans_le hZ
    exponent_pos := hell
    size_lower := ?_
    norm_lower := ?_
    norm_upper := ?_
    avoids := ?_ }⟩
  · change Z ^ (ell - eps) ≤ ((primePoolExteriorLift A pool hprime hSf).card : ℝ)
    rw [card_primePoolExteriorLift]
    exact hcard
  · intro p hp
    exact (hnorm p.val.asIdeal ((mem_primePoolExteriorLift A pool hprime hSf p).mp hp)).2.1
  · intro p hp
    exact (hnorm p.val.asIdeal ((mem_primePoolExteriorLift A pool hprime hSf p).mp hp)).2.2
  · intro p hp v hv
    exact hbad p.val.asIdeal
      ((mem_primePoolExteriorLift A pool hprime hSf p).mp hp) v
      (Finset.mem_union_left A.Sf hv)

namespace PowerScaleExteriorPool

variable {bad : Finset (HeightOneSpectrum (𝓞 F))} {Z ell eps : ℝ}

/-- The same pool loses only the two explicit norm-controlled deletion
terms, with no choice of a different pool for a row or an error term. -/
def rowDensity (P : PowerScaleExteriorPool A bad Z ell eps) (M B : ℝ) : ℝ :=
  Z ^ (ell - eps) - M / (ell / 2) - B / (ell / 2)

theorem eligible_count (P : PowerScaleExteriorPool A bad Z ell eps)
    (frozen : Ideal (𝓞 F)) (I : A.Exterior) (hfrozen : frozen ≠ 0) (B M : ℝ)
    (hfrozenNorm : (Ideal.absNorm frozen : ℝ) ≤ Z ^ B)
    (hrowNorm : (Ideal.absNorm I.val : ℝ) ≤ Z ^ M) :
    P.rowDensity M B ≤
      ((P.primes.filter (actualPrimeEligible frozen I)).card : ℝ) := by
  apply actual_prime_pool_eligible_count P.primes frozen I hfrozen Z (ell / 2) B M
    (P.rowDensity M B) P.base_gt_one (div_pos P.exponent_pos (by norm_num))
    P.norm_lower hfrozenNorm hrowNorm
  have hcount := P.size_lower
  dsimp only [rowDensity]
  linarith

/-- The PIT witness feeds the one-pool amplifier on the original finite
columns.  The only positivity condition on the density concerns its
displayed real expression; there is no assumed eligible-pool cardinality
or assumed frequency-fiber count. -/
theorem finite_energy {ι : Type*} (P : PowerScaleExteriorPool A bad Z ell eps)
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
    (hpool : P.primes ⊆ primes)
    (frozen : Ideal (𝓞 F)) (hfrozen : frozen ≠ 0)
    (hFirstModulus : ∀ i ∈ columns, (Is i).val ∣ frozen)
    (M B : ℝ)
    (hhu : ∀ h ∈ rows, (Ideal.absNorm (rowIdeal h).val : ℝ) ≤ Z ^ M)
    (hfrozenNorm : (Ideal.absNorm frozen : ℝ) ≤ Z ^ B)
    (hdensity : 0 < P.rowDensity M B) :
    let G := fun i z => actualFiniteColumn C (Is i) (Ia i) (s i) (a i) (hs i) (ha i) z
    let ν := fun p i => MaskedQuotientCRT.primeExponent p (Ia i)
    let allow := fun h p => actualPrimeEligible frozen (rowIdeal h) p
    let eligible := eligiblePairs rows P.primes allow
    (∑ h ∈ rows, ‖wholePolynomial columns c G h‖ ^ 2) ≤ (4 / P.rowDensity M B) *
      (((M + 6 * ell) / (ell / 2)) * ∑ y ∈ eligible.image (actualFrequencyAmplify C),
          ‖wholePolynomial columns c G y‖ ^ 2 +
       ∑ x ∈ eligible,
         (‖valuationError columns c G (ν x.2) 1 x.1 (actualFrequencyAmplify C x)‖ ^ 2 +
          ‖valuationError columns c G (ν x.2) 6 x.1 (actualFrequencyAmplify C x)‖ ^ 2 +
          ‖valuationError columns c G (ν x.2) 7 x.1 (actualFrequencyAmplify C x)‖ ^ 2)) := by
  apply actual_finite_pool_energy_from_norms C columns c Is Ia s a hs ha
    hsAllowed haAllowed primes hSupportS hSupportA rows rowIdeal hrows hSupportH
    P.primes hpool frozen hfrozen hFirstModulus Z (ell / 2) M ell B (P.rowDensity M B)
    P.base_gt_one (div_pos P.exponent_pos (by norm_num)) hdensity P.norm_lower P.norm_upper
    hhu hfrozenNorm
  have hcount := P.size_lower
  dsimp only [rowDensity]
  linarith

end PowerScaleExteriorPool

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.exists_power_scale_exterior_pool
#print axioms HeckeSkeleton.Moments.EngineStep.PowerScaleExteriorPool.finite_energy
