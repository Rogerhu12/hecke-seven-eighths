import HeckeGeneral.Characters.SIntegerSexticPowerMask
import HeckeGeneral.Analysis.IdealSquarefreeAmplification
import Mathlib.RingTheory.Coprime.Lemmas

/-!
Actual sextic inverse rows in one finite prime envelope.  The test W and
envelope are shared by every row and every scaled polynomial.  There is
no extra moving mask and no extension of a moving row to a Hecke character.
Coverage of an arbitrary test's ideal support, row counting, and MI energy
bounds are separate obligations.
-/

noncomputable section

namespace HeckeGeneral.Analysis.SquarefreeAmplification

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.IdealMobiusMask HeckeGeneral.Characters
open scoped BigOperators Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

theorem prime_dvd_primeProduct_iff
    (p : HeightOneSpectrum (𝓞 K)) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    p.asIdeal ∣ primeProduct T ↔ p ∈ T := by
  unfold primeProduct
  rw [p.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨q, hq, hpq⟩
    have he : q.asIdeal = p.asIdeal :=
      q.isMaximal.eq_of_le p.isPrime.ne_top (Ideal.dvd_iff_le.mp hpq)
    have hqp : q = p := HeightOneSpectrum.ext he
    simpa only [hqp] using hq
  · intro hp
    exact ⟨p, hp, dvd_rfl⟩

theorem primeIdeal_coprime_iff_not_dvd
    (p : HeightOneSpectrum (𝓞 K)) (J : Ideal (𝓞 K)) :
    IsCoprime p.asIdeal J ↔ ¬p.asIdeal ∣ J := by
  constructor
  · intro hc hd
    have ht : (⊤ : Ideal (𝓞 K)) ≤ p.asIdeal := by
      rw [← hc.sup_eq]
      exact sup_le le_rfl (Ideal.dvd_iff_le.mp hd)
    exact p.isPrime.ne_top (top_le_iff.mp ht)
  · intro hd
    apply Ideal.isCoprime_iff_sup_eq.mpr
    by_contra hn
    have he : p.asIdeal = p.asIdeal ⊔ J := p.isMaximal.eq_of_le hn le_sup_left
    apply hd
    apply Ideal.dvd_iff_le.mpr
    rw [he]
    exact le_sup_right

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (E : Finset (HeightOneSpectrum (𝓞 K)))
variable (hES : ∀ p ∈ E, p ∉ S)
variable (hE6 : ∀ p ∈ E, (6 : 𝓞 K) ∉ p.asIdeal)

/-- Literal evaluation at the actual squarefree denominator ideal. -/
def sexticEnvelopeEvaluation (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : T ⊆ E) (u : S.integer K) : ℂ :=
  sIntegerSexticIdealEvaluation K S ζ hζ σ (squarefreeIdeal K T).val
    (nonZeroDivisors.coe_ne_zero (squarefreeIdeal K T))
    (fun p hp => hES p (hT ((prime_dvd_primeProduct_iff K p T).mp hp)))
    (fun p hp => hE6 p (hT ((prime_dvd_primeProduct_iff K p T).mp hp))) u

theorem sexticEnvelopeEvaluation_one
    (T : Finset (HeightOneSpectrum (𝓞 K))) (hT : T ⊆ E) :
    sexticEnvelopeEvaluation K S ζ hζ σ E hES hE6 T hT 1 = 1 := by
  exact sIntegerSexticIdealEvaluation_one K S ζ hζ σ _ _ _ _

theorem sexticEnvelopeEvaluation_sixth_power_mask
    (T : Finset (HeightOneSpectrum (𝓞 K))) (hT : T ⊆ E) (a : S.integer K) :
    sexticEnvelopeEvaluation K S ζ hζ σ E hES hE6 T hT (a ^ 6) =
      if IsCoprime (squarefreeIdeal K T).val (sIntegerModulusContraction K S a)
        then 1 else 0 := by
  exact sIntegerSexticIdealEvaluation_sixth_power_coprime_mask K S ζ hζ σ _ _ _ _ a

/-- The actual normalized inverse row, including zero at bad denominator
primes. The attached powerset supplies admissibility proofs only. -/
def sexticRowPolynomial (η : HeckeCharacter K) (u : S.integer K)
    (D : ℝ) (W : ℝ → ℂ) : ℂ :=
  (Real.sqrt D : ℂ)⁻¹ * ∑ T ∈ E.powerset.attach,
    (UniqueFactorizationMonoid.moebius (squarefreeIdeal K T.val).val : ℂ) *
      heckeIdealCoefficient K η (squarefreeIdeal K T.val) *
      sexticEnvelopeEvaluation K S ζ hζ σ E hES hE6 T.val
        (Finset.mem_powerset.mp T.property) u ^ (-1 : ℤ) *
      W (idealNorm K (squarefreeIdeal K T.val) / D)

theorem sexticRowPolynomial_one (η : HeckeCharacter K) (D : ℝ) (W : ℝ → ℂ) :
    sexticRowPolynomial K S ζ hζ σ E hES hE6 η 1 D W =
      squarefreePolynomial K η E D W := by
  simp only [sexticRowPolynomial, sexticEnvelopeEvaluation_one, one_zpow, mul_one,
    squarefreePolynomial, squarefreeSum]
  congr 1
  exact Finset.sum_attach E.powerset (fun T =>
    (UniqueFactorizationMonoid.moebius (squarefreeIdeal K T).val : ℂ) *
      heckeIdealCoefficient K η (squarefreeIdeal K T) *
      W (idealNorm K (squarefreeIdeal K T) / D))

/-- For denominators inside P union Q, coprimality with the row modulus
means that every denominator prime belongs to Q. -/
theorem squarefreeIdeal_coprime_contraction_iff_subset
    (P Q : Finset (HeightOneSpectrum (𝓞 K))) (a : S.integer K)
    (hP : ∀ p ∈ P, p.asIdeal ∣ sIntegerModulusContraction K S a)
    (hQ : ∀ p ∈ Q, ¬p.asIdeal ∣ sIntegerModulusContraction K S a)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (hT : T ⊆ P ∪ Q) :
    IsCoprime (squarefreeIdeal K T).val (sIntegerModulusContraction K S a) ↔ T ⊆ Q := by
  change IsCoprime (∏ p ∈ T, p.asIdeal) (sIntegerModulusContraction K S a) ↔ _
  rw [IsCoprime.prod_left_iff]
  constructor
  · intro hc p hp
    rcases Finset.mem_union.mp (hT hp) with hpP | hpQ
    · exact False.elim ((primeIdeal_coprime_iff_not_dvd K p _).mp (hc p hp) (hP p hpP))
    · exact hpQ
  · intro ht p hp
    exact (primeIdeal_coprime_iff_not_dvd K p _).mpr (hQ p (ht hp))

/-- The actual sixth-power row on the SAME envelope P union Q is precisely
the squarefree polynomial on Q; inversion preserves its zero/one mask. -/
theorem sexticRowPolynomial_sixth_power
    (P Q : Finset (HeightOneSpectrum (𝓞 K)))
    (hES : ∀ p ∈ P ∪ Q, p ∉ S)
    (hE6 : ∀ p ∈ P ∪ Q, (6 : 𝓞 K) ∉ p.asIdeal)
    (η : HeckeCharacter K) (a : S.integer K)
    (hP : ∀ p ∈ P, p.asIdeal ∣ sIntegerModulusContraction K S a)
    (hQ : ∀ p ∈ Q, ¬p.asIdeal ∣ sIntegerModulusContraction K S a)
    (D : ℝ) (W : ℝ → ℂ) :
    sexticRowPolynomial K S ζ hζ σ (P ∪ Q) hES hE6 η (a ^ 6) D W =
      squarefreePolynomial K η Q D W := by
  let f : Finset (HeightOneSpectrum (𝓞 K)) → ℂ := fun T =>
    (UniqueFactorizationMonoid.moebius (squarefreeIdeal K T).val : ℂ) *
      heckeIdealCoefficient K η (squarefreeIdeal K T) *
      W (idealNorm K (squarefreeIdeal K T) / D)
  unfold sexticRowPolynomial squarefreePolynomial squarefreeSum
  congr 1
  have hsum :
      (∑ T ∈ (P ∪ Q).powerset.attach,
        (UniqueFactorizationMonoid.moebius (squarefreeIdeal K T.val).val : ℂ) *
          heckeIdealCoefficient K η (squarefreeIdeal K T.val) *
          sexticEnvelopeEvaluation K S ζ hζ σ (P ∪ Q) hES hE6 T.val
            (Finset.mem_powerset.mp T.property) (a ^ 6) ^ (-1 : ℤ) *
          W (idealNorm K (squarefreeIdeal K T.val) / D)) =
        ∑ T ∈ (P ∪ Q).powerset.attach, if T.val ⊆ Q then f T.val else 0 := by
    apply Finset.sum_congr rfl
    intro T _hT
    rw [sexticEnvelopeEvaluation_sixth_power_mask,
      squarefreeIdeal_coprime_contraction_iff_subset K S P Q a hP hQ
        T.val (Finset.mem_powerset.mp T.property)]
    by_cases ht : T.val ⊆ Q <;> simp [ht, f]
  rw [hsum]
  have hattach :
      (∑ T ∈ (P ∪ Q).powerset.attach, if T.val ⊆ Q then f T.val else 0) =
        ∑ T ∈ (P ∪ Q).powerset, if T ⊆ Q then f T else 0 :=
    Finset.sum_attach (P ∪ Q).powerset (fun T => if T ⊆ Q then f T else 0)
  rw [hattach, ← Finset.sum_filter]
  have hfilter : (P ∪ Q).powerset.filter (fun T => T ⊆ Q) = Q.powerset := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h.trans Finset.subset_union_right, h⟩
  rw [hfilter]

/-- Exact source amplification identity with actual sextic coefficients.
The row-one polynomial and every sixth-power row use the same finite prime
envelope and the same W. This is an identity, not an energy bound. -/
theorem sexticRowPolynomial_amplification
    (P Q : Finset (HeightOneSpectrum (𝓞 K))) (hd : Disjoint P Q)
    (hES : ∀ p ∈ P ∪ Q, p ∉ S)
    (hE6 : ∀ p ∈ P ∪ Q, (6 : 𝓞 K) ∉ p.asIdeal)
    (η : HeckeCharacter K) (a : S.integer K)
    (hP : ∀ p ∈ P, p.asIdeal ∣ sIntegerModulusContraction K S a)
    (hQ : ∀ p ∈ Q, ¬p.asIdeal ∣ sIntegerModulusContraction K S a)
    {D : ℝ} (hD : 0 < D) (W : ℝ → ℂ) :
    sexticRowPolynomial K S ζ hζ σ (P ∪ Q) hES hE6 η 1 D W =
      ∑ A ∈ P.powerset,
        (UniqueFactorizationMonoid.moebius (squarefreeIdeal K A).val : ℂ) *
          heckeIdealCoefficient K η (squarefreeIdeal K A) *
          (Real.sqrt (idealNorm K (squarefreeIdeal K A)) : ℂ)⁻¹ *
          sexticRowPolynomial K S ζ hζ σ (P ∪ Q) hES hE6 η (a ^ 6)
            (D / idealNorm K (squarefreeIdeal K A)) W := by
  rw [sexticRowPolynomial_one, squarefreePolynomial_disjoint_union K η P Q hd hD W]
  apply Finset.sum_congr rfl
  intro A _hA
  rw [sexticRowPolynomial_sixth_power K S ζ hζ σ P Q hES hE6 η a hP hQ]

end HeckeGeneral.Analysis.SquarefreeAmplification
