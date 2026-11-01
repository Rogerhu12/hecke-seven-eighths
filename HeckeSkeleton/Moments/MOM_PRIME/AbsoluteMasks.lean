import HeckeGeneral.Analysis.MomentInputs

/-!
# Exact deletion of an additional prime mask

This is the prime-slot identity used alongside divisor inclusion-exclusion
for the two plain factors in §4.6.  The deleted terms are precisely the
primes dividing the additional ideal.  The original common mask and all
ramified coefficient zeros remain in each term.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

theorem primeIdeal_coprime_iff_not_dvd (p : HeightOneSpectrum (𝓞 K))
    (R : Ideal (𝓞 K)) : IsCoprime p.asIdeal R ↔ ¬ p.asIdeal ∣ R := by
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.dvd_iff_le]
  constructor
  · intro h hle
    apply p.isMaximal.ne_top
    simpa only [sup_eq_left.mpr hle] using h
  · intro hn
    by_contra h
    have he : p.asIdeal = p.asIdeal ⊔ R := p.isMaximal.eq_of_le h le_sup_left
    exact hn (le_sup_right.trans_eq he.symm)

/-- Add a fixed ideal mask while preserving every other model field. -/
abbrev withExtraIdealMask {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
    (R : Ideal (𝓞 K)) : MomentData K ω ψ :=
  { d with commonMask := fun u I => d.commonMask u I && decide (IsCoprime I R) }

/-- The prime terms excluded by the additional mask, with their original
normalization, arithmetic coefficients, and original common mask. -/
def deletedPrimePolynomial {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
    (R : Ideal (𝓞 K)) (i : Fin d.geometry.slotCount)
    (u : NonzeroIdeal K) (Z t : ℝ) : ℂ :=
  let P := Z ^ (d.geometry.slots i).length
  (Real.sqrt P : ℂ)⁻¹ *
    ∑ p ∈ ((d.geometry.slots i).support t P).filter (fun p => p.asIdeal ∣ R),
      primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p *
        (d.geometry.slots i).profile t ((Ideal.absNorm p.asIdeal : ℝ) / P) *
        maskValue d u p.asIdeal

/-- Exact prime-slot subtraction before taking any absolute value. -/
theorem primePolynomial_withExtraIdealMask {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (R : Ideal (𝓞 K)) (i : Fin d.geometry.slotCount)
    (u : NonzeroIdeal K) (Z t : ℝ) :
    primePolynomial (withExtraIdealMask d R) i u Z t =
      primePolynomial d i u Z t - deletedPrimePolynomial d R i u Z t := by
  simp only [primePolynomial, deletedPrimePolynomial, withExtraIdealMask]
  rw [← mul_sub, Finset.sum_filter, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  cases hm : d.commonMask u p.asIdeal <;>
    by_cases hp : p.asIdeal ∣ R <;>
      simp [maskValue, primeIdeal_coprime_iff_not_dvd, hm, hp]

/-- The same additional mask can be removed simultaneously from every
actual prime slot, including an empty product. -/
theorem slotProduct_withExtraIdealMask {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (R : Ideal (𝓞 K))
    (u : NonzeroIdeal K) (Z t : ℝ) :
    slotProduct (withExtraIdealMask d R) u Z t =
      ∏ i, (primePolynomial d i u Z t - deletedPrimePolynomial d R i u Z t) := by
  unfold slotProduct
  apply Finset.prod_congr rfl
  intro i _
  exact primePolynomial_withExtraIdealMask d R i u Z t

/-- Adding a column mask does not change either permitted-row branch. -/
theorem pairedRows_withExtraIdealMask {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (R : Ideal (𝓞 K)) (a : RealParameters) (Z : ℝ) :
    pairedRows (withExtraIdealMask d R) a Z = pairedRows d a Z := rfl

end HeckeSkeleton.Moments.MOM_PRIME
