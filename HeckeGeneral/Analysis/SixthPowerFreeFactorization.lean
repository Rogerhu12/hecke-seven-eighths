import HeckeGeneral.Analysis.MomentInputs
import HeckeGeneral.Arithmetic.IdealFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
Recover the sixth-power-free ideal and its sixth-power amplifier separately.
This proves the arithmetic noncollision statement needed by a simultaneous
row amplifier. It does not assert an independent-scale moment estimate.
-/

noncomputable section

namespace HeckeGeneral.Analysis.ConditionalMoments

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open UniqueFactorizationMonoid
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

theorem sixthPowerFreeIdeal_iff_primeExponents_lt (I : NonzeroIdeal K) :
    SixthPowerFreeIdeal I ↔ ∀ p, primeExponents I p < 6 := by
  unfold SixthPowerFreeIdeal
  apply forall_congr'
  intro p
  rw [← emultiplicity_lt_iff_not_dvd,
    emultiplicity_eq_count_normalizedFactors p.irreducible
      (nonZeroDivisors.coe_ne_zero I)]
  simp only [normalize_eq, primeExponents_apply, ENat.natCast_lt_natCast]

theorem primeExponents_pow_apply (I : NonzeroIdeal K) (n : ℕ)
    (p : HeightOneSpectrum (𝓞 K)) :
    primeExponents (I ^ n) p = n * primeExponents I p := by
  change (normalizedFactors (I.val ^ n)).count p.asIdeal =
    n * (normalizedFactors I.val).count p.asIdeal
  simp only [normalizedFactors_pow, Multiset.count_nsmul]

/-- Prime exponents modulo six recover the base, then recover the amplifier. -/
theorem sixthPowerFree_mul_sixth_unique
    {I J A B : NonzeroIdeal K}
    (hI : SixthPowerFreeIdeal I) (hJ : SixthPowerFreeIdeal J)
    (h : I * A ^ 6 = J * B ^ 6) : I = J ∧ A = B := by
  have hcounts (p : HeightOneSpectrum (𝓞 K)) :
      primeExponents I p = primeExponents J p ∧
      primeExponents A p = primeExponents B p := by
    have he := congrArg (fun L => primeExponents L p) h
    simp only [primeExponents_mul, Finsupp.add_apply, primeExponents_pow_apply] at he
    have hi := (sixthPowerFreeIdeal_iff_primeExponents_lt I).mp hI p
    have hj := (sixthPowerFreeIdeal_iff_primeExponents_lt J).mp hJ p
    omega
  constructor
  · apply (primeExponentEquiv (R := 𝓞 K)).injective
    exact Finsupp.ext fun p => (hcounts p).1
  · apply (primeExponentEquiv (R := 𝓞 K)).injective
    exact Finsupp.ext fun p => (hcounts p).2

/-- A pair of actual ideals is not identified with any other amplified pair. -/
def sixthPowerFreeAmplifierEmbedding :
    ({I : NonzeroIdeal K // SixthPowerFreeIdeal I} × NonzeroIdeal K) ↪
      NonzeroIdeal K where
  toFun x := x.1.val * x.2 ^ 6
  inj' x y h := by
    obtain ⟨hbase, hamp⟩ := sixthPowerFree_mul_sixth_unique
      x.1.property y.1.property h
    exact Prod.ext (Subtype.ext hbase) hamp

end HeckeGeneral.Analysis.ConditionalMoments
