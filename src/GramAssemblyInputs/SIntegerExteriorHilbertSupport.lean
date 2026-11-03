import HeckeGeneral.Arithmetic.SIntegerModulusValuation
import HeckeGeneral.Arithmetic.SIntegerLocalDiagonal
import SIntegerSexticExteriorHilbertProduct

/-! SOURCE ONLY, UNRUN. Upstream chosenUnitFiniteSupport is a chosen finite
COVER, not an exact valuation support. Thus equality with contraction prime
support is not asserted. Every contraction prime is in the explicit exterior
Hilbert set, and any extra prime has zero ideal multiplicity. -/
noncomputable section
namespace HeckeGeneral.Arithmetic
open NumberField IsDedekindDomain KummerTheory
open GlobalClassFieldTheory.Reciprocity
open scoped Classical
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "NZI" => NonzeroRingElements (S.integer K)
local notation "U" => nonzeroSIntegerFieldUnit K S

/-- A prime of an actual contraction is exterior and has nonzero genuine
valuation exponent; hence it belongs to every covering support of U(a). -/
theorem sInteger_contraction_prime_mem_chosenHilbertSupport
    (a : NZI) (p : HeightOneSpectrum (𝓞 K))
    (hp : p.asIdeal ∣ sIntegerModulusContraction K S a.val) :
    p ∉ S ∧ p ∈ chosenUnitFiniteSupport (K := K) (U a) := by
  have hpS : p ∉ S := by
    intro hS
    have hc := sIntegerModulusContraction_coprime K S a.val a.property p hS
    rw [sup_eq_right.mpr (Ideal.dvd_iff_le.mp hp)] at hc
    exact p.isPrime.ne_top hc
  refine ⟨hpS, ?_⟩
  by_contra hnot
  have hval : p.valuation K (a.val : K) = 1 :=
    (mem_SUnitGroup_iff (K := K) (chosenUnitFiniteSupport (K := K) (U a)) (U a)).mp
      (mem_sUnitGroup_chosenUnitFiniteSupport (K := K) (U a)) p hnot
  have hcount : sIntegerModulusPrimeExponents K S a.val a.property p ≠ 0 := by
    change (UniqueFactorizationMonoid.normalizedFactors
      (sIntegerModulusContraction K S a.val)).count p.asIdeal ≠ 0
    apply Multiset.count_ne_zero.mpr
    exact (Ideal.mem_normalizedFactors_iff
      (sIntegerModulusContraction_ne_bot K S a.val a.property)).mpr
        ⟨p.isPrime, Ideal.dvd_iff_le.mp hp⟩
  have he := sIntegerModulus_valuation K S a.val a.property p hpS
  rw [hval] at he
  have hz : -(sIntegerModulusPrimeExponents K S a.val a.property p : ℤ) = 0 :=
    WithZero.exp_injective (he.symm.trans WithZero.exp_zero.symm)
  apply hcount
  exact_mod_cast neg_eq_zero.mp hz

/-- Both actual denominator prime sets lie in the explicit product domain.
No equality with the noncanonical chosen support is needed. -/
theorem sInteger_contraction_primes_mem_exteriorHilbertSupport
    (a b : NZI) (p : HeightOneSpectrum (𝓞 K))
    (hp : p.asIdeal ∣ sIntegerModulusContraction K S a.val ∨
      p.asIdeal ∣ sIntegerModulusContraction K S b.val) :
    p ∈ sIntegerSexticHilbertTotalSupport K S (U a) (U b) \ S.toFinset := by
  have hs : p ∉ S ∧ p ∈ powerResidueBadFinitePlaces K ⟨6, by norm_num⟩ (U a) (U b) := by
    rcases hp with ha | hb
    · obtain ⟨hpS, hpa⟩ := sInteger_contraction_prime_mem_chosenHilbertSupport K S a p ha
      exact ⟨hpS, Finset.mem_union_left _ (Finset.mem_union_left _ hpa)⟩
    · obtain ⟨hpS, hpb⟩ := sInteger_contraction_prime_mem_chosenHilbertSupport K S b p hb
      exact ⟨hpS, Finset.mem_union_left _ (Finset.mem_union_right _ hpb)⟩
  apply Finset.mem_sdiff.mpr
  exact ⟨Finset.mem_union_left _ hs.2, by simpa only [Set.mem_toFinset] using hs.1⟩

/-- Extra primes introduced by the finite covering support contribute
exponent zero to BOTH actual ideal-evaluation products. -/
theorem sInteger_exteriorHilbertSupport_extra_multiplicities_zero
    (a b : NZI) (p : HeightOneSpectrum (𝓞 K))
    (_hp : p ∈ sIntegerSexticHilbertTotalSupport K S (U a) (U b) \ S.toFinset)
    (ha : ¬ p.asIdeal ∣ sIntegerModulusContraction K S a.val)
    (hb : ¬ p.asIdeal ∣ sIntegerModulusContraction K S b.val) :
    AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity K p
        (sIntegerModulusContraction K S a.val) = 0 ∧
      AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity K p
        (sIntegerModulusContraction K S b.val) = 0 := by
  exact ⟨AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity_eq_zero_of_not_dvd
      K p _ (sIntegerModulusContraction_ne_bot K S a.val a.property) ha,
    AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity_eq_zero_of_not_dvd
      K p _ (sIntegerModulusContraction_ne_bot K S b.val b.property) hb⟩
end HeckeGeneral.Arithmetic
