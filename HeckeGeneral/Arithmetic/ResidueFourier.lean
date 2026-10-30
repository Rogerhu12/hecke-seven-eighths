import HeckeGeneral.Arithmetic.IdealMobiusMask
import HeckeGeneral.Arithmetic.DilationOperators
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The moving-mask front end on actual residue quotients

An exterior periodic coefficient on `R/c` is pulled back to `R/J`, where
`J` lies in both `c` and the mask's squarefree prime product. The resulting
mask is a genuine quotient function. Its Fourier expansion uses actual
Moebius coefficients and actual quotient maps.

For a principal divisor the finite change of variables includes the exact
cardinality of the multiplication kernel. This prevents treating a
nonunit quotient divisor as a permutation. These finite identities are
distinct from the later lattice change of variables, where multiplication
by a nonzero element is injective before taking a residue quotient.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic.ResidueFourier

open IsDedekindDomain UniqueFactorizationMonoid IdealMobiusMask PeriodicFourier
open scoped BigOperators Classical

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem primeProduct_antitone {S T : Finset (HeightOneSpectrum R)} (hTS : T ⊆ S) :
    primeProduct S ≤ primeProduct T := by
  intro k hk
  apply (mem_primeProduct T k).mpr
  intro p hp
  exact (mem_primeProduct S k).mp hk p (hTS hp)

def quotientIndicator (J I : Ideal R) (hJI : J ≤ I) (x : R ⧸ J) : ℂ :=
  if Ideal.Quotient.factor hJI x = 0 then 1 else 0

omit [IsDedekindDomain R] in
@[simp] theorem quotientIndicator_mk (J I : Ideal R) (hJI : J ≤ I) (k : R) :
    quotientIndicator J I hJI (Ideal.Quotient.mk J k) = membershipIndicator I k := by
  simp only [quotientIndicator, Ideal.Quotient.factor_mk,
    Ideal.Quotient.eq_zero_iff_mem, membershipIndicator]

theorem primeProduct_le_prime {S : Finset (HeightOneSpectrum R)}
    {p : HeightOneSpectrum R} (hp : p ∈ S) : primeProduct S ≤ p.asIdeal := by
  intro k hk
  exact (mem_primeProduct S k).mp hk p hp

def quotientMask (J : Ideal R) (S : Finset (HeightOneSpectrum R))
    (hJS : J ≤ primeProduct S) (x : R ⧸ J) : ℂ :=
  ∏ p : S, (1 - quotientIndicator J p.val.asIdeal (hJS.trans (primeProduct_le_prime p.property)) x)

@[simp] theorem quotientMask_mk (J : Ideal R) (S : Finset (HeightOneSpectrum R))
    (hJS : J ≤ primeProduct S) (k : R) :
    quotientMask J S hJS (Ideal.Quotient.mk J k) = avoidanceMask S k := by
  simp only [quotientMask, quotientIndicator_mk, avoidanceMask_eq_product]
  exact Finset.prod_coe_sort S (fun p => 1 - membershipIndicator p.asIdeal k)

def subsetDivisorIndicator (J : Ideal R) (S : Finset (HeightOneSpectrum R))
    (hJS : J ≤ primeProduct S) (T : S.powerset) : (R ⧸ J) → ℂ :=
  quotientIndicator J (primeProduct T.val)
    (hJS.trans (primeProduct_antitone (Finset.mem_powerset.mp T.property)))

@[simp] theorem subsetDivisorIndicator_mk (J : Ideal R) (S : Finset (HeightOneSpectrum R))
    (hJS : J ≤ primeProduct S) (T : S.powerset) (k : R) :
    subsetDivisorIndicator J S hJS T (Ideal.Quotient.mk J k) =
      membershipIndicator (primeProduct T.val) k := quotientIndicator_mk _ _ _ _

/-- The full moving mask descends and retains every squarefree ideal divisor. -/
theorem quotientMask_moebius_expansion (J : Ideal R) (S : Finset (HeightOneSpectrum R))
    (hJS : J ≤ primeProduct S) (x : R ⧸ J) :
    quotientMask J S hJS x = ∑ T : S.powerset,
      (moebius (primeProduct T.val) : ℂ) * subsetDivisorIndicator J S hJS T x := by
  induction x using Quotient.inductionOn' with
  | h k =>
    change quotientMask J S hJS (Ideal.Quotient.mk J k) = ∑ T : S.powerset,
      (moebius (primeProduct T.val) : ℂ) *
        subsetDivisorIndicator J S hJS T (Ideal.Quotient.mk J k)
    simp only [quotientMask_mk, subsetDivisorIndicator_mk]
    rw [Finset.sum_coe_sort S.powerset
      (fun T => (moebius (primeProduct T) : ℂ) * membershipIndicator (primeProduct T) k)]
    exact avoidanceMask_moebius_expansion S k

def exteriorPullback (J c : Ideal R) (hJc : J ≤ c) (f : (R ⧸ c) → ℂ) : (R ⧸ J) → ℂ :=
  fun x => f (Ideal.Quotient.factor hJc x)

omit [IsDedekindDomain R] in
@[simp] theorem exteriorPullback_mk (J c : Ideal R) (hJc : J ≤ c)
    (f : (R ⧸ c) → ℂ) (k : R) :
    exteriorPullback J c hJc f (Ideal.Quotient.mk J k) = f (Ideal.Quotient.mk c k) := rfl

omit [IsDedekindDomain R] in
theorem exteriorPullback_dilate (J c : Ideal R) (hJc : J ≤ c)
    (f : (R ⧸ c) → ℂ) (d : R) (x : R ⧸ J) :
    exteriorPullback J c hJc f (Ideal.Quotient.mk J d * x) =
      f (Ideal.Quotient.mk c d * Ideal.Quotient.factor hJc x) := by
  simp only [exteriorPullback, map_mul, Ideal.Quotient.factor_mk]

section Finite

variable (J : Ideal R) [Fintype (R ⧸ J)]

/-- A real finite Fourier expansion of the masked exterior coefficient. -/
theorem fourier_quotientMask (S : Finset (HeightOneSpectrum R)) (hJS : J ≤ primeProduct S)
    (ψ : AddChar (R ⧸ J) ℂ) (f : (R ⧸ J) → ℂ) (h : R ⧸ J) :
    fourier ψ (fun x => f x * quotientMask J S hJS x) h =
      ∑ T : S.powerset, (moebius (primeProduct T.val) : ℂ) *
        fourier ψ (fun x => f x * subsetDivisorIndicator J S hJS T x) h := by
  have hf : (fun x => f x * quotientMask J S hJS x) =
      fun x => ∑ T : S.powerset, (moebius (primeProduct T.val) : ℂ) *
        (f x * subsetDivisorIndicator J S hJS T x) := by
    funext x
    rw [quotientMask_moebius_expansion, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    ring
  rw [hf, fourier_sum]
  simp only [fourier_const_mul]

/-- The exact finite Poisson front end before an orbital/lattice integral is introduced. -/
theorem finite_masked_poisson (S : Finset (HeightOneSpectrum R))
    (hJS : J ≤ primeProduct S) (ψ : AddChar (R ⧸ J) ℂ) (hψ : ψ.IsPrimitive)
    (f g : (R ⧸ J) → ℂ) :
    (Fintype.card (R ⧸ J) : ℂ) * ∑ x : R ⧸ J, f x * quotientMask J S hJS x * g x =
      ∑ T : S.powerset, (moebius (primeProduct T.val) : ℂ) *
        ∑ h : R ⧸ J, fourier ψ (fun x => f x * subsetDivisorIndicator J S hJS T x) h *
          fourier ψ g (-h) := by
  rw [finite_poisson ψ hψ (fun x => f x * quotientMask J S hJS x) g]
  simp_rw [fourier_quotientMask, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  simp only [Finset.mul_sum, mul_assoc]

section Principal

variable [IsPrincipalIdealRing R]

omit [IsDedekindDomain R] in
/-- Ideal membership in a compatible quotient is exactly the image of its
actual generator's multiplication map, including all nonunit fibres. -/
theorem quotientIndicator_generator_image (I : Ideal R) (hJI : J ≤ I) (x : R ⧸ J) :
    quotientIndicator J I hJI x =
      if ∃ a : R ⧸ J, Ideal.Quotient.mk J (Submodule.IsPrincipal.generator I) * a = x
        then 1 else 0 := by
  have hequiv : Ideal.Quotient.factor hJI x = 0 ↔
      ∃ a : R ⧸ J, Ideal.Quotient.mk J (Submodule.IsPrincipal.generator I) * a = x := by
    constructor
    · induction x using Quotient.inductionOn' with
      | h k =>
        intro hk
        have hmem : k ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hk
        obtain ⟨a, ha⟩ := (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp hmem
        refine ⟨Ideal.Quotient.mk J a, ?_⟩
        rw [← map_mul, ← ha]
        rfl
    · rintro ⟨a, ha⟩
      rw [← ha, map_mul, Ideal.Quotient.factor_mk]
      have hgen : Ideal.Quotient.mk I (Submodule.IsPrincipal.generator I) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Submodule.IsPrincipal.generator_mem I)
      rw [hgen, zero_mul]
  simp only [quotientIndicator, hequiv]

omit [IsDedekindDomain R] in
/-- The explicit nonunit-divisor Fourier rule for an actual ideal mask. -/
theorem fourier_quotientIndicator_generator (I : Ideal R) (hJI : J ≤ I)
    (ψ : AddChar (R ⧸ J) ℂ) (f : (R ⧸ J) → ℂ) (h : R ⧸ J) :
    fourier ψ (fun x => f x * quotientIndicator J I hJI x) h =
      (fibreCard (Ideal.Quotient.mk J (Submodule.IsPrincipal.generator I)) 0 : ℂ)⁻¹ *
        fourier ψ (dilate (Ideal.Quotient.mk J (Submodule.IsPrincipal.generator I)) f)
          (Ideal.Quotient.mk J (Submodule.IsPrincipal.generator I) * h) := by
  have hf : (fun x => f x * quotientIndicator J I hJI x) =
      fun x => if ∃ a : R ⧸ J,
        Ideal.Quotient.mk J (Submodule.IsPrincipal.generator I) * a = x then f x else 0 := by
    funext x
    rw [quotientIndicator_generator_image]
    split_ifs <;> simp
  rw [hf]
  exact fourier_image_mask ψ f _ h

end Principal
end Finite

end HeckeGeneral.Arithmetic.ResidueFourier
