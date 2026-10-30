import HeckeSkeleton.LowEnergy.IdealRows
import HeckeSkeleton.LowFrozenCube.Exponents

/-!
# Frozen numerator and complete cube on actual nonzero ideals

The previous deliverable proved the exponent arithmetic.  This file transports
it through the project's actual prime-exponent equivalence.  In particular the
complete cube is an actual ideal and the supported/prime-to-supported split is
injective, so transporting coefficients loses no multiplicity.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.FrozenIdealRows

open IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeSkeleton.LowFrozenCube HeckeSkeleton.LowEnergy.IdealRows
open scoped Classical BigOperators nonZeroDivisors NumberField

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

def Admissible (I : (Ideal R)⁰) : Prop :=
  ∀ p : HeightOneSpectrum R, AdmissibleExponent (primeExponents I p)

def minimumPart (I : (Ideal R)⁰) : (Ideal R)⁰ :=
  idealOfPrimeExponents ((primeExponents I).mapRange frozenMin frozenMin_zero)

def cubePart (I : (Ideal R)⁰) : (Ideal R)⁰ :=
  idealOfPrimeExponents ((primeExponents I).mapRange frozenCubeExp frozenCubeExp_zero)

@[simp] theorem exponent_minimumPart (I : (Ideal R)⁰) (p : HeightOneSpectrum R) :
    primeExponents (minimumPart I) p = frozenMin (primeExponents I p) := by
  simp only [minimumPart, primeExponents_idealOfPrimeExponents, Finsupp.mapRange_apply]

@[simp] theorem exponent_cubePart (I : (Ideal R)⁰) (p : HeightOneSpectrum R) :
    primeExponents (cubePart I) p = frozenCubeExp (primeExponents I p) := by
  simp only [cubePart, primeExponents_idealOfPrimeExponents, Finsupp.mapRange_apply]

/-- The actual numerator factorization, with zero valuations treated separately. -/
theorem minimum_cube_decomposition (I : (Ideal R)⁰) (hI : Admissible I) :
    minimumPart I * cubePart I ^ 3 = I := by
  apply (primeExponentEquiv (R := R)).injective
  ext p
  change primeExponents (minimumPart I * cubePart I ^ 3) p = primeExponents I p
  rw [primeExponents_mul, Finsupp.add_apply, exponent_pow,
    exponent_minimumPart, exponent_cubePart]
  exact (frozenExponent_decomposition _ (hI p)).symm

theorem minimumPart_dvd (I : (Ideal R)⁰) (hI : Admissible I) :
    (minimumPart I).val ∣ I.val := by
  refine ⟨(cubePart I).val ^ 3, ?_⟩
  exact (congrArg Subtype.val (minimum_cube_decomposition I hI)).symm

theorem cubePart_dvd (I : (Ideal R)⁰) (hI : Admissible I) :
    (cubePart I).val ∣ I.val := by
  apply dvd_of_exponents_le
  intro p
  rw [exponent_cubePart]
  have h := frozenExponent_decomposition (primeExponents I p) (hI p)
  omega

theorem minimumPart_support (I : (Ideal R)⁰) (p : HeightOneSpectrum R) :
    p.asIdeal ∣ (minimumPart I).val ↔ p.asIdeal ∣ I.val := by
  rw [← exponent_ne_zero_iff_dvd, ← exponent_ne_zero_iff_dvd,
    exponent_minimumPart]
  exact not_congr (frozenMin_eq_zero_iff _)

/-- Canonical minimum and cube data determine the original numerator exactly. -/
theorem minimum_cube_unique (I A X : (Ideal R)⁰)
    (hcanonical : ∀ p : HeightOneSpectrum R,
      CanonicalFrozenPair (primeExponents A p) (primeExponents X p))
    (h : A * X ^ 3 = I) : A = minimumPart I ∧ X = cubePart I := by
  have hloc (p : HeightOneSpectrum R) :
      primeExponents A p = frozenMin (primeExponents I p) ∧
      primeExponents X p = frozenCubeExp (primeExponents I p) := by
    apply frozenExponent_unique (hcanonical p)
    have he := congrArg (fun J : (Ideal R)⁰ => primeExponents J p) h
    simpa only [primeExponents_mul, Finsupp.add_apply, exponent_pow] using he.symm
  constructor
  · apply (primeExponentEquiv (R := R)).injective
    ext p
    change primeExponents A p = primeExponents (minimumPart I) p
    rw [exponent_minimumPart]
    exact (hloc p).1
  · apply (primeExponentEquiv (R := R)).injective
    ext p
    change primeExponents X p = primeExponents (cubePart I) p
    rw [exponent_cubePart]
    exact (hloc p).2

def supportedIdeal (F : Finset (HeightOneSpectrum R)) (I : (Ideal R)⁰) : (Ideal R)⁰ :=
  idealOfPrimeExponents ((primeExponents I).filter (fun p => p ∈ F))

def awayIdeal (F : Finset (HeightOneSpectrum R)) (I : (Ideal R)⁰) : (Ideal R)⁰ :=
  idealOfPrimeExponents ((primeExponents I).filter (fun p => p ∉ F))

@[simp] theorem exponent_supportedIdeal (F : Finset (HeightOneSpectrum R))
    (I : (Ideal R)⁰) (p : HeightOneSpectrum R) :
    primeExponents (supportedIdeal F I) p = if p ∈ F then primeExponents I p else 0 := by
  simp only [supportedIdeal, primeExponents_idealOfPrimeExponents, Finsupp.filter_apply]

@[simp] theorem exponent_awayIdeal (F : Finset (HeightOneSpectrum R))
    (I : (Ideal R)⁰) (p : HeightOneSpectrum R) :
    primeExponents (awayIdeal F I) p = if p ∉ F then primeExponents I p else 0 := by
  simp only [awayIdeal, primeExponents_idealOfPrimeExponents, Finsupp.filter_apply]

theorem supported_away_decomposition (F : Finset (HeightOneSpectrum R)) (I : (Ideal R)⁰) :
    supportedIdeal F I * awayIdeal F I = I := by
  apply (primeExponentEquiv (R := R)).injective
  ext p
  change primeExponents (supportedIdeal F I * awayIdeal F I) p = primeExponents I p
  rw [primeExponents_mul, Finsupp.add_apply, exponent_supportedIdeal, exponent_awayIdeal]
  by_cases hp : p ∈ F <;> simp [hp]

theorem supportedIdeal_dvd (F : Finset (HeightOneSpectrum R)) (I : (Ideal R)⁰) :
    (supportedIdeal F I).val ∣ I.val := by
  refine ⟨(awayIdeal F I).val, ?_⟩
  exact (congrArg Subtype.val (supported_away_decomposition F I)).symm

theorem awayIdeal_dvd (F : Finset (HeightOneSpectrum R)) (I : (Ideal R)⁰) :
    (awayIdeal F I).val ∣ I.val := by
  refine ⟨(supportedIdeal F I).val, ?_⟩
  have h := congrArg Subtype.val (supported_away_decomposition F I)
  simpa only [Submonoid.coe_mul, mul_comm] using h.symm

/-- The full cube `b=x*n` has a unique actual split when x is F-supported
and n avoids F; this is the actual-ideal version of `fullCube_unique`. -/
theorem supported_away_unique (F : Finset (HeightOneSpectrum R)) (X N B : (Ideal R)⁰)
    (hX : ∀ p : HeightOneSpectrum R, p ∉ F → primeExponents X p = 0)
    (hN : ∀ p ∈ F, primeExponents N p = 0)
    (h : X * N = B) : X = supportedIdeal F B ∧ N = awayIdeal F B := by
  have he (p : HeightOneSpectrum R) : primeExponents X p + primeExponents N p =
      primeExponents B p := by
    simpa only [primeExponents_mul, Finsupp.add_apply] using
      congrArg (fun J : (Ideal R)⁰ => primeExponents J p) h
  constructor
  · apply (primeExponentEquiv (R := R)).injective
    ext p
    change primeExponents X p = primeExponents (supportedIdeal F B) p
    rw [exponent_supportedIdeal]
    by_cases hp : p ∈ F
    · simpa [hp, hN p hp] using he p
    · simp [hp, hX p hp]
  · apply (primeExponentEquiv (R := R)).injective
    ext p
    change primeExponents N p = primeExponents (awayIdeal F B) p
    rw [exponent_awayIdeal]
    by_cases hp : p ∈ F
    · simp [hp, hN p hp]
    · simpa [hp, hX p hp] using he p

def fullCubeSplit (F : Finset (HeightOneSpectrum R)) (B : (Ideal R)⁰) :
    (Ideal R)⁰ × (Ideal R)⁰ := (supportedIdeal F B, awayIdeal F B)

theorem fullCubeSplit_mul (F : Finset (HeightOneSpectrum R)) (X N : (Ideal R)⁰)
    (hX : ∀ p : HeightOneSpectrum R, p ∉ F → primeExponents X p = 0)
    (hN : ∀ p ∈ F, primeExponents N p = 0) :
    fullCubeSplit F (X * N) = (X, N) := by
  have h := supported_away_unique F X N (X * N) hX hN rfl
  exact Prod.ext h.1.symm h.2.symm

/-- No multiplicity loss in the exact full-cube indexing. -/
theorem fullCube_mul_injective_on (F : Finset (HeightOneSpectrum R))
    (T : Set ((Ideal R)⁰ × (Ideal R)⁰))
    (hX : ∀ q ∈ T, ∀ p : HeightOneSpectrum R, p ∉ F → primeExponents q.1 p = 0)
    (hN : ∀ q ∈ T, ∀ p ∈ F, primeExponents q.2 p = 0) :
    Set.InjOn (fun q : (Ideal R)⁰ × (Ideal R)⁰ => q.1 * q.2) T := by
  intro q hq r hr h
  calc
    q = fullCubeSplit F (q.1 * q.2) := (fullCubeSplit_mul F _ _ (hX q hq) (hN q hq)).symm
    _ = fullCubeSplit F (r.1 * r.2) := congrArg (fullCubeSplit F) h
    _ = r := fullCubeSplit_mul F _ _ (hX r hr) (hN r hr)

section NumberField

variable {K : Type*} [Field K] [NumberField K]

theorem norm_minimum_cube_decomposition (I : (Ideal (𝓞 K))⁰) (hI : Admissible I) :
    (I.val.absNorm : ℝ) = (minimumPart I).val.absNorm * ((cubePart I).val.absNorm : ℝ) ^ 3 := by
  have h := congrArg (fun J : (Ideal (𝓞 K))⁰ => (J.val.absNorm : ℝ))
    (minimum_cube_decomposition I hI)
  simpa only [Submonoid.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow,
    Nat.cast_mul, Nat.cast_pow] using h.symm

/-- Exact prime product for norms on any finite set containing all factors. -/
theorem norm_eq_prime_product (I : (Ideal (𝓞 K))⁰)
    (F : Finset (HeightOneSpectrum (𝓞 K)))
    (hF : (primeExponents I).support ⊆ F) :
    (I.val.absNorm : ℂ) = ∏ p ∈ F, (p.asIdeal.absNorm : ℂ) ^ primeExponents I p := by
  let f : Ideal (𝓞 K) →* ℂ :=
    (Nat.castRingHom ℂ).toMonoidHom.comp Ideal.absNorm.toMonoidHom
  have h := map_idealOfPrimeExponents f (primeExponents I)
  rw [idealOfPrimeExponents_primeExponents] at h
  rw [Finsupp.prod_of_support_subset _ hF _ (fun _ _ => pow_zero _)] at h
  exact h

end NumberField

#print axioms minimum_cube_decomposition
#print axioms minimum_cube_unique
#print axioms supported_away_unique
#print axioms fullCube_mul_injective_on

end HeckeSkeleton.LowEnergy.FrozenIdealRows
