import HeckeSkeleton.Moments.MOM_INV_STEP.PrimitivePoissonSource
import HeckeSkeleton.Moments.MOM_INV_STEP.ProductGauss

/-!
# The genuine finite transform of the primitive Poisson coefficient

The CRT equivalence is constructed from ordinary squarefree CRT and the
actual S-integer residue equivalence.  Its local additive characters are
the restrictions of the repository's actual principal additive character,
so the Gauss product retains every generator-dependent phase.  The formula
allows arbitrary divisor dilation and arbitrary frequency, including zero
and nonunits.  Normalized Gauss phases are not replaced by unspecified
constants.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.PrimitiveFourier

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton AlgebraicNumberTheory.PowerResidueSymbols
open ActualFiniteSource ConductorMasks PrimitivePoissonSource ResidueTraceCharacters
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

abbrev PrincipalQuotient (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :=
  OS ⧸ Ideal.span ({primitiveModulus K S D B t} : Set OS)

abbrev ResidueProduct (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :=
  ∀ p : activeSupport B.support t, Residue p.val

local instance principalQuotientFinite (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    Finite (PrincipalQuotient K S D B t) :=
  finite_sIntegerPrincipalResidue K Sset (primitiveModulus K S D B t)
    (primitiveModulus_ne_zero K S D B t)

local instance principalQuotientFintype (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    Fintype (PrincipalQuotient K S D B t) := Fintype.ofFinite _

/-- The actual primitive quotient, transported to its ordinary residue
fields.  No equivalence or coefficient identification is an input. -/
def actualCRT (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    PrincipalQuotient K S D B t ≃+* ResidueProduct K S B t :=
  (Ideal.quotEquivOfEq (primitiveModulus_span K S D B t)).trans
    ((sIntegerResidueEquiv K Sset (primitiveIdeal B.support t)
      (sexticIdeal_coprime_S K Sset _ (primitiveExterior K S B t).property)).symm.trans
        (squarefreeCRT (activeSupport B.support t)))

theorem actualCRT_algebraMap (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (a : 𝓞 K) (p : activeSupport B.support t) :
    actualCRT K S D B t (Ideal.Quotient.mk _ (algebraMap (𝓞 K) OS a)) p =
      Ideal.Quotient.mk p.val.asIdeal a := by
  change squarefreeCRT (activeSupport B.support t)
    ((sIntegerResidueEquiv K Sset (primitiveIdeal B.support t)
      (sexticIdeal_coprime_S K Sset _ (primitiveExterior K S B t).property)).symm
      ((Ideal.quotEquivOfEq (primitiveModulus_span K S D B t))
        (Ideal.Quotient.mk _ (algebraMap (𝓞 K) OS a)))) p = _
  rw [Ideal.quotEquivOfEq_mk, sIntegerResidueEquiv_symm_mk]
  rfl

/-- Every coordinate is the literal S-integer residue, including
nonintegral S-integer representatives. -/
theorem actualCRT_mk (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (a : OS) (p : activeSupport B.support t) :
    actualCRT K S D B t (Ideal.Quotient.mk _ a) p =
      sIntegerSexticResidueMap K Sset p.val
        (B.outside p.val (Finset.mem_filter.mp p.property).1) a := by
  letI := sInteger_isLocalizationAway_finiteDenominator K Sset
  let j : OS →+* Residue p.val :=
    ((Pi.evalRingHom (fun p : activeSupport B.support t => Residue p.val) p).comp
      (actualCRT K S D B t).toRingHom).comp (Ideal.Quotient.mk _)
  have hsame : j = sIntegerSexticResidueMap K Sset p.val
      (B.outside p.val (Finset.mem_filter.mp p.property).1) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (finiteSIntegerDenominator K Sset))
    apply RingHom.ext
    intro b
    change actualCRT K S D B t (Ideal.Quotient.mk _ (algebraMap (𝓞 K) OS b)) p =
      sIntegerSexticResidueMap K Sset p.val
        (B.outside p.val (Finset.mem_filter.mp p.property).1)
        (algebraMap (𝓞 K) OS b)
    rw [actualCRT_algebraMap, sIntegerSexticResidueMap_algebraMap]
  exact RingHom.congr_fun hsame a

def activeCharacter (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (p : activeSupport B.support t) :
    MulChar (Residue p.val) ℂ :=
  sexticResidueCharacter K D.root6 D.primitive6 D.embedding p.val
    (B.awaySix p.val (Finset.mem_filter.mp p.property).1) ^ (t p.val).val

theorem activeCharacter_ne_one (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (p : activeSupport B.support t) :
    activeCharacter K S D B t p ≠ 1 := by
  intro hp
  have hd : 6 ∣ (t p.val).val := by
    have hpow : sexticResidueCharacter K D.root6 D.primitive6 D.embedding p.val
        (B.awaySix p.val (Finset.mem_filter.mp p.property).1) ^ (t p.val).val = 1 := hp
    have hdiv := orderOf_dvd_of_pow_eq_one hpow
    simpa only [sexticResidueCharacter_order K D.root6 D.primitive6 D.embedding p.val
      (B.awaySix p.val (Finset.mem_filter.mp p.property).1)] using hdiv
  have hz := Nat.mod_eq_zero_of_dvd hd
  rw [Nat.mod_eq_of_lt (ZMod.val_lt _)] at hz
  exact (Finset.mem_filter.mp p.property).2 ((ZMod.val_eq_zero _).mp hz)

/-- The actual source function is the tensor of its nonprincipal local
characters under the constructed CRT equivalence. -/
theorem primitiveCoefficient_eq_tensor (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (q : PrincipalQuotient K S D B t) :
    primitiveCoefficient K S D B t q =
      ProductGauss.tensorCoefficient (activeCharacter K S D B t) (actualCRT K S D B t q) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [primitiveCoefficient_mk]
  unfold ProductGauss.tensorCoefficient
  simp_rw [actualCRT_mk]
  refine Finset.prod_bij
    (fun p hp => (⟨p.val, Finset.mem_filter.mpr
      ⟨p.property, (Finset.mem_filter.mp hp).2⟩⟩ : activeSupport B.support t))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro p hp q hq he
    exact Subtype.ext (congrArg (fun x : activeSupport B.support t => x.val) he)
  · intro p _hp
    refine ⟨⟨p.val, (Finset.mem_filter.mp p.property).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp p.property).2⟩, rfl⟩
  · intro p hp
    rfl

theorem primitiveCoefficient_mul (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (q r : PrincipalQuotient K S D B t) :
    primitiveCoefficient K S D B t (q * r) =
      primitiveCoefficient K S D B t q * primitiveCoefficient K S D B t r := by
  simp only [primitiveCoefficient_eq_tensor, ProductGauss.tensorCoefficient, map_mul,
    Pi.mul_apply, Finset.prod_mul_distrib]

/-- The original principal additive phase transported to CRT coordinates. -/
def productPhase (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) : AddChar (ResidueProduct K S B t) ℂ :=
  transportCharacter (actualCRT K S D B t).symm
    (sIntegerActualModulusAddCharacter K Sset D.different_outside
      (primitiveModulus K S D B t) (primitiveModulus_ne_zero K S D B t))

theorem productPhase_isPrimitive (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    (productPhase K S D B t).IsPrimitive :=
  transportCharacter_isPrimitive _ _ (sIntegerActualModulusAddCharacter_isPrimitive
    K Sset D.different_outside (primitiveModulus K S D B t)
      (primitiveModulus_ne_zero K S D B t))

def primitiveGauss (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) : ℂ :=
  ProductGauss.gaussProduct (activeCharacter K S D B t) (productPhase K S D B t)

/-- The exact unnormalized finite Fourier coefficient.  The Gauss phase
is built from the actual principal additive character. -/
theorem finite_fourier (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (k : PrincipalQuotient K S D B t) :
    (∑ q : PrincipalQuotient K S D B t, primitiveCoefficient K S D B t q *
      sIntegerActualModulusAddCharacter K Sset D.different_outside
        (primitiveModulus K S D B t) (primitiveModulus_ne_zero K S D B t) (k * q)) =
      star (primitiveCoefficient K S D B t k) * primitiveGauss K S D B t := by
  calc
    _ = ∑ x : ResidueProduct K S B t,
        ProductGauss.tensorCoefficient (activeCharacter K S D B t) x *
          productPhase K S D B t (actualCRT K S D B t k * x) := by
      refine Fintype.sum_bijective _ (actualCRT K S D B t).bijective _ _ ?_
      intro q
      simp only [primitiveCoefficient_eq_tensor, productPhase,
        transportCharacter_apply, ← map_mul, RingEquiv.symm_apply_apply]
    _ = _ := by
      change (∑ x : (p : activeSupport B.support t) → Residue p.val,
        ProductGauss.tensorCoefficient (activeCharacter K S D B t) x *
          productPhase K S D B t (actualCRT K S D B t k * x)) = _
      have hf := ProductGauss.finite_fourier (activeCharacter K S D B t)
        (activeCharacter_ne_one K S D B t) (productPhase K S D B t) (actualCRT K S D B t k)
      rw [primitiveCoefficient_eq_tensor, primitiveGauss]
      convert hf using 1 <;> congr 1 <;> ext x <;> simp

@[simp] theorem primitiveCoefficient_one (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    primitiveCoefficient K S D B t 1 = 1 := by
  rw [primitiveCoefficient_eq_tensor]
  simp only [ProductGauss.tensorCoefficient, map_one, Pi.one_apply, Finset.prod_const_one]

/-- The CRT Gauss product is exactly the finite principal-phase sum on
the actual primitive quotient, including the unit conductor. -/
theorem primitiveGauss_eq_sum (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    primitiveGauss K S D B t =
      ∑ q : PrincipalQuotient K S D B t, primitiveCoefficient K S D B t q *
        sIntegerActualModulusAddCharacter K Sset D.different_outside
          (primitiveModulus K S D B t) (primitiveModulus_ne_zero K S D B t) q := by
  have h := finite_fourier K S D B t 1
  simpa only [one_mul, primitiveCoefficient_one, star_one] using h.symm

/-- A literal sixth power of an S-unit has coefficient one on the
actual primitive quotient, including the unit conductor. -/
theorem primitiveCoefficient_sixth_unit (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (u : (Sset).unit K) :
    primitiveCoefficient K S D B t
      (Ideal.Quotient.mk _ (((Sset).unitEquivUnitsInteger K u).val ^ 6)) = 1 := by
  let Γ₆ := (powMonoidHom 6 : (Sset).unit K →* (Sset).unit K).range
  have hu : u ^ 6 ∈ Γ₆ := ⟨u, rfl⟩
  have h := primitiveCoefficient_invariant K S D Γ₆ le_rfl B t ⟨u ^ 6, hu⟩ 1
  simpa only [map_pow, Units.val_pow_eq_pow_val, mul_one, map_one,
    primitiveCoefficient_one] using h

/-- The genuine Gauss phase is unchanged by a sixth-power unit shift.
This is the exact phase correction required by allowed generators. -/
theorem primitiveGauss_sixth_unit_phase (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (u : (Sset).unit K) :
    (∑ q : PrincipalQuotient K S D B t, primitiveCoefficient K S D B t q *
      sIntegerActualModulusAddCharacter K Sset D.different_outside
        (primitiveModulus K S D B t) (primitiveModulus_ne_zero K S D B t)
        (Ideal.Quotient.mk _ (((Sset).unitEquivUnitsInteger K u).val ^ 6) * q)) =
      primitiveGauss K S D B t := by
  rw [finite_fourier, primitiveCoefficient_sixth_unit, star_one, one_mul]

/-- Arbitrary divisor dilation is retained, including divisors that meet
the active conductor.  No coprimality is silently required. -/
theorem divisor_fourier (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (d : OS) (k : PrincipalQuotient K S D B t) :
    sIntegerPeriodicDivisorFourier K Sset D.different_outside
      (primitiveModulus K S D B t) (primitiveModulus_ne_zero K S D B t)
      (primitiveCoefficient K S D B t) d k =
      primitiveCoefficient K S D B t (Ideal.Quotient.mk _ d) *
        star (primitiveCoefficient K S D B t k) * primitiveGauss K S D B t := by
  rw [sIntegerPeriodicDivisorFourier_apply]
  simp_rw [primitiveCoefficient_mul, mul_assoc]
  rw [← Finset.mul_sum, finite_fourier, ← mul_assoc]

/-- Exact Gauss size at the primitive ideal, including the unit conductor. -/
theorem primitiveGauss_norm (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    ‖primitiveGauss K S D B t‖ = Real.sqrt ((primitiveIdeal B.support t).absNorm : ℝ) := by
  rw [primitiveGauss, ProductGauss.gaussProduct_norm _
    (activeCharacter_ne_one K S D B t) _ (productPhase_isPrimitive K S D B t)]
  simp only [← Nat.card_eq_fintype_card]
  have hcard : Nat.card (ResidueProduct K S B t) =
      Nat.card (PrincipalQuotient K S D B t) :=
    Nat.card_congr (actualCRT K S D B t).symm.toEquiv
  rw [hcard]
  change Real.sqrt (Nat.card (OS ⧸ Ideal.span
    ({primitiveModulus K S D B t} : Set OS)) : ℝ) = _
  rw [natCard_sIntegerPrincipalResidue_eq_productNorm, primitiveModulus_norm]

def normalizedPrimitiveGauss (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) : ℂ :=
  primitiveGauss K S D B t / (Real.sqrt ((primitiveIdeal B.support t).absNorm : ℝ) : ℂ)

theorem normalizedPrimitiveGauss_norm (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    ‖normalizedPrimitiveGauss K S D B t‖ = 1 := by
  have hpos : 0 < ((primitiveIdeal B.support t).absNorm : ℝ) := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors (primitiveExterior K S B t).val
  rw [normalizedPrimitiveGauss, norm_div, primitiveGauss_norm, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), div_self (ne_of_gt (Real.sqrt_pos.mpr hpos))]

/-- Nontrivial active conductor forces the actual finite zero frequency
to vanish; the proof uses an actual active prime factor. -/
theorem primitiveCoefficient_zero (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (hactive : (activeSupport B.support t).Nonempty) :
    primitiveCoefficient K S D B t 0 = 0 := by
  rw [primitiveCoefficient_eq_tensor]
  unfold ProductGauss.tensorCoefficient
  obtain ⟨p, hp⟩ := hactive
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨p, hp⟩ : activeSupport B.support t))
  simp only [map_zero, Pi.zero_apply, MulChar.map_zero]

theorem divisor_fourier_zero_of_active (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (hactive : (activeSupport B.support t).Nonempty) (d : OS) :
    sIntegerPeriodicDivisorFourier K Sset D.different_outside
      (primitiveModulus K S D B t) (primitiveModulus_ne_zero K S D B t)
      (primitiveCoefficient K S D B t) d 0 = 0 := by
  rw [divisor_fourier, primitiveCoefficient_zero K S D B t hactive]
  simp only [star_zero, mul_zero, zero_mul]

variable (Γ : Subgroup (((S : Set (HeightOneSpectrum (𝓞 K)))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 : ((S : Set (HeightOneSpectrum (𝓞 K)))).unit K →* ((S : Set (HeightOneSpectrum (𝓞 K)))).unit K).range)

/-- The actual primitive multiplicative row on the original Γ sectors. -/
def primitiveOrbitCoefficient (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) : SIntegerOrbits K Sset Γ → ℂ :=
  sIntegerPeriodicOrbitWeight K Sset Γ (primitiveModulus K S D B t)
    (primitiveCoefficient K S D B t) (primitiveCoefficient_invariant K S D Γ hΓ B t)

@[simp] theorem primitiveOrbitCoefficient_mk (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (a : NonzeroRingElements OS) :
    primitiveOrbitCoefficient K S D Γ hΓ B t (Quotient.mk _ a) =
      primitiveCoefficient K S D B t (Ideal.Quotient.mk _ a.val) := rfl

/-- The actual transformed row is the conjugate primitive row, with the
literal divisor character and the actual CRT Gauss factor retained. -/
theorem primitiveFourierOrbitWeight_eq (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (d : OS)
    (q : SIntegerOrbits K Sset Γ) :
    sIntegerPeriodicFourierOrbitWeight K Sset D.different_outside Γ
      (primitiveModulus K S D B t) (primitiveModulus_ne_zero K S D B t)
      (primitiveCoefficient K S D B t) (primitiveCoefficient_invariant K S D Γ hΓ B t)
      d q =
    primitiveCoefficient K S D B t (Ideal.Quotient.mk _ d) * primitiveGauss K S D B t *
      star (primitiveOrbitCoefficient K S D Γ hΓ B t q) := by
  refine Quotient.inductionOn q (fun a => ?_)
  rw [sIntegerPeriodicFourierOrbitWeight_mk, primitiveOrbitCoefficient_mk,
    divisor_fourier]
  ring

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]

/-- The complete Fourier orbital series has the actual inverse row.
This identity is valid at every positive radius and every divisor,
including those meeting the active conductor. -/
theorem fourier_orbital_series_eq_inverse (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (d : OS)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (ψ : ((v : Sset) → v.val.adicCompletion K) → ℂ)
    (r : {r : ℝ // 0 < r}) :
    HeckeGeneral.Analysis.sIntegerWeightedOrbitalSeries K S Γ φ ψ r
      (sIntegerPeriodicFourierOrbitWeight K Sset D.different_outside Γ
        (primitiveModulus K S D B t) (primitiveModulus_ne_zero K S D B t)
        (primitiveCoefficient K S D B t) (primitiveCoefficient_invariant K S D Γ hΓ B t) d) =
    primitiveCoefficient K S D B t (Ideal.Quotient.mk _ d) * primitiveGauss K S D B t *
      HeckeGeneral.Analysis.sIntegerWeightedOrbitalSeries K S Γ φ ψ r
        (fun q => star (primitiveOrbitCoefficient K S D Γ hΓ B t q)) := by
  have he :
      sIntegerPeriodicFourierOrbitWeight K Sset D.different_outside Γ
        (primitiveModulus K S D B t) (primitiveModulus_ne_zero K S D B t)
        (primitiveCoefficient K S D B t) (primitiveCoefficient_invariant K S D Γ hΓ B t) d =
      fun q => primitiveCoefficient K S D B t (Ideal.Quotient.mk _ d) *
        primitiveGauss K S D B t * star (primitiveOrbitCoefficient K S D Γ hΓ B t q) := by
    funext q
    exact primitiveFourierOrbitWeight_eq K S D Γ hΓ B t d q
  rw [he]
  unfold HeckeGeneral.Analysis.sIntegerWeightedOrbitalSeries
  simp_rw [mul_assoc]
  rw [tsum_mul_left, tsum_mul_left]

end HeckeSkeleton.Moments.MOM_INV_STEP.PrimitiveFourier
