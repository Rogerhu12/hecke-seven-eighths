import HeckeSkeleton.Moments.MOM_INV_STEP.PrimitiveUnitGauss
import HeckeSkeleton.Moments.MOM_INV_STEP.ThetaGaussCRT

/-!
# Signed CRT for disjoint actual primitive packets

The two packets may have different conductor digits at every prime.
Their source coefficients are the constructed primitive quotient
functions. The union, quotient transports, and product identification
are proved from these functions, before the actual finite Gauss sums
are multiplied.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.PrimitivePacketCRT

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ActualFiniteSource ConductorMasks PrimitivePoissonSource PrimitiveFourier
  PrincipalGaussCRT UnitGaussTransport
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

def unionBlock (B₁ B₂ : PrimeBlock K Sset) : PrimeBlock K Sset where
  support := B₁.support ∪ B₂.support
  outside p hp := (Finset.mem_union.mp hp).elim (B₁.outside p) (B₂.outside p)
  awaySix p hp := (Finset.mem_union.mp hp).elim (B₁.awaySix p) (B₂.awaySix p)

/-- One literal prime coefficient, with the exterior condition explicit. -/
def primeScalar (p : HeightOneSpectrum (𝓞 K)) (a : OS) : ℂ :=
  if hp : p ∉ Sset then
    sIntegerSexticEvaluation K Sset p hp D.root6 D.primitive6 D.embedding
      (D.away_six p hp) a
  else 0

theorem primitiveCoefficient_mk_eq_product (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (a : OS) :
    primitiveCoefficient K S D B t (Ideal.Quotient.mk _ a) =
      ∏ p ∈ activeSupport B.support t, primeScalar K S D p a ^ (t p).val := by
  rw [primitiveCoefficient_mk]
  refine Finset.prod_bij (fun p _hp => p.val) ?_ ?_ ?_ ?_
  · intro p hp
    exact Finset.mem_filter.mpr ⟨p.property, (Finset.mem_filter.mp hp).2⟩
  · intro p _hp q _hq hpq
    exact Subtype.ext hpq
  · intro p hp
    refine ⟨⟨p, (Finset.mem_filter.mp hp).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩, rfl⟩
  · intro p hp
    have ht : (t p.val).val ≠ 0 :=
      (ZMod.val_ne_zero _).mpr (Finset.mem_filter.mp hp).2
    rw [MulChar.pow_apply' _ ht]
    simp only [primeScalar, dif_pos (B.outside p.val p.property), sIntegerSexticEvaluation]

theorem activeSupport_union (B₁ B₂ : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    activeSupport (unionBlock K S B₁ B₂).support t =
      activeSupport B₁.support t ∪ activeSupport B₂.support t := by
  simp only [unionBlock, activeSupport, Finset.filter_union]

theorem activeSupport_disjoint (B₁ B₂ : PrimeBlock K Sset)
    (hdisj : Disjoint B₁.support B₂.support)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    Disjoint (activeSupport B₁.support t) (activeSupport B₂.support t) :=
  hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem primitiveExterior_union (B₁ B₂ : PrimeBlock K Sset)
    (hdisj : Disjoint B₁.support B₂.support)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    primitiveExterior K S (unionBlock K S B₁ B₂) t =
      exteriorMul K Sset (primitiveExterior K S B₁ t) (primitiveExterior K S B₂ t) := by
  apply Subtype.ext
  apply Subtype.ext
  change IdealMobiusMask.primeProduct (activeSupport (unionBlock K S B₁ B₂).support t) =
    IdealMobiusMask.primeProduct (activeSupport B₁.support t) *
      IdealMobiusMask.primeProduct (activeSupport B₂.support t)
  rw [activeSupport_union]
  exact Finset.prod_union (activeSupport_disjoint K S B₁ B₂ hdisj t)

theorem primitiveCoefficient_union_mk (B₁ B₂ : PrimeBlock K Sset)
    (hdisj : Disjoint B₁.support B₂.support)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (a : OS) :
    primitiveCoefficient K S D (unionBlock K S B₁ B₂) t (Ideal.Quotient.mk _ a) =
      primitiveCoefficient K S D B₁ t (Ideal.Quotient.mk _ a) *
        primitiveCoefficient K S D B₂ t (Ideal.Quotient.mk _ a) := by
  rw [primitiveCoefficient_mk_eq_product, primitiveCoefficient_mk_eq_product,
    primitiveCoefficient_mk_eq_product, activeSupport_union,
    Finset.prod_union (activeSupport_disjoint K S B₁ B₂ hdisj t)]

/-- Present the already proved primitive monoid coefficient by any
generator of its actual conductor ideal. -/
def characterAt (B : PrimeBlock K Sset) (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (c : OS)
    (hcspan : Ideal.span ({c} : Set OS) = (primitiveIdeal B.support t).map (algebraMap (𝓞 K) OS)) :
    QuotientRing OS c →* ℂ :=
  (primitiveCharacter K S D B t).comp
    (Ideal.quotEquivOfEq (hcspan.trans (primitiveModulus_span K S D B t).symm)).toMonoidHom

@[simp] theorem characterAt_mk (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (c : OS)
    (hcspan : Ideal.span ({c} : Set OS) = (primitiveIdeal B.support t).map (algebraMap (𝓞 K) OS))
    (a : OS) :
    characterAt K S D B t c hcspan (Ideal.Quotient.mk _ a) =
      primitiveCoefficient K S D B t (Ideal.Quotient.mk _ a) := by
  change primitiveCoefficient K S D B t
    (Ideal.quotEquivOfEq (hcspan.trans (primitiveModulus_span K S D B t).symm)
      (Ideal.Quotient.mk _ a)) = _
  rw [Ideal.quotEquivOfEq_mk]

def gaussAt (B : PrimeBlock K Sset) (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (c : OS) (hc : c ≠ 0)
    (hcspan : Ideal.span ({c} : Set OS) = (primitiveIdeal B.support t).map (algebraMap (𝓞 K) OS)) :
    ℂ := principalGauss K Sset D.different_outside c hc (characterAt K S D B t c hcspan)

theorem gaussAt_canonical (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    gaussAt K S D B t (primitiveModulus K S D B t)
        (primitiveModulus_ne_zero K S D B t) (primitiveModulus_span K S D B t) =
      primitiveGauss K S D B t := by
  letI := finite_sIntegerPrincipalResidue K Sset (primitiveModulus K S D B t)
    (primitiveModulus_ne_zero K S D B t)
  letI := Fintype.ofFinite (PrincipalQuotient K S D B t)
  rw [primitiveGauss_eq_sum]
  unfold gaussAt principalGauss
  apply Finset.sum_congr rfl
  intro q _hq
  congr 1
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact characterAt_mk K S D B t _ _ a

theorem characterAt_sixth_unit (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (c : OS)
    (hcspan : Ideal.span ({c} : Set OS) = (primitiveIdeal B.support t).map (algebraMap (𝓞 K) OS))
    (u : (Sset).unit K) :
    characterAt K S D B t c hcspan
      (Ideal.Quotient.mk _ (((Sset).unitEquivUnitsInteger K u).val ^ 6)) = 1 := by
  rw [characterAt_mk, primitiveCoefficient_sixth_unit]

/-- Exact sixth-unit transport for a packet with arbitrary active digits. -/
theorem gaussAt_sixth_unit (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (c : OS) (hc : c ≠ 0)
    (hcspan : Ideal.span ({c} : Set OS) = (primitiveIdeal B.support t).map (algebraMap (𝓞 K) OS))
    (u : (Sset).unit K)
    (hvspan : Ideal.span ({(((Sset).unitEquivUnitsInteger K u) ^ 6).val * c} : Set OS) =
      (primitiveIdeal B.support t).map (algebraMap (𝓞 K) OS)) :
    gaussAt K S D B t ((((Sset).unitEquivUnitsInteger K u) ^ 6).val * c)
        (mul_ne_zero (((Sset).unitEquivUnitsInteger K u) ^ 6).ne_zero hc) hvspan =
      gaussAt K S D B t c hc hcspan := by
  let v := ((Sset).unitEquivUnitsInteger K u) ^ 6
  have hchar : characterAt K S D B t (v.val * c) hvspan =
      unitCharacter c v (characterAt K S D B t c hcspan) := by
    apply MonoidHom.ext
    intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [characterAt_mk]
    change primitiveCoefficient K S D B t (Ideal.Quotient.mk _ a) =
      characterAt K S D B t c hcspan (unitQuotient c v (Ideal.Quotient.mk _ a))
    rw [unitQuotient_mk, characterAt_mk]
  unfold gaussAt
  rw [hchar, principalGauss_unit_of_value_one]
  simpa only [v, Units.val_pow_eq_pow_val] using
    characterAt_sixth_unit K S D B t c hcspan u

theorem primitiveIdeals_coprime (B₁ B₂ : PrimeBlock K Sset)
    (hdisj : Disjoint B₁.support B₂.support)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    IsCoprime (primitiveIdeal B₁.support t) (primitiveIdeal B₂.support t) := by
  unfold primitiveIdeal IdealMobiusMask.primeProduct
  apply IsCoprime.prod_left
  intro p hp
  apply IsCoprime.prod_right
  intro q hq
  apply Ideal.isCoprime_of_isMaximal
  intro he
  have hpq : p = q := HeightOneSpectrum.asIdeal_injective he
  subst q
  exact Finset.disjoint_left.mp (activeSupport_disjoint K S B₁ B₂ hdisj t) hp hq

theorem primitiveModuli_coprime (B₁ B₂ : PrimeBlock K Sset)
    (hdisj : Disjoint B₁.support B₂.support)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    IsCoprime (primitiveModulus K S D B₁ t) (primitiveModulus K S D B₂ t) :=
  ThetaGaussCRT.generators_coprime K Sset D
    (primitiveExterior K S B₁ t) (primitiveExterior K S B₂ t)
    (primitiveIdeals_coprime K S B₁ B₂ hdisj t)

theorem productModulus_span (B₁ B₂ : PrimeBlock K Sset)
    (hdisj : Disjoint B₁.support B₂.support)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    Ideal.span ({primitiveModulus K S D B₁ t * primitiveModulus K S D B₂ t} : Set OS) =
      (primitiveIdeal (unionBlock K S B₁ B₂).support t).map (algebraMap (𝓞 K) OS) := by
  have h := ThetaGaussCRT.productGenerator_span K Sset D
    (primitiveExterior K S B₁ t) (primitiveExterior K S B₂ t)
  rw [← primitiveExterior_union K S B₁ B₂ hdisj t] at h
  exact h

/-- The union packet on the product modulus is the CRT product of the
two actual primitive monoid coefficients, with arbitrary local digits. -/
theorem characterAt_product (B₁ B₂ : PrimeBlock K Sset)
    (hdisj : Disjoint B₁.support B₂.support)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    characterAt K S D (unionBlock K S B₁ B₂) t
        (primitiveModulus K S D B₁ t * primitiveModulus K S D B₂ t)
        (productModulus_span K S D B₁ B₂ hdisj t) =
      compositeCharacter (primitiveModulus K S D B₁ t) (primitiveModulus K S D B₂ t)
        (primitiveModuli_coprime K S D B₁ B₂ hdisj t)
        (primitiveCharacter K S D B₁ t) (primitiveCharacter K S D B₂ t) := by
  apply MonoidHom.ext
  intro q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [characterAt_mk, primitiveCoefficient_union_mk K S D B₁ B₂ hdisj t]
  change _ = primitiveCoefficient K S D B₁ t
      (quotientCRT (primitiveModulus K S D B₁ t) (primitiveModulus K S D B₂ t)
        (primitiveModuli_coprime K S D B₁ B₂ hdisj t) (Ideal.Quotient.mk _ a)).1 *
    primitiveCoefficient K S D B₂ t
      (quotientCRT (primitiveModulus K S D B₁ t) (primitiveModulus K S D B₂ t)
        (primitiveModuli_coprime K S D B₁ B₂ hdisj t) (Ideal.Quotient.mk _ a)).2
  rw [quotientCRT_mk]

theorem gaussAt_product (B₁ B₂ : PrimeBlock K Sset)
    (hdisj : Disjoint B₁.support B₂.support)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    gaussAt K S D (unionBlock K S B₁ B₂) t
        (primitiveModulus K S D B₁ t * primitiveModulus K S D B₂ t)
        (mul_ne_zero (primitiveModulus_ne_zero K S D B₁ t) (primitiveModulus_ne_zero K S D B₂ t))
        (productModulus_span K S D B₁ B₂ hdisj t) =
      (primitiveCoefficient K S D B₁ t (Ideal.Quotient.mk _ (primitiveModulus K S D B₂ t)) *
        primitiveCoefficient K S D B₂ t (Ideal.Quotient.mk _ (primitiveModulus K S D B₁ t))) *
        primitiveGauss K S D B₁ t * primitiveGauss K S D B₂ t := by
  unfold gaussAt
  rw [characterAt_product K S D B₁ B₂ hdisj t,
    principalGauss_mul K Sset D.different_outside
      (primitiveModulus K S D B₁ t) (primitiveModulus K S D B₂ t)
      (primitiveModulus_ne_zero K S D B₁ t) (primitiveModulus_ne_zero K S D B₂ t)
      (primitiveModuli_coprime K S D B₁ B₂ hdisj t),
    principalGauss_primitiveCharacter, principalGauss_primitiveCharacter]
  rfl

theorem primitiveGauss_eq_gaussAt_of_modulus (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (c : OS) (hc : c ≠ 0)
    (hcspan : Ideal.span ({c} : Set OS) = (primitiveIdeal B.support t).map (algebraMap (𝓞 K) OS))
    (hgen : primitiveModulus K S D B t = c) :
    primitiveGauss K S D B t = gaussAt K S D B t c hc hcspan := by
  subst c
  exact (gaussAt_canonical K S D B t).symm

/-- The actual selected-generator Gauss factor of a disjoint union
splits into the two genuine factors and their displayed cross symbols. -/
theorem primitiveGauss_union (hallowed : AllowedGeneratorInput K Sset D)
    (B₁ B₂ : PrimeBlock K Sset) (hdisj : Disjoint B₁.support B₂.support)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    primitiveGauss K S D (unionBlock K S B₁ B₂) t =
      (primitiveCoefficient K S D B₁ t (Ideal.Quotient.mk _ (primitiveModulus K S D B₂ t)) *
        primitiveCoefficient K S D B₂ t (Ideal.Quotient.mk _ (primitiveModulus K S D B₁ t))) *
        primitiveGauss K S D B₁ t * primitiveGauss K S D B₂ t := by
  obtain ⟨u, hu⟩ := hallowed.multiplicative
    (primitiveExterior K S B₁ t) (primitiveExterior K S B₂ t)
  rw [← primitiveExterior_union K S B₁ B₂ hdisj t] at hu
  let c := primitiveModulus K S D B₁ t * primitiveModulus K S D B₂ t
  let v := ((Sset).unitEquivUnitsInteger K u) ^ 6
  have hc : c ≠ 0 :=
    mul_ne_zero (primitiveModulus_ne_zero K S D B₁ t) (primitiveModulus_ne_zero K S D B₂ t)
  have hgen : primitiveModulus K S D (unionBlock K S B₁ B₂) t = v.val * c := by
    simpa only [primitiveModulus, v, c, Units.val_pow_eq_pow_val, mul_assoc] using hu
  have hvspan : Ideal.span ({v.val * c} : Set OS) =
      (primitiveIdeal (unionBlock K S B₁ B₂).support t).map (algebraMap (𝓞 K) OS) := by
    rw [← hgen]
    exact primitiveModulus_span K S D _ t
  rw [primitiveGauss_eq_gaussAt_of_modulus K S D (unionBlock K S B₁ B₂) t
    (v.val * c) (mul_ne_zero v.ne_zero hc) hvspan hgen]
  rw [gaussAt_sixth_unit K S D (unionBlock K S B₁ B₂) t c hc
    (productModulus_span K S D B₁ B₂ hdisj t) u hvspan]
  exact gaussAt_product K S D B₁ B₂ hdisj t

/-- Normalization preserves the exact signed grouped CRT factorization. -/
theorem normalizedPrimitiveGauss_union (hallowed : AllowedGeneratorInput K Sset D)
    (B₁ B₂ : PrimeBlock K Sset) (hdisj : Disjoint B₁.support B₂.support)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    normalizedPrimitiveGauss K S D (unionBlock K S B₁ B₂) t =
      (primitiveCoefficient K S D B₁ t (Ideal.Quotient.mk _ (primitiveModulus K S D B₂ t)) *
        primitiveCoefficient K S D B₂ t (Ideal.Quotient.mk _ (primitiveModulus K S D B₁ t))) *
        normalizedPrimitiveGauss K S D B₁ t * normalizedPrimitiveGauss K S D B₂ t := by
  have hideal : primitiveIdeal (unionBlock K S B₁ B₂).support t =
      primitiveIdeal B₁.support t * primitiveIdeal B₂.support t := by
    exact congrArg (fun I : ExteriorIdeal K Sset => I.val.val)
      (primitiveExterior_union K S B₁ B₂ hdisj t)
  have hnorm : (Real.sqrt ((primitiveIdeal (unionBlock K S B₁ B₂).support t).absNorm : ℝ) : ℂ) =
      (Real.sqrt ((primitiveIdeal B₁.support t).absNorm : ℝ) : ℂ) *
        (Real.sqrt ((primitiveIdeal B₂.support t).absNorm : ℝ) : ℂ) := by
    rw [hideal, map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  simp only [normalizedPrimitiveGauss]
  rw [primitiveGauss_union K S D hallowed B₁ B₂ hdisj t, hnorm]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

def activeBlock (B : PrimeBlock K Sset) (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    PrimeBlock K Sset where
  support := activeSupport B.support t
  outside p hp := B.outside p (Finset.mem_filter.mp hp).1
  awaySix p hp := B.awaySix p (Finset.mem_filter.mp hp).1

theorem prime_dvd_primitiveIdeal_iff (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (p : HeightOneSpectrum (𝓞 K)) :
    p.asIdeal ∣ primitiveIdeal B.support t ↔ p ∈ activeSupport B.support t := by
  constructor
  · intro hp
    obtain ⟨q, hq, hpq⟩ :=
      (p.prime.dvd_finsetProd_iff (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal)).mp hp
    have hqp : q = p := HeightOneSpectrum.ext
      (q.isMaximal.eq_of_le p.isPrime.ne_top (Ideal.dvd_iff_le.mp hpq))
    simpa only [hqp] using hq
  · intro hp
    exact Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal) hp

/-- The squarefree conductor ideal has one actual local row per active
prime. Its multiplicities are proved to be one, not supplied as data. -/
theorem primitiveIdeal_symbol_eq_product (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (a : OS) :
    idealSymbol K Sset D (primitiveExterior K S B t) a =
      ∏ p ∈ activeSupport B.support t, primeScalar K S D p a := by
  let C := activeBlock K S B t
  have hI : primitiveIdeal B.support t ≠ 0 := IdealMobiusMask.primeProduct_ne_bot _
  have hcover : PrimeBlock.Covers K Sset C (primitiveIdeal B.support t) := by
    intro p hp
    exact (prime_dvd_primitiveIdeal_iff K S B t p).mp hp
  have hrow := PrimeBlock.idealRow_eq_product K Sset D.root6 D.primitive6 D.embedding
    C (primitiveIdeal B.support t) hI hcover a
  change idealSymbol K Sset D (primitiveExterior K S B t) a =
    ∏ p : C.support, PrimeBlock.row K Sset D.root6 D.primitive6 D.embedding C p a ^
      AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity K p.val
        (primitiveIdeal B.support t) at hrow
  rw [hrow]
  calc
    _ = ∏ p : C.support, primeScalar K S D p.val a := by
      apply Finset.prod_congr rfl
      intro p _hp
      have hd : p.val.asIdeal ∣ primitiveIdeal B.support t :=
        (prime_dvd_primitiveIdeal_iff K S B t p.val).mpr p.property
      have hm := squarefree_prime_multiplicity K (primitiveIdeal B.support t) hI
        (primitiveIdeal_squarefree B.support t) p.val
      rw [hm]
      simp only [hd, decide_true, CubeAlgebra.bit, if_true, pow_one,
        primeScalar, dif_pos (C.outside p.val p.property), PrimeBlock.row,
        sIntegerSexticEvaluation]
    _ = _ := by
      convert (Finset.prod_coe_sort (activeSupport B.support t)
        (fun p => primeScalar K S D p a)) using 1 <;>
        congr 1 <;> ext p <;> simp [C, activeBlock]

/-- A uniform digit is the scalar power of the literal squarefree ideal
row. This includes the empty active conductor without deleting its zero mode. -/
theorem primitiveCoefficient_uniform (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (j : ℕ)
    (ht : ∀ p ∈ activeSupport B.support t, (t p).val = j) (a : OS) :
    primitiveCoefficient K S D B t (Ideal.Quotient.mk _ a) =
      idealSymbol K Sset D (primitiveExterior K S B t) a ^ j := by
  rw [primitiveCoefficient_mk_eq_product, primitiveIdeal_symbol_eq_product, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p hp
  rw [ht p hp]

theorem primitiveCharacter_uniform (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (j : ℕ)
    (ht : ∀ p ∈ activeSupport B.support t, (t p).val = j) :
    primitiveCharacter K S D B t =
      ThetaGaussCRT.idealCharacterAt K Sset D (primitiveExterior K S B t)
        (primitiveModulus K S D B t) (primitiveModulus_span K S D B t) j := by
  apply MonoidHom.ext
  intro q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  change primitiveCoefficient K S D B t (Ideal.Quotient.mk _ a) = _
  rw [ThetaGaussCRT.idealCharacterAt_mk, primitiveCoefficient_uniform K S D B t j ht]

/-- The actual normalized packet with uniform digit j is exactly the
existing thetaGamma at j, with its selected principal phase. -/
theorem normalizedPrimitiveGauss_uniform (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (j : ℕ)
    (ht : ∀ p ∈ activeSupport B.support t, (t p).val = j) :
    normalizedPrimitiveGauss K S D B t = thetaGamma K Sset D (primitiveExterior K S B t) j := by
  rw [ThetaGaussCRT.thetaGamma_eq_principalGauss]
  unfold ThetaGaussCRT.idealGaussAt
  rw [← primitiveCharacter_uniform K S D B t j ht,
    principalGauss_primitiveCharacter]
  change primitiveGauss K S D B t /
    (Real.sqrt ((primitiveIdeal B.support t).absNorm : ℝ) : ℂ) = _
  rw [div_eq_mul_inv, mul_comm]

end HeckeSkeleton.Moments.MOM_INV_STEP.PrimitivePacketCRT
