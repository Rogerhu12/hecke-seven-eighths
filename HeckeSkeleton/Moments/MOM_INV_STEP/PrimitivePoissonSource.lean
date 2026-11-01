import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalPoissonSource
import HeckeSkeleton.Moments.MOM_INV_STEP.LocalizedMasks
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualFiniteSource
import HeckeSkeleton.Moments.MOM_INV_STEP.ConductorMasks

/-!
# Genuine Poisson data on the active conductor

The active local digits define an actual function on the quotient by the
localized primitive ideal.  Its finite-prime factors, literal invariance,
and complementary localized mask are proved from the residue maps.  No
primitive Fourier identity, mask identification or Poisson formula is a
field of the data.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.PrimitivePoissonSource

open NumberField IsDedekindDomain
  HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  AlgebraicNumberTheory.PowerResidueSymbols MeasureTheory
open ActualFiniteSource ConductorMasks
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

/-- The actual active squarefree conductor is an exterior nonzero ideal. -/
abbrev primitiveExterior (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) : ExteriorIdeal K Sset :=
  ⟨⟨primitiveIdeal B.support t,
      mem_nonZeroDivisors_of_ne_zero (IdealMobiusMask.primeProduct_ne_bot _)⟩, by
    intro p hp
    obtain ⟨q, hq, hpq⟩ :=
      (p.prime.dvd_finsetProd_iff (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal)).mp hp
    have he : q = p := HeightOneSpectrum.ext
      (q.isMaximal.eq_of_le p.isPrime.ne_top (Ideal.dvd_iff_le.mp hpq))
    subst q
    exact B.outside p (Finset.mem_filter.mp hq).1⟩

abbrev primitiveModulus (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) : OS :=
  D.generator (primitiveExterior K S B t)

theorem primitiveModulus_ne_zero (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) : primitiveModulus K S D B t ≠ 0 :=
  D.generator_ne_zero _

theorem primitiveModulus_span (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    Ideal.span ({primitiveModulus K S D B t} : Set OS) =
      (primitiveIdeal B.support t).map (algebraMap (𝓞 K) OS) :=
  D.generator_span _

theorem primitiveModulus_norm (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    (sIntegerElementNorm K Sset
      ⟨primitiveModulus K S D B t, primitiveModulus_ne_zero K S D B t⟩).val =
      ((primitiveIdeal B.support t).absNorm : ℝ) := by
  rw [← natCard_sIntegerPrincipalResidue_eq_productNorm K Sset,
    natCard_sIntegerPrincipalResidue K Sset _ (primitiveModulus_ne_zero K S D B t)]
  have hc : sIntegerModulusContraction K Sset (primitiveModulus K S D B t) =
      primitiveIdeal B.support t := by
    unfold sIntegerModulusContraction
    rw [primitiveModulus_span]
    exact under_map_coprime_sIntegerIdeal K Sset _
      (sexticIdeal_coprime_S K Sset _ (primitiveExterior K S B t).property)
  rw [hc]

def activePrime (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (p : B.support) (hp : t p.val ≠ 0) :
    idealPrimeDivisors K (primitiveIdeal B.support t) :=
  ⟨p.val, Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal)
    (Finset.mem_filter.mpr ⟨p.property, hp⟩)⟩

/-- An actual finite-prime product on the primitive quotient.  The branch
outside the active support is one, rather than a zero-extended principal
character inserted at every residue. -/
def primitiveQuotientFunction (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (q : ThetaQuotient K Sset (primitiveExterior K S B t)) : ℂ :=
  ∏ p : B.support, if hp : t p.val ≠ 0 then
    (sexticResidueCharacter K D.root6 D.primitive6 D.embedding p.val
      (B.awaySix p.val p.property) ^ (t p.val).val)
      (sexticIdealPrimeQuotientMap K Sset (primitiveIdeal B.support t)
        (primitiveExterior K S B t).property (activePrime K S B t p hp) q)
    else 1

theorem primitiveQuotientFunction_mk (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (a : OS) :
    primitiveQuotientFunction K S D B t (Ideal.Quotient.mk _ a) =
      ∏ p ∈ Finset.univ.filter (fun p : B.support => t p.val ≠ 0),
        (sexticResidueCharacter K D.root6 D.primitive6 D.embedding p.val
          (B.awaySix p.val p.property) ^ (t p.val).val)
          (sIntegerSexticResidueMap K Sset p.val (B.outside p.val p.property) a) := by
  rw [Finset.prod_filter]
  unfold primitiveQuotientFunction
  apply Finset.prod_congr rfl
  intro p _hp
  by_cases ht : t p.val ≠ 0
  · rw [dif_pos ht, if_pos ht, sexticIdealPrimeQuotientMap_mk] <;> rfl
  · rw [dif_neg ht, if_neg ht]

/-- Transport only across the proved equation span(c)=primitiveIdeal.map. -/
def primitiveCoefficient (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (q : OS ⧸ Ideal.span ({primitiveModulus K S D B t} : Set OS)) : ℂ :=
  primitiveQuotientFunction K S D B t
    (Ideal.quotEquivOfEq (D.generator_span (primitiveExterior K S B t)) q)

@[simp] theorem primitiveCoefficient_mk (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (a : OS) :
    primitiveCoefficient K S D B t (Ideal.Quotient.mk _ a) =
      ∏ p ∈ Finset.univ.filter (fun p : B.support => t p.val ≠ 0),
        (sexticResidueCharacter K D.root6 D.primitive6 D.embedding p.val
          (B.awaySix p.val p.property) ^ (t p.val).val)
          (sIntegerSexticResidueMap K Sset p.val (B.outside p.val p.property) a) := by
  unfold primitiveCoefficient
  rw [Ideal.quotEquivOfEq_mk]
  exact primitiveQuotientFunction_mk K S D B t a

variable (Γ : Subgroup (((S : Set (HeightOneSpectrum (𝓞 K)))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 : ((S : Set (HeightOneSpectrum (𝓞 K)))).unit K →* ((S : Set (HeightOneSpectrum (𝓞 K)))).unit K).range)

include hΓ in
theorem primitiveCoefficient_invariant (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (u : Γ) (a : OS) :
    primitiveCoefficient K S D B t
        (Ideal.Quotient.mk _ (((Sset).unitEquivUnitsInteger K u.val).val * a)) =
      primitiveCoefficient K S D B t (Ideal.Quotient.mk _ a) := by
  rw [primitiveCoefficient_mk, primitiveCoefficient_mk]
  apply Finset.prod_congr rfl
  intro p hp
  have hval : (t p.val).val ≠ 0 :=
    (ZMod.val_ne_zero _).mpr (Finset.mem_filter.mp hp).2
  rw [MulChar.pow_apply' _ hval, MulChar.pow_apply' _ hval]
  simpa only [sIntegerSexticEvaluation] using
    congrArg (fun z : ℂ => z ^ (t p.val).val)
      (sIntegerSexticEvaluation_literal_invariant K Sset p.val
        (B.outside p.val p.property) D.root6 D.primitive6 D.embedding
        (B.awaySix p.val p.property) Γ hΓ u a)

def principalMask (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) : Finset (HeightOneSpectrum OS) :=
  LocalizedMasks.localizeSupportedMask K Sset (principalSupport B.support t)
    (fun p hp => B.outside p (Finset.mem_filter.mp hp).1)

theorem principalMask_mk (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (a : NonzeroRingElements OS) :
    sIntegerOrbitAvoidanceMask K Sset Γ (principalMask K S B t) (Quotient.mk _ a) =
      if ∃ p : B.support, t p.val = 0 ∧
        sIntegerSexticResidueMap K Sset p.val (B.outside p.val p.property) a.val = 0
      then 0 else 1 := by
  rw [principalMask, LocalizedMasks.avoidanceMask_localizeSupported_mk]
  by_cases hbad : ∃ p : B.support, t p.val = 0 ∧
    sIntegerSexticResidueMap K Sset p.val (B.outside p.val p.property) a.val = 0
  · rw [if_pos hbad, if_neg]
    intro hgood
    obtain ⟨p, ht, hz⟩ := hbad
    exact hgood p.val (Finset.mem_filter.mpr ⟨p.property, ht⟩)
      ((sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction K Sset p.val
        (B.outside p.val p.property) a.val).mp hz)
  · rw [if_neg hbad, if_pos]
    intro p hp hd
    obtain ⟨hpB, ht⟩ := Finset.mem_filter.mp hp
    exact hbad ⟨⟨p, hpB⟩, ht,
      (sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction K Sset p
        (B.outside p hpB) a.val).mpr hd⟩

/-- The primitive block carries the union of the old mask and the exact
principal-digit mask; its periodic coefficient has only active factors. -/
def block (B : PrimeBlock K Sset) (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) :
    ActualMaskedPoissonBlock K S Γ where
  modulus := primitiveModulus K S D B t
  modulus_ne_zero := primitiveModulus_ne_zero K S D B t
  profile := φ
  localTest := h
  localTest_locallyConstant := hlc
  localTest_compactSupport := hcs
  mask := M ∪ principalMask K S B t
  coefficient := primitiveCoefficient K S D B t
  invariant := primitiveCoefficient_invariant K S D Γ hΓ B t
  radius := r

theorem pair_outside (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset)
    (p : HeightOneSpectrum (𝓞 K))
    (hp : p.asIdeal ∣ b₁.val.val ∨ p.asIdeal ∣ b₂.val.val ∨
      p.asIdeal ∣ n₁.val.val ∨ p.asIdeal ∣ n₂.val.val) : p ∉ Sset := by
  rcases hp with hp | hp | hp | hp
  · exact b₁.property p hp
  · exact b₂.property p hp
  · exact n₁.property p hp
  · exact n₂.property p hp

def pairSupport (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset) : PrimeBlock K Sset :=
  PrimeBlock.ofFour K Sset b₁.val.val b₂.val.val n₁.val.val n₂.val.val
    (nonZeroDivisors.coe_ne_zero b₁.val) (nonZeroDivisors.coe_ne_zero b₂.val)
    (nonZeroDivisors.coe_ne_zero n₁.val) (nonZeroDivisors.coe_ne_zero n₂.val)
    (pair_outside K S n₁ n₂ b₁ b₂)
    (fun p hp => D.away_six p (pair_outside K S n₁ n₂ b₁ b₂ p hp))

theorem mem_pairSupport (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset)
    (p : HeightOneSpectrum (𝓞 K)) :
    p ∈ (pairSupport K S D n₁ n₂ b₁ b₂).support ↔
      p.asIdeal ∣ b₁.val.val ∨ p.asIdeal ∣ b₂.val.val ∨
        p.asIdeal ∣ n₁.val.val ∨ p.asIdeal ∣ n₂.val.val := by
  simp only [pairSupport, PrimeBlock.ofFour, Finset.mem_union,
    Set.Finite.mem_toFinset, mem_idealPrimeDivisors]

/-- The actual local conductor digit, on all ordinary primes. -/
def pairExponent (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset)
    (p : HeightOneSpectrum (𝓞 K)) : ZMod 6 :=
  CubeAlgebra.conductorExponent
    (CubeAlgebra.parity
      (idealPrimeMultiplicity K p b₁.val.val + idealPrimeMultiplicity K p b₂.val.val))
    (decide (p.asIdeal ∣ n₁.val.val)) (decide (p.asIdeal ∣ n₂.val.val))

/-- The source coefficient equals its exact principal mask times the
genuine function on the active quotient.  The support, multiplicity bits,
and positivity inputs are all discharged for the four actual ideals. -/
theorem pair_source_factorization (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset)
    (hn₁ : Squarefree n₁.val.val) (hn₂ : Squarefree n₂.val.val)
    (a : NonzeroRingElements OS) :
    CanonicalPoissonSource.pairCoefficient K S D n₁ n₂ b₁ b₂
        (Ideal.Quotient.mk _ a.val) =
      sIntegerOrbitAvoidanceMask K Sset Γ
          (principalMask K S (pairSupport K S D n₁ n₂ b₁ b₂)
            (pairExponent K S n₁ n₂ b₁ b₂)) (Quotient.mk _ a) *
        primitiveCoefficient K S D (pairSupport K S D n₁ n₂ b₁ b₂)
          (pairExponent K S n₁ n₂ b₁ b₂) (Ideal.Quotient.mk _ a.val) := by
  let B := pairSupport K S D n₁ n₂ b₁ b₂
  have hcb₁ : PrimeBlock.Covers K Sset B b₁.val.val := by
    intro p hp
    exact (mem_pairSupport K S D n₁ n₂ b₁ b₂ p).mpr (Or.inl hp)
  have hcb₂ : PrimeBlock.Covers K Sset B b₂.val.val := by
    intro p hp
    exact (mem_pairSupport K S D n₁ n₂ b₁ b₂ p).mpr (Or.inr (Or.inl hp))
  have hcn₁ : PrimeBlock.Covers K Sset B n₁.val.val := by
    intro p hp
    exact (mem_pairSupport K S D n₁ n₂ b₁ b₂ p).mpr (Or.inr (Or.inr (Or.inl hp)))
  have hcn₂ : PrimeBlock.Covers K Sset B n₂.val.val := by
    intro p hp
    exact (mem_pairSupport K S D n₁ n₂ b₁ b₂ p).mpr (Or.inr (Or.inr (Or.inr hp)))
  have hs := PrimeBlock.actual_pair_source_split K Sset D.root6 D.primitive6 D.embedding
    B b₁.val.val b₂.val.val n₁.val.val n₂.val.val
    (nonZeroDivisors.coe_ne_zero b₁.val) (nonZeroDivisors.coe_ne_zero b₂.val)
    (nonZeroDivisors.coe_ne_zero n₁.val) (nonZeroDivisors.coe_ne_zero n₂.val)
    hcb₁ hcb₂ hcn₁ hcn₂
    (fun p => decide (p.val.asIdeal ∣ n₁.val.val))
    (fun p => decide (p.val.asIdeal ∣ n₂.val.val))
    (fun p => squarefree_prime_multiplicity K n₁.val.val
      (nonZeroDivisors.coe_ne_zero n₁.val) hn₁ p.val)
    (fun p => squarefree_prime_multiplicity K n₂.val.val
      (nonZeroDivisors.coe_ne_zero n₂.val) hn₂ p.val)
    (fun p => supported_prime_positive K b₁.val.val b₂.val.val n₁.val.val n₂.val.val
      (nonZeroDivisors.coe_ne_zero b₁.val) (nonZeroDivisors.coe_ne_zero b₂.val) p.val
      ((mem_pairSupport K S D n₁ n₂ b₁ b₂ p.val).mp p.property)) a.val
  rw [CanonicalPoissonSource.pairCoefficient_mk_cubeNumerator,
    principalMask_mk, primitiveCoefficient_mk]
  dsimp only [B, PrimeBlock.idealRow, idealSymbol, pairExponent, Complex.star_def] at hs ⊢
  convert hs using 1 <;> rfl

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
  [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

/-- The full-period canonical pair and the active-conductor pair are the
same actual orbital series.  Principal zeros move into the mask before
Poisson, including when they overlap the existing external mask. -/
theorem canonical_pair_physical_eq_primitive
    (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset)
    (hn₁ : Squarefree n₁.val.val) (hn₂ : Squarefree n₂.val.val)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) :
    (CanonicalPoissonSource.block K S D Γ hΓ n₁ n₂ b₁ b₂ φ h hlc hcs M r).physical =
      (block K S D Γ hΓ (pairSupport K S D n₁ n₂ b₁ b₂)
        (pairExponent K S n₁ n₂ b₁ b₂) φ h hlc hcs M r).physical := by
  unfold ActualMaskedPoissonBlock.physical
  apply congrArg (sIntegerWeightedOrbitalSeries K S Γ φ (sIntegerFiniteTestFunction K S h) r)
  funext q
  simp only [CanonicalPoissonSource.block, block]
  rw [LocalizedMasks.avoidanceMask_union]
  refine Quotient.inductionOn q ?_
  intro a
  rw [sIntegerPeriodicOrbitWeight_mk, sIntegerPeriodicOrbitWeight_mk,
    pair_source_factorization K S D Γ n₁ n₂ b₁ b₂ hn₁ hn₂ a]
  ring

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- Genuine first Poisson on the exact active conductor with its exact
complementary principal mask.  Both additive zero terms are retained.
Evaluating the finite transform by CRT Gauss sums is a further statement. -/
theorem canonical_pair_primitive_poisson
    (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset)
    (hn₁ : Squarefree n₁.val.val) (hn₂ : Squarefree n₂.val.val)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) :
    (CanonicalPoissonSource.block K S D Γ hΓ n₁ n₂ b₁ b₂ φ h hlc hcs M r).physical =
      (block K S D Γ hΓ (pairSupport K S D n₁ n₂ b₁ b₂)
        (pairExponent K S n₁ n₂ b₁ b₂) φ h hlc hcs M r).transformed
          μv D.different_outside := by
  rw [canonical_pair_physical_eq_primitive K S D Γ hΓ n₁ n₂ b₁ b₂
    hn₁ hn₂ φ h hlc hcs M r,
    ActualMaskedPoissonBlock.physical_eq_transformed μv D.different_outside ν μ]

include ν μ in
/-- The whole finite canonical squared row, transformed on each pair's
exact active conductor with every complementary zero mask preserved. -/
theorem squaredRowOrbitalSeries_primitive_poisson {ι : Type*} (T : Finset ι)
    (n b : ι → ExteriorIdeal K Sset) (A : ι → ℂ)
    (hn : ∀ i ∈ T, Squarefree (n i).val.val)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) :
    CanonicalPoissonSource.squaredRowOrbitalSeries K S D Γ T n b A φ h M r =
      ∑ p ∈ T ×ˢ T, A p.1 * conj (A p.2) *
        (block K S D Γ hΓ (pairSupport K S D (n p.1) (n p.2) (b p.1) (b p.2))
          (pairExponent K S (n p.1) (n p.2) (b p.1) (b p.2))
          φ h hlc hcs M r).transformed μv D.different_outside := by
  rw [CanonicalPoissonSource.squaredRowOrbitalSeries_eq_pair_sum
    K S D Γ hΓ T n b A φ h hlc hcs M r]
  apply Finset.sum_congr rfl
  intro p hp
  rw [canonical_pair_primitive_poisson K S D Γ hΓ μv ν μ
    (n p.1) (n p.2) (b p.1) (b p.2)
    (hn p.1 (Finset.mem_product.mp hp).1) (hn p.2 (Finset.mem_product.mp hp).2)
    φ h hlc hcs M r]

include ν μ in
/-- The genuine inverse-column square has the corresponding primitive
Poisson formula, with the required opposite coefficient conjugations. -/
theorem inverseSquaredRowOrbitalSeries_primitive_poisson {ι : Type*} (T : Finset ι)
    (n b : ι → ExteriorIdeal K Sset) (A : ι → ℂ)
    (hn : ∀ i ∈ T, Squarefree (n i).val.val)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) :
    CanonicalPoissonSource.inverseSquaredRowOrbitalSeries K S D Γ T n b A φ h M r =
      ∑ p ∈ T ×ˢ T, conj (A p.1) * A p.2 *
        (block K S D Γ hΓ (pairSupport K S D (n p.1) (n p.2) (b p.1) (b p.2))
          (pairExponent K S (n p.1) (n p.2) (b p.1) (b p.2))
          φ h hlc hcs M r).transformed μv D.different_outside := by
  rw [CanonicalPoissonSource.inverseSquaredRowOrbitalSeries_eq]
  simpa only [Complex.conj_conj] using
    squaredRowOrbitalSeries_primitive_poisson K S D Γ hΓ μv ν μ T n b
      (fun i => conj (A i)) hn φ h hlc hcs M r

end HeckeSkeleton.Moments.MOM_INV_STEP.PrimitivePoissonSource
