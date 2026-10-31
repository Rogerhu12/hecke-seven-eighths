import HeckeSkeleton.Moments.MOM_INV_STEP.PoissonStep
import HeckeGeneral.Analysis.GlobalThetaData

/-!
# The actual canonical and inverse row sources

The first Poisson input in the canonical inverse step is the coefficient
obtained by expanding the square of `chi_b(k)^3 * chi_n(k)`.  Here `chi`
is the repository's genuine finite-prime product `idealSymbol`, including
its values at bad primes and at zero.  We construct its function on a
finite S-integer quotient and prove literal subgroup invariance; neither
periodicity nor a Poisson identity is assumed.  Absolute orbital summability
justifies expanding the whole finite squared row before its Poisson
transformation.  The conjugated inverse row is treated with its exact
opposite coefficient conjugations.

The product modulus below is a full period.  This file does not claim that
it is the primitive conductor `u₁ u₂ R₁`.  The reduction to that conductor,
its complementary zero mask, and the inverse-column Gauss calibration are
separate obligations.  Keeping this distinction also retains all zero
frequencies of the actual full-modulus Fourier transform.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalPoissonSource

open NumberField IsDedekindDomain
  HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton
  HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => (Sset).integer K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Ext" => ExteriorIdeal K Sset
variable (D : ThetaArithmeticData K Sset)

theorem idealSymbol_mul (I : Ext) (a b : OS) :
    idealSymbol K Sset D I (a * b) =
      idealSymbol K Sset D I a * idealSymbol K Sset D I b :=
  sIntegerSexticIdealEvaluation_mul K Sset D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) a b

theorem idealSymbol_pow (I : Ext) (a : OS) (j : ℕ) :
    idealSymbol K Sset D I (a ^ j) = idealSymbol K Sset D I a ^ j := by
  induction j with
  | zero => simp only [pow_zero, idealSymbol, sIntegerSexticIdealEvaluation_one]
  | succ j ih => rw [pow_succ, idealSymbol_mul, ih, pow_succ]

/-- The actual ideal residue function pulled back to any known full period. -/
def idealSymbolOnQuotient (I : Ext) (c : OS) (hdiv : D.generator I ∣ c)
    (q : OS ⧸ Ideal.span ({c} : Set OS)) : ℂ :=
  sIntegerSexticIdealQuotientFunction K Sset D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp))
    (Ideal.quotientMap (I.val.val.map (algebraMap (𝓞 K) OS))
      (RingHom.id OS) (by
        rw [Ideal.comap_id, ← D.generator_span I]
        exact Ideal.span_singleton_le_span_singleton.mpr hdiv) q)

@[simp] theorem idealSymbolOnQuotient_mk
    (I : Ext) (c : OS) (hdiv : D.generator I ∣ c) (a : OS) :
    idealSymbolOnQuotient K S D I c hdiv (Ideal.Quotient.mk _ a) =
      idealSymbol K Sset D I a := by
  simp only [idealSymbolOnQuotient, Ideal.quotientMap_mk, RingHom.id_apply,
    sIntegerSexticIdealQuotientFunction_mk, idealSymbol]

/-- A full period of the squared row factor.  Repeated or shared primes
are allowed, and no cancellation of their zero masks is performed. -/
def pairModulus (n₁ n₂ b₁ b₂ : Ext) : OS :=
  (D.generator n₁ * D.generator b₁) * (D.generator n₂ * D.generator b₂)

theorem pairModulus_ne_zero (n₁ n₂ b₁ b₂ : Ext) :
    pairModulus K S D n₁ n₂ b₁ b₂ ≠ 0 :=
  mul_ne_zero (mul_ne_zero (D.generator_ne_zero n₁) (D.generator_ne_zero b₁))
    (mul_ne_zero (D.generator_ne_zero n₂) (D.generator_ne_zero b₂))

/-- The full period generates exactly the localized product ideal. -/
theorem pairModulus_span (n₁ n₂ b₁ b₂ : Ext) :
    Ideal.span ({pairModulus K S D n₁ n₂ b₁ b₂} : Set OS) =
      ((n₁.val.val * b₁.val.val) * (n₂.val.val * b₂.val.val)).map
        (algebraMap (𝓞 K) OS) := by
  simp only [pairModulus, ← Ideal.span_singleton_mul_span_singleton,
    D.generator_span, Ideal.map_mul]

/-- Contracting the genuine modulus loses no exterior ideal factor. -/
theorem pairModulus_contraction (n₁ n₂ b₁ b₂ : Ext) :
    sIntegerModulusContraction K Sset (pairModulus K S D n₁ n₂ b₁ b₂) =
      (n₁.val.val * b₁.val.val) * (n₂.val.val * b₂.val.val) := by
  let I := exteriorMul K Sset (exteriorMul K Sset n₁ b₁) (exteriorMul K Sset n₂ b₂)
  unfold sIntegerModulusContraction
  rw [pairModulus_span]
  exact under_map_coprime_sIntegerIdeal K Sset I.val.val
    (sexticIdeal_coprime_S K Sset I.val.val I.property)

/-- The actual finite quotient cardinal is the ideal norm of the full period. -/
theorem natCard_pairQuotient (n₁ n₂ b₁ b₂ : Ext) :
    Nat.card (OS ⧸ Ideal.span ({pairModulus K S D n₁ n₂ b₁ b₂} : Set OS)) =
      ((n₁.val.val * b₁.val.val) * (n₂.val.val * b₂.val.val)).absNorm := by
  rw [natCard_sIntegerPrincipalResidue K Sset _ (pairModulus_ne_zero K S D n₁ n₂ b₁ b₂),
    pairModulus_contraction]

/-- The radius normalization uses the actual S-local modulus norm, proved
equal to the full ideal product norm rather than postulated as a scalar law. -/
theorem pairModulus_norm (n₁ n₂ b₁ b₂ : Ext) :
    (sIntegerElementNorm K Sset
      ⟨pairModulus K S D n₁ n₂ b₁ b₂, pairModulus_ne_zero K S D n₁ n₂ b₁ b₂⟩).val =
      ((n₁.val.val.absNorm : ℝ) * b₁.val.val.absNorm) *
        ((n₂.val.val.absNorm : ℝ) * b₂.val.val.absNorm) := by
  rw [← natCard_sIntegerPrincipalResidue_eq_productNorm K Sset,
    natCard_pairQuotient]
  simp only [map_mul, Nat.cast_mul]

theorem generator_n₁_dvd_pairModulus (n₁ n₂ b₁ b₂ : Ext) :
    D.generator n₁ ∣ pairModulus K S D n₁ n₂ b₁ b₂ := by
  refine ⟨D.generator b₁ * (D.generator n₂ * D.generator b₂), ?_⟩
  simp only [pairModulus, mul_assoc]

theorem generator_n₂_dvd_pairModulus (n₁ n₂ b₁ b₂ : Ext) :
    D.generator n₂ ∣ pairModulus K S D n₁ n₂ b₁ b₂ := by
  refine ⟨(D.generator n₁ * D.generator b₁) * D.generator b₂, ?_⟩
  unfold pairModulus
  ring

theorem generator_b₁_dvd_pairModulus (n₁ n₂ b₁ b₂ : Ext) :
    D.generator b₁ ∣ pairModulus K S D n₁ n₂ b₁ b₂ := by
  refine ⟨D.generator n₁ * (D.generator n₂ * D.generator b₂), ?_⟩
  unfold pairModulus
  ring

theorem generator_b₂_dvd_pairModulus (n₁ n₂ b₁ b₂ : Ext) :
    D.generator b₂ ∣ pairModulus K S D n₁ n₂ b₁ b₂ := by
  refine ⟨(D.generator n₁ * D.generator b₁) * D.generator n₂, ?_⟩
  unfold pairModulus
  ring

/-- The literal coefficient of one pair after expanding the canonical
cube-completed row.  Conjugation acts on the entire second row factor. -/
def pairCoefficient (n₁ n₂ b₁ b₂ : Ext)
    (q : OS ⧸ Ideal.span ({pairModulus K S D n₁ n₂ b₁ b₂} : Set OS)) : ℂ :=
  (idealSymbolOnQuotient K S D b₁ _
      (generator_b₁_dvd_pairModulus K S D n₁ n₂ b₁ b₂) q ^ 3 *
    idealSymbolOnQuotient K S D n₁ _
      (generator_n₁_dvd_pairModulus K S D n₁ n₂ b₁ b₂) q) *
  conj (idealSymbolOnQuotient K S D b₂ _
      (generator_b₂_dvd_pairModulus K S D n₁ n₂ b₁ b₂) q ^ 3 *
    idealSymbolOnQuotient K S D n₂ _
      (generator_n₂_dvd_pairModulus K S D n₁ n₂ b₁ b₂) q)

@[simp] theorem pairCoefficient_mk (n₁ n₂ b₁ b₂ : Ext) (a : OS) :
    pairCoefficient K S D n₁ n₂ b₁ b₂ (Ideal.Quotient.mk _ a) =
      (idealSymbol K Sset D b₁ a ^ 3 * idealSymbol K Sset D n₁ a) *
        conj (idealSymbol K Sset D b₂ a ^ 3 * idealSymbol K Sset D n₂ a) := by
  simp only [pairCoefficient, idealSymbolOnQuotient_mk]

/-- Compatibility with the literal cubed-numerator source used in the
actual finite-prime conductor-digit calculation. -/
theorem pairCoefficient_mk_cubeNumerator (n₁ n₂ b₁ b₂ : Ext) (a : OS) :
    pairCoefficient K S D n₁ n₂ b₁ b₂ (Ideal.Quotient.mk _ a) =
      (idealSymbol K Sset D b₁ (a ^ 3) * idealSymbol K Sset D n₁ a) *
        conj (idealSymbol K Sset D b₂ (a ^ 3) * idealSymbol K Sset D n₂ a) := by
  simp only [pairCoefficient_mk, idealSymbol_pow]

/-- The finite square expansion uses the actual pair coefficient on every
numerator.  Column coefficients may include all frozen labels, backgrounds,
punctures and independently chosen marks. -/
theorem row_mul_conj_expansion {ι : Type*} (T : Finset ι)
    (n b : ι → Ext) (A : ι → ℂ) (a : OS) :
    (∑ i ∈ T, A i *
        (idealSymbol K Sset D (b i) a ^ 3 * idealSymbol K Sset D (n i) a)) *
      conj (∑ j ∈ T, A j *
        (idealSymbol K Sset D (b j) a ^ 3 * idealSymbol K Sset D (n j) a)) =
    ∑ i ∈ T, ∑ j ∈ T, A i * conj (A j) *
      pairCoefficient K S D (n i) (n j) (b i) (b j) (Ideal.Quotient.mk _ a) := by
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [map_mul, pairCoefficient_mk]
  ring

/-- The same identity in the normalization used by a second moment. -/
theorem row_norm_sq_expansion {ι : Type*} (T : Finset ι)
    (n b : ι → Ext) (A : ι → ℂ) (a : OS) :
    ((‖∑ i ∈ T, A i *
        (idealSymbol K Sset D (b i) a ^ 3 * idealSymbol K Sset D (n i) a)‖ ^ 2 : ℝ) : ℂ) =
    ∑ i ∈ T, ∑ j ∈ T, A i * conj (A j) *
      pairCoefficient K S D (n i) (n j) (b i) (b j) (Ideal.Quotient.mk _ a) := by
  simpa only [RCLike.mul_conj, ← Complex.ofReal_pow] using
    row_mul_conj_expansion K S D T n b A a

/-- A nonunit denominator has an actual bad prime at the zero numerator. -/
theorem idealSymbol_zero_of_ne_top (I : Ext) (hI : I.val.val ≠ ⊤) :
    idealSymbol K Sset D I 0 = 0 := by
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I.val.val hI
  have hP0 : P ≠ ⊥ := by
    intro hzero
    exact nonZeroDivisors.coe_ne_zero I.val (le_bot_iff.mp (hzero ▸ hIP))
  let p : HeightOneSpectrum (𝓞 K) := ⟨P, hP.isPrime, hP0⟩
  have hp : p.asIdeal ∣ I.val.val := Ideal.dvd_iff_le.mpr hIP
  exact sIntegerSexticIdealEvaluation_eq_zero_of_badPrime K Sset
    D.root6 D.primitive6 D.embedding I.val.val
    (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun q hq => D.away_six q (I.property q hq)) 0 p hp (map_zero _)

/-- The primal zero term really vanishes if any one of the four denominator
ideals is nontrivial.  This says nothing about the dual zero coefficient. -/
theorem pairCoefficient_zero_of_nontrivial
    (n₁ n₂ b₁ b₂ : Ext)
    (h : n₁.val.val ≠ ⊤ ∨ n₂.val.val ≠ ⊤ ∨ b₁.val.val ≠ ⊤ ∨ b₂.val.val ≠ ⊤) :
    pairCoefficient K S D n₁ n₂ b₁ b₂ 0 = 0 := by
  change pairCoefficient K S D n₁ n₂ b₁ b₂ (Ideal.Quotient.mk _ 0) = 0
  rw [pairCoefficient_mk]
  rcases h with hn₁ | hn₂ | hb₁ | hb₂
  · rw [idealSymbol_zero_of_ne_top K S D n₁ hn₁]
    simp
  · rw [idealSymbol_zero_of_ne_top K S D n₂ hn₂]
    simp
  · rw [idealSymbol_zero_of_ne_top K S D b₁ hb₁]
    simp
  · rw [idealSymbol_zero_of_ne_top K S D b₂ hb₂]
    simp

variable (Γ : Subgroup ((Sset).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 : (Sset).unit K →* (Sset).unit K).range)

include hΓ in
theorem idealSymbol_literal_invariant (I : Ext) (u : Γ) (a : OS) :
    idealSymbol K Sset D I (((Sset).unitEquivUnitsInteger K u.val).val * a) =
      idealSymbol K Sset D I a := by
  exact sIntegerSexticIdealEvaluation_literal_invariant K Sset
    D.root6 D.primitive6 D.embedding I.val.val
    (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) Γ hΓ u a

include hΓ in
theorem pairCoefficient_literal_invariant
    (n₁ n₂ b₁ b₂ : Ext) (u : Γ) (a : OS) :
    pairCoefficient K S D n₁ n₂ b₁ b₂
        (Ideal.Quotient.mk _ (((Sset).unitEquivUnitsInteger K u.val).val * a)) =
      pairCoefficient K S D n₁ n₂ b₁ b₂ (Ideal.Quotient.mk _ a) := by
  simp only [pairCoefficient_mk, idealSymbol_literal_invariant K S D Γ hΓ]

/-- Evaluation on an orbit agrees with the literal row factor at its chosen
representative.  The already proved invariance makes that representative
irrelevant to the value. -/
theorem pairOrbitWeight_eq (n₁ n₂ b₁ b₂ : Ext)
    (q : SIntegerOrbits K Sset Γ) :
    sIntegerPeriodicOrbitWeight K Sset Γ (pairModulus K S D n₁ n₂ b₁ b₂)
        (pairCoefficient K S D n₁ n₂ b₁ b₂)
        (pairCoefficient_literal_invariant K S D Γ hΓ n₁ n₂ b₁ b₂) q =
      (idealSymbol K Sset D b₁ q.out.val ^ 3 * idealSymbol K Sset D n₁ q.out.val) *
        conj (idealSymbol K Sset D b₂ q.out.val ^ 3 * idealSymbol K Sset D n₂ q.out.val) := by
  have he := sIntegerPeriodicOrbitWeight_mk K Sset Γ
    (pairModulus K S D n₁ n₂ b₁ b₂) (pairCoefficient K S D n₁ n₂ b₁ b₂)
    (pairCoefficient_literal_invariant K S D Γ hΓ n₁ n₂ b₁ b₂) q.out
  rw [Quotient.out_eq] at he
  exact he.trans (pairCoefficient_mk K S D n₁ n₂ b₁ b₂ q.out.val)

/-- A genuine masked Poisson packet for the literal first squared row.
Its invariance is proved from sixth-power residue invariance. -/
def block (n₁ n₂ b₁ b₂ : Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) :
    ActualMaskedPoissonBlock K S Γ where
  modulus := pairModulus K S D n₁ n₂ b₁ b₂
  modulus_ne_zero := pairModulus_ne_zero K S D n₁ n₂ b₁ b₂
  profile := φ
  localTest := h
  localTest_locallyConstant := hlc
  localTest_compactSupport := hcs
  mask := M
  coefficient := pairCoefficient K S D n₁ n₂ b₁ b₂
  invariant := pairCoefficient_literal_invariant K S D Γ hΓ n₁ n₂ b₁ b₂
  radius := r

variable [MeasurableSpace (sLocalNormOneGroup K Sset)]
  [BorelSpace (sLocalNormOneGroup K Sset)] [Γ.FiniteIndex]
  [IsPrincipalIdealRing OS]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

/-- The genuine orbital series of the squared finite canonical row.  The
column scalar `A` may include all row-independent data of a frozen block. -/
def squaredRowOrbitalSeries {ι : Type*} (T : Finset ι)
    (n b : ι → Ext) (A : ι → ℂ) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) : ℂ :=
  sIntegerWeightedOrbitalSeries K S Γ φ (sIntegerFiniteTestFunction K S h) r
    (fun q => sIntegerOrbitAvoidanceMask K Sset Γ M q *
      ((‖∑ i ∈ T, A i *
        (idealSymbol K Sset D (b i) q.out.val ^ 3 *
          idealSymbol K Sset D (n i) q.out.val)‖ ^ 2 : ℝ) : ℂ))

/-- Expanding the square and exchanging its finite sums with the infinite
orbit sum is justified by absolute summability of every actual pair. -/
theorem squaredRowOrbitalSeries_eq_pair_sum {ι : Type*} (T : Finset ι)
    (n b : ι → Ext) (A : ι → ℂ) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) :
    squaredRowOrbitalSeries K S D Γ T n b A φ h M r =
      ∑ p ∈ T ×ˢ T, A p.1 * conj (A p.2) *
        (block K S D Γ hΓ (n p.1) (n p.2) (b p.1) (b p.2)
          φ h hlc hcs M r).physical := by
  rw [ActualMaskedPoissonBlock.finite_weighted_physical_eq_tsum]
  unfold squaredRowOrbitalSeries sIntegerWeightedOrbitalSeries
  apply tsum_congr
  intro q
  rw [row_norm_sq_expansion]
  simp only [Finset.sum_product, ActualMaskedPoissonBlock.orbitalTerm, block,
    pairOrbitWeight_eq, pairCoefficient_mk]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

include ν μ in
/-- First Poisson for the whole finite cube-completed canonical row.  This
starts from its literal squared orbital series, proves finite interchange,
and transforms every pair on its own genuine modulus with all zero modes. -/
theorem squaredRowOrbitalSeries_poisson {ι : Type*} (T : Finset ι)
    (n b : ι → Ext) (A : ι → ℂ) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) :
    squaredRowOrbitalSeries K S D Γ T n b A φ h M r =
      ∑ p ∈ T ×ˢ T, A p.1 * conj (A p.2) *
        (block K S D Γ hΓ (n p.1) (n p.2) (b p.1) (b p.2)
          φ h hlc hcs M r).transformed μv D.different_outside := by
  rw [squaredRowOrbitalSeries_eq_pair_sum K S D Γ hΓ T n b A φ h hlc hcs M r,
    ActualMaskedPoissonBlock.finite_physical_eq_transformed μv D.different_outside ν μ]

/-- The literal conjugated row occurring in an inverse-column norm.  No
relation between this source and the first Fourier family is assumed here. -/
def inverseSquaredRowOrbitalSeries {ι : Type*} (T : Finset ι)
    (n b : ι → Ext) (A : ι → ℂ) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) : ℂ :=
  sIntegerWeightedOrbitalSeries K S Γ φ (sIntegerFiniteTestFunction K S h) r
    (fun q => sIntegerOrbitAvoidanceMask K Sset Γ M q *
      ((‖∑ i ∈ T, A i * conj
        (idealSymbol K Sset D (b i) q.out.val ^ 3 *
          idealSymbol K Sset D (n i) q.out.val)‖ ^ 2 : ℝ) : ℂ))

theorem inverseSquaredRowOrbitalSeries_eq {ι : Type*} (T : Finset ι)
    (n b : ι → Ext) (A : ι → ℂ) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) :
    inverseSquaredRowOrbitalSeries K S D Γ T n b A φ h M r =
      squaredRowOrbitalSeries K S D Γ T n b (fun i => conj (A i)) φ h M r := by
  unfold inverseSquaredRowOrbitalSeries squaredRowOrbitalSeries
  congr 1
  funext q
  have he :
      (∑ i ∈ T, A i * conj
        (idealSymbol K Sset D (b i) q.out.val ^ 3 *
          idealSymbol K Sset D (n i) q.out.val)) =
      conj (∑ i ∈ T, conj (A i) *
        (idealSymbol K Sset D (b i) q.out.val ^ 3 *
          idealSymbol K Sset D (n i) q.out.val)) := by
    simp only [map_sum, map_mul, Complex.conj_conj]
  rw [he, Complex.norm_conj]

include ν μ in
/-- Genuine Poisson for an actual inverse-column norm, with its coefficient
conjugations in the opposite order and all finite Fourier zero terms kept.
Identifying this source after the first common-kernel/Cauchy step remains a
separate arithmetic and analytic obligation. -/
theorem inverseSquaredRowOrbitalSeries_poisson {ι : Type*} (T : Finset ι)
    (n b : ι → Ext) (A : ι → ℂ) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) :
    inverseSquaredRowOrbitalSeries K S D Γ T n b A φ h M r =
      ∑ p ∈ T ×ˢ T, conj (A p.1) * A p.2 *
        (block K S D Γ hΓ (n p.1) (n p.2) (b p.1) (b p.2)
          φ h hlc hcs M r).transformed μv D.different_outside := by
  rw [inverseSquaredRowOrbitalSeries_eq]
  simpa only [Complex.conj_conj] using
    squaredRowOrbitalSeries_poisson K S D Γ hΓ μv ν μ T n b
      (fun i => conj (A i)) φ h hlc hcs M r

include ν μ in
/-- The first actual row Poisson identity with no assumed periodicity,
coprimality simplification, or zero-frequency deletion.  The right side is
the explicit full-mask transform defined in `PoissonStep`. -/
theorem canonical_row_pair_poisson
    (n₁ n₂ b₁ b₂ : Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) :
    (block K S D Γ hΓ n₁ n₂ b₁ b₂ φ h hlc hcs M r).physical =
      (block K S D Γ hΓ n₁ n₂ b₁ b₂ φ h hlc hcs M r).transformed
        μv D.different_outside := by
  exact ActualMaskedPoissonBlock.physical_eq_transformed μv D.different_outside ν μ _

end HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalPoissonSource
