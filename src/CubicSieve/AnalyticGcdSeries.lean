import CubicSieve.AnalyticGcdGram
import CubicSieve.AnalyticSmoothingGaussian
import HeckeGeneral.Arithmetic.SIntegerOrbitDilation
import HeckeGeneral.Analysis.SIntegerWeightedOrbitalSum
import HeckeGeneral.Analysis.PrimeCalibrationIdealAssembly

/-!
Gcd and Möbius descent on the original infinite sixth-unit orbit space.
Each exchange of an infinite row sum with the finite divisor sums is
preceded by genuine absolute convergence. Divisor dilation enumerates all
divisible sectors of the same original subgroup. Its radius changes by the
actual exterior ideal norm; no finite-row identity is used as an infinite
identity.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.AnalyticGcdSeries

open NumberField IsDedekindDomain MeasureTheory UniqueFactorizationMonoid
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.PrimeCalibrationDraft
open AlgebraicNumberTheory.PowerResidueSymbols
open CubicSieve.ExteriorKernel CubicSieve.OrbitRows CubicSieve.OrbitKernel
open CubicSieve.AnalyticGcd CubicSieve.AnalyticSmoothing
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)
local instance gammaFiniteIndex : (Γ K S).FiniteIndex :=
  sUnit_power_range_finiteIndex K S 6 (by decide)
local notation "OS" => S.integer K
local notation "Q" => Orbits K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

private def primeValue (a : OS) (p : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if hp : p ∉ S then
    sIntegerSexticEvaluation K S p hp D.root6 D.primitive6 D.embedding
      (D.away_six p hp) a ^ (2 : ℕ) else 1

private theorem coefficient_idealCoefficient (I : ExteriorIdeal K S) (a : NonzeroRingElements OS) :
    coefficient K S D I (Quotient.mk _ a) = idealCoefficient (primeValue K S D a.val) I.val.val := by
  letI : Fintype (idealPrimeDivisors K I.val.val) :=
    (idealPrimeDivisors_finite K I.val.val (nonZeroDivisors.coe_ne_zero I.val)).fintype
  rw [coefficient_mk, idealCoefficient_eq_prod_idealPrimeDivisors K _ I.val]
  simp only [idealSymbol, sIntegerSexticIdealEvaluation]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p hp
  rw [primeValue, dite_eq_left (I.property p.val p.property)]
  simp only [← pow_mul, Nat.mul_comm]

/-- Multiplication in the column ideal is literal ideal-factor multiplicativity,
and is valid at arbitrary nonunit numerators in every original unit sector. -/
theorem coefficient_column_mul (q : Q) (I J : ExteriorIdeal K S) :
    coefficient K S D (exteriorMul K S I J) q =
      coefficient K S D I q * coefficient K S D J q := by
  refine Quotient.inductionOn q (fun a => ?_)
  rw [coefficient_idealCoefficient, coefficient_idealCoefficient,
    coefficient_idealCoefficient]
  exact idealCoefficient_mul _ _ _

def generator (e : ExteriorIdeal K S) : NonzeroRingElements OS :=
  ⟨D.generator e, D.generator_ne_zero e⟩

theorem coefficient_dilation (e I : ExteriorIdeal K S) (q : Q) :
    coefficient K S D I (sIntegerOrbitDilation K S (Γ K S) (generator K S D e) q) =
      positiveKernel K S D e I * coefficient K S D I q := by
  refine Quotient.inductionOn q (fun a => ?_)
  simp only [sIntegerOrbitDilation_mk, sIntegerNonzeroMul, coefficient_mk,
    generator, idealSymbol, sIntegerSexticIdealEvaluation_mul, mul_pow,
    positiveKernel, kernel, symbol, zpow_ofNat]

theorem generator_norm (e : ExteriorIdeal K S) :
    (sIntegerElementNorm K S (generator K S D e)).val = exteriorNorm K S e := by
  simpa only [generatorOrbit, scalarOrbit, map_one, one_smul, sIntegerOrbitNorm_mk,
    generator] using generatorOrbit_norm K S D e

theorem ideal_dvd_iff_orbitDivisible (e : ExteriorIdeal K S) (q : Q) :
    e.val.val ∣ (orbitIdeal K S q).val.val ↔
      sIntegerOrbitDivisible K S (Γ K S) (generator K S D e) q := by
  refine Quotient.inductionOn q (fun a => ?_)
  rw [orbitIdeal_mk, sIntegerOrbitDivisible_mk]
  change e.val.val ∣ (elementIdeal K S a).val.val ↔ D.generator e ∣ a.val
  constructor
  · intro h
    have hh := Ideal.map_mono (f := algebraMap (𝓞 K) OS) (Ideal.dvd_iff_le.mp h)
    rw [elementIdeal_span, ← D.generator_span] at hh
    exact Ideal.span_singleton_le_span_singleton.mp hh
  · intro h
    apply Ideal.dvd_iff_le.mpr
    have hh : Ideal.span ({a.val} : Set OS) ≤ Ideal.span {D.generator e} :=
      Ideal.span_singleton_le_span_singleton.mpr h
    have hu := Ideal.comap_mono (f := algebraMap (𝓞 K) OS) hh
    change (Ideal.span ({a.val} : Set OS)).under (𝓞 K) ≤
      (Ideal.span ({D.generator e} : Set OS)).under (𝓞 K) at hu
    rw [D.generator_span, under_map_coprime_sIntegerIdeal K S e.val.val
      (sexticIdeal_coprime_S K S e.val.val e.property)] at hu
    exact hu

theorem coefficient_common_mask (d : ExteriorIdeal K S) (q : Q) :
    conj (coefficient K S D d q) * coefficient K S D d q =
      if IsCoprime (orbitIdeal K S q).val.val d.val.val then 1 else 0 := by
  obtain ⟨⟨I, l⟩, rfl⟩ := classOrbit_surjective K S D q
  have ho : orbitIdeal K S (classOrbit K S D (I, l)) = I :=
    orbitIdeal_scalarOrbit K S D I l.out
  rw [ho, coefficient_classOrbit]
  calc
    _ = (conj (positiveKernel K S D I d) * positiveKernel K S D I d) *
        (conj (unitPhase K S D l d) * unitPhase K S D l d) := by
      simp only [map_mul]
      ring
    _ = _ := by
      rw [common_kernel_mask, Complex.conj_mul', unitPhase_norm]
      norm_num

def pair (q : Q) (a b : ExteriorIdeal K S) (z : ExteriorIdeal K S → ℂ) : ℂ :=
  conj (coefficient K S D a q * z a) * (coefficient K S D b q * z b)

def coprimeGram (T : Finset (ExteriorIdeal K S)) (q : Q)
    (z : ExteriorIdeal K S → ℂ) : ℂ :=
  ∑ a ∈ T, ∑ b ∈ T, if IsCoprime a.val.val b.val.val then pair K S D q a b z else 0

private theorem gcd_pair (q : Q) (d a b : ExteriorIdeal K S)
    (z : ExteriorIdeal K S → ℂ) :
    (if exteriorGcd K S (exteriorMul K S d a) (exteriorMul K S d b) = d then
      pair K S D q (exteriorMul K S d a) (exteriorMul K S d b) z else 0) =
    (if IsCoprime (orbitIdeal K S q).val.val d.val.val then (1 : ℂ) else 0) *
      (if IsCoprime a.val.val b.val.val then
        pair K S D q a b (fun a => z (exteriorMul K S d a)) else 0) := by
  have hda : d.val.val ∣ (exteriorMul K S d a).val.val := dvd_mul_right _ _
  have hdb : d.val.val ∣ (exteriorMul K S d b).val.val := dvd_mul_right _ _
  have hqa : quotient K S d (exteriorMul K S d a) hda = a :=
    quotient_product_right K S d a hda
  have hqb : quotient K S d (exteriorMul K S d b) hdb = b :=
    quotient_product_right K S d b hdb
  have hg := gcd_eq_iff_quotient_coprime K S d
    (exteriorMul K S d a) (exteriorMul K S d b) hda hdb
  rw [hqa, hqb] at hg
  by_cases hc : IsCoprime a.val.val b.val.val
  · rw [ite_eq_left (hg.mpr hc), ite_eq_left hc]
    simp only [pair, coefficient_column_mul, map_mul]
    rw [← coefficient_common_mask K S D d q]
    ring
  · rw [ite_eq_right (fun h => hc (hg.mp h)), ite_eq_right hc, mul_zero]

theorem row_gram_moebius (T : Finset (ExteriorIdeal K S)) (q : Q)
    (z : ExteriorIdeal K S → ℂ) :
    ((orbitEnergy K S D T z q : ℝ) : ℂ) =
      ∑ d ∈ gcdImage K S T, ∑ e ∈ divisors K S d, (moebius e.val.val : ℂ) *
        (if sIntegerOrbitDivisible K S (Γ K S) (generator K S D e) q then
          coprimeGram K S D (dividedSet K S T d) q
            (fun a => z (exteriorMul K S d a)) else 0) := by
  have hpart : ((orbitEnergy K S D T z q : ℝ) : ℂ) =
      ∑ d ∈ gcdImage K S T, ∑ a ∈ T, ∑ b ∈ T,
        if exteriorGcd K S a b = d then pair K S D q a b z else 0 := by
    have hn : ((orbitEnergy K S D T z q : ℝ) : ℂ) =
        ∑ a ∈ T, ∑ b ∈ T, pair K S D q a b z := by
      rw [orbitEnergy, Complex.ofReal_pow, ← Complex.conj_mul']
      simp only [map_sum, Finset.sum_mul, Finset.mul_sum, pair]
      exact Finset.sum_comm
    have hex : (∑ d ∈ gcdImage K S T, ∑ a ∈ T, ∑ b ∈ T,
        if exteriorGcd K S a b = d then pair K S D q a b z else 0) =
        ∑ a ∈ T, ∑ b ∈ T, ∑ d ∈ gcdImage K S T,
          if exteriorGcd K S a b = d then pair K S D q a b z else 0 := by
      calc
        _ = ∑ a ∈ T, ∑ d ∈ gcdImage K S T, ∑ b ∈ T,
            if exteriorGcd K S a b = d then pair K S D q a b z else 0 := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a ha
          exact Finset.sum_comm
    rw [hn, hex]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    symm
    exact Finset.sum_ite_eq_of_mem _ _ _ (gcd_mem_image K S T a b ha hb)
  rw [hpart]
  apply Finset.sum_congr rfl
  intro d hd
  have hrestrict : (∑ a ∈ T, ∑ b ∈ T,
      if exteriorGcd K S a b = d then pair K S D q a b z else 0) =
      ∑ a ∈ T.filter (fun a => d.val.val ∣ a.val.val),
        ∑ b ∈ T.filter (fun b => d.val.val ∣ b.val.val),
          if exteriorGcd K S a b = d then pair K S D q a b z else 0 := by
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hda : d.val.val ∣ a.val.val
    · rw [ite_eq_left hda]
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hdb : d.val.val ∣ b.val.val
      · rw [ite_eq_left hdb]
      · rw [ite_eq_right hdb,
          ite_eq_right (fun h => hdb (gcd_eq_forces_right K S d a b h))]
    · rw [ite_eq_right hda]
      apply Finset.sum_eq_zero
      intro b hb
      exact ite_eq_right (fun h => hda (gcd_eq_forces_left K S d a b h))
  rw [hrestrict]
  simp_rw [← dividedSet_image K S T d]
  rw [Finset.sum_image (exteriorMul_left_injective K S d).injOn]
  simp_rw [Finset.sum_image (exteriorMul_left_injective K S d).injOn, gcd_pair]
  simp_rw [← Finset.mul_sum]
  change (if IsCoprime (orbitIdeal K S q).val.val d.val.val then (1 : ℂ) else 0) *
      coprimeGram K S D (dividedSet K S T d) q (fun a => z (exteriorMul K S d a)) = _
  rw [coprime_mask K S (orbitIdeal K S q) d, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  rw [ideal_dvd_iff_orbitDivisible K S D e q]
  by_cases h : sIntegerOrbitDivisible K S (Γ K S) (generator K S D e) q <;> simp [h]

theorem coprimeGram_dilation (T : Finset (ExteriorIdeal K S)) (d e : ExteriorIdeal K S)
    (q : Q) (z : ExteriorIdeal K S → ℂ) :
    coprimeGram K S D (dividedSet K S T d)
      (sIntegerOrbitDilation K S (Γ K S) (generator K S D e) q)
      (fun a => z (exteriorMul K S d a)) =
    coprimeGram K S D (dividedSet K S T d) q (pulledCoefficient K S D d e z) := by
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hc : IsCoprime a.val.val b.val.val
  · rw [ite_eq_left hc, ite_eq_left hc]
    simp only [pair, pulledCoefficient, coefficient_dilation, map_mul]
    ring
  · rw [ite_eq_right hc, ite_eq_right hc]

theorem coprimeGram_norm_bound (T : Finset (ExteriorIdeal K S)) (q : Q)
    (z : ExteriorIdeal K S → ℂ) :
    ‖coprimeGram K S D T q z‖ ≤ (∑ a ∈ T, ‖z a‖) ^ 2 := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ T, ∑ b ∈ T, ‖z a‖ * ‖z b‖ := by
      apply Finset.sum_le_sum
      intro a ha
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b hb
      by_cases hc : IsCoprime a.val.val b.val.val
      · rw [ite_eq_left hc]
        simp only [pair, norm_mul, Complex.norm_conj]
        have ha' : ‖coefficient K S D a q‖ * ‖z a‖ ≤ ‖z a‖ := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right
            (coefficient_norm_le_one K S D a q) (norm_nonneg _)
        have hb' : ‖coefficient K S D b q‖ * ‖z b‖ ≤ ‖z b‖ := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right
            (coefficient_norm_le_one K S D b q) (norm_nonneg _)
        exact mul_le_mul ha' hb' (by positivity) (norm_nonneg _)
      · rw [ite_eq_right hc, norm_zero]
        positivity
    _ = _ := by rw [pow_two, Finset.sum_mul]; simp only [Finset.mul_sum]

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]

def profile (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ) (M : ℝ) (hM : 0 < M) (q : Q) : ℂ :=
  sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) (orbitRadius K S M hM q)

theorem bounded_weight_summable (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψcs : HasCompactSupport ψ) (M : ℝ) (hM : 0 < M)
    (w : Q → ℂ) (B : ℝ) (hw : ∀ q, ‖w q‖ ≤ B) :
    Summable (fun q => w q * profile K S φ ψ M hM q) := by
  exact (hasSum_sIntegerOrbitalProfile_weighted K S (Γ K S) φ ψ hψ hψcs
    ⟨M⁻¹, inv_pos.mpr hM⟩ w B hw).summable

theorem profile_dilation (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (M : ℝ) (hM : 0 < M) (e : ExteriorIdeal K S) (q : Q) :
    profile K S φ ψ M hM
      (sIntegerOrbitDilation K S (Γ K S) (generator K S D e) q) =
    profile K S φ ψ (M / exteriorNorm K S e)
      (div_pos hM (by linarith [AnalyticDyadic.one_le_norm K S e])) q := by
  apply congrArg (sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ))
  apply Subtype.ext
  change M⁻¹ * (sIntegerOrbitNorm K S (Γ K S)
    (sIntegerOrbitDilation K S (Γ K S) (generator K S D e) q)).val = _
  rw [sIntegerOrbitNorm_dilation, generator_norm]
  change M⁻¹ * (exteriorNorm K S e * (sIntegerOrbitNorm K S (Γ K S) q).val) =
    (M / exteriorNorm K S e)⁻¹ * (sIntegerOrbitNorm K S (Γ K S) q).val
  rw [inv_div]
  ring

def descendantSeries (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (M : ℝ) (hM : 0 < M) (T : Finset (ExteriorIdeal K S)) (z : ExteriorIdeal K S → ℂ)
    (d e : ExteriorIdeal K S) : ℂ :=
  ∑' q : Q, coprimeGram K S D (dividedSet K S T d) q (pulledCoefficient K S D d e z) *
    profile K S φ ψ (M / exteriorNorm K S e)
      (div_pos hM (by linarith [AnalyticDyadic.one_le_norm K S e])) q

/-- Every transformed row series is genuinely absolutely summable, even for
nonunit divisor dilation. The row space is the original full Γ6 orbit space. -/
theorem descendantSeries_summable (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψcs : HasCompactSupport ψ) (M : ℝ) (hM : 0 < M)
    (T : Finset (ExteriorIdeal K S)) (z : ExteriorIdeal K S → ℂ)
    (d e : ExteriorIdeal K S) :
    Summable (fun q : Q => coprimeGram K S D (dividedSet K S T d) q
      (pulledCoefficient K S D d e z) * profile K S φ ψ (M / exteriorNorm K S e)
        (div_pos hM (by linarith [AnalyticDyadic.one_le_norm K S e])) q) :=
  bounded_weight_summable K S φ ψ hψ hψcs _ _ _ _
    (fun q => coprimeGram_norm_bound K S D _ q _)

theorem descendantSeries_norm_summable (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψcs : HasCompactSupport ψ) (M : ℝ) (hM : 0 < M)
    (T : Finset (ExteriorIdeal K S)) (z : ExteriorIdeal K S → ℂ)
    (d e : ExteriorIdeal K S) :
    Summable (fun q : Q => ‖coprimeGram K S D (dividedSet K S T d) q
      (pulledCoefficient K S D d e z) * profile K S φ ψ (M / exteriorNorm K S e)
        (div_pos hM (by linarith [AnalyticDyadic.one_le_norm K S e])) q‖) :=
  (descendantSeries_summable K S D φ ψ hψ hψcs M hM T z d e).norm

/-- Exact infinite-row gcd/Möbius descent. Both divisor sums are finite;
their exchange with the row sum uses the proved bounded-weight summability. -/
theorem weighted_gram_descent (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψcs : HasCompactSupport ψ) (M : ℝ) (hM : 0 < M)
    (T : Finset (ExteriorIdeal K S)) (z : ExteriorIdeal K S → ℂ) :
    (∑' q : Q, (orbitEnergy K S D T z q : ℂ) * profile K S φ ψ M hM q) =
      ∑ d ∈ gcdImage K S T, ∑ e ∈ divisors K S d,
        (moebius e.val.val : ℂ) * descendantSeries K S D φ ψ M hM T z d e := by
  let G := fun (d : ExteriorIdeal K S) (q : Q) =>
    coprimeGram K S D (dividedSet K S T d) q (fun a => z (exteriorMul K S d a))
  let F := fun (d e : ExteriorIdeal K S) (q : Q) =>
    (if sIntegerOrbitDivisible K S (Γ K S) (generator K S D e) q then G d q else 0) *
      profile K S φ ψ M hM q
  have hF (d e : ExteriorIdeal K S) : Summable (F d e) := by
    apply bounded_weight_summable K S φ ψ hψ hψcs M hM _
      ((∑ a ∈ dividedSet K S T d, ‖z (exteriorMul K S d a)‖) ^ 2)
    intro q
    by_cases h : sIntegerOrbitDivisible K S (Γ K S) (generator K S D e) q
    · simpa only [ite_eq_left h, G] using coprimeGram_norm_bound K S D
        (dividedSet K S T d) q (fun a => z (exteriorMul K S d a))
    · rw [ite_eq_right h, norm_zero]
      positivity
  have hreindex (d e : ExteriorIdeal K S) :
      (∑' q : Q, F d e q) = descendantSeries K S D φ ψ M hM T z d e := by
    rw [tsum_sIntegerOrbitDilation K S (Γ K S) (generator K S D e) (F d e)
      (fun q hq => by simp only [F, ite_eq_right hq, zero_mul])]
    apply tsum_congr
    intro q
    have hdiv : sIntegerOrbitDivisible K S (Γ K S) (generator K S D e)
        (sIntegerOrbitDilation K S (Γ K S) (generator K S D e) q) :=
      (sIntegerOrbitDivisible_iff_exists K S (Γ K S) _ _).mpr ⟨q, rfl⟩
    simp only [F, ite_eq_left hdiv, G, coprimeGram_dilation, profile_dilation]
  calc
    _ = ∑' q : Q, ∑ d ∈ gcdImage K S T, ∑ e ∈ divisors K S d,
        (moebius e.val.val : ℂ) * F d e q := by
      apply tsum_congr
      intro q
      rw [row_gram_moebius, Finset.sum_mul]
      simp only [Finset.sum_mul, F]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      ring
    _ = ∑ d ∈ gcdImage K S T, ∑' q : Q, ∑ e ∈ divisors K S d,
        (moebius e.val.val : ℂ) * F d e q :=
      Summable.tsum_finsetSum (s := gcdImage K S T) (fun d hd =>
        summable_sum (fun e he => (hF d e).mul_left _))
    _ = ∑ d ∈ gcdImage K S T, ∑ e ∈ divisors K S d,
        ∑' q : Q, (moebius e.val.val : ℂ) * F d e q := by
      apply Finset.sum_congr rfl
      intro d hd
      exact Summable.tsum_finsetSum (s := divisors K S d)
        (fun e he => (hF d e).mul_left _)
    _ = _ := by simp_rw [tsum_mul_left, hreindex]

/-- The real smooth-energy used to dominate the full sieve is the real part
of this exact complex divisor sum. No reality assumption on a Fourier profile
or exchange of a conditionally convergent series is used. -/
theorem smoothEnergy_eq_descent_re (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψcs : HasCompactSupport ψ) (M : ℝ) (hM : 0 < M)
    (T : Finset (ExteriorIdeal K S)) (z : ExteriorIdeal K S → ℂ) :
    smoothEnergy K S D φ ψ M hM T z =
      (∑ d ∈ gcdImage K S T, ∑ e ∈ divisors K S d,
        (moebius e.val.val : ℂ) * descendantSeries K S D φ ψ M hM T z d e).re := by
  have hs : Summable (fun q : Q => (orbitEnergy K S D T z q : ℂ) *
      profile K S φ ψ M hM q) := by
    apply bounded_weight_summable K S φ ψ hψ hψcs M hM _ ((∑ J ∈ T, ‖z J‖) ^ 2)
    intro q
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact orbitEnergy_bound K S D T z q
  rw [← weighted_gram_descent K S D φ ψ hψ hψcs M hM T z]
  change smoothEnergy K S D φ ψ M hM T z =
    RCLike.re (∑' q : Q, (orbitEnergy K S D T z q : ℂ) * profile K S φ ψ M hM q)
  rw [RCLike.re_tsum ℂ hs]
  apply tsum_congr
  intro q
  change (profile K S φ ψ M hM q).re * orbitEnergy K S D T z q =
    ((orbitEnergy K S D T z q : ℂ) * profile K S φ ψ M hM q).re
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

section Gaussian

variable (A : DedekindZetaZeroFree.SArithmeticData K)
local instance gaussianMeasurable : MeasurableSpace
    (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) := borel _
local instance gaussianBorel : BorelSpace
    (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) := ⟨rfl⟩

/-- The actual Gaussian is a direct specialization of the absolutely
convergent bridge, with precisely the finite unit-shell used by smoothing. -/
theorem gaussian_smoothEnergy_eq_descent_re
    (D₀ : ThetaArithmeticData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (M : ℝ) (hM : 0 < M)
    (T : Finset (ExteriorIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))))
    (z : ExteriorIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) → ℂ) :
    smoothEnergy K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D₀
      (DedekindZetaZeroFree.AbelianQuotient.Theta.traceGaussianSchwartz K)
      (Profile.finiteTest A) M hM T z =
      (∑ d ∈ gcdImage K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) T,
        ∑ e ∈ divisors K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) d, (moebius e.val.val : ℂ) *
        descendantSeries K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D₀
          (DedekindZetaZeroFree.AbelianQuotient.Theta.traceGaussianSchwartz K)
          (Profile.finiteTest A) M hM T z d e).re := by
  exact smoothEnergy_eq_descent_re K _ D₀ _ (Profile.finiteTest A)
    (Profile.finiteTest_continuous A) (Profile.finiteTest_compactSupport A) M hM T z

end Gaussian
end CubicSieve.AnalyticGcdSeries
