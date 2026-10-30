import CubicSieve.GaussPairOrbitalPoisson
import CubicSieve.PoissonOrigin
import CubicSieve.PoissonCoefficients
import CubicSieve.ProfileSpectrum
import CubicSieve.AnalyticSmoothingKernel

/-! Actual Gaussian Poisson for each coprime column pair, then for a finite
column Gram sum. Finite column sums stay outside the orbital sums. The same
canonical Gaussian dual profile is used, with the physical scalar kappa and
the literal dual origin retained. No infinite/finite sum exchange is used. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.PoissonSmoothed

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.Analysis HeckeGeneral.Bridge
open CubicSieve.OrbitRows CubicSieve.OrbitKernel CubicSieve.GaussPairLiteral
open scoped Classical BigOperators NumberField

variable (K : Type) [Field K] [NumberField K]

abbrev archConstant : ℂ :=
  (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ)

abbrev scaleScalar (M : ℝ) : ℂ := (M : ℂ) * archConstant K

variable {K} (A : SArithmeticData K)
local notation "S" => (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
local notation "Q" => Orbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))

local instance normOneMeasurable :
    MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) := borel _
local instance normOneBorel :
    BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) := ⟨rfl⟩
local instance completionMeasurable (v : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (v.adicCompletion K) := borel _
local instance completionBorel (v : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (v.adicCompletion K) := ⟨rfl⟩
local instance finiteAdeleMeasurable : MeasurableSpace (FiniteAdeleRing (𝓞 K) K) := borel _
local instance finiteAdeleBorel : BorelSpace (FiniteAdeleRing (𝓞 K) K) := ⟨rfl⟩
local instance adeleMeasurable : MeasurableSpace (AdeleRing (𝓞 K) K) := borel _
local instance adeleBorel : BorelSpace (AdeleRing (𝓞 K) K) := ⟨rfl⟩
local instance gammaFiniteIndex : (Γ K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))).FiniteIndex :=
  sUnit_power_range_finiteIndex K _ 6 (by norm_num)

private theorem norm_pos (I : ExteriorIdeal K S) : 0 < exteriorNorm K S I := by
  change 0 < (I.val.val.absNorm : ℝ)
  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I.val

def pairWeight (I J : ExteriorIdeal K S) (q : Q) : ℂ :=
  star (coefficient K S D I q) * coefficient K S D J q

theorem rowWeight_eq (I J : ExteriorIdeal K S) (hI : Squarefree I.val.val)
    (hJ : Squarefree J.val.val) (q : Q) :
    GaussPairOrbitalPoisson.rowWeight K A.Sf D (Γ K S) le_rfl I J hI hJ q =
      pairWeight A D I J q := by
  refine Quotient.inductionOn q (fun a => ?_)
  change literalRow K S D I J hI hJ (Ideal.Quotient.mk _ a.val) =
    star (idealSymbol K S D I a.val ^ 2) * idealSymbol K S D J a.val ^ 2
  exact literalRow_mk K S D I J hI hJ a.val

def sourceProfile (M : ℝ) (hM : 0 < M) (q : Q) : ℂ :=
  sUnitOrbitalProfile K S
    (sLocalTensorTestFunction K S (Profile.Gaussian.archTest K) (Profile.finiteTest A))
    ⟨M⁻¹ * (sIntegerOrbitNorm K S (Γ K S) q).val,
      mul_pos (inv_pos.mpr hM) (sIntegerOrbitNorm K S (Γ K S) q).property⟩

def sourcePair (M : ℝ) (hM : 0 < M) (I J : ExteriorIdeal K S) : ℂ :=
  ∑' q : Q, pairWeight A D I J q * sourceProfile A M hM q

/-- Absolute summability comes from the actual Schwartz orbital unfolding. -/
theorem sourcePair_norm_summable (M : ℝ) (hM : 0 < M) (I J : ExteriorIdeal K S) :
    Summable (fun q : Q => ‖pairWeight A D I J q * sourceProfile A M hM q‖) := by
  apply (hasSum_sIntegerOrbitalProfile_weighted K S (Γ K S)
    (Profile.Gaussian.archTest K) (Profile.finiteTest A)
    (Profile.finiteTest_continuous A) (Profile.finiteTest_compactSupport A)
    ⟨M⁻¹, inv_pos.mpr hM⟩ (pairWeight A D I J) 1 ?_).summable.norm
  intro q
  rw [pairWeight, norm_mul, norm_star]
  calc
    _ ≤ 1 * 1 := mul_le_mul
      (AnalyticSmoothing.coefficient_norm_le_one K S D I q)
      (AnalyticSmoothing.coefficient_norm_le_one K S D J q) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

def dualPair (M : ℝ) (hM : 0 < M) (I J : ExteriorIdeal K S) : ℂ :=
  ∑' q : Q, star (pairWeight A D I J q) * Profile.Gaussian.dualProfile A
    ⟨M * (sIntegerOrbitNorm K S (Γ K S) q).val /
        (exteriorNorm K S I * exteriorNorm K S J),
      div_pos (mul_pos hM (sIntegerOrbitNorm K S (Γ K S) q).property)
        (mul_pos (norm_pos A I) (norm_pos A J))⟩

abbrev gaussPhase (I J : ExteriorIdeal K S) : ℂ :=
  star (thetaGamma K S D I 2) * thetaGamma K S D J 2

/-- The dual origin is an actual tensor integral, with its unit-ideal mask. -/
def dualOrigin (M : ℝ) (I J : ExteriorIdeal K S) : ℂ :=
  ((sUnitHaarCovolume K S (Γ K S)).toReal : ℂ) *
    (scaleScalar K M * ((exteriorNorm K S I * exteriorNorm K S J : ℝ) : ℂ)⁻¹ *
      (((Real.sqrt (exteriorNorm K S I * exteriorNorm K S J) : ℂ) * gaussPhase A D I J) *
        star (if I.val.val = ⊤ ∧ J.val.val = ⊤ then (1 : ℂ) else 0) *
        sIntegerDualTensorTerm K (localNormalizedHaar K) A.Sf
          (traceSchwartzToMixed K (Profile.Gaussian.archTest K))
          (TateFiniteShell.annularTest K) 0))

theorem physicalProfile_eq (r : {r : ℝ // 0 < r}) :
    sUnitOrbitalProfile K S
      (sLocalTensorTestFunction K S (traceSchwartzFourier K (Profile.Gaussian.archTest K))
        (sIntegerFiniteFourierTestFunction K A.Sf (localNormalizedHaar K)
          (TateFiniteShell.annularTest K))) r =
      HeckeAxiom.ProbeTestChoice.kappa A * Profile.Gaussian.dualProfile A r := by
  change (∫ t : sLocalNormOneGroup K S, _ ∂sUnitHaarMeasure K S) =
    HeckeAxiom.ProbeTestChoice.kappa A *
      (∫ t : sLocalNormOneGroup K S,
        Profile.Gaussian.dualLocalFunction A (sLocalNormSection K S r * t.val)
          ∂sUnitHaarMeasure K S)
  simp_rw [Profile.Gaussian.physicalDual_eq_kappa]
  rw [integral_const_mul]

theorem pair_poisson (hD : AllowedGeneratorInput K S D)
    (M : ℝ) (hM : 0 < M) (I J : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) (hJ : Squarefree J.val.val)
    (hcop : IsCoprime I.val.val J.val.val) :
    sourcePair A D M hM I J =
      (scaleScalar K M * HeckeAxiom.ProbeTestChoice.kappa A) *
        ((Real.sqrt (exteriorNorm K S I * exteriorNorm K S J) : ℂ)⁻¹ *
          gaussPhase A D I J) * dualPair A D M hM I J + dualOrigin A D M I J := by
  let c := D.generator I * D.generator J
  have hc : c ≠ 0 := mul_ne_zero (D.generator_ne_zero I) (D.generator_ne_zero J)
  let rd : {r : ℝ // 0 < r} :=
    ⟨(M⁻¹ * (sIntegerElementNorm K S ⟨c, hc⟩).val)⁻¹,
      inv_pos.mpr (mul_pos (inv_pos.mpr hM) (sIntegerElementNorm K S ⟨c, hc⟩).property)⟩
  have hrd : rd.val = M / (exteriorNorm K S I * exteriorNorm K S J) :=
    GaussPairOrbitalPoisson.dual_radius_eq K A.Sf D I J hD M
  have hright : sIntegerWeightedOrbitalSeries K A.Sf (Γ K S)
      (traceSchwartzFourier K (Profile.Gaussian.archTest K))
      (sIntegerFiniteFourierTestFunction K A.Sf (localNormalizedHaar K)
        (TateFiniteShell.annularTest K)) rd
      (fun q => star (pairWeight A D I J q)) =
      HeckeAxiom.ProbeTestChoice.kappa A * dualPair A D M hM I J := by
    unfold sIntegerWeightedOrbitalSeries dualPair
    rw [← tsum_mul_left]
    apply tsum_congr
    intro q
    rw [physicalProfile_eq]
    have hr : (⟨rd.val * (sIntegerOrbitNorm K S (Γ K S) q).val,
        mul_pos rd.property (sIntegerOrbitNorm K S (Γ K S) q).property⟩ : {r : ℝ // 0 < r}) =
        ⟨M * (sIntegerOrbitNorm K S (Γ K S) q).val /
            (exteriorNorm K S I * exteriorNorm K S J),
          div_pos (mul_pos hM (sIntegerOrbitNorm K S (Γ K S) q).property)
            (mul_pos (norm_pos A I) (norm_pos A J))⟩ := by
      apply Subtype.ext
      dsimp only
      rw [hrd]
      ring
    rw [hr]
    ring
  have hweight : sIntegerPeriodicOrbitWeight K S (Γ K S) c
      (fun z => literalRow K S D I J hI hJ (Ideal.Quotient.mk _ 1 * z))
      (sIntegerPeriodic_divisorPullback_literal_invariant K A.Sf (Γ K S) c
        (literalRow K S D I J hI hJ)
        (GaussPairOrbitalPoisson.row_literal_invariant K A.Sf D (Γ K S) le_rfl I J hI hJ) 1) =
      pairWeight A D I J := by
    funext q
    refine Quotient.inductionOn q (fun a => ?_)
    change literalRow K S D I J hI hJ (Ideal.Quotient.mk _ 1 * Ideal.Quotient.mk _ a.val) =
      star (idealSymbol K S D I a.val ^ 2) * idealSymbol K S D J a.val ^ 2
    rw [map_one, one_mul]
    exact literalRow_mk K S D I J hI hJ a.val
  have hf1 : literalRow K S D I J hI hJ 1 = 1 := by
    simpa only [map_one, idealSymbol, sIntegerSexticIdealEvaluation_one,
      one_pow, star_one, mul_one] using literalRow_mk K S D I J hI hJ (1 : Set.integer S K)
  have hC : ((M⁻¹ : ℝ) : ℂ)⁻¹ * archConstant K *
      ((sIntegerElementNorm K S ⟨c, hc⟩).val : ℂ)⁻¹ =
      scaleScalar K M * ((exteriorNorm K S I * exteriorNorm K S J : ℝ) : ℂ)⁻¹ := by
    rw [GaussPairOrbitalPoisson.modulus_norm K A.Sf D I J hD]
    simp only [Complex.ofReal_inv, inv_inv, scaleScalar]
  have hp := GaussPairOrbitalPoisson.pair_orbital_poisson K A.Sf D (Γ K S) le_rfl I J hI hJ
    (Measure.addHaar : Measure (FiniteAdeleRing (𝓞 K) K)) (localNormalizedHaar K)
    (Measure.addHaar : Measure (AdeleRing (𝓞 K) K)) hD hcop (Profile.Gaussian.archTest K)
    (TateFiniteShell.annularTest K)
    (fun v _ => (TateFiniteShell.annularTest_mem_localSchwartz K v).1)
    (fun v _ => (TateFiniteShell.annularTest_mem_localSchwartz K v).2)
    1 ⟨M⁻¹, inv_pos.mpr hM⟩
  dsimp only at hp
  simp only [map_one, one_mul, hf1] at hp
  rw [hweight] at hp
  simp_rw [rowWeight_eq A D I J hI hJ] at hp
  rw [hright, hC, PoissonOrigin.literalRow_zero,
    PoissonOrigin.sIntegerTensorTerm_zero] at hp
  simp only [mul_zero, sub_zero] at hp
  have hraw : sourcePair A D M hM I J =
      (scaleScalar K M * ((exteriorNorm K S I * exteriorNorm K S J : ℝ) : ℂ)⁻¹ *
        ((Real.sqrt (exteriorNorm K S I * exteriorNorm K S J) : ℂ) * gaussPhase A D I J)) *
        (HeckeAxiom.ProbeTestChoice.kappa A * dualPair A D M hM I J) + dualOrigin A D M I J := hp
  rw [hraw]
  have hsq : (Real.sqrt (exteriorNorm K S I * exteriorNorm K S J) : ℂ) ^ 2 =
      ((exteriorNorm K S I * exteriorNorm K S J : ℝ) : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (mul_pos (norm_pos A I) (norm_pos A J)).le
  have hs : (Real.sqrt (exteriorNorm K S I * exteriorNorm K S J) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (mul_pos (norm_pos A I) (norm_pos A J))).ne'
  have hcancel : ((exteriorNorm K S I * exteriorNorm K S J : ℝ) : ℂ)⁻¹ *
      (Real.sqrt (exteriorNorm K S I * exteriorNorm K S J) : ℂ) =
      (Real.sqrt (exteriorNorm K S I * exteriorNorm K S J) : ℂ)⁻¹ := by
    rw [← hsq, pow_two, mul_inv, mul_assoc, inv_mul_cancel₀ hs, mul_one]
  calc
    _ = (scaleScalar K M * HeckeAxiom.ProbeTestChoice.kappa A) *
        (((exteriorNorm K S I * exteriorNorm K S J : ℝ) : ℂ)⁻¹ *
          (Real.sqrt (exteriorNorm K S I * exteriorNorm K S J) : ℂ)) *
        gaussPhase A D I J * dualPair A D M hM I J + dualOrigin A D M I J := by ring
    _ = _ := by rw [hcancel]; ring

def sourceSeries (M : ℝ) (hM : 0 < M) (T : Finset (ExteriorIdeal K S))
    (z : ExteriorIdeal K S → ℂ) : ℂ :=
  ∑ I ∈ T, ∑ J ∈ T, if IsCoprime I.val.val J.val.val then
    star (z I) * z J * sourcePair A D M hM I J else 0

def coprimeGram (T : Finset (ExteriorIdeal K S)) (z : ExteriorIdeal K S → ℂ) (q : Q) : ℂ :=
  ∑ I ∈ T, ∑ J ∈ T, if IsCoprime I.val.val J.val.val then
    star (z I * coefficient K S D I q) * (z J * coefficient K S D J q) else 0

/-- The finite Gram expansion exchanges sums only after actual absolute summability. -/
theorem sourceSeries_eq_tsum (M : ℝ) (hM : 0 < M) (T : Finset (ExteriorIdeal K S))
    (z : ExteriorIdeal K S → ℂ) :
    sourceSeries A D M hM T z =
      ∑' q : Q, coprimeGram A D T z q * sourceProfile A M hM q := by
  let F := fun (I J : ExteriorIdeal K S) (q : Q) =>
    if IsCoprime I.val.val J.val.val then
      star (z I) * z J * (pairWeight A D I J q * sourceProfile A M hM q) else 0
  have hFnorm (I J : ExteriorIdeal K S) : Summable (fun q => ‖F I J q‖) := by
    by_cases hc : IsCoprime I.val.val J.val.val
    · simpa only [F, if_pos hc, norm_mul] using
        (sourcePair_norm_summable A D M hM I J).mul_left ‖star (z I) * z J‖
    · simp only [F, if_neg hc, norm_zero]
      exact summable_zero
  have hF (I J : ExteriorIdeal K S) : Summable (F I J) := (hFnorm I J).of_norm
  symm
  calc
    _ = ∑' q : Q, ∑ I ∈ T, ∑ J ∈ T, F I J q := by
      apply tsum_congr
      intro q
      simp only [coprimeGram, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro J hJ
      by_cases hc : IsCoprime I.val.val J.val.val
      · simp only [F, if_pos hc, pairWeight, star_mul]
        ring
      · simp only [F, if_neg hc, zero_mul]
    _ = ∑ I ∈ T, ∑' q : Q, ∑ J ∈ T, F I J q :=
      Summable.tsum_finsetSum (s := T) (fun I _ => summable_sum (fun J _ => hF I J))
    _ = ∑ I ∈ T, ∑ J ∈ T, ∑' q : Q, F I J q := by
      apply Finset.sum_congr rfl
      intro I hI
      exact Summable.tsum_finsetSum (s := T) (fun J _ => hF I J)
    _ = _ := by
      unfold sourceSeries
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro J hJ
      by_cases hc : IsCoprime I.val.val J.val.val <;> simp [F, hc, sourcePair, tsum_mul_left]

def dualSeries (M : ℝ) (hM : 0 < M) (T : Finset (ExteriorIdeal K S))
    (z : ExteriorIdeal K S → ℂ) : ℂ :=
  ∑ I ∈ T, ∑ J ∈ T, if IsCoprime I.val.val J.val.val then
    PoissonCoefficients.dual K S D z I * star (PoissonCoefficients.dual K S D z J) *
      dualPair A D M hM I J else 0

def originSeries (M : ℝ) (T : Finset (ExteriorIdeal K S))
    (z : ExteriorIdeal K S → ℂ) : ℂ :=
  ∑ I ∈ T, ∑ J ∈ T, if IsCoprime I.val.val J.val.val then
    star (z I) * z J * dualOrigin A D M I J else 0

/-- The actual finite-column coprime Gaussian Gram Poisson identity. -/
theorem smoothed_coprime_gram (hD : AllowedGeneratorInput K S D)
    (M : ℝ) (hM : 0 < M) (T : Finset (ExteriorIdeal K S))
    (hT : ∀ I ∈ T, Squarefree I.val.val) (z : ExteriorIdeal K S → ℂ) :
    sourceSeries A D M hM T z =
      (scaleScalar K M * HeckeAxiom.ProbeTestChoice.kappa A) * dualSeries A D M hM T z +
        originSeries A D M T z := by
  unfold sourceSeries dualSeries originSeries
  calc
    _ = ∑ I ∈ T, ∑ J ∈ T,
        ((scaleScalar K M * HeckeAxiom.ProbeTestChoice.kappa A) *
          (if IsCoprime I.val.val J.val.val then
            PoissonCoefficients.dual K S D z I * star (PoissonCoefficients.dual K S D z J) *
              dualPair A D M hM I J else 0) +
          (if IsCoprime I.val.val J.val.val then
            star (z I) * z J * dualOrigin A D M I J else 0)) := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro J hJ
      by_cases hc : IsCoprime I.val.val J.val.val
      · rw [if_pos hc, if_pos hc, if_pos hc, pair_poisson A D hD M hM I J (hT I hI) (hT J hJ) hc]
        calc
          _ = (scaleScalar K M * HeckeAxiom.ProbeTestChoice.kappa A) *
              (star (z I) * z J * (Real.sqrt (exteriorNorm K S I * exteriorNorm K S J) : ℂ)⁻¹ *
                gaussPhase A D I J) * dualPair A D M hM I J +
              star (z I) * z J * dualOrigin A D M I J := by ring
          _ = _ := by rw [gaussPhase, PoissonCoefficients.pair_scalar K S D z I J]; ring
      · simp only [if_neg hc, mul_zero, zero_add]
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- A fixed field/arithmetic-set constant, including the actual dual tensor integral. -/
def originConstant : ℝ :=
  ‖((sUnitHaarCovolume K S (Γ K S)).toReal : ℂ)‖ * ‖archConstant K‖ *
    ‖sIntegerDualTensorTerm K (localNormalizedHaar K) A.Sf
      (traceSchwartzToMixed K (Profile.Gaussian.archTest K))
      (TateFiniteShell.annularTest K) 0‖

theorem dualOrigin_eq_zero_of_ne (M : ℝ) (I J : ExteriorIdeal K S) (hIJ : I ≠ J) :
    dualOrigin A D M I J = 0 := by
  have hmask : ¬ (I.val.val = ⊤ ∧ J.val.val = ⊤) := by
    rintro ⟨hI, hJ⟩
    apply hIJ
    apply Subtype.ext
    apply Subtype.ext
    exact hI.trans hJ.symm
  simp only [dualOrigin, if_neg hmask, star_zero, mul_zero, zero_mul]

theorem dualOrigin_diagonal_norm_le (M : ℝ) (hM : 0 < M)
    (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    ‖dualOrigin A D M I I‖ ≤ originConstant A * M := by
  by_cases hi : I.val.val = ⊤
  · have hNI : exteriorNorm K S I = 1 := by simp [exteriorNorm, hi]
    have heq : ‖dualOrigin A D M I I‖ =
        ‖((sUnitHaarCovolume K S (Γ K S)).toReal : ℂ)‖ * (M * ‖archConstant K‖) *
          ‖sIntegerDualTensorTerm K (localNormalizedHaar K) A.Sf
            (traceSchwartzToMixed K (Profile.Gaussian.archTest K))
            (TateFiniteShell.annularTest K) 0‖ := by
      simp [dualOrigin, hNI, hi, norm_mul, norm_star, gaussPhase,
        GaussSquarefree.thetaGamma_norm K S D I hI 2 (Or.inl rfl),
        scaleScalar, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM, mul_assoc]
    rw [heq]
    unfold originConstant
    exact le_of_eq (by ring)
  · have hz : dualOrigin A D M I I = 0 := by simp [dualOrigin, hi]
    rw [hz, norm_zero]
    exact mul_nonneg (by unfold originConstant; positivity) hM.le

/-- The dual origin costs only a fixed constant times M times coefficient energy.
The actual unit-ideal mask forces every surviving column pair onto the diagonal. -/
theorem originSeries_norm_le (M : ℝ) (hM : 0 < M)
    (T : Finset (ExteriorIdeal K S)) (hT : ∀ I ∈ T, Squarefree I.val.val)
    (z : ExteriorIdeal K S → ℂ) :
    ‖originSeries A D M T z‖ ≤ originConstant A * M * ∑ I ∈ T, ‖z I‖ ^ 2 := by
  have hC : 0 ≤ originConstant A := by unfold originConstant; positivity
  unfold originSeries
  calc
    _ ≤ ∑ I ∈ T, ∑ J ∈ T,
        ‖if IsCoprime I.val.val J.val.val then
          star (z I) * z J * dualOrigin A D M I J else 0‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro I hI
      exact norm_sum_le _ _
    _ ≤ ∑ I ∈ T, ∑ J ∈ T,
        if I = J then (originConstant A * M) * ‖z I‖ ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro I hI
      apply Finset.sum_le_sum
      intro J hJ
      by_cases hIJ : I = J
      · subst J
        rw [if_pos rfl]
        by_cases hc : IsCoprime I.val.val I.val.val
        · rw [if_pos hc, norm_mul, norm_mul, norm_star]
          calc
            _ ≤ (‖z I‖ * ‖z I‖) * (originConstant A * M) :=
              mul_le_mul_of_nonneg_left (dualOrigin_diagonal_norm_le A D M hM I (hT I hI))
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            _ = _ := by ring
        · simp only [if_neg hc, norm_zero]
          positivity
      · simp [hIJ, dualOrigin_eq_zero_of_ne A D M I J hIJ]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I hI
      simp [hI]

end CubicSieve.PoissonSmoothed
