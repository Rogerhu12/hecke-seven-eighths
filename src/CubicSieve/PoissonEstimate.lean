import CubicSieve.PoissonSmoothed
import CubicSieve.PoissonTail

/-! The actual annular-column coprime Poisson estimate. The dual pair series
is absolutely summable before its exchange with the finite column sums. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.PoissonEstimate

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis HeckeGeneral.Bridge
open CubicSieve.OrbitRows CubicSieve.OrbitKernel
open scoped Classical BigOperators NumberField

variable {K : Type} [Field K] [NumberField K] (A : SArithmeticData K)
local notation "S" => (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
local notation "Q" => Orbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
local instance normOneMeasurable : MeasurableSpace
    (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) := borel _
local instance normOneBorel : BorelSpace
    (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) := ⟨rfl⟩
local instance gammaFiniteIndex : (Γ K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))).FiniteIndex :=
  sUnit_power_range_finiteIndex K _ 6 (by norm_num)

private theorem norm_pos (I : ExteriorIdeal K S) : 0 < exteriorNorm K S I := by
  change 0 < (I.val.val.absNorm : ℝ)
  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I.val

def dualTerm (M : ℝ) (hM : 0 < M) (I J : ExteriorIdeal K S) (q : Q) : ℂ :=
  star (PoissonSmoothed.pairWeight A D I J q) * Profile.Gaussian.dualProfile A
    ⟨M * (sIntegerOrbitNorm K S (Γ K S) q).val /
        (exteriorNorm K S I * exteriorNorm K S J),
      div_pos (mul_pos hM (sIntegerOrbitNorm K S (Γ K S) q).property)
        (mul_pos (norm_pos A I) (norm_pos A J))⟩

theorem dualTerm_tensor (M : ℝ) (hM : 0 < M) (I J : ExteriorIdeal K S) (q : Q) :
    dualTerm A D M hM I J q = star (PoissonSmoothed.pairWeight A D I J q) *
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S
        (Profile.Gaussian.archTest K) (Profile.Gaussian.finiteFourierProduct A))
        ⟨(M / (exteriorNorm K S I * exteriorNorm K S J)) *
            (sIntegerOrbitNorm K S (Γ K S) q).val,
          mul_pos (div_pos hM (mul_pos (norm_pos A I) (norm_pos A J)))
            (sIntegerOrbitNorm K S (Γ K S) q).property⟩ := by
  rw [dualTerm, Profile.Gaussian.dualProfile, Profile.Gaussian.dualLocalFunction_eq_tensor]
  congr 1
  congr 1
  apply Subtype.ext
  dsimp only
  ring

theorem dualTerm_norm_summable (M : ℝ) (hM : 0 < M) (I J : ExteriorIdeal K S) :
    Summable (fun q => ‖dualTerm A D M hM I J q‖) := by
  have hw (q : Q) : ‖star (PoissonSmoothed.pairWeight A D I J q)‖ ≤ 1 := by
    rw [norm_star, PoissonSmoothed.pairWeight, norm_mul, norm_star]
    calc
      _ ≤ 1 * 1 := mul_le_mul
        (AnalyticSmoothing.coefficient_norm_le_one K S D I q)
        (AnalyticSmoothing.coefficient_norm_le_one K S D J q) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hs := (hasSum_sIntegerOrbitalProfile_weighted K S (Γ K S)
    (Profile.Gaussian.archTest K) (Profile.Gaussian.finiteFourierProduct A)
    (Profile.Gaussian.finiteFourierProduct_continuous A)
    (Profile.Gaussian.finiteFourierProduct_compactSupport A)
    ⟨M / (exteriorNorm K S I * exteriorNorm K S J),
      div_pos hM (mul_pos (norm_pos A I) (norm_pos A J))⟩
    (fun q => star (PoissonSmoothed.pairWeight A D I J q)) 1 hw).summable.norm
  simpa only [dualTerm_tensor] using hs

/-- The actual finite dual Gram sum is the orbital row to which the tail applies. -/
theorem dualSeries_eq_tsum (M : ℝ) (hM : 0 < M) (T : Finset (ExteriorIdeal K S))
    (z : ExteriorIdeal K S → ℂ) :
    PoissonSmoothed.dualSeries A D M hM T z =
      ∑' q : Q, PoissonTail.row A D T M
        (fun I => PoissonCoefficients.dual K S D z I.val) q := by
  let b := PoissonCoefficients.dual K S D z
  let F := fun (I J : ExteriorIdeal K S) (q : Q) =>
    if IsCoprime I.val.val J.val.val then b I * star (b J) * dualTerm A D M hM I J q else 0
  have hFnorm (I J : ExteriorIdeal K S) : Summable (fun q => ‖F I J q‖) := by
    by_cases hc : IsCoprime I.val.val J.val.val
    · simpa only [F, if_pos hc, norm_mul] using
        (dualTerm_norm_summable A D M hM I J).mul_left ‖b I * star (b J)‖
    · simp only [F, if_neg hc, norm_zero]; exact summable_zero
  have hF (I J : ExteriorIdeal K S) : Summable (F I J) := (hFnorm I J).of_norm
  symm
  calc
    _ = ∑' q : Q, ∑ I ∈ T, ∑ J ∈ T, F I J q := by
      apply tsum_congr
      intro q
      let G := fun (I J : ExteriorIdeal K S) =>
        if IsCoprime I.val.val J.val.val then
          (coefficient K S D I q * b I) * star (coefficient K S D J q * b J) *
            Profile.Gaussian.rawEnvelope A
              (M * (sIntegerOrbitNorm K S (Γ K S) q).val /
                (exteriorNorm K S I * exteriorNorm K S J)) else 0
      have hterm (I J : ExteriorIdeal K S) : G I J = F I J q := by
        dsimp only [G, F]
        by_cases hc : IsCoprime I.val.val J.val.val
        · simp only [if_pos hc]
          rw [Profile.Gaussian.rawEnvelope_eq_dualProfile A _
            (div_pos (mul_pos hM (sIntegerOrbitNorm K S (Γ K S) q).property)
              (mul_pos (norm_pos A I) (norm_pos A J)))]
          simp only [dualTerm, PoissonSmoothed.pairWeight, star_mul, star_star]
          ring
        · simp only [if_neg hc]
      change (∑ I : T, ∑ J : T, G I.val J.val) = _
      calc
        _ = ∑ I ∈ T, ∑ J ∈ T, G I J := by
          rw [Finset.sum_coe_sort T (fun I => ∑ J : T, G I J.val)]
          apply Finset.sum_congr rfl
          intro I hI
          exact Finset.sum_coe_sort T (fun J => G I J)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro I hI
          apply Finset.sum_congr rfl
          intro J hJ
          exact hterm I J
    _ = ∑ I ∈ T, ∑' q : Q, ∑ J ∈ T, F I J q :=
      Summable.tsum_finsetSum (s := T) (fun I _ => summable_sum (fun J _ => hF I J))
    _ = ∑ I ∈ T, ∑ J ∈ T, ∑' q : Q, F I J q := by
      apply Finset.sum_congr rfl
      intro I hI
      exact Summable.tsum_finsetSum (s := T) (fun J _ => hF I J)
    _ = _ := by
      unfold PoissonSmoothed.dualSeries
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro J hJ
      by_cases hc : IsCoprime I.val.val J.val.val <;>
        simp [F, hc, b, PoissonSmoothed.dualPair, dualTerm, tsum_mul_left]

theorem actual_annular_bound (hD : AllowedGeneratorInput K S D) {ξ : ℝ}
    (h : Bootstrap.HasCubicExponent (ExteriorSieve.B K S D) ξ)
    (hξ : (4 / 3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδsmall : δ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, ∀ hM : 0 < M, 1 ≤ N →
      ∀ T : Finset (ExteriorIdeal K S),
        (∀ I ∈ T, Squarefree I.val.val ∧ N / 2 ≤ exteriorNorm K S I ∧ exteriorNorm K S I ≤ N) →
        ∀ z : ExteriorIdeal K S → ℂ,
        ‖PoissonSmoothed.sourceSeries A D M hM T z‖ ≤
          C * (M + N ^ (ε + 3 * δ) * M ^ (-δ) *
            ((M * N) ^ (2 / 3 : ℝ) + M ^ (1 - ξ) * N ^ (2 * ξ - 1))) *
              ∑ I ∈ T, ‖z I‖ ^ 2 := by
  obtain ⟨Ct, hCt, ht⟩ := PoissonTail.actual_tail A D hD h hξ hξ2 ε δ hε hδ hδsmall
  let P := AnalyticDecay.decayConstant (1 / 3 + δ - 1 / 6)
  let Qc := AnalyticDecay.decayConstant (ξ + δ - 1 / 6)
  let L : ℝ := 1 + |P| + |Qc|
  let H : ℝ := ‖PoissonSmoothed.archConstant K‖ * ‖HeckeAxiom.ProbeTestChoice.kappa A‖
  have hL : 0 < L := by dsimp [L]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hO : 0 ≤ PoissonSmoothed.originConstant A := by
    unfold PoissonSmoothed.originConstant; positivity
  let C := 1 + 2 * H * Ct * L + PoissonSmoothed.originConstant A
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro M N hM hN T hT z
  have hN0 : 0 < N := by linarith
  let E := ∑ I ∈ T, ‖z I‖ ^ 2
  let Eb := ∑ I ∈ T, ‖PoissonCoefficients.dual K S D z I‖ ^ 2
  let Frow := PoissonTail.row A D T M (fun I => PoissonCoefficients.dual K S D z I.val)
  let U : ℝ := ∑' q : Q, ‖Frow q‖
  let X := (M * N) ^ (2 / 3 : ℝ)
  let Y := M ^ (1 - ξ) * N ^ (2 * ξ - 1)
  let R := N ^ (ε + 3 * δ) * M ^ (-δ) * (X + Y)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hEb : 0 ≤ Eb := by dsimp [Eb]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨hs, hb⟩ := ht M N hM hN T (fun I hI => ⟨(hT I hI).1, (hT I hI).2.2⟩)
    (fun I => PoissonCoefficients.dual K S D z I.val)
  rw [Finset.sum_coe_sort T (fun I => ‖PoissonCoefficients.dual K S D z I‖ ^ 2)] at hb
  replace hb : (M / N) * U ≤ Ct * N ^ (ε + 3 * δ) * M ^ (-δ) *
      (P * X + Qc * Y) * Eb := by
    convert hb using 1 <;> dsimp only [U, Frow, P, Qc, X, Y, Eb] <;> ring
  have hPQ : P * X + Qc * Y ≤ L * (X + Y) := by
    have hP : P ≤ L := (le_abs_self P).trans (by dsimp [L]; linarith [abs_nonneg Qc])
    have hQ : Qc ≤ L := (le_abs_self Qc).trans (by dsimp [L]; linarith [abs_nonneg P])
    calc
      _ ≤ L * X + L * Y := add_le_add (mul_le_mul_of_nonneg_right hP hX)
        (mul_le_mul_of_nonneg_right hQ hY)
      _ = _ := by ring
  have hb' : (M / N) * U ≤ Ct * L * R * Eb := by
    apply hb.trans
    calc
      _ ≤ Ct * N ^ (ε + 3 * δ) * M ^ (-δ) * (L * (X + Y)) * Eb :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPQ (by positivity)) hEb
      _ = _ := by dsimp [R]; ring
  have he : Eb ≤ (2 / N) * E := PoissonCoefficients.annular_energy K S D T N hN0
    (fun I hI => ⟨(hT I hI).1, (hT I hI).2.1⟩) z
  have hscaled : M * U ≤ 2 * Ct * L * R * E := by
    calc
      _ = N * ((M / N) * U) := by field_simp [hN0.ne']
      _ ≤ N * (Ct * L * R * Eb) := mul_le_mul_of_nonneg_left hb' hN0.le
      _ = (N * (Ct * L * R)) * Eb := by ring
      _ ≤ (N * (Ct * L * R)) * ((2 / N) * E) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by field_simp [hN0.ne']
  have hd : ‖PoissonSmoothed.dualSeries A D M hM T z‖ ≤ U := by
    rw [dualSeries_eq_tsum A D M hM T z]
    exact norm_tsum_le_tsum_norm hs
  have hn : ‖PoissonSmoothed.scaleScalar K M * HeckeAxiom.ProbeTestChoice.kappa A‖ = M * H := by
    simp [PoissonSmoothed.scaleScalar, H, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hM, mul_assoc]
  have ho := PoissonSmoothed.originSeries_norm_le A D M hM T (fun I hI => (hT I hI).1) z
  calc
    _ ≤ ‖PoissonSmoothed.scaleScalar K M * HeckeAxiom.ProbeTestChoice.kappa A‖ *
        ‖PoissonSmoothed.dualSeries A D M hM T z‖ + ‖PoissonSmoothed.originSeries A D M T z‖ := by
      rw [PoissonSmoothed.smoothed_coprime_gram A D hD M hM T (fun I hI => (hT I hI).1) z]
      simpa only [norm_mul] using norm_add_le
        ((PoissonSmoothed.scaleScalar K M * HeckeAxiom.ProbeTestChoice.kappa A) *
          PoissonSmoothed.dualSeries A D M hM T z) (PoissonSmoothed.originSeries A D M T z)
    _ ≤ (M * H) * U + PoissonSmoothed.originConstant A * M * E := by
      rw [hn]
      exact add_le_add (mul_le_mul_of_nonneg_left hd (by positivity)) ho
    _ = H * (M * U) + PoissonSmoothed.originConstant A * M * E := by ring
    _ ≤ H * (2 * Ct * L * R * E) + PoissonSmoothed.originConstant A * M * E :=
      add_le_add (mul_le_mul_of_nonneg_left hscaled hH) le_rfl
    _ = (2 * H * Ct * L * R + PoissonSmoothed.originConstant A * M) * E := by ring
    _ ≤ C * (M + R) * E := by
      apply mul_le_mul_of_nonneg_right _ hE
      dsimp [C]
      nlinarith [mul_nonneg (show 0 ≤ 2 * H * Ct * L by positivity) hM.le,
        mul_nonneg hO hR]

end CubicSieve.PoissonEstimate
