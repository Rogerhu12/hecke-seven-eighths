import HeckeSkeleton.GramAssembly.Aggregate
import HeckeSkeleton.GramDefinitions

/-!
GR-12-ASSEMBLY, final step: the nonzero dual row-ball series is bounded by the
Gram scale.  Summability and the total bound of the residual majorant come from
the partial-sum bound over finite sets of frequency orbits; the dual series is
then estimated by Step B, and the explicit expression is compared with
`gramScale`.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.GramAssembly.Final

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open AlgebraicNumberTheory.PowerResidueSymbols
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.ActualGeneratorDivisionDraft
open HeckeGeneral.ThetaSkeleton.Global.ActualGcdMobiusDraft
open ActualProbeGaussFourierDraft ActualProbePairNormDraft ActualAdditiveGramDraft
open ActualGramJointChartDraft ActualGramJointChartCoverDraft
open ActualGramMajorantDraft ActualRowBallDualChartDraft
open ActualDenominatorGramWeightDraft ActualRowBallResidualAnalyticDraft
open ActualRowBallResidualMaskedDraft ActualAllowedTotalNormProviderDraft
open ActualChoiceMaskedTotalNormDraft ActualGeneratorChoiceDraft ActualGramJointMeanDraft
open HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallResidualGoodPrimeDraft
open HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallResidualScalarDraft
open HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallDualResidualNormDraft
open HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallResidualTrivialDraft
open HeckeGeneral.Analysis.ActualGramExceptionalCountDraft HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.ActualExceptionalWeightedShellDraft HeckeGeneral.Analysis.ActualOrdinaryOrbitShellCountDraft
open HeckeSkeleton.GramAssembly.Bookkeeping HeckeSkeleton.GramAssembly.Aggregate
open scoped Classical BigOperators ContDiff nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (w : GeneratorMaskWitness K)
local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "E" => ExteriorIdeal K S
local notation "NZ" => NonzeroRingElements (Set.integer S K)
local notation "gen" => probeGenerator K S w.D
local notation "Orb" => SIntegerOrbits K S (sixthPowerUnits K S)

variable [MeasurableSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (μf : Measure (FiniteAdeleRing (𝓞 K) K)) [μf.IsAddHaarMeasure]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
variable [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
variable [∀ v, (μv v).IsAddHaarMeasure]
variable (P : ProbeData K (w.S : Set (HeightOneSpectrum (𝓞 K))))

theorem residualMajorant_nonneg (Y η : ℝ) (r : {r : ℝ // 0 < r}) (q : Orb) :
    0 ≤ residualMajorant K w μv P Y η r q := by
  unfold residualMajorant
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))

/-- Summability and the total bound of the residual majorant. -/
theorem majorant_tsum_le (hP : P.arithmetic = w.D) (Bg Bt K1 : ℝ) (Jg Jt J : ℕ)
    (hgood : GoodScalar K w μv P Bg Jg) (htriv : TrivScalar K w μv P Bt Jt)
    (hBg : 0 ≤ Bg) (hBt : 0 ≤ Bt) (hg : Bg ≤ K1) (ht : Bt ≤ K1) (hJg : Jg ≤ J) (hJt : Jt ≤ J)
    (c0 : ℝ) (hc0 : 0 ≤ c0)
    (hdiv : ∀ (C : E) (T : ℝ), 0 < T → ∀ G : Finset Orb,
      (∀ q ∈ G, w.D.generator C ∣ q.out.val ∧
        (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val ≤ T) →
      (G.card : ℝ) ≤ c0 * T / exteriorNorm K S C)
    (C0e : ℝ) (hC0e : 0 ≤ C0e)
    (hexc : ∀ (A D : Finset (NonzeroIdeal K)) (Q Y T M : ℝ), 0 < Q → 0 < Y → 0 < T → 0 ≤ M →
      (Q / Y ^ 3) * M * (∑ C ∈ A, ∑ d ∈ D, exceptionalShellColumnMass K S C d Y T) ≤
        C0e * M * (Q / Y) * T ^ (1 / 6 : ℝ))
    (C9 : ℝ) (hC9 : 0 < C9)
    (h9 : ∀ Λ : ℝ, 0 < Λ →
      Summable (fun IJ : NonzeroIdeal K × NonzeroIdeal K =>
        (idealNorm K IJ.1) ^ (-(2 : ℝ)) * (idealNorm K IJ.2) ^ (-(2 : ℝ)) *
          min 1 ((idealNorm K IJ.1 * idealNorm K IJ.2 / Λ) ^ 3)) ∧
      (∑' IJ : NonzeroIdeal K × NonzeroIdeal K,
        (idealNorm K IJ.1) ^ (-(2 : ℝ)) * (idealNorm K IJ.2) ^ (-(2 : ℝ)) *
          min 1 ((idealNorm K IJ.1 * idealNorm K IJ.2 / Λ) ^ 3)) ≤
        C9 * (1 + Real.log (2 + Λ)) / Λ)
    (Y η : ℝ) (hY : 0 < Y) (r : {r : ℝ // 0 < r}) :
    Summable (residualMajorant K w μv P Y η r) ∧
    ∑' q, residualMajorant K w μv P Y η r q ≤
      (K1 * (1 + |η|) ^ J) *
        (C0e * Y ^ 2 * (Dyadic.Ke * (r.val * Y ^ 2) ^ (1 / 6 : ℝ)) +
         c0 * Dyadic.Ko * C9 * (r.val * Y ^ 2) ^ 2 * Y *
          (1 + Real.log (2 + Y / (r.val * Y ^ 2)))) := by
  have hpart : ∀ F : Finset Orb, ∑ q ∈ F, residualMajorant K w μv P Y η r q ≤
      (K1 * (1 + |η|) ^ J) *
        (C0e * Y ^ 2 * (Dyadic.Ke * (r.val * Y ^ 2) ^ (1 / 6 : ℝ)) +
         c0 * Dyadic.Ko * C9 * (r.val * Y ^ 2) ^ 2 * Y *
          (1 + Real.log (2 + Y / (r.val * Y ^ 2)))) := by
    intro F
    apply majorant_partial_le K w μv P hP Bg Bt K1 Jg Jt J hgood htriv hBg hBt hg ht hJg hJt c0 hc0
      hdiv C0e hC0e hexc C9 hC9 h9 Y η hY r F
      (F.sup (fun q => Dyadic.shellIndex (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val) + 1)
    intro q hq
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun q => Dyadic.shellIndex
      (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val) hq)
  have hsum : Summable (residualMajorant K w μv P Y η r) :=
    summable_of_sum_le (fun q => residualMajorant_nonneg K w μv P Y η r q) hpart
  exact ⟨hsum, Real.tsum_le_of_sum_le (fun q => residualMajorant_nonneg K w μv P Y η r q) hpart⟩

section Arith

open HeckeSkeleton.Gram

/-- `(1 + log (2 + B Z^L))` is bounded by `Z^ε`. -/
theorem one_add_log_le (B L ε Z : ℝ) (hB : 0 < B) (hL : 0 < L) (hε : 0 < ε) (hZ : 1 ≤ Z) :
    1 + Real.log (2 + B * Z ^ L) ≤ (1 + Real.log (2 + B) + L / ε) * Z ^ ε := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hZL : 1 ≤ Z ^ L := Real.one_le_rpow hZ hL.le
  have hZe : 1 ≤ Z ^ ε := Real.one_le_rpow hZ hε.le
  have h1 : 2 + B * Z ^ L ≤ (2 + B) * Z ^ L := by nlinarith
  have hlog1 : Real.log (2 + B * Z ^ L) ≤ Real.log (2 + B) + L * Real.log Z := by
    calc Real.log (2 + B * Z ^ L) ≤ Real.log ((2 + B) * Z ^ L) :=
          Real.log_le_log (by positivity) h1
      _ = Real.log (2 + B) + L * Real.log Z := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hZ0]
  have hlog2 : Real.log Z ≤ Z ^ ε / ε := Real.log_le_rpow_div hZ0.le hε
  have hlogB : 0 ≤ Real.log (2 + B) := Real.log_nonneg (by linarith)
  have hL2 : L * Real.log Z ≤ L / ε * Z ^ ε := by
    calc L * Real.log Z ≤ L * (Z ^ ε / ε) := mul_le_mul_of_nonneg_left hlog2 hL.le
      _ = L / ε * Z ^ ε := by ring
  calc 1 + Real.log (2 + B * Z ^ L) ≤ 1 + (Real.log (2 + B) + L / ε * Z ^ ε) := by linarith
    _ ≤ (1 + Real.log (2 + B) + L / ε) * Z ^ ε := by
        have : 0 ≤ L / ε := by positivity
        nlinarith

theorem gramScale_ge_Pa (Q Y : ℝ) (hQ : 0 < Q) (hY : 0 < Y) :
    Pa Q Y ≤ gramScale Q Y := by
  unfold gramScale Pa
  have h1 : 0 ≤ (Y ^ 2 / Q) ^ (1 / 6 : ℝ) := Real.rpow_nonneg (by positivity) _
  have h2 : Q / Y * ((Y ^ 2 / Q) ^ 2 / Y) = Y ^ 2 / Q := by field_simp
  have h3 : 0 ≤ Q / Y * (Y ^ 2 / Q) ^ (1 / 6 : ℝ) := by positivity
  have h4 : 0 ≤ Q / Y := by positivity
  nlinarith

theorem gramScale_ge_root (Q Y : ℝ) (hQ : 0 < Q) (hY : 0 < Y) :
    Q / Y * (Pa Q Y) ^ (1 / 6 : ℝ) ≤ gramScale Q Y := by
  unfold gramScale Pa
  have h1 : 0 ≤ (Y ^ 2 / Q) ^ (1 / 6 : ℝ) := Real.rpow_nonneg (by positivity) _
  have h4 : 0 ≤ Q / Y := by positivity
  have h5 : 0 ≤ Q / Y * ((Y ^ 2 / Q) ^ 2 / Y) := by positivity
  nlinarith

/-- The final comparison with the Gram scale. -/
theorem final_arith (B L ε Z Q Y nf K1 C0e Ke Ko C9 c0 u : ℝ) (hB : 0 < B) (hL : 0 < L) (hε : 0 < ε)
    (hZ : 1 ≤ Z) (hQ : 1 ≤ Q) (hY : 1 ≤ Y) (hQZ : Q ≤ Z ^ L)
    (hnf : 0 ≤ nf) (hK1 : 0 ≤ K1) (hC0e : 0 ≤ C0e) (hKe : 0 ≤ Ke) (hKo : 0 ≤ Ko)
    (hC9 : 0 ≤ C9) (hc0 : 0 ≤ c0) (hu : 1 ≤ u) :
    ((B * Q) * Y ^ (-(3 : ℝ)) * nf) *
      ((K1 * u) * (C0e * Y ^ 2 * (Ke * (((B * Q)⁻¹) * Y ^ 2) ^ (1 / 6 : ℝ)) +
        c0 * Ko * C9 * (((B * Q)⁻¹) * Y ^ 2) ^ 2 * Y *
          (1 + Real.log (2 + Y / (((B * Q)⁻¹) * Y ^ 2))))) ≤
    (nf * K1 * (C0e * Ke * B ^ (5 / 6 : ℝ) + c0 * Ko * C9 * B⁻¹ * (1 + Real.log (2 + B) + L / ε)) + 1)
      * u * gramScale Q Y * Z ^ ε := by
  have hY0 : 0 < Y := by linarith
  have hQ0 : 0 < Q := by linarith
  have hBQ : 0 < B * Q := mul_pos hB hQ0
  have hZ0 : 0 < Z := by linarith
  set a : ℝ := ((B * Q)⁻¹) * Y ^ 2 with ha
  have ha0 : 0 < a := by positivity
  have hPa0 : 0 < Pa Q Y := by unfold Pa; positivity
  have haP : a = Pa Q Y / B := by
    rw [ha]; unfold Pa; field_simp
  have hG0 : 0 ≤ gramScale Q Y := (hPa0.le).trans (gramScale_ge_Pa Q Y hQ0 hY0)
  have hZe : 1 ≤ Z ^ ε := Real.one_le_rpow hZ hε.le
  have hY3 : Y ^ (-(3 : ℝ)) = (Y ^ 3)⁻¹ := by
    rw [Real.rpow_neg hY0.le]; norm_cast
  -- first term
  have hc1 : (B * Q) * Y ^ (-(3 : ℝ)) * Y ^ 2 * a ^ (1 / 6 : ℝ) ≤ B ^ (5 / 6 : ℝ) * gramScale Q Y := by
    have e1 : (B * Q) * Y ^ (-(3 : ℝ)) * Y ^ 2 * a ^ (1 / 6 : ℝ) =
        (B / B ^ (1 / 6 : ℝ)) * (Q / Y * Pa Q Y ^ (1 / 6 : ℝ)) := by
      rw [haP, Real.div_rpow hPa0.le hB.le, hY3]
      field_simp
    have e2 : B / B ^ (1 / 6 : ℝ) = B ^ (5 / 6 : ℝ) := by
      have := Real.rpow_sub hB 1 (1 / 6 : ℝ)
      rw [Real.rpow_one] at this
      rw [← this]; norm_num
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left (gramScale_ge_root Q Y hQ0 hY0) (by positivity)
  -- second term
  have hc2 : (B * Q) * Y ^ (-(3 : ℝ)) * a ^ 2 * Y = a := by
    rw [hY3, ha]; field_simp
  have hc2' : a ≤ B⁻¹ * gramScale Q Y := by
    rw [haP]
    calc Pa Q Y / B = B⁻¹ * Pa Q Y := by ring
      _ ≤ B⁻¹ * gramScale Q Y :=
          mul_le_mul_of_nonneg_left (gramScale_ge_Pa Q Y hQ0 hY0) (inv_nonneg.mpr hB.le)
  have hc3 : 1 + Real.log (2 + Y / a) ≤ (1 + Real.log (2 + B) + L / ε) * Z ^ ε := by
    have hYa : Y / a = B * Q / Y := by rw [ha]; field_simp
    have hle : Y / a ≤ B * Z ^ L := by
      rw [hYa]
      calc B * Q / Y ≤ B * Q := div_le_self (by positivity) hY
        _ ≤ B * Z ^ L := mul_le_mul_of_nonneg_left hQZ hB.le
    have hpos : 0 < 2 + Y / a := by positivity
    calc 1 + Real.log (2 + Y / a) ≤ 1 + Real.log (2 + B * Z ^ L) := by
          have := Real.log_le_log hpos (by linarith : 2 + Y / a ≤ 2 + B * Z ^ L)
          linarith
      _ ≤ _ := one_add_log_le B L ε Z hB hL hε hZ
  -- assembly
  have hX : 0 ≤ 1 + Real.log (2 + B) + L / ε := by
    have : 0 ≤ Real.log (2 + B) := Real.log_nonneg (by linarith)
    have : 0 ≤ L / ε := by positivity
    linarith
  set X : ℝ := 1 + Real.log (2 + B) + L / ε with hXdef
  have hlogY : 0 ≤ 1 + Real.log (2 + Y / a) := by
    have : 0 ≤ Real.log (2 + Y / a) := Real.log_nonneg (by have : 0 < Y / a := by positivity
                                                           linarith)
    linarith
  have hT1 : (B * Q) * Y ^ (-(3 : ℝ)) * (C0e * Y ^ 2 * (Ke * a ^ (1 / 6 : ℝ))) ≤
      C0e * Ke * B ^ (5 / 6 : ℝ) * gramScale Q Y * Z ^ ε := by
    have : (B * Q) * Y ^ (-(3 : ℝ)) * (C0e * Y ^ 2 * (Ke * a ^ (1 / 6 : ℝ))) =
        C0e * Ke * ((B * Q) * Y ^ (-(3 : ℝ)) * Y ^ 2 * a ^ (1 / 6 : ℝ)) := by ring
    rw [this]
    calc C0e * Ke * ((B * Q) * Y ^ (-(3 : ℝ)) * Y ^ 2 * a ^ (1 / 6 : ℝ))
        ≤ C0e * Ke * (B ^ (5 / 6 : ℝ) * gramScale Q Y) :=
          mul_le_mul_of_nonneg_left hc1 (mul_nonneg hC0e hKe)
      _ = C0e * Ke * B ^ (5 / 6 : ℝ) * gramScale Q Y * 1 := by ring
      _ ≤ C0e * Ke * B ^ (5 / 6 : ℝ) * gramScale Q Y * Z ^ ε :=
          mul_le_mul_of_nonneg_left hZe (by positivity)
  have hT2 : (B * Q) * Y ^ (-(3 : ℝ)) * (c0 * Ko * C9 * a ^ 2 * Y * (1 + Real.log (2 + Y / a))) ≤
      c0 * Ko * C9 * B⁻¹ * X * gramScale Q Y * Z ^ ε := by
    have : (B * Q) * Y ^ (-(3 : ℝ)) * (c0 * Ko * C9 * a ^ 2 * Y * (1 + Real.log (2 + Y / a))) =
        c0 * Ko * C9 * ((B * Q) * Y ^ (-(3 : ℝ)) * a ^ 2 * Y) * (1 + Real.log (2 + Y / a)) := by ring
    rw [this, hc2]
    have hcc : 0 ≤ c0 * Ko * C9 := by positivity
    calc c0 * Ko * C9 * a * (1 + Real.log (2 + Y / a))
        ≤ c0 * Ko * C9 * (B⁻¹ * gramScale Q Y) * (X * Z ^ ε) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hc2' hcc) hc3 hlogY
            (mul_nonneg hcc (mul_nonneg (inv_nonneg.mpr hB.le) hG0))
      _ = c0 * Ko * C9 * B⁻¹ * X * gramScale Q Y * Z ^ ε := by ring
  have hpref : 0 ≤ nf * K1 * u := by
    have : 0 ≤ u := by linarith
    positivity
  calc ((B * Q) * Y ^ (-(3 : ℝ)) * nf) * ((K1 * u) * (C0e * Y ^ 2 * (Ke * a ^ (1 / 6 : ℝ)) +
          c0 * Ko * C9 * a ^ 2 * Y * (1 + Real.log (2 + Y / a))))
      = (nf * K1 * u) * ((B * Q) * Y ^ (-(3 : ℝ)) * (C0e * Y ^ 2 * (Ke * a ^ (1 / 6 : ℝ))) +
          (B * Q) * Y ^ (-(3 : ℝ)) * (c0 * Ko * C9 * a ^ 2 * Y * (1 + Real.log (2 + Y / a)))) := by
        ring
    _ ≤ (nf * K1 * u) * (C0e * Ke * B ^ (5 / 6 : ℝ) * gramScale Q Y * Z ^ ε +
          c0 * Ko * C9 * B⁻¹ * X * gramScale Q Y * Z ^ ε) :=
        mul_le_mul_of_nonneg_left (add_le_add hT1 hT2) hpref
    _ = (nf * K1 * (C0e * Ke * B ^ (5 / 6 : ℝ) + c0 * Ko * C9 * B⁻¹ * X)) * u * gramScale Q Y * Z ^ ε := by
        ring
    _ ≤ (nf * K1 * (C0e * Ke * B ^ (5 / 6 : ℝ) + c0 * Ko * C9 * B⁻¹ * X) + 1) * u * gramScale Q Y * Z ^ ε := by
        have h0 : 0 ≤ u * gramScale Q Y * Z ^ ε := by
          have : 0 ≤ u := by linarith
          positivity
        nlinarith

end Arith


include μf in
/-- Step B: the nonzero dual row-ball series (with its exact prefactor) is bounded by
the prefactor times the total of the residual majorant. -/
theorem norm_dualSeriesTerm_le (Y η : ℝ) (hY : 0 < Y) (r : {r : ℝ // 0 < r})
    (hsum : Summable (residualMajorant K w μv P Y η r)) :
    ‖rowBallDualSeriesTerm K w.S μv P (fun _ => 1) P.denominator.toSmoothAnnularTest Y η r‖ ≤
      (r.val⁻¹ * Y ^ (-3 : ℝ) * ‖additiveGramPoissonFieldFactor K‖) *
        ∑' q, residualMajorant K w μv P Y η r q := by
  have hsixth : Subgroup.FiniteIndex (sixthPowerUnits K (w.S : Set (HeightOneSpectrum (𝓞 K)))) :=
    sUnit_power_range_finiteIndex K (w.S : Set (HeightOneSpectrum (𝓞 K))) 6 (by decide)
  haveI := hsixth
  have hone := rowBallDualSeriesTerm_one_eq_tsum K w.S μv μf P
    P.denominator.toSmoothAnnularTest Y η r
  rw [hone, norm_mul]
  have hpref : ‖((r.val : ℂ)⁻¹ * ((Y ^ (-3 : ℝ) : ℝ) : ℂ) * additiveGramPoissonFieldFactor K)‖ =
      r.val⁻¹ * Y ^ (-3 : ℝ) * ‖additiveGramPoissonFieldFactor K‖ := by
    rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg r.property.le,
      Real.norm_of_nonneg (Real.rpow_nonneg hY.le _)]
  rw [hpref]
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (mul_nonneg (inv_nonneg.mpr r.property.le) (Real.rpow_nonneg hY.le _))
      (norm_nonneg _))
  have hle : ∀ q, ‖rowBallDualIntegrand K w.S μv P P.denominator.toSmoothAnnularTest Y η r q‖ ≤
      residualMajorant K w μv P Y η r q := fun q =>
    norm_rowBallDualIntegrand_le_actualDivisors K w μv P Y η r q
  have hnormsum : Summable (fun q => ‖rowBallDualIntegrand K w.S μv P
      P.denominator.toSmoothAnnularTest Y η r q‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum
  exact (norm_tsum_le_tsum_norm hnormsum).trans (hnormsum.tsum_le_tsum hle hsum)

include μf in
/-- The nonzero dual series is bounded by the Gram scale (the `DualShellBound`). -/
theorem dualShell_core (hP : P.arithmetic = w.D)
    (leaf09 : ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℝ, 0 < Λ →
      Summable (fun IJ : NonzeroIdeal K × NonzeroIdeal K =>
        (idealNorm K IJ.1) ^ (-(2 : ℝ)) * (idealNorm K IJ.2) ^ (-(2 : ℝ)) *
          min 1 ((idealNorm K IJ.1 * idealNorm K IJ.2 / Λ) ^ 3)) ∧
      (∑' IJ : NonzeroIdeal K × NonzeroIdeal K,
        (idealNorm K IJ.1) ^ (-(2 : ℝ)) * (idealNorm K IJ.2) ^ (-(2 : ℝ)) *
          min 1 ((idealNorm K IJ.1 * idealNorm K IJ.2 / Λ) ^ 3)) ≤
        C * (1 + Real.log (2 + Λ)) / Λ) :
    ∀ B L : ℝ, 0 < B → 0 < L → ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧
      ∀ (Z Q Y ν : ℝ), Z₀ ≤ Z → 1 ≤ Q → 1 ≤ Y → Q ≤ Z ^ L → Y ≤ Z ^ L →
        1 ≤ HeckeSkeleton.Gram.Pa Q Y → ∀ hBQ : 0 < B * Q,
          ‖rowBallDualSeriesTerm K w.S μv P (fun _ => 1) P.denominator.toSmoothAnnularTest Y ν
              ⟨(B * Q)⁻¹, inv_pos.mpr hBQ⟩‖ ≤
            C * (1 + |ν|) ^ J * HeckeSkeleton.Gram.gramScale Q Y * Z ^ ε := by
  obtain ⟨Bg, Jg, hBg, hgood⟩ := exists_rowBallResidual_goodPrime_scalar_bound K w μf μv P hP 3
    (by norm_num) (1 / 12) 5 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Bt, Jt, hBt, htriv⟩ := exists_rowBallResidual_trivial_scalar_bound K w μf μv P hP
    (1 / 12) 5 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c0, hc0, hdiv0⟩ := exists_divisible_ordinaryOrbit_finset_count K S
  obtain ⟨C0e, hC0e, hexc0⟩ := exists_exceptional_weighted_shell_bound K S
    (δ := 1 / 12) (by norm_num) (by norm_num)
  obtain ⟨C9, hC9, h9⟩ := leaf09
  have hdiv : ∀ (C : E) (T : ℝ), 0 < T → ∀ G : Finset Orb,
      (∀ q ∈ G, w.D.generator C ∣ q.out.val ∧
        (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val ≤ T) →
      (G.card : ℝ) ≤ c0 * T / exteriorNorm K S C := by
    intro C T hT G hG
    have := hdiv0 P (gen C) T hT G hG
    rwa [probeGenerator_norm_eq_exteriorNorm] at this
  have hexc : ∀ (A D : Finset (NonzeroIdeal K)) (Q Y T M : ℝ), 0 < Q → 0 < Y → 0 < T → 0 ≤ M →
      (Q / Y ^ 3) * M * (∑ C ∈ A, ∑ d ∈ D, exceptionalShellColumnMass K S C d Y T) ≤
        C0e * M * (Q / Y) * T ^ (1 / 6 : ℝ) :=
    fun A D Q Y T M hQ hY hT hM => hexc0 P A D Q Y T M hQ hY hT hM
  intro B L hB hL ε hε
  set K1 : ℝ := max Bg Bt with hK1
  set J : ℕ := max Jg Jt with hJ
  set nf : ℝ := ‖additiveGramPoissonFieldFactor K‖ with hnf
  have hnf0 : 0 ≤ nf := norm_nonneg _
  have hK10 : 0 ≤ K1 := hBg.trans (le_max_left _ _)
  have hKe : 0 ≤ Dyadic.Ke := by
    unfold Dyadic.Ke
    have h1 : (1 : ℝ) < 2 ^ (1 / 12 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
    have h2 : (2 : ℝ) ^ (-(29 / 6 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    have : 0 ≤ 1 / ((2 : ℝ) ^ (1 / 12 : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
    have : 0 ≤ 1 / (1 - (2 : ℝ) ^ (-(29 / 6 : ℝ))) := div_nonneg zero_le_one (by linarith)
    positivity
  have hKo := Dyadic.Ko_nonneg
  refine ⟨J, nf * K1 * (C0e * Dyadic.Ke * B ^ (5 / 6 : ℝ) + c0 * Dyadic.Ko * C9 * B⁻¹ *
      (1 + Real.log (2 + B) + L / ε)) + 1, 1, ?_, le_rfl, ?_⟩
  · have : 0 ≤ nf * K1 * (C0e * Dyadic.Ke * B ^ (5 / 6 : ℝ) + c0 * Dyadic.Ko * C9 * B⁻¹ *
        (1 + Real.log (2 + B) + L / ε)) := by
      have hlogB : 0 ≤ Real.log (2 + B) := Real.log_nonneg (by linarith)
      have : 0 ≤ L / ε := by positivity
      positivity
    linarith
  intro Z Q Y ν hZ hQ hY hQZ hYZ hPa hBQ
  set r : {r : ℝ // 0 < r} := ⟨(B * Q)⁻¹, inv_pos.mpr hBQ⟩ with hr
  have hY0 : 0 < Y := by linarith
  obtain ⟨hsum, htot⟩ := majorant_tsum_le K w μv P hP Bg Bt K1 Jg Jt J hgood htriv hBg hBt
    (le_max_left _ _) (le_max_right _ _) (le_max_left _ _) (le_max_right _ _) c0 hc0.le hdiv
    C0e hC0e.le hexc C9 hC9 h9 Y ν hY0 r
  have hB1 := norm_dualSeriesTerm_le K w μf μv P Y ν hY0 r hsum
  have hnn : 0 ≤ r.val⁻¹ * Y ^ (-3 : ℝ) * nf :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr r.property.le) (Real.rpow_nonneg hY0.le _)) hnf0
  have hmain := final_arith B L ε Z Q Y nf K1 C0e Dyadic.Ke Dyadic.Ko C9 c0 ((1 + |ν|) ^ J)
    hB hL hε (by linarith) hQ hY hQZ hnf0 hK10 hC0e.le hKe hKo hC9.le hc0.le
    (one_le_pow₀ (by linarith [abs_nonneg ν]))
  calc _ ≤ (r.val⁻¹ * Y ^ (-3 : ℝ) * nf) * ∑' q, residualMajorant K w μv P Y ν r q := hB1
    _ ≤ (r.val⁻¹ * Y ^ (-3 : ℝ) * nf) * ((K1 * (1 + |ν|) ^ J) *
        (C0e * Y ^ 2 * (Dyadic.Ke * (r.val * Y ^ 2) ^ (1 / 6 : ℝ)) +
         c0 * Dyadic.Ko * C9 * (r.val * Y ^ 2) ^ 2 * Y *
          (1 + Real.log (2 + Y / (r.val * Y ^ 2))))) := mul_le_mul_of_nonneg_left htot hnn
    _ ≤ _ := by
        have hrv : r.val⁻¹ = B * Q := by rw [hr]; simp
        rw [hrv]
        simpa [hr] using hmain

end HeckeSkeleton.GramAssembly.Final
