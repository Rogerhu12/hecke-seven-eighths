import HeckeSkeleton.GramDefinitions
import ActualGramRowBallPoissonReduction
import ActualRowBallResidualGoodPrimeBound

/-!
GR-12-ASSEMBLY (work in progress): decomposition of the coarse assembly
`HeckeSkeleton.Gram.gram_assembly` into explicit steps.

Step A: the literal skeleton `rowEnergy` of the actual physical denominator is
bounded by the nonzero dual row-ball series plus the zero-frequency `C Q / Y`,
via the core theorem `exists_actualGram_rowBall_reduction`.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.GramAssembly
open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft
open HeckeSkeleton.Gram
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (T : Finset (HeightOneSpectrum (𝓞 K)))

/-- The skeleton orbit amplitude is the core `c = 1` orbit amplitude. -/
theorem orbitAmplitude_eq_core (P : ProbeData K (T : Set (HeightOneSpectrum (𝓞 K))))
    (W : SmoothAnnularTest) (Y ν : ℝ) (q : Orbit K (T : Set (HeightOneSpectrum (𝓞 K)))) :
    orbitAmplitude K (T : Set (HeightOneSpectrum (𝓞 K))) P W Y ν q =
      actualAdditiveGramOrbitAmplitude K (T : Set (HeightOneSpectrum (𝓞 K))) P
        (fun _ => 1) W Y ν q := by
  conv_rhs => rw [← Quotient.out_eq q]
  simp only [actualAdditiveGramOrbitAmplitude, Quotient.lift_mk, orbitAmplitude, amplitude,
    actualAdditiveGramAmplitude, additiveGramCentralNormalization, gramTerm,
    actualAdditiveGramTerm, one_mul]


section StepA
variable [MeasurableSpace (sLocalNormOneGroup K (T : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (T : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (μf : Measure (FiniteAdeleRing (𝓞 K) K)) [μf.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

local instance stepA_sixthUnits_finiteIndex :
    Subgroup.FiniteIndex (sixthPowerUnits K (T : Set (HeightOneSpectrum (𝓞 K)))) :=
  sUnit_power_range_finiteIndex K (T : Set (HeightOneSpectrum (𝓞 K))) 6 (by decide)

include μ μf in
/-- Step A. The skeleton row energy over the scaled original row ball
`norm ≤ B * Q` is bounded by the nonzero dual row-ball series at radius
`(B * Q)⁻¹` plus the zero-frequency term `C * (B * Q) / Y`, for `Y ≥ Y₀`.
The orbit finiteness is the ordinary frequency count (GR-06). -/
theorem rowEnergy_le_dual_add_zero
    (hfin : ∀ X : ℝ, 0 < X → Finite (ordinaryCutoff K (T : Set (HeightOneSpectrum (𝓞 K))) X))
    (W : SmoothAnnularTest) :
    ∃ C Y₀ : ℝ, 0 < C ∧ 1 ≤ Y₀ ∧
      ∀ (P : ProbeData K (T : Set (HeightOneSpectrum (𝓞 K)))) (B Q Y ν : ℝ)
        (hBQ : 0 < B * Q), Y₀ ≤ Y →
        rowEnergy K (T : Set (HeightOneSpectrum (𝓞 K))) P W B Q Y ν ≤
          (sUnitHaarCovolume K (T : Set (HeightOneSpectrum (𝓞 K)))
              (sixthPowerUnits K (T : Set (HeightOneSpectrum (𝓞 K))))).toReal⁻¹ *
            ‖rowBallDualSeriesTerm K T μv P (fun _ => 1) W Y ν
              ⟨(B * Q)⁻¹, inv_pos.mpr hBQ⟩‖ + C * (B * Q) / Y := by
  obtain ⟨C, Y₀, hC, hY₀, h⟩ := exists_actualGram_rowBall_reduction K T μv μf μ W
  refine ⟨C, Y₀, hC, hY₀, fun P B Q Y ν hBQ hY => ?_⟩
  have hfs : Set.Finite {q : Orbit K (T : Set (HeightOneSpectrum (𝓞 K))) |
      (sIntegerOrbitNorm K (T : Set (HeightOneSpectrum (𝓞 K)))
        (sixthPowerUnits K (T : Set (HeightOneSpectrum (𝓞 K)))) q).val ≤ B * Q} :=
    Set.finite_coe_iff.mp (hfin (B * Q) hBQ)
  let F := hfs.toFinset
  have hF : ∀ q ∈ F, (sIntegerOrbitNorm K (T : Set (HeightOneSpectrum (𝓞 K)))
      (sixthPowerUnits K (T : Set (HeightOneSpectrum (𝓞 K)))) q).val ≤ B * Q := by
    intro q hq
    exact (Set.Finite.mem_toFinset hfs).mp hq
  have hrow : rowEnergy K (T : Set (HeightOneSpectrum (𝓞 K))) P W B Q Y ν =
      ∑ q ∈ F, ‖actualAdditiveGramOrbitAmplitude K (T : Set (HeightOneSpectrum (𝓞 K))) P
        (fun _ => 1) W Y ν q‖ ^ 2 := by
    unfold rowEnergy
    rw [tsum_eq_sum (s := F)]
    · apply Finset.sum_congr rfl
      intro q hq
      rw [if_pos (hF q hq), orbitAmplitude_eq_core]
    · intro q hq
      have : ¬ ((sIntegerOrbitNorm K (T : Set (HeightOneSpectrum (𝓞 K)))
          (sixthPowerUnits K (T : Set (HeightOneSpectrum (𝓞 K)))) q).val ≤ B * Q) :=
        fun h' => hq ((Set.Finite.mem_toFinset hfs).mpr h')
      rw [if_neg this]
  rw [hrow]
  exact h P (fun _ => 1) (fun _ => by simp) (B * Q) Y ν hBQ hY F hF

end StepA


section Combine
variable [MeasurableSpace (sLocalNormOneGroup K (T : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (T : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (μf : Measure (FiniteAdeleRing (𝓞 K) K)) [μf.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

local instance combine_sixthUnits_finiteIndex :
    Subgroup.FiniteIndex (sixthPowerUnits K (T : Set (HeightOneSpectrum (𝓞 K)))) :=
  sUnit_power_range_finiteIndex K (T : Set (HeightOneSpectrum (𝓞 K))) 6 (by decide)

/-- OBLIGATION (nonzero dual series). The nonzero dual row-ball series at
radius `(B Q)⁻¹`, with its exact prefactor `r⁻¹ Y⁻³ · field factor`, is bounded
by the Gram scale. This is the weighted ideal/orbit shell summation fed by the
consumer bounds `exists_rowBallResidual_goodPrime_scalar_bound` (non-exceptional
frequencies), `exists_rowBallResidual_trivial_scalar_bound` (exceptional ones) and
the counting leaves. -/
def DualShellBound (P : ProbeData K (T : Set (HeightOneSpectrum (𝓞 K)))) : Prop :=
  ∀ B L : ℝ, 0 < B → 0 < L → ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧
    ∀ (Z Q Y ν : ℝ), Z₀ ≤ Z → 1 ≤ Q → 1 ≤ Y → Q ≤ Z ^ L → Y ≤ Z ^ L → 1 ≤ Pa Q Y →
      ∀ hBQ : 0 < B * Q,
        ‖rowBallDualSeriesTerm K T μv P (fun _ => 1) P.denominator.toSmoothAnnularTest Y ν
            ⟨(B * Q)⁻¹, inv_pos.mpr hBQ⟩‖ ≤
          C * (1 + |ν|) ^ J * gramScale Q Y * Z ^ ε

/-- OBLIGATION (bounded `Y`). For `Y` in the bounded initial interval
`[1, Y₀)` the row energy is trivially bounded: finitely many ideals and orbits
(`Q ≤ Y²`), uniformly bounded Gauss amplitudes. -/
def SmallYBound (P : ProbeData K (T : Set (HeightOneSpectrum (𝓞 K)))) : Prop :=
  ∀ Y₀ : ℝ, 1 ≤ Y₀ → ∀ B L : ℝ, 0 < B → 0 < L → ∀ ε : ℝ, 0 < ε →
    ∃ J : ℕ, ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧
      ∀ (Z Q Y ν : ℝ), Z₀ ≤ Z → 1 ≤ Q → 1 ≤ Y → Y < Y₀ → Q ≤ Z ^ L → Y ≤ Z ^ L →
        1 ≤ Pa Q Y →
        rowEnergy K (T : Set (HeightOneSpectrum (𝓞 K))) P
            P.denominator.toSmoothAnnularTest B Q Y ν ≤
          C * (1 + |ν|) ^ J * gramScale Q Y * Z ^ ε

theorem gramScale_ge (Q Y : ℝ) (hQ : 1 ≤ Q) (hY : 1 ≤ Y) (hP : 1 ≤ Pa Q Y) :
    Q / Y ≤ gramScale Q Y := by
  unfold gramScale
  have hQY : 0 ≤ Q / Y := div_nonneg (by linarith) (by linarith)
  have h1 : 0 ≤ Pa Q Y ^ (1 / 6 : ℝ) := Real.rpow_nonneg (by linarith) _
  have h2 : 0 ≤ Pa Q Y ^ 2 / Y := div_nonneg (sq_nonneg _) (by linarith)
  nlinarith

include μ μf in
/-- The refined GR-12 assembly: the Gram bound for the actual physical
denominator follows from the two explicit obligations, the ordinary orbit
count and the core reduction (Step A). -/
theorem gramBound_of_obligations
    (hfin : ∀ X : ℝ, 0 < X → Finite (ordinaryCutoff K (T : Set (HeightOneSpectrum (𝓞 K))) X))
    (P : ProbeData K (T : Set (HeightOneSpectrum (𝓞 K))))
    (hdual : DualShellBound K T μv P) (hsmall : SmallYBound K T P) :
    GramBound K (T : Set (HeightOneSpectrum (𝓞 K))) P := by
  intro B L hB hL ε hε
  obtain ⟨CA, Y₀, hCA, hY₀, hA⟩ := rowEnergy_le_dual_add_zero K T μv μf μ hfin
    P.denominator.toSmoothAnnularTest
  obtain ⟨J₁, C₁, Z₁, hC₁, hZ₁, h₁⟩ := hdual B L hB hL ε hε
  obtain ⟨J₂, C₂, Z₂, hC₂, hZ₂, h₂⟩ := hsmall Y₀ hY₀ B L hB hL ε hε
  let κ : ℝ := (sUnitHaarCovolume K (T : Set (HeightOneSpectrum (𝓞 K)))
    (sixthPowerUnits K (T : Set (HeightOneSpectrum (𝓞 K))))).toReal⁻¹
  have hκ : 0 ≤ κ := by positivity
  refine ⟨max J₁ J₂, κ * C₁ + CA * B + C₂, max Z₁ Z₂, ?_, ?_, ?_⟩
  · positivity
  · exact hZ₁.trans (le_max_left _ _)
  intro Z Q Y ν hZ hQ hY hQZ hYZ hPa
  have hZ1 : Z₁ ≤ Z := (le_max_left _ _).trans hZ
  have hZ2 : Z₂ ≤ Z := (le_max_right _ _).trans hZ
  have hZ1' : 1 ≤ Z := hZ₁.trans hZ1
  have hν : 1 ≤ 1 + |ν| := by linarith [abs_nonneg ν]
  have hpowJ : ∀ J : ℕ, J ≤ max J₁ J₂ → (1 + |ν|) ^ J ≤ (1 + |ν|) ^ max J₁ J₂ :=
    fun J hJ => pow_le_pow_right₀ hν hJ
  have hZε : 1 ≤ Z ^ ε := Real.one_le_rpow hZ1' hε.le
  have hG : 0 ≤ gramScale Q Y := (div_nonneg (by linarith) (by linarith)).trans
    (gramScale_ge Q Y hQ hY hPa)
  have hpow0 : 1 ≤ (1 + |ν|) ^ max J₁ J₂ := one_le_pow₀ hν
  set M : ℝ := (1 + |ν|) ^ max J₁ J₂ * gramScale Q Y * Z ^ ε with hM
  have hM0 : 0 ≤ M := by positivity
  have hMge : Q / Y ≤ M := by
    have := gramScale_ge Q Y hQ hY hPa
    calc Q / Y ≤ gramScale Q Y := this
      _ = 1 * gramScale Q Y * 1 := by ring
      _ ≤ M := by
        apply mul_le_mul (mul_le_mul hpow0 le_rfl hG (by linarith)) hZε zero_le_one
          (by positivity)
  have hrewrite : (κ * C₁ + CA * B + C₂) * (1 + |ν|) ^ max J₁ J₂ * gramScale Q Y * Z ^ ε =
      (κ * C₁ + CA * B + C₂) * M := by rw [hM]; ring
  rw [hrewrite]
  have hmon : ∀ (J : ℕ) (C : ℝ), 0 ≤ C → J ≤ max J₁ J₂ →
      C * (1 + |ν|) ^ J * gramScale Q Y * Z ^ ε ≤ C * M := by
    intro J C hC hJ
    have h := hpowJ J hJ
    have h' : (1 + |ν|) ^ J * gramScale Q Y * Z ^ ε ≤
        (1 + |ν|) ^ max J₁ J₂ * gramScale Q Y * Z ^ ε :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hG) (by positivity)
    calc C * (1 + |ν|) ^ J * gramScale Q Y * Z ^ ε
        = C * ((1 + |ν|) ^ J * gramScale Q Y * Z ^ ε) := by ring
      _ ≤ C * M := mul_le_mul_of_nonneg_left h' hC
  by_cases hYY : Y₀ ≤ Y
  · have hBQ : 0 < B * Q := mul_pos hB (by linarith)
    have hstep := hA P B Q Y ν hBQ hYY
    have hd := h₁ Z Q Y ν hZ1 hQ hY hQZ hYZ hPa hBQ
    have hd' : ‖rowBallDualSeriesTerm K T μv P (fun _ => 1) P.denominator.toSmoothAnnularTest Y ν
        ⟨(B * Q)⁻¹, inv_pos.mpr hBQ⟩‖ ≤ C₁ * M :=
      hd.trans (hmon J₁ C₁ hC₁.le (le_max_left _ _))
    have hY0 : 0 < Y := by linarith
    have hzero : CA * (B * Q) / Y ≤ CA * B * M := by
      calc CA * (B * Q) / Y = CA * B * (Q / Y) := by ring
        _ ≤ CA * B * M := mul_le_mul_of_nonneg_left hMge (by positivity)
    calc _ ≤ κ * ‖rowBallDualSeriesTerm K T μv P (fun _ => 1) P.denominator.toSmoothAnnularTest Y ν
          ⟨(B * Q)⁻¹, inv_pos.mpr hBQ⟩‖ + CA * (B * Q) / Y := hstep
      _ ≤ κ * (C₁ * M) + CA * B * M := add_le_add (mul_le_mul_of_nonneg_left hd' hκ) hzero
      _ ≤ _ := by nlinarith [mul_nonneg hC₂.le hM0]
  · have hYY' : Y < Y₀ := not_le.mp hYY
    have hr := h₂ Z Q Y ν hZ2 hQ hY hYY' hQZ hYZ hPa
    have := hmon J₂ C₂ hC₂.le (le_max_right _ _)
    have hk1 : 0 ≤ κ * C₁ * M := by positivity
    have hk2 : 0 ≤ CA * B * M := by positivity
    nlinarith [hr, this]

end Combine



section SmallY
variable [MeasurableSpace (sLocalNormOneGroup K (T : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (T : Set (HeightOneSpectrum (𝓞 K))))]

/-- Every nonzero term of the amplitude is bounded by the sup of the test, the
inverse of the annulus lower end, and the Gauss factor (no dependence on `ν`). -/
theorem term_norm_le (P : ProbeData K (T : Set (HeightOneSpectrum (𝓞 K))))
    (W : SmoothAnnularTest) (M : ℝ) (hM : ∀ x, ‖W.toFun x‖ ≤ M) (Y ν : ℝ) (hY : 0 < Y)
    (m : (T : Set (HeightOneSpectrum (𝓞 K))).integer K)
    (I : ExteriorIdeal K (T : Set (HeightOneSpectrum (𝓞 K)))) :
    ‖actualAdditiveGramTerm K (T : Set (HeightOneSpectrum (𝓞 K))) P (fun _ => 1) W Y ν m I‖ ≤
      M * W.lower⁻¹ * ‖probeGauss K (T : Set (HeightOneSpectrum (𝓞 K))) P I (-m)‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  by_cases hW : W.toFun (exteriorNorm K (T : Set (HeightOneSpectrum (𝓞 K))) I / Y) = 0
  · simp only [actualAdditiveGramTerm, hW, mul_zero, zero_mul, norm_zero]
    exact mul_nonneg (mul_nonneg hM0 (inv_nonneg.mpr W.lower_pos.le)) (norm_nonneg _)
  · have hmem := W.support hW
    have hx : W.lower ≤ exteriorNorm K (T : Set (HeightOneSpectrum (𝓞 K))) I / Y := hmem.1
    have hxpos : 0 < exteriorNorm K (T : Set (HeightOneSpectrum (𝓞 K))) I / Y :=
      lt_of_lt_of_le W.lower_pos hx
    have hcpow : ‖(((exteriorNorm K (T : Set (HeightOneSpectrum (𝓞 K))) I / Y : ℝ) : ℂ)) ^
        ((-1 : ℂ) + Complex.I * (ν : ℂ))‖ ≤ W.lower⁻¹ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
      have hre : ((-1 : ℂ) + Complex.I * (ν : ℂ)).re = -1 := by simp
      rw [hre, Real.rpow_neg_one]
      exact inv_anti₀ W.lower_pos hx
    simp only [actualAdditiveGramTerm, one_mul, norm_mul]
    have h1 : ‖W.toFun (exteriorNorm K (T : Set (HeightOneSpectrum (𝓞 K))) I / Y)‖ ≤ M := hM _
    have h2 := hcpow
    calc ‖W.toFun (exteriorNorm K (T : Set (HeightOneSpectrum (𝓞 K))) I / Y)‖ *
          ‖(((exteriorNorm K (T : Set (HeightOneSpectrum (𝓞 K))) I / Y : ℝ) : ℂ)) ^
            ((-1 : ℂ) + Complex.I * (ν : ℂ))‖ *
          ‖probeGauss K (T : Set (HeightOneSpectrum (𝓞 K))) P I (-m)‖
        ≤ M * W.lower⁻¹ * ‖probeGauss K (T : Set (HeightOneSpectrum (𝓞 K))) P I (-m)‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul h1 h2 (norm_nonneg _) hM0
      _ = _ := rfl

end SmallY


section SmallY2
variable [MeasurableSpace (sLocalNormOneGroup K (T : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (T : Set (HeightOneSpectrum (𝓞 K))))]

/-- For `1 ≤ Y ≤ Y₀` the amplitude of a fixed row is bounded by a quantity
depending only on `Y₀`, the test and the row (not on `Y` or `ν`). -/
theorem small_amplitude_bound (P : ProbeData K (T : Set (HeightOneSpectrum (𝓞 K))))
    (W : SmoothAnnularTest) (M : ℝ) (hM : ∀ x, ‖W.toFun x‖ ≤ M) (Y₀ Y ν : ℝ)
    (hY : 1 ≤ Y) (hYY : Y ≤ Y₀) (m : (T : Set (HeightOneSpectrum (𝓞 K))).integer K) :
    ‖actualAdditiveGramAmplitude K (T : Set (HeightOneSpectrum (𝓞 K))) P (fun _ => 1) W Y ν m‖ ≤
      M * W.lower⁻¹ * ∑ I ∈ additiveGramIdealSupport K (T : Set (HeightOneSpectrum (𝓞 K))) W Y₀,
        ‖probeGauss K (T : Set (HeightOneSpectrum (𝓞 K))) P I (-m)‖ := by
  have hY0 : 0 < Y := by linarith
  have hY₀ : 0 < Y₀ := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rw [actualAdditiveGramAmplitude_eq_sum K _ P (fun _ => 1) W Y ν hY0, norm_mul]
  have hcent : ‖additiveGramCentralNormalization Y‖ ≤ 1 := by
    unfold additiveGramCentralNormalization
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hY0.le _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hY (by norm_num)
  have hsum : ‖∑ I ∈ additiveGramIdealSupport K (T : Set (HeightOneSpectrum (𝓞 K))) W Y,
      actualAdditiveGramTerm K (T : Set (HeightOneSpectrum (𝓞 K))) P (fun _ => 1) W Y ν m I‖ ≤
      M * W.lower⁻¹ * ∑ I ∈ additiveGramIdealSupport K (T : Set (HeightOneSpectrum (𝓞 K))) W Y₀,
        ‖probeGauss K (T : Set (HeightOneSpectrum (𝓞 K))) P I (-m)‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    calc ∑ I ∈ additiveGramIdealSupport K (T : Set (HeightOneSpectrum (𝓞 K))) W Y,
          ‖actualAdditiveGramTerm K (T : Set (HeightOneSpectrum (𝓞 K))) P (fun _ => 1) W Y ν m I‖
        ≤ ∑ I ∈ additiveGramIdealSupport K (T : Set (HeightOneSpectrum (𝓞 K))) W Y,
          M * W.lower⁻¹ * ‖probeGauss K (T : Set (HeightOneSpectrum (𝓞 K))) P I (-m)‖ :=
          Finset.sum_le_sum (fun I _ => term_norm_le K T P W M hM Y ν hY0 m I)
      _ ≤ ∑ I ∈ additiveGramIdealSupport K (T : Set (HeightOneSpectrum (𝓞 K))) W Y₀,
          M * W.lower⁻¹ * ‖probeGauss K (T : Set (HeightOneSpectrum (𝓞 K))) P I (-m)‖ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro I hI
            rw [mem_additiveGramIdealSupport_iff K _ W Y hY0] at hI
            rw [mem_additiveGramIdealSupport_iff K _ W Y₀ hY₀]
            exact hI.trans (mul_le_mul_of_nonneg_left hYY
              (lt_of_lt_of_le W.lower_pos W.upper_ge).le)
          · intro I _ _
            exact mul_nonneg (mul_nonneg hM0 (inv_nonneg.mpr W.lower_pos.le)) (norm_nonneg _)
  calc _ ≤ 1 * _ := mul_le_mul hcent le_rfl (norm_nonneg _) zero_le_one
    _ ≤ _ := by rw [one_mul]; exact hsum

end SmallY2


section SmallY3
variable [MeasurableSpace (sLocalNormOneGroup K (T : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (T : Set (HeightOneSpectrum (𝓞 K))))]

/-- The bounded initial interval of `Y` (`SmallYBound`): finitely many rows and
ideals, hence a constant bound. -/
theorem smallYBound
    (hfin : ∀ X : ℝ, 0 < X → Finite (ordinaryCutoff K (T : Set (HeightOneSpectrum (𝓞 K))) X))
    (P : ProbeData K (T : Set (HeightOneSpectrum (𝓞 K)))) :
    SmallYBound K T P := by
  intro Y₀ hY₀ B L hB hL ε hε
  set W := P.denominator.toSmoothAnnularTest with hWdef
  have hcs : HasCompactSupport W.toFun := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc W.lower W.upper))
    intro x hx
    by_contra h
    exact hx (W.support h)
  obtain ⟨M, hM⟩ := W.smooth.continuous.bounded_above_of_compact_support hcs
  have hX : 0 < B * Y₀ ^ 2 := by positivity
  have hfs : Set.Finite {q : Orbit K (T : Set (HeightOneSpectrum (𝓞 K))) |
      (sIntegerOrbitNorm K (T : Set (HeightOneSpectrum (𝓞 K)))
        (sixthPowerUnits K (T : Set (HeightOneSpectrum (𝓞 K)))) q).val ≤ B * Y₀ ^ 2} :=
    Set.finite_coe_iff.mp (hfin _ hX)
  let F := hfs.toFinset
  let G : Orbit K (T : Set (HeightOneSpectrum (𝓞 K))) → ℝ := fun q =>
    M * W.lower⁻¹ * ∑ I ∈ additiveGramIdealSupport K (T : Set (HeightOneSpectrum (𝓞 K))) W Y₀,
      ‖probeGauss K (T : Set (HeightOneSpectrum (𝓞 K))) P I (-q.out.val)‖
  let C0 : ℝ := ∑ q ∈ F, (G q) ^ 2
  have hC0 : 0 ≤ C0 := Finset.sum_nonneg (fun q _ => sq_nonneg _)
  refine ⟨0, C0 * Y₀ + 1, 1, by positivity, le_rfl, ?_⟩
  intro Z Q Y ν hZ hQ hY hYY hQZ hYZ hPa
  have hQ0 : 0 < Q := by linarith
  have hQY : Q ≤ Y ^ 2 := by
    have := (one_le_div hQ0).mp hPa
    exact this
  have hQY₀ : Q ≤ Y₀ ^ 2 := by
    refine hQY.trans ?_
    exact pow_le_pow_left₀ (by linarith) hYY.le 2
  have hrow : rowEnergy K (T : Set (HeightOneSpectrum (𝓞 K))) P W B Q Y ν ≤ C0 := by
    unfold rowEnergy
    rw [tsum_eq_sum (s := F)]
    · apply Finset.sum_le_sum
      intro q hq
      split_ifs with h
      · rw [orbitAmplitude_eq_core]
        have hamp := small_amplitude_bound K T P W M hM Y₀ Y ν hY hYY.le q.out.val
        have hq' : ‖actualAdditiveGramOrbitAmplitude K (T : Set (HeightOneSpectrum (𝓞 K))) P
            (fun _ => 1) W Y ν q‖ ≤ G q := by
          conv_lhs => rw [← Quotient.out_eq q]
          simpa only [actualAdditiveGramOrbitAmplitude, Quotient.lift_mk] using hamp
        exact pow_le_pow_left₀ (norm_nonneg _) hq' 2
      · exact sq_nonneg _
    · intro q hq
      have : ¬ ((sIntegerOrbitNorm K (T : Set (HeightOneSpectrum (𝓞 K)))
          (sixthPowerUnits K (T : Set (HeightOneSpectrum (𝓞 K)))) q).val ≤ B * Q) := by
        intro h'
        apply hq
        rw [Set.Finite.mem_toFinset]
        exact h'.trans (mul_le_mul_of_nonneg_left hQY₀ hB.le)
      rw [if_neg this]
  have hY0 : 0 < Y := by linarith
  have hG := gramScale_ge Q Y hQ hY hPa
  have hZε : 1 ≤ Z ^ ε := Real.one_le_rpow hZ hε.le
  have hQYge : 1 / Y₀ ≤ Q / Y := by
    calc 1 / Y₀ ≤ 1 / Y := one_div_le_one_div_of_le hY0 hYY.le
      _ ≤ Q / Y := div_le_div_of_nonneg_right hQ hY0.le
  have hCpos : 0 ≤ C0 * Y₀ + 1 := by positivity
  calc rowEnergy K (T : Set (HeightOneSpectrum (𝓞 K))) P W B Q Y ν ≤ C0 := hrow
    _ ≤ (C0 * Y₀ + 1) * (1 / Y₀) := by
        rw [mul_one_div, add_div, mul_div_assoc, div_self (by linarith : Y₀ ≠ 0)]
        have : 0 ≤ 1 / Y₀ := by positivity
        nlinarith
    _ ≤ (C0 * Y₀ + 1) * (Q / Y) := mul_le_mul_of_nonneg_left hQYge hCpos
    _ ≤ (C0 * Y₀ + 1) * gramScale Q Y := mul_le_mul_of_nonneg_left hG hCpos
    _ ≤ (C0 * Y₀ + 1) * gramScale Q Y * Z ^ ε := by
        have h0 : 0 ≤ (C0 * Y₀ + 1) * gramScale Q Y :=
          mul_nonneg hCpos ((div_nonneg (by linarith) hY0.le).trans hG)
        nlinarith
    _ = (C0 * Y₀ + 1) * (1 + |ν|) ^ (0 : ℕ) * gramScale Q Y * Z ^ ε := by ring

end SmallY3

end HeckeSkeleton.GramAssembly
