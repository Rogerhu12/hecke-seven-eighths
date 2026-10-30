import HeckeSkeleton.HighBinSupport.ActualContourTransport
import HeckeSkeleton.HighBinSupport.ActualLRatioStrip
import HeckeSkeleton.HighBinSupport.ActualEulerProduct
import HeckeGeneral.Analysis.FrequencyRowCounting

/-!
# Horizontal tails for the constructed arithmetic Euler provider

The actual finite Laurent tables, actual deleted L-functions, original
Mellin tests and original prime-window normalizer are used throughout.
The single-row estimate below has no correction regularity, Euler bound,
normalizer lower bound, conductor bound, or contour estimate as a premise.
Its remaining data are the actual buffered zero detector and the explicit
heights of the finite rectangle. The row and height degrees are fixed
before the external decay order.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HighBinBoundary.ActualEstimate

open NumberField IsDedekindDomain MeasureTheory Set Complex
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HighBinBoundary.CoarseEuler
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Membership in the repository's finite row envelope gives its actual
norm bound, with no separate counting or norm-envelope assumption. -/
theorem frequencyRowNorm_le_of_mem_rows {U : ℝ} (hU : 0 ≤ U)
    (u : FrequencyRow K S) (hu : u ∈ frequencyRows K S U) :
    frequencyRowNorm K S u ≤ U := by
  letI : Fintype (SixthUnitClasses K S) := Fintype.ofFinite _
  unfold frequencyRows at hu
  obtain ⟨⟨I, sector⟩, _, rfl⟩ := Finset.mem_image.mp hu
  have hmem := (Finset.mem_filter.mp I.property).1
  have hn := (HeckeGeneral.Analysis.SquarefreeAmplification.mem_dyadicIdealSupport_iff
    K (div_nonneg hU (by norm_num)) I.val).mp hmem
  change idealNorm K I.val ≤ U
  linarith

/-- Actual finite-box continuity follows from normal Euler convergence. -/
theorem correction_continuousOn_heightBox
    (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (a e H σ : ℝ) (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1)
    (he : 0 < e) (he1 : e ≤ 1 / 10000) (hs : a + 16 * e ≤ σ) :
    ContinuousOn (fun q =>
      rowCorrection K S P ψ (arithmeticHighEulerData K S P ψ) Q u
        (ActualIntegrability.sLine σ q)
        (ActualIntegrability.wLine (1 - a - 6 * e) q)
        (ActualIntegrability.zLine q)) (ActualIntegrability.heightBox H) := by
  apply (rowCorrection_continuousOn_sweptTube K S P ψ Q u ha ha1 he he1).comp
  · exact ((ActualIntegrability.continuous_sLine σ).prodMk
      ((ActualIntegrability.continuous_wLine (1 - a - 6 * e)).prodMk
        ActualIntegrability.continuous_zLine)).continuousOn
  · intro q _
    exact swept_contour_mem_tube he hs _ _ _
      (by simp [ActualIntegrability.sLine])
      (by simp [ActualIntegrability.wLine])
      (by norm_num [ActualIntegrability.zLine])

/-- Every s-slice through the actual horizontal faces is holomorphic. -/
theorem correction_differentiableAt_s
    (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (a e : ℝ) (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1)
    (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (s w z : ℂ) (hs : a + 16 * e ≤ s.re)
    (hw : w.re = 1 - a - 6 * e) (hz : z.re = 17 / 50) :
    DifferentiableAt ℂ (fun s =>
      rowCorrection K S P ψ (arithmeticHighEulerData K S P ψ) Q u s w z) s := by
  have hsw : 1 - a - 7 * e < w.re := by rw [hw]; linarith
  have hsz : 17 / 50 - e < z.re := by rw [hz]; linarith
  have h := rowCorrection_differentiableOn_s K S P ψ Q u ha ha1 he he1 w z hsw hsz
  exact h.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by linarith))

/-- A fixed polynomial envelope for the literal arithmetic marked Euler
continuation. Every prime mark is retained, and the finite table is allowed
to vanish. The external decay order does not enter this estimate. -/
theorem exists_uniform_arithmetic_rowEuler_bound
    (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ) (J : ℕ)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000) :
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → ∀ u : FrequencyRow K S,
      Z ^ d ≤ frequencyRowNorm K S u → ∀ a H U : ℝ,
      51 / 100 ≤ a → a ≤ 1 → 0 ≤ H → H + 3 / 2 ≤ U →
      rowZeroBelow K S ψ Θ P (arithmeticHighEulerData K S P ψ) u U (a + 2 * e) →
      ∀ Q : Finset (ExteriorPrime K S), Q.card ≤ J → ∀ s w z : ℂ,
      a + 16 * e ≤ s.re → s.re ≤ 2 → w.re = 1 - a - 6 * e →
      z.re = 17 / 50 → |s.im| ≤ H → |w.im| ≤ H →
      ‖rowEulerContinuation K S P ψ (arithmeticHighEulerData K S P ψ) Q u s w z‖ ≤
        C * frequencyRowNorm K S u ^ 7 * (2 + U) ^ ActualLRatioStrip.boundaryHeightDegree K := by
  let E := arithmeticHighEulerData K S P ψ
  obtain ⟨C, Z₀, hC, hZ₀, hratio⟩ :=
    ActualLRatioStrip.exists_uniform_high_row_deletedLRatio_norm_bound K S ψ Θ hΘ P E he he1
  obtain ⟨D, hD, hzeta⟩ := ActualLRatioStrip.exists_uniform_deleted_zeta_six_bound K S
  let A : ℝ := Real.exp (∑' p : ExteriorPrime K S,
    (11 / sweptTubeEulerMargin) * (p.val.asIdeal.absNorm : ℝ) ^ (-1 - 8 * e))
  have hA : 0 < A := Real.exp_pos _
  have hM : 0 < markedBound ^ J := pow_pos (zero_lt_one.trans_le one_le_markedBound) _
  refine ⟨D * C * A * markedBound ^ J, Z₀, by positivity, hZ₀, ?_⟩
  intro Z hZ d hd u hu a H U ha ha1 hH hHU hbelow Q hQ s w z hs hs2 hw hz hsi hwi
  have hL := hratio Z hZ d hd u hu a H U ha ha1 hH hHU hbelow s w hs hs2 hw hsi hwi
  have hv : (s, w, z) ∈ sweptTube a e :=
    swept_contour_mem_tube he hs s w z rfl hw hz
  have hE := rowCorrection_coarse_bound K S P ψ Q u ha ha1 he he1 (s, w, z) hv
  have hmark : markedBound ^ Q.card ≤ markedBound ^ J :=
    pow_le_pow_right₀ one_le_markedBound hQ
  have hEc : ‖rowCorrection K S P ψ E Q u s w z‖ ≤
      (frequencyRowNorm K S u ^ 4 * markedBound ^ J) * A :=
    hE.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmark (pow_nonneg (idealNorm_pos K u.ideal.val).le _)) hA.le)
  have hζ := hzeta z hz.ge
  have hheight : 0 ≤ (2 + U) ^ ActualLRatioStrip.boundaryHeightDegree K := by
    apply pow_nonneg
    linarith
  change ‖rowEulerContinuation K S P ψ E Q u s w z‖ ≤ _
  calc
    _ = ‖heckeDeletedContinuation K 1 (exceptionalPrimes K S) (6 * z)‖ *
        (‖heckeDeletedContinuation K (E.rows.character u) (exceptionalPrimes K S) w‖ *
          ‖(heckeDeletedContinuation K (ψ * conjugate (E.rows.character u))
            (exceptionalPrimes K S) s)⁻¹‖) *
        ‖rowCorrection K S P ψ E Q u s w z‖ := by
      simp only [rowEulerContinuation, div_eq_mul_inv, norm_mul]
      ring
    _ ≤ D * (C * frequencyRowNorm K S u ^ 3 *
        (2 + U) ^ ActualLRatioStrip.boundaryHeightDegree K) *
        ((frequencyRowNorm K S u ^ 4 * markedBound ^ J) * A) := by
      exact mul_le_mul
        (mul_le_mul hζ hL (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hD.le)
        hEc (norm_nonneg _) (by positivity)
    _ = _ := by ring

end HighBinBoundary.ActualEstimate

namespace HighBinBoundary.ActualEstimate

open NumberField IsDedekindDomain MeasureTheory Set Complex
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S₀" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [MeasurableSpace (sLocalNormOneGroup K S₀)]
  [BorelSpace (sLocalNormOneGroup K S₀)]
variable [∀ p : S₀, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S₀, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S₀) → Measure (p.val.adicCompletion K))
variable [∀ p : S₀, (μ p).IsAddHaarMeasure]

/-- The original finite row contour moves from B+20e to a+16e, with
arbitrary external T decay. All lower-level estimates and regularity
premises have been discharged for the constructed arithmetic provider.
The constant and cutoff are uniform in all rows, bins and ray filters;
the powers Z^5, Nu^7 and (2+U)^(6#∞) are independent of N. -/
theorem exists_arithmetic_rowContourBox_external_tail
    (P : ProbeData K S₀) (ψ : HeckeCharacter K)
    (Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ) (g : PrimeWindowGeometry)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (T : Finset (HeckeCharacter K)) (Z : ℝ), Z₀ ≤ Z →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → ∀ u : FrequencyRow K S₀,
      Z ^ d ≤ frequencyRowNorm K S₀ u → ∀ a B H U Text : ℝ,
      51 / 100 ≤ a → a ≤ B → B ≤ 1 →
      1 ≤ Text → Text ≤ H → H + 3 / 2 ≤ U →
      rowZeroBelow K S₀ ψ Θ P (arithmeticHighEulerData K S₀ P ψ) u U (a + 2 * e) →
      ‖rowContourBox K S₀ μ P ψ (arithmeticHighEulerData K S₀ P ψ) g T u Z H
          (B + 20 * e) (1 - a - 6 * e) (17 / 50) -
        rowContourBox K S₀ μ P ψ (arithmeticHighEulerData K S₀ P ψ) g T u Z H
          (a + 16 * e) (1 - a - 6 * e) (17 / 50)‖ ≤
        C * Z ^ 5 * frequencyRowNorm K S₀ u ^ 7 *
          (2 + U) ^ ActualLRatioStrip.boundaryHeightDegree K * Text ^ (-(N : ℝ)) := by
  let E := arithmeticHighEulerData K S₀ P ψ
  obtain ⟨D, Z₁, hD, hZ₁, hrow⟩ := exists_uniform_arithmetic_rowEuler_bound
    K S₀ P ψ Θ hΘ g.slots he he1
  have hFib := HeckeSkeleton.ActualCanonicalRowConsumers.rowCharacter_fiber_finite K S₀ P E
  let v : InfinitePlace K := Classical.choice inferInstance
  obtain ⟨Z₂, hZ₂, hnon⟩ :=
    HeckeSkeleton.HighNormBackgroundExclusion.high_rows_exclude_background_norm_twists
      K S₀ P E.rows hFib v ({1, ψ} : Finset (HeckeCharacter K))
  refine ⟨max Z₁ Z₂, hZ₁.trans (le_max_left _ _), ?_⟩
  intro N
  obtain ⟨C, hC, htail⟩ := ActualContour.exists_rowContourBox_external_tail K S μ P g N
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro T Z hZ d hd u hu a B H U Text ha haB hB hT hTH hHU hbelow
  have hZZ₁ : Z₁ ≤ Z := (le_max_left _ _).trans hZ
  have hZZ₂ : Z₂ ≤ Z := (le_max_right _ _).trans hZ
  have hZ1 : 1 ≤ Z := hZ₁.trans hZZ₁
  have ha1 : a ≤ 1 := haB.trans hB
  have hH : 0 ≤ H := by linarith
  have hU : 0 ≤ U := by linarith
  have hχ : ∀ t : ℝ, E.rows.character u ≠ heckeNormTwist K t := by
    simpa only [one_mul] using (hnon Z hZZ₂ d hd u hu 1 (by simp)).1
  have hβ := (hnon Z hZZ₂ d hd u hu ψ (by simp)).2
  obtain ⟨hlr, hr2, hwidth, hν0, hν1⟩ := actual_contour_ranges ha haB hB he.le he1
  have hcorrC : ∀ σ ∈ ({a + 16 * e, B + 20 * e} : Finset ℝ),
      ∀ Q : Finset (ExteriorPrime K S₀),
      ContinuousOn (fun q => rowCorrection K S₀ P ψ E Q u
        (ActualIntegrability.sLine σ q)
        (ActualIntegrability.wLine (1 - a - 6 * e) q)
        (ActualIntegrability.zLine q)) (ActualIntegrability.heightBox H) := by
    intro σ hσ Q
    have hs : a + 16 * e ≤ σ := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
      rcases hσ with rfl | rfl
      · exact le_rfl
      · exact hlr
    exact correction_continuousOn_heightBox K S₀ P ψ Q u a e H σ ha ha1 he he1 hs
  have hcorrD : ∀ q ∈ Icc (-H) H ×ˢ Icc (-H) H,
      ∀ s ∈ Icc (a + 16 * e) (B + 20 * e) ×ℂ Icc (-H) H,
      ∀ Q : Finset (ExteriorPrime K S₀),
      DifferentiableAt ℂ (fun s => rowCorrection K S₀ P ψ E Q u s
        (((1 - a - 6 * e : ℝ) : ℂ) + q.1 * I) ((17 / 50 : ℂ) + q.2 * I)) s := by
    intro q _ s hs Q
    exact correction_differentiableAt_s K S₀ P ψ Q u a e ha ha1 he he1 s _ _ hs.1.1
      (by simp) (by norm_num)
  let M : ℝ := D * frequencyRowNorm K S₀ u ^ 7 *
    (2 + U) ^ ActualLRatioStrip.boundaryHeightDegree K
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hmarks : ∀ p : Fin g.slots → ExteriorPrime K S₀,
      ∀ Q : Finset (ExteriorPrime K S₀), Q ⊆ Finset.univ.image p → Q.card ≤ g.slots := by
    intro p Q hQ
    exact (Finset.card_le_card hQ).trans (by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (Finset.card_image_le (s := (Finset.univ : Finset (Fin g.slots))) (f := p)))
  have hrowM : ∀ σ ∈ Icc (a + 16 * e) (B + 20 * e),
      ∀ q ∈ Icc (-H) H ×ˢ Icc (-H) H, ∀ x : ℝ, |x| = H →
      ∀ p ∈ Fintype.piFinset (fun i => primeWindow K S₀ g T Z i),
      ∀ Q : Finset (ExteriorPrime K S₀), Q ⊆ Finset.univ.image p →
        ‖rowEulerContinuation K S₀ P ψ E Q u ((σ : ℂ) + x * I)
          (((1 - a - 6 * e : ℝ) : ℂ) + q.1 * I)
          ((17 / 50 : ℂ) + q.2 * I)‖ ≤ M := by
    intro σ hσ q hq x hx p _ Q hQ
    exact hrow Z hZZ₁ d hd u hu a H U ha ha1 hH hHU hbelow Q (hmarks p Q hQ) _ _ _
      (by simpa using hσ.1) (by simpa using hσ.2.trans hr2)
      (by simp) (by norm_num) (by simpa using hx.le)
      (by simpa using (abs_le.mpr hq.1))
  have hb := htail ψ E T Θ hΘ u hχ hβ Z H U (a + 2 * e) (a + 16 * e)
    (B + 20 * e) (1 - a - 6 * e) Text hZ1 hT hTH (by linarith)
    (by linarith) (by linarith) hlr (by linarith) hr2 (by linarith) (by linarith)
    hbelow hcorrC hcorrD M hM hrowM
  apply hb.trans
  calc
    C * Z ^ 5 * M * |(B + 20 * e) - (a + 16 * e)| * Text ^ (-(N : ℝ)) ≤
        C * Z ^ 5 * M * 1 * Text ^ (-(N : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
      exact mul_le_mul_of_nonneg_left (le_trans hwidth.le (by norm_num)) (by positivity)
    _ = _ := by dsimp [M]; ring

#print axioms correction_continuousOn_heightBox
#print axioms correction_differentiableAt_s
#print axioms exists_uniform_arithmetic_rowEuler_bound
#print axioms exists_arithmetic_rowContourBox_external_tail

/-- Summation over an original fixed arithmetic shell costs one further
power of Z by the repository's actual frequency-row counting theorem.
No amplitude label, row-count estimate, or boundary estimate is assumed.
The fixed degree 13 is selected before every external tail order. -/
theorem exists_arithmetic_fixedRows_external_tail
    (P : ProbeData K S₀) (ψ : HeckeCharacter K)
    (Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ) (g : PrimeWindowGeometry)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (T : Finset (HeckeCharacter K)) (Z : ℝ), Z₀ ≤ Z →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → d ≤ 1 →
      ∀ R : Finset (FrequencyRow K S₀), R ⊆ frequencyRows K S₀ (2 * Z ^ d) →
      (∀ u ∈ R, Z ^ d ≤ frequencyRowNorm K S₀ u) → ∀ a B H U Text : ℝ,
      51 / 100 ≤ a → a ≤ B → B ≤ 1 →
      1 ≤ Text → Text ≤ H → H + 3 / 2 ≤ U →
      (∀ u ∈ R, rowZeroBelow K S₀ ψ Θ P (arithmeticHighEulerData K S₀ P ψ)
        u U (a + 2 * e)) →
      ‖(∑ u ∈ R, rowContourBox K S₀ μ P ψ (arithmeticHighEulerData K S₀ P ψ)
          g T u Z H (B + 20 * e) (1 - a - 6 * e) (17 / 50)) -
        (∑ u ∈ R, rowContourBox K S₀ μ P ψ (arithmeticHighEulerData K S₀ P ψ)
          g T u Z H (a + 16 * e) (1 - a - 6 * e) (17 / 50))‖ ≤
        C * Z ^ 13 * (2 + U) ^ ActualLRatioStrip.boundaryHeightDegree K *
          Text ^ (-(N : ℝ)) := by
  obtain ⟨Z₀, hZ₀, hb⟩ :=
    exists_arithmetic_rowContourBox_external_tail K S μ P ψ Θ hΘ g he he1
  obtain ⟨D, hD, hcount⟩ := frequencyRows_linear_count K S₀
  refine ⟨Z₀, hZ₀, ?_⟩
  intro N
  obtain ⟨C, hC, hpiece⟩ := hb N
  refine ⟨256 * D * C, by positivity, ?_⟩
  intro T Z hZ d hd hd1 R hR hlo a B H U Text ha haB hB hT hTH hHU hbelow
  have hZ1 : 1 ≤ Z := hZ₀.trans hZ
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ1
  have hd0 : 0 ≤ d := by linarith
  have hZd : 1 ≤ Z ^ d := Real.one_le_rpow hZ1 hd0
  have hZdZ : Z ^ d ≤ Z := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ1 hd1
  have hrow : ∀ u ∈ R, frequencyRowNorm K S₀ u ≤ 2 * Z := by
    intro u hu
    exact (frequencyRowNorm_le_of_mem_rows K S₀ (by positivity) u (hR hu)).trans
      (mul_le_mul_of_nonneg_left hZdZ (by norm_num))
  have hcard : (R.card : ℝ) ≤ 2 * D * Z := by
    calc
      _ ≤ ((frequencyRows K S₀ (2 * Z ^ d)).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hR)
      _ ≤ D * (2 * Z ^ d) := hcount _ (by linarith)
      _ ≤ D * (2 * Z) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hZdZ (by norm_num)) hD.le
      _ = _ := by ring
  have hU : 0 ≤ U := by linarith
  have hT0 : 0 ≤ Text := by linarith
  have hconst : 0 ≤ C * Z ^ 5 * (2 * Z) ^ 7 *
      (2 + U) ^ ActualLRatioStrip.boundaryHeightDegree K * Text ^ (-(N : ℝ)) := by positivity
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ u ∈ R,
        ‖rowContourBox K S₀ μ P ψ (arithmeticHighEulerData K S₀ P ψ)
            g T u Z H (B + 20 * e) (1 - a - 6 * e) (17 / 50) -
          rowContourBox K S₀ μ P ψ (arithmeticHighEulerData K S₀ P ψ)
            g T u Z H (a + 16 * e) (1 - a - 6 * e) (17 / 50)‖ := norm_sum_le _ _
    _ ≤ ∑ _u ∈ R, C * Z ^ 5 * (2 * Z) ^ 7 *
        (2 + U) ^ ActualLRatioStrip.boundaryHeightDegree K * Text ^ (-(N : ℝ)) := by
      apply Finset.sum_le_sum
      intro u hu
      apply (hpiece T Z hZ d hd u (hlo u hu) a B H U Text ha haB hB hT hTH hHU
        (hbelow u hu)).trans
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hT0 _)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by positivity) _)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (idealNorm_pos K u.ideal.val).le (hrow u hu) 7) (by positivity)
    _ = (R.card : ℝ) * (C * Z ^ 5 * (2 * Z) ^ 7 *
        (2 + U) ^ ActualLRatioStrip.boundaryHeightDegree K * Text ^ (-(N : ℝ))) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * D * Z) * (C * Z ^ 5 * (2 * Z) ^ 7 *
        (2 + U) ^ ActualLRatioStrip.boundaryHeightDegree K * Text ^ (-(N : ℝ))) :=
      mul_le_mul_of_nonneg_right hcard hconst
    _ = _ := by ring

#print axioms frequencyRowNorm_le_of_mem_rows
#print axioms exists_arithmetic_fixedRows_external_tail

end HighBinBoundary.ActualEstimate
