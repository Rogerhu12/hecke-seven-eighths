import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionSmall
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionFinite

/-!
# One actual long cube block after its common Mellin integral

Each annular frequency is treated by the genuine recursive provider or
by the proved subunit-column bound. The same finite seminorm covers
both branches. The original common Mellin density is then integrated,
and the complete square-root normalization is restored exactly. The
remaining divisor-cap square is explicit for the final small-power
budget; the original total node length is unchanged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionBlockBound

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP
open CanonicalNormPools FixedTripleEnergy
open ProviderNodes CubeCompletionGeometry CubeCompletionMellin CubeCompletionProfile
open CubeCompletionNodeStep CubeCompletionFinite
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

theorem square_scale_identity {Z N V H : ℝ} (hZ : 1 < Z) (hH : 0 < H) :
    (Z ^ N) ^ 2 * (Z ^ V) ^ 2 / H = Z ^ (2 * (N + V) - cubeLength Z H) := by
  have hz0 := zero_lt_one.trans hZ
  rw [← Real.rpow_mul_natCast hz0.le, ← Real.rpow_mul_natCast hz0.le,
    ← Real.rpow_add hz0, Real.rpow_sub hz0, cubeLength_scale hZ hH]
  congr 2
  ring

theorem normalization_power_identity {Z N V H loss : ℝ} (hZ : 1 < Z) (hH : 0 < H) :
    Z ^ (-V) * (2 * H / Z ^ N) *
        Z ^ (2 * (N + V) - cubeLength Z H + loss) =
      2 * Z ^ (N + V + loss) := by
  have hz0 := zero_lt_one.trans hZ
  calc
    _ = 2 * ((Z ^ (-V) * Z ^ cubeLength Z H / Z ^ N) *
      Z ^ (2 * (N + V) - cubeLength Z H + loss)) := by
      rw [cubeLength_scale hZ hH]
      ring
    _ = 2 * Z ^ ((-V + cubeLength Z H - N) +
      (2 * (N + V) - cubeLength Z H + loss)) := by
      rw [← Real.rpow_add hz0, ← Real.rpow_sub hz0, ← Real.rpow_add hz0]
    _ = _ := by congr 2; ring

include hΓ hallowed μv ν μ in
theorem exists_uniform_block_bound
    (slotCap : ℕ) (A pi tauMin : ℝ) (hA : 1 ≤ A)
    (hpi : 0 < pi) (htauMin : 0 < tauMin) (t : Finset (ℕ × ℕ)) :
    ∃ q : Finset (ℕ × ℕ), ∃ C : ℝ, 1 ≤ C ∧
      ∀ {σ : Type u} [DecidableEq σ] (Θ : Subgroup (HeckeCharacter K))
        (ψ Λ G : HeckeCharacter K), G ∈ Θ →
      ∀ (Z Fcap c z lo hi d eta h tau eps Cih Rmax : ℝ)
        (x : Node K S Γ Θ ψ σ),
      2 ≤ Z → Fcap ≤ A → 0 ≤ c - eta / 2 → 0 ≤ z →
      x.Admissible D Λ G slotCap Z Fcap c z lo hi → x.rowLength ≤ Rmax →
      h ∈ Set.Icc (0 : ℝ) 1 → tau ∈ Set.Icc (0 : ℝ) A → tauMin ≤ tau →
      2 ≤ Z ^ h → h ≤ eta / 128 → eta ≤ d / 16 →
      0 ≤ eps → 1 ≤ Cih →
      UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
        (Fcap + 11 * eta) (c - 7 * eta) z lo hi eps (Rmax - d) Cih t →
      (∀ i : SchwartzTestPartition.Index, |Real.logb Z (annularScale i)| ≤ eta / 8) →
      ∀ (P : Ideal (𝓞 K) → Prop) (B : Finset Ext) (H : ℝ),
      1 ≤ H → H ^ 3 ≤ 2 * Z ^ x.columnLength →
      (∀ b ∈ B, H ≤ height K Sset b ∧ height K Sset b ≤ 2 * H) →
      2 * d / 3 ≤ cubeLength Z H →
      finiteEnergy K S D Γ slotCap x P B ≤
        C * Cih * cubeCoefficientCap (CubeCompletionProvider.cubeIdeals K S B) ^ 2 *
          (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 *
            Z ^ (x.totalLength + 21 * eta + tau + pi + eps) := by
  obtain ⟨qStep, CStep, hCStep, hstep⟩ := exists_uniform_annular_step
    K S D Γ hΓ hallowed μv ν μ slotCap A pi tauMin hA hpi htauMin t
  obtain ⟨CSmall, hCSmall, hsmall⟩ := CubeCompletionSmall.exists_uniform_small_annular_bound
    K S D Γ slotCap A pi hA hpi
  let qCommon := insert (0, 0) qStep
  obtain ⟨q, CMellin, hCMellin, hmellin⟩ :=
    CubeCompletionEnergy.exists_uniform_sourceEnergy_bound
      (β := Ext) (α := Ext) (κ := Ext × (Ideal (𝓞 K) × Sector)) qCommon
  let CAnnular := CStep + CSmall
  let CBlock := 2 * CMellin * CAnnular
  refine ⟨q, max 1 CBlock, le_max_left _ _, ?_⟩
  intro σ _ Θ ψ Λ G hG Z Fcap c z lo hi d eta h tau eps Cih Rmax x
    hZ hFcap hc hz hx hM hh htau htau' hwidth hmesh hstepsize heps hCih hih
    hshift P B H hH hsupport hB hlong
  have hz1 : 1 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hz0 := zero_lt_one.trans hz1
  have hb0 : 0 < x.family.base := hx.base_eq.symm ▸ hz0
  have hH0 := zero_lt_one.trans_le hH
  have heta : 0 ≤ eta := by linarith [hh.1]
  have hc0 : 0 ≤ c := by linarith
  have hCAnnular : 0 ≤ CAnnular := by dsimp only [CAnnular]; linarith
  have hCih0 : 0 ≤ Cih := zero_le_one.trans hCih
  let Lexp := 21 * eta + tau + pi + eps
  let E := CAnnular * Cih * Z ^ (2 * x.totalLength - cubeLength Z H + Lexp)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hqStep (W : SchwartzMap ℝ ℂ) :
      qStep.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ qCommon.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert (0, 0) qStep)) W
  have hqZero (W : SchwartzMap ℝ ℂ) :
      SchwartzMap.seminorm ℝ 0 0 W ≤ qCommon.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
    Seminorm.le_def.mp (Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ)
      (Finset.mem_insert_self (0, 0) qStep)) W
  have hannular (s : ℝ) (i : SchwartzTestPartition.Index) :
      annularEnergy K S D Γ slotCap x P B H s i ≤
        E * (qCommon.sup (schwartzSeminormFamily ℝ ℝ ℂ) (annularTest s i)) ^ 2 := by
    by_cases hlarge : 1 ≤ annularScale i * (Z ^ x.columnLength / H ^ 3)
    · have hp := hstep Θ ψ Λ G hG Z Fcap c z lo hi d eta h tau eps Cih Rmax x
        hZ hFcap hc hz hx hM hh htau htau' hwidth hmesh hstepsize heps hCih hih
        P B H hH hsupport (fun b hb => (hB b hb).2) hlong s i (hshift i) hlarge
      have hexp : 2 * annularLength Z x.columnLength H i + 5 * cubeLength Z H +
          2 * x.labelLength + 20 * eta + tau + pi + eps ≤
          2 * x.totalLength - cubeLength Z H + Lexp := by
        have ht := annular_total_length (V := x.labelLength) hz1 hH0 i
        have hs := (abs_le.mp (hshift i)).2
        dsimp only [Node.totalLength, Lexp]
        linarith
      apply hp.trans
      calc
        _ ≤ CAnnular * Cih *
            (qCommon.sup (schwartzSeminormFamily ℝ ℝ ℂ) (annularTest s i)) ^ 2 *
              Z ^ (2 * x.totalLength - cubeLength Z H + Lexp) := by
          gcongr
          · dsimp only [CAnnular]; linarith
          · exact hqStep _
          · exact hexp
        _ = _ := by dsimp only [E]; ring
    · have hs := hsmall Θ ψ Λ G Z Fcap c z lo hi x hz1 hFcap hc0 hz hx
        P B H hH hsupport (fun b hb => (hB b hb).2) s i (lt_of_not_ge hlarge)
      rw [square_scale_identity hz1 hH0] at hs
      have hpow : Z ^ (2 * x.totalLength - cubeLength Z H) * Z ^ pi ≤
          Z ^ (2 * x.totalLength - cubeLength Z H + Lexp) := by
        rw [← Real.rpow_add hz0]
        apply Real.rpow_le_rpow_of_exponent_le hz1.le
        dsimp only [Lexp]
        linarith [htau.1]
      calc
        _ ≤ CSmall * (Z ^ (2 * x.totalLength - cubeLength Z H) * Z ^ pi) *
            (SchwartzMap.seminorm ℝ 0 0 (annularTest s i)) ^ 2 := by
          simpa only [Node.totalLength, mul_assoc] using hs
        _ ≤ (CAnnular * Cih) * Z ^ (2 * x.totalLength - cubeLength Z H + Lexp) *
            (qCommon.sup (schwartzSeminormFamily ℝ ℝ ℂ) (annularTest s i)) ^ 2 := by
          gcongr
          · calc
              CSmall ≤ CAnnular := by dsimp only [CAnnular]; linarith
              _ ≤ CAnnular * Cih := le_mul_of_one_le_right hCAnnular hCih
          · exact hpow
          · exact hqZero _
        _ = _ := by dsimp only [E]; ring
  have hsource := hmellin
    ((ProviderChildParent.exteriorLabels K S x.labels) ×ˢ x.rows)
    (fun fk => labelDivisorWeight slotCap fk.1.val.val)
    (fun fk _ => labelDivisorWeight_nonneg slotCap _)
    B (squarefreePool K Sset (8 * x.family.base ^ x.columnLength))
    (height K Sset) (height K Sset) (coefficients K S D Γ x P B H)
    x.test hx.test_support H (x.family.base ^ x.columnLength / H ^ 3)
    (x.family.base ^ x.columnLength) E hH0
    (div_pos (Real.rpow_pos_of_pos hb0 _) (pow_pos hH0 _))
    (by field_simp [hH0.ne'] <;> ring) hE hB (fun n _ => height_pos K Sset n) hannular
  rw [finiteEnergy_eq_sourceEnergy K S D Γ slotCap x hb0 hx.calibration.lambda_unramified P B H hH0]
  apply (mul_le_mul_of_nonneg_left hsource
    (mul_nonneg (Real.rpow_nonneg hb0.le _) (sq_nonneg _))).trans
  rw [sourceScale_sq _ _ _ hH0.le (Real.rpow_nonneg hb0.le _), hx.base_eq]
  have hpower := normalization_power_identity (N := x.columnLength) (V := x.labelLength)
    (loss := Lexp) hz1 hH0
  calc
    _ = CBlock * Cih * cubeCoefficientCap (CubeCompletionProvider.cubeIdeals K S B) ^ 2 *
        (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 * Z ^ (x.totalLength + Lexp) := by
      dsimp only [E, CBlock]
      calc
        _ = (CMellin * CAnnular) * Cih * cubeCoefficientCap
            (CubeCompletionProvider.cubeIdeals K S B) ^ 2 *
            (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 *
              (Z ^ (-x.labelLength) * (2 * H / Z ^ x.columnLength) *
                Z ^ (2 * (x.columnLength + x.labelLength) - cubeLength Z H + Lexp)) := by
          dsimp only [Node.totalLength]
          ring
        _ = _ := by rw [hpower]; dsimp only [Node.totalLength]; ring
    _ ≤ _ := by
      change _ ≤ max 1 CBlock * Cih * _ * _ * Z ^ (x.totalLength + Lexp)
      gcongr
      exact le_max_right (1 : ℝ) CBlock

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionBlockBound
