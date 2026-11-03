import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceScaleSupRows
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourcePrefixEnergy
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceScaleBudget

/-!
# The common positive prefix closes the complete-row scale-sup seed

This is the analytic assembly of the strict seed.  The annular input is
the literal complete-row polynomial at each supported scale; the orbital
source estimate supplies it.  The original row-local profile stays fixed
while all smaller column scales vary.  One row function bounds all those
scales, and its sum is bounded using the same common Fourier measure.

All seminorm orders, Fourier moments and constants are selected before
the source parameters and row cutoff.  The squared dyadic count is paid
by the single threshold of `SourceScaleBudget`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceScaleSupClosure

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.UniformAmplify
open HeckeSkeleton.Moments.MOM_INV_STEP
open SourceScaleSupRows
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

/-- The exact finite annular expansion gives the squared dyadic count.
There is no complete-row cardinality in this estimate. -/
theorem prefix_bound (i : Parameters K c) (H : ℝ) (L J : ℕ) (t E : ℝ)
    (hE : 0 ≤ E)
    (hAnn : ∀ j ∈ Finset.range (L + 1), ∀ k : SchwartzTestPartition.Index,
      (∑ u ∈ (originalData K c i).rows H,
        ‖SourceAnnularRows.polynomial K (pulledData K c i) u
          (SourcePrefixEnergy.scale j k) (SourceAnnularTests.piece t k)‖ ^ 2) ≤
        E * (1 + |t|) ^ J) :
    (∑ u ∈ (originalData K c i).rows H,
      ‖SourceScaleSup.prefixColumn (SourcePrefixEnergy.pool K L)
        (SourceActualScale.normWeightedCoefficient (pulledData K c i) u)
        (idealNorm K) L t‖ ^ 2) ≤
      4608 * (L + 1 : ℕ) ^ 2 * E * (1 + |t|) ^ J := by
  calc
    _ ≤ 192 * (L + 1 : ℕ) *
        ∑ j ∈ Finset.range (L + 1), ∑ k : SchwartzTestPartition.Index,
          ∑ u ∈ (originalData K c i).rows H,
            ‖SourceAnnularRows.polynomial K (pulledData K c i) u
              (SourcePrefixEnergy.scale j k) (SourceAnnularTests.piece t k)‖ ^ 2 :=
      SourcePrefixEnergy.prefix_energy_le K (pulledData K c i)
        ((originalData K c i).rows H) L t
    _ ≤ 192 * (L + 1 : ℕ) *
        ∑ _j ∈ Finset.range (L + 1), ∑ _k : SchwartzTestPartition.Index,
          E * (1 + |t|) ^ J := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun k hk => hAnn j hj k))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, SchwartzTestPartition.Index,
        Fintype.card_fin, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat]
      ring

/-- A weighted Fourier moment controls both occurrences of the common
measure.  The proof uses actual integrable finite prefix energies. -/
theorem majorant_sum_le (i : Parameters K c) (H : ℝ) (L J : ℕ)
    (W : ℝ → ℝ) (hW : ∀ t, 0 ≤ W t) (iW : Integrable W)
    (iWJ : Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * W t))
    (E M : ℝ) (hE : 0 ≤ E) (hM : 0 ≤ M)
    (hmass : (∫ t : ℝ, (1 + ‖t‖) ^ J * W t) ≤ M)
    (hAnn : ∀ t : ℝ, ∀ j ∈ Finset.range (L + 1), ∀ k : SchwartzTestPartition.Index,
      (∑ u ∈ (originalData K c i).rows H,
        ‖SourceAnnularRows.polynomial K (pulledData K c i) u
          (SourcePrefixEnergy.scale j k) (SourceAnnularTests.piece t k)‖ ^ 2) ≤
        E * (1 + |t|) ^ J) :
    (∑ u ∈ (originalData K c i).rows H, majorant K c i L W u) ≤
      4608 * (L + 1 : ℕ) ^ 2 * E * M ^ 2 := by
  let A : ℝ := 4608 * (L + 1 : ℕ) ^ 2 * E
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hmass0 : 0 ≤ ∫ t : ℝ, W t := integral_nonneg hW
  have hmass1 : (∫ t : ℝ, W t) ≤ M := by
    apply (integral_mono iW iWJ _).trans hmass
    intro t
    have hp : 1 ≤ (1 + ‖t‖) ^ J := one_le_pow₀ (by linarith [norm_nonneg t])
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (hW t)
  have hi : Integrable (fun t : ℝ => W t *
      ∑ u ∈ (originalData K c i).rows H,
        ‖SourceScaleSup.prefixColumn (SourcePrefixEnergy.pool K L)
          (SourceActualScale.normWeightedCoefficient (pulledData K c i) u)
          (idealNorm K) L t‖ ^ 2) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finset_sum _ (fun u hu =>
      SourceScaleSup.prefix_energy_integrable _ _ _ _ _ iW)
  have he : (∫ t : ℝ, W t *
      ∑ u ∈ (originalData K c i).rows H,
        ‖SourceScaleSup.prefixColumn (SourcePrefixEnergy.pool K L)
          (SourceActualScale.normWeightedCoefficient (pulledData K c i) u)
          (idealNorm K) L t‖ ^ 2) ≤ A * M := by
    calc
      _ ≤ ∫ t : ℝ, A * ((1 + ‖t‖) ^ J * W t) := by
        apply integral_mono hi (iWJ.const_mul A)
        intro t
        have hb := mul_le_mul_of_nonneg_left (prefix_bound K c i H L J t E hE (hAnn t)) (hW t)
        simpa only [Real.norm_eq_abs, A, mul_assoc, mul_left_comm, mul_comm] using hb
      _ = A * ∫ t : ℝ, (1 + ‖t‖) ^ J * W t := integral_const_mul _ _
      _ ≤ A * M := mul_le_mul_of_nonneg_left hmass hA
  rw [complete_row_sum K c i H L W iW]
  calc
    _ ≤ (∫ t : ℝ, W t) * (A * M) := mul_le_mul_of_nonneg_left he hmass0
    _ ≤ M * (A * M) := mul_le_mul_of_nonneg_right hmass1 (mul_nonneg hA hM)
    _ = _ := by dsimp only [A]; ring

/-- This internal bridge consumes the actual complete-row annular
estimate.  Its input will be discharged by the zero-slot orbital source
and the canonical finite induction, not assumed by the original theorem. -/
theorem strict_seed_of_uniform_annular
    (hAnn : ∀ gap eps : ℝ, 0 < gap → gap < 1 → 0 < eps →
      ∃ q : Finset (ℕ × ℕ), ∃ C H₀ : ℝ, 0 ≤ C ∧ 2 ≤ H₀ ∧
        ∀ (i : Parameters K c) (H X : ℝ), H₀ ≤ H → 0 < X →
          X ≤ H ^ (1 - gap / 2) → ∀ W : SchwartzMap ℝ ℂ,
          tsupport W ⊆ Set.Icc (1 : ℝ) 2 →
          (∑ u ∈ (originalData K c i).rows H,
            ‖SourceAnnularRows.polynomial K (pulledData K c i) u X W‖ ^ 2) ≤
            C * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 * H ^ (1 + eps)) :
    CompleteUnmarkedScaleSupBound
      (recipeMomentModels K c (expansionRecipeRaw K c)).unmarked := by
  intro gap eps hgap0 hgap1 heps
  obtain ⟨q, CAnn, HAnn, hCAnn, hHAnn, hann⟩ :=
    hAnn gap (eps / 2) hgap0 hgap1 (by positivity)
  obtain ⟨J, CTest, hCTest, htest⟩ := SourceAnnularTests.piece_polynomial_seminorm q
  obtain ⟨CMass, hCMass, hmajor⟩ := exists_actual_common_majorant K c (2 * J)
  obtain ⟨HScale, hHScale, hscale⟩ :=
    SourceScaleBudget.exists_uniform_scale_budget gap eps hgap0 hgap1 heps
  let C := 4608 * CAnn * CTest ^ 2 * CMass ^ 2
  let A : ℕ := 2 * (2 * J + 2)
  refine ⟨max 1 C, (A : ℝ), 1, max HAnn HScale,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), Nat.cast_nonneg _, zero_lt_one,
    (by linarith [le_max_left HAnn HScale]), ?_⟩
  intro i H hH hheight
  have hHa : HAnn ≤ H := (le_max_left _ _).trans hH
  have hHs : HScale ≤ H := (le_max_right _ _).trans hH
  have hH1 : 1 ≤ H := by linarith
  have hHp : 0 < H := zero_lt_one.trans_le hH1
  let L := SourceScaleBudget.cap H gap
  obtain ⟨hcap, hcount, hlength⟩ := hscale H hHs
  obtain ⟨W, hW, cW, iW, iWJ, hmass, hb⟩ := hmajor ‖i.heights‖ (norm_nonneg _)
  obtain ⟨hB0, hB⟩ := hb i le_rfl L
  refine ⟨majorant K c i L W, hB0, ?_, ?_⟩
  · intro u hu D hD hDH
    exact hB u D hD ((mul_le_mul_of_nonneg_left hDH (by norm_num)).trans hcap.1)
  · let E := CAnn * CTest ^ 2 * H ^ (1 + eps / 2)
    let M := CMass * (1 + ‖i.heights‖) ^ (2 * J + 2 : ℕ)
    have hE : 0 ≤ E := by dsimp only [E]; positivity
    have hM : 0 ≤ M := by dsimp only [M]; positivity
    have hpiece : ∀ t : ℝ, ∀ j ∈ Finset.range (L + 1), ∀ k : SchwartzTestPartition.Index,
        (∑ u ∈ (originalData K c i).rows H,
          ‖SourceAnnularRows.polynomial K (pulledData K c i) u
            (SourcePrefixEnergy.scale j k) (SourceAnnularTests.piece t k)‖ ^ 2) ≤
          E * (1 + |t|) ^ (2 * J) := by
      intro t j hj k
      have hjL : j ≤ L := by have := Finset.mem_range.mp hj; omega
      have hX : SourcePrefixEnergy.scale j k ≤ H ^ (1 - gap / 2) := by
        by_cases hx : 1 ≤ SourcePrefixEnergy.scale j k
        · have hn := (hlength j hjL k hx).2
          have hp := Real.rpow_le_rpow_of_exponent_le hH1 hn
          rw [SourceScaleBudget.columnScale_eq_rpow (by linarith : 1 < H)] at hp
          exact hp
        · exact (le_of_not_ge hx).trans (Real.one_le_rpow hH1 (by linarith))
      have ht := pow_le_pow_left₀ (apply_nonneg _ _) (htest t k) 2
      calc
        _ ≤ CAnn * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) (SourceAnnularTests.piece t k)) ^ 2 *
            H ^ (1 + eps / 2) := hann i H _ hHa (SourcePrefixEnergy.scale_pos j k) hX
              (SourceAnnularTests.piece t k) (SourceAnnularTests.piece_support t k)
        _ ≤ CAnn * (CTest * (1 + |t|) ^ J) ^ 2 * H ^ (1 + eps / 2) := by gcongr
        _ = _ := by
          dsimp only [E]
          rw [mul_pow, ← pow_mul, Nat.mul_comm J 2]
          ring
    have hbtotal := majorant_sum_le K c i H L (2 * J) W hW iW iWJ E M hE hM hmass hpiece
    have hcount' : ((L + 1 : ℕ) : ℝ) ^ 2 ≤ H ^ (eps / 2) := by
      simpa only [L, Nat.cast_add, Nat.cast_one] using hcount
    calc
      _ ≤ 4608 * (L + 1 : ℕ) ^ 2 * E * M ^ 2 := hbtotal
      _ ≤ 4608 * H ^ (eps / 2) * E * M ^ 2 := by gcongr
      _ = C * H ^ (1 + eps) * (1 + ‖i.heights‖) ^ A := by
        dsimp only [C, E, M, A]
        rw [mul_pow, ← pow_mul]
        have hp : H ^ (eps / 2) * H ^ (1 + eps / 2) = H ^ (1 + eps) := by
          rw [← Real.rpow_add hHp]; congr 1; ring
        calc
          _ = (4608 * CAnn * CTest ^ 2 * CMass ^ 2) *
              (H ^ (eps / 2) * H ^ (1 + eps / 2)) *
                (1 + ‖i.heights‖) ^ ((2 * J + 2) * 2) := by ring
          _ = _ := by rw [hp, Nat.mul_comm (2 * J + 2) 2]
      _ ≤ max 1 C * H ^ (1 + eps) * (1 + ‖i.heights‖) ^ (A : ℝ) := by
        rw [Real.rpow_natCast]
        gcongr
        exact le_max_right _ _

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceScaleSupClosure

end
