import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalBlock
import HeckeSkeleton.Moments.MOM_INV_STEP.FixedTripleFibers

/-!
# Pointwise bounds for the original marked coefficients

The finite divisor estimate is applied to the literal original mark
product. Its constant is uniform in the lists and their individual
weights. The canonical coefficient estimate retains the actual cube/label
weight and the original norm test, so it applies to both principal terms
and absolute tail estimates without inventing a coefficient family.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CoefficientBounds

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep DedekindZetaZeroFree.LargeSieve
open FixedTripleFibers CanonicalBlock
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

theorem divisorMark_norm_le_divisorPower {σ : Type*}
    (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (ha : ∀ i ∈ slots, ∀ P ∈ lists i, ‖a i P‖ ≤ 1) :
    ‖divisorMark slots lists a I‖ ≤ ((idealDivisors I).card : ℝ) ^ slots.card := by
  have hslot (i : σ) (hi : i ∈ slots) :
      ‖∑ P ∈ lists i, if P ∣ I then a i P else 0‖ ≤
        ((idealDivisors I).card : ℝ) := by
    rw [← Finset.sum_filter]
    calc
      _ ≤ ∑ P ∈ (lists i).filter (fun P => P ∣ I), ‖a i P‖ := norm_sum_le _ _
      _ ≤ ∑ _P ∈ (lists i).filter (fun P => P ∣ I), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro P hP
        exact ha i hi P (Finset.mem_filter.mp hP).1
      _ = (((lists i).filter (fun P => P ∣ I)).card : ℝ) := by simp
      _ ≤ ((idealDivisors I).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (show
          (lists i).filter (fun P => P ∣ I) ⊆ idealDivisors I from by
            intro P hP
            exact (mem_idealDivisors hI).mpr (Finset.mem_filter.mp hP).2)
  rw [divisorMark, norm_prod]
  calc
    _ ≤ ∏ _i ∈ slots, ((idealDivisors I).card : ℝ) :=
      Finset.prod_le_prod (fun i _ => norm_nonneg _) hslot
    _ = _ := by simp

/-- Constants are selected before every original mark list and weight. -/
theorem exists_divisorMark_bound (slotCap : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {σ : Type*}
      (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
      (a : σ → Ideal (𝓞 K) → ℂ) (I : Ideal (𝓞 K)),
      I ≠ 0 → slots.card ≤ slotCap →
      (∀ i ∈ slots, ∀ P ∈ lists i, ‖a i P‖ ≤ 1) →
      ‖divisorMark slots lists a I‖ ≤ C * (Ideal.absNorm I : ℝ) ^ ε := by
  obtain ⟨C, hC, hb⟩ := exists_divisor_power_bound (K := K)
    (slotCap + 1) (by omega) ε hε
  refine ⟨C, hC, ?_⟩
  intro σ slots lists a I hI hcap ha
  apply (divisorMark_norm_le_divisorPower K slots lists a I hI ha).trans
  apply le_trans _ (hb I)
  apply pow_le_pow_right₀
  · exact_mod_cast divisor_card_pos I hI
  · omega

variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset

theorem idealSymbol_norm_le_one (I : Ext) (a : Set.integer Sset K) :
    ‖idealSymbol K Sset D I a‖ ≤ 1 :=
  norm_sIntegerSexticIdealEvaluation_le_one K Sset D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) a

theorem canonicalColumn_norm_le {σ : Type*} (C : ColumnData K S σ)
    (G : HeckeCharacter K) (hcal : ThetaCalibrationInput K Sset D C.lambda G)
    (f b n : Ext) (hn : Squarefree n.val.val)
    (ha : ∀ i ∈ C.slots, ∀ P ∈ C.primeLists i, ‖C.primeWeights i P‖ ≤ 1) :
    ‖canonicalColumn K S D C f b n‖ ≤
      ‖C.labelWeight b f‖ *
        ((idealDivisors (n.val.val * b.val.val ^ 3)).card : ℝ) ^ C.slots.card *
        ‖C.cutoff ((n.val.val.absNorm : ℝ) / C.base ^ C.length)‖ := by
  have hm : ‖(if IsCoprime n.val.val C.puncture then 1 else 0 : ℂ)‖ ≤ 1 := by
    split_ifs <;> norm_num
  have hχ := idealSymbol_norm_le_one K S D n (D.generator f)
  have hν := norm_heckeIdealCoefficient_le_one K C.background n.val
  have hmark := divisorMark_norm_le_divisorPower K C.slots C.primeLists C.primeWeights
    (n.val.val * b.val.val ^ 3)
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero n.val)
      (pow_ne_zero 3 (nonZeroDivisors.coe_ne_zero b.val))) ha
  rw [canonicalColumn]
  simp only [norm_mul, norm_pow, CoefficientCycle.canonicalCoefficient_norm hcal n hn]
  calc
    _ ≤ ‖C.labelWeight b f‖ * 1 * 1 * 1 * 1 ^ 4 *
        ((idealDivisors (n.val.val * b.val.val ^ 3)).card : ℝ) ^ C.slots.card *
          ‖C.cutoff ((n.val.val.absNorm : ℝ) / C.base ^ C.length)‖ := by
      gcongr <;> assumption
    _ = _ := by ring

end HeckeSkeleton.Moments.MOM_INV_STEP.CoefficientBounds

end
