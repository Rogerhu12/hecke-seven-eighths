import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalMaskCardinality
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalCoverCardinality

/-!
# Uniform small powers for the actual omitted finite coordinates

There are two Boolean subset coordinates and four original extraction
tuples.  The former are bounded by their original mask ideals; the
latter by their original extracted ideals.  Each receives epsilon/6.
The finite character count and fixed dyadic coordinate box contribute
only to the constant, chosen before all scales, ideals and sources.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.OriginalFiniteFibre

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LargeSieve

variable {K : Type} [Field K] [NumberField K]

def coordinateCount {α β : Type*} (M : Finset α) (support : Finset β)
    (I₁ I₂ D E : Ideal (𝓞 K)) (cap classifierCount dimension width : ℕ) : ℕ :=
  2 ^ M.card * idealDivisorCount I₁ ^ (cap + 2) * idealDivisorCount I₂ ^ (cap + 2) *
    (2 ^ support.card * classifierCount * (width + 1) ^ dimension) *
      idealDivisorCount D ^ (cap + 2) * idealDivisorCount E ^ (cap + 2)

private def coordinateCardinalCount (m n : ℕ)
    (I₁ I₂ D E : Ideal (𝓞 K)) (cap classifierCount dimension width : ℕ) : ℕ :=
  2 ^ m * idealDivisorCount I₁ ^ (cap + 2) * idealDivisorCount I₂ ^ (cap + 2) *
    (2 ^ n * classifierCount * (width + 1) ^ dimension) *
      idealDivisorCount D ^ (cap + 2) * idealDivisorCount E ^ (cap + 2)

/-- Select the real constant using only natural cardinalities. No carrier
universe occurs in the proposition from which this constant is chosen. -/
private theorem coordinate_cardinal_uniform_subpower
    (cap classifierCount dimension width : ℕ)
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ (m n : ℕ) (Rmask Rrow I₁ I₂ D E : Ideal (𝓞 K)),
        (Ideal.absNorm Rmask : ℝ) ≤ Z ^ B →
        (Ideal.absNorm Rrow : ℝ) ≤ Z ^ B →
        (Ideal.absNorm I₁ : ℝ) ≤ Z ^ B →
        (Ideal.absNorm I₂ : ℝ) ≤ Z ^ B →
        (Ideal.absNorm D : ℝ) ≤ Z ^ B →
        (Ideal.absNorm E : ℝ) ≤ Z ^ B →
        2 ^ m ≤ idealDivisorCount Rmask → 2 ^ n ≤ idealDivisorCount Rrow →
        (coordinateCardinalCount m n I₁ I₂ D E cap classifierCount dimension width : ℝ) ≤
          C * Z ^ ε := by
  let δ : ℝ := ε / 6
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Cm, hCm, hm⟩ := support_tuple_multiplicity_subpower (K := K) 1 B δ hB hδ
  obtain ⟨Cd, hCd, hd⟩ := support_tuple_multiplicity_subpower (K := K) (cap + 2) B δ hB hδ
  let fixed : ℝ := (classifierCount : ℝ) * ((width + 1 : ℕ) : ℝ) ^ dimension
  have hfixed : 0 ≤ fixed := by dsimp [fixed]; positivity
  refine ⟨Cm ^ 2 * Cd ^ 4 * (fixed + 1), by positivity, ?_⟩
  intro Z hZ m n Rmask Rrow I₁ I₂ D E
    hNmask hNrow hNI₁ hNI₂ hND hNE hM hS
  let t : ℝ := Z ^ δ
  have ht : 0 ≤ t := Real.rpow_nonneg (zero_le_one.trans hZ) _
  have hmt : 0 ≤ Cm * t := mul_nonneg hCm.le ht
  have hdt : 0 ≤ Cd * t := mul_nonneg hCd.le ht
  have hmaskCount : (2 : ℝ) ^ m ≤ (idealDivisorCount Rmask : ℝ) := by
    exact_mod_cast hM
  have hrowCount : (2 : ℝ) ^ n ≤ (idealDivisorCount Rrow : ℝ) := by
    exact_mod_cast hS
  have hmask : (2 : ℝ) ^ m ≤ Cm * t :=
    hmaskCount.trans (by simpa only [pow_one] using hm Z hZ Rmask hNmask)
  have hrow : (2 : ℝ) ^ n ≤ Cm * t :=
    hrowCount.trans (by simpa only [pow_one] using hm Z hZ Rrow hNrow)
  have hI₁ := hd Z hZ I₁ hNI₁
  have hI₂ := hd Z hZ I₂ hNI₂
  have hD := hd Z hZ D hND
  have hE := hd Z hZ E hNE
  have hmaskpair : (2 : ℝ) ^ m * (2 : ℝ) ^ n ≤ (Cm * t) ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul hmask hrow (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hmt
  have hfirst : (idealDivisorCount I₁ : ℝ) ^ (cap + 2) *
      (idealDivisorCount I₂ : ℝ) ^ (cap + 2) ≤ (Cd * t) ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul hI₁ hI₂ (pow_nonneg (Nat.cast_nonneg _) _) hdt
  have hsecond : (idealDivisorCount D : ℝ) ^ (cap + 2) *
      (idealDivisorCount E : ℝ) ^ (cap + 2) ≤ (Cd * t) ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul hD hE (pow_nonneg (Nat.cast_nonneg _) _) hdt
  have hfour :
      ((idealDivisorCount I₁ : ℝ) ^ (cap + 2) * (idealDivisorCount I₂ : ℝ) ^ (cap + 2)) *
        ((idealDivisorCount D : ℝ) ^ (cap + 2) * (idealDivisorCount E : ℝ) ^ (cap + 2)) ≤
          (Cd * t) ^ 4 := by
    calc
      _ ≤ (Cd * t) ^ 2 * (Cd * t) ^ 2 :=
        mul_le_mul hfirst hsecond (by positivity) (sq_nonneg _)
      _ = _ := by ring
  have ht6 : t ^ 6 = Z ^ ε := by
    dsimp only [t]
    rw [← Real.rpow_mul_natCast (zero_le_one.trans hZ)]
    congr 1
    dsimp only [δ]
    norm_num
  calc
    _ = ((2 : ℝ) ^ m * (2 : ℝ) ^ n) *
        (((idealDivisorCount I₁ : ℝ) ^ (cap + 2) * (idealDivisorCount I₂ : ℝ) ^ (cap + 2)) *
          ((idealDivisorCount D : ℝ) ^ (cap + 2) * (idealDivisorCount E : ℝ) ^ (cap + 2))) * fixed := by
      simp only [coordinateCardinalCount, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, fixed]
      ring
    _ ≤ (Cm * t) ^ 2 * (Cd * t) ^ 4 * fixed :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hmaskpair hfour (by positivity) (sq_nonneg _)) hfixed
    _ = (Cm ^ 2 * Cd ^ 4 * fixed) * t ^ 6 := by ring
    _ = (Cm ^ 2 * Cd ^ 4 * fixed) * Z ^ ε := by rw [ht6]
    _ ≤ (Cm ^ 2 * Cd ^ 4 * (fixed + 1)) * Z ^ ε := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hZ) _)
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (by positivity)

theorem coordinate_uniform_subpower (cap classifierCount dimension width : ℕ)
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ {α β : Type*} (M : Finset α) (support : Finset β)
        (Rmask Rrow I₁ I₂ D E : Ideal (𝓞 K)),
        Rmask ≠ 0 → Rrow ≠ 0 →
        (Ideal.absNorm Rmask : ℝ) ≤ Z ^ B →
        (Ideal.absNorm Rrow : ℝ) ≤ Z ^ B →
        (Ideal.absNorm I₁ : ℝ) ≤ Z ^ B →
        (Ideal.absNorm I₂ : ℝ) ≤ Z ^ B →
        (Ideal.absNorm D : ℝ) ≤ Z ^ B →
        (Ideal.absNorm E : ℝ) ≤ Z ^ B →
        OriginalMaskPrimeData M Rmask → OriginalMaskPrimeData support Rrow →
        (coordinateCount M support I₁ I₂ D E cap classifierCount dimension width : ℝ) ≤
          C * Z ^ ε := by
  obtain ⟨C, hC, hbound⟩ := coordinate_cardinal_uniform_subpower (K := K)
    cap classifierCount dimension width B ε hB hε
  refine ⟨C, hC, ?_⟩
  intro Z hZ α β M support Rmask Rrow I₁ I₂ D E
    hRmask hRrow hNmask hNrow hNI₁ hNI₂ hND hNE WM WR
  have hM : 2 ^ M.card ≤ idealDivisorCount Rmask := by
    simpa only [Finset.card_powerset] using WM.powerset_card_le_divisorCount hRmask
  have hS : 2 ^ support.card ≤ idealDivisorCount Rrow := by
    simpa only [Finset.card_powerset] using WR.powerset_card_le_divisorCount hRrow
  simpa only [coordinateCount, coordinateCardinalCount] using
    hbound Z hZ M.card support.card Rmask Rrow I₁ I₂ D E
      hNmask hNrow hNI₁ hNI₂ hND hNE hM hS

/-- This particular constant is selected solely from the earlier
fixed cap, classifier box and epsilon allocation. -/
def coordinateConstant (cap classifierCount dimension width : ℕ)
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) : ℝ :=
  Classical.choose (coordinate_cardinal_uniform_subpower (K := K)
    cap classifierCount dimension width B ε hB hε)

theorem coordinateConstant_pos (cap classifierCount dimension width : ℕ)
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    0 < coordinateConstant (K := K) cap classifierCount dimension width B ε hB hε :=
  (Classical.choose_spec (coordinate_cardinal_uniform_subpower (K := K)
    cap classifierCount dimension width B ε hB hε)).1

theorem coordinateCount_le (cap classifierCount dimension width : ℕ)
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (Z : ℝ) (hZ : 1 ≤ Z)
    {α β : Type*} (M : Finset α) (support : Finset β)
    (Rmask Rrow I₁ I₂ D E : Ideal (𝓞 K))
    (hRmask : Rmask ≠ 0) (hRrow : Rrow ≠ 0)
    (hNmask : (Ideal.absNorm Rmask : ℝ) ≤ Z ^ B)
    (hNrow : (Ideal.absNorm Rrow : ℝ) ≤ Z ^ B)
    (hNI₁ : (Ideal.absNorm I₁ : ℝ) ≤ Z ^ B)
    (hNI₂ : (Ideal.absNorm I₂ : ℝ) ≤ Z ^ B)
    (hND : (Ideal.absNorm D : ℝ) ≤ Z ^ B)
    (hNE : (Ideal.absNorm E : ℝ) ≤ Z ^ B)
    (WM : OriginalMaskPrimeData M Rmask) (WR : OriginalMaskPrimeData support Rrow) :
    (coordinateCount M support I₁ I₂ D E cap classifierCount dimension width : ℝ) ≤
      coordinateConstant (K := K) cap classifierCount dimension width B ε hB hε * Z ^ ε := by
  have hM : 2 ^ M.card ≤ idealDivisorCount Rmask := by
    simpa only [Finset.card_powerset] using WM.powerset_card_le_divisorCount hRmask
  have hS : 2 ^ support.card ≤ idealDivisorCount Rrow := by
    simpa only [Finset.card_powerset] using WR.powerset_card_le_divisorCount hRrow
  simpa only [coordinateCount, coordinateCardinalCount, coordinateConstant] using
    (Classical.choose_spec (coordinate_cardinal_uniform_subpower (K := K)
      cap classifierCount dimension width B ε hB hε)).2 Z hZ
        M.card support.card Rmask Rrow I₁ I₂ D E
        hNmask hNrow hNI₁ hNI₂ hND hNE hM hS

end HeckeSkeleton.Moments.EngineStep.OriginalFiniteFibre

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalFiniteFibre.coordinate_uniform_subpower
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalFiniteFibre.coordinateCount_le
