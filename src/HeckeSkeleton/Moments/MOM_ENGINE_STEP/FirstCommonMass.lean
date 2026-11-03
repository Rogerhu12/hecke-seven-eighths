import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualLengths
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CommonHarmonicMass

/-!
# The normalized first common-support mass

The first Cauchy allowances are computed from the literal prime
multiplicities and absolute ideal norms.  Their normalized weight is
bounded by the inverse norm of the actual common radical.  The proved
harmonic count then sums every complete common-support pair and every
subset label, retaining the old-mask density.  No allowance or aggregate
mass inequality is assumed.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open UniqueFactorizationMonoid HeckePort.IdealMobiusDivisorSum CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

def firstActiveRadical (C D : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  ∏ P ∈ (primeSupport C).filter (fun P =>
      (normalizedFactors C).count P % 6 ≠ (normalizedFactors D).count P % 6), P

theorem firstActiveRadical_ne_zero (C D : Ideal (𝓞 K)) : firstActiveRadical C D ≠ 0 :=
  support_product_ne_zero (Finset.filter_subset _ _)

theorem ideal_primeSupport_reconstruct (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    I = ∏ P ∈ primeSupport I, P ^ (normalizedFactors I).count P := by
  calc
    I = (normalizedFactors I).prod := (Ideal.prod_normalizedFactors_eq_self hI).symm
    _ = _ := Finset.prod_multiset_count _

theorem first_actual_common_allowance (Z : ℝ) (hZ : 1 < Z)
    (C D : Ideal (𝓞 K)) (hC : C ≠ 0) (hD : D ≠ 0)
    (hCD : primeSupport C = primeSupport D) :
    firstAllowance (idealLogLength Z C) (idealLogLength Z D)
        (idealLogLength Z (firstActiveRadical C D)) +
      firstAllowance (idealLogLength Z D) (idealLogLength Z C)
        (idealLogLength Z (firstActiveRadical C D)) ≤
      idealLogLength Z C + idealLogLength Z D -
        2 * idealLogLength Z (commonRadical C D) -
        idealLogLength Z (firstActiveRadical C D) := by
  have hc (P : Ideal (𝓞 K)) (hP : P ∈ primeSupport C) :
      1 ≤ (normalizedFactors C).count P :=
    Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hP)
  have hd (P : Ideal (𝓞 K)) (hP : P ∈ primeSupport C) :
      1 ≤ (normalizedFactors D).count P := by
    have hPD : P ∈ primeSupport D := by
      rw [← hCD]
      exact hP
    exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hPD)
  have he := actual_ideal_paired_allowance Z hZ (primeSupport C)
    (fun P : Ideal (𝓞 K) => P)
    (fun P => (normalizedFactors C).count P)
    (fun P => (normalizedFactors D).count P)
    (fun _ _ _ _ h => h) (fun P hP => support_prime hP) hc hd
  dsimp only at he
  have hDp : D = ∏ P ∈ primeSupport C, P ^ (normalizedFactors D).count P := by
    rw [hCD]
    exact ideal_primeSupport_reconstruct D hD
  have hrad : commonRadical C D = ∏ P ∈ primeSupport C, P := by
    simp only [commonRadical, ← hCD, Finset.inter_self]
  rw [← ideal_primeSupport_reconstruct C hC, ← hDp, ← hrad] at he
  exact he

theorem rpow_idealLogLength (Z : ℝ) (hZ : 1 < Z)
    (I : Ideal (𝓞 K)) (hI : I ≠ 0) : Z ^ idealLogLength Z I = (Ideal.absNorm I : ℝ) := by
  have hn : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  rw [idealLogLength, Real.rpow_def_of_pos (zero_lt_one.trans hZ)]
  convert Real.exp_log hn using 1
  congr 1
  field_simp [(Real.log_pos hZ).ne']

/-- The genuine pair allowance divided by both central norm factors. -/
def firstCommonWeight (Z : ℝ) (C D : Ideal (𝓞 K)) : ℝ :=
  Z ^ ((firstAllowance (idealLogLength Z C) (idealLogLength Z D)
          (idealLogLength Z (firstActiveRadical C D)) +
        firstAllowance (idealLogLength Z D) (idealLogLength Z C)
          (idealLogLength Z (firstActiveRadical C D)) +
        idealLogLength Z (firstActiveRadical C D) -
        idealLogLength Z C - idealLogLength Z D) / 2)

theorem firstCommonWeight_norm_formula (Z : ℝ) (hZ : 1 < Z)
    (C D : Ideal (𝓞 K)) (hC : C ≠ 0) (hD : D ≠ 0) :
    firstCommonWeight Z C D =
      (Ideal.absNorm (firstActiveRadical C D) : ℝ) ^ ((1 : ℝ) / 2) *
        Z ^ ((firstAllowance (idealLogLength Z C) (idealLogLength Z D)
            (idealLogLength Z (firstActiveRadical C D)) +
          firstAllowance (idealLogLength Z D) (idealLogLength Z C)
            (idealLogLength Z (firstActiveRadical C D))) / 2) /
        ((Ideal.absNorm C : ℝ) ^ ((1 : ℝ) / 2) *
          (Ideal.absNorm D : ℝ) ^ ((1 : ℝ) / 2)) := by
  have hz := zero_lt_one.trans hZ
  rw [← rpow_idealLogLength Z hZ C hC, ← rpow_idealLogLength Z hZ D hD,
    ← rpow_idealLogLength Z hZ (firstActiveRadical C D) (firstActiveRadical_ne_zero C D)]
  simp only [← Real.rpow_mul hz.le]
  rw [← Real.rpow_add hz, ← Real.rpow_add hz, ← Real.rpow_sub hz]
  unfold firstCommonWeight
  congr 1
  ring

theorem firstCommonWeight_le_radical (Z : ℝ) (hZ : 1 < Z)
    (C D : Ideal (𝓞 K)) (hC : C ≠ 0) (hD : D ≠ 0)
    (hCD : primeSupport C = primeSupport D) :
    firstCommonWeight Z C D ≤ 1 / (Ideal.absNorm (commonRadical C D) : ℝ) := by
  have hb := first_actual_common_allowance Z hZ C D hC hD hCD
  unfold firstCommonWeight
  calc
    _ ≤ Z ^ (-idealLogLength Z (commonRadical C D)) :=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    _ = _ := by
      rw [Real.rpow_neg (zero_lt_one.trans hZ).le,
        rpow_idealLogLength Z hZ _ (commonRadical_ne_zero C D), one_div]

/-- The whole first outer mass includes the exact two allowances, every
common subset, and the inverse density of the original common mask. -/
theorem actual_first_common_mass (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ Z : ℝ, 1 < Z → ∀ s : Ideal (𝓞 K),
      Squarefree s → s ≠ 0 → ∀ labels : Finset (Label K),
      (∀ v ∈ labels, Valid s v) →
      (∀ v ∈ labels, (Ideal.absNorm v.1.1 : ℝ) ≤ Z ^ B ∧
        (Ideal.absNorm v.1.2 : ℝ) ≤ Z ^ B) →
      (∑ v ∈ labels, firstCommonWeight Z v.1.1 v.1.2) ≤
        Cbound * Z ^ δ / (Ideal.absNorm s : ℝ) := by
  obtain ⟨Cbound, hC, hmass⟩ := common_radical_harmonic_mass (K := K) B δ hB hδ
  refine ⟨Cbound, hC, ?_⟩
  intro Z hZ s hs hs0 labels hvalid hnorm
  apply le_trans _ (hmass Z hZ.le s hs hs0 labels hvalid hnorm)
  apply Finset.sum_le_sum
  intro v hv
  exact firstCommonWeight_le_radical Z hZ v.1.1 v.1.2
    (hvalid v hv).1 (hvalid v hv).2.1 (hvalid v hv).2.2.1

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.firstCommonWeight_le_radical
#print axioms HeckeSkeleton.Moments.EngineStep.actual_first_common_mass

