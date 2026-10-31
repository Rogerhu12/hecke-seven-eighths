module

public import HeckePort.CenteredMoment.Mask
public import HeckeSkeleton.Moments.MOM_INV_STEP.IntegralEnergy

/-!
# Full mutual-gcd extension before the positive energy step

The starting expression is the genuine coprime residual sum. Its complete
joint kernel is retained when the mutual coprimality mask is expanded.
The common divisor pool is the union of the actual ideal-divisor sets of
the left source; it is not an extra hypothetical range. After this exact
extension, the same Fourier density separates both columns. The signed
Moebius factor becomes one common positive weight only at Cauchy.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOMInvStep.FullMobius

open NumberField IsDedekindDomain UniqueFactorizationMonoid MeasureTheory
open DedekindZetaZeroFree.LargeSieve
open HeckeSkeleton.Moments.MOM_INV_STEP.CommonKernel IntegralEnergy
open scoped Classical BigOperators NumberField FourierTransform

variable {K : Type*} [Field K] [NumberField K]
variable {ι κ : Type*}

def divisorPool (T : Finset ι) (A : ι → Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  T.biUnion fun i => idealDivisors (A i)

theorem mem_divisorPool (T : Finset ι) (A : ι → Ideal (𝓞 K))
    (i : ι) (hi : i ∈ T) (D : Ideal (𝓞 K)) (hD : D ∈ idealDivisors (A i)) :
    D ∈ divisorPool T A := Finset.mem_biUnion.mpr ⟨i, hi, hD⟩

theorem mutual_mask_eq_sum (T : Finset ι) (A : ι → Ideal (𝓞 K))
    (i : ι) (hi : i ∈ T) (hA : A i ≠ ⊥) (B : Ideal (𝓞 K)) :
    (if IsCoprime (A i) B then (1 : ℂ) else 0) =
      ∑ D ∈ divisorPool T A,
        if D ∣ A i ∧ D ∣ B then (moebius D : ℂ) else 0 := by
  calc
    _ = ∑ D ∈ idealDivisors (A i), if D ∣ B then (moebius D : ℂ) else 0 := by
      rw [isCoprime_comm]
      exact HeckePort.CenteredMomentMask.ideal_coprime_mobius B (A i) hA
    _ = ∑ D ∈ idealDivisors (A i),
        if D ∣ A i ∧ D ∣ B then (moebius D : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro D hD
      simp only [(mem_idealDivisors hA).mp hD, true_and]
    _ = _ := by
      apply Finset.sum_subset (fun D hD => mem_divisorPool T A i hi D hD)
      intro D _hD hnot
      have hn : ¬D ∣ A i := fun hd => hnot ((mem_idealDivisors hA).mpr hd)
      simp only [hn, false_and, ite_false]

/-- The whole residual kernel is extended. No separated or bounded
replacement of it is used on the genuine coprime locus. -/
theorem full_mobius_expansion (T : Finset ι) (U : Finset κ)
    (A : ι → Ideal (𝓞 K)) (B : κ → Ideal (𝓞 K))
    (hA : ∀ i ∈ T, A i ≠ ⊥) (H : ι → κ → ℂ) :
    (∑ i ∈ T, ∑ j ∈ U, if IsCoprime (A i) (B j) then H i j else 0) =
      ∑ D ∈ divisorPool T A, (moebius D : ℂ) *
        ∑ i ∈ T with D ∣ A i, ∑ j ∈ U with D ∣ B j, H i j := by
  have hterm (i : ι) (hi : i ∈ T) (j : κ) :
      (if IsCoprime (A i) (B j) then H i j else 0) =
        ∑ D ∈ divisorPool T A, (moebius D : ℂ) *
          (if D ∣ A i then if D ∣ B j then H i j else 0 else 0) := by
    calc
      _ = (if IsCoprime (A i) (B j) then (1 : ℂ) else 0) * H i j := by
        split_ifs <;> simp
      _ = _ := by
        rw [mutual_mask_eq_sum T A i hi (hA i hi), Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro D _hD
        by_cases ha : D ∣ A i <;> by_cases hb : D ∣ B j <;> simp [ha, hb]
  calc
    _ = ∑ i ∈ T, ∑ j ∈ U, ∑ D ∈ divisorPool T A, (moebius D : ℂ) *
        (if D ∣ A i then if D ∣ B j then H i j else 0 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_congr rfl (fun j _hj => hterm i hi j)
    _ = ∑ D ∈ divisorPool T A, ∑ i ∈ T, ∑ j ∈ U, (moebius D : ℂ) *
        (if D ∣ A i then if D ∣ B j then H i j else 0 else 0) := by
      simp_rw [Finset.sum_comm U (divisorPool T A)]
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D _hD
      simp only [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases ha : D ∣ A i
      · simp only [ha, ite_true, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        by_cases hb : D ∣ B j <;> simp [hb]
      · simp [ha]

/-- Full Moebius extension followed by the actual logarithmic Fourier
inversion. Both columns keep the same whole joint profile. -/
theorem full_mobius_separated (T : Finset ι) (U : Finset κ)
    (A : ι → Ideal (𝓞 K)) (B : κ → Ideal (𝓞 K))
    (hA : ∀ i ∈ T, A i ≠ ⊥) (F : SchwartzMap LogPlane ℂ)
    (x : ι → ℝ) (y : κ → ℝ) (a : ι → ℂ) (b : κ → ℂ) :
    (∑ i ∈ T, ∑ j ∈ U, if IsCoprime (A i) (B j) then
      a i * b j * F (logPoint (x i) (y j)) else 0) =
      ∑ D ∈ divisorPool T A, (moebius D : ℂ) *
        ∫ ξ : LogPlane, (𝓕 F) ξ *
          (∑ i ∈ T with D ∣ A i, a i * columnPhase ξ.fst (x i)) *
          (∑ j ∈ U with D ∣ B j, b j * columnPhase ξ.snd (y j)) := by
  rw [full_mobius_expansion T U A B hA]
  apply Finset.sum_congr rfl
  intro D _hD
  rw [finite_bilinear_separated]

/-- Cauchy over one positive outer measure. In particular, the absolute
Moebius factor is charged once after taking the two square roots. -/
theorem common_weighted_cauchy {δ : Type*} (T : Finset δ)
    (w L R : δ → ℝ) (hw : ∀ t ∈ T, 0 ≤ w t)
    (hL : ∀ t ∈ T, 0 ≤ L t) (hR : ∀ t ∈ T, 0 ≤ R t) :
    (∑ t ∈ T, w t * (Real.sqrt (L t) * Real.sqrt (R t))) ≤
      Real.sqrt (∑ t ∈ T, w t * L t) * Real.sqrt (∑ t ∈ T, w t * R t) := by
  have hs (V : δ → ℝ) (hV : ∀ t ∈ T, 0 ≤ V t) :
      (∑ t ∈ T, (Real.sqrt (w t) * Real.sqrt (V t)) ^ 2) =
        ∑ t ∈ T, w t * V t := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [mul_pow, Real.sq_sqrt (hw t ht), Real.sq_sqrt (hV t ht)]
  calc
    _ = ∑ t ∈ T, (Real.sqrt (w t) * Real.sqrt (L t)) *
        (Real.sqrt (w t) * Real.sqrt (R t)) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [show (Real.sqrt (w t) * Real.sqrt (L t)) *
          (Real.sqrt (w t) * Real.sqrt (R t)) =
          (Real.sqrt (w t)) ^ 2 * (Real.sqrt (L t) * Real.sqrt (R t)) by ring,
        Real.sq_sqrt (hw t ht)]
    _ ≤ _ := by
      simpa only [hs L hL, hs R hR] using Real.sum_mul_le_sqrt_mul_sqrt T
        (fun t => Real.sqrt (w t) * Real.sqrt (L t))
        (fun t => Real.sqrt (w t) * Real.sqrt (R t))

/-- Positive inverse-column norms for the original coprime residual
bilinear source. The whole Fourier density is inside both energies. -/
theorem full_mobius_energy (T : Finset ι) (U : Finset κ)
    (A : ι → Ideal (𝓞 K)) (B : κ → Ideal (𝓞 K))
    (hA : ∀ i ∈ T, A i ≠ ⊥) (F : SchwartzMap LogPlane ℂ)
    (x : ι → ℝ) (y : κ → ℝ) (a : ι → ℂ) (b : κ → ℂ) :
    ‖∑ i ∈ T, ∑ j ∈ U, if IsCoprime (A i) (B j) then
      a i * b j * F (logPoint (x i) (y j)) else 0‖ ≤
      Real.sqrt (∑ D ∈ divisorPool T A, ‖(moebius D : ℂ)‖ *
        ∫ ξ : LogPlane, ‖(𝓕 F) ξ‖ *
          ‖∑ i ∈ T with D ∣ A i, a i * columnPhase ξ.fst (x i)‖ ^ 2) *
      Real.sqrt (∑ D ∈ divisorPool T A, ‖(moebius D : ℂ)‖ *
        ∫ ξ : LogPlane, ‖(𝓕 F) ξ‖ *
          ‖∑ j ∈ U with D ∣ B j, b j * columnPhase ξ.snd (y j)‖ ^ 2) := by
  rw [full_mobius_expansion T U A B hA]
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun D hD => ?_)).trans
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (finite_bilinear_energy (T.filter fun i => D ∣ A i)
        (U.filter fun j => D ∣ B j) F x y a b) (norm_nonneg _)
  · apply common_weighted_cauchy
    · exact fun _ _ => norm_nonneg _
    · intro D hD
      exact integral_nonneg fun ξ => mul_nonneg (norm_nonneg _) (sq_nonneg _)
    · intro D hD
      exact integral_nonneg fun ξ => mul_nonneg (norm_nonneg _) (sq_nonneg _)

end HeckeSkeleton.Moments.MOMInvStep.FullMobius

end
