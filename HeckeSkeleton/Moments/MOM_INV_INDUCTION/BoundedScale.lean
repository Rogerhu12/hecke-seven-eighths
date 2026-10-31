import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ActualMoments
import HeckeGeneral.Analysis.IdealMobiusReciprocal
import DedekindZetaZeroFree.Arithmetic.Ideals.LinearCountingBound

/-!
# The bounded range of the independent inverse moment

An eventual canonical estimate leaves a compact range of the independent
scales.  Here that range is bounded directly from the literal ideal
polynomial: the unitary character coefficients and the common zero mask
are contractions, and the support is counted by the ideal norm.  No
moment estimate or arithmetic row calibration is needed for this finite
range.  All constants precede the varying moment data and both scales.
-/

set_option autoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

/-- The complete row ball used before sixth-power amplification. -/
def completeIndependentInverseEnergy {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (U D : ℝ) : ℝ :=
  ∑ u ∈ d.rows (2 * U), ‖inversePolynomial d u D 0‖ ^ 2

/-- The original sixth-free energy is a positive sub-sum of the full
row ball. Both use exactly the same polynomial and common mask. -/
theorem independentInverseEnergy_le_complete {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (U D : ℝ) :
    independentInverseEnergy d U D ≤ completeIndependentInverseEnergy d U D := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => sq_nonneg _)

private theorem multiset_prod_zero_or_norm_one (s : Multiset ℂ)
    (hs : ∀ z ∈ s, z = 0 ∨ ‖z‖ = 1) : s.prod = 0 ∨ ‖s.prod‖ = 1 := by
  induction s using Multiset.induction with
  | empty => simp
  | cons z s ih =>
    rcases hs z (Multiset.mem_cons_self z s) with hz | hz
    · left
      simp [hz]
    · rcases ih (fun w hw => hs w (Multiset.mem_cons_of_mem hw)) with ht | ht
      · left
        simp [ht]
      · right
        simp [Multiset.prod_cons, norm_mul, hz, ht]

/-- The zero extension is retained when the character coefficient is
inverted.  This stronger fact, rather than a one-sided norm bound, is
what justifies the negative orientation in `inversePolynomial`. -/
theorem hecke_coefficient_zero_or_norm_one (χ : HeckeCharacter K)
    (I : NonzeroIdeal K) :
    heckeIdealCoefficient K χ I = 0 ∨ ‖heckeIdealCoefficient K χ I‖ = 1 := by
  have hI : I.val ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  unfold heckeIdealCoefficient nonzeroIdealCoefficient idealCoefficient
  rw [if_neg hI]
  apply multiset_prod_zero_or_norm_one
  intro z hz
  obtain ⟨P, _hP, rfl⟩ := Multiset.mem_map.mp hz
  unfold primeIdealValue
  split_ifs with hP
  · unfold primeCoefficient
    split_ifs <;> simp
  · simp

theorem directed_coefficient_norm_le_one {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (u I : NonzeroIdeal K) :
    ‖heckeIdealCoefficient K (d.rowCharacter u) I ^ d.direction‖ ≤ 1 := by
  rcases hecke_coefficient_zero_or_norm_one (d.rowCharacter u) I with hz | hz
  · rw [hz]
    rcases d.direction_spec with hd | hd <;> simp [hd]
  · rw [norm_zpow, hz, one_zpow]

theorem common_mask_norm_le_one {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (u : NonzeroIdeal K) (I : Ideal (𝓞 K)) :
    ‖maskValue d u I‖ ≤ 1 := by
  unfold maskValue
  split_ifs <;> norm_num

/-- Counting the actual finite support bounds the normalized polynomial
uniformly for every column scale at least one. -/
theorem inversePolynomial_norm_le_support {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (u : NonzeroIdeal K) {D B : ℝ}
    (hD : 1 ≤ D) (hB : 0 ≤ B)
    (hprofile : ∀ I ∈ d.inverseTest.support u 0 D,
      ‖d.inverseTest.profile u 0 (idealNorm K I / D)‖ ≤ B) :
    ‖inversePolynomial d u D 0‖ ≤
      ((d.inverseTest.support u 0 D).card : ℝ) * B := by
  have hterm : ∀ I ∈ d.inverseTest.support u 0 D,
      ‖(UniqueFactorizationMonoid.moebius I.val : ℂ) *
        heckeIdealCoefficient K d.inverseBackground I *
        heckeIdealCoefficient K (d.rowCharacter u) I ^ d.direction *
        d.inverseTest.profile u 0 (idealNorm K I / D) * maskValue d u I.val‖ ≤ B := by
    intro I hI
    simp only [norm_mul]
    calc
      _ ≤ ((1 * 1) * 1) * B * 1 := by
        gcongr
        · exact IdealMobiusReciprocal.norm_moebius_le_one K I
        · exact norm_heckeIdealCoefficient_le_one K d.inverseBackground I
        · exact directed_coefficient_norm_le_one d u I
        · exact hprofile I hI
        · exact common_mask_norm_le_one d u I.val
      _ = B := by ring
  have hsum : ‖∑ I ∈ d.inverseTest.support u 0 D,
      (UniqueFactorizationMonoid.moebius I.val : ℂ) *
        heckeIdealCoefficient K d.inverseBackground I *
        heckeIdealCoefficient K (d.rowCharacter u) I ^ d.direction *
        d.inverseTest.profile u 0 (idealNorm K I / D) * maskValue d u I.val‖ ≤
        ((d.inverseTest.support u 0 D).card : ℝ) * B := by
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans_eq (by simp))
  have hsqrt : 1 ≤ Real.sqrt D := by
    simpa using Real.sqrt_le_sqrt hD
  have hnorm : ‖(Real.sqrt D : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg D)]
    exact inv_le_one_of_one_le₀ hsqrt
  rw [inversePolynomial, norm_mul]
  calc
    _ ≤ 1 * (((d.inverseTest.support u 0 D).card : ℝ) * B) := by
      exact mul_le_mul hnorm hsum (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

/-- The ideal-counting constant also counts nonzero ideals, without
changing the original row or column support. -/
theorem exists_nonzero_ideal_count_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (s : Finset (NonzeroIdeal K)) (X : ℝ),
      1 ≤ X → (∀ I ∈ s, idealNorm K I ≤ X) → (s.card : ℝ) ≤ C * X := by
  obtain ⟨C, hC, _hcount, hfinite⟩ :=
    DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound_finset K
  refine ⟨C, hC, ?_⟩
  intro s X hX hs
  have hi : Function.Injective (fun I : NonzeroIdeal K => I.val) := Subtype.val_injective
  have hcard : (s.image (fun I => I.val)).card = s.card := Finset.card_image_of_injective s hi
  have hb := hfinite X hX (s.image (fun I => I.val)) (by
    intro I hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact hs J hJ)
  simpa only [hcard] using hb

/-- A common bound for the full compact scale range.  The height
dependence is still in the explicit profile bound `B`; the square is
the square appearing in the actual moment. -/
theorem exists_bounded_complete_scale_inverse_bound (R b : ℝ) (hR : 1 ≤ R) (hb : 1 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ω ψ : HeckeCharacter K}
      (d : MomentData K ω ψ) (U D B : ℝ),
      1 ≤ U → U ≤ R → 1 ≤ D → D ≤ R → 0 ≤ B →
      (∀ u I, I ∈ d.inverseTest.support u 0 D → idealNorm K I / D ≤ b) →
      (∀ u I, I ∈ d.inverseTest.support u 0 D →
        ‖d.inverseTest.profile u 0 (idealNorm K I / D)‖ ≤ B) →
      completeIndependentInverseEnergy d U D ≤ C * B ^ 2 := by
  obtain ⟨A, hA, hcount⟩ := exists_nonzero_ideal_count_bound (K := K)
  let C := (A * (2 * R)) * (A * (b * R)) ^ 2
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hbp : 0 < b := zero_lt_one.trans_le hb
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro ω ψ d U D B hU hUR hD hDR hB hsupport hprofile
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hcol (u : NonzeroIdeal K) :
      ((d.inverseTest.support u 0 D).card : ℝ) ≤ A * (b * R) := by
    apply hcount _ _ (one_le_mul_of_one_le_of_one_le hb hR)
    intro I hI
    exact ((div_le_iff₀ hDpos).mp (hsupport u I hI)).trans
      (mul_le_mul_of_nonneg_left hDR hbp.le)
  have hpoint (u : NonzeroIdeal K) :
      ‖inversePolynomial d u D 0‖ ≤ A * (b * R) * B :=
    (inversePolynomial_norm_le_support d u hD hB (hprofile u)).trans
      (mul_le_mul_of_nonneg_right (hcol u) hB)
  let rows := d.rows (2 * U)
  have hrows : (rows.card : ℝ) ≤ A * (2 * R) := by
    apply hcount _ _ (by linarith)
    intro I hI
    have hrow := (d.rows_spec (2 * U) I).mp hI
    exact hrow.2.trans (by linarith)
  have hpoint2 (u : NonzeroIdeal K) :
      ‖inversePolynomial d u D 0‖ ^ 2 ≤ (A * (b * R) * B) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hpoint u) 2
  calc
    completeIndependentInverseEnergy d U D ≤
        ∑ _u ∈ rows, (A * (b * R) * B) ^ 2 := by
      exact Finset.sum_le_sum (fun u _ => hpoint2 u)
    _ = (rows.card : ℝ) * (A * (b * R) * B) ^ 2 := by simp
    _ ≤ (A * (2 * R)) * (A * (b * R) * B) ^ 2 :=
      mul_le_mul_of_nonneg_right hrows (sq_nonneg _)
    _ = C * B ^ 2 := by dsimp only [C]; ring

/-- The same constant controls the skeleton's sixth-free specialization. -/
theorem exists_bounded_scale_inverse_bound (R b : ℝ) (hR : 1 ≤ R) (hb : 1 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ω ψ : HeckeCharacter K}
      (d : MomentData K ω ψ) (U D B : ℝ),
      1 ≤ U → U ≤ R → 1 ≤ D → D ≤ R → 0 ≤ B →
      (∀ u I, I ∈ d.inverseTest.support u 0 D → idealNorm K I / D ≤ b) →
      (∀ u I, I ∈ d.inverseTest.support u 0 D →
        ‖d.inverseTest.profile u 0 (idealNorm K I / D)‖ ≤ B) →
      independentInverseEnergy d U D ≤ C * B ^ 2 := by
  obtain ⟨C, hC, hbnd⟩ := exists_bounded_complete_scale_inverse_bound (K := K) R b hR hb
  exact ⟨C, hC, fun d U D B hU hUR hD hDR hB hs hp =>
    (independentInverseEnergy_le_complete d U D).trans
      (hbnd d U D B hU hUR hD hDR hB hs hp)⟩

end HeckeSkeleton.Moments.MOM_INV_INDUCTION
