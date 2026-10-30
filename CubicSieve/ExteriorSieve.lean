import CubicSieve.ExteriorKernel
import CubicSieve.FiniteDuality
import CubicSieve.Bootstrap
import DedekindZetaZeroFree.Arithmetic.Ideals.LinearCountingBound
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
The actual squarefree exterior-ideal sieve operator and its exact consumer.
The sharp estimate is an explicit hypothesis in the bridge below.  The
unconditional estimate proved here is the elementary cardinality bound,
which gives the requested shape only when epsilon is at least one third.
-/

set_option autoImplicit false
noncomputable section

namespace CubicSieve.ExteriorSieve

open NumberField IsDedekindDomain
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

def underlyingIdeal (I : ExteriorIdeal K S) : Ideal (𝓞 K) := I.val.val

omit [NumberField K] [Fintype S] in
theorem underlyingIdeal_injective : Function.Injective (underlyingIdeal K S) := by
  intro I J h
  exact Subtype.ext (Subtype.ext h)

theorem finite_cutoff (X : ℝ) :
    {I : ExteriorIdeal K S | Squarefree I.val.val ∧ exteriorNorm K S I ≤ X}.Finite := by
  refine ((DedekindZetaZeroFree.LargeSieve.finite_ideals_absNorm_le K X).preimage
    (underlyingIdeal_injective K S).injOn).subset ?_
  intro I hI
  exact hI.2

def cutoff (X : ℝ) : Finset (ExteriorIdeal K S) := (finite_cutoff K S X).toFinset

@[simp] theorem mem_cutoff (X : ℝ) (I : ExteriorIdeal K S) :
    I ∈ cutoff K S X ↔ Squarefree I.val.val ∧ exteriorNorm K S I ≤ X := by
  exact Set.Finite.mem_toFinset _

theorem cutoff_mono {X Y : ℝ} (hXY : X ≤ Y) : cutoff K S X ⊆ cutoff K S Y := by
  intro I hI
  rcases (mem_cutoff K S X I).mp hI with ⟨hsq, hnorm⟩
  exact (mem_cutoff K S Y I).mpr ⟨hsq, hnorm.trans hXY⟩

theorem cutoff_card_le_ideal_count (X : ℝ) :
    (cutoff K S X).card ≤ (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals K X).card := by
  have hsub : (cutoff K S X).image (underlyingIdeal K S) ⊆
      DedekindZetaZeroFree.LargeSieve.boundedNormIdeals K X := by
    intro I hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals.mpr
      ((mem_cutoff K S X J).mp hJ).2
  simpa only [Finset.card_image_of_injective _ (underlyingIdeal_injective K S)] using
    Finset.card_le_card hsub

/-- The squared norm of the genuine positive-orientation cubic matrix. -/
def B (X Y : ℝ) : ℝ :=
  ‖FiniteKernel.operator (cutoff K S X) (cutoff K S Y)
    (ExteriorKernel.kernel K S D 2)‖ ^ 2

theorem B_nonneg (X Y : ℝ) : 0 ≤ B K S D X Y := sq_nonneg _

theorem cutoff_bound (X Y : ℝ) :
    FiniteKernel.HasBound (cutoff K S X) (cutoff K S Y)
      (ExteriorKernel.kernel K S D 2) (B K S D X Y) :=
  (FiniteKernel.hasBound_iff_norm_sq_le _ _ _ _ (B_nonneg K S D X Y)).mpr le_rfl

theorem B_mono {X Y X' Y' : ℝ} (hX : X ≤ X') (hY : Y ≤ Y') :
    B K S D X Y ≤ B K S D X' Y' := by
  apply (FiniteKernel.hasBound_iff_norm_sq_le _ _ _ _ (B_nonneg K S D X' Y')).mp
  exact FiniteKernel.restrict_bound (cutoff K S X') (cutoff K S X)
    (cutoff K S Y') (cutoff K S Y) (cutoff_mono K S hX) (cutoff_mono K S hY)
    (ExteriorKernel.kernel K S D 2) (B K S D X' Y') (B_nonneg K S D X' Y')
    (cutoff_bound K S D X' Y')

private theorem B_swap_le (hD : AllowedGeneratorInput K S D) (X Y : ℝ) :
    B K S D X Y ≤ B K S D Y X := by
  have ht := FiniteKernel.transpose_bound (cutoff K S Y) (cutoff K S X)
    (ExteriorKernel.kernel K S D 2) (B K S D Y X) (B_nonneg K S D Y X)
    (cutoff_bound K S D Y X)
  have hk : (fun I J : ExteriorIdeal K S => ExteriorKernel.kernel K S D 2 J I) =
      ExteriorKernel.kernel K S D 2 := by
    funext I J
    exact ExteriorKernel.kernel_reciprocity K S D hD 2 J I
  rw [hk] at ht
  exact (FiniteKernel.hasBound_iff_norm_sq_le _ _ _ _ (B_nonneg K S D Y X)).mp ht

/-- Exact reciprocity uses the actual generator-section hypothesis. -/
theorem B_reciprocity (hD : AllowedGeneratorInput K S D) (X Y : ℝ) :
    B K S D X Y = B K S D Y X :=
  le_antisymm (B_swap_le K S D hD X Y) (B_swap_le K S D hD Y X)

/-- The original consumer at one epsilon, including arbitrary subsets and both signs. -/
def TargetAt (ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y →
    ∀ A T : Finset (ExteriorIdeal K S),
      (∀ I ∈ A, Squarefree I.val.val ∧ exteriorNorm K S I ≤ X) →
      (∀ J ∈ T, Squarefree J.val.val ∧ exteriorNorm K S J ≤ Y) →
      ∀ e : ℤ, (e = 2 ∨ e = -2) → ∀ z : ExteriorIdeal K S → ℂ,
        ∑ I ∈ A, ‖∑ J ∈ T, z J * idealSymbol K S D J (D.generator I) ^ e‖ ^ 2 ≤
          C * (X * Y) ^ ε * (X + Y + (X * Y) ^ (2 / 3 : ℝ)) *
            ∑ J ∈ T, ‖z J‖ ^ 2

def TargetBound : Prop := ∀ ε : ℝ, 0 < ε → TargetAt K S D ε

theorem targetAt_of_operator_bound (ε C : ℝ) (hC : 0 < C)
    (hB : ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y →
      B K S D X Y ≤ C * (X * Y) ^ ε * (X + Y + (X * Y) ^ (2 / 3 : ℝ))) :
    TargetAt K S D ε := by
  refine ⟨C, hC, ?_⟩
  intro X Y hX hY A T hA hT e he z
  have hXpos : 0 < X := by linarith
  have hYpos : 0 < Y := by linarith
  let L := C * (X * Y) ^ ε * (X + Y + (X * Y) ^ (2 / 3 : ℝ))
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hb : FiniteKernel.HasBound (cutoff K S X) (cutoff K S Y)
      (ExteriorKernel.kernel K S D 2) L :=
    (FiniteKernel.hasBound_iff_norm_sq_le _ _ _ _ hL).mpr (hB X Y hX hY)
  have hsubA : A ⊆ cutoff K S X := fun I hI => (mem_cutoff K S X I).mpr (hA I hI)
  have hsubT : T ⊆ cutoff K S Y := fun J hJ => (mem_cutoff K S Y J).mpr (hT J hJ)
  have hr := FiniteKernel.restrict_bound (cutoff K S X) A (cutoff K S Y) T
    hsubA hsubT (ExteriorKernel.kernel K S D 2) L hL hb
  have hp : ∀ w : ExteriorIdeal K S → ℂ,
      ExteriorKernel.energy K S D 2 A T w ≤ L * ∑ J ∈ T, ‖w J‖ ^ 2 := by
    intro w
    simpa only [ExteriorKernel.energy, ExteriorKernel.rowSum, FiniteKernel.form,
      FiniteKernel.energy, mul_comm] using hr w
  exact ExteriorKernel.both_orientations_of_positive K S D A T L hp e he z

/-- This is a conditional bridge; it does not prove the sharp arithmetic estimate. -/
theorem target_of_sharp_bound (h : Bootstrap.HasSharpBound (B K S D)) :
    TargetBound K S D := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h ε hε
  exact targetAt_of_operator_bound K S D ε C hC hb

/-- Conversely, the literal arbitrary-coefficient target bounds the full matrix. -/
theorem sharp_bound_of_target (h : TargetBound K S D) :
    Bootstrap.HasSharpBound (B K S D) := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h ε hε
  refine ⟨C, hC, ?_⟩
  intro X Y hX hY
  have hXpos : 0 < X := by linarith
  have hYpos : 0 < Y := by linarith
  let L := C * (X * Y) ^ ε * (X + Y + (X * Y) ^ (2 / 3 : ℝ))
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  apply (FiniteKernel.hasBound_iff_norm_sq_le _ _ _ _ hL).mp
  intro z
  have hz := hb X Y hX hY (cutoff K S X) (cutoff K S Y)
    (fun I hI => (mem_cutoff K S X I).mp hI)
    (fun J hJ => (mem_cutoff K S Y J).mp hJ) 2 (Or.inl rfl) z
  simpa only [FiniteKernel.form, FiniteKernel.energy, ExteriorKernel.kernel,
    ExteriorKernel.symbol, mul_comm] using hz

theorem target_iff_sharp_bound :
    TargetBound K S D ↔ Bootstrap.HasSharpBound (B K S D) :=
  ⟨sharp_bound_of_target K S D, target_of_sharp_bound K S D⟩

private theorem form_le_card_mul_card {α β : Type*} (R : Finset α) (T : Finset β)
    (k : α → β → ℂ) (hk : ∀ i ∈ R, ∀ j ∈ T, ‖k i j‖ ≤ 1) :
    FiniteKernel.HasBound R T k ((R.card : ℝ) * (T.card : ℝ)) := by
  intro z
  have hrow (i : α) (hi : i ∈ R) :
      ‖∑ j ∈ T, k i j * z j‖ ^ 2 ≤ (T.card : ℝ) * FiniteKernel.energy T z := by
    have hn : ‖∑ j ∈ T, k i j * z j‖ ≤ ∑ j ∈ T, ‖z j‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hk i hi j hj)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℝ)) (fun j => ‖z j‖)
    have hcs' : (∑ j ∈ T, ‖z j‖) ^ 2 ≤
        (T.card : ℝ) * FiniteKernel.energy T z := by
      simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
        FiniteKernel.energy] using hcs
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hcs'
  unfold FiniteKernel.form
  calc
    _ ≤ ∑ _i ∈ R, (T.card : ℝ) * FiniteKernel.energy T z :=
      Finset.sum_le_sum hrow
    _ = ((R.card : ℝ) * (T.card : ℝ)) * FiniteKernel.energy T z := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

theorem B_le_card_mul_card (X Y : ℝ) :
    B K S D X Y ≤ ((cutoff K S X).card : ℝ) * ((cutoff K S Y).card : ℝ) := by
  apply (FiniteKernel.hasBound_iff_norm_sq_le _ _ _ _ (by positivity)).mp
  exact form_le_card_mul_card (cutoff K S X) (cutoff K S Y)
    (ExteriorKernel.kernel K S D 2)
    (fun I _ J _ => ExteriorKernel.norm_kernel_le_one K S D 2 (Or.inl rfl) I J)

/-- An unconditional elementary bound; this contains no cancellation estimate. -/
theorem exists_linear_product_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y →
      B K S D X Y ≤ C * X * Y := by
  obtain ⟨C, hC, hc⟩ := DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound K
  have hCpos : 0 < C := by linarith
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro X Y hX hY
  have hcx : ((cutoff K S X).card : ℝ) ≤ C * X :=
    (Nat.cast_le.mpr (cutoff_card_le_ideal_count K S X)).trans (hc X hX)
  have hcy : ((cutoff K S Y).card : ℝ) ≤ C * Y :=
    (Nat.cast_le.mpr (cutoff_card_le_ideal_count K S Y)).trans (hc Y hY)
  calc
    _ ≤ ((cutoff K S X).card : ℝ) * ((cutoff K S Y).card : ℝ) :=
      B_le_card_mul_card K S D X Y
    _ ≤ (C * X) * (C * Y) := mul_le_mul hcx hcy (Nat.cast_nonneg _)
      (mul_nonneg (by linarith) (by linarith))
    _ = C ^ 2 * X * Y := by ring

theorem product_le_sharp_shape (X Y ε : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hε : (1 / 3 : ℝ) ≤ ε) :
    X * Y ≤ (X * Y) ^ ε * (X + Y + (X * Y) ^ (2 / 3 : ℝ)) := by
  have hXY : 1 ≤ X * Y := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have hXYpos : 0 < X * Y := by linarith
  have hp : (X * Y) ^ (1 / 3 : ℝ) ≤ (X * Y) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hXY hε
  calc
    X * Y = (X * Y) ^ (1 / 3 : ℝ) * (X * Y) ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_add hXYpos]
      norm_num
    _ ≤ (X * Y) ^ ε * (X * Y) ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hXYpos.le _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hXYpos.le _)

/-- A genuine bound only for epsilon at least one third; the small-loss range is open. -/
theorem targetAt_of_one_third_le (ε : ℝ) (hε : (1 / 3 : ℝ) ≤ ε) :
    TargetAt K S D ε := by
  obtain ⟨C, hC, hb⟩ := exists_linear_product_bound K S D
  apply targetAt_of_operator_bound K S D ε C hC
  intro X Y hX hY
  calc
    _ ≤ C * X * Y := hb X Y hX hY
    _ = C * (X * Y) := by ring
    _ ≤ C * ((X * Y) ^ ε * (X + Y + (X * Y) ^ (2 / 3 : ℝ))) :=
      mul_le_mul_of_nonneg_left (product_le_sharp_shape X Y ε hX hY hε) hC.le
    _ = _ := by ring

end CubicSieve.ExteriorSieve
