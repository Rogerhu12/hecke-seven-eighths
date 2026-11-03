import DedekindZetaZeroFree.Analysis.FiniteMatrixDualityAndPhases
import DedekindZetaZeroFree.Analysis.QuadraticFormRestriction

/-!
# Finite complex kernels for the cubic large sieve

These are finite Hilbert-space facts, with independent complex column
coefficients. They impose no arithmetic character-family hypothesis.
In particular, transpose duality alone does not identify the transpose of
a residue-symbol kernel with the arithmetic kernel with its ideals reversed:
that step needs an actual reciprocity identity, including its finite phases
and its common-prime zeros.

Nothing in this file asserts a cubic large sieve estimate.
-/

noncomputable section

namespace CubicSieve.FiniteKernel

open scoped Classical BigOperators

variable {α β γ κ δ : Type*}

def energy (S : Finset β) (z : β → ℂ) : ℝ :=
  ∑ j ∈ S, ‖z j‖ ^ 2

def form (R : Finset α) (S : Finset β) (K : α → β → ℂ) (z : β → ℂ) : ℝ :=
  ∑ i ∈ R, ‖∑ j ∈ S, K i j * z j‖ ^ 2

def HasBound (R : Finset α) (S : Finset β) (K : α → β → ℂ) (D : ℝ) : Prop :=
  ∀ z : β → ℂ, form R S K z ≤ D * energy S z

def matrix (R : Finset α) (S : Finset β) (K : α → β → ℂ) : Matrix R S ℂ :=
  fun i j => K i j

def operator (R : Finset α) (S : Finset β) (K : α → β → ℂ) :
    EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ R :=
  (matrix R S K).toEuclideanLin.toContinuousLinearMap

theorem energy_nonneg (S : Finset β) (z : β → ℂ) : 0 ≤ energy S z := by
  unfold energy
  positivity

theorem form_nonneg (R : Finset α) (S : Finset β) (K : α → β → ℂ) (z : β → ℂ) :
    0 ≤ form R S K z := by
  unfold form
  positivity

theorem form_eq_norm_sq (R : Finset α) (S : Finset β) (K : α → β → ℂ)
    (z : β → ℂ) :
    form R S K z =
      ‖operator R S K (WithLp.toLp 2 (fun j : S => z j))‖ ^ 2 := by
  classical
  unfold form
  rw [EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_subtype (s := R) (p := fun i => i ∈ R) (fun _ => Iff.rfl)
    (f := fun i => ‖∑ j ∈ S, K i j * z j‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  change (∑ j ∈ S, K i j * z j) = ∑ j : S, K i j * z j
  rw [Finset.sum_subtype (s := S) (p := fun j => j ∈ S) (fun _ => Iff.rfl)
    (f := fun j => K i j * z j)]

theorem energy_eq_norm_sq (S : Finset β) (z : β → ℂ) :
    energy S z = ‖(WithLp.toLp 2 (fun j : S => z j) : EuclideanSpace ℂ S)‖ ^ 2 := by
  classical
  unfold energy
  rw [EuclideanSpace.norm_sq_eq]
  exact (Finset.sum_subtype (s := S) (p := fun j => j ∈ S) (fun _ => Iff.rfl)
    (f := fun j => ‖z j‖ ^ 2))

theorem hasBound_iff_norm_sq_le (R : Finset α) (S : Finset β)
    (K : α → β → ℂ) (D : ℝ) (hD : 0 ≤ D) :
    HasBound R S K D ↔ ‖operator R S K‖ ^ 2 ≤ D := by
  classical
  constructor
  · intro h
    have hT : ‖operator R S K‖ ≤ Real.sqrt D := by
      apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg D)
      intro v
      let z : β → ℂ := fun j => if hj : j ∈ S then v ⟨j, hj⟩ else 0
      have hz : (WithLp.toLp 2 (fun j : S => z j) : EuclideanSpace ℂ S) = v := by
        ext j
        simp [z]
      have hv := h z
      rw [form_eq_norm_sq, energy_eq_norm_sq, hz] at hv
      apply (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
      simpa [mul_pow, Real.sq_sqrt hD] using hv
    simpa [Real.sq_sqrt hD] using pow_le_pow_left₀ (norm_nonneg _) hT 2
  · intro h z
    rw [form_eq_norm_sq, energy_eq_norm_sq]
    calc
      _ ≤ (‖operator R S K‖ *
          ‖(WithLp.toLp 2 (fun j : S => z j) : EuclideanSpace ℂ S)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.le_opNorm _ _) 2
      _ = ‖operator R S K‖ ^ 2 *
          ‖(WithLp.toLp 2 (fun j : S => z j) : EuclideanSpace ℂ S)‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h (sq_nonneg _)

theorem transpose_bound (R : Finset α) (S : Finset β) (K : α → β → ℂ)
    (D : ℝ) (hD : 0 ≤ D) (h : HasBound R S K D) :
    HasBound S R (fun j i => K i j) D := by
  apply (hasBound_iff_norm_sq_le S R _ D hD).mpr
  change ‖(matrix R S K).transpose.toEuclideanLin.toContinuousLinearMap‖ ^ 2 ≤ D
  rw [DedekindZetaZeroFree.LargeSieve.Vendor.FiniteOperator.operator_transpose_norm]
  exact (hasBound_iff_norm_sq_le R S K D hD).mp h

/-- Sharp analytic duality; arithmetic reciprocity is a separate step. -/
theorem transpose_bound_iff (R : Finset α) (S : Finset β) (K : α → β → ℂ)
    (D : ℝ) (hD : 0 ≤ D) :
    HasBound R S K D ↔ HasBound S R (fun j i => K i j) D :=
  ⟨transpose_bound R S K D hD, transpose_bound S R (fun j i => K i j) D hD⟩

theorem energy_conjugate (S : Finset β) (z : β → ℂ) :
    energy S (fun j => star (z j)) = energy S z := by
  simp [energy]

theorem form_conjugate (R : Finset α) (S : Finset β) (K : α → β → ℂ)
    (z : β → ℂ) :
    form R S (fun i j => star (K i j)) z = form R S K (fun j => star (z j)) := by
  unfold form
  apply Finset.sum_congr rfl
  intro i _
  have heq : (∑ j ∈ S, star (K i j) * z j) =
      star (∑ j ∈ S, K i j * star (z j)) := by simp
  rw [heq, norm_star]

theorem conjugate_bound (R : Finset α) (S : Finset β) (K : α → β → ℂ)
    (D : ℝ) (h : HasBound R S K D) :
    HasBound R S (fun i j => star (K i j)) D := by
  intro z
  rw [form_conjugate]
  simpa only [energy_conjugate] using h (fun j => star (z j))

theorem conjugate_bound_iff (R : Finset α) (S : Finset β) (K : α → β → ℂ)
    (D : ℝ) : HasBound R S K D ↔ HasBound R S (fun i j => star (K i j)) D := by
  constructor
  · exact conjugate_bound R S K D
  · intro h
    simpa only [star_star] using conjugate_bound R S (fun i j => star (K i j)) D h

theorem conjTranspose_bound_iff (R : Finset α) (S : Finset β) (K : α → β → ℂ)
    (D : ℝ) (hD : 0 ≤ D) :
    HasBound R S K D ↔ HasBound S R (fun j i => star (K i j)) D :=
  (transpose_bound_iff R S K D hD).trans
    (conjugate_bound_iff S R (fun j i => K i j) D)

def zeroExtension (S : Finset β) (z : β → ℂ) (j : β) : ℂ :=
  if j ∈ S then z j else 0

theorem zeroExtension_sum (S S' : Finset β) (hS : S' ⊆ S)
    (K : α → β → ℂ) (z : β → ℂ) (i : α) :
    (∑ j ∈ S, K i j * zeroExtension S' z j) = ∑ j ∈ S', K i j * z j := by
  simpa only [zeroExtension, mul_comm] using
    DedekindZetaZeroFree.LargeSieve.Vendor.finite_subrange_mask_sum_mul
      S S' hS (fun j i => K i j) z i

theorem zeroExtension_energy (S S' : Finset β) (hS : S' ⊆ S) (z : β → ℂ) :
    energy S (zeroExtension S' z) = energy S' z := by
  exact DedekindZetaZeroFree.LargeSieve.Vendor.finite_subrange_mask_sum_norm_sq S S' hS z

theorem restrict_bound (R R' : Finset α) (S S' : Finset β)
    (hR : R' ⊆ R) (hS : S' ⊆ S) (K : α → β → ℂ)
    (D : ℝ) (hD : 0 ≤ D) (h : HasBound R S K D) : HasBound R' S' K D := by
  simpa only [HasBound, form, energy, mul_comm] using
    DedekindZetaZeroFree.LargeSieve.Vendor.finite_subrange_bound
      R R' S S' hR hS (fun j i => K i j) D hD
      (by simpa only [HasBound, form, energy, mul_comm] using h)

theorem diagonal_twist_bound (R : Finset α) (S : Finset β) (K : α → β → ℂ)
    (l : α → ℂ) (r : β → ℂ) (hl : ∀ i ∈ R, ‖l i‖ ≤ 1)
    (hr : ∀ j ∈ S, ‖r j‖ ≤ 1) (D : ℝ) (hD : 0 ≤ D)
    (h : HasBound R S K D) : HasBound R S (fun i j => l i * K i j * r j) D := by
  apply (hasBound_iff_norm_sq_le R S _ D hD).mpr
  have ht := DedekindZetaZeroFree.LargeSieve.Vendor.FiniteOperator.Auxiliary.diagonal_twist_norm_le
    (matrix R S K) (fun i : R => l i) (fun j : S => r j)
    (fun i => hl i i.property) (fun j => hr j j.property)
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
    ((hasBound_iff_norm_sq_le R S K D hD).mp h)

/-- Composition of finite kernels multiplies the squared operator bounds. -/
theorem composition_bound (R : Finset α) (S : Finset β) (T : Finset γ)
    (K : α → β → ℂ) (L : β → γ → ℂ) (D E : ℝ)
    (hD : 0 ≤ D) (hK : HasBound R S K D) (hL : HasBound S T L E) :
    HasBound R T (fun i k => ∑ j ∈ S, K i j * L j k) (D * E) := by
  intro z
  let y : β → ℂ := fun j => ∑ k ∈ T, L j k * z k
  have hf : form R T (fun i k => ∑ j ∈ S, K i j * L j k) z = form R S K y := by
    unfold form
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    dsimp only [y]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun k _ => mul_assoc _ _ _))
  rw [hf]
  calc
    _ ≤ D * energy S y := hK y
    _ ≤ D * (E * energy T z) := mul_le_mul_of_nonneg_left (hL z) hD
    _ = _ := by ring

/-- A supplied exact reciprocity identity gives finite-class transpose control.
The identity must also hold at shared-prime pairs; no zero terms are removed. -/
theorem phase_transpose_bound [Fintype κ]
    (R : Finset α) (S : Finset β) (K : α → β → ℂ) (L : β → α → ℂ)
    (rowClass : α → κ) (colClass : β → δ) (phase : κ → δ → ℂ)
    (hphase : ∀ a b, ‖phase a b‖ ≤ 1)
    (hrec : ∀ i ∈ R, ∀ j ∈ S, K i j = phase (rowClass i) (colClass j) * L j i)
    (D : ℝ) (hD : 0 ≤ D) (h : HasBound S R L D) :
    HasBound R S K ((Fintype.card κ : ℝ) ^ 2 * D) := by
  apply (hasBound_iff_norm_sq_le R S K _ (mul_nonneg (sq_nonneg _) hD)).mpr
  have hp := DedekindZetaZeroFree.LargeSieve.Vendor.FiniteOperator.separated_phase_norm_le
    (matrix R S K) (matrix S R L) (fun i : R => rowClass i) (fun j : S => colClass j)
    phase hphase (fun i j => hrec i i.property j j.property)
  exact hp.trans (mul_le_mul_of_nonneg_left
    ((hasBound_iff_norm_sq_le S R L D hD).mp h) (sq_nonneg _))

end CubicSieve.FiniteKernel
