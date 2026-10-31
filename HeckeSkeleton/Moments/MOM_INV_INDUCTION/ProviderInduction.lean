import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderNodes
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.UniformThreshold

/-!
# Finite backward induction on the actual canonical node class

Each stage retains the original column family, all labels and sectors,
the exact coefficient puncture, both canonical margins, and the complete
squarefree column pool.  The energy is `Node.energy`, the provider's
literal normalized finite sum.  There is no substituted energy function.

The local implication is used at a prescribed child seminorm.  Its parent
seminorm is then selected, finitely many times backwards.  At the last
stage the nonnegative row length contradicts its strictly negative upper
bound; no terminal estimate is assumed for that empty stage.  The short
completed contribution belongs to the local implication, alongside the
long-cube and long-label applications of the actual single-step theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInduction

open NumberField IsDedekindDomain
open HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderNodes
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
variable {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Λ G : HeckeCharacter K) (slotCap : ℕ)

/-- A strictly negative row cap makes the actual complete node class
empty, regardless of its coefficient/test/label data. -/
theorem uniformBound_of_negative_row_cap
    (Z A c z lo hi eps R C : ℝ) (t : Finset (ℕ × ℕ)) (hR : R < 0) :
    UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap
      Z A c z lo hi eps R C t := by
  intro σ x hx hrow
  exact False.elim (not_lt_of_ge hx.row_nonneg (hrow.trans_lt hR))

/-- Enlarge the final allocated exponent only after the common finite
seminorm and scalar have been chosen. -/
theorem uniformBound_mono_loss
    (Z A c z lo hi eps eps' R C : ℝ) (t : Finset (ℕ × ℕ))
    (hZ : 1 ≤ Z) (hC : 0 ≤ C) (heps : eps ≤ eps')
    (h : UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap
      Z A c z lo hi eps R C t) :
    UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap
      Z A c z lo hi eps' R C t := by
  intro σ x hx hrow
  exact (h x hx hrow).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ (add_le_add le_rfl heps))
    (mul_nonneg hC (sq_nonneg _)))

/-- Closure of the real uniform node class under one backwards choice
per level.  All bases and source nodes are quantified after the final
constant and seminorm.  The only supplied implication is local: it must
consume the actual uniform next-stage bound. -/
theorem exists_uniform_bound_from_local_steps
    (depth : ℕ) (d eta loss Mmax Fmax c z lo hi Z₀ : ℝ)
    (hdepth : Mmax < (depth : ℝ) * d) (hloss : 0 ≤ loss)
    (hstep : ∀ t : Finset (ℕ × ℕ),
      ∃ q : Finset (ℕ × ℕ), ∃ C : ℝ, 1 ≤ C ∧
        ∀ j : ℕ, j < depth → ∀ Z : ℝ, Z₀ ≤ Z →
        ∀ eps B : ℝ, 0 ≤ eps → 1 ≤ B →
        UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
          (stageCapacity Fmax eta (j + 1)) (stageMargin c eta (j + 1))
          z lo hi eps (stageRowBound Mmax d (j + 1)) B t →
        UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
          (stageCapacity Fmax eta j) (stageMargin c eta j)
          z lo hi (eps + loss) (stageRowBound Mmax d j) (3 * C * B) q) :
    ∃ q : Finset (ℕ × ℕ), ∃ C : ℝ, 1 ≤ C ∧
      ∀ Z : ℝ, Z₀ ≤ Z →
        UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap
          Z Fmax c z lo hi ((depth : ℝ) * loss) Mmax C q := by
  have stages : ∀ n : ℕ, n ≤ depth →
      ∃ q : Finset (ℕ × ℕ), ∃ C : ℝ, 1 ≤ C ∧
        ∀ j : ℕ, j + n = depth → ∀ Z : ℝ, Z₀ ≤ Z →
        UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
          (stageCapacity Fmax eta j) (stageMargin c eta j)
          z lo hi ((n : ℝ) * loss) (stageRowBound Mmax d j) C q := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨∅, 1, le_rfl, ?_⟩
      intro j hj Z _
      have heq : j = depth := by omega
      subst j
      apply uniformBound_of_negative_row_cap
      dsimp only [stageRowBound]
      linarith
    | succ n ih =>
      intro hn
      obtain ⟨t, B, hB, ht⟩ := ih (Nat.le_trans (Nat.le_succ n) hn)
      obtain ⟨q, C, hC, hq⟩ := hstep t
      have hCB : 1 ≤ 3 * C * B := by
        have hprod := one_le_mul_of_one_le_of_one_le hC hB
        nlinarith
      refine ⟨q, 3 * C * B, hCB, ?_⟩
      intro j hj Z hZ
      have hjlt : j < depth := by omega
      have hchild := ht (j + 1) (by omega) Z hZ
      have hb := hq j hjlt Z hZ ((n : ℝ) * loss) B
        (mul_nonneg (Nat.cast_nonneg _) hloss) hB hchild
      have hex : (n : ℝ) * loss + loss = ((n + 1 : ℕ) : ℝ) * loss := by
        push_cast
        ring
      simpa only [hex] using hb
  obtain ⟨q, C, hC, hq⟩ := stages depth le_rfl
  refine ⟨q, C, hC, ?_⟩
  intro Z hZ
  simpa only [stageCapacity, stageMargin, stageRowBound, Nat.cast_zero,
    mul_zero, zero_mul, add_zero, sub_zero] using hq 0 (by omega) Z hZ

/-- The simultaneous numerical budget gives the requested epsilon for
the literal node class.  This final comparison does not change the
profiles or any canonical admissibility condition. -/
theorem exists_uniform_bound_of_budget
    {Mmax c eps : ℝ} (b : DescentBudget Mmax c eps)
    (Fmax z lo hi Z₀ : ℝ) (hZ₀ : 1 ≤ Z₀)
    (hstep : ∀ t : Finset (ℕ × ℕ),
      ∃ q : Finset (ℕ × ℕ), ∃ C : ℝ, 1 ≤ C ∧
        ∀ j : ℕ, j < b.depth → ∀ Z : ℝ, Z₀ ≤ Z →
        ∀ e B : ℝ, 0 ≤ e → 1 ≤ B →
        UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
          (stageCapacity Fmax b.eta (j + 1)) (stageMargin c b.eta (j + 1))
          z lo hi e (stageRowBound Mmax b.step (j + 1)) B t →
        UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
          (stageCapacity Fmax b.eta j) (stageMargin c b.eta j)
          z lo hi (e + (40 * b.eta + b.tau + b.pi))
          (stageRowBound Mmax b.step j) (3 * C * B) q) :
    ∃ q : Finset (ℕ × ℕ), ∃ C : ℝ, 1 ≤ C ∧
      ∀ Z : ℝ, Z₀ ≤ Z →
        UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap
          Z Fmax c z lo hi (eps / 2) Mmax C q := by
  have hloss : 0 ≤ 40 * b.eta + b.tau + b.pi := by
    have := b.eta_pos
    have := b.tau_pos
    have := b.pi_pos
    positivity
  obtain ⟨q, C, hC, hq⟩ := exists_uniform_bound_from_local_steps D Λ G slotCap
    b.depth b.step b.eta (40 * b.eta + b.tau + b.pi) Mmax Fmax c z lo hi Z₀
    b.depth_bound hloss hstep
  refine ⟨q, C, hC, ?_⟩
  intro Z hZ
  exact uniformBound_mono_loss D Λ G slotCap Z Fmax c z lo hi
    ((b.depth : ℝ) * (40 * b.eta + b.tau + b.pi)) (eps / 2) Mmax C q
    (hZ₀.trans hZ) (zero_le_one.trans hC) b.loss_budget.le (hq Z hZ)

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInduction

end
