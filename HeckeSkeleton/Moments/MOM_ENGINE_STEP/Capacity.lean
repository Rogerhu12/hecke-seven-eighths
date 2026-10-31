import HeckePort.Moments.SlotRemoval

/-!
# One capacity repair on the actual live product

`capacity_removal_step` chooses one set of whole slots after all defects
have been included.  It handles an empty live set and a nonempty live set
in the same statement.  The output is either the unrestricted zero-slot
case or the capacity inequality for the remaining product.

The pointwise and energy conclusions use the literal products of the
functions supplied to the theorem.  They are not bounds on a formal
replacement for the child polynomial.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

def capacityDefect {ι : Type*} (live : Finset ι) (length : ι → ℝ)
    (n₁ n₂ width κ : ℝ) : ℝ :=
  max (n₁ + n₂ + 6 * κ * (∑ i ∈ live, length i) - width) 0

theorem capacityDefect_nonneg {ι : Type*} (live : Finset ι) (length : ι → ℝ)
    (n₁ n₂ width κ : ℝ) : 0 ≤ capacityDefect live length n₁ n₂ width κ :=
  le_max_right _ _

theorem remaining_capacity {ι : Type*} [DecidableEq ι]
    (live removed : Finset ι) (hR : removed ⊆ live) (length : ι → ℝ)
    (n₁ n₂ width κ : ℝ)
    (hpay : removed = live ∨
      capacityDefect live length n₁ n₂ width κ -
        6 * κ * (∑ i ∈ removed, length i) ≤ 0) :
    removed = live ∨ n₁ + n₂ + 6 * κ * (∑ i ∈ live \ removed, length i) ≤ width := by
  rcases hpay with h | h
  · exact Or.inl h
  · right
    have hs := Finset.sum_sdiff hR (f := length)
    have hm := le_max_left (n₁ + n₂ + 6 * κ * (∑ i ∈ live, length i) - width) (0 : ℝ)
    change max _ _ - _ ≤ _ at h
    rw [← hs] at hm h
    nlinarith

/-- A single choice of removed slots works simultaneously for every row. -/
theorem capacity_removal_step {ι : Type*} [DecidableEq ι]
    (live : Finset ι) (length : ι → ℝ) (n₁ n₂ width κ mesh Δ err : ℝ)
    (hκ : 0 < κ) (hmesh : 0 ≤ mesh)
    (hL : ∀ i ∈ live, 0 ≤ length i) (hLm : ∀ i ∈ live, length i ≤ mesh)
    (hdefect : capacityDefect live length n₁ n₂ width κ ≤ 6 * Δ + err) :
    ∃ removed : Finset ι, removed ⊆ live ∧
      (removed = live ∨ n₁ + n₂ + 6 * κ * (∑ i ∈ live \ removed, length i) ≤ width) ∧
      ∀ Z : ℝ, 1 ≤ Z → ∀ C : ι → ℝ, (∀ i ∈ live, 0 ≤ C i) →
      ∀ Q : ι → ℂ, (∀ i ∈ live, ‖Q i‖ ^ 2 ≤ C i * Z ^ (κ * length i)) →
        ‖∏ i ∈ live, Q i‖ ^ 2 ≤
          (∏ i ∈ removed, C i) * Z ^ (Δ + err / 6 + κ * mesh) *
            ‖∏ i ∈ live \ removed, Q i‖ ^ 2 := by
  obtain ⟨removed, hR, hpay, hbound⟩ := HeckePort.Moments.actual_product_removal
    live length mesh κ (capacityDefect live length n₁ n₂ width κ) hmesh hκ
    (capacityDefect_nonneg _ _ _ _ _ _) hL hLm
  refine ⟨removed, hR, remaining_capacity live removed hR length n₁ n₂ width κ hpay, ?_⟩
  intro Z hZ C hC Q hQ
  apply (hbound Z hZ C hC Q hQ).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg (‖∏ i ∈ live \ removed, Q i‖))
  apply mul_le_mul_of_nonneg_left _
    (Finset.prod_nonneg (fun i hi => hC i (hR hi)))
  exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

/-- The same single removal pays for a finite row norm of two plain
factors and every live prime factor.  Plain factors are untouched. -/
theorem capacity_energy_step {ι H : Type*} [DecidableEq ι]
    (live : Finset ι) (length : ι → ℝ) (n₁ n₂ width κ mesh Δ err : ℝ)
    (hκ : 0 < κ) (hmesh : 0 ≤ mesh)
    (hL : ∀ i ∈ live, 0 ≤ length i) (hLm : ∀ i ∈ live, length i ≤ mesh)
    (hdefect : capacityDefect live length n₁ n₂ width κ ≤ 6 * Δ + err) :
    ∃ removed : Finset ι, removed ⊆ live ∧
      (removed = live ∨ n₁ + n₂ + 6 * κ * (∑ i ∈ live \ removed, length i) ≤ width) ∧
      ∀ (Z : ℝ), 1 ≤ Z → ∀ C : ι → ℝ, (∀ i ∈ live, 0 ≤ C i) →
      ∀ (rows : Finset H) (Q : H → ι → ℂ) (plain₁ plain₂ : H → ℂ)
        (rowWeight : H → ℝ), (∀ h ∈ rows, 0 ≤ rowWeight h) →
      (∀ h ∈ rows, ∀ i ∈ live, ‖Q h i‖ ^ 2 ≤ C i * Z ^ (κ * length i)) →
      (∑ h ∈ rows, rowWeight h * ‖plain₁ h * plain₂ h * ∏ i ∈ live, Q h i‖ ^ 2) ≤
        (∏ i ∈ removed, C i) * Z ^ (Δ + err / 6 + κ * mesh) *
        ∑ h ∈ rows, rowWeight h *
          ‖plain₁ h * plain₂ h * ∏ i ∈ live \ removed, Q h i‖ ^ 2 := by
  obtain ⟨removed, hR, hcap, hbound⟩ :=
    capacity_removal_step live length n₁ n₂ width κ mesh Δ err hκ hmesh hL hLm hdefect
  refine ⟨removed, hR, hcap, ?_⟩
  intro Z hZ C hC rows Q plain₁ plain₂ rowWeight hW hQ
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h hh
  have hb := hbound Z hZ C hC (Q h) (hQ h hh)
  have hm := mul_le_mul_of_nonneg_left hb
    (mul_nonneg (hW h hh) (sq_nonneg (‖plain₁ h * plain₂ h‖)))
  simpa only [norm_mul, mul_pow, mul_assoc, mul_left_comm, mul_comm] using hm

/-- Frozen slots and plain extractions reduce the affine capacity load.
The reduction length pays for every removed slot length; no divisor
condition is dropped from the actual coefficient to obtain this inequality. -/
theorem frozen_subsupport_capacity {ι : Type*} [DecidableEq ι]
    (parent live : Finset ι) (hlive : live ⊆ parent) (length : ι → ℝ)
    (κ reduction : ℝ) (hκ : 0 ≤ κ) (hlen : ∀ i ∈ parent, 0 ≤ length i)
    (hred : (∑ i ∈ parent, length i) - (∑ i ∈ live, length i) ≤ reduction) :
    -reduction + (6 * κ - 1) * (∑ i ∈ live, length i) ≤
      (6 * κ - 1) * (∑ i ∈ parent, length i) := by
  have hsum : (∑ i ∈ live, length i) ≤ ∑ i ∈ parent, length i :=
    Finset.sum_le_sum_of_subset_of_nonneg hlive (fun i hi _ => hlen i hi)
  nlinarith

/-- Collect extraction, clipping and row-width errors before taking the
positive part.  This is the precise input to the one-time removal above. -/
theorem capacity_defect_after_all_errors {ι : Type*} [DecidableEq ι]
    (parent live : Finset ι) (hlive : live ⊆ parent) (length : ι → ℝ)
    (κ A M rawA nominalWidth actualWidth reduction n₁ n₂
      w ell supportError clipError widthError : ℝ)
    (hκ : 0 ≤ κ) (hlen : ∀ i ∈ parent, 0 ≤ length i)
    (hparent : A + (6 * κ - 1) * (∑ i ∈ parent, length i) ≤ M)
    (hred : (∑ i ∈ parent, length i) - (∑ i ∈ live, length i) ≤ reduction)
    (hshift : rawA - nominalWidth ≤ A - M + 6 * (w + ell) + supportError)
    (hclip : n₁ + n₂ + (∑ i ∈ live, length i) ≤ rawA - reduction + clipError)
    (hwidth : nominalWidth - actualWidth ≤ widthError)
    (hbudget : 0 ≤ 6 * (w + ell) + supportError + clipError + widthError) :
    capacityDefect live length n₁ n₂ actualWidth κ ≤
      6 * (w + ell) + supportError + clipError + widthError := by
  have hr := frozen_subsupport_capacity parent live hlive length κ reduction hκ hlen hred
  apply max_le _ hbudget
  nlinarith

end HeckeSkeleton.Moments.EngineStep
