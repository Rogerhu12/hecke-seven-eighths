import HeckeSkeleton.Moments.MOM_INV_INDUCTION.EnergyClosure
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Backward induction in the published inverse-step form

The actual provider returns a conditional estimate on all of its smaller
pieces. Its scalar is `Cih + 1`, and its primitive error is
`Z^(M + 5 h + pi)`. It does not return the older linear `StepEnergy`
inequality. This file consumes that published form directly.

The finite seminorm at a parent may be larger than the seminorm used at
its children. `cost n` records the seminorm selected with `n` remaining
steps, so no invariant finite order is assumed. All constants and costs
are fixed before the varying node. The child relation may include the
provider's continuous spectral parameters; only its strict row decrease,
not finite branching, is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

/-- The actual primitive principal error fits inside the main step
power on every admissible parent. The fine mesh is charged only here. -/
theorem provider_error_exponent_le {F M h eta tau pi eps : ℝ}
    (hMF : M ≤ F) (hh : 0 ≤ h) (hmesh : h ≤ eta / 32)
    (htau : 0 ≤ tau) (heps : 0 ≤ eps) :
    M + 5 * h + pi ≤ F + stepLoss eta tau pi + eps := by
  unfold stepLoss
  linarith

/-- Consume exactly the two terms of the published provider estimate.
The common child constant is charged once, including the provider's
additive principal constant. -/
theorem provider_step_bound {E Z F M h eta tau pi eps B S : ℝ}
    (hZ : 1 ≤ Z) (hMF : M ≤ F) (hh : 0 ≤ h)
    (hmesh : h ≤ eta / 32) (htau : 0 ≤ tau) (heps : 0 ≤ eps)
    (hB : 1 ≤ B) (hS : 0 ≤ S)
    (hstep : E ≤ S * ((B + 1) * Z ^ (F + stepLoss eta tau pi + eps) +
      Z ^ (M + 5 * h + pi))) :
    E ≤ 3 * S * B * Z ^ (F + stepLoss eta tau pi + eps) := by
  have hp := Real.rpow_le_rpow_of_exponent_le hZ
    (provider_error_exponent_le (pi := pi) hMF hh hmesh htau heps)
  have hpow : 0 ≤ Z ^ (F + stepLoss eta tau pi + eps) :=
    Real.rpow_nonneg (zero_le_one.trans hZ) _
  apply hstep.trans
  calc
    _ ≤ S * ((B + 1) * Z ^ (F + stepLoss eta tau pi + eps) +
        Z ^ (F + stepLoss eta tau pi + eps)) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hp _) hS
    _ = S * ((B + 2) * Z ^ (F + stepLoss eta tau pi + eps)) := by ring
    _ ≤ S * ((3 * B) * Z ^ (F + stepLoss eta tau pi + eps)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by linarith) hpow) hS
    _ = _ := by ring

/-- The induction envelope retains the actual depth-dependent finite
seminorm, instead of bounding all future transformed tests by the
initial seminorm. -/
def providerEnvelope {α : Type*} (cost : ℕ → α → ℝ)
    (n : ℕ) (C Z L : ℝ) (F : α → ℝ) (x : α) : ℝ :=
  (3 * C) ^ n * cost n x * Z ^ (F x + (n : ℝ) * L)

/-- Finite closure for the provider's implication-style reduction.
`cost n x` can be the square of the selected finite Schwartz seminorm
of the literal profile at `x`. The hypotheses on children are exactly
the previous-stage estimate; there is no estimate at the parent among
the inputs. -/
theorem provider_finite_energy_bound {α : Type*}
    (E F M mesh : α → ℝ) (cost : ℕ → α → ℝ)
    (Child : α → α → Prop) (Terminal : α → Prop)
    (Good : ℕ → α → Prop)
    (D : ℕ) (Z eta tau pi C d Mmax : ℝ)
    (hZ : 1 ≤ Z) (heta : 0 ≤ eta) (htau : 0 ≤ tau) (hpi : 0 ≤ pi)
    (hC : 1 ≤ C) (hdepth : Mmax < (D : ℝ) * d)
    (hcost : ∀ n x, 0 ≤ cost n x)
    (hnonneg : ∀ h x, Good h x → 0 ≤ M x)
    (hMF : ∀ h x, Good h x → M x ≤ F x)
    (hmesh : ∀ h x, Good h x → 0 ≤ mesh x ∧ mesh x ≤ eta / 32)
    (hchild : ∀ h x y, h < D → Good h x → ¬ Terminal x → Child x y →
      Good (h + 1) y ∧ M y + d ≤ M x)
    (hterminal : ∀ h x, h < D → Good h x → Terminal x →
      E x ≤ C * cost (D - h) x * Z ^ F x)
    (hstep : ∀ h x, h < D → Good h x → ¬ Terminal x →
      ∀ B eps : ℝ, 1 ≤ B → 0 ≤ eps →
      (∀ y, Child x y →
        E y ≤ B * cost (D - (h + 1)) y * Z ^ (F y + eps)) →
      E x ≤ (C * cost (D - h) x) *
        ((B + 1) * Z ^ (F x + stepLoss eta tau pi + eps) +
          Z ^ (M x + 5 * mesh x + pi))) :
    ∀ x, Good 0 x → M x ≤ Mmax →
      E x ≤ providerEnvelope cost D C Z (stepLoss eta tau pi) F x := by
  have h3C : 1 ≤ 3 * C := by linarith
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hL : 0 ≤ stepLoss eta tau pi := stepLoss_nonneg heta htau hpi
  apply finite_descent_with_terminal M Child Terminal Good
    (fun h x => E x ≤ providerEnvelope cost (D - h) C Z (stepLoss eta tau pi) F x)
    D d Mmax hdepth hnonneg hchild
  · intro h x hh hx ht
    have hn : D - h = (D - (h + 1)) + 1 := by omega
    have hpowC : C ≤ (3 * C) ^ (D - h) := by
      rw [hn, pow_succ]
      nlinarith [one_le_pow₀ h3C (n := D - (h + 1))]
    have hpowZ : Z ^ F x ≤ Z ^ (F x + ((D - h : ℕ) : ℝ) * stepLoss eta tau pi) :=
      Real.rpow_le_rpow_of_exponent_le hZ
        (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hL))
    apply (hterminal h x hh hx ht).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_right hpowC (hcost _ _)) hpowZ
      (Real.rpow_nonneg (zero_le_one.trans hZ) _)
      (mul_nonneg (pow_nonneg (by linarith) _) (hcost _ _))
  · intro h x hh hx ht ih
    let n := D - (h + 1)
    have hn : D - h = n + 1 := by dsimp only [n]; omega
    have hB : 1 ≤ (3 * C) ^ n := one_le_pow₀ h3C
    have heps : 0 ≤ (n : ℝ) * stepLoss eta tau pi :=
      mul_nonneg (Nat.cast_nonneg _) hL
    have hp := hstep h x hh hx ht ((3 * C) ^ n)
      ((n : ℝ) * stepLoss eta tau pi) hB heps ih
    have hb := provider_step_bound hZ (hMF h x hx) (hmesh h x hx).1
      (hmesh h x hx).2 htau heps hB
      (mul_nonneg hC0 (hcost _ _)) hp
    have hex : F x + stepLoss eta tau pi + (n : ℝ) * stepLoss eta tau pi =
        F x + ((n + 1 : ℕ) : ℝ) * stepLoss eta tau pi := by
      push_cast
      ring
    rw [hex, hn] at hb
    simpa only [providerEnvelope, hn, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hb

/-- A finite common derivative order is chosen after the finite descent
schedule, before any varying scale or source profile. -/
def providerCommonSeminorm (q : ℕ → Finset (ℕ × ℕ)) (D : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (D + 1)).biUnion q

theorem provider_seminorm_le_common (q : ℕ → Finset (ℕ × ℕ))
    (D n : ℕ) (hn : n ≤ D) (W : SchwartzMap ℝ ℂ) :
    (q n).sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤
      (providerCommonSeminorm q D).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  apply Seminorm.le_def.mp (Finset.sup_mono ?_) W
  intro k hk
  exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_range.mpr (by omega), hk⟩

end HeckeSkeleton.Moments.MOM_INV_INDUCTION

end
