import HeckePort.Schedule.MomentMesh
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Order
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.TerminalCertificate
import Mathlib.Tactic.Ring

/-!
# The original moment mesh pays for the complete induction order

The skeleton fixes `momentMeshValue` before choosing the target geometry.
This module uses that same mesh.  It does not replace it by a fresh smaller
parameter after the source has been chosen.

The complete rank includes both slot regimes and both proof stages.  Its
depth is at most eight times the strict-width schedule depth.  The reserve
already built into `momentMeshValue` pays for this larger count together
with the terminal loss, at width limit two.  This limit includes the actual
dyadic source row exponent proved in `RootNormalization`.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

/-- The rank count includes comparison calls and the change of slot regime,
as well as the strict-width calls counted by the preselected schedule. -/
theorem engine_rank_bound_le_schedule_depth {M σ : ℝ}
    (hM : 0 ≤ M) (hσ : 0 < σ) :
    4 * (widthBand σ M + 1) ≤ 8 * HeckePort.Schedule.depth M σ := by
  have hd := HeckePort.Schedule.depth_covers M σ hσ
  have hband : widthBand σ M < 2 * HeckePort.Schedule.depth M σ := by
    unfold widthBand
    apply (Nat.floor_lt (show 0 ≤ 4 * M / σ from by positivity)).2
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    apply (div_lt_iff₀ hσ).2
    nlinarith
  omega

/-- The actual reserve used in the skeleton's fixed width-two mesh. -/
def sourceReserve (ε : ℝ) : ℝ :=
  HeckePort.Schedule.reserve 2 (HeckePort.Schedule.finalSourceCap 2 0 1 ε) ε

/-- The fixed mesh is already small enough for the prime-pool window and
for the aggregate boundary precision in the strict-width step. -/
theorem moment_mesh_engine_bounds {ε : ℝ} (hε : 0 < ε) :
    0 < HeckePort.Schedule.amplification ε ∧
      0 < sourceReserve ε ∧ 0 < HeckePort.Schedule.momentMeshValue ε ∧
      HeckePort.Schedule.momentMeshValue ε < HeckePort.Schedule.amplification ε / 6 ∧
      sourceReserve ε ≤ HeckePort.Schedule.amplification ε / 2 := by
  obtain ⟨hσ, _, _, hr, hm, hmr, _, hsmall, _, _⟩ :=
    HeckePort.Schedule.bounds 2 (HeckePort.Schedule.finalSourceCap 2 0 1 ε) 1 ε
      (by norm_num)
      (HeckePort.Schedule.finalSourceCap_nonneg 2 0 1 ε (by norm_num) le_rfl)
      zero_le_one hε
  change 0 < sourceReserve ε at hr
  change 0 < HeckePort.Schedule.momentMeshValue ε at hm
  change HeckePort.Schedule.momentMeshValue ε ≤ sourceReserve ε at hmr
  change 20 * sourceReserve ε ≤ HeckePort.Schedule.amplification ε / 2 at hsmall
  exact ⟨hσ, hr, hm, by linarith, by linarith⟩

/-- Keep the original mesh, choose the coarse step first, and use the
existing reserve for boundary precision and local analytic loss.  The
terminal error is paid once and all three edge errors are paid at every
rank.  All these parameters depend only on the fixed requested loss. -/
theorem moment_mesh_total_loss_budget {ε : ℝ} (hε : 0 < ε) :
    let σ := HeckePort.Schedule.amplification ε
    let r := sourceReserve ε
    let η := HeckePort.Schedule.momentMeshValue ε
    terminalBudget (16 * σ) (σ / 16) σ r +
      (4 * (widthBand σ 2 + 1) : ℕ) * (r + η + r) < ε := by
  dsimp only
  let σ := HeckePort.Schedule.amplification ε
  let r := sourceReserve ε
  let η := HeckePort.Schedule.momentMeshValue ε
  let D := HeckePort.Schedule.count 2 ε
  let N := 4 * (widthBand σ 2 + 1)
  change terminalBudget (16 * σ) (σ / 16) σ r + (N : ℝ) * (r + η + r) < ε
  obtain ⟨hσ, _, hσε, hr, _, hmr, _, _, _, hloss⟩ :=
    HeckePort.Schedule.bounds 2 (HeckePort.Schedule.finalSourceCap 2 0 1 ε) 1 ε
      (by norm_num)
      (HeckePort.Schedule.finalSourceCap_nonneg 2 0 1 ε (by norm_num) le_rfl)
      zero_le_one hε
  change 0 < r at hr
  change η ≤ r at hmr
  change r + 64 * (D : ℝ) * r ≤ ε / 1000 at hloss
  have hNnat : N ≤ 8 * D :=
    engine_rank_bound_le_schedule_depth (by norm_num) hσ
  have hN : (N : ℝ) ≤ 8 * (D : ℝ) := by exact_mod_cast hNnat
  have hcoarse : terminalBudget (16 * σ) (σ / 16) σ r ≤ 24 * σ + r := by
    unfold terminalBudget
    change 0 < σ at hσ
    linarith
  have hedge : (N : ℝ) * (r + η + r) ≤ 24 * (D : ℝ) * r := by
    calc
      _ ≤ (N : ℝ) * (3 * r) :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      _ ≤ (8 * (D : ℝ)) * (3 * r) :=
        mul_le_mul_of_nonneg_right hN (by positivity)
      _ = _ := by ring
  have hDr : 0 ≤ (D : ℝ) * r := mul_nonneg (Nat.cast_nonneg _) hr.le
  have htotal : terminalBudget (16 * σ) (σ / 16) σ r +
      (N : ℝ) * (r + η + r) ≤ 24 * σ + ε / 1000 := by
    linarith
  apply htotal.trans_lt
  change σ ≤ ε / 16000 at hσε
  linarith

/-- The unchanged original mesh also pays for one genuine outer ordinary
reflection. Its local mass loss is charged once, after the finite core
induction, rather than being inserted as a fictitious earlier edge. -/
theorem moment_mesh_loss_budget_with_outer_reflection {ε : ℝ} (hε : 0 < ε) :
    let σ := HeckePort.Schedule.amplification ε
    let r := sourceReserve ε
    let η := HeckePort.Schedule.momentMeshValue ε
    terminalBudget (16 * σ) (σ / 16) σ r +
      (4 * (widthBand σ 2 + 1) : ℕ) * (r + η + r) + r < ε := by
  dsimp only
  let σ := HeckePort.Schedule.amplification ε
  let r := sourceReserve ε
  let η := HeckePort.Schedule.momentMeshValue ε
  let D := HeckePort.Schedule.count 2 ε
  let N := 4 * (widthBand σ 2 + 1)
  change terminalBudget (16 * σ) (σ / 16) σ r + (N : ℝ) * (r + η + r) + r < ε
  obtain ⟨hσ, _, hσε, hr, _, hmr, _, _, _, hloss⟩ :=
    HeckePort.Schedule.bounds 2 (HeckePort.Schedule.finalSourceCap 2 0 1 ε) 1 ε
      (by norm_num)
      (HeckePort.Schedule.finalSourceCap_nonneg 2 0 1 ε (by norm_num) le_rfl)
      zero_le_one hε
  change 0 < r at hr
  change η ≤ r at hmr
  change r + 64 * (D : ℝ) * r ≤ ε / 1000 at hloss
  have hNnat : N ≤ 8 * D :=
    engine_rank_bound_le_schedule_depth (by norm_num) hσ
  have hN : (N : ℝ) ≤ 8 * (D : ℝ) := by exact_mod_cast hNnat
  have hcoarse : terminalBudget (16 * σ) (σ / 16) σ r ≤ 24 * σ + r := by
    unfold terminalBudget
    change 0 < σ at hσ
    linarith
  have hedge : (N : ℝ) * (r + η + r) ≤ 24 * (D : ℝ) * r := by
    calc
      _ ≤ (N : ℝ) * (3 * r) :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      _ ≤ (8 * (D : ℝ)) * (3 * r) :=
        mul_le_mul_of_nonneg_right hN (by positivity)
      _ = _ := by ring
  have hDr : 0 ≤ (D : ℝ) * r := mul_nonneg (Nat.cast_nonneg _) hr.le
  have hrε : r ≤ ε / 1000 := by linarith
  have htotal : terminalBudget (16 * σ) (σ / 16) σ r +
      (N : ℝ) * (r + η + r) + r ≤ 24 * σ + 2 * ε / 1000 := by
    linarith
  apply htotal.trans_lt
  change σ ≤ ε / 16000 at hσε
  linarith

end HeckeSkeleton.Moments.EngineInduction
