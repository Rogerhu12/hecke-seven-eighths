import HeckeGeneral.Analysis.MomentInputs

/-!
Numerical rounding margins for the source witness crossing.
Q quasi-riemann.tex 15314--15406 uses r >= 23/37 on the inverse branch,
z <= (1-r)/2 minus a fixed decrement, and the dynamic plain capacity.
These lemmas account for an upper rounding of the actual length by eta.
They neither round an actual annular test to a different scale nor derive
the compact-range uniform moment estimates from fixed-parameter estimates.
-/

namespace HeckeGeneral.Analysis.ConditionalMoments

theorem inverse_witness_grid_margins {r rGrid z ν η : ℝ}
    (hr : 23 / 37 ≤ r) (hz : z ≤ (1 - r) / 2 - ν)
    (hgrid : rGrid ≤ r + η) (hν : 0 ≤ ν) :
    2 * ν - η ≤ 1 - rGrid - 2 * z ∧
      9 / 37 - 2 * η ≤ 3 - 2 * rGrid - 8 * z := by
  constructor <;> linarith

theorem inverse_witness_grid_uniform_margins {r rGrid z ν η : ℝ}
    (hr : 23 / 37 ≤ r) (hz : z ≤ (1 - r) / 2 - ν)
    (hgrid : rGrid ≤ r + η) (hν : 0 ≤ ν)
    (hην : η ≤ ν) :
    ν ≤ 1 - rGrid - 2 * z ∧ ν + 9 / 37 ≤ 3 - 2 * rGrid - 8 * z := by
  obtain ⟨h₁, h₂⟩ := inverse_witness_grid_margins hr hz hgrid hν
  constructor <;> linarith

/-- If the target margin is no larger than the decrement, the
rounded inverse parameters satisfy the actual MIUniformMargins predicate. -/
theorem inverse_witness_grid_MIUniformMargins {b : RealBox} {a : RealParameters}
    {r ν η : ℝ} (hm : a.m = 1)
    (hr : 23 / 37 ≤ r) (hz : a.z ≤ (1 - r) / 2 - ν)
    (hgrid : a.r ≤ r + η) (hν : 0 ≤ ν)
    (hην : η ≤ ν)
    (hbν : b.margin ≤ ν) :
    MIUniformMargins b a := by
  obtain ⟨h₁, h₂⟩ := inverse_witness_grid_uniform_margins hr hz hgrid hν hην
  constructor <;> rw [hm] <;> linarith

theorem plain_witness_grid_capacity {m mGrid κ z ν η : ℝ}
    (hκ : 3 / 4 ≤ κ) (hν : 0 ≤ ν)
    (hcapacity : 2 * m + 6 * κ * z ≤ 1)
    (hgrid : mGrid ≤ m + η) :
    2 * mGrid + 6 * κ * (z - ν) ≤ 1 + 2 * η - (9 / 2) * ν := by
  have hcost : (9 / 2) * ν ≤ 6 * κ * ν := by nlinarith
  nlinarith

theorem plain_witness_grid_retained_margin {m mGrid κ z ν η : ℝ}
    (hκ : 3 / 4 ≤ κ) (hν : 0 ≤ ν)
    (hcapacity : 2 * m + 6 * κ * z ≤ 1)
    (hgrid : mGrid ≤ m + η) (hη : η ≤ 9 * ν / 8) :
    2 * mGrid + 6 * κ * (z - ν) + (9 / 4) * ν ≤ 1 := by
  have h := plain_witness_grid_capacity hκ hν hcapacity hgrid
  linarith

/-- Squared-norm inverse thresholds lose at most eta, and the two-copy
plain threshold loses at most 2*eta under a length rounding by eta. -/
theorem witness_grid_spike_losses {δ r rGrid η : ℝ}
    (hδlo : 0 ≤ δ) (hδhi : δ ≤ 1) (hη : 0 ≤ η)
    (hgrid : rGrid ≤ r + η) :
    δ * rGrid - η ≤ δ * r ∧ 2 * δ * rGrid - 2 * η ≤ 2 * δ * r := by
  have hmul := mul_le_mul_of_nonneg_left hgrid hδlo
  have hcost := mul_le_mul_of_nonneg_right hδhi hη
  constructor <;> nlinarith

theorem witness_slot_capacity_spike_loss {q ν : ℝ}
    (hq : q ≤ 1 / 2) (hν : 0 ≤ ν) : 2 * q * ν ≤ ν := by
  nlinarith

end HeckeGeneral.Analysis.ConditionalMoments
